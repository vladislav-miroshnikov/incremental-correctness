Require Import List.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(* Абстрактные типы *)
Parameter type : Type. (* Типы данных в системе *)

(* Файлы *)
Parameter file : Type. (* Файлы, содержащие код *)

(* Выражения *)
Parameter expr : Type. (* Выражения, для которых нужно выводить типы *)

(* Имена для resolve *)
Parameter name : Type.

(* Отношение зависимости между файлами *)
Parameter depends : file -> file -> Prop. (* depends f1 f2: файл f1 зависит от файла f2 *)

(* Процедура разрешения имён *)
Parameter resolve : file -> name -> type. (* resolve f n: тип имени n в файле f *)

(* Кэш: отображение file -> expr -> option type *)
Definition cache := file -> expr -> option type. (* Кэш для хранения типов выражений в файлах *)

(* Функция сравнения файлов *)
Parameter eq_file : file -> file -> bool. (* Булева функция для сравнения файлов *)

(* Аксиома: eq_file корректна *)
Axiom eq_file_correct : forall f1 f2 : file, eq_file f1 f2 = true <-> f1 = f2.
(* eq_file f1 f2 = true тогда и только тогда, когда f1 и f2 — один и тот же файл *)

(* Аксиомы для depends *)
Axiom depends_trans : forall f1 f2 f3 : file,
  depends f1 f2 -> depends f2 f3 -> depends f1 f3.
(* Транзитивность отношения depends: если f1 зависит от f2, а f2 от f3, то f1 зависит от f3 *)

Axiom depends_acyclic : forall f : file, ~ depends f f.
(* Ацикличность: файл не может зависеть сам от себя *)

(* Аксиомы для resolve *)
Axiom resolve_defined : forall f : file, forall n : name, exists t : type, resolve f n = t.
(* resolve всегда определена: для любого файла и имени существует тип *)

(* Абстрактная функция вывода типов *)
Parameter infer : cache -> file -> expr -> type.
(* infer c f e: вычисляет тип выражения e в файле f, используя кэш c *)

(* Аксиомы для infer *)
Axiom infer_cache_hit : forall c : cache, forall f : file, forall e : expr, forall t : type,
  c f e = Some t -> infer c f e = t.
(* Если кэш содержит Some t для (f, e), то infer возвращает t *)

Axiom infer_cache_miss : forall c : cache, forall f : file, forall e : expr,
  c f e = None -> exists t : type, infer c f e = t.
(* Если кэш пуст для (f, e), infer всё равно возвращает некоторый тип *)

Axiom infer_deterministic : forall c1 c2 : cache, forall f : file, forall e : expr,
  (forall x : file, forall y : expr, c1 x y = c2 x y) -> infer c1 f e = infer c2 f e.
(* Если два кэша идентичны, infer выдаёт одинаковый результат *)

Axiom infer_depends_on_cache : forall c1 c2 : cache, forall f : file, forall e : expr,
  c1 f e = c2 f e -> infer c1 f e = infer c2 f e.
(* infer зависит только от значения кэша для (f, e) *)

(* Транзитивное замыкание depends *)
Inductive depends_transitive : file -> file -> Prop :=
  | depends_direct : forall f1 f2 : file, depends f1 f2 -> depends_transitive f1 f2
  | depends_indirect : forall f1 f2 f3 : file,
      depends f1 f2 -> depends_transitive f2 f3 -> depends_transitive f1 f3.
(* depends_transitive f1 f3: f1 зависит от f3 прямо или через цепочку зависимостей *)

(* Булева версия depends_transitive *)
Parameter depends_transitive_bool : file -> file -> bool.
(* Булева функция для проверки depends_transitive *)

Axiom depends_transitive_bool_correct : forall f1 f2 : file,
  depends_transitive_bool f1 f2 = true <-> depends_transitive f1 f2.
(* depends_transitive_bool корректно отражает depends_transitive *)

(* Сброс кэша в baseline подходе *)
Definition reset_cache_baseline (f : file) (c : cache) : cache :=
  fun f' e => if depends_transitive_bool f' f then None else c f' e.
(* Сбрасывает кэш для всех файлов, транзитивно зависящих от f *)

(* Сброс кэша в инкрементальном подходе *)
Definition reset_cache_incremental (f : file) (c : cache) : cache :=
  fun f' e => if eq_file f' f then None else c f' e.
(* Сбрасывает кэш только для файла f *)

(* Аксиома для корректности инкрементального подхода *)
Axiom incremental_correct : forall f : file, forall c : cache, forall f' : file, forall e : expr,infer (reset_cache_incremental f c) f' e = infer (reset_cache_baseline f c) f' e.
(* incremental и baseline подходы эквивалентны для infer *)

(* Лемма: если файл x не равен f0, то reset_cache_incremental не меняет кэш для x *)
Lemma reset_cache_alternative_neq : forall f0 : file, forall c : cache, forall x : file, forall e : expr,
  eq_file x f0 = false ->
  (reset_cache_incremental f0 c) x e = c x e.
Proof.
  intros f0 c x e H. (* Вводим переменные и гипотезу H: eq_file x f0 = false *)
  unfold reset_cache_incremental. (* Разворачиваем определение reset_cache_incremental *)
  rewrite H. (* Подставляем false из гипотезы H в условное выражение *)
  reflexivity. (* Получаем c x e = c x e, так как условие if не выполняется *)
Qed.

(* Лемма: если нет транзитивной зависимости, то depends_transitive_bool возвращает false *)
Lemma not_depends_transitive_bool : forall f ch : file,
  ~ depends_transitive f ch -> depends_transitive_bool f ch = false.
Proof.
  intros f ch Hndep. (* Вводим файлы f, ch и гипотезу Hndep: нет транзитивной зависимости *)
  destruct (depends_transitive_bool f ch) eqn:Hdt.
  - (* Случай: depends_transitive_bool f ch = true *)
    exfalso.
    apply Hndep. (* Используем отрицание транзитивной зависимости *)
    apply depends_transitive_bool_correct. (* Из Hdt следует, что depends_transitive f ch *)
    assumption. (* Hdt по assumption *)
  - (* Случай: depends_transitive_bool f ch = false *)
    reflexivity.
Qed.

(* Лемма: если файл f не зависит транзитивно от ch, то infer не меняется при сбросе кэша для ch *)
Lemma incremental_equiv_step : forall cache : cache, forall ch : file, forall f : file, forall e : expr,
  ~ depends_transitive f ch ->
  infer (reset_cache_incremental ch cache) f e = infer cache f e.
Proof.
  intros cache ch f e Hndep. (* Вводим переменные и гипотезу Hndep: нет транзитивной зависимости *)
  rewrite incremental_correct. (* Заменяем incremental на baseline с помощью аксиомы *)
  unfold reset_cache_baseline. (* Разворачиваем определение reset_cache_baseline *)
  assert (
    (fun f' e0 => if depends_transitive_bool f' ch then None else cache f' e0) f e = cache f e
  ) as Heq. (* Утверждаем, что кэш для (f, e) не меняется *)
  { 
    simpl.
    pose proof (not_depends_transitive_bool f ch Hndep) as Hbool. (* Доказываем, что depends_transitive_bool f ch = false *)
    rewrite Hbool. (* Подставляем false в условие if *)
    reflexivity. (* Получаем cache f e = cache f e *)
  }
  apply infer_depends_on_cache. (* Применяем аксиому: infer зависит только от кэша в (f, e) *)
  exact Heq. (* Используем Heq, подтверждающее равенство кэшей *)
Qed.

(* Лемма: последовательный сброс кэша для списка изменений эквивалентен полному сбросу *)
Lemma incremental_equiv_full : forall changes : list file, forall f' : file, forall e : expr,
  infer (fold_left (fun c f => reset_cache_incremental f c) changes (fun _ _ => None)) f' e =
  infer (fun _ _ => None) f' e.
Proof.
  intros changes f' e.
  induction changes as [| f changes' IH].
  - (* Базовый случай: changes = [] *)
    simpl. (* Разворачиваем fold_left, получаем (fun _ _ => None) *)
    reflexivity.
  - (* Индуктивный шаг: changes = f :: changes' *)
    simpl. (* Разворачиваем fold_left: infer (fold_left ... (reset_cache_incremental f (fun _ _ => None))) f' e *)
    assert (H: reset_cache_incremental f (fun _ _ => None) = (fun _ _ => None)).
    { 
      (* Доказываем, что reset_cache_incremental f (fun _ _ => None) эквивалентно (fun _ _ => None) *)
      extensionality f''. (* Вводим переменную f'' для file *)
      extensionality e''. (* Вводим переменную e'' для expr *)
      unfold reset_cache_incremental. (* Разворачиваем определение *)
      destruct (eq_file f'' f). (* Анализируем eq_file f'' f *)
      - (* Случай eq_file f'' f = true *)
        reflexivity. 
      - (* Случай eq_file f'' f = false *)
        reflexivity.
    }rewrite H. (* Заменяем reset_cache_incremental на (fun _ _ => None) *)
    apply IH. (* Применяем индуктивную гипотезу *)
Qed.