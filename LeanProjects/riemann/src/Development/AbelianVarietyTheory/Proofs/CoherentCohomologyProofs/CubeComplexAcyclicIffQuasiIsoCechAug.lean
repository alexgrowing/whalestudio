import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars

open CategoryTheory Limits HomologicalComplex

universe v u

namespace GlobalTheory

namespace Cube

section Faces

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]

def lowerFace (e : κ ↪o ι) (A : Cube.{v} ι R) : Cube.{v} κ R :=
  mk (fun s => A.obj (s.map e.toEmbedding)) (fun h => res A (Finset.map_subset_map.2 h))
    (fun _ _ => res_self A _ _) (fun _ _ _ => res_res A _ _ _)

def upperFace (e : κ ↪o ι) (i : ι) (A : Cube.{v} ι R) : Cube.{v} κ R :=
  mk (fun s => A.obj (insert i (s.map e.toEmbedding)))
    (fun h => res A (Finset.insert_subset_insert i (Finset.map_subset_map.2 h)))
    (fun _ _ => res_self A _ _) (fun _ _ _ => res_res A _ _ _)

variable (e : κ ↪o ι) (i : ι)

theorem lowerFace_obj (A : Cube.{v} ι R) (s : Finset κ) :
    (lowerFace e A).obj s = A.obj (s.map e.toEmbedding) := rfl

theorem upperFace_obj (A : Cube.{v} ι R) (s : Finset κ) :
    (upperFace e i A).obj s = A.obj (insert i (s.map e.toEmbedding)) := rfl

theorem res_lowerFace (A : Cube.{v} ι R) {s t : Finset κ} (h : s ⊆ t) :
    res (lowerFace e A) h = res A (Finset.map_subset_map.2 h) := rfl

theorem res_upperFace (A : Cube.{v} ι R) {s t : Finset κ} (h : s ⊆ t) :
    res (upperFace e i A) h =
      res A (Finset.insert_subset_insert i (Finset.map_subset_map.2 h)) := rfl

def faceMap (A : Cube.{v} ι R) : lowerFace e A ⟶ upperFace e i A :=
  homMk (fun s => res A (Finset.subset_insert i (s.map e.toEmbedding)))
    fun _ _ => (res_res A _ _ _).trans (res_res A _ _ _).symm

theorem faceMap_app (A : Cube.{v} ι R) (s : Finset κ) :
    ((faceMap e i A).app s).hom = res A (Finset.subset_insert i (s.map e.toEmbedding)) := rfl

def lowerFaceMap {A B : Cube.{v} ι R} (φ : A ⟶ B) : lowerFace e A ⟶ lowerFace e B :=
  homMk (fun s => (φ.app (s.map e.toEmbedding)).hom) fun _ _ => app_res φ _ _

def upperFaceMap {A B : Cube.{v} ι R} (φ : A ⟶ B) : upperFace e i A ⟶ upperFace e i B :=
  homMk (fun s => (φ.app (insert i (s.map e.toEmbedding))).hom) fun _ _ => app_res φ _ _

theorem lowerFaceMap_app {A B : Cube.{v} ι R} (φ : A ⟶ B) (s : Finset κ) :
    (lowerFaceMap e φ).app s = φ.app (s.map e.toEmbedding) := rfl

theorem upperFaceMap_app {A B : Cube.{v} ι R} (φ : A ⟶ B) (s : Finset κ) :
    (upperFaceMap e i φ).app s = φ.app (insert i (s.map e.toEmbedding)) := rfl

@[reassoc]
theorem faceMap_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    lowerFaceMap e φ ≫ faceMap e i B = faceMap e i A ≫ upperFaceMap e i φ := by
  ext s x
  exact (app_res φ (Finset.subset_insert i (s.map e.toEmbedding)) x).symm

theorem cubeSign_map (s : Finset κ) (k : κ) :
    cubeSign (s.map e.toEmbedding) (e k) = cubeSign s k := by
  unfold cubeSign
  rw [Finset.filter_map, Finset.card_map]
  congr 2
  ext j
  simp

def upperSign (s : Finset κ) : ℤ :=
  (-1) ^ s.card * cubeSign (insert i (s.map e.toEmbedding)) i

@[simp]
theorem upperSign_mul_self (s : Finset κ) : upperSign e i s * upperSign e i s = 1 := by
  rw [upperSign, mul_mul_mul_comm, cubeSign_mul_self, ← mul_pow]; simp

@[simp]
theorem upperSign_smul_smul {M : Type*} [AddCommGroup M] (s : Finset κ) (x : M) :
    upperSign e i s • upperSign e i s • x = x := by
  rw [smul_smul, upperSign_mul_self, one_smul]

theorem upperSign_eq_one (h : ∀ k, e k < i) (s : Finset κ) : upperSign e i s = 1 := by
  have : (insert i (s.map e.toEmbedding)).filter (· < i) = s.map e.toEmbedding := by
    rw [Finset.filter_insert, if_neg (lt_irrefl i), Finset.filter_true_of_mem]
    intro j hj
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hj
    exact h k
  rw [upperSign, cubeSign, this, Finset.card_map, ← mul_pow]; simp

theorem upperSign_eq_pow (h : ∀ k, i ≤ e k) (s : Finset κ) :
    upperSign e i s = (-1) ^ s.card := by
  rw [upperSign, cubeSign_eq_one_of_forall_le, mul_one]
  intro j hj
  rcases Finset.mem_insert.1 hj with rfl | hj
  · exact le_rfl
  · obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hj
    exact h k

theorem totalD_map (A : Cube.{v} ι R) (x : ∀ t, A.obj t) (s : Finset κ) :
    totalD A x (s.map e.toEmbedding) =
      totalD (lowerFace e A) (fun s => x (s.map e.toEmbedding)) s := by
  rw [totalD_apply, Finset.sum_map]
  refine Eq.trans ?_ (totalD_apply (lowerFace e A) _ s).symm
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [res_congr A x (Finset.map_erase e.toEmbedding s k).symm _
    (Finset.map_subset_map.2 (Finset.erase_subset k s))]
  exact congrArg (· • _) (cubeSign_map e s k)

variable {e i}

theorem notMem_map_of_range_eq (he : Set.range e = {i}ᶜ) (s : Finset κ) :
    i ∉ s.map e.toEmbedding := by
  intro h
  obtain ⟨k, -, hk⟩ := Finset.mem_map.1 h
  have : i ∈ Set.range e := ⟨k, hk⟩
  simp [he] at this

theorem map_preimage_of_notMem (he : Set.range e = {i}ᶜ) {t : Finset ι} (ht : i ∉ t) :
    (t.preimage e e.injective.injOn).map e.toEmbedding = t := by
  ext j
  simp only [Finset.mem_map, Finset.mem_preimage]
  refine ⟨by rintro ⟨k, hk, rfl⟩; exact hk, fun hj => ?_⟩
  obtain ⟨k, rfl⟩ : j ∈ Set.range e := by
    rw [he]; rintro rfl; exact ht hj
  exact ⟨k, hj, rfl⟩

theorem preimage_insert_map (he : Set.range e = {i}ᶜ) (s : Finset κ) :
    (insert i (s.map e.toEmbedding)).preimage e e.injective.injOn = s := by
  ext k
  have : e k ≠ i := by
    have : e k ∈ Set.range e := ⟨k, rfl⟩
    simpa [he] using this
  simp [this]

theorem preimage_map_orderEmbedding (s : Finset κ) :
    (s.map e.toEmbedding).preimage e e.injective.injOn = s := by
  ext k
  simp

theorem exists_eq_map_or_eq_insert (he : Set.range e = {i}ᶜ) (t : Finset ι) :
    (∃ s : Finset κ, t = s.map e.toEmbedding) ∨
      ∃ s : Finset κ, t = insert i (s.map e.toEmbedding) := by
  by_cases ht : i ∈ t
  · exact Or.inr ⟨_, by rw [map_preimage_of_notMem he (Finset.notMem_erase i t),
      Finset.insert_erase ht]⟩
  · exact Or.inl ⟨_, (map_preimage_of_notMem he ht).symm⟩

theorem card_insert_map (he : Set.range e = {i}ᶜ) (s : Finset κ) :
    (insert i (s.map e.toEmbedding)).card = s.card + 1 := by
  rw [Finset.card_insert_of_notMem (notMem_map_of_range_eq he s), Finset.card_map]

theorem totalD_insert_map (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) (x : ∀ t, A.obj t)
    (s : Finset κ) :
    upperSign e i s • totalD A x (insert i (s.map e.toEmbedding)) =
      totalD (upperFace e i A)
          (fun s => upperSign e i s • x (insert i (s.map e.toEmbedding))) s +
        (-1 : ℤ) ^ s.card • ((faceMap e i A).app s).hom (x (s.map e.toEmbedding)) := by
  have hi := notMem_map_of_range_eq he s
  rw [totalD_apply, Finset.sum_insert hi, Finset.sum_map, smul_add, add_comm,
    res_congr A x (Finset.erase_insert hi) _ (Finset.subset_insert _ _), Finset.smul_sum]
  refine congrArg₂ (· + ·) (Eq.trans (Finset.sum_congr rfl fun k hk => ?_)
    (totalD_apply (upperFace e i A) _ s).symm) ?_
  · have hki : e k ≠ i := fun h => hi (Finset.mem_map.2 ⟨k, hk, h⟩)
    have h1 : (insert i (s.map e.toEmbedding)).erase (e k) =
        insert i ((s.erase k).map e.toEmbedding) := by
      rw [Finset.erase_insert_of_ne hki.symm, Finset.map_erase]; rfl
    have h2 := cubeSign_mul_erase (t := insert i (s.map e.toEmbedding)) (i := i) (j := e k)
      (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨k, hk, rfl⟩)) hki.symm
    rw [h1, Finset.erase_insert hi, cubeSign_map] at h2
    have h3 : upperSign e i s * cubeSign (insert i (s.map e.toEmbedding)) (e k) =
        cubeSign s k * upperSign e i (s.erase k) := by
      rw [upperSign, upperSign, ← Finset.card_erase_add_one hk, pow_succ]
      have a1 := cubeSign_mul_self (insert i (s.map e.toEmbedding)) i
      have a2 := cubeSign_mul_self (insert i ((s.erase k).map e.toEmbedding)) i
      generalize cubeSign (insert i (s.map e.toEmbedding)) i = a at *
      generalize cubeSign (insert i ((s.erase k).map e.toEmbedding)) i = b at *
      generalize cubeSign (insert i (s.map e.toEmbedding)) (e k) = c at *
      generalize cubeSign s k = f at *
      generalize (-1 : ℤ) ^ (s.erase k).card = g
      linear_combination (-(g * a * b)) * h2 + (g * f * b) * a1 + (g * a * c) * a2
    refine Eq.trans (congrArg (fun y => upperSign e i s • cubeSign _ (e k) • y)
      (res_congr A x h1 _ (Finset.insert_subset_insert i
        (Finset.map_subset_map.2 (Finset.erase_subset k s))))) ?_
    rw [smul_smul, h3, ← smul_smul, ← map_zsmul]
    rfl
  · rw [upperSign, smul_smul, mul_assoc, cubeSign_mul_self, mul_one]
    rfl

end Faces

section Terms

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}

variable (e) in

def termLower (A : Cube.{v} ι R) (p : ℕ) : Term A p →ₗ[R] Term (lowerFace e A) p :=
  LinearMap.pi fun s => LinearMap.proj (R := R)
    (φ := fun t : {t : Finset ι // t.card = p} => A.obj t.1)
    ⟨s.1.map e.toEmbedding, (Finset.card_map _).trans s.2⟩

theorem termLower_apply (A : Cube.{v} ι R) (p : ℕ) (x : Term A p)
    (s : {s : Finset κ // s.card = p}) :
    termLower e A p x s = x ⟨s.1.map e.toEmbedding, (Finset.card_map _).trans s.2⟩ := rfl

def termUpper (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) (p : ℕ) :
    Term A (p + 1) →ₗ[R] Term (upperFace e i A) p :=
  LinearMap.pi fun s => upperSign e i s.1 • LinearMap.proj (R := R)
    (φ := fun t : {t : Finset ι // t.card = p + 1} => A.obj t.1)
    ⟨insert i (s.1.map e.toEmbedding), by rw [card_insert_map he, s.2]⟩

theorem termUpper_apply (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) (p : ℕ) (x : Term A (p + 1))
    (s : {s : Finset κ // s.card = p}) :
    termUpper he A p x s = upperSign e i s.1 •
      x ⟨insert i (s.1.map e.toEmbedding), by rw [card_insert_map he, s.2]⟩ := rfl

variable (e i) in

noncomputable def termIncl (A : Cube.{v} ι R) (p : ℕ) :
    Term (upperFace e i A) p →ₗ[R] Term A (p + 1) :=
  LinearMap.pi fun t => if h : i ∈ t.1 then
    upperSign e i (t.1.preimage e e.injective.injOn) •
      (res A (s := insert i ((t.1.preimage e e.injective.injOn).map e.toEmbedding)) (t := t.1)
        (Finset.insert_subset h fun j hj => by
          obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hj
          exact Finset.mem_preimage.1 hk) ∘ₗ
        LinearMap.proj (R := R) (φ := fun s : Finset κ => (upperFace e i A).obj s)
          (t.1.preimage e e.injective.injOn) ∘ₗ extend (upperFace e i A) p)
    else 0

variable (e i) in

noncomputable def termSec (A : Cube.{v} ι R) (p : ℕ) :
    Term (lowerFace e A) p →ₗ[R] Term A p :=
  LinearMap.pi fun t => if i ∈ t.1 then 0 else
    res A (s := (t.1.preimage e e.injective.injOn).map e.toEmbedding) (t := t.1)
        (fun j hj => by
          obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hj
          exact Finset.mem_preimage.1 hk) ∘ₗ
        LinearMap.proj (R := R) (φ := fun s : Finset κ => (lowerFace e A).obj s)
          (t.1.preimage e e.injective.injOn) ∘ₗ extend (lowerFace e A) p

variable (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R)

theorem termIncl_apply_of_notMem {p : ℕ} (y : Term (upperFace e i A) p)
    (t : {t : Finset ι // t.card = p + 1}) (ht : i ∉ t.1) : termIncl e i A p y t = 0 := by
  rw [termIncl, LinearMap.pi_apply, dif_neg ht]; rfl

theorem termIncl_apply_insert {p : ℕ} (y : Term (upperFace e i A) p)
    (s : {s : Finset κ // s.card = p}) :
    termIncl e i A p y ⟨insert i (s.1.map e.toEmbedding), by rw [card_insert_map he, s.2]⟩ =
      upperSign e i s.1 • y s := by
  rw [termIncl, LinearMap.pi_apply, dif_pos (Finset.mem_insert_self _ _)]
  have key : ∀ (s' : Finset κ) (_ : s' = s.1) (h : insert i (s'.map e.toEmbedding) ⊆
      insert i (s.1.map e.toEmbedding)), upperSign e i s' • res A h
        (extend (upperFace e i A) p y s') = upperSign e i s.1 • y s := by
    rintro _ rfl h
    rw [extend_apply_of_eq _ y s.2]
    exact congrArg (upperSign e i s.1 • ·) (res_self A h _)
  exact key _ (preimage_insert_map he s.1) _

theorem termSec_apply_of_mem {p : ℕ} (y : Term (lowerFace e A) p)
    (t : {t : Finset ι // t.card = p}) (ht : i ∈ t.1) : termSec e i A p y t = 0 := by
  rw [termSec, LinearMap.pi_apply, if_pos ht]; rfl

include he in

theorem termSec_apply_map {p : ℕ} (y : Term (lowerFace e A) p)
    (s : {s : Finset κ // s.card = p}) :
    termSec e i A p y ⟨s.1.map e.toEmbedding, (Finset.card_map _).trans s.2⟩ = y s := by
  rw [termSec, LinearMap.pi_apply, if_neg (notMem_map_of_range_eq he s.1)]
  have key : ∀ (s' : Finset κ) (_ : s' = s.1) (h : s'.map e.toEmbedding ⊆
      s.1.map e.toEmbedding), res A h (extend (lowerFace e A) p y s') = y s := by
    rintro _ rfl h
    rw [extend_apply_of_eq _ y s.2]
    exact res_self A h _
  exact key _ (preimage_map_orderEmbedding s.1) _

@[simp]
theorem termUpper_termIncl {p : ℕ} (y : Term (upperFace e i A) p) :
    termUpper he A p (termIncl e i A p y) = y := by
  funext s
  rw [termUpper_apply, termIncl_apply_insert he]
  exact upperSign_smul_smul e i s.1 (y s)

include he in

theorem termLower_termIncl {p : ℕ} (y : Term (upperFace e i A) p) :
    termLower e A (p + 1) (termIncl e i A p y) = 0 :=
  funext fun s => termIncl_apply_of_notMem A y _ (notMem_map_of_range_eq he s.1)

include he in

theorem termLower_termSec {p : ℕ} (y : Term (lowerFace e A) p) :
    termLower e A p (termSec e i A p y) = y :=
  funext fun s => termSec_apply_map he A y s

@[simp]
theorem termUpper_termSec {p : ℕ} (y : Term (lowerFace e A) (p + 1)) :
    termUpper he A p (termSec e i A (p + 1) y) = 0 := by
  funext s
  rw [termUpper_apply, termSec_apply_of_mem A y _ (Finset.mem_insert_self _ _), smul_zero]
  rfl

theorem term_ext_faces {p : ℕ} {x y : Term A (p + 1)}
    (h₁ : termUpper he A p x = termUpper he A p y)
    (h₂ : termLower e A (p + 1) x = termLower e A (p + 1) y) : x = y := by
  funext ⟨t, ht⟩
  rcases exists_eq_map_or_eq_insert he t with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact congrFun h₂ ⟨s, (Finset.card_map _).symm.trans ht⟩
  · have hs : s.card = p := by rw [card_insert_map he] at ht; omega
    have h := congrArg (upperSign e i s • ·) (congrFun h₁ ⟨s, hs⟩)
    exact (upperSign_smul_smul e i s _).symm.trans (h.trans (upperSign_smul_smul e i s _))

include he in

theorem termLower_zero_injective : Function.Injective (termLower e A 0) := by
  intro x y h
  funext ⟨t, ht⟩
  rcases exists_eq_map_or_eq_insert he t with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact congrFun h ⟨s, (Finset.card_map _).symm.trans ht⟩
  · rw [card_insert_map he] at ht; omega

theorem termIncl_add_termSec {p : ℕ} (x : Term A (p + 1)) :
    termIncl e i A p (termUpper he A p x) + termSec e i A (p + 1) (termLower e A (p + 1) x) = x :=
  term_ext_faces he A (by simp) (by simp [termLower_termSec he, termLower_termIncl he])

include he in

theorem termSec_termLower_zero (x : Term A 0) : termSec e i A 0 (termLower e A 0 x) = x :=
  termLower_zero_injective he A (termLower_termSec he A _)

theorem termLower_d {p : ℕ} (x : Term A p) :
    termLower e A (p + 1) (d A p x) = d (lowerFace e A) p (termLower e A p x) := by
  funext s
  rw [termLower_apply, d_apply_eq_totalD A x _ (fun s => (extend_apply_of_eq A x s.2).symm),
    totalD_map]
  exact (d_apply_eq_totalD (lowerFace e A) (termLower e A p x)
    (fun s => extend A p x (s.map e.toEmbedding))
    (fun s => (extend_apply_of_eq A x ((Finset.card_map _).trans s.2)).symm) s).symm

theorem termUpper_d {p : ℕ} (x : Term A (p + 1)) :
    termUpper he A (p + 1) (d A (p + 1) x) = d (upperFace e i A) p (termUpper he A p x) +
      (-1 : ℤ) ^ (p + 1) • termMap (faceMap e i A) (p + 1) (termLower e A (p + 1) x) := by
  funext s
  rw [termUpper_apply, d_apply_eq_totalD A x _ (fun s => (extend_apply_of_eq A x s.2).symm),
    totalD_insert_map he]
  refine congrArg₂ (· + ·) (d_apply_eq_totalD _ _ _ (fun s => ?_) s).symm ?_
  · exact congrArg (upperSign e i s.1 • ·) (extend_apply_of_eq A x _).symm
  · rw [s.2, extend_apply_of_eq A x ((Finset.card_map _).trans s.2)]
    rfl

theorem termUpper_d_zero (x : Term A 0) :
    termUpper he A 0 (d A 0 x) = termMap (faceMap e i A) 0 (termLower e A 0 x) := by
  funext ⟨s, hs⟩
  rw [termUpper_apply, d_apply_eq_totalD A x _ (fun s => (extend_apply_of_eq A x s.2).symm),
    totalD_insert_map he]
  obtain rfl := Finset.card_eq_zero.1 hs
  refine (congrArg (· + _) (totalD_apply (upperFace e i A) _ ∅)).trans ?_
  rw [Finset.sum_empty, zero_add, Finset.card_empty, pow_zero, one_smul,
    extend_apply_of_eq A x ((Finset.card_map _).trans hs)]
  rfl

include he in

theorem d_termIncl {p : ℕ} (y : Term (upperFace e i A) p) :
    d A (p + 1) (termIncl e i A p y) = termIncl e i A (p + 1) (d (upperFace e i A) p y) :=
  term_ext_faces he A (by simp [termUpper_d, termLower_termIncl he])
    (by simp [termLower_d, termLower_termIncl he])

include he in

theorem d_termSec {p : ℕ} (y : Term (lowerFace e A) p) :
    d A p (termSec e i A p y) = termSec e i A (p + 1) (d (lowerFace e A) p y) +
      termIncl e i A p ((-1 : ℤ) ^ p • termMap (faceMap e i A) p y) := by
  refine term_ext_faces he A ?_
    (by simp [termLower_d, termLower_termSec he, termLower_termIncl he])
  cases p with
  | zero => simp [termUpper_d_zero, termLower_termSec he]
  | succ p => simp [termUpper_d, termLower_termSec he]

variable {A} {B : Cube.{v} ι R} (φ : A ⟶ B)

theorem termLower_termMap {p : ℕ} (x : Term A p) :
    termLower e B p (termMap φ p x) = termMap (lowerFaceMap e φ) p (termLower e A p x) := rfl

theorem termUpper_termMap {p : ℕ} (x : Term A (p + 1)) :
    termUpper he B p (termMap φ (p + 1) x) =
      termMap (upperFaceMap e i φ) p (termUpper he A p x) :=
  funext fun s => (map_zsmul (φ.app (insert i (s.1.map e.toEmbedding))).hom _ _).symm

include he in

theorem termMap_termIncl {p : ℕ} (y : Term (upperFace e i A) p) :
    termMap φ (p + 1) (termIncl e i A p y) =
      termIncl e i B p (termMap (upperFaceMap e i φ) p y) :=
  term_ext_faces he B (by simp [termUpper_termMap])
    (by simp [termLower_termMap, termLower_termIncl he])

end Terms

end Cube

section Shift

def succEmbedding : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.embeddingUp'Add 1 1

instance succEmbedding_isRelIff : succEmbedding.IsRelIff :=
  inferInstanceAs (ComplexShape.embeddingUp'Add (1 : ℕ) 1).IsRelIff

theorem succEmbedding_f (p : ℕ) : succEmbedding.f p = p + 1 := rfl

theorem succEmbedding_f_ne_zero (p : ℕ) : succEmbedding.f p ≠ 0 := Nat.succ_ne_zero p

variable {R : Type u} [Ring R]

noncomputable abbrev shiftSucc (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    CochainComplex (ModuleCat.{v} R) ℕ := K.extend succEmbedding

noncomputable abbrev shiftSuccXIso (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) :
    (shiftSucc K).X (p + 1) ≅ K.X p := K.extendXIso succEmbedding (succEmbedding_f p)

noncomputable abbrev shiftSuccHomologyIso (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) :
    (shiftSucc K).homology (p + 1) ≅ K.homology p :=
  K.extendHomologyIso succEmbedding (succEmbedding_f p)

theorem isZero_shiftSucc_X_zero (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    IsZero ((shiftSucc K).X 0) := K.isZero_extend_X _ 0 succEmbedding_f_ne_zero

theorem isZero_shiftSucc_homology_zero (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    IsZero ((shiftSucc K).homology 0) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_shiftSucc_X_zero K)

theorem shiftSucc_d (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) :
    (shiftSucc K).d (p + 1) (p + 1 + 1) =
      (shiftSuccXIso K p).hom ≫ K.d p (p + 1) ≫ (shiftSuccXIso K (p + 1)).inv :=
  K.extend_d_eq _ (succEmbedding_f p) (succEmbedding_f (p + 1))

end Shift

section Cone

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}

variable (e) in

def cubeLowerProj (A : Cube.{v} ι R) : cubeComplex A ⟶ cubeComplex (Cube.lowerFace e A) :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (Cube.termLower e A p)) fun p => by
    rw [cubeComplex_d, cubeComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (Cube.termLower_d A x).symm)

theorem cubeLowerProj_f (A : Cube.{v} ι R) (p : ℕ) :
    (cubeLowerProj e A).f p = ModuleCat.ofHom (Cube.termLower e A p) := rfl

@[reassoc]
theorem cubeLowerProj_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    cubeComplexMap φ ≫ cubeLowerProj e B =
      cubeLowerProj e A ≫ cubeComplexMap (Cube.lowerFaceMap e φ) := rfl

theorem isIso_cubeLowerProj (he : Function.Surjective e) (A : Cube.{v} ι R) :
    IsIso (cubeLowerProj e A) := by
  have : ∀ p, IsIso ((cubeLowerProj e A).f p) := fun p => by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (Cube.termLower e A p)
    have hb : Function.Bijective (fun s : {s : Finset κ // s.card = p} =>
        (⟨s.1.map e.toEmbedding, (Finset.card_map _).trans s.2⟩ : {t : Finset ι // t.card = p})) := by
      refine ⟨fun s s' h => Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h)), ?_⟩
      rintro ⟨t, ht⟩
      have h : (t.preimage e e.injective.injOn).map e.toEmbedding = t := by
        ext j
        obtain ⟨k, rfl⟩ := he j
        simp
      exact ⟨⟨t.preimage e e.injective.injOn, by rw [← ht, ← h, Finset.card_map, h]⟩,
        Subtype.ext h⟩
    exact (Equiv.piCongrLeft (fun t : {t : Finset ι // t.card = p} => A.obj t.1)
      (Equiv.ofBijective _ hb)).symm.bijective
  exact HomologicalComplex.Hom.isIso_of_components _

variable (e i) in

noncomputable def cubeInclX (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex (Cube.upperFace e i A)).X p ⟶ (cubeComplex A).X (p + 1) :=
  ModuleCat.ofHom (Cube.termIncl e i A p)

variable (e i) in

noncomputable def cubeSecX (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex (Cube.lowerFace e A)).X p ⟶ (cubeComplex A).X p :=
  ModuleCat.ofHom (Cube.termSec e i A p)

variable (e i) in

noncomputable def cubeUpperInclF (A : Cube.{v} ι R) : ∀ p : ℕ,
    (shiftSucc (cubeComplex (Cube.upperFace e i A))).X p ⟶ (cubeComplex A).X p
  | 0 => 0
  | p + 1 => (shiftSuccXIso _ p).hom ≫ cubeInclX e i A p

variable (he : Set.range e = {i}ᶜ)

noncomputable def cubeUpperIncl (A : Cube.{v} ι R) :
    shiftSucc (cubeComplex (Cube.upperFace e i A)) ⟶ cubeComplex A :=
  CochainComplex.ofHom (cubeUpperInclF e i A) fun p => by
    cases p with
    | zero => exact (isZero_shiftSucc_X_zero _).eq_of_src _ _
    | succ p =>
      change ((shiftSuccXIso _ p).hom ≫ cubeInclX e i A p) ≫ _ =
        _ ≫ (shiftSuccXIso _ (p + 1)).hom ≫ cubeInclX e i A (p + 1)
      rw [shiftSucc_d, Category.assoc, Category.assoc,
        Category.assoc, Iso.inv_hom_id_assoc, cubeComplex_d, cubeComplex_d]
      congr 1
      exact ModuleCat.hom_ext (LinearMap.ext fun x => Cube.d_termIncl he A x)

theorem cubeUpperIncl_f_succ (A : Cube.{v} ι R) (p : ℕ) :
    (cubeUpperIncl he A).f (p + 1) = (shiftSuccXIso _ p).hom ≫ cubeInclX e i A p := rfl

@[reassoc]
theorem cubeUpperIncl_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    extendMap (cubeComplexMap (Cube.upperFaceMap e i φ)) succEmbedding ≫ cubeUpperIncl he B =
      cubeUpperIncl he A ≫ cubeComplexMap φ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  cases p with
  | zero => exact (isZero_shiftSucc_X_zero _).eq_of_src _ _
  | succ p =>
    rw [comp_f, comp_f, cubeUpperIncl_f_succ, cubeUpperIncl_f_succ,
      extendMap_f _ _ (succEmbedding_f p), Category.assoc, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
    congr 1
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (Cube.termMap_termIncl he φ x).symm)

noncomputable abbrev cubeFaceSequence (A : Cube.{v} ι R) :
    ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ) :=
  ShortComplex.mk (cubeUpperIncl he A) (cubeLowerProj e A) (by
    refine HomologicalComplex.hom_ext _ _ fun p => ?_
    cases p with
    | zero => exact (isZero_shiftSucc_X_zero _).eq_of_src _ _
    | succ p =>
      rw [comp_f, cubeUpperIncl_f_succ, Category.assoc, zero_f]
      have h : cubeInclX e i A p ≫ (cubeLowerProj e A).f (p + 1) = 0 :=
        ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termLower_termIncl he A x)
      rw [h, comp_zero])

noncomputable def cubeFaceSequenceMap {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    cubeFaceSequence he A ⟶ cubeFaceSequence he B where
  τ₁ := extendMap (cubeComplexMap (Cube.upperFaceMap e i φ)) succEmbedding
  τ₂ := cubeComplexMap φ
  τ₃ := cubeComplexMap (Cube.lowerFaceMap e φ)
  comm₁₂ := cubeUpperIncl_naturality he φ
  comm₂₃ := cubeLowerProj_naturality φ

noncomputable def cubeFaceSplitting (A : Cube.{v} ι R) : ∀ p : ℕ,
    ((cubeFaceSequence he A).map (eval _ _ p)).Splitting
  | 0 =>
    { r := 0
      s := cubeSecX e i A 0
      f_r := (isZero_shiftSucc_X_zero _).eq_of_src _ _
      s_g := ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termLower_termSec he A x)
      id := by
        rw [zero_comp, zero_add]
        exact ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termSec_termLower_zero he A x) }
  | p + 1 =>
    { r := ModuleCat.ofHom (Cube.termUpper he A p) ≫
        (shiftSuccXIso (cubeComplex (Cube.upperFace e i A)) p).inv
      s := cubeSecX e i A (p + 1)
      f_r := by
        have h : ModuleCat.ofHom (Cube.termIncl e i A p) ≫
            ModuleCat.ofHom (Cube.termUpper he A p) =
            𝟙 ((cubeComplex (Cube.upperFace e i A)).X p) :=
          ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termUpper_termIncl he A x)
        let j := shiftSuccXIso (cubeComplex (Cube.upperFace e i A)) p
        have h' := congrArg (fun f => j.hom ≫ f ≫ j.inv) h
        simp only [Category.id_comp, Iso.hom_inv_id] at h'
        exact h'
      s_g := ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termLower_termSec he A x)
      id := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x =>
          Eq.trans ?_ (Cube.termIncl_add_termSec he A x))
        let j := shiftSuccXIso (cubeComplex (Cube.upperFace e i A)) p
        have h : j.hom.hom (j.inv.hom (Cube.termUpper he A p x)) = Cube.termUpper he A p x :=
          congr(($(j.inv_hom_id)).hom (Cube.termUpper he A p x))
        exact congrArg (fun y => Cube.termIncl e i A p y +
          Cube.termSec e i A (p + 1) (Cube.termLower e A (p + 1) x)) h }

theorem cubeFaceSequence_shortExact (A : Cube.{v} ι R) : (cubeFaceSequence he A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p =>
    (cubeFaceSplitting he A p).shortExact

theorem cubeFaceSequence_δ (A : Cube.{v} ι R) (p : ℕ) :
    (cubeFaceSequence_shortExact he A).δ p (p + 1) rfl ≫
        (shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).hom =
      (-1 : ℤ) ^ p • homologyMap (cubeComplexMap (Cube.faceMap e i A)) p := by
  let L := cubeComplex (Cube.lowerFace e A)
  let U := cubeComplex (Cube.upperFace e i A)
  let φ : L ⟶ U := cubeComplexMap (Cube.faceMap e i A)
  let σ : L.X p ⟶ (cubeComplex A).X p := cubeSecX e i A p
  have hσ : σ ≫ (cubeLowerProj e A).f p = 𝟙 _ :=
    ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termLower_termSec he A x)
  have hd : σ ≫ (cubeComplex A).d p (p + 1) =
      L.d p (p + 1) ≫ cubeSecX e i A (p + 1) +
        ((-1 : ℤ) ^ p • φ.f p) ≫ cubeInclX e i A p := by
    rw [cubeComplex_d, cubeComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Cube.d_termSec he A x)
  have key := (cubeFaceSequence_shortExact he A).δ_eq p (p + 1) rfl (L.iCycles p)
    (L.iCycles_d p (p + 1)) (L.iCycles p ≫ σ)
    ((Category.assoc _ _ _).trans ((congrArg (L.iCycles p ≫ ·) hσ).trans (Category.comp_id _)))
    (L.iCycles p ≫ ((-1 : ℤ) ^ p • φ.f p) ≫ (shiftSuccXIso U p).inv)
    (by
      change (L.iCycles p ≫ ((-1 : ℤ) ^ p • φ.f p) ≫ (shiftSuccXIso U p).inv) ≫
        (cubeUpperIncl he A).f (p + 1) = (L.iCycles p ≫ σ) ≫ (cubeComplex A).d p (p + 1)
      rw [cubeUpperIncl_f_succ, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
        Category.assoc, hd, Preadditive.comp_add, iCycles_d_assoc, zero_comp, zero_add])
    (p + 1 + 1) (by simp)
  have h1 : L.liftCycles (L.iCycles p) (p + 1) (by simp) (L.iCycles_d p (p + 1)) = 𝟙 _ := by
    rw [← cancel_mono (L.iCycles p), liftCycles_i, Category.id_comp]
  change L.liftCycles (L.iCycles p) (p + 1) _ _ ≫ L.homologyπ p ≫ _ =
    (shiftSucc U).liftCycles _ _ _ _ ≫ (shiftSucc U).homologyπ (p + 1) at key
  rw [h1, Category.id_comp] at key
  change _ = (-1 : ℤ) ^ p • homologyMap φ p
  rw [← cancel_epi (L.homologyπ p)]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans ?_)
  rw [Category.assoc, homologyπ_extendHomologyIso_hom, Preadditive.comp_zsmul,
    homologyπ_naturality, ← Preadditive.zsmul_comp, ← Category.assoc]
  congr 1
  rw [← cancel_mono (U.iCycles p), Category.assoc, extendCyclesIso_hom_iCycles,
    liftCycles_i_assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Preadditive.zsmul_comp, cyclesMap_i, Preadditive.comp_zsmul]

end Cone

section FiveLemma

open ComposableArrows Abelian HomologySequence

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂

theorem mono_homologyMap_τ₂ (j : ι) (h₁ : Mono (homologyMap φ.τ₁ j))
    (h₂ : Mono (homologyMap φ.τ₃ j)) (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i)) :
    Mono (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₃ _ hij
    · exact h₁
    · exact h₂
  · refine mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) ?_ h₁ h₂
    have := hS₂.mono_f
    apply mono_homologyMap_of_mono_of_not_rel
    simpa using hj

theorem epi_homologyMap_τ₂ (i : ι) (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Epi (homologyMap φ.τ₃ i)) (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Epi (homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δlast.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ _ hij
  · refine epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₂ i) ?_ h₁ h₂
    have := hS₁.epi_g
    apply epi_homologyMap_of_epi_of_not_rel
    simpa using hi

theorem quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := mono_homologyMap_τ₂ φ hS₁ hS₂ i inferInstance inferInstance fun _ _ => inferInstance
  have := epi_homologyMap_τ₂ φ hS₁ hS₂ i inferInstance inferInstance fun _ _ => inferInstance
  apply isIso_of_mono_of_epi

end FiveLemma

section Corollaries

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)

include he

theorem quasiIso_cubeComplexMap_of_faces {A B : Cube.{v} ι R} (φ : A ⟶ B)
    (h₀ : QuasiIso (cubeComplexMap (Cube.lowerFaceMap e φ)))
    (h₁ : QuasiIso (cubeComplexMap (Cube.upperFaceMap e i φ))) : QuasiIso (cubeComplexMap φ) :=
  quasiIso_τ₂ (cubeFaceSequenceMap he φ) (cubeFaceSequence_shortExact he A)
    (cubeFaceSequence_shortExact he B) ((quasiIso_extendMap_iff _ _).2 h₁) h₀

theorem cubeFaceSequence_δ_eq (A : Cube.{v} ι R) (p : ℕ) :
    (cubeFaceSequence_shortExact he A).δ p (p + 1) rfl =
      homologyMap (cubeComplexMap (Cube.faceMap e i A)) p ≫
        (Int.negOnePow p • shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).inv := by
  rw [Iso.eq_comp_inv, Preadditive.smul_iso_hom, Units.smul_def, Preadditive.comp_zsmul,
    cubeFaceSequence_δ, smul_smul, Int.coe_negOnePow_natCast, ← mul_pow]
  simp

theorem mono_cubeFaceSequence_δ_iff (A : Cube.{v} ι R) (p : ℕ) :
    Mono ((cubeFaceSequence_shortExact he A).δ p (p + 1) rfl) ↔
      Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) := by
  rw [cubeFaceSequence_δ_eq]
  exact ⟨fun h => @mono_of_mono _ _ _ _ _ _ _ h, fun _ => mono_comp _ _⟩

theorem epi_cubeFaceSequence_δ_iff (A : Cube.{v} ι R) (p : ℕ) :
    Epi ((cubeFaceSequence_shortExact he A).δ p (p + 1) rfl) ↔
      Epi (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) := by
  rw [cubeFaceSequence_δ_eq, epi_comp_iff_of_isIso]

theorem cubeComplex_exactAt_zero_iff_faces (A : Cube.{v} ι R) :
    (cubeComplex A).ExactAt 0 ↔ Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) 0) := by
  have hS := cubeFaceSequence_shortExact he A
  rw [← mono_cubeFaceSequence_δ_iff he, exactAt_iff_isZero_homology]
  exact ((hS.homology_exact₂ 0).isZero_X₂_iff.trans
    (and_iff_right ((isZero_shiftSucc_homology_zero _).eq_of_src _ _))).trans
    (hS.homology_exact₃ 0 (0 + 1) rfl).mono_g_iff.symm

theorem cubeComplex_exactAt_succ_iff_faces (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex A).ExactAt (p + 1) ↔
      Epi (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) ∧
        Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) (p + 1)) := by
  have hS := cubeFaceSequence_shortExact he A
  rw [← mono_cubeFaceSequence_δ_iff he, ← epi_cubeFaceSequence_δ_iff he,
    exactAt_iff_isZero_homology, (hS.homology_exact₃ (p + 1) (p + 1 + 1) rfl).mono_g_iff,
    (hS.homology_exact₁ p (p + 1) rfl).epi_f_iff]
  exact (hS.homology_exact₂ (p + 1)).isZero_X₂_iff

theorem cubeComplex_acyclic_iff_quasiIso_faceMap (A : Cube.{v} ι R) :
    (cubeComplex A).Acyclic ↔ QuasiIso (cubeComplexMap (Cube.faceMap e i A)) := by
  constructor
  · intro h
    rw [quasiIso_iff]
    intro p
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have := ((cubeComplex_exactAt_succ_iff_faces he A p).1 (h _)).1
    have : Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) := by
      cases p with
      | zero => exact (cubeComplex_exactAt_zero_iff_faces he A).1 (h _)
      | succ p => exact ((cubeComplex_exactAt_succ_iff_faces he A p).1 (h _)).2
    apply isIso_of_mono_of_epi
  · intro h p
    cases p with
    | zero => exact (cubeComplex_exactAt_zero_iff_faces he A).2 inferInstance
    | succ p =>
      exact (cubeComplex_exactAt_succ_iff_faces he A p).2 ⟨inferInstance, inferInstance⟩

theorem cubeComplex_exactAt_succ_of_faces (A : Cube.{v} ι R) (p : ℕ)
    (h₀ : (cubeComplex (Cube.lowerFace e A)).ExactAt (p + 1))
    (h₁ : (cubeComplex (Cube.upperFace e i A)).ExactAt p) : (cubeComplex A).ExactAt (p + 1) :=
  (cubeFaceSequence_shortExact he A).exactAt_X₂ (p + 1)
    ((extend_exactAt_iff _ _ (succEmbedding_f p)).2 h₁) h₀

theorem cubeComplex_acyclic_of_faces (A : Cube.{v} ι R)
    (h₀ : (cubeComplex (Cube.lowerFace e A)).Acyclic)
    (h₁ : (cubeComplex (Cube.upperFace e i A)).Acyclic) : (cubeComplex A).Acyclic := by
  rw [cubeComplex_acyclic_iff_quasiIso_faceMap he, quasiIso_iff]
  exact fun p => (quasiIsoAt_iff_exactAt _ p (h₀ p)).2 (h₁ p)

end Corollaries

section DegreeZero

variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem quasiIsoAt_zero_cubeComplexMap_iff {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    QuasiIsoAt (cubeComplexMap φ) 0 ↔ Set.BijOn (φ.app ∅).hom
      (LinearMap.ker (Cube.aug A)) (LinearMap.ker (Cube.aug B)) := by
  have h1 : QuasiIsoAt (cubeComplexMap φ) 0 ↔ IsIso (cyclesMap (cubeComplexMap φ) 0) := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoMk (CochainComplex.isoHomologyπ₀ (cubeComplex A))
        (CochainComplex.isoHomologyπ₀ (cubeComplex B))
        (homologyπ_naturality (cubeComplexMap φ) 0))).symm
  let j (X : Cube.{v} ι R) (x : (cubeComplex X).cycles 0) : X.obj ∅ :=
    Cube.termZeroEquiv X (((cubeComplex X).iCycles 0).hom x)
  have hj (X : Cube.{v} ι R) : Function.Injective (j X) :=
    (Cube.termZeroEquiv X).injective.comp
      ((ModuleCat.mono_iff_injective ((cubeComplex X).iCycles 0)).1 inferInstance)
  have hr (X : Cube.{v} ι R) : Set.range (j X) = LinearMap.ker (Cube.aug X) := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      have h := congr(($((cubeComplex X).iCycles_d 0 (0 + 1))).hom x)
      rw [cubeComplex_d] at h
      exact (Cube.d_zero_apply X _).symm.trans h
    · intro ha
      have ha' : (Cube.termZeroEquiv X).symm a ∈ LinearMap.ker (Cube.d X 0) := by
        rw [LinearMap.mem_ker, Cube.d_zero_apply, LinearEquiv.apply_symm_apply]
        exact ha
      refine ⟨(cubeCyclesIso X 0).inv.hom ⟨_, ha'⟩, ?_⟩
      have h := congr(($((Iso.inv_comp_eq _).2 (cubeCyclesIso_hom_subtype X 0).symm)).hom ⟨_, ha'⟩)
      exact (congrArg (Cube.termZeroEquiv X) h).trans (LinearEquiv.apply_symm_apply _ a)
  have hc (x : (cubeComplex A).cycles 0) :
      j B ((cyclesMap (cubeComplexMap φ) 0).hom x) = (φ.app ∅).hom (j A x) :=
    congrArg (Cube.termZeroEquiv B) congr(($(cyclesMap_i (cubeComplexMap φ) 0)).hom x)
  rw [h1, ConcreteCategory.isIso_iff_bijective, ← hr, ← hr]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, hc x⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      exact congrArg _ (h.1 (hj B ((hc x).trans (hxy.trans (hc y).symm))))
    · rintro _ ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := h.2 y
      exact ⟨_, ⟨x, rfl⟩, (hc x).symm⟩
  · intro h
    refine ⟨fun x y hxy => hj A (h.injOn ⟨x, rfl⟩ ⟨y, rfl⟩
      ((hc x).symm.trans ((congrArg (j B) hxy).trans (hc y)))), fun y => ?_⟩
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := h.surjOn ⟨y, rfl⟩
    exact ⟨x, hj B ((hc x).trans hx)⟩

theorem cubeComplex_acyclic_of_faces_of_bijOn {κ : Type} [LinearOrder κ] {e : κ ↪o ι} {i : ι}
    (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R)
    (h₀ : ∀ p, (cubeComplex (Cube.lowerFace e A)).ExactAt (p + 1))
    (h₁ : ∀ p, (cubeComplex (Cube.upperFace e i A)).ExactAt (p + 1))
    (h : Set.BijOn ((Cube.faceMap e i A).app ∅).hom
      (LinearMap.ker (Cube.aug (Cube.lowerFace e A)))
      (LinearMap.ker (Cube.aug (Cube.upperFace e i A)))) : (cubeComplex A).Acyclic := by
  rw [cubeComplex_acyclic_iff_quasiIso_faceMap he, quasiIso_iff]
  intro p
  cases p with
  | zero => exact (quasiIsoAt_zero_cubeComplexMap_iff _).2 h
  | succ p => exact (quasiIsoAt_iff_exactAt _ _ (h₀ p)).2 (h₁ p)

theorem cubeComplex_acyclic_of_bijective (A : Cube.{v} ι R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → Function.Bijective (Cube.res A (Finset.subset_insert i s))) :
    (cubeComplex A).Acyclic :=
  cubeComplex_exactAt_of_bijective A i hA

end DegreeZero

section Cech

variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

def cechAugX (A : Cube.{v} ι R) : A.obj ∅ ⟶ (cechComplex A).X 0 := ModuleCat.ofHom (Cube.aug A)

noncomputable def cechAugHomology (A : Cube.{v} ι R) : A.obj ∅ ⟶ (cechComplex A).homology 0 :=
  (cechComplex A).liftCycles (cechAugX A) 1 (by simp) (by
      rw [cechComplex_d A 0]
      exact ModuleCat.hom_ext (LinearMap.ext (Cube.d_aug A))) ≫
    (cechComplex A).homologyπ 0

theorem cechAugHomology_comp (A : Cube.{v} ι R) :
    cechAugHomology A ≫ (cechHomologyZeroIso A).hom ≫
      ModuleCat.ofHom (LinearMap.ker (Cube.d A 1)).subtype = ModuleCat.ofHom (Cube.aug A) := by
  rw [cechAugHomology, Category.assoc, homologyπ_cechHomologyZeroIso_hom_assoc]
  exact (congrArg (_ ≫ ·) (cechCyclesIso_hom_subtype A 0)).trans (liftCycles_i _ _ _ _ _)

@[reassoc]
theorem cechAugHomology_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    φ.app ∅ ≫ cechAugHomology B = cechAugHomology A ≫ homologyMap (cechComplexMap φ) 0 := by
  rw [cechAugHomology, cechAugHomology, Category.assoc, homologyπ_naturality, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono ((cechComplex B).iCycles 0), Category.assoc, Category.assoc, liftCycles_i,
    cyclesMap_i, liftCycles_i_assoc]
  exact ModuleCat.hom_ext (LinearMap.ext fun a => (Cube.termMap_aug φ a).symm)

theorem isIso_cechAugHomology_iff (A : Cube.{v} ι R) :
    IsIso (cechAugHomology A) ↔ (cubeComplex A).ExactAt 0 ∧ (cubeComplex A).ExactAt 1 := by
  rw [cechAugHomology, isIso_comp_right_iff, CochainComplex.isIso_liftCycles_iff, and_comm,
    cubeComplex_exactAt_zero_iff, cubeComplex_exactAt_one_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, ModuleCat.mono_iff_injective]
  refine and_congr Iff.rfl ?_
  change Function.Exact (Cube.aug A) ((cechComplex A).d 0 (0 + 1)).hom ↔ _
  rw [cechComplex_d]
  rfl

noncomputable def cechHomologySuccIso (A : Cube.{v} ι R) (p : ℕ) :
    (cechComplex A).homology (p + 1) ≅ (cubeComplex A).homology (p + 2) :=
  (cechComplex A).homologyIsoSc' p (p + 1) (p + 2) (by simp) (by simp) ≪≫
    ((cubeComplex A).homologyIsoSc' (p + 1) (p + 2) (p + 3) (by simp) (by simp)).symm

theorem cubeComplex_acyclic_iff_cech (A : Cube.{v} ι R) :
    (cubeComplex A).Acyclic ↔
      IsIso (cechAugHomology A) ∧ ∀ p, IsZero ((cechComplex A).homology (p + 1)) := by
  simp only [isIso_cechAugHomology_iff, ← exactAt_iff_isZero_homology,
    cechComplex_exactAt_succ_iff_cube]
  refine ⟨fun h => ⟨⟨h _, h _⟩, fun _ => h _⟩, fun h p => ?_⟩
  match p with
  | 0 => exact h.1.1
  | 1 => exact h.1.2
  | p + 2 => exact h.2 p

theorem cubeComplex_acyclic_iff_exact (A : Cube.{v} ι R) :
    (cubeComplex A).Acyclic ↔ Function.Injective (Cube.aug A) ∧
      Function.Exact (Cube.aug A) (Cube.d A 1) ∧
        ∀ p, Function.Exact (Cube.d A (p + 1)) (Cube.d A (p + 2)) := by
  rw [cubeComplex_acyclic_iff_cech, isIso_cechAugHomology_iff, cubeComplex_exactAt_zero_iff,
    cubeComplex_exactAt_one_iff, and_assoc]
  simp only [← exactAt_iff_isZero_homology, cechComplex_exactAt_succ_iff]

theorem quasiIsoAt_zero_cechAug_iff (A : Cube.{v} ι R) :
    QuasiIsoAt (cechAug A) 0 ↔ (cubeComplex A).ExactAt 0 ∧ (cubeComplex A).ExactAt 1 := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros _ rfl rfl rfl, and_comm,
    cubeComplex_exactAt_zero_iff, cubeComplex_exactAt_one_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, ModuleCat.mono_iff_injective]
  change Function.Injective ((cechAug A).f 0).hom ∧
    Function.Exact ((cechAug A).f 0).hom ((cechComplex A).d 0 (0 + 1)).hom ↔ _
  rw [cechComplex_d, cechAug_f_zero]
  rfl

theorem cubeComplex_acyclic_iff_quasiIso_cechAug (A : Cube.{v} ι R) :
    (cubeComplex A).Acyclic ↔ QuasiIso (cechAug A) := by
  rw [cubeComplex_acyclic_iff_cech, isIso_cechAugHomology_iff, ← quasiIsoAt_zero_cechAug_iff,
    quasiIso_iff]
  have h (p : ℕ) : QuasiIsoAt (cechAug A) (p + 1) ↔ IsZero ((cechComplex A).homology (p + 1)) := by
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ p),
      exactAt_iff_isZero_homology]
  refine ⟨fun H p => ?_, fun H => ⟨H 0, fun p => (h p).1 (H _)⟩⟩
  cases p with
  | zero => exact H.1
  | succ p => exact (h p).2 (H.2 p)

end Cech

section Main

variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

abbrev otherDirections (i : ι) : {j : ι // j ≠ i} ↪o ι := OrderEmbedding.subtype _

theorem range_otherDirections (i : ι) : Set.range (otherDirections i) = {i}ᶜ := by
  ext j
  exact ⟨by rintro ⟨k, rfl⟩; exact k.2, fun h => ⟨⟨j, h⟩, rfl⟩⟩

theorem cube_cone_of_faces {κ : Type} [LinearOrder κ] {e : κ ↪o ι} {i : ι}
    (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) :
    (∃ hS : (ShortComplex.mk (cubeUpperIncl he A) (cubeLowerProj e A)
        (cubeFaceSequence he A).zero).ShortExact,
      (∀ p, Nonempty ((cubeFaceSequence he A).map (eval _ _ p)).Splitting) ∧
      ∀ p, hS.δ p (p + 1) rfl ≫
          (shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).hom =
        (-1 : ℤ) ^ p • homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) ∧
    ((∀ s : Finset ι, i ∉ s → Function.Bijective (Cube.res A (Finset.subset_insert i s))) →
      (cubeComplex A).Acyclic) ∧
    (∀ (B : Cube.{v} ι R) (φ : A ⟶ B), QuasiIso (cubeComplexMap (Cube.lowerFaceMap e φ)) →
      QuasiIso (cubeComplexMap (Cube.upperFaceMap e i φ)) → QuasiIso (cubeComplexMap φ)) ∧
    ((cubeComplex A).Acyclic ↔
      IsIso (cechAugHomology A) ∧ ∀ p, IsZero ((cechComplex A).homology (p + 1))) :=
  ⟨⟨cubeFaceSequence_shortExact he A, fun p => ⟨cubeFaceSplitting he A p⟩,
      cubeFaceSequence_δ he A⟩,
    cubeComplex_acyclic_of_bijective A i, fun _ φ => quasiIso_cubeComplexMap_of_faces he φ,
    cubeComplex_acyclic_iff_cech A⟩

example (A : Cube.{v} ι R) (i : ι) : (cubeFaceSequence (range_otherDirections i) A).ShortExact :=
  cubeFaceSequence_shortExact _ A

example {n : ℕ} (A : Cube.{v} (Fin (n + 1)) R) (i : Fin (n + 1)) :
    (cubeFaceSequence (e := Fin.succAboveOrderEmb i) (Fin.range_succAbove i) A).ShortExact :=
  cubeFaceSequence_shortExact _ A

end Main

end GlobalTheory
