import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThK.PlaneCo

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Glue

variable {R : Type} [CommRing R] {κ κ' κ₁ : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁]

def glue (eq : κ ≃ κ' ⊕ κ₁) (a : κ' → R) (b : κ₁ → R) : κ → R := fun k => Sum.elim a b (eq k)

def glueEquiv (eq : κ ≃ κ' ⊕ κ₁) : ((κ' → R) × (κ₁ → R)) ≃ₗ[R] (κ → R) :=
  (LinearEquiv.sumArrowLequivProdArrow κ' κ₁ R R).symm.trans (LinearEquiv.funCongrLeft R R eq)

theorem glueEquiv_apply (eq : κ ≃ κ' ⊕ κ₁) (a : κ' → R) (b : κ₁ → R) : glueEquiv eq (a, b) = glue eq a b := by
  funext k
  simp only [glueEquiv, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, glue]
  rcases h : eq k with k' | k₁ <;> simp [LinearMap.funLeft, h, LinearEquiv.sumArrowLequivProdArrow]

theorem glue_dot (eq : κ ≃ κ' ⊕ κ₁) (a a' : κ' → R) (b b' : κ₁ → R) :
    glue eq a b ⬝ᵥ glue eq a' b' = a ⬝ᵥ a' + b ⬝ᵥ b' := by
  simp only [dotProduct, glue]
  rw [← Equiv.sum_comp eq.symm, Fintype.sum_sum_type]
  simp

def glueDarboux {V V₁ : Type} [AddCommGroup V] [Module R V] [AddCommGroup V₁] [Module R V₁] {Bf : V → V → R}
    {B₁ : V₁ → V₁ → R} (d₁ : Darboux B₁ κ₁) (eq : κ ≃ κ' ⊕ κ₁) (T : V ≃ₗ[R] ((κ' → R) × (κ' → R)) × V₁)
    (hB : ∀ w w', Bf w w' = (T w).1.1 ⬝ᵥ (T w').1.2 - (T w').1.1 ⬝ᵥ (T w).1.2 + B₁ (T w).2 (T w').2) : Darboux Bf κ where
  e := (T.trans ((LinearEquiv.refl R _).prodCongr d₁.e)).trans
    ((LinearEquiv.prodProdProdComm R _ _ _ _).trans ((glueEquiv eq).prodCongr (glueEquiv eq)))
  form w w' := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.prodProdProdComm_apply, glueEquiv_apply, glue_dot, hB w w', d₁.form]
    ring

theorem glueDarboux_e {V V₁ : Type} [AddCommGroup V] [Module R V] [AddCommGroup V₁] [Module R V₁] {Bf : V → V → R}
    {B₁ : V₁ → V₁ → R} (d₁ : Darboux B₁ κ₁) (eq : κ ≃ κ' ⊕ κ₁) (T : V ≃ₗ[R] ((κ' → R) × (κ' → R)) × V₁)
    (hB : ∀ w w', Bf w w' = (T w).1.1 ⬝ᵥ (T w').1.2 - (T w').1.1 ⬝ᵥ (T w).1.2 + B₁ (T w).2 (T w').2) (w : V) :
    (glueDarboux d₁ eq T hB).e w = (glue eq (T w).1.1 (d₁.e (T w).2).1, glue eq (T w).1.2 (d₁.e (T w).2).2) := by
  simp [glueDarboux, glueEquiv_apply]

end Glue

section Plane

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def planeMat {n n₁ : ℕ} (H : Plane E n n₁) : Matrix (Fin n) (Fin n₁ ⊕ Fin 2) E :=
  Matrix.of fun i k => Sum.elim (fun j => H.ι i j) (fun t : Fin 2 => if t = 0 then H.x i else H.y i) k

open Classical in

def planeCoef {n n₁ : ℕ} (H : Plane E n n₁) : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E :=
  if h : n₁ + 2 = n then
    ((planeMat H).submatrix id (finSumFinEquiv.trans (finCongr h)).symm)⁻¹.submatrix
      (finSumFinEquiv.trans (finCongr h)) id
  else 0

def planeGram (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) :
    Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E :=
  (planeMat H)ᵀ * J * (planeMat H).map σ

abbrev Ic (d₁ n₁ : ℕ) : Type := (Fin d₁ ⊕ Fin 2) ⊕ Fin n₁

abbrev Kc (F E : Type) [Field F] [Field E] [Algebra F E] (d₁ n₁ : ℕ) : Type := Ic d₁ n₁ × Fin (Module.finrank F E)

def posS {d₁ n₁ : ℕ} : Ic d₁ n₁ → (Fin n₁ ⊕ Fin 2) × (Fin d₁ ⊕ Fin 2)
  | .inl j => (.inr 1, j)
  | .inr a => (.inl a, .inr 1)

def posT {d₁ n₁ : ℕ} : Ic d₁ n₁ → (Fin n₁ ⊕ Fin 2) × (Fin d₁ ⊕ Fin 2)
  | .inl j => (.inr 0, j)
  | .inr a => (.inl a, .inr 0)

variable (F E) in

def bE : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E

variable (F E) in

def bE' : Module.Basis (Fin (Module.finrank F E)) F E :=
  (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) (bE F E)

variable (F E) in

def bA : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) (bE F E)

variable (F E) in

def bA' : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) (bE' F E)

def coefLin {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) where
  toFun u := incM F (planeCoef H) * u * (incM F (planeCoef H'))ᵀ
  map_add' a b := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c u := by simp [Matrix.mul_smul, Matrix.smul_mul]

def sI {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (u : Matrix (Fin n) (Fin d) (AE F E)) (k : Ic d₁ n₁) :
    AE F E := coefLin H H' u (posS k).1 (posS k).2

def tI {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (u : Matrix (Fin n) (Fin d) (AE F E)) (k : Ic d₁ n₁) :
    AE F E := coefLin H H' u (posT k).1 (posT k).2

def pairI (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁) (H' : Plane E d d₁)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (k : Ic d₁ n₁) : AE F E :=
  -∑ m, inclR (F := F) (AF F) (planeGram σ X.J H (posS k).1 (posT m).1 * planeGram σ W.J H' (posS k).2 (posT m).2) *
    cA σ (tI H H' u m)

theorem tI_add {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (a b : Matrix (Fin n) (Fin d) (AE F E))
    (k : Ic d₁ n₁) : tI H H' (a + b) k = tI H H' a k + tI H H' b k := by
  simp only [tI, map_add, Matrix.add_apply]

theorem tI_smul {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (c : AF F) (a : Matrix (Fin n) (Fin d) (AE F E))
    (k : Ic d₁ n₁) : tI H H' (c • a) k = c • tI H H' a k := by
  simp only [tI, map_smul, Matrix.smul_apply]

theorem sI_add {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (a b : Matrix (Fin n) (Fin d) (AE F E))
    (k : Ic d₁ n₁) : sI H H' (a + b) k = sI H H' a k + sI H H' b k := by
  simp only [sI, map_add, Matrix.add_apply]

theorem sI_smul {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (c : AF F) (a : Matrix (Fin n) (Fin d) (AE F E))
    (k : Ic d₁ n₁) : sI H H' (c • a) k = c • sI H H' a k := by
  simp only [sI, map_smul, Matrix.smul_apply]

theorem pairI_add (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (a b : Matrix (Fin n) (Fin d) (AE F E)) (k : Ic d₁ n₁) :
    pairI σ X W H H' (a + b) k = pairI σ X W H H' a k + pairI σ X W H H' b k := by
  simp only [pairI, tI_add, map_add, mul_add, Finset.sum_add_distrib, neg_add]

theorem pairI_smul (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (c : AF F) (a : Matrix (Fin n) (Fin d) (AE F E)) (k : Ic d₁ n₁) :
    pairI σ X W H H' (c • a) k = c • pairI σ X W H H' a k := by
  simp only [pairI, tI_smul, AlgHom.map_smul_of_tower, mul_smul_comm, ← Finset.smul_sum, smul_neg]

def planeT (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁) (H' : Plane E d d₁) :
    Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F]
      ((Kc F E d₁ n₁ → AF F) × (Kc F E d₁ n₁ → AF F)) × Matrix (Fin n₁) (Fin d₁) (AE F E) where
  toFun u := ((fun k => (bA F E).repr (sI H H' u k.1) k.2, fun k => (bA' F E).repr (pairI σ X W H H' u k.1) k.2),
    (coefLin H H' u).submatrix Sum.inl Sum.inl)
  map_add' a b := by
    refine Prod.ext (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) ?_
    · simp only [sI_add, map_add, Finsupp.add_apply, Prod.fst_add, Pi.add_apply]
    · simp only [pairI_add, map_add, Finsupp.add_apply, Prod.snd_add, Prod.fst_add, Pi.add_apply]
    · ext i j; simp only [map_add, Matrix.submatrix_apply, Prod.snd_add, Matrix.add_apply]
  map_smul' c u := by
    refine Prod.ext (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) ?_
    · simp only [sI_smul, map_smul, Finsupp.smul_apply, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    · simp only [pairI_smul, map_smul, Finsupp.smul_apply, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply,
        smul_eq_mul]
    · ext i j; simp only [map_smul, Matrix.submatrix_apply, Prod.smul_snd, RingHom.id_apply, Matrix.smul_apply]

end Plane

section Vac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latS (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁) (H' : Plane E d d₁)
    (v : Pl F) : Set (Kc F E d₁ n₁ → Fv F v) :=
  {y | ∃ γ ∈ latAtV X W v, ∀ k, y k = evFin F v ((planeT σ X W H H' γ).1.1 k)}

def vacS (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁) (H' : Plane E d d₁)
    (v : Pl F) : (Kc F E d₁ n₁ → Fv F v) → ℂ :=
  Set.indicator (latS σ X W H H' v) 1

end Vac

section Fun

variable {R : Type} [CommRing R] {κ κ' κ₁ : Type}

def vacGlue (eq : κ ≃ κ' ⊕ κ₁) (l : (κ' → R) → ℂ) (φ : (κ₁ → R) → ℂ) : (κ → R) → ℂ :=
  fun x => l (fun k => x (eq.symm (.inl k))) * φ (fun k => x (eq.symm (.inr k)))

def restr (eq : κ ≃ κ' ⊕ κ₁) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ) where
  toFun Φ x := Φ (glue eq 0 x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vacGlue_indicator {R : Type} [CommRing R] {κ κ' κ₁ : Type} (eq : κ ≃ κ' ⊕ κ₁) (S : Set R) :
    vacGlue eq (Set.indicator {y : κ' → R | ∀ k, y k ∈ S} 1) (Set.indicator {y : κ₁ → R | ∀ k, y k ∈ S} 1) =
      Set.indicator {y : κ → R | ∀ k, y k ∈ S} 1 := by
  funext x
  have key : (∀ k, x k ∈ S) ↔ (∀ k, x (eq.symm (.inl k)) ∈ S) ∧ ∀ k, x (eq.symm (.inr k)) ∈ S := by
    constructor
    · intro h; exact ⟨fun k => h _, fun k => h _⟩
    · rintro ⟨h1, h2⟩ k
      have hk := eq.symm_apply_apply k
      rcases h : eq k with k' | k'
      · rw [h] at hk; rw [← hk]; exact h1 k'
      · rw [h] at hk; rw [← hk]; exact h2 k'
  unfold vacGlue
  by_cases h1 : ∀ k, x (eq.symm (.inl k)) ∈ S
  · by_cases h2 : ∀ k, x (eq.symm (.inr k)) ∈ S
    · rw [Set.indicator_of_mem (s := {y : κ' → R | ∀ k, y k ∈ S}) h1,
        Set.indicator_of_mem (s := {y : κ₁ → R | ∀ k, y k ∈ S}) h2,
        Set.indicator_of_mem (s := {y : κ → R | ∀ k, y k ∈ S}) (key.2 ⟨h1, h2⟩)]
      simp
    · rw [Set.indicator_of_notMem (s := {y : κ₁ → R | ∀ k, y k ∈ S}) h2,
        Set.indicator_of_notMem (s := {y : κ → R | ∀ k, y k ∈ S}) (fun h => h2 (key.1 h).2)]
      simp
  · rw [Set.indicator_of_notMem (s := {y : κ' → R | ∀ k, y k ∈ S}) h1,
      Set.indicator_of_notMem (s := {y : κ → R | ∀ k, y k ∈ S}) (fun h => h1 (key.1 h).1)]
    simp

end Fun

end GlobalTheory.ThK.PlaneCo
