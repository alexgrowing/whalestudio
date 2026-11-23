import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.ConjModelTr

def Tw (X : Type) : Type := X

instance (X : Type) [AddCommGroup X] : AddCommGroup (Tw X) := inferInstanceAs (AddCommGroup X)
instance (X : Type) [AddCommGroup X] [Module ℂ X] : Module ℂ (Tw X) := Module.compHom X (starRingEnd ℂ)

section Gen

variable {ι : Type} [Fintype ι] {X₁ X : ι → Type} [∀ i, AddCommGroup (X₁ i)] [∀ i, Module ℂ (X₁ i)]
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

theorem comp_update [DecidableEq ι] (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (v : ∀ i, X₁ i) (i : ι) (x : X₁ i) :
    (fun j => c j (Function.update v i x j)) = Function.update (fun j => c j (v j)) i (c i x) :=
  funext fun j => Function.apply_update (fun j => (c j : X₁ j → X j)) v i x j

def cmul (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) : MultilinearMap ℂ X₁ (Tw (⨂[ℂ] i, X i)) where
  toFun v := (PiTensorProduct.tprod ℂ (fun i => c i (v i)) : ⨂[ℂ] i, X i)
  map_update_add' v i x y := by
    classical
    show PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i (x + y) j)) =
      PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i x j)) +
        PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i y j))
    rw [comp_update, comp_update, comp_update, map_add, MultilinearMap.map_update_add]
  map_update_smul' v i a x := by
    classical
    show PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i (a • x) j)) =
      (starRingEnd ℂ a) • PiTensorProduct.tprod ℂ (fun j => c j (Function.update v i x j))
    rw [comp_update, comp_update, map_smulₛₗ, MultilinearMap.map_update_smul]

def kapF (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) : (⨂[ℂ] i, X₁ i) →+ ⨂[ℂ] i, X i where
  toFun x := (PiTensorProduct.lift (cmul c) x : Tw (⨂[ℂ] i, X i))
  map_zero' := map_zero (PiTensorProduct.lift (cmul c))
  map_add' x y := map_add (PiTensorProduct.lift (cmul c)) x y

theorem kapF_tprod (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (v : ∀ i, X₁ i) :
    kapF c (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun i => c i (v i)) := by
  show (PiTensorProduct.lift (cmul c) (PiTensorProduct.tprod ℂ v) : Tw (⨂[ℂ] i, X i)) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem kapF_smul (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (r : ℂ) (x : ⨂[ℂ] i, X₁ i) :
    kapF c (r • x) = starRingEnd ℂ r • kapF c x := by
  show (PiTensorProduct.lift (cmul c) (r • x) : Tw (⨂[ℂ] i, X i)) = _
  rw [map_smul]
  rfl

theorem kapF_symm (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (x : ⨂[ℂ] i, X₁ i) :
    kapF (fun i => (c i).symm) (kapF c x) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [kapF_smul, kapF_smul, kapF_tprod, kapF_tprod]; simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def kap (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) : (⨂[ℂ] i, X₁ i) ≃+ ⨂[ℂ] i, X i where
  toFun := kapF c
  invFun := kapF fun i => (c i).symm
  left_inv := kapF_symm c
  right_inv y := by
    have := kapF_symm (fun i => (c i).symm) y
    simpa using this
  map_add' := map_add (kapF c)

theorem kap_tprod (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (v : ∀ i, X₁ i) :
    kap c (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun i => c i (v i)) := kapF_tprod c v

theorem kap_smul (c : ∀ i, X₁ i ≃ₛₗ[starRingEnd ℂ] X i) (r : ℂ) (x : ⨂[ℂ] i, X₁ i) :
    kap c (r • x) = starRingEnd ℂ r • kap c x := kapF_smul c r x

end Gen

section Model

open GlobalTheory.ConjDS

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def cM (M : DSModel V S) (τ : D.what₂.Tau) : (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := GlobalTheory.ConjDS.cj (M.H τ)

theorem rep_conjModel (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : (conjModel M).H τ) : cM M τ ((conjModel M).rep τ g w) = M.rep τ g (cM M τ w) := by
  have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
    rw [inv_submatrix_equiv]
    have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (M.fr τ * g * (M.fr τ)⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  show M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cM M τ w) = M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cM M τ w)
  rw [e]

theorem sm_iff (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) (w : (conjModel M).H τ) :
    w ∈ (conjModel M).sm τ ↔ cM M τ w ∈ M.sm τ :=
  (GlobalTheory.ConjMult.conj_mult θ M (conjModel M) (cM M) (fun τ g _ w => rep_conjModel M τ g w)).1 τ w

def csm (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) : (conjModel M).sm τ ≃ₗ⋆[ℂ] M.sm τ where
  toFun w := ⟨cM M τ (w : (conjModel M).H τ), (sm_iff θ M τ w).1 w.2⟩
  invFun w := ⟨(cM M τ).symm (w : M.H τ), (sm_iff θ M τ _).2 (by simpa using w.2)⟩
  map_add' x y := Subtype.ext (map_add (cM M τ) _ _)
  map_smul' a x := Subtype.ext (map_smulₛₗ (cM M τ) _ _)
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

theorem csm_val (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) (w : (conjModel M).sm τ) :
    ((csm θ M τ w : M.sm τ) : M.H τ) = cM M τ (w : (conjModel M).H τ) := rfl

def chs (M : DSModel V S) (τ : D.what₂.Tau) : (conjModel M).H τ ≃ₗ⋆[ℂ] M.H τ := (cM M τ).toLinearEquiv

theorem incl_kap (θ : InfFam D) (M : DSModel V S) (x : SmT (conjModel M)) :
    inclT M (kap (csm θ M) x) = kap (chs M) (inclT (conjModel M) x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [kap_smul, map_smul, map_smul, kap_smul, kap_tprod, inclT, inclT, PiTensorProduct.map_tprod,
      PiTensorProduct.map_tprod, kap_tprod]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem act_kap (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (z : ⨂[ℂ] ρ, (conjModel M).H ρ) :
    kap (chs M) (actT (conjModel M) τ g z) = actT M τ g (kap (chs M) z) := by
  classical
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, kap_smul, kap_smul, map_smul, actT, actT, PiTensorProduct.map_tprod, kap_tprod, kap_tprod,
      PiTensorProduct.map_tprod]
    congr 2
    funext ρ
    by_cases h : ρ = τ
    · subst h
      simp only [Function.update_self]
      exact rep_conjModel M ρ g (f ρ)
    · simp only [Function.update_of_ne h]
      rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem ell_kap (M : DSModel V S) (w₁ : ∀ τ, (conjModel M).H τ) (z : ⨂[ℂ] ρ, (conjModel M).H ρ) :
    ellT (conjModel M) w₁ z = starRingEnd ℂ (ellT M (fun τ => cM M τ (w₁ τ)) (kap (chs M) z)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, kap_smul, map_smul, kap_tprod, ellT, ellT, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, smul_eq_mul,
      map_mul, map_prod, Complex.conj_conj]
    congr 1
    refine Finset.prod_congr rfl fun ρ _ => ?_
    change ⟪(cM M ρ (f ρ) : M.H ρ), cM M ρ (w₁ ρ)⟫_ℂ = starRingEnd ℂ ⟪(cM M ρ (w₁ ρ) : M.H ρ), cM M ρ (f ρ)⟫_ℂ
    exact (inner_conj_symm (𝕜 := ℂ) _ _).symm
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end Model

section Main

open GlobalTheory.ConjDS

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem cart_conjModel (M : DSModel V S) (τ : D.what₂.Tau) : cart (conjModel M) τ = cart M τ := by
  unfold cart
  show ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹ * Formalism.REAL.Jm (fun a => M.ε τ a.rev) *
      (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) = (M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) * M.fr τ
  rw [inv_submatrix_equiv, ← rv_Jm (ε := fun a => M.ε τ a.rev) (ε' := M.ε τ) (fun a => by simp), rv,
    submatrix_mul_equiv, submatrix_mul_equiv]
  simp

theorem act_iff (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x y : SmT (conjModel M)) :
    inclT (conjModel M) y = actT (conjModel M) τ g (inclT (conjModel M) x) ↔
      inclT M (kap (csm θ M) y) = actT M τ g (inclT M (kap (csm θ M) x)) := by
  rw [incl_kap, incl_kap, ← act_kap]
  exact (kap (chs M)).injective.eq_iff.symm

theorem ell_inv (M : DSModel V S) (w : ∀ τ, M.H τ) (z : ⨂[ℂ] ρ, (conjModel M).H ρ) :
    ellT M w (kap (chs M) z) = starRingEnd ℂ (ellT (conjModel M) (fun τ => (cM M τ).symm (w τ)) z) := by
  rw [ell_kap, Complex.conj_conj]
  congr 2

theorem der_iff (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x y : SmT (conjModel M)) : DerT (conjModel M) τ Y x y ↔ DerT M τ Y (kap (csm θ M) x) (kap (csm θ M) y) := by
  unfold DerT
  constructor
  · intro h w
    have e1 : (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • Y)) (inclT M (kap (csm θ M) x)))) =
        fun t : ℝ => star (ellT (conjModel M) (fun τ => (cM M τ).symm (w τ))
          (actT (conjModel M) τ (NormedSpace.exp (t • Y)) (inclT (conjModel M) x))) := by
      funext t
      rw [incl_kap, ← act_kap, ell_inv]
      rfl
    have e2 : ellT M w (inclT M (kap (csm θ M) y)) =
        star (ellT (conjModel M) (fun τ => (cM M τ).symm (w τ)) (inclT (conjModel M) y)) := by
      rw [incl_kap, ell_inv]
      rfl
    rw [e1, e2]
    exact (h _).star
  · intro h w₁
    have e1 : (fun t : ℝ => ellT (conjModel M) w₁ (actT (conjModel M) τ (NormedSpace.exp (t • Y)) (inclT (conjModel M) x))) =
        fun t : ℝ => star (ellT M (fun τ => cM M τ (w₁ τ))
          (actT M τ (NormedSpace.exp (t • Y)) (inclT M (kap (csm θ M) x)))) := by
      funext t
      rw [ell_kap, act_kap, ← incl_kap]
      rfl
    have e2 : ellT (conjModel M) w₁ (inclT (conjModel M) y) =
        star (ellT M (fun τ => cM M τ (w₁ τ)) (inclT M (kap (csm θ M) y))) := by
      rw [ell_kap, ← incl_kap]
      rfl
    rw [e1, e2]
    exact (h _).star

theorem ell_field (θ : InfFam D) (M : DSModel V S) (w₁ : ∀ τ, (conjModel M).H τ) :
    ∃ w : ∀ τ, M.H τ, ∀ x, ellT (conjModel M) w₁ (inclT (conjModel M) x) =
      starRingEnd ℂ (ellT M w (inclT M (kap (csm θ M) x))) :=
  ⟨fun τ => cM M τ (w₁ τ), fun x => by rw [ell_kap, incl_kap]⟩

theorem mult_fw (θ : InfFam D) (M : DSModel V S) : ∀ F ∈ MultT θ M ∅ 1, ∃ F₁ ∈ MultT θ (conjModel M) ∅ 1,
    ∀ x g, F₁ x g = starRingEnd ℂ (F (kap (csm θ M) x) g) := by
  intro F hF
  have hT := (mem_multT θ M ∅ 1 F).1 hF
  obtain ⟨T', hT', hv⟩ :=
    (GlobalTheory.ConjMult.conj_mult θ M (conjModel M) (cM M) (fun τ g _ w => rep_conjModel M τ g w)).2 ∅ 1 _ hT
  have e1 : (fun k => star ((1 : GA D V → ℂ) k)) = 1 := by funext k; simp
  rw [e1] at hT'
  refine ⟨PiTensorProduct.lift T', (mem_multT θ _ ∅ 1 _).2 (by simpa using hT'), fun x g => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, kap_smul, map_smul, PiTensorProduct.lift.tprod, kap_tprod]
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rw [hv f (fun i => csm θ M i (f i)) (fun τ => rfl) g]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hx, hy]

theorem mult_bw (θ : InfFam D) (M : DSModel V S) : ∀ F₁ ∈ MultT θ (conjModel M) ∅ 1, ∃ F ∈ MultT θ M ∅ 1,
    ∀ x g, F₁ x g = starRingEnd ℂ (F (kap (csm θ M) x) g) := by
  intro F₁ hF
  have hT := (mem_multT θ (conjModel M) ∅ 1 F₁).1 hF
  have hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w,
      (cM M τ).symm (M.rep τ g w) = (conjModel M).rep τ g ((cM M τ).symm w) := by
    intro τ g _ w
    apply (cM M τ).injective
    rw [LinearIsometryEquiv.apply_symm_apply, rep_conjModel, LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨T', hT', hv⟩ :=
    (GlobalTheory.ConjMult.conj_mult θ (conjModel M) M (fun τ => (cM M τ).symm) hc).2 ∅ 1 _ hT
  have e1 : (fun k => star ((1 : GA D V → ℂ) k)) = 1 := by funext k; simp
  rw [e1] at hT'
  refine ⟨PiTensorProduct.lift T', (mem_multT θ _ ∅ 1 _).2 (by simpa using hT'), fun x g => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, kap_smul, map_smul, kap_tprod, PiTensorProduct.lift.tprod]
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rw [hv (fun i => csm θ M i (f i)) f (fun τ => by simp [csm_val]) g]
    simp [PiTensorProduct.lift_symm]
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hx, hy]

theorem modelTr_conjModel (θ : InfFam D) (M : DSModel V S) :
    ModelTr (starRingEnd ℂ) false θ (V := V) (conjModel M) M (kap (csm θ M)) where
  smul c x := kap_smul _ c x
  cart τ := cart_conjModel M τ
  act τ g _ x y := act_iff θ M τ g x y
  der τ Y _ x y := der_iff θ M τ Y x y
  ell w₁ := ell_field θ M w₁
  vec v₁ := ⟨fun τ => csm θ M τ (v₁ τ), kap_tprod _ _, fun τ => rfl⟩
  mult := mult_fw θ M
  mult' := mult_bw θ M

end Main

theorem exists_conjModelTr : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S), ∃ (M₁ : DSModel (sgn false V) fun τ => dualPar (S τ)) (κ : SmT M₁ ≃+ SmT M),
      ModelTr (starRingEnd ℂ) false θ M₁ M κ := by
  intro D θ _ V S M
  exact ⟨GlobalTheory.ConjDS.conjModel M, kap (csm θ M), modelTr_conjModel θ M⟩

end GlobalTheory.ConjModelTr

end
