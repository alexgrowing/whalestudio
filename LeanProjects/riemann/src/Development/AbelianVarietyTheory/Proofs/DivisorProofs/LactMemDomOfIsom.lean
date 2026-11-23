import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem hermC_of_isom (G : Matrix (Fin r) (Fin r) E) {γ : GL (Fin r) E}
    (hγ : ∀ v w, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = herm G v w)
    (τ : E →+* ℂ) (v w : Fin r → ℂ) :
    hermC τ G ((γ : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E).map τ *ᵥ w) = hermC τ G v w := by
  rw [GlobalTheory.LevelCusp.hermC_of_herm (ε := 1) (fun v w => by rw [hγ, one_mul]), map_one, one_mul]

theorem lact_mem_dom_of_isom (M : TwoLevels E r U C) {γ : GL (Fin r) E}
    (hγ : ∀ v w, herm M.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = herm M.Gm v w)
    {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact γ x ∈ M.dom := fun τ => by
  have hd : ∀ i, dmin M.Gm (lact γ x) τ i = dmin M.Gm x τ i := fun i => by
    unfold dmin
    congr 1
    ext p q
    exact hermC_of_isom M.Gm hγ τ.1 (col (mat x τ) p) (col (mat x τ) q)
  refine ⟨?_, fun i => by rw [hd]; exact (hx τ).2 i⟩
  have e : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx τ).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

theorem lact_tr_mem (M : TwoLevels E r U C) (u : U) (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    lact (M.tr u c) x ∈ M.dom :=
  lact_mem_dom_of_isom M (M.tr_herm u c) hx

theorem lact_Γ_mem (M : TwoLevels E r U C) (c : C) {γ : GL (Fin r) E} (hγ : γ ∈ (M.comp c).Γ)
    {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact γ x ∈ M.dom :=
  lact_mem_dom_of_isom M (fun v w => by
    have := ((M.comp c).Γ_stab γ hγ).1 v w
    rwa [M.comp_Gm c] at this) hx

def Lmap (M : TwoLevels E r U C) (u : U) (c : C) (x : M.dom) : M.dom :=
  ⟨lact (M.tr u c) x.1, lact_tr_mem M u c x.2⟩

def pb (M : TwoLevels E r U C) (u : U) : (C → M.dom → ℂ) →ₐ[ℂ] (C → M.dom → ℂ) where
  toFun f := fun c x => f (u • c) (Lmap M u c x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem pb_apply (M : TwoLevels E r U C) (u : U) (f : C → M.dom → ℂ) (c : C) (x : M.dom) :
    pb M u f c x = f (u • c) (Lmap M u c x) := rfl

def IsHol (M : TwoLevels E r U C) (f : C → M.dom → ℂ) : Prop :=
  ∀ c, ∃ G : Frame M.Ψ r → ℂ, DifferentiableOn ℂ G M.dom ∧ ∀ x : M.dom, f c x = G x.1

def IsInv (M : TwoLevels E r U C) (f : C → M.dom → ℂ) : Prop :=
  ∀ c, ∀ γ ∈ (M.comp c).Γ, ∀ (x : M.dom) (hx : lact γ x.1 ∈ M.dom), f c ⟨lact γ x.1, hx⟩ = f c x

def HA (M : TwoLevels E r U C) : Subalgebra ℂ (C → M.dom → ℂ) where
  carrier := {f | IsHol M f ∧ IsInv M f}
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
    · obtain ⟨F, hF, hF'⟩ := hf c
      obtain ⟨G, hG, hG'⟩ := hg c
      exact ⟨F * G, hF.mul hG, fun x => by simp [hF', hG']⟩
    · simp only [Pi.mul_apply]
      rw [hf' c γ hγ x hx, hg' c γ hγ x hx]
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
    · obtain ⟨F, hF, hF'⟩ := hf c
      obtain ⟨G, hG, hG'⟩ := hg c
      exact ⟨F + G, hF.add hG, fun x => by simp [hF', hG']⟩
    · simp only [Pi.add_apply]
      rw [hf' c γ hγ x hx, hg' c γ hγ x hx]
  algebraMap_mem' := by
    intro z
    refine ⟨fun c => ⟨fun _ => z, differentiableOn_const z, fun x => rfl⟩, fun c γ hγ x hx => rfl⟩

theorem pb_mem (M : TwoLevels E r U C) (u : U) {f : C → M.dom → ℂ} (hf : f ∈ HA M) : pb M u f ∈ HA M := by
  obtain ⟨hf, hf'⟩ := hf
  refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
  · obtain ⟨G, hG, hG'⟩ := hf (u • c)
    refine ⟨fun y => G (lact (M.tr u c) y),
      hG.comp (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiable_lact _).differentiableOn (fun y hy => lact_tr_mem M u c hy),
      fun x => ?_⟩
    rw [pb_apply, hG']
    rfl
  · have hδ : M.tr u c * γ * (M.tr u c)⁻¹ ∈ (M.comp (u • c)).Γ := (M.tr_conj u c γ).1 hγ
    have e : lact (M.tr u c) (lact γ x.1) = lact (M.tr u c * γ * (M.tr u c)⁻¹) (lact (M.tr u c) x.1) := by
      simp only [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr u c)⁻¹ (M.tr u c),
        inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    have hy : lact (M.tr u c * γ * (M.tr u c)⁻¹) (Lmap M u c x).1 ∈ M.dom := by
      show lact (M.tr u c * γ * (M.tr u c)⁻¹) (lact (M.tr u c) x.1) ∈ M.dom
      rw [← e]; exact lact_tr_mem M u c hx
    rw [pb_apply, pb_apply, ← hf' (u • c) _ hδ (Lmap M u c x) hy]
    congr 1
    exact Subtype.ext e

def pbA (M : TwoLevels E r U C) (u : U) : HA M →ₐ[ℂ] HA M where
  toFun f := ⟨pb M u f, pb_mem M u f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def cst (M : TwoLevels E r U C) (a : C → ℂ) : HA M :=
  ⟨fun c _ => a c, fun c => ⟨fun _ => a c, differentiableOn_const _, fun _ => rfl⟩, fun _ _ _ _ _ => rfl⟩

def tw (M : TwoLevels E r U C) (a : C → ℂ) (u : U) : Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M) :=
  { Polynomial.eval₂RingHom (Polynomial.C.comp (pbA M u).toRingHom) (Polynomial.C (cst M a) * Polynomial.X) with
    commutes' := fun z => by
      show Polynomial.eval₂ _ _ (algebraMap ℂ (Polynomial (HA M)) z) = _
      rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
      simp }

theorem tw_C (M : TwoLevels E r U C) (a : C → ℂ) (u : U) (f : HA M) :
    tw M a u (Polynomial.C f) = Polynomial.C (pbA M u f) := by
  show Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_C]
  rfl

theorem tw_X (M : TwoLevels E r U C) (a : C → ℂ) (u : U) :
    tw M a u Polynomial.X = Polynomial.C (cst M a) * Polynomial.X := by
  show Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_X]

theorem tw_monomial_one (M : TwoLevels E r U C) (a : C → ℂ) (u : U) (f : HA M) :
    tw M a u (Polynomial.monomial 1 f) = Polynomial.monomial 1 (cst M a * pbA M u f) := by
  rw [← Polynomial.C_mul_X_eq_monomial, map_mul, tw_C, tw_X, ← mul_assoc, ← Polynomial.C_mul, mul_comm (pbA M u f),
    Polynomial.C_mul_X_eq_monomial]

end GlobalTheory.CuspEmb

end
