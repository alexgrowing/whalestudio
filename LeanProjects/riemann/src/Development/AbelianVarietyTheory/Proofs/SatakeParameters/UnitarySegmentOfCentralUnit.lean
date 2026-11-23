import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

noncomputable section

namespace GlobalTheory.UnitLSeg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def stabForm {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (l : Module.Dual ℂ V) : Subgroup (GL (Fin N) k) where
  carrier := {g | l ∘ₗ π g = l}
  one_mem' := by
    show l ∘ₗ π 1 = l
    rw [map_one, Module.End.one_eq_id, LinearMap.comp_id]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc l ∘ₗ π a⁻¹ = (l ∘ₗ π a) ∘ₗ π a⁻¹ := by rw [ha]
      _ = l := by rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_eq_id, LinearMap.comp_id]

theorem stab_le {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (χ : kˣ →* ℂˣ) (l : Module.Dual ℂ V) :
    stabForm π l ⊓ (detChar (Fin N) χ).ker ≤ stabForm (twist π (detChar (Fin N) χ)) l := by
  intro g ⟨h1, h2⟩
  have h2' : detChar (Fin N) χ g = 1 := h2
  change l ∘ₗ π g = l at h1
  change l ∘ₗ twist π (detChar (Fin N) χ) g = l
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, twist_apply, h2', Units.val_one, one_smul, ← LinearMap.comp_apply, h1]

theorem coeffLp_of_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {p : ℝ}
    {π : Representation ℂ (GL (Fin N) k) V} {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (h : CoeffLp p (twist π (detChar (Fin N) χ))) : CoeffLp p π := by
  intro _ _ μ hμ v l hl
  have ho : IsOpen ((stabForm (twist π (detChar (Fin N) χ)) l : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) :=
    Subgroup.isOpen_mono (stab_le π χ l) (IsOpen.inter hl (hχ.detChar (n := Fin N)))
  obtain ⟨F, hF, hm⟩ := h μ hμ v l ho
  refine ⟨F, fun g => ?_, hm⟩
  rw [hF, twist_apply, map_smul, norm_smul, detChar_apply, hu, one_mul]

theorem isUnitarisable_of_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {χ : kˣ →* ℂˣ} (hu : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (h : IsUnitarisable (twist π (detChar (Fin N) χ))) : IsUnitarisable π := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  have e := h3 g v w
  have : (detChar (Fin N) χ g : ℂ) * starRingEnd ℂ (detChar (Fin N) χ g) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, detChar_apply, hu]; simp
  rw [twist_apply, twist_apply, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, this, one_mul] at e
  exact e

theorem isUnitarisable_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : IsUnitarisable σ) : IsUnitarisable π := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B.comp E.toLinearMap).compl₂ E.toLinearMap, fun v w => h1 _ _, fun v hv => h2 _ ?_, fun g v w => ?_⟩
  · exact fun h => hv (E.toLinearEquiv.map_eq_zero_iff.1 h)
  · show B (E.toIntertwiningMap (π g v)) (E.toIntertwiningMap (π g w)) = _
    rw [E.toIntertwiningMap.isIntertwining, E.toIntertwiningMap.isIntertwining, h3]
    rfl

end GlobalTheory.UnitLSeg

open GlobalTheory.UnitLSeg in
theorem GlobalTheory.UnitLSeg.main : GlobalTheory.Published.EssSquareIntegrableSegments → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (δ : IrrGL k) (Δ : Segment k) (ω : kˣ →* ℂˣ), IsLSeg Δ δ.rep → HasCentralChar δ.rep ω → (∀ z, ‖(ω z : ℂ)‖ = 1) → 1 ≤ δ.1 ∧ IsSqIntCoeff δ.rep ∧ GlobalTheory.GenericUnitary.IsUnitaryLSeg δ := by
  intro hP k _ _ _ _ _ δ Δ ω hL hω hωu
  have hd : 1 ≤ δ.1 := by
    have h1 := hL.deg_eq
    have := Nat.mul_pos Δ.len_pos Δ.d_pos
    simp only [Segment.deg] at h1
    omega
  obtain ⟨χ, hχ, hsq⟩ := (hP k δ hd).2 ⟨Δ, hL⟩
  have hU : IsUnitarisable (δ.tw χ hχ).rep :=
    GlobalTheory.T.unitarisable_of_square_integrable k _ _ _ (δ.tw χ hχ).2.rep.smooth (δ.tw χ hχ).2.rep.irr (fun {c d} => @hsq c d)
  haveI := Model.nontrivial_of_isIrreducible (δ.tw χ hχ).2.rep.irr
  have hc := hasCentralChar_of_equiv (δ.twEquiv χ hχ) (hasCentralChar_twist hω χ)
  have hχu : ∀ z, ‖(χ z : ℂ)‖ = 1 := fun z => by
    have h1 := GlobalTheory.LocLanglands.TemperedRec.norm_centralChar_eq_one hU hc z
    rw [Fintype.card_fin, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul,
      norm_pow, hωu, one_mul] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
  have hU' : IsUnitarisable δ.rep :=
    isUnitarisable_of_twist hχu (isUnitarisable_of_equiv' (δ.twEquiv χ hχ) hU)
  have h1 : CoeffLp 2 (δ.tw χ hχ).rep := hsq
  have h2 : CoeffLp 2 (twist δ.rep (detChar (Fin δ.1) χ)) :=
    @GlobalTheory.Published.TemperedProduct.coeffLp_of_equiv k _ _ _ _ _ _ _ _ δ.1 2 _ _ (δ.twEquiv χ hχ).symm @h1
  have hsq' : IsSqIntCoeff δ.rep := coeffLp_of_twist hχ hχu h2
  exact ⟨hd, hsq', ⟨Δ, hL⟩, hU'⟩
