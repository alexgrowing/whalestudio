import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Member.character_quotient_values_in_embedding_field

theorem small_quot_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (k : Type) [Field k] (σ : k →+* ℂ), SmallIn R i σ → (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) σ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i k _ σ h v hv
  have hE : R.C.eta.UnrAt v := R.C.isEta.unr v
  have hM : (R.C.mu0 i).UnrAt v := by
    intro x hx
    have h1 := hv x hx
    have h2 := hE x hx
    have h3 : ((R.C.mu0 i * R.C.eta⁻¹).loc v) x = (R.C.mu0 i).loc v x * (R.C.eta.loc v x)⁻¹ := rfl
    rw [h3, h2, inv_one, mul_one] at h1
    exact h1
  obtain ⟨y1, hy1⟩ := h.1 v hM
  obtain ⟨y2, hy2⟩ := h.2 v hE
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast this
  have hval : ((R.C.mu0 i * R.C.eta⁻¹).val v : ℂ) = ((R.C.mu0 i).val v : ℂ) * ((R.C.eta.val v : ℂ))⁻¹ := by
    have : (R.C.mu0 i * R.C.eta⁻¹).val v = (R.C.mu0 i).val v * (R.C.eta.val v)⁻¹ := rfl
    rw [this, Units.val_mul, Units.val_inv_eq_inv_val]
  have hy2' : σ y2 ≠ 0 := by
    rw [hy2, Formalism.L2.Host.HChar.valTw]
    exact mul_ne_zero (Units.ne_zero _) ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hN)
  refine ⟨y1 / y2, ?_⟩
  rw [map_div₀, hy1, hy2]
  simp only [Formalism.L2.Host.HChar.valTw, hval]
  have e1 : (-((-1 / 2 : ℝ) : ℂ)) = -(-((1 / 2 : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, Complex.cpow_neg _ (-((1/2 : ℝ) : ℂ))]
  push_cast
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  field_simp

end GlobalTheory.Member.character_quotient_values_in_embedding_field
