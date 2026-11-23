import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameFull

variable {D : D7}

theorem mL_div (I : Formalism.MainNotions.S.AutInst) (m : ℕ) :
    ∀ v ∈ mL I m, ∃ z ∈ I.Lf, v = (m : I.E ⊗[I.F] Af I.F) • z := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, I.Lf.zero_mem, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, I.Lf.add_mem ha hb, (smul_add _ _ _).symm⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, I.Lf.smul_mem c ha, smul_comm _ _ _⟩

theorem embA_smul (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
  simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem embA_zero (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA 0 = 0 := by
  simp [embA]

theorem step (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hmem : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    (hinj : Function.Injective (embA X wt ιA))
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F)
    (m : ℕ) (w : VA X.B.I) (hw : w ∈ X.B.I.Lf)
    (hwe : embA X wt ιA (c • y) = (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w) :
    ∃ z ∈ hat D.host.F (Mq wt), c • y = (m : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero]
    apply hinj
    rw [hwe, embA_zero, Nat.cast_zero, zero_smul]
  · have hF : IsUnit ((m : D.host.F)) := (Nat.cast_ne_zero.mpr hm.ne').isUnit
    have hR : IsUnit ((m : D.host.E ⊗[D.host.F] Ad D.host.F)) := by
      simpa using hF.map (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))
    obtain ⟨t, ht⟩ := hR.exists_right_inv
    refine ⟨t • (c • y), ?_, ?_⟩
    · rw [hmem, embA_smul, hwe, smul_smul, ← map_natCast ιA.symm m, ← map_mul, mul_comm, ht, map_one, one_smul]
      exact hw
    · rw [smul_smul, ht, one_smul]

theorem symm_unit (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA) :
    ιA.symm (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) =
      1 - X.ew - sigA X.B.I X.ew := by
  have h := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI X.ew
  apply ιA.injective
  rw [RingEquiv.apply_symm_apply, map_sub, map_sub, map_one]
  exact congrArg (fun t => 1 - ιA X.ew - t) h.symm

theorem emb_mem (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA)
    (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (hy : embA X wt ιA y ∈ X.B.I.Lf) :
    ∃ w ∈ X.B.I.Lf, embA X wt ιA
      ((1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y) =
      ((D.host.g 0 * D.host.g 1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w := by
  rw [embA_smul, symm_unit X ιA hI]
  obtain ⟨w, hw, hw'⟩ := mL_div X.B.I X.B.g _ (X.ew_full _ hy)
  exact ⟨w, hw, by rw [hw', X.g_eq]⟩

theorem eps_full : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ y ∈ hat D.host.F (Mq wt), ∃ z ∈ hat D.host.F (Mq wt), (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  intro D X u wt ιA hW hI y hy
  obtain ⟨hmem, -, hinj, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  obtain ⟨w, hw, hwe⟩ := emb_mem X wt ιA hI y ((hmem y).1 hy)
  exact step X wt ιA hmem hinj _ y _ w hw hwe

end GlobalTheory.St.G.FrameFull
