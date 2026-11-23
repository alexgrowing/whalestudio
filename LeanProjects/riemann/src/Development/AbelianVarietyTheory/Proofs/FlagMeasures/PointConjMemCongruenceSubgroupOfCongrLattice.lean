import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PointLattice

theorem conj_mulVec_eq_smul (I : AutInst) (x : I.GA) (c : ℕ) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (hM : ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, M *ᵥ y = (c : I.E) • z)
    (w : Fin I.n → I.E ⊗[I.F] Af I.F) (hw : w ∈ I.Lf) :
    ∃ z ∈ I.Lf, (I.fmat x.2⁻¹ * M.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x.2) *ᵥ w =
      (c : I.E ⊗[I.F] Af I.F) • z := by
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    rw [Set.image_eq_range]
    rfl
  have hfin := Module.Finite.iff_fg.2 I.L_fg
  have hu := Formalism.UG.P.csSpan_back Formalism.UG.P.csGlob_intAdApprox I.L hfin I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (I.fmat x.2 *ᵥ w)
    (by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]; exact e1.symm ▸ hw)
  rw [← lamX_eq_globLat] at hu
  rw [← mulVec_mulVec]
  generalize I.fmat x.2 *ᵥ w = u at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨z, hz, e⟩ := hM y hy
    refine ⟨_, (GlobalTheory.Count.Test.mem_lamX I x z).1 hz, ?_⟩
    rw [← mulVec_mulVec, ← mulVec_smul]
    congr 1
    funext i
    have h := (RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F) : I.E →+* _) M y i).symm
    rw [e] at h
    refine h.trans ?_
    simp
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨z, hz, e⟩ := hu
    obtain ⟨z', hz', e'⟩ := hv
    exact ⟨z + z', add_mem hz hz', by rw [mulVec_add, e, e', smul_add]⟩
  | smul s u _ hu =>
    obtain ⟨z, hz, e⟩ := hu
    refine ⟨s • z, Submodule.smul_mem _ s hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, mulVec_smul, e, smul_comm]

theorem conj_mem_Kg_of_congr : ∀ (I : AutInst) (x a : I.GA) (g : ℕ) (γ : GL (Fin I.n) I.E), I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (∀ y ∈ lamX I x, ∃ z ∈ lamX I x, ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y = (g : I.E) • z) → (∀ y ∈ lamX I x, ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) → (x⁻¹ * a * x).2 ∈ I.Kg g := by
  intro I x a g γ ha h1 h2
  have hk : I.fmat (x⁻¹ * a * x).2 = I.fmat x.2⁻¹ * I.fmat a.2 * I.fmat x.2 := rfl
  have hx1 : I.fmat x.2⁻¹ * I.fmat x.2 = 1 := Units.inv_mul _
  have hx2 : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := Units.mul_inv _
  have hc : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (I.fmat (x⁻¹ * a * x).2 - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    obtain ⟨z, hz, e⟩ := conj_mulVec_eq_smul I x g _ h1 y hy
    refine ⟨z, hz, ?_⟩
    rw [← e, hk, ha, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      mul_sub, sub_mul, mul_one, hx1]
  refine ⟨fun y => ?_, hc⟩
  symm
  show I.fmat (x⁻¹ * a * x).2 *ᵥ y ∈ I.Lf ↔ y ∈ I.Lf
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := conj_mulVec_eq_smul I x 1 _
      (fun y hy => ⟨_, h2 y hy, by rw [Nat.cast_one, one_smul]⟩) _ hy
    rw [Nat.cast_one, one_smul, mulVec_mulVec, hk, ha] at e
    have hγ : ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map
        (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : ∀ A B C D : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F), A * B = 1 → B * A = 1 →
        C * D = 1 → A * C * B * (A * D * B) = 1 := by
      intro A B C D p q r
      calc A * C * B * (A * D * B) = A * (C * (B * A) * D) * B := by simp only [mul_assoc]
        _ = 1 := by rw [q, mul_one, r, mul_one, p]
    rw [h3 _ _ _ _ hx1 hx2 hγ, one_mulVec] at e
    exact e ▸ hz
  · obtain ⟨z, hz, e⟩ := hc y hy
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add, Nat.cast_smul_eq_nsmul] at e
    rw [e]
    exact add_mem (nsmul_mem hz g) hy

end GlobalTheory.PointLattice
