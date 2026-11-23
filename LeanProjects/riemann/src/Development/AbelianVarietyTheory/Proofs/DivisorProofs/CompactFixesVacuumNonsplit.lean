import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section
namespace GlobalTheory.VacFixKAt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev eAt (v : Pl F) : AF F := GlobalTheory.LatVac.liftV v 1

theorem eAt_mul (v : Pl F) (a : AF F) (ha : At (evFin F v) a) : eAt v * a = a := by
  have h1 : evFin F v (1 - eAt v) = 0 := by
    rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
  have h2 : (1 - eAt v) • a = 0 := ha _ h1
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h2
  exact h2.symm

theorem at_eAt_mul (v : Pl F) (a : AF F) : At (evFin F v) (eAt v * a) := by
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul]
  exact GlobalTheory.LatVac.at_liftV v _

theorem evFin_eAt_mul (v : Pl F) (a : AF F) : evFin F v (eAt v * a) = evFin F v a := by
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul, GlobalTheory.LatVac.evFin_liftV]

theorem latAt_le_latHat {d : ℕ} (W : Spc F E d) (v : Pl F) : GlobalTheory.InertSph.latAt W v ≤ latHat W := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro z ⟨a, ha, hai, y, hy, rfl⟩
  refine AddSubgroup.subset_closure ⟨a, GlobalTheory.ThK.LocalOps.evI_of_at ha, fun w => ?_, y, hy, rfl⟩
  by_cases hw : w = v
  · subst hw; exact hai
  · rw [GlobalTheory.ThK.LocalOps.evFin_of_at hw ha]; exact zero_mem _

theorem eAt_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl F) {z : Fin d → AE F E} (hz : z ∈ latHat W) :
    eAt v • z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hai, x, hx, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨eAt v * a, at_eAt_mul v a, ?_, x, hx, rfl⟩
    rw [evFin_eAt_mul]; exact hai v
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg z _ h => rw [smul_neg]; exact neg_mem h

theorem eAt_smul_of_mem {d : ℕ} (W : Spc F E d) (v : Pl F) {z : Fin d → AE F E}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : eAt v • z = z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    rw [smul_smul, eAt_mul v a ha]
  | zero => rw [smul_zero]
  | add z z' _ _ h h' => rw [smul_add, h, h']
  | neg z _ h => rw [smul_neg, h]

theorem smul_mulVec' {d : ℕ} (u : AF F) (M : Matrix (Fin d) (Fin d) (AE F E)) (z : Fin d → AE F E) :
    (u • M) *ᵥ z = u • (M *ᵥ z) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc]

theorem mulVec_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl F) (M : Matrix (Fin d) (Fin d) (AE F E))
    (hM : At (evFin F v) (M - 1)) (hL : ∀ z ∈ latHat W, M *ᵥ z ∈ latHat W) {z : Fin d → AE F E}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  have h1 : evFin F v (1 - eAt v) = 0 := by
    rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
  have hz' : (1 - eAt v) • z = 0 := by
    rw [sub_smul, one_smul, eAt_smul_of_mem W v hz, sub_self]
  have hMz : (1 - eAt v) • ((M - 1) *ᵥ z) = 0 := by
    rw [← smul_mulVec', hM _ h1, Matrix.zero_mulVec]
  have key : M *ᵥ z = eAt v • (M *ᵥ z) := by
    have e : M *ᵥ z = z + (M - 1) *ᵥ z := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
    have : (1 - eAt v) • (M *ᵥ z) = 0 := by
      rw [e, smul_add, hz', hMz, add_zero]
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this
  rw [key]
  exact eAt_smul_mem W v (hL z (latAt_le_latHat W v hz))

theorem mem_inertSph_KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) {k : UA σ W.J} (hk : k ∈ KAt σ W v) :
    k ∈ GlobalTheory.InertSph.KAt σ W v := by
  obtain ⟨hU, hL⟩ := hk
  have hinv : mat k⁻¹ * mat k = 1 := Units.inv_mul k.1
  have hU' : At (evFin F v) (mat k⁻¹ - 1) := by
    intro u hu
    have h0 : u • (mat k - 1) = 0 := hU u hu
    have : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
    rw [this, smul_neg, ← Matrix.mul_smul, h0, Matrix.mul_zero, neg_zero]
  refine ⟨hU, fun z hz => ⟨?_, ?_⟩⟩
  · exact mulVec_mem_latAt W v _ hU (fun z hz => (hL z hz).1) hz
  · exact mulVec_mem_latAt W v _ hU' (fun z hz => (hL z hz).2) hz

end GlobalTheory.VacFixKAt

namespace GlobalTheory.VacFixKAt

theorem vacFixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → v ∉ X.T → ∀ k ∈ KAt σ G.W v,
      Acts (evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h v hv hT k hk
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w :=
    (GlobalTheory.KFinLoc.split_or_inert F E σ B h.base v).resolve_left fun ⟨e⟩ => hv.false e
  exact GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum F E σ B a a' G X om om' h v w hw hT k (mem_inertSph_KAt σ G.W v hk)

end GlobalTheory.VacFixKAt
