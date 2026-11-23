import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.ThK.ConeEuler.StabComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem map_piInf_of_one {n : ℕ} {w : InfinitePlace F} (τ : EmbOver E w) {ε : AF F} (hε : evInf F w ε = 1)
    (G : Matrix (Fin n) (Fin n) (AE F E)) :
    (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (piInf τ) = G.map (piInf τ) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  simp only [piInf, RingHom.comp_apply, map_add, compInf_smul, map_sub, map_one, hε, sub_self, zero_smul, one_smul,
    map_zero, add_zero]

theorem map_piInf_of_zero {n : ℕ} {w : InfinitePlace F} (τ : EmbOver E w) {ε : AF F} (hε : evInf F w ε = 0)
    (G : Matrix (Fin n) (Fin n) (AE F E)) :
    (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (piInf τ) = 1 := by
  rw [← Matrix.map_one (piInf (F := F) τ) (map_zero _) (map_one _)]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  simp only [piInf, RingHom.comp_apply, map_add, compInf_smul, map_sub, map_one, hε, sub_zero, zero_smul, one_smul,
    map_zero, zero_add]

theorem smul_mem_latHat {n : ℕ} {X : Spc F E n} {c : AF F} (hc : ∀ v, evFin F v c ∈ v.adicCompletionIntegers F)
    {z : Fin n → AE F E} (hz : z ∈ latHat X) : c • z ∈ latHat X := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, hi, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨c * a, ?_, fun v => ?_, x, hx, smul_smul _ _ _⟩
    · rw [GlobalTheory.ArchUniq.evI_eq_evIHom, map_mul, ← GlobalTheory.ArchUniq.evI_eq_evIHom, ← GlobalTheory.ArchUniq.evI_eq_evIHom, ha, mul_zero]
    · rw [map_mul]
      exact mul_mem (hc v) (hi v)
  | zero => rw [smul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [smul_neg]; exact neg_mem h1

theorem idem_mulVec_mem {n : ℕ} {X : Spc F E n} {ε : AF F} (hε : ∀ v, evFin F v ε ∈ v.adicCompletionIntegers F)
    {G : Matrix (Fin n) (Fin n) (AE F E)} {z : Fin n → AE F E} (hz : z ∈ latHat X) (hG : G *ᵥ z ∈ latHat X) :
    (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))) *ᵥ z ∈ latHat X := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine add_mem (smul_mem_latHat hε hG) (smul_mem_latHat (fun v => ?_) hz)
  rw [map_sub, map_one]
  exact sub_mem (one_mem _) (hε v)

theorem evFin_eFin_mem (v w : Pl F) : evFin F w (eFin v) ∈ w.adicCompletionIntegers F := by
  by_cases hw : w = v
  · subst hw
    rw [eFin, GlobalTheory.LatVac.evFin_liftV]
    exact one_mem _
  · rw [show evFin F w (eFin v) = 0 from evalV_singleFin_ne hw 1]
    exact zero_mem _

theorem evFin_eInf_mem (w : Pl F) : evFin F w (eInf F) ∈ w.adicCompletionIntegers F := by
  rw [show evFin F w (eInf F) = 0 from map_zero (evalV F w)]
  exact zero_mem _

theorem evInf_eInf (w : InfinitePlace F) : evInf F w (eInf F) = 1 := by
  have h1 : (eInf F).1 = 1 :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_one]; exact evI_realAd_one)
  exact congrFun h1 w

theorem comp_mem_of_isStab (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (K : Subgroup (UA σ X.J)) (hK : IsStab B K) :
    ∀ k ∈ K, (∀ v : Pl F, compAt σ X.J v k ∈ K) ∧ compArch σ X.J k ∈ K := by
  intro k hk
  obtain ⟨h1, h2⟩ := (hK k).1 hk
  refine ⟨fun v => (hK _).2 ⟨fun w => ?_, fun z hz => ?_⟩, (hK _).2 ⟨fun w => ?_, fun z hz => ?_⟩⟩
  · rw [mat_compAt, map_piInf_of_zero _ rfl]
    exact Commute.one_left _
  · rw [← map_inv, mat_compAt, mat_compAt]
    exact ⟨idem_mulVec_mem (evFin_eFin_mem v) hz (h2 z hz).1, idem_mulVec_mem (evFin_eFin_mem v) hz (h2 z hz).2⟩
  · rw [mat_compArch, map_piInf_of_one _ (evInf_eInf w)]
    exact h1 w
  · rw [← map_inv, mat_compArch, mat_compArch]
    exact ⟨idem_mulVec_mem evFin_eInf_mem hz (h2 z hz).1, idem_mulVec_mem evFin_eInf_mem hz (h2 z hz).2⟩

end GlobalTheory.ThK.ConeEuler.StabComp

end
