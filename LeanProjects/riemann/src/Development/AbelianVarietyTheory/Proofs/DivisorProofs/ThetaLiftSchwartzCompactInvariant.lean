import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupFixingSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler

noncomputable section

namespace GlobalTheory.ThK.BotFixFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem smul_sub_one_eq_zero {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : AF F} {hε : ε * ε = ε} {k : UA σ J}
    (h : idemU σ J ε hε k = 1) (i j : Fin n) : ε • (mat k - 1) i j = 0 := by
  have h1 : ε • mat k + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E)) = 1 := congrArg mat h
  have h2 : ε • (mat k - 1) = 0 := by
    rw [sub_smul, one_smul] at h1
    rw [smul_sub, ← sub_eq_zero.2 h1]
    abel
  exact congrFun (congrFun h2 i) j

theorem fstA_eInf : fstA F (eInf F) = 1 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (evI_realAd_one.trans (map_one _).symm)

theorem eq_one_of_components {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {k : UA σ J} (h1 : compArch σ J k = 1)
    (h2 : ∀ v, compAt σ J v k = 1) : k = 1 := by
  apply Subtype.ext; apply Units.ext
  change mat k = 1
  rw [← sub_eq_zero]
  ext i j
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_
  · have := congrArg (compInf F E w) (smul_sub_one_eq_zero h1 i j)
    rw [compInf_smul, show evInf F w (eInf F) = 1 from congrFun fstA_eInf w, one_smul] at this
    exact this
  · have := congrArg (compFin F E w) (smul_sub_one_eq_zero (h2 w) i j)
    rw [compFin_smul, eFin, GlobalTheory.LatVac.evFin_liftV, one_smul] at this
    exact this

omit [NumberField E] in
theorem tmap_eInf_smul (x : AE F E) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (eInf F • x) =
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [TensorProduct.smul_tmul', fstA_eInf]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add]

theorem map_fst_eq_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {k : UA σ J} (h1 : compArch σ J k = 1) :
    (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
  ext i j
  have := congrArg (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (smul_sub_one_eq_zero h1 i j)
  rw [tmap_eInf_smul, map_zero, Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  exacts [map_one _, map_zero _]

theorem exists_finset_subset {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {C U : Set (UA σ J)} (hC : IsCompact C)
    (hA : ∀ k ∈ C, compArch σ J k = 1) (hU : IsOpen U) (h1 : (1 : UA σ J) ∈ U) :
    ∃ S : Finset (Pl F), ∀ k ∈ C, (∀ v ∈ S, compAt σ J v k = 1) → k ∈ U := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  haveI : T2Space (UA σ J) := inferInstance
  obtain ⟨S, hS⟩ := (hC.diff hU).elim_finite_subfamily_closed (fun v : Pl F => {k | compAt σ J v k = 1})
    (fun v => isClosed_eq ((continuous_components F E σ n J).1 v) continuous_const) (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro k ⟨⟨hk, hkU⟩, hv⟩
      rw [Set.mem_iInter] at hv
      exact hkU (eq_one_of_components (hA k hk) hv ▸ h1))
  refine ⟨S, fun k hk hv => ?_⟩
  by_contra hkU
  exact (Set.eq_empty_iff_forall_notMem.1 hS k) ⟨⟨hk, hkU⟩, Set.mem_iInter₂.2 hv⟩

theorem fix_off_finset : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ K : Subgroup (UA σ X.J), IsCompact {k : UA σ X.J | compArch σ X.J k = 1 ∧ ∀ v, compAt σ X.J v k ∈ K} →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ S₀ : Finset (Pl F), ∀ k : UA σ X.J, compArch σ X.J k = 1 → (∀ v, compAt σ X.J v k ∈ K) →
      (∀ v ∈ S₀, compAt σ X.J v k = 1) → om (k, 1) Φ = Φ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP K hC Φ hΦ
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.FixLeftSchA.level_left hKP F E σ B n d X W M χX χW om r s' r₁ s₁ hP Φ hΦ
  obtain ⟨S, hS⟩ := exists_finset_subset hC (fun k hk => hk.1) hUo U.one_mem
  exact ⟨S, fun k h1 h2 h3 => hU k (hS k ⟨h1, h2⟩ h3) (map_fst_eq_one h1)⟩

end GlobalTheory.ThK.BotFixFin
