import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralCompAddEquiv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFinsetAnnLeK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ProfHeisLiftK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SplitLagrF
open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
variable {B : Base F E}
theorem prof_support_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    ∃ K : Set (conjHalf σ e nS nT), IsCompact K ∧
      ∀ t : conjHalf σ e nS nT, t ∉ K → prof σ JS JT ξ₀ B.ψ ν 𝓕 f t = 0 := by
  obtain ⟨K, hK, hKs⟩ := _root_.GlobalTheory.SplitLagrF.exists_compact_ann_k (JS := JS) hB hS hT hξ hσξ he
    (fun g => heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f = f) (fun g hg => by
      obtain ⟨k, hk, h⟩ := exists_nsmul_fix (GlobalTheory.SplitVacF.isSplitIdemF_conj he)
        (mul_mem_conjHalf (dC F E nT) (smul_mem_conjHalf (-hlf F E) hg)) hf
      refine ⟨k, hk, ?_⟩
      rwa [smul_comm, Matrix.mul_smul])
  refine ⟨K, hK, fun t ht => ?_⟩
  by_contra hne
  refine ht (hKs t fun g hg => ?_)
  have h := _root_.GlobalTheory.SplitLagrF.prof_heis_lift_k hB hS hT hξ hσξ hν h𝓕 hf g t
  rw [hg] at h
  exact (mul_eq_right₀ hne).1 h.symm
theorem prof_integrable_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)] (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure]
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    Integrable (fun t : conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f t) μ := by
  obtain ⟨-, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : T2Space (conjHalf σ e nS nT) := inferInstance
  have : R1Space (conjHalf σ e nS nT) := T2Space.r1Space
  obtain ⟨U, hU, hUf⟩ := prof_level (JT := JT) ν 𝓕 he hf
  obtain ⟨K, hK, hKs⟩ := _root_.GlobalTheory.SplitLagrF.prof_support_k hB hS hT hξ hσξ hν h𝓕 he hf
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK hKs)
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hn : {s : conjHalf σ e nS nT | s - t ∈ U} ∈ nhds t := by
    refine IsOpen.mem_nhds (hU.preimage (continuous_id.sub continuous_const)) ?_
    show t - t ∈ U
    rw [sub_self]; exact U.zero_mem
  filter_upwards [hn] with s hs
  have h1 := hUf t _ hs
  rwa [add_sub_cancel] at h1
theorem commF_eventually_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) {e : AEF F E} (he : IsSplitIdemF σ e) (g : WOF F E nS nT) :
    ∀ᶠ y : conjHalf σ e nS nT in nhds 0, commF σ JS JT ξ₀ B.ψ g y = 1 := by
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨K, hK⟩ := GlobalTheory.HeisThetaF.exists_openAddSubgroup_psi_fin B.ψ hψ
  let φ : WOF F E nS nT → AF F := fun u => symplOHF σ JS JT ξ₀ g u - symplOHF σ JS JT ξ₀ u g
  have hφ : Continuous φ :=
    (GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g)
  let ρ : conjHalf σ e nS nT → Af F := fun u => (φ u.1).2
  have hρ : Continuous ρ := continuous_snd.comp (hφ.comp continuous_subtype_val)
  have h0 : ρ 0 = 0 := by
    show (symplOHF σ JS JT ξ₀ g 0 - symplOHF σ JS JT ξ₀ 0 g).2 = 0
    rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero]
    rfl
  have hn : ρ ⁻¹' (K : Set (Af F)) ∈ nhds (0 : conjHalf σ e nS nT) :=
    (K.isOpen.preimage hρ).mem_nhds (by rw [Set.mem_preimage, h0]; exact K.zero_mem)
  filter_upwards [hn] with u hu
  have h1 : pairA F 1 0 • u.1 = 0 :=
    GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (GlobalTheory.SplitVacF.fin_of_mem he u.2)
  have hfst : fstA F (φ u.1) = 0 := by
    rw [← GlobalTheory.HeisThetaF.fstA_mul_idem]
    show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ g u.1 - symplOHF σ JS JT ξ₀ u.1 g)) = 0
    rw [mul_sub, ← GlobalTheory.HeisThetaF.symplOHF_smul_left (pairA F 1 0) u.1 g,
      ← GlobalTheory.HeisThetaF.symplOHF_smul_right (pairA F 1 0) g u.1, h1, GlobalTheory.HeisThetaF.symplOHF_zero_left,
      GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, map_zero]
  have hφu : φ u.1 = pairA F 0 (ρ u) := Prod.ext hfst rfl
  show B.ψ (φ u.1) = 1
  rw [hφu]
  exact hK _ hu
theorem lagrInt_eq_zero_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)] (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure]
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f)
    (hall : ∀ u, ∫ t : conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ u f) t ∂μ = 0) :
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f = 0 := by
  obtain ⟨U, hU, hUf⟩ := prof_level (JT := JT) ν 𝓕 he hf
  obtain ⟨K, hK, hKs⟩ := _root_.GlobalTheory.SplitLagrF.prof_support_k hB hS hT hξ hσξ hν h𝓕 he hf
  obtain ⟨G, -, hG⟩ := _root_.GlobalTheory.SplitLagrF.exists_open_sep_k (JS := JS) hB hS hT hξ hσξ he U hU
  let L : AddSubgroup (conjHalf σ e nS nT) :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, GlobalTheory.SplitVacF.commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => GlobalTheory.SplitVacF.commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := GlobalTheory.SplitVacF.commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g
          (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hL : IsOpen (L : Set (conjHalf σ e nS nT)) := by
    refine AddSubgroup.isOpen_of_mem_nhds L (g := 0) ?_
    exact (Filter.eventually_all_finset G).2 fun g _ => _root_.GlobalTheory.SplitLagrF.commF_eventually_k hB he g
  have hφ := GlobalTheory.fourier_uniqueness_of_openSubgroup μ
    (fun (a : WOF F E nS nT) (t : conjHalf σ e nS nT) => commF σ JS JT ξ₀ B.ψ a t)
    (fun a s t => GlobalTheory.SplitVacF.commF_add_right a s.1 t.1)
    (fun a => GlobalTheory.SplitVacF.commF_zero_right a) (fun t => GlobalTheory.SplitVacF.commF_zero_left t.1)
    (fun a b t => GlobalTheory.SplitVacF.commF_add_left a b t.1) L hL
    (fun x hx => by
      have hx' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (x : WOF F E nS nT) = 1 := hx
      push_neg at hx'
      obtain ⟨g, hg, hne⟩ := hx'
      exact ⟨g, fun l hl => hl g hg, hne⟩)
    (fun t => prof σ JS JT ξ₀ B.ψ ν 𝓕 f t) K hK hKs (fun t l hl => hUf t l (hG l hl))
    (fun a _ => by
      rw [← hall (dC F E nT * ((-hlf F E) • a : WOF F E nS nT))]
      simp only [_root_.GlobalTheory.SplitLagrF.prof_heis_lift_k hB hS hT hξ hσξ hν h𝓕 hf])
  rw [← prof_zero (σ := σ) (JS := JS) (JT := JT) (ξ₀ := ξ₀) (ψ := B.ψ)]
  exact congrFun hφ 0
end GlobalTheory.SplitLagrF
end
end
