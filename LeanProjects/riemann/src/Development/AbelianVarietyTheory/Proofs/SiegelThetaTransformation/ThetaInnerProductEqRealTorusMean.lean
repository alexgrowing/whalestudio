import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompactStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.TorusMean

section Abstract

open Pointwise

variable {G V : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  (p : G →+ V) (R : V →+ G) (U : AddSubgroup G)

def tube : AddSubgroup G := U.comap (AddMonoidHom.id G - R.comp p)

omit [TopologicalSpace G] [IsTopologicalAddGroup G] [TopologicalSpace V] [IsTopologicalAddGroup V] in
theorem mem_tube (w : G) : w ∈ tube p R U ↔ w - R (p w) ∈ U := Iff.rfl

variable {p R U}

omit [IsTopologicalAddGroup V] in

theorem exists_compact (hR : Continuous R) (hU : IsCompact (U : Set G)) {K : Set V} (hK : IsCompact K) :
    ∃ K' : Set G, IsCompact K' ∧ p ⁻¹' K ∩ tube p R U ⊆ K' := by
  refine ⟨(fun x : G × V => x.1 + R x.2) '' ((U : Set G) ×ˢ K),
    (hU.prod hK).image (continuous_fst.add (hR.comp continuous_snd)), ?_⟩
  rintro w ⟨hwK, hwU⟩
  refine ⟨(w - R (p w), p w), ⟨(mem_tube p R U w).mp hwU, hwK⟩, ?_⟩
  simp

theorem discrete_image [T2Space G] [T2Space V] [LocallyCompactSpace V] (hR : Continuous R)
    (hU : IsCompact (U : Set G)) (Γ : AddSubgroup G) [DiscreteTopology Γ] (L : AddSubgroup V)
    (hL : ∀ v ∈ L, ∃ γ ∈ Γ, γ ∈ tube p R U ∧ p γ = v) : DiscreteTopology L := by
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : V)
  obtain ⟨K', hK', hsub⟩ := exists_compact (p := p) (U := U) hR hU hKc
  have hΓc : IsClosed (Γ : Set G) := AddSubgroup.isClosed_of_discrete
  have hfin : ((Γ : Set G) ∩ K').Finite := by
    apply (hK'.inter_left hΓc).finite
    have hd : DiscreteTopology (Γ : Set G) := inferInstanceAs (DiscreteTopology Γ)
    have hd' : DiscreteTopology ↥((Γ : Set G) ∩ K') := DiscreteTopology.of_subset hd Set.inter_subset_left
    exact ⟨hd'⟩
  have hLK : ((L : Set V) ∩ K).Finite := by
    apply (hfin.image p).subset
    rintro v ⟨hvL, hvK⟩
    obtain ⟨γ, hγ, hγt, rfl⟩ := hL v hvL
    exact ⟨γ, ⟨hγ, hsub ⟨hvK, hγt⟩⟩, rfl⟩
  apply discreteTopology_of_isOpen_singleton_zero
  have hB : IsClosed (((L : Set V) ∩ K) \ {0}) := (hLK.subset Set.sdiff_subset).isClosed
  refine isOpen_induced_iff.mpr ⟨interior K ∩ (((L : Set V) ∩ K) \ {0})ᶜ,
    isOpen_interior.inter hB.isOpen_compl, ?_⟩
  ext ⟨v, hv⟩
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hvK, hvB⟩
    by_contra hne
    apply hvB
    refine ⟨⟨hv, interior_subset hvK⟩, ?_⟩
    intro h0
    exact hne (Subtype.ext h0)
  · intro h0
    have hv0 : v = 0 := congrArg Subtype.val h0
    subst hv0
    exact ⟨mem_interior_iff_mem_nhds.mpr hK0, fun h => h.2 rfl⟩

variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace V] [BorelSpace V]

theorem exists_map_eq_smul [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] (hp : Continuous p)
    (hR : Continuous R) (hpR : ∀ v, p (R v) = v) (hU : IsCompact (U : Set G))
    (μ : Measure G) [μ.IsAddHaarMeasure] (ν : Measure V) [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, (μ.restrict (tube p R U)).map p = c • ν := by
  set ν' := (μ.restrict (tube p R U)).map p with hν'
  have hpm : Measurable p := hp.measurable
  have : IsFiniteMeasureOnCompacts ν' := ⟨fun K hK => by
    obtain ⟨K', hK', hsub⟩ := exists_compact hR hU hK
    rw [hν', Measure.map_apply hpm hK.measurableSet, Measure.restrict_apply (hpm hK.measurableSet)]
    exact lt_of_le_of_lt (measure_mono hsub) hK'.measure_lt_top⟩
  have : ν'.IsAddLeftInvariant := ⟨fun v => by
    have hpre : (fun w => R v + w) ⁻¹' (tube p R U : Set G) = tube p R U := by
      ext w
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_tube, map_add, hpR]
      rw [show R v + w - (R v + R (p w)) = w - R (p w) by abel]
    have hpres : MeasurePreserving (fun w => R v + w) (μ.restrict (tube p R U))
        (μ.restrict (tube p R U)) := by
      have := (measurePreserving_add_left μ (R v)).restrict_preimage_emb
        (measurableEmbedding_addLeft (R v)) (tube p R U : Set G)
      rwa [hpre] at this
    have hcomm : (fun x => v + x) ∘ p = p ∘ (fun w => R v + w) := by
      funext w
      simp [hpR]
    rw [hν', Measure.map_map (continuous_const_add v).measurable hpm, hcomm,
      ← Measure.map_map hpm (continuous_const_add (R v)).measurable, hpres.map_eq]⟩
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul ν' ν⟩

theorem integral_eq_mean [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] (hp : Continuous p)
    (hR : Continuous R) (hpR : ∀ v, p (R v) = v) (hU : IsCompact (U : Set G))
    (hO : IsOpen (tube p R U : Set G)) (μ : Measure G) [μ.IsAddHaarMeasure] (ν : Measure V) [ν.IsAddHaarMeasure]
    (Γ : AddSubgroup G) [Countable Γ] (L : AddSubgroup V)
    (hL : ∀ v, v ∈ L ↔ ∃ γ ∈ Γ, γ ∈ tube p R U ∧ p γ = v) (hcov : ∀ w, ∃ γ ∈ Γ, γ + w ∈ tube p R U)
    (hinj : ∀ γ ∈ Γ, γ ∈ U → γ = 0) {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)
    {Fd : Set V} (hFd : IsAddFundamentalDomain L Fd ν) {h : G → ℂ} (hc : Continuous h)
    (hΓ : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (hhU : ∀ u ∈ U, ∀ w, h (w + u) = h w) :
    ∫ w in 𝓕, h w ∂μ = ((ν Fd).toReal : ℂ)⁻¹ * ∫ v in Fd, h (R v) ∂ν := by
  classical
  have hpm : Measurable p := hp.measurable
  have hTm : MeasurableSet (tube p R U : Set G) := hO.measurableSet
  obtain ⟨c, hcν⟩ := exists_map_eq_smul hp hR hpR hU μ ν
  have hnull : ∀ N : Set V, ν N = 0 → μ ((tube p R U : Set G) ∩ p ⁻¹' N) = 0 := by
    intro N hN
    have hN0 : ν (toMeasurable ν N) = 0 := by rwa [measure_toMeasurable]
    apply measure_mono_null
      (Set.inter_subset_inter_right _ (Set.preimage_mono (subset_toMeasurable ν N)))
    rw [Set.inter_comm, ← Measure.restrict_apply (hpm (measurableSet_toMeasurable ν N)),
      ← Measure.map_apply hpm (measurableSet_toMeasurable ν N), hcν]
    simp [hN0]
  have hfac : ∀ w ∈ (tube p R U : Set G), h w = h (R (p w)) := by
    intro w hw
    have hu : w - R (p w) ∈ U := (mem_tube p R U w).mp hw
    have h1 := hhU _ hu (R (p w))
    rw [show R (p w) + (w - R (p w)) = w by abel] at h1
    exact h1
  have hΓT : ∀ γ ∈ Γ, γ ∈ tube p R U → p γ = 0 → γ = 0 := by
    intro γ hγ hγt h0
    apply hinj γ hγ
    have := (mem_tube p R U γ).mp hγt
    rwa [h0, map_zero, sub_zero] at this
  have hFdm : NullMeasurableSet Fd ν := hFd.nullMeasurableSet
  have hFd₀m : MeasurableSet (toMeasurable ν Fd) := measurableSet_toMeasurable ν Fd
  have hFd₀ae : toMeasurable ν Fd =ᵐ[ν] Fd := hFdm.toMeasurable_ae_eq
  have hFdsub : Fd ⊆ toMeasurable ν Fd := subset_toMeasurable ν Fd
  have hdiff : ν (toMeasurable ν Fd \ Fd) = 0 := (ae_eq_set.mp hFd₀ae).1
  have hΦ₀m : MeasurableSet ((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd) := hTm.inter (hpm hFd₀m)
  have hΦae : (((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd : Set G)) =ᵐ[μ]
      (((tube p R U : Set G) ∩ p ⁻¹' Fd : Set G)) := by
    rw [ae_eq_set]
    constructor
    · apply measure_mono_null _ (hnull _ hdiff)
      rintro w ⟨⟨hwT, hw0⟩, hwn⟩
      exact ⟨hwT, hw0, fun hw => hwn ⟨hwT, hw⟩⟩
    · exact measure_mono_null (fun w hw => (hw.2 ⟨hw.1.1, hFdsub hw.1.2⟩).elim) measure_empty
  have hΦ : IsAddFundamentalDomain Γ ((tube p R U : Set G) ∩ p ⁻¹' Fd) μ := by
    refine ⟨hΦ₀m.nullMeasurableSet.congr hΦae, ?_, ?_⟩
    · have hbad : ν {v | ¬ ∃ l : L, l +ᵥ v ∈ Fd} = 0 := ae_iff.mp hFd.ae_covers
      rw [ae_iff]
      refine measure_mono_null ?_ (measure_iUnion_null fun γ : Γ =>
        (show μ ((fun w => (γ : G) + w) ⁻¹'
            ((tube p R U : Set G) ∩ p ⁻¹' {v | ¬ ∃ l : L, l +ᵥ v ∈ Fd})) = 0 by
          rw [measure_preimage_add]
          exact hnull _ hbad))
      intro w hw
      simp only [Set.mem_ofPred_eq, not_exists] at hw
      obtain ⟨γ, hγ, hγw⟩ := hcov w
      refine Set.mem_iUnion.mpr ⟨⟨γ, hγ⟩, hγw, ?_⟩
      rintro ⟨l, hl⟩
      obtain ⟨γ', hγ', hγ't, hpl⟩ := (hL l).mp l.2
      apply hw ⟨γ' + γ, Γ.add_mem hγ' hγ⟩
      refine ⟨?_, ?_⟩
      · show γ' + γ + w ∈ tube p R U
        rw [add_assoc]
        exact (tube p R U).add_mem hγ't hγw
      · show p (γ' + γ + w) ∈ Fd
        rw [add_assoc, map_add, hpl]
        exact hl
    · intro γ₁ γ₂ hne
      show μ ((γ₁ +ᵥ ((tube p R U : Set G) ∩ p ⁻¹' Fd)) ∩ (γ₂ +ᵥ ((tube p R U : Set G) ∩ p ⁻¹' Fd))) = 0
      have hδΓ : (γ₁ : G) - γ₂ ∈ Γ := Γ.sub_mem γ₁.2 γ₂.2
      by_cases hδt : (γ₁ : G) - γ₂ ∈ tube p R U
      · have hl0 : p ((γ₁ : G) - γ₂) ≠ 0 := fun h0 =>
          hne (Subtype.ext (sub_eq_zero.mp (hΓT _ hδΓ hδt h0)))
        have hlL : p ((γ₁ : G) - γ₂) ∈ L := (hL _).mpr ⟨_, hδΓ, hδt, rfl⟩
        have hN : ν (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd)) = 0 := by
          have := hFd.aedisjoint
            (show (0 : L) ≠ ⟨p ((γ₁ : G) - γ₂), hlL⟩ from fun h => hl0 (congrArg Subtype.val h).symm)
          rw [Function.onFun, zero_vadd] at this
          exact this
        refine measure_mono_null ?_ (show μ ((fun w => -(γ₂ : G) + w) ⁻¹' ((tube p R U : Set G) ∩
            p ⁻¹' (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd)))) = 0 by
          rw [measure_preimage_add]
          exact hnull _ hN)
        rintro x ⟨hx1, hx2⟩
        obtain ⟨y₁, ⟨hy₁T, hy₁F⟩, rfl⟩ := hx1
        obtain ⟨y₂, ⟨hy₂T, hy₂F⟩, hxy⟩ := hx2
        have hxy' : (γ₂ : G) + y₂ = γ₁ + y₁ := hxy
        have e : (γ₁ : G) - γ₂ = y₂ - y₁ := by
          rw [sub_eq_sub_iff_add_eq_add, ← hxy']
          exact add_comm _ _
        have hy : -(γ₂ : G) + ((γ₁ : G) + y₁) = y₂ := by
          rw [← hxy', neg_add_cancel_left]
        show -(γ₂ : G) + ((γ₁ : G) + y₁) ∈ (tube p R U : Set G) ∩
          p ⁻¹' (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd))
        rw [hy]
        refine ⟨hy₂T, hy₂F, p y₁, hy₁F, ?_⟩
        show p ((γ₁ : G) - γ₂) + p y₁ = p y₂
        rw [← map_add, e, sub_add_cancel]
      · refine measure_mono_null ?_ measure_empty
        rintro x ⟨hx1, hx2⟩
        obtain ⟨y₁, ⟨hy₁T, -⟩, rfl⟩ := hx1
        obtain ⟨y₂, ⟨hy₂T, -⟩, hxy⟩ := hx2
        have hxy' : (γ₂ : G) + y₂ = γ₁ + y₁ := hxy
        have e : (γ₁ : G) - γ₂ = y₂ - y₁ := by
          rw [sub_eq_sub_iff_add_eq_add, ← hxy']
          exact add_comm _ _
        exact hδt (e ▸ (tube p R U).sub_mem hy₂T hy₁T)
  have hint1 : ∫ w in 𝓕, h w ∂μ = ∫ w in (tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd, h w ∂μ := by
    rw [h𝓕.setIntegral_eq hΦ (fun γ w => hΓ γ γ.2 w), setIntegral_congr_set hΦae.symm]
  have hint2 : ∫ w in (tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd, h w ∂μ =
      ∫ v in toMeasurable ν Fd, h (R v) ∂((μ.restrict (tube p R U)).map p) := by
    rw [setIntegral_map (f := fun v => h (R v)) hFd₀m
      (show Continuous (fun v => h (R v)) from hc.comp hR).aestronglyMeasurable hpm.aemeasurable,
      Measure.restrict_restrict (hpm hFd₀m), Set.inter_comm]
    apply setIntegral_congr_fun ((hpm hFd₀m).inter hTm)
    intro w hw
    exact hfac w hw.2
  have hmass : (c : ENNReal) * ν Fd = 1 := by
    have e2 : μ ((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd) = (c : ENNReal) * ν Fd := by
      rw [Set.inter_comm, ← Measure.restrict_apply (hpm hFd₀m), ← Measure.map_apply hpm hFd₀m, hcν]
      simp [measure_toMeasurable]
    rw [← e2, measure_congr hΦae, hΦ.measure_eq h𝓕, h1]
  have hreal : (c : ℝ) * (ν Fd).toReal = 1 := by
    have := congrArg ENNReal.toReal hmass
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at this
  rw [hint1, hint2, hcν, Measure.restrict_smul, integral_smul_nnreal_measure,
    setIntegral_congr_set hFd₀ae, NNReal.smul_def, Complex.real_smul]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by exact_mod_cast hreal)

end Abstract

variable {D : D7} {S T : HSp D}

theorem finW_add (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (y + y') = finW S T y + finW S T y' := by
  ext a k
  simp [finW, TensorProduct.tmul_add]

theorem finW_nsmul (N : ℕ) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (N • y) = N • finW S T y := by
  induction N with
  | zero =>
    ext a k
    simp [finW]
  | succ m ih => rw [succ_nsmul, succ_nsmul, finW_add, ih]

theorem fin_finW (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : IsFinPt (finW S T y) := by
  unfold IsFinPt
  ext a k
  simp only [finW, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
  show (Algebra.TensorProduct.map (fstA (F := D.host.F)) (AlgHom.id D.host.F D.host.E))
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = 0
  rw [Algebra.TensorProduct.map_tmul]
  have h0 : fstA (F := D.host.F) (pairA D.host.F 0 1) = 0 := rfl
  rw [h0, TensorProduct.zero_tmul]

theorem real_rat_sub (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    IsRealPt (S := S) (T := T) (ratW T S yᵀ - finW S T y) := by
  unfold IsRealPt
  ext a k
  simp only [finW, ratW, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply, Matrix.sub_apply,
    Matrix.transpose_apply, map_sub]
  show (Algebra.TensorProduct.map (sndA (F := D.host.F)) (AlgHom.id D.host.F D.host.E))
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] y k a) -
    (Algebra.TensorProduct.map (sndA (F := D.host.F)) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = 0
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  have h1 : sndA (F := D.host.F) (pairA D.host.F 0 1) = 1 := rfl
  rw [h1, map_one, sub_self]

theorem realPt_ratW (C : Ctx S T) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    C.realPt (ratW T S yᵀ) = embR C.X y := by
  funext σ k a
  have h1 : infPart D (incA D (y k a)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a := by
    show (Algebra.TensorProduct.map (fstA (F := D.host.F)) (AlgHom.id D.host.F D.host.E))
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] y k a) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have h2 : (C.θ (C.m.e.symm σ)) ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a) =
      tauE D (C.m.e.symm σ) (y k a) := (C.inf (C.m.e.symm σ)).1 (y k a)
  have h3 := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at h3
  simp only [Ctx.realPt, embR, ratW, compAt, Matrix.map_apply, Matrix.transpose_apply]
  rw [h1, h2, h3, ComplexEmbedding.conjugate_coe_eq]

theorem nsmul_cancel_tensor {F A B : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    {m n N : ℕ} (hN : 0 < N) {w w' : Matrix (Fin m) (Fin n) (A ⊗[F] B)} (h : N • w = N • w') : w = w' := by
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have h' : (N : F) • w = (N : F) • w' := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h
  exact smul_right_injective _ hN' h'

theorem nsmul_cancel {N : ℕ} (hN : 0 < N) {w w' : WO S T} (h : N • w = N • w') : w = w' := nsmul_cancel_tensor (F := D.host.F) hN h

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)

theorem eq_zero_of_embR {y : Matrix (Fin n) (Fin r) E} (h : embR X y = 0) : y = 0 := by
  ext k a
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hτ : τ0 ∈ X.Ψ
  · have h1 := congrFun (congrFun (congrFun h ⟨τ0, hτ⟩) k) a
    simpa [embR] using h1
  · have hc : ComplexEmbedding.conjugate τ0 ∈ X.Ψ := by
      by_contra hc
      exact hτ ((X.cmType τ0).mpr hc)
    have h1 := congrFun (congrFun (congrFun h ⟨_, hc⟩) k) a
    simpa [embR] using h1

theorem embR_smul (N : ℕ) (y : Matrix (Fin n) (Fin r) E) : embR X (N • y) = N • embR X y := by
  funext τ k a
  simp [embR]

theorem mem_latR_iff (N : ℕ) (v : WR X n) :
    v ∈ latR X n N ↔ ∃ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) ∧ v = N • embR X y := by
  unfold latR
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨0, fun k => show (0 : Fin r → E) ∈ X.Λ from X.Λ.zero_mem, ?_⟩
      funext τ k a
      simp [embR]
    | add x x' _ _ hx hx' =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hx'
      refine ⟨u + u', fun k => show u k + u' k ∈ X.Λ from X.Λ.add_mem (hu k) (hu' k), ?_⟩
      funext τ k a
      simp [embR, smul_add]
    | neg x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨-u, fun k => show -u k ∈ X.Λ from X.Λ.neg_mem (hu k), ?_⟩
      funext τ k a
      simp [embR]
  · rintro ⟨y, hy, rfl⟩
    exact AddSubgroup.subset_closure ⟨y, hy, rfl⟩

omit [IsCMField E] in
theorem span_stdL : Submodule.span E (stdL E n : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  apply Submodule.subset_span
  rw [Pi.basisFun_apply]
  exact Submodule.subset_span ⟨a, rfl⟩

theorem haar_WR : (volume : Measure (WR X n)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi.isAddHaarMeasure _
  have h2 : (volume : Measure (Fin n → Fin r → ℂ)).IsAddHaarMeasure := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi.isAddHaarMeasure _
  unfold WR
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi.isAddHaarMeasure _

end Classical

theorem mul_conj_phase {a : ℂ} (ha : ‖a‖ = 1) (x y : ℂ) : a * x * conj (a * y) = x * conj y := by
  have h1 : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  rw [map_mul]
  linear_combination (x * conj y) * h1

theorem ipO_eq_mean : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f', C.IsTh f → C.IsTh f' → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → (∃ Fd : Set (WR C.X S.rank), IsAddFundamentalDomain (latR C.X S.rank N) Fd volume) ∧ ∀ Fd : Set (WR C.X S.rank), IsAddFundamentalDomain (latR C.X S.rank N) Fd volume → ∀ F : WR C.X S.rank → ℂ, (∀ w, IsRealPt w → f w * conj (f' w) = F (C.realPt w)) → ipO μ 𝓕 f f' = ((volume Fd).toReal : ℂ)⁻¹ * ∫ v in Fd, F v := by
  intro D S T C μ 𝓕 hcov f f' hf hf'
  unfold IsCovolOne at hcov
  obtain ⟨hμ, h𝓕, h1⟩ := hcov
  obtain ⟨R, hRc, hpc, hpadd, hRv, hRreal, hfp, hfin0, -, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hstdfg : (stdL D.host.E S.rank).FG := by
    unfold stdL
    exact Submodule.fg_span (Set.finite_range _)
  obtain ⟨hA1, hA2, hA3, -, hA5, hA6⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C (stdL D.host.E S.rank) C.X.Λ
    ⟨hstdfg, span_stdL⟩ ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨-, -, hTh⟩ := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  obtain ⟨-, -, -, -, -, Nf, hNf, hfN⟩ := hTh f hf
  obtain ⟨-, -, -, -, -, Nf', hNf', hfN'⟩ := hTh f' hf'
  have hψ : ∀ x, ‖C.ψ x‖ = 1 := C.std.1.2.1
  set A := hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) with hAdef
  refine ⟨Nf * Nf', Nat.mul_pos hNf hNf', fun N hN hdvd => ?_⟩
  obtain ⟨k, hk⟩ := hdvd
  have hfU : ∀ u ∈ A, C.rho (N • u) f = f := by
    intro u hu
    have e : N • u = Nf • ((Nf' * k) • u) := by rw [smul_smul, hk, mul_assoc]
    rw [e]
    exact hfN _ (A.nsmul_mem hu _)
  have hf'U : ∀ u ∈ A, C.rho (N • u) f' = f' := by
    intro u hu
    have e : N • u = Nf' • ((Nf * k) • u) := by
      rw [smul_smul, hk]
      congr 1
      ring
    rw [e]
    exact hfN' _ (A.nsmul_mem hu _)
  set h : WO S T → ℂ := fun w => f w * conj (f' w) with hhdef
  have hstep : ∀ w₀ w, C.rho w₀ f = f → C.rho w₀ f' = f' → h (w + w₀) = h w := by
    intro w₀ w e e'
    have a1 := congrFun e w
    have a2 := congrFun e' w
    simp only [Ctx.rho, heisO] at a1 a2
    simp only [hhdef]
    conv_rhs => rw [← a1, ← a2]
    rw [mul_conj_phase (hψ _)]
  have hΓ : ∀ γ ∈ ratL T S, ∀ w, h (γ + w) = h w := by
    rintro _ ⟨z, rfl⟩ w
    have q1 := hf.quasi z w
    have q2 := hf'.quasi z w
    simp only [hhdef]
    change f (ratW T S z + w) * conj (f' (ratW T S z + w)) = _
    rw [q1, q2, mul_conj_phase (hψ _)]
  set U : AddSubgroup (WO S T) := A.map (DistribSMul.toAddMonoidHom (WO S T) N) with hUdef
  have hmemU : ∀ x, x ∈ U ↔ ∃ u ∈ A, N • u = x := fun x => AddSubgroup.mem_map
  have hhU : ∀ u ∈ U, ∀ w, h (w + u) = h w := by
    intro x hx w
    obtain ⟨u, hu, rfl⟩ := (hmemU x).mp hx
    exact hstep _ w (hfU u hu) (hf'U u hu)
  set p : WO S T →+ WR C.X S.rank := AddMonoidHom.mk' C.realPt hpadd with hpdef
  have hpapp : ∀ w, p w = C.realPt w := fun w => rfl
  have hfinsmul : ∀ u ∈ A, C.realPt (N • u) = 0 := by
    intro u hu
    rw [← hpapp, map_nsmul, hpapp, hfin0 u (hA3 u hu).1, smul_zero]
  have hRemb : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
      R (embR C.X y) = ratW T S yᵀ - finW S T y := by
    intro y
    have e1 := hRreal _ (real_rat_sub y)
    have e2 : C.realPt (ratW T S yᵀ - finW S T y) = embR C.X y := by
      rw [← hpapp, map_sub, hpapp, hpapp, realPt_ratW, hfin0 _ (fin_finW y), sub_zero]
    rwa [e2] at e1
  have hmemT : ∀ w, w ∈ tube p R U ↔ ∃ u ∈ A, N • u = w - R (C.realPt w) :=
    fun w => (mem_tube p R U w).trans (hmemU _)
  have hO : IsOpen (tube p R U : Set (WO S T)) := by
    convert hA5 N hN using 1
    ext w
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
    rw [hmemT]
    constructor
    · rintro ⟨u, hu, e⟩
      refine ⟨u, hu, ?_⟩
      rw [show w - N • u = R (C.realPt w) by rw [e]; abel]
      exact (hRv _).1
    · rintro ⟨u, hu, hr⟩
      refine ⟨u, hu, ?_⟩
      have e1 := hRreal _ hr
      have e2 : C.realPt (w - N • u) = C.realPt w := by
        rw [← hpapp, map_sub, hpapp, hpapp, hfinsmul u hu, sub_zero]
      rw [e2] at e1
      rw [e1]
      abel
  have hcov' : ∀ w, ∃ γ ∈ ratL T S, γ + w ∈ tube p R U := by
    intro w
    obtain ⟨y, hy⟩ := hA1 _ (hfp w)
    obtain ⟨-, hsplit⟩ := hA3 _ hy
    obtain ⟨y', -, u', hu', e⟩ := hsplit N hN
    refine ⟨-(ratW T S (y + y')ᵀ), (ratL T S).neg_mem ⟨(y + y')ᵀ, rfl⟩, ?_⟩
    rw [hmemT]
    refine ⟨u', hu', ?_⟩
    have e3 : C.realPt (-(ratW T S (y + y')ᵀ) + w) = -embR C.X (y + y') + C.realPt w := by
      rw [← hpapp, map_add, map_neg, hpapp, hpapp, realPt_ratW]
    rw [e3, map_add, map_neg, hRemb, finW_add]
    rw [show N • u' = w - R (C.realPt w) - finW S T y - finW S T y' by rw [e]; abel]
    abel
  have hinj : ∀ γ ∈ ratL T S, γ ∈ U → γ = 0 := by
    rintro _ ⟨z, rfl⟩ hzU
    obtain ⟨u, hu, e⟩ := (hmemU _).mp hzU
    change ratW T S z = 0
    have e' : N • u = ratW T S z := e
    have e1 : embR C.X zᵀ = 0 := by
      rw [← realPt_ratW C zᵀ, Matrix.transpose_transpose, ← e', hfinsmul u hu]
    have e2 := eq_zero_of_embR C.X e1
    rw [← Matrix.transpose_transpose z, e2]
    ext i j
    simp [ratW]
  have hL : ∀ v, v ∈ latR C.X S.rank N ↔ ∃ γ ∈ ratL T S, γ ∈ tube p R U ∧ p γ = v := by
    intro v
    rw [mem_latR_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨ratW T S (N • y)ᵀ, ⟨_, rfl⟩, ?_, ?_⟩
      · rw [hmemT]
        refine ⟨finW S T y, (hA2 y).mpr ((GlobalTheory.SW.TensLat.mem_tens_stdL C.X.Λ y).mpr hy), ?_⟩
        rw [realPt_ratW, hRemb, finW_nsmul]
        abel
      · show C.realPt _ = _
        rw [realPt_ratW, embR_smul]
    · rintro ⟨_, ⟨z, rfl⟩, hzt, rfl⟩
      obtain ⟨y, rfl⟩ : ∃ y, z = yᵀ := ⟨zᵀ, (Matrix.transpose_transpose z).symm⟩
      change ratW T S yᵀ ∈ tube p R U at hzt
      rw [hmemT, realPt_ratW, hRemb] at hzt
      obtain ⟨u, hu, e⟩ := hzt
      have e2 : finW S T y = N • u := by
        rw [e]
        abel
      have hNE : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
      have hy3 : N • ((N : D.host.E)⁻¹ • y) = y := by
        rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
      have e3 : finW S T ((N : D.host.E)⁻¹ • y) = u := by
        apply nsmul_cancel hN
        rw [← finW_nsmul, hy3, e2]
      have hmem := (GlobalTheory.SW.TensLat.mem_tens_stdL C.X.Λ _).mp ((hA2 _).mp (by rw [e3]; exact hu))
      refine ⟨(N : D.host.E)⁻¹ • y, hmem, ?_⟩
      show C.realPt (ratW T S yᵀ) = N • embR C.X ((N : D.host.E)⁻¹ • y)
      rw [realPt_ratW, ← embR_smul, hy3]
  have hUc : IsCompact (U : Set (WO S T)) := by
    rw [hUdef, AddSubgroup.coe_map]
    exact hA6.image (show Continuous (DistribSMul.toAddMonoidHom (WO S T) N) from continuous_nsmul N)
  obtain ⟨hTG, hLC, hSC, hT2, hdisc, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := hT2
  have := hdisc
  have := hSC
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable (ratL T S) := GlobalTheory.countable_of_discrete_addSubgroup (ratL T S)
  have := haar_WR C.X (n := S.rank)
  have := hμ
  have hLdisc : DiscreteTopology (latR C.X S.rank N) :=
    discrete_image (p := p) hRc hUc (ratL T S) (latR C.X S.rank N) (fun v hv => (hL v).mp hv)
  obtain ⟨Fd0, -, -, hFd0⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (latR C.X S.rank N)
  refine ⟨⟨Fd0, hFd0 volume⟩, fun Fd hFd F hF => ?_⟩
  have hcont : Continuous h := hf.cont.mul (Complex.continuous_conj.comp hf'.cont)
  have key := integral_eq_mean (p := p) (R := R) (U := U) hpc hRc (fun v => (hRv v).2) hUc hO μ volume
    (ratL T S) (latR C.X S.rank N) hL hcov' hinj h𝓕 h1 hFd hcont hΓ hhU
  have hFR : (fun v => h (R v)) = F := by
    funext v
    have := hF (R v) (hRv v).1
    rw [(hRv v).2] at this
    exact this
  show ∫ w in 𝓕, h w ∂μ = _
  rw [key, hFR]

end GlobalTheory.Ker.TorusMean
