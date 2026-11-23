import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetEqSumAddCosetIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterTrivialMatrixLatticeOpenCompactBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LinearModelL2

section General

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

def ip (μ : Measure X) (f g : X → ℂ) : ℂ := ∫ y, f y * (starRingEnd ℂ) (g y) ∂μ

theorem integrable_mul_conj (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f g : X → ℂ} (hf : f ∈ SB X)
    (hg : g ∈ SB X) : Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  have hcf : Continuous f := hf.1.continuous
  have hcg : Continuous g := hg.1.continuous
  have hs : HasCompactSupport (fun y => f y * (starRingEnd ℂ) (g y)) := hf.2.mul_right
  exact (hcf.mul (Complex.continuous_conj.comp hcg)).integrable_of_hasCompactSupport hs

theorem ip_smul_smul (μ : Measure X) (a b : ℂ) (f g : X → ℂ) :
    ip μ (a • f) (b • g) = a * (starRingEnd ℂ) b * ip μ f g := by
  unfold ip
  rw [← integral_const_mul]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem ip_sum_sum (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {V : Type} (F : Finset V) (a : V → ℂ)
    (xs : V → X → ℂ) (hxs : ∀ y, xs y ∈ SB X) :
    ip μ (∑ y ∈ F, a y • xs y) (∑ y ∈ F, a y • xs y) =
      ∑ y ∈ F, ∑ y' ∈ F, a y * (starRingEnd ℂ) (a y') * ip μ (xs y) (xs y') := by
  unfold ip
  have e : (fun z => (∑ y ∈ F, a y • xs y) z * (starRingEnd ℂ) ((∑ y ∈ F, a y • xs y) z)) =
      fun z => ∑ y ∈ F, ∑ y' ∈ F, a y * (starRingEnd ℂ) (a y') * (xs y z * (starRingEnd ℂ) (xs y' z)) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    rw [map_mul]
    ring
  rw [e, integral_finset_sum _ (fun y _ => integrable_finset_sum _ fun y' _ =>
    (integrable_mul_conj μ (hxs y) (hxs y')).const_mul _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_finset_sum _ (fun y' _ => (integrable_mul_conj μ (hxs y) (hxs y')).const_mul _)]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [integral_const_mul]

theorem ip_self (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : f ∈ SB X) :
    ip μ f f = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧ ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  have hcf : Continuous f := hf.1.continuous
  have hs : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ f) :=
    hf.2.comp_left (by norm_num : ‖(0 : ℂ)‖ ^ 2 = 0)
  have hint : Integrable (fun y => ‖f y‖ ^ 2) μ := (hcf.norm.pow 2).integrable_of_hasCompactSupport hs
  have hE : ∀ y, ENNReal.ofReal (‖f y‖ ^ 2) = ‖f y‖ₑ ^ 2 := fun y => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hfin := hint.lintegral_lt_top
  simp only [hE] at hfin
  refine ⟨?_, hfin.ne⟩
  unfold ip
  have e : (fun y => f y * (starRingEnd ℂ) (f y)) = fun y => (((‖f y‖ ^ 2 : ℝ)) : ℂ) := by
    funext y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => by positivity)
    hint.aestronglyMeasurable]
  simp only [hE]

theorem lintegral_ne_zero (μ : Measure X) [μ.IsOpenPosMeasure] {f : X → ℂ} (hf : f ∈ SB X) (h0 : f ≠ 0) :
    ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0 := by
  have hc : Continuous f := hf.1.continuous
  have hcont : Continuous fun Y => ‖f Y‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp hc.enorm
  intro h
  rw [lintegral_eq_zero_iff hcont.measurable] at h
  have h' := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 h
  apply h0
  funext Y
  have := congrFun h' Y
  simpa using this

end General

end GlobalTheory.LinearModelL2

namespace GlobalTheory.LinearModelL2

open GlobalTheory.LinSchur

section Cosets

variable {T : Type} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]

open Classical in

theorem expand (μ : Measure T) [IsFiniteMeasureOnCompacts μ] {V : Type} [AddGroup V]
    (ι : (T → ℂ) →ₗ[ℂ] (V → ℂ)) (hinj : Set.InjOn ι (SB T)) (L : AddSubgroup V) (xs : V → T → ℂ)
    (hxs : ∀ y, xs y ∈ SB T) (hιxs : ∀ y, ι (xs y) = cind L y) (c : ℂ)
    (hP : ∀ y y', ip μ (xs y) (xs y') = if y - y' ∈ L then c else 0) (x : T → ℂ) (hx : x ∈ SB T) (f : V → ℂ)
    (hf : ι x = f) (F : Finset V) (hF : f = ∑ y ∈ F, f y • cind L y) :
    ip μ x x = (∑ y ∈ F, ∑ y' ∈ F, if y - y' ∈ L then f y * (starRingEnd ℂ) (f y') else 0) * c := by
  have hxe : x = ∑ y ∈ F, f y • xs y := by
    refine hinj hx (Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (hxs y)) ?_
    rw [hf, map_sum]
    simp only [map_smul, hιxs]
    exact hF
  rw [hxe, ip_sum_sum μ F f xs hxs, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [hP]
  split_ifs <;> ring

open Classical in
theorem cind_eq_of_sub_mem {V : Type} [AddGroup V] (L : AddSubgroup V) {y y' : V} (h : y - y' ∈ L) :
    cind L y = cind L y' := by
  funext Y
  unfold cind
  have iff : Y - y ∈ L ↔ Y - y' ∈ L := by
    rw [← sub_add_sub_cancel Y y y']
    exact (L.add_mem_cancel_right h).symm
  exact if_congr iff rfl rfl

theorem cind_translate {V : Type} [AddGroup V] (L : AddSubgroup V) (y : V) :
    (fun Y => cind L 0 (Y + -y)) = cind L y := by
  funext Y
  unfold cind
  rw [sub_zero, ← sub_eq_add_neg]

end Cosets

end GlobalTheory.LinearModelL2

namespace GlobalTheory.LinearModelL2

open GlobalTheory.LinSchur

open Classical in

theorem ip_cind {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V) [ν.IsAddRightInvariant] (L : AddSubgroup V) (y y' : V) :
    ip ν (cind L y) (cind L y') = if y - y' ∈ L then ip ν (cind L 0) (cind L 0) else 0 := by
  split_ifs with h
  · rw [cind_eq_of_sub_mem L h, ← cind_translate L y']
    unfold ip
    exact integral_add_right_eq_self (fun Y => cind L 0 Y * (starRingEnd ℂ) (cind L 0 Y)) (-y')
  · unfold ip
    have e : (fun Y => cind L y Y * (starRingEnd ℂ) (cind L y' Y)) = fun _ => 0 := by
      funext Y
      unfold cind
      by_cases h1 : Y - y ∈ L
      · by_cases h2 : Y - y' ∈ L
        · exact absurd (by simpa [sub_sub_sub_cancel_left] using L.sub_mem h2 h1) h
        · simp [h2]
      · simp [h1]
    rw [e, integral_zero]

open Classical in

theorem ip_cosets {T : Type} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : Measure T) (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0)
    (ι : (T → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) (hinj : Set.InjOn ι (SB T))
    (Tr : Matrix (Fin n) (Fin d) k → (T → ℂ) → T → ℂ) (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → (T → ℂ) → T → ℂ)
    (hTr : ∀ C, ∀ φ ∈ SB T, Tr C φ ∈ SB T ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (hMu : ∀ l, ∀ φ ∈ SB T, Mu l φ ∈ SB T ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hTrI : ∀ C φ φ', ip μ (Tr C φ) (Tr C φ') = ip μ φ φ')
    (hMuI : ∀ l φ φ', ip μ (Mu l φ) (Mu l φ') = ip μ φ φ')
    (s : k) (x0 : T → ℂ) (hx0 : x0 ∈ SB T) (hιx0 : ι x0 = cind (latt ψ0 n d s) 0)
    (y y' : Matrix (Fin n) (Fin d) k) :
    ip μ (Tr (-y) x0) (Tr (-y') x0) = if y - y' ∈ latt ψ0 n d s then ip μ x0 x0 else 0 := by
  have hx : ∀ z, Tr (-z) x0 ∈ SB T ∧ ι (Tr (-z) x0) = cind (latt ψ0 n d s) z := fun z =>
    ⟨(hTr _ _ hx0).1, by rw [(hTr _ _ hx0).2, hιx0]; exact cind_translate _ z⟩
  split_ifs with h
  · have e : Tr (-y) x0 = Tr (-y') x0 :=
      hinj (hx y).1 (hx y').1 (by rw [(hx y).2, (hx y').2]; exact cind_eq_of_sub_mem _ h)
    rw [e, hTrI]
  · obtain ⟨l, hl1, hl2⟩ := dual h
    have hm : ∀ z, Mu l (Tr (-z) x0) = ψ0 (l z) • Tr (-z) x0 := fun z => by
      refine hinj (hMu l _ (hx z).1).1 (Submodule.smul_mem _ _ (hx z).1) ?_
      rw [(hMu l _ (hx z).1).2, map_smul, (hx z).2]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul]
      unfold cind
      split_ifs with hY
      · rw [mul_one, mul_one, show l Y = l (Y - z) + l z by rw [← map_add, sub_add_cancel],
          AddChar.map_add_eq_mul, hl1 _ hY, one_mul]
      · simp
    have e := hMuI l (Tr (-y) x0) (Tr (-y') x0)
    rw [hm y, hm y', ip_smul_smul] at e
    have hconj : ∀ w, (starRingEnd ℂ) (ψ0 w) = ψ0 (-w) := fun w => by
      have h1 : ψ0 w * (starRingEnd ℂ) (ψ0 w) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, GlobalTheory.norm_addChar_nonarch ψ0 hψ w]
        simp
      have h2 : ψ0 w * ψ0 (-w) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      exact mul_left_cancel₀ (addChar_ne_zero ψ0 w) (h1.trans h2.symm)
    rw [hconj, ← AddChar.map_add_eq_mul, ← map_neg, ← map_add, ← sub_eq_add_neg] at e
    have e2 : (ψ0 (l (y - y')) - 1) * ip μ (Tr (-y) x0) (Tr (-y') x0) = 0 := by linear_combination e
    rcases mul_eq_zero.mp e2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hl2
    · exact h3

end GlobalTheory.LinearModelL2

namespace GlobalTheory.LinearModelL2

open GlobalTheory.LinSchur
open scoped GlobalTheory.VacAny GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem linIso_lintegral_eq : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
    (∀ μ : @Measure (Fin a × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ ν : @Measure (Matrix (Fin a) (Fin (a + a')) (Fv F v)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖ι φ₁ Y‖ₑ ^ 2 ∂ν = ∫⁻ Y, ‖ι φ Y‖ₑ ^ 2 ∂ν := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι φ hφ φ₁ hφ₁ hnorm ν hν
  letI : MeasurableSpace (Fin a × Fin (a + a') → Fv F v) := borel _
  haveI : BorelSpace (Fin a × Fin (a + a') → Fv F v) := ⟨rfl⟩
  letI : MeasurableSpace (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin (a + a') → Fv F v))
  haveI := hν
  let μ : Measure (Fin a × Fin (a + a') → Fv F v) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.UnitWShape.heisW B G X om om' hTr v t 1 id (fun f hf => hf)
    (fun γ _ f _ => by simp [actAB, mat])
  obtain ⟨hT0, hM0, -, -⟩ := hA ι hι
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hmaps := hbij.mapsTo
  have hsb : ∀ w, ∀ f ∈ SB (Fin a × Fin (a + a') → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) w f ∈ SB _ :=
    fun w f hf => GlobalTheory.SchrSB.schr_mem_SB B.ψ hTr.base.std.1 v w f hf
  have hU : ∀ w f f', ip μ (schr (GlobalTheory.LatVac.psiAt B.ψ v) w f) (schr (GlobalTheory.LatVac.psiAt B.ψ v) w f') = ip μ f f' :=
    fun w f f' => GlobalTheory.schr_unitary (GlobalTheory.LatVac.psiAt B.ψ v) hψc μ hμ w f f'
  obtain ⟨hLoc, hBasis⟩ := GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis a (a + a') (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1
  have hB' : ∀ W ∈ 𝓝 (0 : Matrix (Fin a) (Fin (a + a')) (Fv F v)), ∃ i : {s : Fv F v // s ≠ 0},
      (latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') i.1 : Set _) ⊆ W := fun W hW => by
    obtain ⟨s, hs, h⟩ := hBasis W hW
    exact ⟨⟨s, hs⟩, h⟩
  obtain ⟨⟨s1, hs1⟩, hper1⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : Fv F v // s ≠ 0} => latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s.1)
    (fun s => (hLoc s.1 s.2).1) hB' (ι φ) (hmaps hφ)
  obtain ⟨⟨s2, hs2⟩, hper2⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : Fv F v // s ≠ 0} => latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s.1)
    (fun s => (hLoc s.1 s.2).1) hB' (ι φ₁) (hmaps hφ₁)
  obtain ⟨s, hs, hsub⟩ := hBasis ((latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s1 : Set _) ∩ latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s2)
    (Filter.inter_mem ((hLoc s1 hs1).1.mem_nhds (zero_mem _)) ((hLoc s2 hs2).1.mem_nhds (zero_mem _)))
  set L := latt (GlobalTheory.LatVac.psiAt B.ψ v) a (a + a') s with hLdef
  obtain ⟨Fa, hFa⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator L (hLoc s hs).1 (ι φ) (hmaps hφ) (fun Y C hC => hper1 Y C (hsub hC).1)
  obtain ⟨Fb, hFb⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator L (hLoc s hs).1 (ι φ₁) (hmaps hφ₁) (fun Y C hC => hper2 Y C (hsub hC).2)
  have hcm : ∀ y, cind L y ∈ SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
    fun y => cind_mem (hLoc s hs).1 (hLoc s hs).2 y
  obtain ⟨x0, hx0, hιx0⟩ := hbij.surjOn (hcm 0)
  have hPD := ip_cosets μ (GlobalTheory.LatVac.psiAt B.ψ v) hψc ι hbij.injOn
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C)) (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l))
    (fun C f hf => ⟨hsb _ f hf, hT0 C f hf⟩) (fun l f hf => ⟨hsb _ f hf, hM0 l f hf⟩)
    (fun C => hU _) (fun l => hU _) s x0 hx0 hιx0
  have hιxs : ∀ y, ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT (-y)) x0) = cind L y := fun y => by
    rw [hT0 _ x0 hx0, hιx0]
    exact cind_translate L y
  have eA := expand μ ι hbij.injOn L (fun y => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT (-y)) x0) (fun y => hsb _ x0 hx0) hιxs
    (ip μ x0 x0) hPD φ hφ (ι φ) rfl Fa hFa
  have eB := expand μ ι hbij.injOn L (fun y => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT (-y)) x0) (fun y => hsb _ x0 hx0) hιxs
    (ip μ x0 x0) hPD φ₁ hφ₁ (ι φ₁) rfl Fb hFb
  have eA' := expand ν LinearMap.id (fun _ _ _ _ h => h) L (cind L) hcm (fun y => rfl)
    (ip ν (cind L 0) (cind L 0)) (ip_cind ν L) (ι φ) (hmaps hφ) (ι φ) rfl Fa hFa
  have eB' := expand ν LinearMap.id (fun _ _ _ _ h => h) L (cind L) hcm (fun y => rfl)
    (ip ν (cind L 0) (cind L 0)) (ip_cind ν L) (ι φ₁) (hmaps hφ₁) (ι φ₁) rfl Fb hFb
  have hipD : ip μ φ₁ φ₁ = ip μ φ φ := by
    rw [(ip_self μ hφ₁).1, (ip_self μ hφ).1, hnorm μ hμ]
  have hne : x0 ≠ 0 := fun h => by
    have e := congrFun hιx0 0
    rw [h, map_zero] at e
    simp [cind] at e
  have hc0 : ip μ x0 x0 ≠ 0 := by
    rw [(ip_self μ hx0).1]
    exact_mod_cast (ENNReal.toReal_pos (lintegral_ne_zero μ hx0 hne) (ip_self μ hx0).2).ne'
  rw [eA, eB] at hipD
  have hK := mul_right_cancel₀ hc0 hipD
  have hQ : ip ν (ι φ₁) (ι φ₁) = ip ν (ι φ) (ι φ) := by rw [eA', eB', hK]
  rw [(ip_self ν (hmaps hφ₁)).1, (ip_self ν (hmaps hφ)).1] at hQ
  have hR := Complex.ofReal_injective hQ
  exact (ENNReal.toReal_eq_toReal_iff' (ip_self ν (hmaps hφ₁)).2 (ip_self ν (hmaps hφ)).2).mp hR

end GlobalTheory.LinearModelL2
