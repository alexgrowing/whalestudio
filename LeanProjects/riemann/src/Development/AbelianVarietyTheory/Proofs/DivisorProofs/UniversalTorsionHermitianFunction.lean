import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricChernFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.TorsionForm (IsDatum IsTorsionForm Ext)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (riem transl translPullFactor IsFactor thetaExp IsLat IsPeriodMap)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnivTorsion

def thJ (g : ℕ) : Fl g → Pt (symMat g) g → ℂ :=
  fun l P => Complex.exp (2 * Real.pi * Complex.I * thetaExp (tauU P.1) l P.2)

def thH (g : ℕ) : Pt (symMat g) g → ℝ := fun P => Real.exp (-2 * Real.pi *
  ((fun i => (P.2 i).im) ⬝ᵥ ((((tauU P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))

theorem isLat_stdLat (g : ℕ) : IsLat (stdLat g) := by
  unfold IsLat stdLat
  exact ⟨inferInstance, inferInstance⟩

theorem riem_int (g : ℕ) : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∃ k : ℤ, riem l l' = k := by
  have hint : ∀ l ∈ stdLat g, ∀ i, ∃ k : ℤ, l i = k := by
    intro l hl i
    obtain ⟨k, hk⟩ := ((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ l).1 hl i
    exact ⟨k, by simpa using hk.symm⟩
  intro l hl l' hl'
  choose a ha using hint l hl
  choose b hb using hint l' hl'
  refine ⟨∑ i, (a (Sum.inr i) * b (Sum.inl i) - a (Sum.inl i) * b (Sum.inr i)), ?_⟩
  simp [riem, ha, hb]

theorem isDatum_theta (g : ℕ) :
    IsDatum (siegel g) tauU (stdLat g) (thJ g) (thH g) ∧ ChernIsFlat (siegel g) tauU (thH g) := by
  have hτ := (GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected g).1
  obtain ⟨hm, hc⟩ := GlobalTheory.ThetaMet.isMetric_chernIsFlat hτ
  exact ⟨⟨hτ, isLat_stdLat g, (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.theta_factor hτ).1, hm⟩, hc⟩

theorem isFactor_transl {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) {M : Submodule ℤ (Fl g)}
    {j : Fl g → Pt E g → ℂ} (hj : IsFactor B τ M j) (x : Fl g) :
    IsFactor B τ M (translPullFactor τ x j) := by
  refine ⟨fun l hl => ⟨(hj.1 l hl).1.comp (GlobalTheory.FlatRigidity.differentiableOn_transl hτ x)
    fun P hP => GlobalTheory.FlatRigidity.transl_mem τ x hP,
    fun P hP => (hj.1 l hl).2 _ (GlobalTheory.FlatRigidity.transl_mem τ x hP)⟩, fun l hl l' hl' P hP => ?_⟩
  simp only [translPullFactor]
  have hc : transl τ x (transl τ l' P) = transl τ l' (transl τ x P) := by
    rw [GlobalTheory.FlatRigidity.transl_transl, GlobalTheory.FlatRigidity.transl_transl, add_comm]
  rw [hc]
  exact hj.2 l hl l' hl' _ (GlobalTheory.FlatRigidity.transl_mem τ x hP)

theorem finset_fin_two_eq_cases (I : Finset (Fin (1 + 1))) : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = Finset.univ := by
  revert I; decide

end GlobalTheory.UnivTorsion

namespace GlobalTheory.UnivTorsion

theorem univTorsion_hermFun : GlobalTheory.Published.BismutKoehlerTorsion → Naturality → ∀ g : ℕ,
    ∃ F : symMat g → symMat g → Ext (1 + 1), IsHermFun g F ∧ ∀ s ∈ siegel g, ∀ (v : symMat g)
      (T : Ext (1 + 1)), IsUnivTorsion g s v T ↔ T = F s v := by
  intro hBK hN g
  obtain ⟨_, hOne, hIso, hTr, _, _, hAc⟩ := hN
  have hτ := (GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected g).1
  have hsc := (GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected g).2
  obtain ⟨hD, hC⟩ := isDatum_theta g
  have hA := hAc (symMat g) g (siegel g) tauU (stdLat g) (thJ g) (thH g) hD hC
  set n := Module.finrank ℂ (symMat g) with hn
  set bs := Module.finBasis ℂ (symMat g) with hbs
  obtain ⟨T, hTs, hT⟩ := hBK (symMat g) g n (siegel g) tauU (stdLat g) (thJ g) (thH g) hD hA bs
  set F : symMat g → symMat g → Ext (1 + 1) := fun s v I => if I = ∅ then T s ∅ else
    if I = Finset.univ then ∑ i, ∑ k, bs.repr v i * star (bs.repr v k) * T s {i.castAdd n, k.natAdd n}
    else 0 with hF
  have key : ∀ s ∈ siegel g, ∀ v,
      IsTorsionForm tauU (stdLat g) (thJ g) (thH g) ![v] s (F s v) := by
    intro s hs v
    obtain ⟨T', hT'1, hT'0, hT'u⟩ := hOne (symMat g) g n (siegel g) tauU (stdLat g) (thJ g) (thH g)
      hD bs (bs.repr v) s hs (T s) (((hT s hs).1 (T s)).2 rfl)
    rw [bs.sum_repr] at hT'1
    obtain ⟨T1, -, hT1⟩ := hBK (symMat g) g 1 (siegel g) tauU (stdLat g) (thJ g) (thH g) hD hA ![v]
    obtain ⟨hu, hz, -, -⟩ := hT1 s hs
    have h1 : T' = T1 s := (hu T').1 hT'1
    have e : T' = F s v := by
      funext I
      rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
      · simpa [hF] using hT'0
      · rw [h1, hz {0} (by decide)]; simp [hF]
      · rw [h1, hz {1} (by decide)]; simp [hF]
      · rw [hT'u, hF]
        simp only
        rw [if_neg Finset.univ_nonempty.ne_empty, if_true]
    rw [← e]; exact hT'1
  refine ⟨F, ?_, fun s hs v T' => ⟨fun ⟨j, m, hjm, hcm, htor⟩ => ?_, fun h => ?_⟩⟩
  · refine ⟨?_, fun s hs => ⟨⟨(T s ∅).re, fun v => ?_⟩,
      fun v w => -Complex.I * ∑ i, ∑ k, bs.repr v i * star (bs.repr w k) * T s {i.castAdd n, k.natAdd n},
      fun a v v' w => ?_, fun v w => ?_, fun v => ?_⟩⟩
    · have hTc : ContinuousOn (fun x : symMat g × symMat g => T x.1) (siegel g ×ˢ Set.univ) :=
        hTs.continuousOn.comp continuousOn_fst fun x hx => hx.1
      have hr : ∀ i, Continuous fun x : symMat g × symMat g => bs.repr x.2 i := fun i =>
        ((bs.coord i).continuous_of_finiteDimensional).comp continuous_snd
      refine continuousOn_pi.2 fun I => ?_
      by_cases h0 : I = ∅
      · simp only [hF, h0, if_true]
        exact (continuous_apply (∅ : Finset (Fin (n + n)))).comp_continuousOn hTc
      by_cases h1 : I = Finset.univ
      · simp only [hF, h0, h1, if_false, if_true]
        refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun k _ => ?_
        exact (((hr i).mul (hr k).star).continuousOn).mul
          ((continuous_apply _).comp_continuousOn hTc)
      · simp only [hF, h0, h1, if_false]
        exact continuousOn_const
    · have him := (hT s hs).2.2.1
      simp only [hF, if_true]
      exact Complex.ext (by simp) (by simp [him])
    · simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    · have hh := (hT s hs).2.2.2
      have hs' : ∀ i k : Fin n, star (T s {i.castAdd n, k.natAdd n}) = -T s {k.castAdd n, i.natAdd n} :=
        fun i k => by rw [hh i k, neg_neg]
      simp only [star_mul', star_neg, star_sum, star_star, hs']
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [Complex.star_def, Complex.conj_I]
      ring
    · simp only [hF, if_neg Finset.univ_nonempty.ne_empty, if_true]
      rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  · obtain ⟨x, φ, hφi, hφm⟩ := GlobalTheory.FlatRigidity.rigidity hτ hsc (stdLat g) (isLat_stdLat g)
      (riem_int g) (thJ g) j (thH g) m hD.2.2.1 hD.2.2.2 hC hjm.2.2.1 hjm.2.2.2 hcm
    obtain ⟨hmx, hcx⟩ := GlobalTheory.FlatTransl.translate_isMetric_chernIsFlat hτ (stdLat g) (thJ g) (thH g)
      hD.2.2.2 hC x
    have hDx : IsDatum (siegel g) tauU (stdLat g) (translPullFactor tauU x (thJ g))
        (fun P => thH g (transl tauU x P)) := ⟨hτ, isLat_stdLat g, isFactor_transl hτ hD.2.2.1 x, hmx⟩
    have h1 := hIso (symMat g) g 1 (siegel g) tauU (stdLat g) j _ m _ φ hjm hDx hφi hφm ![v] s hs T' htor
    have h2 := hTr (symMat g) g 1 (siegel g) tauU (stdLat g) (thJ g) (thH g) hD x ![v] s hs _
      (key s hs v)
    obtain ⟨T1, -, hT1⟩ := hBK (symMat g) g 1 (siegel g) tauU (stdLat g) _ _ hDx
      (hAc _ g _ _ _ _ _ hDx hcx) ![v]
    exact (((hT1 s hs).1 T').1 h1).trans (((hT1 s hs).1 _).1 h2).symm
  · subst h
    exact ⟨thJ g, thH g, hD, hC, key s hs v⟩

end GlobalTheory.UnivTorsion
