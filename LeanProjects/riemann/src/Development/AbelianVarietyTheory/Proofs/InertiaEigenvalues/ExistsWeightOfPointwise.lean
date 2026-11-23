import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimes
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CuspAndSupCLeOfBounded
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BpfUniform

theorem exists_complex_zero {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hI
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let _ : Algebra K ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨κ.comp (Ideal.Quotient.mkₐ K M), fun x hx => ?_⟩
  show κ (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]

theorem exists_finset_span_eq_top {A ι : Type} [CommRing A] (v : ι → A) (h : Ideal.span (Set.range v) = ⊤) :
    ∃ s : Finset ι, Ideal.span (v '' (s : Set ι)) = ⊤ := by
  classical
  have h1 : (1 : A) ∈ Submodule.span A (Set.range v) := by
    show (1 : A) ∈ Ideal.span (Set.range v)
    rw [h]; trivial
  obtain ⟨t, ht, h1t⟩ := Submodule.mem_span_finite_of_mem_span h1
  choose g hg using fun x : t => ht x.2
  refine ⟨Finset.univ.image g, (Ideal.eq_top_iff_one _).2 (Submodule.span_mono ?_ h1t)⟩
  intro x hx
  exact ⟨g ⟨x, hx⟩, by simp, hg ⟨x, hx⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_finite_subfamily {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (la : HeightOneSpectrum (𝓞 c.F)) (hM : GlobalTheory.Reg.ModelAt Xo c la) (σ : c.F →+* ℂ) {ι : Type}
    (a : ι → (E →+* ℂ) × ℕ → ℕ) (n : ι → ℕ) (f : ι → Rul Xo c) (hf : ∀ i, f i ∈ sec Xo c (a i) (n i))
    (hnz : ∀ z : FrPt Xo c (CAt σ), ∃ i, evR Xo c (f i) z ≠ 0) :
    ∃ s : Set ι, s.Finite ∧ ∀ z : FrPt Xo c (CAt σ), ∃ i ∈ s, evR Xo c (f i) z ≠ 0 := by
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨Y, hP⟩ := hM
  obtain ⟨J, hJ, P, hC⟩ := GlobalTheory.Reg.exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c
    hE.bc (la.valuation c.F).valuationSubring Y hP
  have hev := fun i => GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE (a i) (n i) (f i) (hf i)
  have htop : ∀ (p : Σ j : J, ((P j).es : Set (P j).Ω)),
      Ideal.span (Set.range fun i => (evR Xo c (f i) ((P p.1).y p.2.1 p.2.2) : (P p.1).R p.2.1)) = ⊤ := by
    rintro ⟨j, e, he⟩
    by_contra hne
    haveI := (P j).sm e he
    obtain ⟨ψ, hψ⟩ := exists_complex_zero σ _ hne
    obtain ⟨z, hz⟩ := hE.bc _ (CAt σ) ψ ((P j).y e he)
    obtain ⟨i, hi⟩ := hnz z
    apply hi
    rw [(hev i _).1 _ ψ _ _ hz]
    exact hψ _ (Ideal.subset_span ⟨i, rfl⟩)
  choose s hs using fun p => exists_finset_span_eq_top _ (htop p)
  refine ⟨⋃ p, (s p : Set ι), Set.finite_iUnion fun p => (s p).finite_toSet, fun y => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨j, e, he, ψ, z, t, -, hz, hb⟩ := hC (CAt σ) ⊤ (fun _ => trivial) y
  by_contra hcon
  push Not at hcon
  have hle : Ideal.span ((fun i => (evR Xo c (f i) ((P j).y e he) : (P j).R e)) '' (s ⟨j, e, he⟩ : Set ι)) ≤
      RingHom.ker ψ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    show ψ _ = 0
    rw [← (hev i _).1 _ ψ _ _ hz, GlobalTheory.ArcQ.evR_frBor_of_isDomain hE (hf i) t y z hb,
      hcon i (Set.mem_iUnion.2 ⟨⟨j, e, he⟩, hi⟩), mul_zero]
  rw [hs ⟨j, e, he⟩] at hle
  have h1 : ψ 1 = 0 := hle Submodule.mem_top
  rw [map_one] at h1
  exact one_ne_zero h1

theorem bounded_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = 0 ∨ X.p0 = r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) :
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := by
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  let K : Set (Frame X.Ψ r) := {x | X.IsOrtho x}
  have hKd : K ⊆ X.dom := fun x hx => PIW.FdPA.orthonormal_domain r X x hx
  have hKc : IsClosed K := by
    have e : K = ⋂ τ : X.Ψ, {x : Frame X.Ψ r | gram τ.1 X.Gm (mat x τ) =
        Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)} := by
      ext x; simp [K, Data.IsOrtho]
    rw [e]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    unfold gram hermC col mat
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    fun_prop
  have hKb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max R 0, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun b => ?_
    exact (hR x hx τ a b).trans (le_max_left _ _)
  obtain ⟨C, hC⟩ := (Metric.isCompact_of_isClosed_isBounded hKc hKb).exists_bound_of_continuousOn
    (hP.1.continuousOn.mono hKd)
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨b, hb, ho⟩ := (orthonormalFlagTranslate_holds r X).1 x hx
  rw [← (orthonormalFlagTranslate_holds r X).2.1 la P hP.2.1 x hx b hb,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit X la P (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho X ho)]
  exact hC _ ho

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem laU_one (V : Unf Xo c σ r) (n : ℕ) : laU V (fun _ => 1) n = laU V 0 (n + 2) := by
  funext k τ j
  have e : (n + 2) / 2 = n / 2 + 1 := by omega
  simp only [laU, Pi.zero_apply, e]
  split_ifs <;> push_cast <;> ring

theorem pow_mem_holSub0 (V : Unf Xo c σ r) {n : ℕ} (hn : Even n) {P : FDSec V.X}
    (hP : P ∈ Formalism.L2.Pj.holSub0 V.X (laU V 0 n)) (e : ℕ) :
    P ^ (e + 1) ∈ Formalism.L2.Pj.holSub0 V.X (laU V 0 ((e + 1) * n)) := by
  induction e with
  | zero => simpa using hP
  | succ e ih =>
    rw [pow_succ]
    refine ⟨?_, fun k x hx => by simp [hP.2 k x hx]⟩
    have h1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 ih.1
    have h2 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hP.1
    refine (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).2 fun k => ?_
    have e1 : laU V 0 ((e + 1 + 1) * n) k = laU V 0 ((e + 1) * n) k + laU V 0 n k := by
      have := GlobalTheory.CuspProduct.laU_add (Formalism.L2.PjFree.Unf.ofPj V) 0 0 ((e + 1) * n) n (hn.mul_left _) hn k
      rw [add_zero, show (e + 1) * n + n = (e + 1 + 1) * n by ring] at this
      exact this
    rw [e1]
    exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ (h1 k) _ (h2 k).1

theorem exists_holSub0_of_SS (V : Unf Xo c σ r) (la : ∀ k, Wt (V.X k).Ψ r) (k : V.Comp) {P : Frame (V.X k).Ψ r → ℂ}
    (hP : P ∈ (V.X k).SS (la k)) : ∃ Q ∈ Formalism.L2.Pj.holSub0 V.X la, ∀ x ∈ (V.X k).dom, Q k x = P x := by
  classical
  refine ⟨Pi.single k ((V.X k).dom.indicator P), ⟨holCusp_mem_holSub _ _ fun k' => ?_, fun k' y' hy' => ?_⟩,
    fun x hx => ?_⟩
  · by_cases h : k' = k
    · subst h
      simp only [Pi.single_eq_same]
      exact (GlobalTheory.DomCongr.bddSec_cusp_congr E r _ _ P _ (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
    · simp only [Pi.single_eq_of_ne h]
      exact (siegelSpaceAlgebra_holds (E := E) r (V.X k') (la k') (la k') 0).1.1
  · by_cases h : k' = k
    · subst h
      simp only [Pi.single_eq_same]
      exact Set.indicator_of_notMem hy' _
    · simp only [Pi.single_eq_of_ne h, Pi.zero_apply]
  · simp only [Pi.single_eq_same]
    exact Set.indicator_of_mem hx _

theorem exists_scalar_ne_zero
    (hP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ y ∈ X.dom, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), P y ≠ 0)
    (V : Unf Xo c σ r) (hU : IsUnf V)
    (hχ : ∀ n, Even n → ∀ k, ∀ γ ∈ (V.X k).Γ, (V.X k).χ (laU V 0 n k) γ = 1)
    (k : V.Comp) (x : Frame (V.X k).Ψ r) (hx : x ∈ (V.X k).dom) :
    ∃ n, 0 < n ∧ Even n ∧ ∃ Q ∈ Formalism.L2.Pj.holSub0 V.X (laU V 0 n), Q k x ≠ 0 := by
  by_cases hdef : (V.X k).p0 = 0 ∨ (V.X k).p0 = r
  · obtain ⟨n, hn, he, f, hf, hne⟩ := GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H Dw l Xo c σ (V.un k ⟨x, hx⟩)
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, he⟩
    have hs := hU.2.2.2.2.1 0 n hD f hf k
    obtain ⟨τ0⟩ : Nonempty (V.X k).Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : τ ∈ (V.X k).Ψ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, not_not.mp (fun h' => h (((V.X k).cmType τ).mpr h'))⟩⟩
    obtain ⟨Q, hQ, hQx⟩ := exists_holSub0_of_SS V (laU V 0 n) k
      (GlobalTheory.BoundedCusp.mem_SS_of_definite _ _ τ0 hdef _ ⟨hs, bounded_of_definite _ hdef _ _ hs⟩)
    refine ⟨n, hn, he, Q, hQ, ?_⟩
    have e : rdU V f k x = toC (evR Xo c f (V.un k ⟨x, hx⟩)) := dif_pos hx
    rw [hQx x hx, e]
    exact hne
  · have hle := (V.X k).p0_le
    have hla : ∀ n : ℕ, laU V 0 n k = fun (τ : (V.X k).Ψ) (j : Fin r) =>
        if (V.X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ) := fun n => by
      funext τ j
      simp [laU]
    obtain ⟨n, -, hn, he, P, hPm, hne⟩ := hP E r (V.X k) (by omega) (by omega)
      (fun n hn γ hγ => by rw [← hla]; exact hχ n hn k γ hγ) x hx 0
    rw [← hla] at hPm
    obtain ⟨Q, hQ, hQx⟩ := exists_holSub0_of_SS V (laU V 0 n) k hPm
    exact ⟨n, hn, he, Q, hQ, by rw [hQx x hx]; exact hne⟩

end Model

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_one (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : Formalism.L2.Pj.InR D j)
    (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (n : ℕ) (hev : Even n)
    (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n) :
    Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (fun _ => 1) n) ≤
      Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j (fun _ => 1) n : Set (T.R j))) := by
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have hdom : Dom (fun _ : (D.host.E →+* ℂ) × ℕ => 1) n := ⟨fun _ => antitone_const, hev⟩
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    (fun _ => 1) n hdom (fun _ _ _ => Nat.one_pos) hn
    (fun k => h.chiTriv j hj σ hσ _ n hdom k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

set_option maxHeartbeats 1000000 in

theorem exists_weight_of_pointwise
    (hP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ y ∈ X.dom, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), P y ≠ 0) :
    ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m : ℕ), Dom b m ∧ LastPos (T.Q.Dw j) b ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ m ∧ ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ P ∈ Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) b m), P k x ≠ 0 := by
  intro D T h j hj σ hσ
  classical
  set B : ℕ := 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 with hB
  have hU := h.unf j hj σ hσ
  have hrd : ∀ (f : T.R j) k (x : ((T.U j σ).X k).dom),
      rdU (T.U j σ) f k x.1 = toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k x)) := fun f k x => dif_pos x.2

  have hpt : ∀ k (x : ((T.U j σ).X k).dom), ∃ n, Even n ∧ B ≤ n ∧ ∃ f ∈ T.cuspA j (fun _ => 1) n,
      rdU (T.U j σ) f k x.1 ≠ 0 := by
    intro k x
    obtain ⟨n, hn, he, Q, hQ, hQx⟩ := exists_scalar_ne_zero hP (T.U j σ) hU
      (fun n hn k => h.chiTriv j hj σ hσ 0 n ⟨fun _ => antitone_const, hn⟩ k) k x.1 x.2
    have hQ' := pow_mem_holSub0 (T.U j σ) he hQ (B + 1)
    have hge : B + 1 + 1 ≤ (B + 1 + 1) * n := Nat.le_mul_of_pos_right _ hn
    obtain ⟨m, hm⟩ : ∃ m, (B + 1 + 1) * n = m + 2 := ⟨(B + 1 + 1) * n - 2, by omega⟩
    have hme : Even m := by
      have h2 : Even (m + 2) := hm ▸ he.mul_left _
      exact (Nat.even_add.1 h2).2 even_two
    rw [hm, ← laU_one] at hQ'
    have hs := holSub0_le_span_one D T h j hj σ hσ m hme (by omega) hQ'
    refine ⟨m, hme, by omega, ?_⟩
    by_contra hcon
    push Not at hcon
    let ev : FDSec (T.U j σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k x.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j (fun _ => 1) m : Set (T.R j))) ≤ LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    have h0 : (Q k x.1) ^ (B + 1 + 1) = 0 := hle hs
    exact hQx (pow_eq_zero_iff (by omega) |>.1 h0)
  choose n hne hnB f hf hfx using hpt
  have hE := (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1
  have hsec : ∀ k x, f k x ∈ sec (T.Q.Xo j) T.Q.c (fun _ => 1) (n k x) := fun k x => cusp_le_sec _ _ _ _ _ (hf k x)
  obtain ⟨hg, hA, -, -, -, -, hpq⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hM := (GlobalTheory.Reg.modelAt_and_nonempty_global_model _ _ _ _ (T.Q.Xo j) T.Q.c
    (by rw [(hpq j hj).1]; exact (hpq j hj).2.1) hg hA).1
  obtain ⟨la⟩ : Nonempty (HeightOneSpectrum (𝓞 T.Q.c.F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 T.Q.c.F)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  obtain ⟨s, hs, hsz⟩ := exists_finite_subfamily la (hM la) σ (ι := Σ k, ((T.U j σ).X k).dom)
    (fun _ _ => 1) (fun p => n p.1 p.2) (fun p => f p.1 p.2) (fun p => hsec p.1 p.2) (fun z => by
      obtain ⟨k, x, t, ht⟩ := hU.2.2.1 z
      refine ⟨⟨k, x⟩, ?_⟩
      rw [GlobalTheory.ArcQ.evR_frBor_of_isDomain hE (hsec k x) t _ z ht]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (t c).ne_zero) fun h0 => ?_
      apply hfx k x
      rw [hrd, h0]
      rfl)

  set L : ℕ := (B + 2) * 2 * ∏ p ∈ hs.toFinset, (n p.1 p.2 + 2) with hL
  have hprod : 0 < ∏ p ∈ hs.toFinset, (n p.1 p.2 + 2) := Finset.prod_pos fun _ _ => by omega
  have hLB : (B + 2) * 2 ≤ L := Nat.le_mul_of_pos_right _ hprod
  have hLe : Even L := (even_two.mul_left _).mul_right _
  obtain ⟨m, hm⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have hme : Even m := (Nat.even_add.1 (hm ▸ hLe)).2 even_two
  refine ⟨fun _ => 1, m, ⟨fun _ => antitone_const, hme⟩, fun _ _ _ => Nat.one_pos, by omega, fun k x hx => ?_⟩
  obtain ⟨p, hp, hpz⟩ := hsz ((T.U j σ).un k ⟨x, hx⟩)
  obtain ⟨e, he⟩ : n p.1 p.2 + 2 ∣ L :=
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (hs.mem_toFinset.2 hp)) _
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := by
    rcases e with _ | e
    · omega
    · exact ⟨e, rfl⟩
  have hmem : rdU (T.U j σ) (f p.1 p.2) ∈ Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) 0 (n p.1 p.2 + 2)) := by
    rw [← laU_one]
    exact ⟨((mem_cusp _ _ _ _ _ _).1 (hf p.1 p.2)).2 σ hσ, rdU_mem_offZero _ _⟩
  have hpw := pow_mem_holSub0 (T.U j σ) ((hne p.1 p.2).add even_two) hmem e
  rw [mul_comm, ← he, hm, ← laU_one] at hpw
  refine ⟨_, hpw, ?_⟩
  show (rdU (T.U j σ) (f p.1 p.2) k x) ^ (e + 1) ≠ 0
  refine pow_ne_zero _ ?_
  rw [hrd _ k ⟨x, hx⟩]
  exact hpz

end GlobalTheory.BpfUniform
