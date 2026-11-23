import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FinitePrimesSumSquaresZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrimeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSuccStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdealStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultAtTwistQuadEqStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HorizontalDivSuppTwistStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwLineSmoothConjInvariantGlueStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralConjLineEqStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreTwistEqUnionEmbeddingsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecompositionStatement

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Tw.Main
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory

theorem exists_prime_noRoot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (S : Set (Ideal (MRing ι))) (hS : S.Finite) (h : ∀ W ∈ S, W.IsPrime ∧ IsHorizontal W) :
    ∃ p : ℕ, p.Prime ∧ ∀ W ∈ S, NoRoot p W := by
  classical
  have hbad : ∀ W ∈ S, {p : ℕ | p.Prime ∧ ∃ a b : MRing ι ⧸ W, b ≠ 0 ∧ a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0}.Finite := by
    intro W hW
    obtain ⟨hp, hh⟩ := h W hW
    haveI := hp
    haveI : IsDomain (MRing ι ⧸ W) := Ideal.Quotient.isDomain W
    haveI : CharZero (MRing ι ⧸ W) := by
      refine ⟨fun a b hab => ?_⟩
      have h0 : (C (((a : ℤ) - (b : ℤ))) : MRing ι) ∈ W := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [sub_eq_zero] using hab
      have h1 : ((a : ℤ) - (b : ℤ)) ∈ W.comap (C : ℤ →+* MRing ι) := h0
      rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hh, Ideal.mem_bot] at h1
      omega
    exact GlobalTheory.T.finite_primes_sum_squares_zero _ _ (Ideal.Quotient.mk W) Ideal.Quotient.mk_surjective
  have hfin : (⋃ W ∈ S, {p : ℕ | p.Prime ∧ ∃ a b : MRing ι ⧸ W, b ≠ 0 ∧ a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0}).Finite :=
    hS.biUnion hbad
  obtain ⟨p, hp, hpn⟩ := (Nat.infinite_setOf_prime.diff hfin).nonempty
  refine ⟨p, hp, fun W hW a b hab => ?_⟩
  by_contra hb
  apply hpn
  refine Set.mem_biUnion hW ⟨hp, Ideal.Quotient.mk W a, Ideal.Quotient.mk W b, ?_, ?_⟩
  · rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  · have := Ideal.Quotient.eq_zero_iff_mem.mpr hab
    simpa using this

theorem isArithVar_twist {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {d : ℕ} (hQ : IsArithVar Q d) (hR : NoRoot p Q) :
    IsArithVar (twist p Q) d := by
  obtain ⟨hK, hM, hH, hd⟩ := hQ
  refine ⟨⟨none⟩, ⟨GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p Q hM.1 hR, GlobalTheory.T.twist_isMultiHomogIdeal K ι p Q hM.2.1,
    isRelevant_twist p hM.1.ne_top hM.2.2⟩, isHorizontal_twist p hH, ?_⟩
  haveI := hM.1
  rw [GlobalTheory.T.ringKrullDim_twist_succ K ι p Q hM.1, hd, Fintype.card_option, ← add_assoc]
  push_cast
  rfl

theorem inc_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {s : MRing ι} (hs : s ∉ Q) : inc s ∉ twist p Q := fun h =>
  hs (by rw [← comap_inc_twist p Q]; exact h)

theorem oldIdx_injective {K : Type} {ι : K → Type} : Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  obtain rfl : k = k' := Option.some_injective _ (congrArg Sigma.fst h)
  have : i = i' := eq_of_heq (Sigma.mk.inj h).2
  rw [this]

theorem isMultiHomog_inc {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (inc s) (fun o => match o with | none => 0 | some k => a k) := by
  classical
  intro m hm o
  simp only [inc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hm
  rw [MvPolynomial.support_rename_of_injective oldIdx_injective] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  cases o with
  | none =>
    show ∑ i, (Finsupp.mapDomain oldIdx m0) ⟨none, i⟩ = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨q, hq⟩
    cases hq
  | some k =>
    show ∑ i, (Finsupp.mapDomain oldIdx m0) ⟨some k, i⟩ = a k
    rw [← hs m0 hm0 k]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply (f := oldIdx (ι := ι)) oldIdx_injective m0 ⟨k, i⟩

theorem isSectionOn_twist {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι} (hs : IsSectionOn Q A s) :
    IsSectionOn (twist p Q) (twLine p A) (inc s) := by
  obtain ⟨a, ha, hh, hn⟩ := hs
  refine ⟨fun o => match o with | none => 0 | some k => a k, fun o => ?_, isMultiHomog_inc hh, inc_notMem hn⟩
  cases o with
  | none => rfl
  | some k => exact ha k

theorem embL_inj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {v : Fin 2 → ℂ}
    (h1 : v 1 = 1) : Function.Injective (embL v : (((k : K) → ι k) → ℂ) → _) := by
  intro w w' h
  funext j
  have := congrFun h (fun o => match o with | none => (1 : Fin 2) | some k => j k)
  simpa [embL, h1] using this

theorem twist_integral (hI : PtsIntegrableStatement) (hD : PtsIndepStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ} (hp : p ≠ 0)
    {Q : Ideal (MRing ι)} {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hQ : IsArithVar Q (e + 1)) (hR : NoRoot p Q) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn Q A s) :
    ptsIntegral (twist p Q) (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) =
      ptsIntegral Q (pot L) (logNorm A s) +
        ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) := by
  classical
  have hQ' : IsArithVar (twist p Q) (e + 1) := isArithVar_twist hQ hR
  have hKne : Nonempty K := hQ.1
  have hF := fun B : HermLine ι => GlobalTheory.T.twLine_smooth_conjInvariant_glue K ι p B hp
  have hL' : ∀ j, IsSmoothHerm (twLine p (L j)) := fun j => (hF _).1 (hL j)
  have hA' : IsSmoothHerm (twLine p A) := (hF _).1 hA
  have hLc : ∀ j, IsSmoothHerm (conjLine (L j)) := fun j => (hF _).2.1 (hL j)
  have hAc : IsSmoothHerm (conjLine A) := (hF _).2.1 hA
  have hs' : IsSectionOn (twist p Q) (twLine p A) (inc s) := isSectionOn_twist hs
  have hsc : IsSectionOn Q (conjLine A) s := hs
  obtain ⟨Ψ, hΨ⟩ := goodProjExists (Option K) (Tb ι) (twist p Q) e hQ'
  have good : ∀ v : Fin 2 → ℂ, v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0 → v 1 ≠ 0 → IsGoodProj Q (pj v Ψ) := by
    intro v hv hv1 z hz
    have := hΨ _ (glue_mem_mcPts hz hv hv1)
    rw [segre_glue] at this
    exact this
  have v1p : vPlus p 1 = 1 := by simp [vPlus]
  have v1m : vMinus p 1 = 1 := by simp [vMinus]
  have gp := good _ (vPlus_root p) (by rw [v1p]; exact one_ne_zero)
  have gm := good _ (vMinus_root p) (by rw [v1m]; exact one_ne_zero)
  have atOf : ∀ {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {P : Ideal (MRing ι')}
      {Φ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {M : Fin e → HermLine ι'}
      {B : HermLine ι'} {t : MRing ι'}, IsArithVar P (e + 1) → IsGoodProj P Φ →
      (∀ j, IsSmoothHerm (M j)) → IsSmoothHerm B → IsSectionOn P B t →
      ptsIntegral P (pot M) (logNorm B t) = ptsIntegralAt P Φ (pot M) (logNorm B t) := by
    intro K' _ ι' _ P Φ M B t h1 h2 h3 h4 h5
    have hex : ∃ Φ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Φ := ⟨Φ, h2⟩
    unfold ptsIntegral
    rw [dif_pos hex]
    exact hD K' ι' P e _ Φ M B t h1 hex.choose_spec h2 h3 h4 h5
  rw [atOf hQ' hΨ hL' hA' hs', atOf hQ gp hL hA hs, atOf hQ gm hLc hAc hsc]
  have sp := GlobalTheory.T.twist_height_integral_decomposition K ι p Q e Ψ (fun j => twLine p (L j)) (twLine p A) L A s (vPlus p) hp hQ hQ' hΨ hL' hA' hs'
    (Or.inl rfl) (fun j z hz => (hF _).2.2.2.1 z hz.1) (fun z hz => (hF _).2.2.2.1 z hz.1)
  have sm := GlobalTheory.T.twist_height_integral_decomposition K ι p Q e Ψ (fun j => twLine p (L j)) (twLine p A) (fun j => conjLine (L j)) (conjLine A) s
    (vMinus p) hp hQ hQ' hΨ hL' hA' hs' (Or.inr rfl) (fun j z hz => (hF _).2.2.2.2 z hz.1)
    (fun z hz => (hF _).2.2.2.2 z hz.1)
  have hae : ∀ᵐ y, (∑ᶠ w ∈ fibre (twist p Q) Ψ y, sheetDensity (twist p Q) Ψ (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) y w) =
      (∑ᶠ w ∈ fibre Q (pj (vPlus p) Ψ) y, sheetDensity Q (pj (vPlus p) Ψ) (pot L) (logNorm A s) y w) +
      ∑ᶠ w ∈ fibre Q (pj (vMinus p) Ψ) y, sheetDensity Q (pj (vMinus p) Ψ) (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) y w := by
    filter_upwards [sp, sm] with y hpl hmi
    have fpl := fibreFinite K ι Q e _ hQ gp y
    have fmi := fibreFinite K ι Q e _ hQ gm y
    have hdis : Disjoint (embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y)
        (embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y) := by
      rw [Set.disjoint_left]
      rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', he⟩
      have hc : cRoot p ≠ 0 := by
        simp [cRoot, Real.sqrt_eq_zero', hp, Nat.pos_of_ne_zero hp]
      have hww : w' = w := by
        funext j
        have := congrFun he (fun o => match o with | none => (1 : Fin 2) | some k => j k)
        simpa [embL, v1p, v1m] using this
      subst hww
      have hz : w' = 0 := by
        funext j
        have := congrFun he (fun o => match o with | none => (0 : Fin 2) | some k => j k)
        simp only [embL, vPlus, vMinus, LinearMap.coe_mk, AddHom.coe_mk] at this
        have h2 : w' j * (2 * cRoot p) = 0 := by
          have h3 : w' j * (-cRoot p) = w' j * cRoot p := by simpa using this
          linear_combination -h3
        simpa [hc] using h2
      obtain ⟨z, -, -, h⟩ := hw
      rw [hz, map_zero] at h
      have := congrFun h 0
      simp at this
    rw [GlobalTheory.T.fibre_twist_eq_union_embeddings K ι p Q e Ψ y hp hKne hQ.2.1.2.1, finsum_mem_union hdis (fpl.image _) (fmi.image _),
      finsum_mem_image (embL_inj v1p).injOn, finsum_mem_image (embL_inj v1m).injOn]
    simp only [hpl, hmi]
  unfold ptsIntegralAt
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_add
    (hI K ι Q e _ L A s hQ gp hL hA hs) (hI K ι Q e _ _ _ s hQ gm hLc hAc hsc)]

theorem twist_double (hI : PtsIntegrableStatement) (hD : PtsIndepStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ} (hp : p ≠ 0)
    {Q : Ideal (MRing ι)} {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hQ : IsArithVar Q (e + 1)) (hR : NoRoot p Q) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn Q A s) :
    ptsIntegral (twist p Q) (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) =
      2 * ptsIntegral Q (pot L) (logNorm A s) := by
  rw [twist_integral hI hD hp hQ hR hL hA hs, GlobalTheory.T.ptsIntegral_conjLine_eq hD K ι Q e L A s hQ hL hA hs]
  ring

theorem pot_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (B : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons B L : Fin (e + 1) → HermLine ι) =
      Fin.cons (fun z => Real.log (B.h z)) (pot L) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem tw_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (p : ℕ)
    (B : HermLine ι) (L : Fin e → HermLine ι) :
    (fun j => twLine p ((Fin.cons B L : Fin (e + 1) → HermLine ι) j)) =
      (Fin.cons (twLine p B) (fun j => twLine p (L j)) : Fin (e + 1) → HermLine (Tb ι)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem logNorm_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (B : HermLine ι) : logNorm (invLine B) 1 = fun z => Real.log (B.h z) := by
  funext z
  simp [logNorm, invLine]

theorem logNorm_tw_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ)
    (B : HermLine ι) : logNorm (twLine p (invLine B)) (inc 1) = fun z => Real.log ((twLine p B).h z) := by
  classical
  funext z
  have hh : (twLine p (invLine B)).h z = ((twLine p B).h z)⁻¹ := by
    show twH p (invLine B) z = (twH p B z)⁻¹
    unfold twH
    split_ifs with h
    · rw [← Real.exp_neg]
      congr 1
      simp only [invLine, Real.log_inv]
      ring
    · simp
  simp [logNorm, hh]

theorem isSectionOn_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRing ι)} (hQ : Q ≠ ⊤) {B : HermLine ι} (hB : B.a = 0) :
    IsSectionOn Q (invLine B) 1 := by
  refine ⟨0, fun k => by simp [invLine, hB], fun m hm k => ?_, fun h => hQ ((Ideal.eq_top_iff_one _).mpr h)⟩
  have : m = 0 := by
    by_contra h0
    classical
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm h0)] at hm
    exact hm rfl
  simp [this]

theorem isSmooth_inv {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm (invLine B) :=
  ContDiffOn.inv hB fun z hz => (B.pos z hz).ne'

theorem tw_cons_smooth {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {B : HermLine ι} {L : Fin e → HermLine ι} (hB : IsSmoothHerm B) (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons B L : Fin (e + 1) → HermLine ι) j) := fun j => by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hB
  · exact hL i

theorem poincareLelong_of_inv :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv →
      GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong := by
  intro hRK hInv K _ ι _ P n L A B s hP hL hA hB hBa hs
  classical
  have hI : PtsIntegrableStatement := GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK hRK
  have hD : PtsIndepStatement := ptsIndep_of (GlobalTheory.T.resolution_exists_of_resolution_statement hRK) resBridge
  have hPp : P.IsPrime := hP.2.1.1
  set H : Set (Ideal (MRing ι)) := {W | W ∈ divSupp P s ∧ IsHorizontal W} with hH
  have hHfin : H.Finite := (divSupp_finite P s).subset fun W h => h.1
  have hHar : ∀ W ∈ H, IsArithVar W (n + 1) := fun W h =>
    (divSuppArith K ι P (n + 1) A s W hP hs h.1).1 h.2
  obtain ⟨p, hp, hpS⟩ := exists_prime_noRoot (insert P H) (hHfin.insert P) (by
    rintro W (rfl | hW)
    · exact ⟨hPp, hP.2.2.1⟩
    · exact ⟨(hHar W hW).2.1.1, hW.2⟩)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hRP : NoRoot p P := hpS P (Set.mem_insert _ _)
  have hRW : ∀ W ∈ H, NoRoot p W := fun W h => hpS W (Set.mem_insert_of_mem _ h)
  have hF := fun C : HermLine ι => GlobalTheory.T.twLine_smooth_conjInvariant_glue K ι p C hp0
  have hP' : IsArithVar (twist p P) (n + 2) := isArithVar_twist hP hRP
  have hInv' := hInv (Option K) (Tb ι) (twist p P) n (fun j => twLine p (L j)) (twLine p A) (twLine p B)
    (inc s) hP' (fun j => (hF _).1 (hL j)) ((hF _).1 hA) ((hF _).1 hB)
    (fun j => (hF _).2.2.1) (hF _).2.2.1 (hF _).2.2.1
    (by funext o; cases o with
        | none => rfl
        | some k => exact congrFun hBa k)
    (isSectionOn_twist hs)

  have e1 := twist_double hI hD hp0 (e := n + 1) (L := Fin.cons B L) (A := A) (s := s) hP hRP
    (tw_cons_smooth hB hL) hA hs
  rw [tw_cons, pot_cons, pot_cons] at e1
  have e3 := twist_double hI hD hp0 (e := n + 1) (L := Fin.cons A L) (A := invLine B) (s := 1) hP hRP
    (tw_cons_smooth hA hL) (isSmooth_inv hB) (isSectionOn_inv_one hPp.ne_top hBa)
  rw [tw_cons, pot_cons, pot_cons, logNorm_inv_one, logNorm_tw_inv_one] at e3
  have e2 : ∀ W ∈ H, ptsIntegral (twist p W) (pot fun j => twLine p (L j))
      (fun z => Real.log ((twLine p B).h z)) = 2 * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    intro W hW
    have hWa := hHar W hW
    have := twist_double hI hD hp0 (e := n) (L := L) (A := invLine B) (s := 1) hWa (hRW W hW) hL
      (isSmooth_inv hB) (isSectionOn_inv_one hWa.2.1.1.ne_top hBa)
    rwa [logNorm_inv_one, logNorm_tw_inv_one] at this
  have hsup : twist p P ⊔ Ideal.span {inc s} =
      (P ⊔ Ideal.span {s}).map inc ⊔ Ideal.span {quad p} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, twist, sup_right_comm]
  have hdiv := GlobalTheory.T.horizontal_divSupp_twist_eq_image K ι p P s (fun W hW hh =>
    GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p W (hHar W ⟨hW, hh⟩).2.1.1 (hRW W ⟨hW, hh⟩))
  have hsum : (∑ᶠ (W') (_ : W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'),
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z))) =
      2 * ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    have h1 : (∑ᶠ (W') (_ : W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'),
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z))) =
        ∑ᶠ W' ∈ {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'},
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z)) := rfl
    have h2 : (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) =
        ∑ᶠ W ∈ H, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := rfl
    rw [h1, h2, hdiv, finsum_mem_image (twist_injective p).injOn, mul_finsum_mem]
    refine finsum_mem_congr rfl fun W hW => ?_
    rw [e2 W hW, hsup, GlobalTheory.T.multAt_twist_quad_eq K ι p _ W hW.1.1 (GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p W (hHar W hW).2.1.1 (hRW W hW))]
    ring
  have hInv2 : ptsIntegral (twist p P)
      (Fin.cons (fun z => Real.log ((twLine p B).h z)) (pot fun j => twLine p (L j)))
      (logNorm (twLine p A) (inc s)) = _ := hInv'
  rw [e1, hsum, e3] at hInv2
  linarith

end GlobalTheory.CompanionTheory.Ar.Tw.Main
