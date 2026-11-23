import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigenLiftsOfDirectionsBiext
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProducts
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceHarmonic

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.ChartUnram

open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem isRQ_or_rat (T : CDVR) : TB.IsRQ (R := T.V) T.Fr ∨ Nonempty (Algebra ℚ T.V) := by
  by_cases hN : ∃ N : ℕ, N ≠ 0 ∧ ¬ IsUnit (N : T.V)
  · left
    obtain ⟨N, hN0, hNu⟩ := hN
    refine ⟨IsFractionRing.injective T.V T.Fr, fun y => ?_⟩
    have hNV0 : (N : T.V) ≠ 0 := by exact_mod_cast hN0
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ
    have hϖN : ϖ ∣ (N : T.V) := by
      rcases m with _ | m
      · exact absurd (hm.isUnit_iff.2 (by simp)) hNu
      · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T.V) y
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
    obtain ⟨c, hc⟩ : s ∣ (N : T.V) ^ n := hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)
    refine ⟨c * a, N ^ n, pow_pos (Nat.pos_of_ne_zero hN0) n, ?_⟩
    have hsK : algebraMap T.V T.Fr s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]; exact hs0
    have hcast : ((N ^ n : ℕ) : T.Fr) = algebraMap T.V T.Fr ((N : T.V) ^ n) := by
      rw [map_pow, map_natCast]; push_cast; rfl
    rw [hcast, hc, map_mul, map_mul]
    field_simp
  · right
    push Not at hN
    have hu : ∀ z : nonZeroDivisors ℤ, IsUnit (Int.castRingHom T.V z) := by
      rintro ⟨z, hz⟩
      have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
      have h1 := hN z.natAbs (Int.natAbs_ne_zero.2 hz0)
      rcases Int.natAbs_eq z with h | h
      · show IsUnit ((z : ℤ) : T.V)
        rw [h, Int.cast_natCast]; exact h1
      · show IsUnit ((z : ℤ) : T.V)
        rw [h, Int.cast_neg, Int.cast_natCast]; exact h1.neg
    exact ⟨(IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) hu).toAlgebra⟩

section Abstract

variable {R k : Type} [CommRing R] [Field k] [Algebra ℚ k] [Algebra R k]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem value_mem_rat [Algebra ℚ R] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O]
    (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h) (w0 : O) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ)) (σ : T → O →+* k) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a))
    (u : (Σ τ : T, Fin (rr τ)) → Fin d → R)
    (hu : ∀ l a, (dAct k B a).mulVec (fun j => algebraMap R k (u l j)) = σ l.1 a • fun j => algebraMap R k (u l j))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T rr n) k)
    (hP : P ∈ HaO rr n k (algebraMap R k).range cc isX a)
    (f : Fin n → PS k 1 d) (hf : ∀ b, TB.IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ (algebraMap R k).range := by
  classical
  obtain ⟨h0, hh0⟩ := GlobalTheory.canonGauge_exists R d O R B
  obtain ⟨hc, hv⟩ := GlobalTheory.canonGauge_nabVal_baseChange R d O B R k (Algebra.ofId R k) h0 hh0
  have e := GlobalTheory.canonGauge_independence_harmonic R d O k B h _ hg hc T rr cc isX σ hcc hX hσ hsep
    (fun ℓ j => algebraMap R k (u ℓ j)) hu n (MvPolynomial.rename (CVA.lEq (T := T) (r := rr) (n := n)) P)
    (CVA.harm_rename (r := rr) (n := n) cc isX P hP.1.1) w0 m f
  rw [CVA.sum_rename, CVA.sum_rename] at e
  simp only [colM_lEq_colL] at e
  rw [e]
  refine Subring.sum_mem _ fun mo _ => Subring.mul_mem _ (hP.2 mo) (Subring.prod_mem _ fun b _ => ?_)
  choose g hg' using hf b
  have hfb : f b = MvPowerSeries.map (Algebra.ofId R k : R →+* k) (g : PS R 1 d) := by
    ext mm
    exact (hg' mm).symm
  have h1 := hv w0 m g _ u (MvPolynomial.monomial (colL rr n mo b) 1)
  rw [MvPolynomial.map_monomial, map_one, ← hfb] at h1
  exact ⟨_, h1.symm⟩

theorem value_mem_idem (hRQ : TB.IsRQ (R := R) k)
    (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h) (w0 : O) (hw0 : w0 + star w0 = 1) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ)) (hX' : ∀ τ, ¬ (isX τ ∧ isX (cc τ)))
    (σ : T → O →+* k) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a))
    (hidem : ∀ t : T, ∃ (n : ℕ) (b : Fin n → O) (c : Fin n → R), (∑ i, algebraMap R k (c i) * σ t (b i) = 1) ∧
      ∀ a : O, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap R k (c i) = σ t a * algebraMap R k (c j))
    (u : (Σ τ : T, Fin (rr τ)) → Fin d → R)
    (hu : ∀ l a, (dAct k B a).mulVec (fun j => algebraMap R k (u l j)) = σ l.1 a • fun j => algebraMap R k (u l j))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T rr n) k)
    (hP : P ∈ HaO rr n k (algebraMap R k).range cc isX a)
    (f : Fin n → PS k 1 d) (hf : ∀ b, TB.IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ (algebraMap R k).range := by
  classical
  obtain ⟨φ, hφ⟩ := EigA.eigLift_core hRQ B h hg (fun ℓ : (Σ τ : T, Fin (rr τ)) => ℓ.1) σ u hu hidem
  have heig0 : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 →
      ∑ i, (algebraMap R k (φ ℓ' i) - (TB.sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0 := by
    intro ℓ ℓ' hne
    obtain ⟨x, hx⟩ := hsep ℓ.1 (cc ℓ'.1) fun e => hne (by rw [e, hcc])
    rw [hσ] at hx
    exact hφ ℓ ℓ' ⟨x, sub_ne_zero.1 hx.ne_zero⟩
  let c : T → T := fun τ => if isX τ then τ else cc τ
  let s : T → Bool := fun τ => decide (isX τ)
  have hcs : ∀ τ, c (cc τ) = c τ ∧ s (cc τ) ≠ s τ := by
    intro τ
    have hc : cc (cc τ) = τ := hcc τ
    by_cases h1 : isX τ
    · have h2 : ¬ isX (cc τ) := fun h2 => hX' τ ⟨h1, h2⟩
      constructor
      · simp only [c, h1, h2, if_true, if_false, hc]
      · simp [s, h1, h2]
    · have h2 : isX (cc τ) := (hX τ).resolve_left h1
      constructor
      · simp only [c, h1, h2, if_true, if_false]
      · simp [s, h1, h2]
  have hnot : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ¬ (c ℓ.1 = c ℓ'.1 ∧ s ℓ.1 ≠ s ℓ'.1) → ℓ'.1 ≠ cc ℓ.1 := by
    intro ℓ ℓ' hn he'
    apply hn
    rw [he']
    exact ⟨(hcs ℓ.1).1.symm, (hcs ℓ.1).2.symm⟩
  have key := chartValJ (R := R) (k := k) hRQ 1
    (Submodule.mem_one.2 ⟨1, map_one _⟩) B h hg w0 hw0 m rr cc hcc isX hX c s hcs u φ (fun _ _ => 0)
    (fun _ _ => Submodule.zero_mem _)
    (fun ℓ ℓ' hne => by simpa only [add_zero] using heig0 ℓ ℓ' hne)
    (fun ℓ ℓ' hn => by
      have h1 := hnot ℓ ℓ' hn
      have h2 : ℓ.1 ≠ cc ℓ'.1 := fun h2 => h1 (by rw [h2]; exact (hcc _).symm)
      simp only [TB.betaH]
      rw [Finset.sum_sub_distrib, heig0 ℓ ℓ' h1]
      have h3 := heig0 ℓ' ℓ h2
      simp only [mul_comm] at h3 ⊢
      rw [h3, sub_self])
    (fun ℓ ℓ' _ => by simp [TB.betaH]) (fun ℓ ℓ' _ => by simp [TB.betaH])
    n a P hP
    (∑ mo ∈ P.support, ∑ b, TB.pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL _ n mo b))
    (fun mo hmo => Finset.single_le_sum (f := fun mo => ∑ b, TB.pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1)
      (fun ℓ => s ℓ.1) (colL _ n mo b)) (fun _ _ => Nat.zero_le _) hmo) f hf
  rw [one_pow] at key
  exact Submodule.mem_one.1 key

end Abstract

end GlobalTheory.ChartUnram

open GlobalTheory.ChartUnram ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf in

theorem GlobalTheory.PlaceInt.chBound_zero_of_isUnit_discr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsUnit ((NumberField.discr E : ℤ) : T.V) → ∀ (e : ℕ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e 0 w n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hdisc e w n
  refine GlobalTheory.PlaceInt.chBound_of_columns E H Dw l Xo c hstar T io y C e 0 w n fun k P hP f hf => ?_
  letI := io.toAlgebra
  obtain ⟨B, hBT, hB⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hg, -, heig, -⟩ := hB B hBT
  obtain ⟨gF, gA, -, -, -, -, gu⟩ := C.gen.1
  have hu : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) := funext fun ℓ => funext fun i => gu ℓ i
  rw [hu] at heig
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [ChartBiext.toK_self, gF, hBT.1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [ChartBiext.toK_self, gA, hBT.2.1]
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => star_star τ
  have hσ : ∀ (τ : E →+* ℂ) (a : 𝓞 E), (io.comp (embK c (ComplexEmbedding.conjugate τ))) a =
      (io.comp (embK c τ)) (star a) := by
    intro τ a
    refine congrArg io (Subtype.ext ?_)
    change ((embK c _ a : c.F) : ℂ) = ((embK c _ _ : c.F) : ℂ)
    simp only [embK_coe]
    rw [ComplexEmbedding.conjugate_coe_eq, hstar, H.bar_eq, NumberField.IsCMField.complexEmbedding_complexConj]
  have hsep : ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a, IsUnit ((io.comp (embK c τ)) a - (io.comp (embK c τ')) a) := by
    intro τ τ' hne
    by_contra hall
    push Not at hall
    apply hne
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
    have h0 := hall x
    rw [isUnit_iff_ne_zero, not_not, sub_eq_zero] at h0
    have h2 := congrArg (fun z : c.F => (z : ℂ)) (io.injective h0)
    simpa only [embK_coe] using h2
  have key : ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal T.Fr C.ch.h H.w0 k (f b)
      (fun ℓ j => algebraMap T.V T.Fr (C.uvecT ℓ j)) (MvPolynomial.monomial (colL Dw.mult n mo b) 1) ∈
        (algebraMap T.V T.Fr).range := by
    rcases isRQ_or_rat T with hRQ | ⟨⟨_⟩⟩
    · have hunit : IsUnit (((discr E).natAbs : ℕ) : T.V) := by
        rcases Int.natAbs_eq (discr E) with h | h
        · rwa [h, Int.cast_natCast] at hdisc
        · rw [h, Int.cast_neg, Int.cast_natCast] at hdisc
          simpa using hdisc.neg
      obtain ⟨v, hv⟩ : ∃ v : T.V, algebraMap T.V T.Fr v * (((discr E).natAbs : ℕ) : T.Fr) = 1 := by
        refine ⟨↑hunit.unit⁻¹, ?_⟩
        rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hunit.val_inv_mul, map_one]
      have hint : ∀ τ : E →+* ℂ, ∀ x : 𝓞 E, ∃ v : T.V,
          algebraMap T.V T.Fr v = (io.comp (embF c τ)) (algebraMap (𝓞 E) E x) := by
        intro τ x
        obtain ⟨Q, hPm, hPe⟩ := RingOfIntegers.isIntegral_coe x
        refine IsIntegrallyClosed.isIntegral_iff.1 ⟨Q.map (Int.castRingHom T.V), hPm.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
          ((io.comp (embF c τ)).comp (algebraMap ℤ E)), ← Polynomial.hom_eval₂]
        exact (congrArg _ hPe).trans (map_zero _)
      exact value_mem_idem hRQ B C.ch.h hg H.w0 (by rw [hstar]; exact CVA.cmHostUnit_add_conj_eq_one H) k Dw.mult _ hcc (InPsi H)
        (CVA.inPsi_or H) (CVA.not_inPsi_both H) (fun τ => io.comp (embK c τ)) hσ hsep
        (fun τ => EigA.idem_data (io.comp (embF c τ)) (hint τ) v hv) C.uvecT heig n _ P hP f hf
    · exact value_mem_rat B C.ch.h hg H.w0 k Dw.mult _ hcc (InPsi H)
        (CVA.inPsi_or H) (fun τ => io.comp (embK c τ)) hσ hsep C.uvecT heig n _ P hP f hf
  rw [neg_zero, EReal.coe_zero]
  refine nval_nonneg_of_int e ?_
  unfold FB.nabVal FB.hL at key ⊢
  rw [eF, eA] at key
  rw [hu]
  exact key
