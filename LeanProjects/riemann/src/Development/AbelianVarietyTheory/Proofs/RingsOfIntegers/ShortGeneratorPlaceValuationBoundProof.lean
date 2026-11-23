import Mathlib
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardFunLevQ
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortValueBoundOfCoprime
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortBoundOfTrivAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfCastDvd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsIntegralZpowOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EmbEqOfInPsi
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightOnDatum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.ShortBound

section Val
variable {V : Type} {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

theorem vV_one : vV V (1 : K') = 0 := by simp [vV]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV_one]
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem vV_inv {x : K'} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have := vV_mul (V := V) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vV_one] at this
  omega

theorem vV_nonneg {x : K'} (hx : IsIntegral ℤ x) : 0 ≤ vV V x := by
  have h1 : IsIntegral V x := hx.tower_top
  obtain ⟨a, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := K')).1 h1
  have h2 : valV V (algebraMap V K' a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
  by_cases h0 : algebraMap V K' a = 0
  · simp [vV, h0]
  have := (WithZero.log_le_log (valV_ne_zero h0) one_ne_zero).2 h2
  rw [WithZero.log_one] at this
  simp only [vV]; omega

theorem nval_nonneg (e : ℕ) {x : K'} (hx : IsIntegral ℤ x) : 0 ≤ nval V e x := by
  by_cases h0 : x = 0
  · rw [h0, nval_zero]; exact le_top
  rw [nval_of_ne h0]
  have : (0 : ℝ) ≤ (vV V x : ℝ) := by exact_mod_cast vV_nonneg hx
  exact EReal.coe_nonneg.2 (by positivity)

theorem le_nval_sum (e : ℕ) {J : Type} (s : Finset J) (f : J → K') (a : EReal) (h : ∀ i ∈ s, a ≤ nval V e (f i)) :
    a ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, nval_zero]; exact le_top
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (le_min (h i (Finset.mem_insert_self _ _))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).trans (nval_add e _ _)

theorem le_nval_avg (e : ℕ) {J : Type} [Finite J] (w X : J → K') (ζ u cc b : K') (m : ℕ) (hm : 0 < m) (hζ : ζ ^ m = 1)
    (hu : u ≠ 0) (hcc : cc ≠ 0) (hw : ∀ q, IsIntegral ℤ (w q)) (ρ : ℝ)
    (hX : ∀ q, ((-ρ : ℝ) : EReal) ≤ nval V e (u * b * X q)) :
    ((-(ρ + (vV V u : ℝ) / e + (vV V cc : ℝ) / e) : ℝ) : EReal) ≤ nval V e (ζ * (cc⁻¹ * b * ∑ᶠ q, w q * X q)) := by
  classical
  have := Fintype.ofFinite J
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hm.ne'] at hζ; exact zero_ne_one hζ
  have hv : vV V ζ = 0 := by
    have := vV_pow (V := V) hζ0 m
    rw [hζ, vV_one] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd (by exact_mod_cast h) hm.ne'
    · exact h
  rw [nval_mul_unit e hζ0 hv, finsum_eq_sum_of_fintype]
  have : cc⁻¹ * b * ∑ q, w q * X q = (cc⁻¹ * u⁻¹) * ∑ q, w q * (u * b * X q) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    field_simp
  rw [this, nval_mul, nval_of_ne (mul_ne_zero (inv_ne_zero hcc) (inv_ne_zero hu)),
    vV_mul (inv_ne_zero hcc) (inv_ne_zero hu), vV_inv hcc, vV_inv hu]
  have h2 : ((-ρ : ℝ) : EReal) ≤ nval V e (∑ q, w q * (u * b * X q)) := by
    refine le_nval_sum e _ _ _ fun q _ => ?_
    rw [nval_mul]
    calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
      _ ≤ _ := add_le_add (nval_nonneg e (hw q)) (hX q)
  refine le_trans (le_of_eq ?_) (add_le_add le_rfl h2)
  rw [← EReal.coe_add]
  congr 1
  push_cast
  ring
end Val

theorem exists_resChar (T : CDVR) (h : T.FinRes) : ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ IsUnit (ℓ : T.V) := by
  haveI : Finite (ResidueField T.V) := h
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField T.V)
  haveI := Fintype.ofFinite (ResidueField T.V)
  refine ⟨p, (CharP.char_is_prime_or_zero (ResidueField T.V) p).resolve_right
    (CharP.char_ne_zero_of_finite (ResidueField T.V) p), fun hu => ?_⟩
  have := hu.map (residue T.V)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem nrm_one (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) : nrm Dw c w 1 = 1 := by simp [nrm]

theorem nrm_mul (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) (a b : 𝓞 E) :
    nrm Dw c w (a * b) = nrm Dw c w a * nrm Dw c w b := by
  simp [nrm, mul_pow, Finset.prod_mul_distrib]

theorem nrm_nat (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) (p : ℕ) :
    nrm Dw c w (p : 𝓞 E) = (p : c.F) ^ Formalism.L2.Pj.DF Dw w := by
  simp [nrm, Formalism.L2.Pj.DF, Finset.prod_pow_eq_pow_sum]

theorem nrm_ne_zero (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) {a : 𝓞 E} (ha : a ≠ 0) : nrm Dw c w a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
  exact (map_ne_zero (embF c τ)).2 (by simpa using ha)

theorem nrm_integral (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) (a : 𝓞 E) : IsIntegral ℤ (nrm Dw c w a) :=
  IsIntegral.prod _ fun τ _ => ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (embK c τ).toIntAlgHom).pow _

theorem levPt_killed (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : Dw.La) :
    KilledBy Xo l.Mb (levPt Xo x a) := by
  intro b hb
  have := (GlobalTheory.moduli_univ_eta_killed GlobalTheory.firstFiveLaws.1 E H Dw l Xo a).1 b hb
  rw [levPt, Category.assoc, this, MonObj.comp_one]

theorem class_bound (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hch : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hΛ : Λ.Unimod) (hT : Λ.TrivAt l.M) (hN : Λ.LevOK N l.M) (β : c.F) (hβ0 : β ≠ 0) (hβ : BetaIs (Dw := Dw) c Λ β)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b))
    (hR : AllRat Xo (xOf y) (N ^ 2)) (hsq : ¬ ℓ ^ 2 ∣ l.M) (α : 𝓞 E)
    (hα : (¬ ℓ ∣ l.M ∧ α = 1) ∨ (ℓ ∣ l.M ∧ α * H.bar α = (ℓ : 𝓞 E) ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨
      (ℓ ∣ l.M ∧ α = (ℓ : 𝓞 E))) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α) *
      io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [(htp b).1]; exact levPt_killed Xo _ _
  obtain ⟨t1, t2⟩ := GlobalTheory.TorsFac.factorisation E H Dw l Xo N ℓ hN.1 hN.2.1 hℓ
  have lev : ∀ A : ℕ, ℓ ∣ l.M → α * H.bar α = (A : 𝓞 E) →
      ((A = ℓ ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨ (α = (ℓ : 𝓞 E) ∧ ℓ ∣ l.M)) →
      letI := io.toAlgebra
      ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α) *
        io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
          ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
    intro A hd hA hor
    obtain ⟨n', Bn, j, β₀, h1, h2, h3, h4, h5⟩ := t2 α A hA hsq hor
    obtain ⟨k, hk1, hk2⟩ := hT
    rw [← map_mul]
    exact GlobalTheory.PlaceInt.ShortTriv.short_bound_of_trivAt E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hch ℓ hℓ hu Λ N l.M hΛ hN β hβ0 hβ P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF ⟨k, hk1.coprime_dvd_right hd, hk2⟩ n' A Bn j α β₀ h1 h2 hA h3 h4
      (fun b => (h5 _ _ (hk b) (htp b).2).2)
  rcases hα with ⟨hd, rfl⟩ | ⟨hd, hA, hM⟩ | ⟨hd, hA⟩
  · obtain ⟨n', j, -, -, h5⟩ := t1 hd
    rw [nrm_one, map_one, _root_.one_mul]
    choose i hi using fun b => (h5 _ _ (hk b) (htp b).2).2.2
    refine GlobalTheory.short_value_bound_of_coprime E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hch ℓ hℓ hu Λ N l.M hΛ hN β hβ0 hβ P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF hR ⟨l.M ^ (∑ b, i b),
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd).symm, fun b => ?_⟩
    obtain ⟨m, hm⟩ : l.M ^ i b ∣ l.M ^ (∑ b, i b) :=
      pow_dvd_pow _ (Finset.single_le_sum (f := i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
    rw [hm, pow_mul, hi b, one_pow]
  · exact lev ℓ hd hA (Or.inl ⟨rfl, hM⟩)
  · exact lev (ℓ ^ 2) hd (by rw [hA, map_natCast]; push_cast; ring) (Or.inr ⟨hA, hd⟩)
end Point

section Run
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons GlobalTheory.PlaceTop

theorem exists_alpha (D : D7) (T : Top D) (h : LawsP T) (hs : LawsSh T) (j : ℕ) (hj : InR D j) (EX : ErrX D)
    (hor : Oriented T EX) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ¬ ℓ ^ 2 ∣ (T.dδ j n).l₂.M ∧ (T.dδ j n).pd ≠ 0 ∧ ∃ α α' : 𝓞 D.host.E,
      α * α' = EX.piG 0 * EX.piG 1 * ((T.dδ j n).pd : 𝓞 D.host.E) ∧ α ≠ 0 ∧ α' ≠ 0 ∧
      ((¬ ℓ ∣ (T.dδ j n).l₂.M ∧ α = 1) ∨
        (ℓ ∣ (T.dδ j n).l₂.M ∧ α * T.Q.H.bar α = (ℓ : 𝓞 D.host.E) ∧ (T.dδ j n).l₂.Mb ≤ Ideal.span {T.Q.H.bar α}) ∨
        (ℓ ∣ (T.dδ j n).l₂.M ∧ α = (ℓ : 𝓞 D.host.E))) := by
  obtain ⟨hdv, hM, hcop, -⟩ := hs.dLev j hj n
  have hM0 : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  obtain ⟨p, hp, hpd⟩ := hs.dPd
  have hpp : (T.dδ j n).pd.Prime := by
    rw [hpd j hj n]
    rcases hp with rfl | rfl
    exacts [D.host.pde_prime, D.host.pde'_prime]
  have hbar := (GlobalTheory.HalfGen.half_principal_and_split D T.toCore h.toLawsM EX).2.1
  have hb : ∀ i, T.Q.H.bar (EX.piG i) = piBarO EX i := fun i => (hbar i).1
  have hn : ∀ i, EX.piG i * T.Q.H.bar (EX.piG i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
    intro i
    apply RingOfIntegers.ext
    rw [hb]
    exact (EX.piG_norm i).trans (by simp)
  have h0 : ∀ i, EX.piG i ≠ 0 := by
    intro i hi
    have := hn i
    rw [hi, zero_mul] at this
    exact (D.host.g_prime i).ne_zero (by exact_mod_cast this.symm)
  have hp0 : (((T.dδ j n).pd : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hsf : Squarefree (T.dδ j n).l₂.M := by
    rw [hM, Nat.squarefree_mul hcop.symm, hM0,
      Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]
    exact ⟨⟨(D.host.g_prime 0).prime.squarefree, (D.host.g_prime 1).prime.squarefree⟩, hpp.prime.squarefree⟩
  refine ⟨fun hd => hℓ.prime.not_unit (hsf ℓ (by rwa [← pow_two])), hpp.ne_zero, ?_⟩
  by_cases hd : ℓ ∣ (T.dδ j n).l₂.M
  · have hd' := hd
    rw [hM, hM0, hℓ.dvd_mul, hℓ.dvd_mul, Nat.prime_dvd_prime_iff_eq hℓ (D.host.g_prime 0),
      Nat.prime_dvd_prime_iff_eq hℓ (D.host.g_prime 1), Nat.prime_dvd_prime_iff_eq hℓ hpp] at hd'
    rcases hd' with (e | e) | e
    · exact ⟨EX.piG 0, EX.piG 1 * _, (mul_assoc _ _ _).symm, h0 0, mul_ne_zero (h0 1) hp0,
        Or.inr (Or.inl ⟨hd, by rw [hn, e], by rw [hb]; exact hdv.2.1.trans (hor 0)⟩)⟩
    · exact ⟨EX.piG 1, EX.piG 0 * _, by ring, h0 1, mul_ne_zero (h0 0) hp0,
        Or.inr (Or.inl ⟨hd, by rw [hn, e], by rw [hb]; exact hdv.2.1.trans (hor 1)⟩)⟩
    · exact ⟨_, EX.piG 0 * EX.piG 1, mul_comm _ _, hp0, mul_ne_zero (h0 0) (h0 1),
        Or.inr (Or.inr ⟨hd, by rw [e]⟩)⟩
  · exact ⟨1, _, _root_.one_mul _, one_ne_zero, mul_ne_zero (mul_ne_zero (h0 0) (h0 1)) hp0, Or.inl ⟨hd, rfl⟩⟩

theorem shortBound : ShortBoundSt := by
  intro D T h hs j hj hinj EX hor w g hg la y
  obtain ⟨hsec, Λ, N, x0, P, hU, hTb, hTM, hN, hadm, hP, hR⟩ := hg
  obtain ⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
  have hv0 : vAtV y g = nval Tc.V e (evI yI g) := by
    show y.1.1 g = _
    rw [hq]
    rfl
  rw [hv0]
  obtain ⟨inst, hnab⟩ := hs.dNab j hj w.n
  have hlev := hs.dLev j hj w.n
  obtain ⟨hDF, -, -, -, -, -, -, hfin⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore h.pins j hj w
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    obtain ⟨h1, h2, -⟩ := h.pins.2.2.2 j hj
    have h3 := hj.1
    have h4 := hj.2
    have h5 := D.R.m_add_three_le_k
    rw [h1, h2]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hrn : D.R.r ≤ w.n := hpq ▸
    (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n)).1 _ x0 hadm
  obtain ⟨ph, ψ, x₀, -, hph, -⟩ := hs.dPhi j hj w.n hrn
  have hwi := GlobalTheory.PlaceInt.datum_isIntegral _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n) hlev ph ψ x₀ hph x0
  obtain ⟨Cls, i1, i2, δ, gdet, hcmp⟩ := hs.dRoot j hj w.n
  obtain ⟨m₀, hm₀, hroot⟩ := GlobalTheory.CoverRoot.value_pow_eq_one _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n) Cls δ gdet hcmp
  have hbe := hs.beta j hj w.n (h.kPsi j hj) Λ hU hTb
  have hβ : betaH (Dw := T.Q.Dw j) T.Q.c Λ ≠ 0 ∧ BetaIs (Dw := T.Q.Dw j) T.Q.c Λ (betaH (Dw := T.Q.Dw j) T.Q.c Λ) := by
    unfold betaH
    rw [dif_pos hbe]
    exact ⟨hbe.choose_spec.1, hbe.choose_spec.2.1⟩
  obtain ⟨ef1, ef2, ef3⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n) Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n) hlev hnab m₀ hroot Λ N hU hTM hN (wtA w) P hP x0 g hsec hR
      Tc io yI hy
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have heR : ((r * e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast he'.ne'
  have hv : ∀ a : T.Q.c.F, vV T'.V (io₂ ((T.dδ j w.n).eF a)) = ((r * e : ℕ) : ℤ) * vLa la a := by
    intro a
    rw [hio]
    exact ho'.2 a
  have hvn : ∀ p : ℕ, vV T'.V (p : T'.Fr) = ((r * e : ℕ) : ℤ) * vLa la (p : T.Q.c.F) := by
    intro p
    rw [← hv, map_natCast, map_natCast]
  rw [← nval_bc iT hr hiT e, hval]
  obtain ⟨ℓ, hℓ, hu⟩ := exists_resChar T' hfr
  obtain ⟨hsq, hp0, α, α', hαb, hα0, hb0, hα⟩ := exists_alpha D T h hs j hj EX hor w.n (wtA w) ℓ hℓ
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ (T.Q.Dw j) _ (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ hnab.1 T' io₂ y₂ C (r * e) he' (wtA w) w.n
    (WeightAlgebra.DF w) hDF.le
  have hcard := GlobalTheory.PlaceInt.card_fun_levQ _ _ (T.Q.Dw j) (T.dδ j w.n).l₂ w.n
  have hM2 : (T.dδ j w.n).l₂.M = D.host.g 0 * D.host.g 1 * (T.dδ j w.n).pd := by
    rw [hlev.2.1, show T.Q.l.M = _ from h.pins.2.1.1]
  have hg0 : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  rw [hfin, hpq, Nat.mul_div_cancel_left _ two_pos, hM2] at hcard
  have hc0 : Nat.card (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) ≠ 0 := by
    rw [hcard]; exact pow_ne_zero _ (mul_ne_zero hg0 hp0)
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) α) ≠ 0 := (map_ne_zero io₂).2 (nrm_ne_zero _ _ hα0)
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ ((T.dδ j w.n).w x0 q)) _ ζ _
    ((Nat.card (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) : ℕ) : T'.Fr) _ m₀ hm₀ hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi q)) _
    (fun q => class_bound (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ (wtA w) w.n he' hch ℓ hℓ
      hu Λ N hU hTM hN _ ((map_ne_zero (T.dδ j w.n).eF).2 hβ.1) (ef1 _ hβ.2) _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi
      (fun b => levRep (q b)) (htp q) (hF q) hrat hsq α hα)
  refine le_trans ?_ (key.trans (le_of_eq ?_))
  · refine EReal.coe_le_coe_iff.2 (neg_le_neg ?_)
    have a1 : ∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) *
        D.host.vdH p * (WeightAlgebra.DF w : ℝ) / 2 = ramLoss D la w := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hvn, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ heR]
    have a2 : vV T'.V ((Nat.card (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) : ℕ) : T'.Fr) =
        ((r * e : ℕ) : ℤ) * ((vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) +
          vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F)) * (D.R.f * D.R.r * w.n : ℕ)) := by
      rw [hcard, Nat.cast_pow, vV_pow (by exact_mod_cast mul_ne_zero hg0 hp0), Nat.cast_mul (D.host.g 0 * D.host.g 1),
        vV_mul (by exact_mod_cast hg0) (by exact_mod_cast hp0), hvn, hvn]
      ring
    have a3 : vV T'.V (io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) α)) ≤
        ((r * e : ℕ) : ℤ) * (vLa la ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) +
          vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) * (WeightAlgebra.DF w : ℕ)) := by
      have hπ : EX.piG 0 * EX.piG 1 ≠ 0 := left_ne_zero_of_mul (hαb ▸ mul_ne_zero hα0 hb0)
      have b1 := congrArg (fun a => vV T'.V (io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) a))) hαb
      rw [nrm_mul, nrm_mul _ _ (EX.piG 0 * EX.piG 1), map_mul, map_mul,
        vV_mul hu0 ((map_ne_zero io₂).2 (nrm_ne_zero _ _ hb0)), nrm_nat, map_pow, map_natCast,
        vV_mul ((map_ne_zero io₂).2 (nrm_ne_zero _ _ hπ)) (pow_ne_zero _ (by exact_mod_cast hp0)),
        vV_pow (by exact_mod_cast hp0), hvn, ← ef3 _ (EX.piG 0 * EX.piG 1), hv,
        GlobalTheory.PtTie.nrm_eq_nnW D T h j hj hinj EX w, hDF] at b1
      have b3 : 0 ≤ vV T'.V (io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) α')) :=
        vV_nonneg (map_isIntegral_int io₂ (nrm_integral _ _ _))
      linarith
    have a4 : (vV T'.V (io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) α)) : ℝ) / (r * e : ℕ) ≤
        ((vLa la ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) +
          ((vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) * (WeightAlgebra.DF w : ℕ) := by
      rw [div_le_iff₀ (by exact_mod_cast he'), mul_comm]
      exact_mod_cast a3
    rw [a1, a2, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ heR]
    push_cast at a4 ⊢
    linarith
  · congr 3
    simp only [map_mul, map_inv₀, map_natCast]
    ring
end Run

end GlobalTheory.ShortBound
