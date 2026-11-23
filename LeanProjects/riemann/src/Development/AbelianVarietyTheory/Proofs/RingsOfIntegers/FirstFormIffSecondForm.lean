import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HarmonicValueSplitOfExtension
import Development.AbelianVarietyTheory.BlockTheory.GoodPlaces.ThetaValueRamifiedExtension

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaValueIdentityCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaValueRamifiedExtension

attribute [local instance] Over.cartesianMonoidalCategory

section Valuations

open IsLocalRing Polynomial

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_zpow (x : K) (n : ℤ) : vV V (x ^ n) = n * vV V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem vV_pow (x : K) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simpa using vV_zpow (V := V) x n

theorem exists_unit {x : K} (hx : x ≠ 0) (h : vV V x = 0) : ∃ u : V, IsUnit u ∧ algebraMap V K u = x := by
  have h1 : valV V x = 1 := by
    have h2 : WithZero.log (valV V x) = 0 := by simp only [vV] at h; omega
    rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), h2, WithZero.exp_zero]
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) (x := x) h1.le
  refine ⟨u, ?_, rfl⟩
  by_contra hu
  exact ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) (IsDiscreteValuationRing.maximalIdeal V) u).2 hu).ne h1

theorem exists_root {A : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [Fintype (ResidueField A)] {u : A} (hu : IsUnit u) (m : ℕ) :
    ∃ a : A, a ^ (Fintype.card (ResidueField A) * m + 1) = u ^ (Fintype.card (ResidueField A) - 1) := by
  set q := Fintype.card (ResidueField A) with hq
  have hmon : (X ^ (q * m + 1) - C (u ^ (q - 1)) : A[X]).Monic := monic_X_pow_sub_C _ (Nat.succ_ne_zero _)
  have h0 : (X ^ (q * m + 1) - C (u ^ (q - 1)) : A[X]).eval 1 ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff]
    have : residue A u ≠ 0 := (hu.map (residue A)).ne_zero
    simp [FiniteField.pow_card_sub_one_eq_one _ this, hq]
  have h1 : IsUnit (Ideal.Quotient.mk (maximalIdeal A)
      ((derivative (X ^ (q * m + 1) - C (u ^ (q - 1)) : A[X])).eval 1)) := by
    change IsUnit (residue A _)
    have : ((q : ℕ) : ResidueField A) = 0 := FiniteField.cast_card_eq_zero _
    rw [derivative_sub, derivative_C, derivative_X_pow]
    simp [this]
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := maximalIdeal A) _ hmon 1 h0 h1
  exact ⟨a, by simpa [sub_eq_zero] using ha⟩

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

theorem exists_scale [IsAdicComplete (maximalIdeal V) V] [Finite (ResidueField V)] (i : K →+* L) :
    ∃ r : ℤ, ∀ x : K, vV W (i x) = r * vV V x := by
  have := Fintype.ofFinite (ResidueField V)
  have hz : ∀ x : K, x ≠ 0 → vV V x = 0 → vV W (i x) = 0 := fun x hx h => by
    obtain ⟨u, hu, rfl⟩ := exists_unit hx h
    set q := Fintype.card (ResidueField V) with hq
    have hq1 : 1 < q := Fintype.one_lt_card
    set t := vV W (i (algebraMap V K u)) with ht
    obtain ⟨a, ha⟩ := exists_root hu (((q - 1 : ℕ) : ℤ) * t).natAbs
    have h2 := congrArg (fun z => vV W (i (algebraMap V K z))) ha
    simp only [map_pow, vV_pow, ← hq, ← ht] at h2
    have h3 : ((q - 1 : ℕ) : ℤ) * t = 0 := by
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨_, h2.symm⟩ ?_
      rw [Int.natAbs_natCast]
      exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_left _ (by omega))
    rcases mul_eq_zero.1 h3 with h4 | h4
    · omega
    · exact h4
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal V).valuation_exists_uniformizer K
  have hπ1 : vV V π = 1 := by simp [vV, valV, hπ]
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ1
  refine ⟨vV W (i π), fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, vV]
  have h := hz (x * π ^ (-vV V x)) (mul_ne_zero hx (zpow_ne_zero _ hπ0))
    (by rw [vV_mul hx (zpow_ne_zero _ hπ0), vV_zpow, hπ1]; ring)
  rw [map_mul, map_zpow₀, vV_mul ((map_ne_zero i).2 hx) (zpow_ne_zero _ ((map_ne_zero i).2 hπ0)), vV_zpow] at h
  linarith

end Valuations

theorem overLa_iff {F : Type} [Field F] [NumberField F] {la : HeightOneSpectrum (𝓞 F)} {V V' : CDVR}
    {io : F →+* V.Fr} {e : ℕ} (ho : OverLa la V.V io e) (hV : V.FinRes) (i : V.Fr →+* V'.Fr) (e' : ℕ) :
    OverLa la V'.V (i.comp io) e' ↔ ∃ r, IsRamExt V V' i r ∧ e' = r * e := by
  constructor
  · intro ho'
    have : Finite (IsLocalRing.ResidueField V.V) := hV
    obtain ⟨r, hr⟩ := exists_scale (V := V.V) (W := V'.V) i
    obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer F
    have hπ1 : vLa la π = 1 := by simp [vLa, hπ]
    have h := ho'.2 π
    rw [RingHom.comp_apply, hr, ho.2, hπ1, _root_.mul_one, _root_.mul_one] at h
    have he : (0 : ℤ) < e := by exact_mod_cast ho.1
    have he' : (0 : ℤ) < e' := by exact_mod_cast ho'.1
    have hr0 : 0 < r := by by_contra hn; nlinarith
    lift r to ℕ using hr0.le
    exact ⟨r, ⟨by exact_mod_cast hr0, fun a _ => hr a⟩, by exact_mod_cast h.symm⟩
  · rintro ⟨r, ⟨hr0, hr⟩, rfl⟩
    refine ho.bc i hr0 fun a => ?_
    by_cases ha : a = 0
    · subst ha
      rw [map_zero]
      simp [vV]
    · exact hr a ha

section Clauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isBaseChange_iff {V V' : CDVR} {io : c.F →+* V.Fr} (i : V.Fr →+* V'.Fr) (y : IntFr Xo c V io)
    (y' : IntFr Xo c V' (i.comp io)) :
    IsBaseChange i y y' ↔
      letI := io.toAlgebra
      letI := (i.comp io).toAlgebra
      ∃ φ : V.Fr →ₐ[c.F] V'.Fr, φ.toRingHom = i ∧ FrMap φ y.1 y'.1 := by
  letI := io.toAlgebra
  letI := (i.comp io).toAlgebra
  refine ⟨fun h => ⟨extAlg io i, rfl, h⟩, ?_⟩
  rintro ⟨φ, hφ, h⟩
  have : φ = extAlg io i := AlgHom.ext fun a => RingHom.congr_fun hφ a
  rw [this] at h
  exact h

variable [StarRing (𝓞 E)]

theorem rhs_eq {V : CDVR} {io : c.F →+* V.Fr} {y : IntFr Xo c V io} (C : IntegralChartA3 Xo c V io y) {n : ℕ}
    (P : MvPolynomial (LtN Dw n) c.F) (g : Fin n → Germ.PS V.Fr 1 (chD C.ch)) :
    letI := io.toAlgebra
    io (((l.M : c.F) ^ P.totalDegree)⁻¹) *
        ∑ mo ∈ (P.map io).support, (P.map io).coeff mo *
          ∏ b, C.ch.B.nabVal V.Fr C.ch.h H.w0 (l.M ^ 2) (g b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1) =
      ((l.M : V.Fr) ^ P.totalDegree)⁻¹ * harmComb C P g := by
  rw [map_inv₀, map_pow, map_natCast, MvPolynomial.support_map_of_injective P io.injective]
  refine congrArg _ (Finset.sum_congr rfl fun m _ => ?_)
  rw [MvPolynomial.coeff_map]

end Clauses

abbrev Comparison₂ : Type 1 :=
  ∀ (D : D7) (T : Top D) (j : ℕ) (V : CDVR) (io : T.Q.c.F →+* V.Fr) (V' : CDVR) (i : V.Fr →+* V'.Fr),
    IntFr (T.Q.Xo j) T.Q.c V io → IntFr (T.Q.Xo j) T.Q.c V' (i.comp io) → Prop

def trivialTieCondition : Comparison₂ := fun _ _ _ _ _ _ _ _ _ => True

def baseChangeTie : Comparison₂ := fun _ _ _ _ _ _ i y y' => IsBaseChange i y y'

def fullTie : Comparison₂ := fun _ _ _ _ _ _ i y y' => IsBaseChange i y y' ∧ ModelsSplit y'

def FirstForm (R : Comparison₂) : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ) (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)),
        OverLa la T'.V (iT.comp io) e' ∧ yI'.IsAlg ∧ R D T j Tc io T' iT yI yI' ∧
        letI := (iT.comp io).toAlgebra
        ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' (iT.comp io) yI')
          (F : Fin w.n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yI'.1.x)))
          (g : Fin w.n → Germ.PS T'.Fr 1 (chD C.ch)),
          (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yI'.1.s (levPt (T.Q.Xo j) yI'.1.x (x b)) (F b)) ∧
          (∀ b, IsGerm yI'.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (T.Q.l.M ^ 2)
            (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (g b)) ∧
          (∀ b, IsIntPS T' (g b)) ∧
          iT (evI yI f) = (iT.comp io) (((T.Q.l.M : T.Q.c.F) ^ P.totalDegree)⁻¹) *
            ∑ mo ∈ (P.map (iT.comp io)).support, (P.map (iT.comp io)).coeff mo *
              ∏ b, C.ch.B.nabVal T'.Fr C.ch.h T.Q.H.w0 (T.Q.l.M ^ 2) (g b) C.ch.uvec
                (MvPolynomial.monomial (colOf mo b) 1)

def SecondForm (R : Comparison₂) : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (V : CDVR) (io : T.Q.c.F →+* V.Fr) (y : IntFr (T.Q.Xo j) T.Q.c V io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la V.V io e → y.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      ∃ (V' : CDVR) (i : V.Fr →+* V'.Fr) (r : ℕ) (y' : IntFr (T.Q.Xo j) T.Q.c V' (i.comp io))
        (F : Fin w.n → LevelSec y') (C : IntegralChartA3 (T.Q.Xo j) T.Q.c V' (i.comp io) y')
        (g : Fin w.n → Germ.PS V'.Fr 1 (chD C.ch)),
        IsRamExt V V' i r ∧ y'.IsAlg ∧ R D T j V io V' i y y' ∧
        (∀ b, IsLevelTranslate y' (x b) (F b)) ∧
        (∀ b, IsLevelGerm C (F b) (g b)) ∧ (∀ b, IsIntPS V' (g b)) ∧
        i (evI y f) = ((T.Q.l.M : V'.Fr) ^ P.totalDegree)⁻¹ * harmComb C P g

theorem firstForm_iff_secondForm (R : Comparison₂) : FirstForm R ↔ SecondForm R := by
  constructor
  · intro hA D T h j hj _ nab hnab w x P hP f hf V io y e la ho hy hM
    obtain ⟨V', i, e', y', ho', hy', hR, C, F, g, hF, hg, hI, hv⟩ :=
      hA D T h j hj nab hnab w x P hP f hf V io y e la ho hy hM
    obtain ⟨r, hr, -⟩ := (overLa_iff ho hy i e').1 ho'
    exact ⟨V', i, r, y', F, C, g, hr, hy', hR, hF, hg, hI, hv.trans (rhs_eq C P g)⟩
  · intro hB D T h j hj _ nab hnab w x P hP f hf V io y e la ho hy hM
    obtain ⟨V', i, r, y', F, C, g, hr, hy', hR, hF, hg, hI, hv⟩ :=
      hB D T h j hj nab hnab w x P hP f hf V io y e la ho hy hM
    exact ⟨V', i, r * e, y', (overLa_iff ho hy i _).2 ⟨r, hr, rfl⟩, hy', hR, C, F, g, hF, hg, hI,
      hv.trans (rhs_eq C P g).symm⟩

theorem FirstForm.mono {R R' : Comparison₂} (hR : ∀ D T j V io V' i y y', R D T j V io V' i y y' → R' D T j V io V' i y y')
    (hA : FirstForm R) : FirstForm R' := by
  intro D T h j hj _ nab hnab w x P hP f hf V io y e la ho hy hM
  obtain ⟨V', i, e', y', ho', hy', h1, h2⟩ := hA D T h j hj nab hnab w x P hP f hf V io y e la ho hy hM
  exact ⟨V', i, e', y', ho', hy', hR _ _ _ _ _ _ _ _ _ h1, h2⟩

theorem first_iff : HarmonicValueAfterExtension ↔ FirstForm trivialTieCondition := by
  constructor
  · intro hA D T h j hj _ nab hnab w x P hP f hf V io y e la ho hy hM
    obtain ⟨V', i, e', y', ho', hy', h2⟩ := hA D T h j hj nab hnab w x P hP f hf V io y e la ho hy hM
    exact ⟨V', i, e', y', ho', hy', trivial, h2⟩
  · intro hA D T h j hj _ nab hnab w x P hP f hf V io y e la ho hy hM
    obtain ⟨V', i, e', y', ho', hy', -, h2⟩ := hA D T h j hj nab hnab w x P hP f hf V io y e la ho hy hM
    exact ⟨V', i, e', y', ho', hy', h2⟩

theorem second_iff : ThetaValueIdentity ↔ SecondForm fullTie := by
  constructor
  · intro hB D T h j hj _ nab hnab w x P hP f hf V io y e la ho hy hM
    obtain ⟨V', i, r, y', F, C, g, hr, hy', h1, h2, h3⟩ := hB D T h j hj nab hnab w x P hP f hf V io y e la ho hy hM
    exact ⟨V', i, r, y', F, C, g, hr, hy', ⟨h1, h2⟩, h3⟩
  · intro hB D T h j hj _ nab hnab w x P hP f hf V io y e la ho hy hM
    obtain ⟨V', i, r, y', F, C, g, hr, hy', ⟨h1, h2⟩, h3⟩ :=
      hB D T h j hj nab hnab w x P hP f hf V io y e la ho hy hM
    exact ⟨V', i, r, y', F, C, g, hr, hy', h1, h2, h3⟩

theorem first_of_second (hB : ThetaValueIdentity) : HarmonicValueAfterExtension :=
  first_iff.2 (((firstForm_iff_secondForm _).2 (second_iff.1 hB)).mono fun _ _ _ _ _ _ _ _ _ _ => trivial)

theorem valuation_form_of_first (hA : HarmonicValueAfterExtension) : HarmonicValueAtIntegralPoint := by
  intro D T h j hj _ nab hnab w x P hP f hf Tc io yI e la ho hy hM
  obtain ⟨T', iT, e', yI', ho', hy', C, F, g, -, -, hI, hv⟩ :=
    hA D T h j hj nab hnab w x P hP f hf Tc io yI e la ho hy hM
  obtain ⟨r, ⟨hr0, hr⟩, rfl⟩ := (overLa_iff ho hy iT e').1 ho'
  have hi : ∀ a : Tc.Fr, vV T'.V (iT a) = (r : ℤ) * vV Tc.V a := fun a => by
    by_cases ha : a = 0
    · subst ha
      rw [map_zero]
      simp [vV]
    · exact hr a ha
  have hM0 : (T.Q.l.M : T.Q.c.F) ≠ 0 := by
    intro h0
    apply hM
    rw [Nat.cast_eq_zero.1 h0, Nat.cast_zero]
    exact la.asIdeal.zero_mem
  refine ⟨T', iT.comp io, r * e, yI', ho', hy', C, P.map (iT.comp io), g,
    ffvMap D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c (wtA w) w.n P hP T' (iT.comp io), hI, ?_⟩
  rw [← nval_bc iT hr0 hi e (evI yI f), hv, nval_smul ho' (inv_ne_zero (pow_ne_zero _ hM0)),
    vLa_natCast_inv_pow la hM]
  simp only [Int.cast_zero, EReal.coe_zero, zero_add]

theorem comparison :
    (∀ R : Comparison₂, FirstForm R ↔ SecondForm R) ∧
    (HarmonicValueAfterExtension ↔ SecondForm trivialTieCondition) ∧ (ThetaValueIdentity ↔ FirstForm fullTie) ∧
    (ThetaValueIdentity → HarmonicValueAfterExtension) ∧ (HarmonicValueAfterExtension → HarmonicValueAtIntegralPoint) :=
  ⟨firstForm_iff_secondForm, first_iff.trans (firstForm_iff_secondForm _),
    second_iff.trans (firstForm_iff_secondForm _).symm, first_of_second, valuation_form_of_first⟩

theorem second_of_inputs (hFin : ThValFinExtSplitSt) (hCI : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) (hG : GermChartSplitFibre) :
    ThetaValueIdentity := by
  refine second_iff.2 ((firstForm_iff_secondForm _).1 ?_)
  intro D T h j hj _ nab hnab w x P hP f hf Tc io yI e la ho hy hM
  obtain ⟨Tc', iT, e', he', hval, yI', hy', hsplit, hrest⟩ :=
    hFin D T h j hj nab ⟨inferInstance, hnab⟩ w x P hP f hf Tc io yI hy
  letI := io.toAlgebra
  letI := (iT.comp io).toAlgebra
  obtain ⟨φ, F, hφ, hmap, hV, hth⟩ := hrest
  have ho' : OverLa la Tc'.V (iT.comp io) (e' * e) := (overLa_iff ho hy iT _).2 ⟨e', ⟨he', hval⟩, rfl⟩
  obtain ⟨C₀, hgerm₀, hval₀⟩ := hnab.2 Tc'.Fr yI'.1
  obtain ⟨C, g, hgG, hgI⟩ := hG D T h j hj hnab.1 Tc' (iT.comp io) yI' (e' * e) la ho' hy' hM hsplit x F hV
  choose g₀ hg₀ using fun b => hgerm₀ (T.Q.l.M ^ 2) (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b))
  have hci := hCI D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c hnab.1 Tc'.Fr yI'.1 C₀ C.ch (T.Q.l.M ^ 2) w.n
    (fun b => zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) g₀ g hg₀ hgG (wtA w) P hP
  have hte : thExpr (T.Q.Xo j) T.Q.c nab yI'.1 P F =
      algebraMap T.Q.c.F Tc'.Fr (((T.Q.l.M : T.Q.c.F) ^ P.totalDegree)⁻¹) *
        Formalism.MainNotions.ModuliIntegralCharts.H1.chartVal C₀ (T.Q.l.M ^ 2) g₀ P := by
    unfold thExpr Formalism.MainNotions.ModuliIntegralCharts.H1.chartVal
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    exact (nab_zCast nab yI'.1 (natCast_sq T.Q.l.M) (F b) (colOf m b)).trans (hval₀ _ _ _ (hg₀ b) _)
  refine ⟨Tc', iT, e' * e, yI', ho', hy', ⟨(isBaseChange_iff iT yI yI').2 ⟨φ, hφ, hmap⟩, hsplit⟩, C, F, g, hV, hgG,
    hgI, ?_⟩
  rw [hth, hte, hci]
  refine congrArg _ ?_
  unfold Formalism.MainNotions.ModuliIntegralCharts.H1.chartVal
  rw [MvPolynomial.support_map_of_injective P (iT.comp io).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  rfl

end GlobalTheory.ThetaValueIdentityCompare
