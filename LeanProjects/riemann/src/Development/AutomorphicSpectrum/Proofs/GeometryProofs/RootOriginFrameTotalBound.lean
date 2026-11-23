import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SandwichPointOverFieldExtStatement
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PRootsOfUnityValuation
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnLie

section Dvr

variable {V : Type} {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem valV_algebraMap_le_one (x : V) : valV V (algebraMap V K x) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one _ x

theorem vV_unit {u : V} (hu : IsUnit u) : vV V (algebraMap V K u) = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 : valV V (algebraMap V K (w : V)) ≤ 1 := valV_algebraMap_le_one _
  have h2 : valV V (algebraMap V K ((w⁻¹ : Vˣ) : V)) ≤ 1 := valV_algebraMap_le_one _
  have h3 : valV V (algebraMap V K (w : V)) * valV V (algebraMap V K ((w⁻¹ : Vˣ) : V)) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  have h4 : valV V (algebraMap V K (w : V)) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ valV V (algebraMap V K (w : V)) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  simp [vV, h4]

theorem vV_one : vV V (1 : K) = 0 := by simp [vV]

theorem vV_pow {x : K} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV_one]
  | succ n ih =>
    rw [pow_succ, vV_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

theorem vV_associated {a b : V} (h : Associated a b) (ha : a ≠ 0) :
    vV V (algebraMap V K a) = vV V (algebraMap V K b) := by
  obtain ⟨u, rfl⟩ := h
  have inj := IsFractionRing.injective V K
  rw [map_mul, vV_mul ((map_ne_zero_iff _ inj).2 ha) ((map_ne_zero_iff _ inj).2 u.ne_zero), vV_unit u.isUnit,
    add_zero]

theorem vV_sub_one {p : ℕ} (hp : p.Prime) {ζ : V} (hζ : IsPrimitiveRoot ζ p) :
    ((p - 1 : ℕ) : ℤ) * vV V (algebraMap V K (ζ - 1)) = vV V (algebraMap V K (p : V)) := by
  have inj := IsFractionRing.injective V K
  have h0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hp.one_lt)
  have hass : Associated ((ζ - 1) ^ (p - 1)) (p : V) :=
    ((GroundTheory.Heights₂.Heights.RootsOfUnityValuation.associated_sub_comm ζ 1).pow_pow).trans
      (GroundTheory.Heights₂.Heights.RootsOfUnityValuation.one_sub_pow_associated hp hζ)
  rw [← vV_associated hass (pow_ne_zero _ h0), map_pow, vV_pow ((map_ne_zero_iff _ inj).2 h0)]

variable (V K) in

def realVal : Valuation K NNReal :=
  (valV V).map (WithZeroMulInt.toNNReal (e := 2) two_ne_zero)
    (WithZeroMulInt.toNNReal_strictMono (by norm_num)).monotone

theorem realVal_le_one_iff {x : K} : realVal V K x ≤ 1 ↔ valV V x ≤ 1 := by
  have := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).le_iff_le (a := valV V x) (b := 1)
  simpa [realVal] using this

theorem realVal_lt_one_iff {x : K} : realVal V K x < 1 ↔ valV V x < 1 := by
  have := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).lt_iff_lt (a := valV V x) (b := 1)
  simpa [realVal] using this

theorem realVal_integers : (realVal V K).Integers V where
  hom_inj := IsFractionRing.injective V K
  map_le_one x := realVal_le_one_iff.2 (valV_algebraMap_le_one x)
  exists_of_le_one _ h := IsDiscreteValuationRing.exists_lift_of_le_one (realVal_le_one_iff.1 h)

end Dvr

section Pt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {R : Type} [CommRing R] [IsLocalRing R]

theorem exists_value (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem value_aeval (hg : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R} (hv : ValAt ξ z a r)
    (f : Polynomial ℤ) (hf : Polynomial.aeval a f = 0) : Polynomial.aeval r f = 0 := by
  obtain ⟨h, s, hs, rfl⟩ := hv
  let φ : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  have e1 := Polynomial.aeval_algHom_apply (genMap ξ ⟨centre z, h⟩).toIntAlgHom s f
  have e2 := Polynomial.aeval_algHom_apply φ.toIntAlgHom s f
  have h0 : Polynomial.aeval s f = 0 := by
    apply hg.inj ⟨centre z, h⟩
    rw [map_zero]
    have : (genMap ξ ⟨centre z, h⟩).toIntAlgHom s = a := hs
    rw [this, hf] at e1
    exact e1.symm
  rw [h0] at e2
  exact e2.trans (map_zero φ.toIntAlgHom)

theorem isUnit_of_unitAt (hg : IsCptGen ξ) (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {n : ℕ}
    (hu : unitAt ξ ⟨centre z, h⟩ (n : Ω)) : IsUnit (n : R) := by
  obtain ⟨hn, -, hi⟩ := hu
  obtain ⟨r, hr⟩ := exists_value z h hi
  have h1 := value_aeval hg hr (Polynomial.C (n : ℤ) * Polynomial.X - 1) (by
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one]
    simp [hn])
  simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one] at h1
  have h2 : (n : R) * r = 1 := by simpa [sub_eq_zero] using h1
  exact IsUnit.of_mul_eq_one _ h2

theorem aeval_cyclotomic {S : Type} [CommRing S] (n : ℕ) (x : S) :
    Polynomial.aeval x (Polynomial.cyclotomic n ℤ) = (Polynomial.cyclotomic n S).eval x := by
  rw [← Polynomial.map_cyclotomic n (algebraMap ℤ S), Polynomial.eval_map_algebraMap]

end Pt

section Abs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  {c : Coeff l}

theorem vLa_prime {p : ℕ} [hp : Fact p.Prime] {la : HeightOneSpectrum (𝓞 c.F)} (hla : (p : 𝓞 c.F) ∈ la.asIdeal) :
    vLa la (p : c.F) = ramOverZ la := by
  have hres : Formalism.L2.Pj.resCharOf la = p := by
    by_contra h
    refine Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => h ?_) hla
    exact (Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp.out).1 hd
  rw [← hres]
  exact Formalism.L2.Pj.Crude.crv_vLa_char la

theorem vV_prime {p : ℕ} [Fact p.Prime] {la : HeightOneSpectrum (𝓞 c.F)} (hla : (p : 𝓞 c.F) ∈ la.asIdeal)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (hov : OverLa la T.V io e) :
    vV T.V (algebraMap T.V T.Fr (p : T.V)) = (e : ℤ) * ramOverZ la := by
  have h := hov.2 (p : c.F)
  rw [map_natCast, vLa_prime hla] at h
  rwa [map_natCast]

theorem absT_of_vV {p : ℕ} (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) {e : ℕ} (he : 0 < e)
    (hr : 0 < ramOverZ la) {x : T.Fr} (hx : x ≠ 0) {a : ℝ}
    (h : (vV T.V x : ℝ) = a * ((e : ℝ) * (ramOverZ la : ℝ))) : absT p la T e x = (p : ℝ) ^ (-a) := by
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hr' : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold absT
  rw [if_neg hx, h, mul_div_assoc, div_self (mul_ne_zero he' hr'), mul_one]

theorem absT_kappa {p : ℕ} [hp : Fact p.Prime] {la : HeightOneSpectrum (𝓞 c.F)} (hla : (p : 𝓞 c.F) ∈ la.asIdeal)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (hov : OverLa la T.V io e) {κz : T.V} (h2 : p = 2 → κz = 4)
    (hodd : p ≠ 2 → IsPrimitiveRoot (κz + 1) p) :
    absT p la T e (algebraMap T.V T.Fr κz) = (p : ℝ) ^ (-Small.htExp p) := by
  have hr := FinRd.ram_pos hla
  have he := hov.1
  have inj := IsFractionRing.injective T.V T.Fr
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hr' : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hvp := vV_prime hla hov
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  by_cases h : p = 2
  · have hk : algebraMap T.V T.Fr κz = algebraMap T.V T.Fr (p : T.V) ^ 2 := by
      rw [h2 h, ← map_pow, h]
      norm_num
    have hne : algebraMap T.V T.Fr (p : T.V) ≠ 0 := (map_ne_zero_iff _ inj).2 hp0
    rw [hk, absT_of_vV la T he hr (pow_ne_zero _ hne) (a := Small.htExp p)]
    rw [vV_pow hne, hvp]
    simp only [Small.htExp, if_pos h]
    push_cast
    ring
  · have hz := hodd h
    have h1 := vV_sub_one (K := T.Fr) hp.out hz
    rw [add_sub_cancel_right, hvp] at h1
    have hk0 : κz ≠ 0 := fun h0 => hz.ne_one hp.out.one_lt (by rw [h0, zero_add])
    refine absT_of_vV la T he hr ((map_ne_zero_iff _ inj).2 hk0) ?_
    have h3 : ((p : ℝ) - 1) ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
      linarith
    have h4 : (((p - 1 : ℕ) : ℤ) : ℝ) = (p : ℝ) - 1 := by
      push_cast [Nat.cast_sub hp.out.one_lt.le]
      ring
    have h5 : ((p : ℝ) - 1) * (vV T.V (algebraMap T.V T.Fr κz) : ℝ) = (e : ℝ) * (ramOverZ la : ℝ) := by
      rw [← h4]
      exact_mod_cast h1
    simp only [Small.htExp, if_neg h]
    field_simp
    linarith

end Abs

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnLie

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnLie

theorem lieEig_htDual : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → Or.𝔐.OmVB → 0 < Dw.p + Dw.q → p ∈ SS → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → ∃ κz : T.V, FinRd.Roots.lieEig Or MC ρC σ ≤ Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC ∧ (∀ w ∈ Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC, κz • w ∈ FinRd.Roots.lieEig Or MC ρC σ) ∧ FinRd.absT p la T e (algebraMap T.V T.Fr κz) = (p : ℝ) ^ (-Small.htExp p) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hev hgood la T io e y evT zT t hI zV hRd
    hOm hpq hpS EC _ _ _ _ MC ρC hAct s σ hσ
  obtain ⟨hla, hov, -⟩ := hI
  have hHT : HT.HTFree Or.𝔐 p := hOm p hpS
  obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hG.2.2.2.2.2.2.1 E H Dw l Xo c O β Y SS _ _ _ RM.y Or.𝔐 p hpS hpq hHT
  have hgen := Or.𝔐.tie.gen
  have hr := FinRd.ram_pos hla
  have hpos : (0 : ℤ) < (e : ℤ) * ramOverZ la := by
    have h1 : (0 : ℤ) < e := by exact_mod_cast hov.1
    have h2 : (0 : ℤ) < ramOverZ la := by exact_mod_cast hr
    exact mul_pos h1 h2
  have hvp := vV_prime hla hov
  have hFib : InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := fun hu => by
    have h2 := vV_unit (K := T.Fr) (isUnit_of_unitAt hgen zV (Or.𝔐.all _) hu)
    rw [hvp] at h2
    omega
  obtain ⟨κz, hκz⟩ := exists_value zV (Or.𝔐.all _) (hS _ hFib).1
  have : CharZero T.Fr := IsFractionRing.charZero T.V
  have hv1 : realVal T.V T.Fr (p : T.Fr) < 1 := by
    refine realVal_lt_one_iff.2 (lt_of_le_of_ne ?_ fun h1 => ?_)
    · simpa using valV_algebraMap_le_one (K := T.Fr) (p : T.V)
    · have h2 : vV T.V (algebraMap T.V T.Fr (p : T.V)) = 0 := by simp [vV, h1]
      rw [hvp] at h2
      omega
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.sandwich_point_over_field_ext E H Dw l Xo c O β Y SS _ _ _ RM.y Or.𝔐 p hpS κ hHT hS T.Fr
    (realVal T.V T.Fr) T.V realVal_integers hv1 zV EC MC ρC s σ κz hAct hσ hκz
  refine ⟨κz, h1, h2, absT_kappa hla hov (fun h => ?_) (fun h => ?_)⟩
  · rw [HT.IsCp, if_pos h] at hκ
    have h3 := value_aeval hgen hκz (Polynomial.X - Polynomial.C 4) (by
      simp only [map_sub, Polynomial.aeval_X, hκ, map_ofNat, sub_self])
    simp only [map_sub, Polynomial.aeval_X, map_ofNat] at h3
    exact sub_eq_zero.1 h3
  · rw [HT.IsCp, if_neg h] at hκ
    obtain ⟨ζ, hζ, rfl⟩ := hκ
    have hp0 : NeZero (p : T.V) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
    have h3 := value_aeval hgen hκz ((Polynomial.cyclotomic p ℤ).comp (Polynomial.X + 1)) (by
      rw [Polynomial.aeval_comp]
      simp only [map_add, Polynomial.aeval_X, map_one, sub_add_cancel]
      rw [aeval_cyclotomic]
      exact hζ.isRoot_cyclotomic (Fact.out : p.Prime).pos)
    rw [Polynomial.aeval_comp] at h3
    simp only [map_add, Polynomial.aeval_X, map_one] at h3
    rw [aeval_cyclotomic] at h3
    exact Polynomial.isRoot_cyclotomic_iff.1 h3

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnLie
