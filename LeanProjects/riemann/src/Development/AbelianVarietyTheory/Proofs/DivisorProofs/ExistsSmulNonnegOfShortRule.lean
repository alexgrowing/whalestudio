import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.VdHLeNatAbs
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortBoundOfTrivAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecomposition
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueTranslatedProductValuationBound

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv

namespace GlobalTheory.IntCuspLat

theorem nval_natCast_nonneg {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] (e m : ℕ) : 0 ≤ nval V e (m : K') :=
  GlobalTheory.ShortBound.nval_nonneg e (isIntegral_natCast _)

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem sum_bound_of_trivAt (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N M : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (ht : ∀ b, tp b ^ (N ^ 2) = 1)
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ)
    (n' A Bn j : ℕ) (α β₀ : 𝓞 E) (hn' : Nat.Coprime n' ℓ) (hfac : (N : 𝓞 E) = β₀ * α * n')
    (hA : α * H.bar α = (A : 𝓞 E)) (hB : β₀ * H.bar β₀ = (Bn : 𝓞 E)) (hAB : A * Bn = ℓ ^ j)
    (htp : ∀ b, (tp b ≫ Xo.univ.t.act.act β₀) ^ (n' ^ 2 * A) = 1) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
      ((N : c.F) ^ P.totalDegree)⁻¹)) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  letI := io.toAlgebra
  have hN : Odd N := hL.1
  obtain ⟨hfz, hm0, hT⟩ := GlobalTheory.TrivLattice.trivAt_units E H Dw l c n Λ N M ℓ hU hL hℓ htr
  obtain ⟨-, hFF⟩ := hT T io hlu
  obtain ⟨J, J', _, _, a, a', σ, -, haZ, ⟨m, hm, ha'⟩, hzs, hcard⟩ :=
    GlobalTheory.T.isotropic_group_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hℓ z hz hg
  have hlev : N ^ 2 = n' ^ 2 * ℓ ^ j := by
    have h2 : (N : 𝓞 E) = H.bar β₀ * H.bar α * n' := by
      have := congrArg H.bar hfac
      simpa only [map_mul, map_natCast] using this
    have h3 : ((N ^ 2 : ℕ) : 𝓞 E) = ((n' ^ 2 * (A * Bn) : ℕ) : 𝓞 E) := by
      push_cast
      rw [← hA, ← hB, sq]
      nth_rewrite 1 [hfac]
      rw [h2]; ring
    rw [← hAB]
    exact_mod_cast h3
  have hUU : ∀ i i' b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (a' i' b) (tp b) (F (σ (i, i')) b) := by
    intro i i' b
    obtain ⟨hi, hi2⟩ := (haZ (a i)).1 ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hi2 b
    have h1 := hF (σ (i, i')) b
    rw [hzs] at h1
    exact isUUOver_of_mul Xo hN _ (a i b) (a' i' b) (tp b) (pow_eq_one_of_trivAt Xo htr hi b hk) (ha' i' b).2 (ht b)
      (hm.pow_right k) hk (ha' i' b).1 _ h1
  obtain ⟨i₀⟩ : Nonempty J := Fintype.card_pos_iff.1 (by rw [hcard]; exact pow_pos hℓ.pos _)
  have hsum : ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P =
      (Fintype.card J : T.Fr) * ∑ i', hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (i₀, i')) b)) P := by
    rw [← σ.sum_comp, Fintype.sum_prod_type, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    congr 1
    funext b
    exact sqN_eq_of_isUUOver Xo hN _ _ _ (ha' i' b).2 (ht b) _ _ (hUU i i' b) (hUU i₀ i' b)
  have hterm : ∀ i', ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) *
      hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (i₀, i')) b)) P) := fun i' => by
    refine GlobalTheory.T.harmonicValue_translated_product_valuation_bound E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hb N n' A Bn α β₀ hN hfac hA hB
      (isUnit_of_coprime T hn' hlu) (a' i') tp _ (fun b => ⟨(ha' i' b).2, ht b, ?_, htp b, hUU i₀ i' b⟩) P hP.1
      (hFF w P hP)
    have h1 : (a' i' b ^ (n' ^ 2)) ^ m = 1 := by rw [← pow_mul, _root_.mul_comm, pow_mul, (ha' i' b).1, one_pow]
    have h2 : (a' i' b ^ (n' ^ 2)) ^ (ℓ ^ j) = 1 := by rw [← pow_mul, ← hlev, (ha' i' b).2]
    have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rw [(hm.pow_right j).gcd_eq_one, pow_one] at h3
    have := Xo.univ.t.act.hom (α * β₀)
    rw [← MonObj.pow_comp, h3, MonObj.one_comp]
  obtain ⟨m', hm'c, hm'⟩ : ∃ m' : ℕ, Nat.Coprime m' ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) = Fintype.card J * m' :=
    ⟨_, (Nat.coprime_ordCompl hℓ hm0).symm, by rw [hcard, hfz, Nat.ordProj_mul_ordCompl_eq_self]⟩
  have hm'u := isUnit_of_coprime T hm'c hlu
  haveI : CharZero T.Fr := algebraRat.charZero _
  have hm'0 : (m' : T.Fr) ≠ 0 := by
    have : m' ≠ 0 := by rintro rfl; simp at hm'u
    exact_mod_cast this
  have hJ0 : (Fintype.card J : T.Fr) ≠ 0 := by
    have : Fintype.card J ≠ 0 := by rw [hcard]; exact (pow_pos hℓ.pos _).ne'
    exact_mod_cast this
  have hre : ∀ s : T.Fr, io (nrm Dw c w α * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
      ((Fintype.card J : T.Fr) * s) =
      (m' : T.Fr)⁻¹ * (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) * s) := fun s => by
    rw [hm']
    simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
    generalize (io ((N : c.F) ^ P.totalDegree))⁻¹ = q
    field_simp
  rw [hsum, hre, nval_mul_unit e (inv_ne_zero hm'0) (vV_inv_eq_zero T (vV_natCast T hm'u)), Finset.mul_sum]
  exact le_nval_sum T _ e _ _ fun i' _ => hterm i'

theorem class_bound_of_trivAt (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N l.M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ)
    (hsq : ¬ ℓ ^ 2 ∣ l.M) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (((l.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T.Fr) *
      (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P)) := by
  letI := io.toAlgebra
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [(htp b).1]; exact GlobalTheory.ShortBound.levPt_killed Xo _ _
  obtain ⟨t1, t2⟩ := GlobalTheory.TorsFac.factorisation E H Dw l Xo N ℓ hL.1 hL.2.1 hℓ
  have key : ∃ u : ℕ, u ∣ l.M ∧ ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w (u : 𝓞 E) *
      (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
    by_cases hd : ℓ ∣ l.M
    · have hA : (ℓ : 𝓞 E) * H.bar (ℓ : 𝓞 E) = ((ℓ ^ 2 : ℕ) : 𝓞 E) := by rw [map_natCast]; push_cast; ring
      obtain ⟨n', Bn, j, β₀, h1, h2, h3, h4, h5⟩ := t2 (ℓ : 𝓞 E) (ℓ ^ 2) hA hsq (Or.inr ⟨rfl, hd⟩)
      exact ⟨ℓ, hd, sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP z tp F
        hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF htr n' (ℓ ^ 2) Bn j _ β₀ h1 h2 hA h3 h4
        (fun b => (h5 _ _ (hk b) (htp b).2).2)⟩
    · obtain ⟨n', j, h1, h2, h5⟩ := t1 hd
      refine ⟨1, one_dvd _, sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP
        z tp F hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF htr n' 1 (ℓ ^ (2 * j)) (2 * j) _ ((ℓ : 𝓞 E) ^ j) h1
        ?_ (by simp) ?_ (_root_.one_mul _) (fun b => (h5 _ _ (hk b) (htp b).2).2.1)⟩
      · rw [h2]; push_cast; ring
      · rw [map_pow, map_natCast]; push_cast; ring
  obtain ⟨u, ⟨m, hm⟩, h⟩ := key
  rw [GlobalTheory.ShortBound.nrm_nat, map_mul, map_pow, map_natCast, _root_.mul_assoc] at h
  rw [hm, mul_pow, Nat.cast_mul, _root_.mul_comm ((u ^ _ : ℕ) : T.Fr), _root_.mul_assoc, nval_mul, Nat.cast_pow u]
  calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
    _ ≤ _ := add_le_add (nval_natCast_nonneg e _) h

end Point

theorem vV_prod_pow (T : CDVR) (X : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) :
    vV T.V ((∏ p ∈ S, p ^ X : ℕ) : T.Fr) = ∑ p ∈ S, (X : ℤ) * vV T.V (p : T.Fr) := by
  classical
  haveI : CharZero T.Fr := algebraRat.charZero _
  induction S using Finset.induction_on with
  | empty => simp [GlobalTheory.ShortBound.vV_one]
  | insert p S hp ih =>
    have h1 : (p : T.Fr) ≠ 0 := by exact_mod_cast hS p (Finset.mem_insert_self _ _)
    have h2 : ((∏ p ∈ S, p ^ X : ℕ) : T.Fr) ≠ 0 := by
      exact_mod_cast Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ (hS q (Finset.mem_insert_of_mem hq))
    rw [Finset.prod_insert hp, Finset.sum_insert hp, Nat.cast_mul, Nat.cast_pow, vV_mul (pow_ne_zero _ h1) h2,
      GlobalTheory.ShortBound.vV_pow h1, ih fun q hq => hS q (Finset.mem_insert_of_mem hq)]

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ℓ : ℕ}
    (h0 : ℓ ≠ 0) (h : (ℓ : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (ℓ : K) := by
  have h1 : la.valuation K (algebraMap (𝓞 K) K (ℓ : 𝓞 K)) < 1 := (la.valuation_lt_one_iff_mem _).2 h
  rw [map_natCast] at h1
  have h2 : la.valuation K (ℓ : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (by exact_mod_cast h0)
  have := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at this
  unfold vLa
  omega

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions in

theorem exists_smul_nonneg_of_shortRule (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)] (hlev : d.IsLev)
    (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (hroot : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1)
    (hwi : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) (hsf : Squarefree d.l₂.M)
    (Λ : GenLat D.host.E n) (N : ℕ) (hU : Λ.Unimod) (hTM : Λ.TrivAt d.l₂.M) (hN : Λ.LevOK N d.l₂.M)
    (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w) (x0 : Fin n → Dw.La)
    (g : Rul Xo c) (hsec : g ∈ sec Xo c w n) (hR : IsShortRule Xo c d Λ N x0 P g) :
    ∃ t : c.F, t ≠ 0 ∧ ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → Λ.TrivAt ℓ →
      ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (t • g) := by
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  have hM0 : d.l₂.M ≠ 0 := hsf.ne_zero
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  haveI := Nat.finite_of_card_ne_zero hc0
  have hS : ∀ p ∈ D.host.condN.primeFactors, p ≠ 0 := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  obtain ⟨X, hX⟩ : ∃ X : ℕ, X = (NumberField.discr D.host.E).natAbs * Formalism.L2.Pj.DF Dw w := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = ∏ p ∈ D.host.condN.primeFactors, p ^ X := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ (hS q hq)
  refine ⟨betaH (Dw := Dw) c Λ * ((Nat.card (Fin n → LevQ Dw d.l₂) * (Q * d.l₂.M ^ Formalism.L2.Pj.DF Dw w) : ℕ) : c.F),
    mul_ne_zero hβ (by exact_mod_cast mul_ne_zero hc0 (mul_ne_zero hQ0 (pow_ne_zero _ hM0))), ?_⟩
  rintro la ℓ hℓ hmem htr _ ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩
  show 0 ≤ nval Tc.V e (evI yI _)
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot Λ N hU hTM hN w P hP x0 g hsec hR Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have hu : ¬ IsUnit (ℓ : T'.V) := fun hu => by
    have h1 := vV_natCast T' hu
    have h2 := ho'.2 (ℓ : c.F)
    rw [map_natCast, h1] at h2
    have h3 := vLa_pos_of_mem la hℓ.ne_zero hmem
    have h4 : (0 : ℤ) < ((r * e : ℕ) : ℤ) := by exact_mod_cast he'
    exact (mul_pos h4 h3).ne h2
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  have hsq : ¬ ℓ ^ 2 ∣ d.l₂.M := fun hd => hℓ.prime.not_unit (hsf ℓ (by rwa [← pow_two]))
  have key := fun q => class_bound_of_trivAt d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (fun b => levRep (q b)) (htp q) (hF q) htr hsq
  rw [pow_one] at hζ
  rw [← nval_bc iT hr hiT e, evI_smul, map_mul, hval, ← hio, hζ, _root_.one_mul]
  have := Fintype.ofFinite (Fin n → LevQ Dw d.l₂)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
  refine le_nval_sum T' _ _ _ _ fun q _ => ?_
  have hq := key q
  letI := io₂.toAlgebra
  generalize (∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b))
    (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P)) = Sm at hq ⊢
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hc1 : ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) ≠ 0 := by exact_mod_cast hc0
  have hQ1 : (Q : T'.Fr) ≠ 0 := by exact_mod_cast hQ0
  have hQv : 0 ≤ nval T'.V (r * e) ((Q : T'.Fr) * (((d.l₂.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T'.Fr) *
      (io₂ (((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ *
        ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * Sm))) := by
    rw [nval_mul, nval_of_ne hQ1]
    refine le_trans ?_ (add_le_add le_rfl hq)
    rw [← EReal.coe_add, EReal.coe_nonneg, ← sub_eq_add_neg, sub_nonneg, hQ, vV_prod_pow T' X _ hS, Int.cast_sum,
      Finset.sum_div]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : (0 : ℝ) ≤ (vV T'.V (p : T'.Fr) : ℝ) / ((r * e : ℕ) : ℝ) :=
      div_nonneg (by exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p) (Nat.cast_nonneg _)
    have h2 := D.host.vdH_le_natAbs p
    have h3 := D.host.vdH_nonneg p
    have h4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) := Nat.cast_nonneg _
    rw [Int.cast_mul, Int.cast_natCast, mul_div_assoc (X : ℝ), hX, Nat.cast_mul (NumberField.discr D.host.E).natAbs]
    have h5 := mul_nonneg (mul_nonneg h1 h3) h4
    have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h1) h4
    linarith
  refine le_trans (add_nonneg (GlobalTheory.ShortBound.nval_nonneg (V := T'.V) (r * e) (map_isIntegral_int io₂ (hwi x0 q))) hQv)
    (le_of_eq ?_)
  rw [← nval_mul]
  congr 1
  simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
  generalize (io₂ ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree))⁻¹ = a1
  generalize ((Λ.mIdx N (Dw.p + Dw.q) : ℕ) : T'.Fr)⁻¹ = a2
  field_simp

end GlobalTheory.IntCuspLat
