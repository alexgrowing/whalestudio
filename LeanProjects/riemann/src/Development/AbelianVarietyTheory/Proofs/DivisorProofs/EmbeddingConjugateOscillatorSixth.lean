import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormPeriodRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaAtOfIsEtaConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormSqOfMulConjEqDifferentIdeal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.ClassConj

section Local

open Formalism.L2.JoinChr Formalism.L2.Host

variable {D : D7}

theorem unram_eq_prod (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (η : (AE D)ˣ →* Circle) (hη : UnramEverywhere D η) (P : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (es : HeightOneSpectrum (𝓞 D.host.E) → AE D) (xs : HeightOneSpectrum (𝓞 D.host.E) → (AE D)ˣ)
    (hes : ∀ Q ∈ P, IsPlIdem D (es Q) Q ∧ ((xs Q : (AE D)ˣ) : AE D) = locE D (es Q) ((unif Q : D.host.Eˣ) : D.host.E))
    (δ : HeightOneSpectrum (𝓞 D.host.E) → ℤ) (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1)
    (hv : ∀ Q ∈ P, Valued.v (ι (finPart D (x : AE D)) Q) = WithZero.exp (-δ Q))
    (hoff : ∀ Q, Q ∉ P → ι (finPart D (x : AE D)) Q = 1) :
    η x = ∏ Q ∈ P, η (xs Q) ^ δ Q := by
  classical
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  let φ : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (AE D)ˣ →* (WithZero (Multiplicative ℤ))ˣ := fun Q =>
    (Units.map (Valued.v : Valuation (Q.adicCompletion D.host.E) _).toMonoidHom).comp (Units.map (ev Q).toMonoidHom)
  have hφ : ∀ Q (w : (AE D)ˣ), ((φ Q w : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) =
      Valued.v (ι (finPart D (w : AE D)) Q) := fun Q w =>
    show Valued.v (ev Q (w : AE D)) = _ by rw [hev]
  let ψ := Units.map (infPart D).toMonoidHom
  let u : (AE D)ˣ := x * ∏ Q ∈ P, xs Q ^ (-δ Q)
  have hinc : ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (k : D.host.E), ev Q (incA D k) = algebraMap D.host.E _ k := fun Q k => by
    rw [hev]
    exact congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => w Q) (h1 k)
  have hψ : ∀ Q ∈ P, ψ (xs Q) = 1 := fun Q hQ => Units.ext (by
    obtain ⟨a, b⟩ := hes Q hQ
    have p := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι h1 h2 a
    show infPart D ((xs Q : (AE D)ˣ) : AE D) = 1
    rw [b]
    unfold locE
    rw [GlobalTheory.HeckeTensorRead.map_loc (infPart D) (es Q) _, p.1, zero_mul, add_zero])
  have hψx : ψ x = 1 := Units.ext hx
  have hu : ψ u = 1 := by
    simp only [u, map_mul, map_prod, map_zpow, hψx, one_mul]
    exact Finset.prod_eq_one fun Q hQ => by rw [hψ Q hQ, _root_.one_zpow]
  have hφ0 : ∀ Q' ∈ P, ∀ Q, Q ≠ Q' → φ Q (xs Q') = 1 := fun Q' hQ' Q hne => Units.ext (by
    obtain ⟨a, b⟩ := hes Q' hQ'
    have p := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι h1 h2 a
    rw [hφ, ← hev, b]
    unfold locE
    rw [GlobalTheory.HeckeTensorRead.map_loc (ev Q) (es Q') _, hev Q (es Q'), p.2.2 Q hne]
    simp)
  have hφ1 : ∀ Q ∈ P, ((φ Q (xs Q) : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := fun Q hQ => by
    obtain ⟨a, b⟩ := hes Q hQ
    have p := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι h1 h2 a
    rw [hφ, ← hev, b]
    unfold locE
    rw [GlobalTheory.HeckeTensorRead.map_loc (ev Q) (es Q) _, hev Q (es Q), p.2.1, hinc, one_mul, add_sub_cancel]
    exact (GlobalTheory.CharLocProd.val_algebraMap Q _).trans (GlobalTheory.EtaConjLocal.val_unif Q)
  have hφu : ∀ Q, φ Q u = 1 := fun Q => by
    simp only [u, map_mul, map_prod, map_zpow]
    by_cases hQ : Q ∈ P
    · rw [Finset.prod_eq_single_of_mem Q hQ fun Q' h' hne => by rw [hφ0 Q' h' Q hne.symm, _root_.one_zpow]]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hφ1 Q hQ, hφ, hv Q hQ, Units.val_one, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    · rw [Finset.prod_eq_one fun Q' h' => by rw [hφ0 Q' h' Q fun e => hQ (e ▸ h'), _root_.one_zpow], mul_one]
      refine Units.ext ?_
      rw [hφ, hoff Q hQ]
      simp
  have hint : ∀ w : (AE D)ˣ, (∀ Q, φ Q w = 1) → finPart D (w : AE D) ∈ intAE D := fun w hw => (h2 _).2 fun Q => by
    rw [← hφ, hw, Units.val_one]
  have h := hη u (congrArg Units.val hu) (hint u hφu) (hint u⁻¹ fun Q => by rw [map_inv, hφu, inv_one])
  simp only [u, map_mul, map_prod, map_zpow] at h
  rw [mul_eq_one_iff_eq_inv, ← Finset.prod_inv_distrib] at h
  rw [h]
  exact Finset.prod_congr rfl fun Q _ => by rw [_root_.zpow_neg, inv_inv]

theorem absNorm_cP (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (GlobalTheory.IdemSupport.cP Q).asIdeal = Ideal.absNorm Q.asIdeal := by
  have e : (GlobalTheory.IdemSupport.cP Q).asIdeal = Q.asIdeal.map (GlobalTheory.IdemSupport.cO D).toRingHom := by
    ext x
    rw [GlobalTheory.IdemSupport.mem_cP]
    constructor
    · intro h
      have := Ideal.mem_map_of_mem (GlobalTheory.IdemSupport.cO D).toRingHom h
      rwa [show (GlobalTheory.IdemSupport.cO D).toRingHom (GlobalTheory.IdemSupport.cO D x) = x from GlobalTheory.IdemSupport.cO_cO x] at this
    · intro h
      obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_of_equiv (GlobalTheory.IdemSupport.cO D) x).1 h
      rwa [GlobalTheory.IdemSupport.cO_cO]
  rw [e]
  exact GlobalTheory.absNorm_map_ringEquiv_self _ _

theorem absNorm_eq_prod (cc : Ideal (𝓞 D.host.E)) (c0 : cc ≠ ⊥) (δ : HeightOneSpectrum (𝓞 D.host.E) → ℤ)
    (hI : ∀ Q, FractionalIdeal.count D.host.E Q (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = max (δ Q) 0)
    (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hP : ∀ Q ∈ P, GlobalTheory.IdemSupport.cP Q ∉ P)
    (h0 : ∀ Q, Q ∉ P → GlobalTheory.IdemSupport.cP Q ∉ P → δ Q = 0) (hδ : ∀ Q, δ (GlobalTheory.IdemSupport.cP Q) = -δ Q) :
    (Ideal.absNorm cc : ℚ) = ∏ Q ∈ P, (Ideal.absNorm Q.asIdeal : ℚ) ^ (δ Q).natAbs := by
  classical
  have hinj : Function.Injective (GlobalTheory.IdemSupport.cP (D := D)) := Function.Involutive.injective GlobalTheory.ClassScalarValue.cP_cP
  have hne : (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 c0
  have hf := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := D.host.E) hne
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := P ∪ P.image GlobalTheory.IdemSupport.cP)] at hf
  · have h1 := congrArg FractionalIdeal.absNorm hf
    rw [FractionalIdeal.coeIdeal_absNorm, map_prod, Finset.prod_union, Finset.prod_image fun a _ b _ h => hinj h,
      ← Finset.prod_mul_distrib] at h1
    · rw [← h1]
      refine Finset.prod_congr rfl fun Q _ => ?_
      rw [hI, hI, hδ, map_zpow₀, map_zpow₀, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm, absNorm_cP,
        ← zpow_add₀, ← zpow_natCast]
      · congr 1
        omega
      · exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 Q.ne_bot)
    · refine Finset.disjoint_left.2 fun Q h1 h2 => ?_
      obtain ⟨Q', h3, rfl⟩ := Finset.mem_image.1 h2
      exact hP Q' h3 h1
  · intro Q hQ
    by_contra hn
    rw [Finset.mem_coe, Finset.mem_union, not_or] at hn
    refine hQ ?_
    have := h0 Q hn.1 fun h => hn.2 (Finset.mem_image.2 ⟨_, h, GlobalTheory.ClassScalarValue.cP_cP Q⟩)
    simp only [hI, this, max_self, zpow_zero]

theorem pow_factor {a s : ℂ} (hs : s ≠ 0) (ha : a ≠ 0) (d : ℤ) (m : ℕ) (h : 2 * (m : ℤ) = d.natAbs - d) :
    (a * s⁻¹) ^ (-d) * (s * s) ^ m = a ^ (-d) * s ^ d.natAbs := by
  rw [mul_zpow, _root_.inv_zpow', neg_neg, ← pow_two, ← pow_mul, mul_assoc, ← zpow_natCast s (2 * m), ← zpow_add₀ hs,
    ← zpow_natCast s d.natAbs]
  congr 2
  omega

theorem coefficientField_reading_at_embedding_prod {LL : Type} [Field LL] (f : LL →+* ℂ) (c : (AE D)ˣ →* Circle) (x : (AE D)ˣ)
    (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (xs : HeightOneSpectrum (𝓞 D.host.E) → (AE D)ˣ)
    (δ : HeightOneSpectrum (𝓞 D.host.E) → ℤ) (hc : c x = ∏ Q ∈ P, c (xs Q) ^ δ Q) (y : HeightOneSpectrum (𝓞 D.host.E) → LL)
    (hy : ∀ Q ∈ P, f (y Q) = ((c (xs Q) : Circle) : ℂ) * (((Real.sqrt (Ideal.absNorm Q.asIdeal : ℝ))⁻¹ : ℝ) : ℂ))
    (N : ℕ) (hN : (N : ℚ) = ∏ Q ∈ P, (Ideal.absNorm Q.asIdeal : ℚ) ^ (δ Q).natAbs) :
    f (∏ Q ∈ P, y Q ^ (-δ Q) * (Ideal.absNorm Q.asIdeal : LL) ^ ((((δ Q).natAbs : ℤ) - δ Q) / 2).toNat) =
      ((c x : Circle) : ℂ)⁻¹ * ((Real.sqrt (N : ℝ) : ℝ) : ℂ) := by
  have hN' : (N : ℝ) = ∏ Q ∈ P, (Ideal.absNorm Q.asIdeal : ℝ) ^ (δ Q).natAbs := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hN
    simpa using this
  have hsq : Real.sqrt (N : ℝ) = ∏ Q ∈ P, Real.sqrt (Ideal.absNorm Q.asIdeal : ℝ) ^ (δ Q).natAbs := by
    have h0 : 0 ≤ ∏ Q ∈ P, Real.sqrt (Ideal.absNorm Q.asIdeal : ℝ) ^ (δ Q).natAbs :=
      Finset.prod_nonneg fun _ _ => pow_nonneg (Real.sqrt_nonneg _) _
    rw [← Real.sqrt_mul_self h0, ← Finset.prod_mul_distrib, hN']
    congr 1
    refine Finset.prod_congr rfl fun Q _ => ?_
    rw [← mul_pow, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [map_prod, hsq, hc]
  have hcoe : (((∏ Q ∈ P, c (xs Q) ^ δ Q : Circle)) : ℂ)⁻¹ = ∏ Q ∈ P, ((c (xs Q) : Circle) : ℂ) ^ (-δ Q) := by
    rw [← Circle.coe_inv, ← Finset.prod_inv_distrib]
    refine (map_prod Circle.coeHom (fun Q => (c (xs Q) ^ δ Q)⁻¹) P).trans (Finset.prod_congr rfl fun Q _ => ?_)
    show (((c (xs Q) ^ δ Q)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv, Circle.coe_zpow, _root_.zpow_neg]
  rw [hcoe, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun Q hQ => ?_
  have hp : Ideal.absNorm Q.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 Q.ne_bot
  have hs : ((Real.sqrt (Ideal.absNorm Q.asIdeal : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by exact_mod_cast Nat.pos_of_ne_zero hp))
  have hn : ((Ideal.absNorm Q.asIdeal : ℕ) : ℂ) = ((Real.sqrt (Ideal.absNorm Q.asIdeal : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Ideal.absNorm Q.asIdeal : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hm : 2 * (((((δ Q).natAbs : ℤ) - δ Q) / 2).toNat : ℤ) = (δ Q).natAbs - δ Q := by
    omega
  rw [map_mul, map_zpow₀, map_pow, map_natCast, hy Q hQ, hn, Complex.ofReal_inv,
    pow_factor hs (Circle.coe_ne_zero _) _ _ hm, Complex.ofReal_pow]

set_option maxHeartbeats 1600000 in

theorem exists_ideal_conj (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (h : GA D V)
    (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ) (he : Formalism.IndefR.Datum.IsIdemSum e P)
    (hs : SuppAt e V h) (hy : IsDetAt e V h y) (b : ℕ) (hb : ∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal)
    (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q)
    (hr : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1)
    (σ : D.what₂.LL →+* ℂ) (η η' : (AE D)ˣ →* Circle) (hη : UnramEverywhere D η) (hC : IsEtaConj σ η η') :
    ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ cc.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ ∧
      cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧
      Submodule.span (𝓞 D.host.E) (detSet (Bridge.hLat V (FWT.fin V h))) *
        idlE (cc.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) = idlE cc ∧
      ((c y : Circle) : ℂ) = ((χ.onId (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℂˣ) : ℂ) ∧
      ConjVal σ (((η y : Circle) : ℂ)⁻¹ * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ))
        (((η' y : Circle) : ℂ)⁻¹ * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)) ∧ infPart D (y : AE D) = 1 := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, horth⟩ := he
  have e0 : infPart D e = 0 := by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q hQ => (hid _ _ (hes Q hQ)).1
  have e1 : ∀ Q ∈ P, ev Q e = 1 := fun Q hQ => by
    rw [hsum, map_sum, Finset.sum_eq_single Q (fun Q' h' hne => (hid _ _ (hes Q' h')).2.2 Q hne.symm)
      (fun h' => absurd hQ h'), (hid _ _ (hes Q hQ)).2.1]
  have e2 : ∀ Q, Q ∉ P → ev Q e = 0 := fun Q hQ => by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 Q fun hh => hQ (hh ▸ h')
  have hP : ∀ Q ∈ P, GlobalTheory.IdemSupport.cP Q ∉ P := fun Q hQ hQ' => by
    have a := congrArg (ev (GlobalTheory.IdemSupport.cP Q)) horth
    rw [map_mul, e1 _ hQ', one_mul, map_zero] at a
    have a' := hcj e Q
    rw [a, e1 Q hQ, map_zero, map_one] at a'
    exact zero_ne_one a'
  obtain ⟨d, hd⟩ : ∃ d, d = (Formalism.L2.Theta.mt V h).det := ⟨_, rfl⟩
  have d1 : ∀ Q, Q ∉ P → GlobalTheory.IdemSupport.cP Q ∉ P → ev Q d = 1 := fun Q hQ hQ' => by
    rw [hd]
    refine GlobalTheory.ClassScalarValue.det_supp (ev Q) hs ?_
    have a := hcj e (GlobalTheory.IdemSupport.cP Q)
    rw [e2 _ hQ', map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at a
    rw [map_add, e2 Q hQ, a, add_zero]
  have d2 : ∀ Q, Valued.v (ev Q d) * Valued.v (ev (GlobalTheory.IdemSupport.cP Q) d) = 1 := fun Q => by
    rw [← hcj, ← map_mul, ← map_mul, hd, GlobalTheory.ClassScalarValue.det_unitary V hg h, map_one, map_one]
  have d3 : ∀ Q, Valued.v (ev Q d) ≠ 0 := fun Q => left_ne_zero_of_mul_eq_one (d2 Q)
  obtain ⟨δ, hδ⟩ : ∃ δ : HeightOneSpectrum (𝓞 D.host.E) → ℤ, ∀ Q, Valued.v (ev Q d) = WithZero.exp (-δ Q) :=
    ⟨fun Q => -WithZero.log (Valued.v (ev Q d)), fun Q => by rw [neg_neg, WithZero.exp_log (d3 Q)]⟩
  have δ0 : ∀ Q, Q ∉ P → GlobalTheory.IdemSupport.cP Q ∉ P → δ Q = 0 := fun Q hQ hQ' => by
    have a := hδ Q
    rw [d1 Q hQ hQ', map_one, ← WithZero.exp_zero, WithZero.exp_inj] at a
    omega
  have δ1 : ∀ Q, δ (GlobalTheory.IdemSupport.cP Q) = -δ Q := fun Q => by
    have a := d2 Q
    rw [hδ, hδ, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at a
    omega
  have hbc : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∈ (GlobalTheory.IdemSupport.cP Q).asIdeal ↔ (b : 𝓞 D.host.E) ∈ Q.asIdeal :=
    fun Q => by rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
  have hfin : (Function.support δ).Finite := by
    refine (P ∪ P.image GlobalTheory.IdemSupport.cP).finite_toSet.subset fun Q hQ => ?_
    by_contra hn
    rw [Finset.mem_coe, Finset.mem_union, not_or] at hn
    exact hQ (δ0 Q hn.1 fun h => hn.2 (Finset.mem_image.2 ⟨_, h, GlobalTheory.ClassScalarValue.cP_cP Q⟩))
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.T.exists_numeratorIdeal_of_antiInvariant_divisor D.host.E (GlobalTheory.IdemSupport.cO D) GlobalTheory.IdemSupport.cP GlobalTheory.IdemSupport.cO_cO GlobalTheory.IdemSupport.mem_cP δ hfin δ1
  have hy' : (y : AE D) = e * d + (1 - e) := hd ▸ hy
  have y0 : infPart D (y : AE D) = 1 := by
    rw [hy', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, e0, RingHom.map_one, zero_mul, zero_add, sub_zero]
  have y1 : ∀ Q ∈ P, Valued.v (ι (finPart D (y : AE D)) Q) = WithZero.exp (-δ Q) := fun Q hQ => by
    rw [← hev, ← hδ, hy', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, e1 Q hQ, RingHom.map_one, one_mul, sub_self,
      add_zero]
  have y2 : ∀ Q, Q ∉ P → ι (finPart D (y : AE D)) Q = 1 := fun Q hQ => by
    rw [← hev, hy', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, e2 Q hQ, RingHom.map_one, zero_mul, zero_add,
      sub_zero]
  refine ⟨cc, c0, c1, c3 _ fun Q hQ hm => ?_, c4 _ fun x => ?_, ?_, ?_, y0⟩
  · exact hQ (δ0 Q (fun h' => hb Q h' hm) fun h' => hb _ h' ((hbc Q).2 hm))
  · rw [GlobalTheory.T.mem_span_detSet_iff_adelicLattice_valuation D.host.E _ _ _ (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL (FWT.fin V h)) x]
    refine forall_congr' fun Q => ?_
    rw [← hδ, hev, hd]
    have a : ι (finPart D (Formalism.L2.Theta.mt V h).det) =
        (Matrix.GeneralLinearGroup.map ι.toRingHom (FWT.fin V h).1).1.det :=
      RingHom.map_det (ι.toRingHom.comp (finPart D)) _
    rw [a]
  · have hv : ∀ (k : D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)),
        (GlobalTheory.IdemSupport.cP Q).valuation D.host.E (star k) = Q.valuation D.host.E k := fun k Q => by
      have a : ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (k : D.host.E),
          Valued.v (ev Q (incA D k)) = Q.valuation D.host.E k := fun Q k => by
        rw [hev]
        exact (congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => Valued.v (w Q)) (h1 k)).trans
          (GlobalTheory.CharLocProd.val_algebraMap Q k)
      rw [← a, ← a Q, ← hcj _ Q, GlobalTheory.IdemSupport.cA_incA]
    rw [GlobalTheory.ClassScalarValue.onId_eq χ _ δ c2 P hP δ0 δ1 fun Q hQ => GlobalTheory.ClassScalarValue.val_mul_val hv χ (fun a => hP Q hQ (a.symm ▸ hQ))
      (hr Q fun a => hP Q hQ (a.symm ▸ hQ)) (hu Q (hb Q hQ)) (hu _ fun a => hb Q hQ ((hbc Q).1 a))]
    exact GlobalTheory.T.idelicCharacter_eq_prod_unramifiedValue_zpow D ι h1 h2 h4 c χ hc y y0 P δ (fun Q hQ => ⟨hu Q (hb Q hQ), y1 Q hQ⟩) y2
  · obtain ⟨es', hes'⟩ : ∃ es' : HeightOneSpectrum (𝓞 D.host.E) → AE D, ∀ Q, IsPlIdem D (es' Q) Q :=
      ⟨fun Q => (h4 Q).choose, fun Q => (h4 Q).choose_spec.1⟩
    let xs : HeightOneSpectrum (𝓞 D.host.E) → (AE D)ˣ := fun Q => locU (hes' Q).1 (unif Q)
    have hxs : ∀ Q ∈ P, IsPlIdem D (es' Q) Q ∧ ((xs Q : (AE D)ˣ) : AE D) = locE D (es' Q) ((unif Q : D.host.Eˣ) : D.host.E) :=
      fun Q _ => ⟨hes' Q, rfl⟩
    have hcard : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Nat.card (kP Q) = Ideal.absNorm Q.asIdeal := fun Q => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hconj : ∀ Q, ConjVal σ (((η (xs Q) : Circle) : ℂ) * (((Real.sqrt (Ideal.absNorm Q.asIdeal : ℝ))⁻¹ : ℝ) : ℂ))
        (((η' (xs Q) : Circle) : ℂ) * (((Real.sqrt (Ideal.absNorm Q.asIdeal : ℝ))⁻¹ : ℝ) : ℂ)) := fun Q => by
      have := hC.2.2 Q (es' Q) (hes' Q) (xs Q) rfl
      rwa [hcard] at this
    choose yq hy1 hy2 using hconj
    have hN := absNorm_eq_prod cc c0 δ c2 P hP δ0 δ1
    exact ⟨_, coefficientField_reading_at_embedding_prod D.what₂.embLL η y P xs δ (unram_eq_prod ι h1 h2 η hη P es' xs hxs δ y y0 y1 y2) yq (fun Q _ => hy1 Q) _ hN,
      coefficientField_reading_at_embedding_prod σ η' y P xs δ (unram_eq_prod ι h1 h2 η' hC.2.1 P es' xs hxs δ y y0 y1 y2) yq (fun Q _ => hy2 Q) _ hN⟩

end Local

end GlobalTheory.GalOne.ClassConj
