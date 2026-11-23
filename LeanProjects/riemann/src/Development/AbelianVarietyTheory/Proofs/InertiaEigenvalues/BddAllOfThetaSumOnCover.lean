import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtensionIntegralFramedPointLiftCove
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShortThetaValueBoundedGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPointsStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

namespace GlobalTheory.CoverBound

theorem inV_iff (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0
    simp [InV, vV]
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV
    omega
  · intro h3
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log (valV_ne_zero h0) one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h3
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_map_iff {T T' : CDVR} (i : T.Fr →+* T'.Fr) {r : ℕ} (hr : 0 < r)
    (hi : ∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) (x : T.Fr) : InV T' (i x) ↔ InV T x := by
  rw [inV_iff, inV_iff, hi]
  exact mul_nonneg_iff_of_pos_left (by exact_mod_cast hr)

theorem inV_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {x : K} (hx : la.valuation K x ≤ 1) : InV T (io x) := by
  rw [inV_iff, ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : x = 0
  · simp [vLa, h0]
  have h2 := (WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 hx
  rw [WithZero.log_one] at h2
  unfold vLa
  omega

theorem inV_of_pow_eq (T : CDVR) {x : T.Fr} {e : ℕ} (he : 0 < e) (hx : x ^ (e + 1) = x) : InV T x := by
  by_cases h0 : x = 0
  · subst h0
    exact zero_mem (algebraMap T.V T.Fr).range
  have h := GlobalTheory.PlaceExtField.vV_pow (V := T.V) h0 (e + 1)
  rw [hx] at h
  rw [inV_iff]
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  push_cast at h
  have : (e : ℤ) * vV T.V x = 0 := by linarith
  exact ((mul_eq_zero.1 this).resolve_left he'.ne').ge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem good_lift {X X₂ : Scheme.{0}} (t : SAB H X) (t₂ : SAB H X₂) (r : X₂ ⟶ X) (m : SABMap t₂ t r) (T T' : CDVR)
    (i : T.Fr →+* T'.Fr) (e : ℕ) (hi : ∀ a : T.Fr, vV T'.V (i a) = (e : ℤ) * vV T.V a) (x : Sp T.Fr ⟶ X)
    (x₂ : Sp T'.Fr ⟶ X₂) (hx : x₂ ≫ r = spMap i ≫ x)
    (h : ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' t x)
      (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), IsProper G.G.hom) :
    ∃ (G : SAB H (Sp T'.V)) (t' : SAB H (Sp T'.Fr)) (_ : SABMap t' t₂ x₂)
      (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), IsProper G.G.hom := by
  obtain ⟨G, t', m1, m2, hp⟩ := h
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceInt.Ext.exists_restrict T T' i e hi
  obtain ⟨G', ⟨mG⟩⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap φ)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap φ) G⟩⟩
  obtain ⟨s, ⟨n⟩⟩ : ∃ s : SAB H (Sp T'.Fr), Nonempty (SABMap s t' (spMap i)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap i) t'⟩⟩
  have hio : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← GlobalTheory.FramedBaseChange.spec_comp, ← GlobalTheory.FramedBaseChange.spec_comp]
    exact congrArg spMap (RingHom.ext fun a => (hφ a).symm)
  obtain ⟨a1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 n
  obtain ⟨a2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 n
  rw [← hx] at a1
  rw [hio] at a2
  obtain ⟨b1, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m a1
  obtain ⟨b2, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG a2
  exact ⟨G', s, b1, b2, MorphismProperty.of_isPullback mG.cart.1 hp⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem shortValAt_of_map (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (La : GenLat E n) (β : c.F)
    (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {K k : Type} [Field K] [Field k] [Algebra c.F K] [Algebra c.F k]
    (ψ : K →ₐ[c.F] k) (y : FrPt Xo c K) (z : FrPt Xo c k) (h : FrMap ψ y z) (v : K)
    (hv : ShortValAt Xo c nab w La β N P z (ψ v)) : ShortValAt Xo c nab w La β N P y v := by
  obtain ⟨S, _, _, φ, y', a, b, F, hf, hm, h1, h2, h3, h4, h5⟩ := hv
  refine ⟨S, inferInstance, inferInstance, φ.comp ψ, y', a, b, F, ?_, GlobalTheory.FramedBaseChange.trans ψ φ h hm,
    h1, h2, h3, h4, h5⟩
  haveI : Nontrivial S := hf.injective.nontrivial
  letI := (φ.comp ψ).toRingHom.toAlgebra
  exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

theorem evR_pow_succ (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (e : ℕ) :
    evR Xo c (f ^ (e + 1)) y = evR Xo c f y ^ (e + 1) := by
  induction e with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ e ih => rw [pow_succ f, pow_succ (evR Xo c f y), ← ih]; exact evalAt_mul _ _ _ _ _

set_option maxHeartbeats 1000000 in

theorem bddAll_of_theta_sum_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n d N m : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (cs : Fin m → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : Fin m → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Dom a n → dδ.IsLev → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t q, la.valuation c.F (w t q) ≤ 1) → (∀ t, P t ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ∧ (P t).IsHomogeneous d ∧ ∀ k, la.valuation c.F ((P t).coeff k) ≤ 1) → f ∈ cusp Xo c U a n → (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : Fin m → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → BddAll Xo c la (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw dδ.l₂) : ℕ) : c.F) * ((2 * NumberField.discr E * N : ℤ) : c.F) ^ d) f := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hl _ a n d N m dδ La cs e w P f hdom hlev hnab hun htr hN he hcs hw hP hf
    hval
  refine GlobalTheory.T.cuspFormBound_goodPoints_extends_allPoints E H Dw l Xo c r U hU la p hp hpl hl a n f _ hdom hf ?_
  intro T io e₀ ho y hfin hgood
  have laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨T₁, i₁, e₁, y₁, io₁, z₁, ⟨he₁, hv₁, φ₁, hφ₁, hm₁⟩, -, hio₁, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover E H Dw l Xo c n dδ hlev T io y hfin
  letI a0 : Algebra c.F T.Fr := io.toAlgebra
  letI a1 : Algebra c.F T₁.Fr := (i₁.comp io).toAlgebra
  letI b1 : Algebra dδ.c₂.F T₁.Fr := io₁.toAlgebra
  obtain ⟨k, _, _, _, _, -⟩ : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra T₁.Fr k)
      (_ : Algebra.IsAlgebraic T₁.Fr k), True :=
    ⟨AlgebraicClosure T₁.Fr, inferInstance, inferInstance, inferInstance, inferInstance, trivial⟩
  letI ak : Algebra c.F k := ((algebraMap T₁.Fr k).comp (i₁.comp io)).toAlgebra
  letI bk : Algebra dδ.c₂.F k := ((algebraMap T₁.Fr k).comp io₁).toAlgebra
  let ψ₁ : T₁.Fr →ₐ[c.F] k := { algebraMap T₁.Fr k with commutes' := fun _ => rfl }
  let ψ₂ : T₁.Fr →ₐ[dδ.c₂.F] k := { algebraMap T₁.Fr k with commutes' := fun _ => rfl }
  obtain ⟨yk, hyk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw l Xo c _ _ ψ₁ y₁.1
  obtain ⟨zk, hzk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ _ _ ψ₂ z₁.1
  have hc1 : ∀ x : c.F, algebraMap dδ.c₂.F T₁.Fr (dδ.eF x) = algebraMap c.F T₁.Fr x := hio₁
  have hck : ∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x := fun x =>
    congrArg (algebraMap T₁.Fr k) (hio₁ x)
  have hoverk : FrOver dδ zk yk :=
    (GlobalTheory.frames_lift_to_cover laws E H Dw l Xo c n dδ).2.1 T₁.Fr hc1 k hck ψ₁ ψ₂ rfl y₁.1 z₁.1 yk zk hover hyk hzk
  obtain ⟨v, hv, hev⟩ := hval k hck yk zk hoverk
  let K := IntermediateField.adjoin T₁.Fr (Set.range v)
  haveI : FiniteDimensional T₁.Fr K := IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T₂, i₂, e₂, ρ, -, he₂, hv₂, hρ, -, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T₁ K
  obtain ⟨z₂, -, -, φ₂, hφ₂, hm₂⟩ :=
    (GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ T₁ T₂ io₁ z₁ i₂ e₂ he₂ hv₂).1
  letI b2 : Algebra dδ.c₂.F T₂.Fr := (i₂.comp io₁).toAlgebra
  obtain ⟨j, hj, hjv⟩ : ∃ j : T₂.Fr →+* k, (∀ x, j (i₂ x) = algebraMap T₁.Fr k x) ∧ ∀ t, ∃ u, j u = v t := by
    refine ⟨(algebraMap K k).comp ρ.symm.toRingHom, fun x => ?_, fun t =>
      ⟨ρ ⟨v t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩, ?_⟩⟩
    · rw [← hρ]
      exact congrArg (algebraMap K k) (ρ.symm_apply_apply _)
    · exact congrArg (algebraMap K k) (ρ.symm_apply_apply _)
  choose u hu using hjv
  let χ : T₂.Fr →ₐ[dδ.c₂.F] k := { j with commutes' := fun x => hj (io₁ x) }
  have hχ : χ.comp φ₂ = ψ₂ := AlgHom.ext fun x => by
    show j (φ₂.toRingHom x) = algebraMap T₁.Fr k x
    rw [hφ₂, hj]
  have hm₃ : FrMap χ z₂.1 zk := GlobalTheory.FramedBaseChange.cancel φ₂ χ hm₂ (hχ ▸ hzk)
  have hv₀ : ∀ x : T.Fr, vV T₂.V ((i₂.comp i₁) x) = ((e₂ * e₁ : ℕ) : ℤ) * vV T.V x := fun x => by
    rw [RingHom.comp_apply, hv₂, hv₁]
    push_cast
    ring
  have he₀ : 0 < e₂ * e₁ := Nat.mul_pos he₂ he₁
  have hgood₂ : Good z₂ := by
    refine good_lift Xo.univ.t dδ.Xo₂.univ.t dδ.r dδ.m T T₂ (i₂.comp i₁) _ hv₀ y.1.x z₂.1.x ?_ hgood
    rw [hm₂.1, Category.assoc, hover.1, hm₁.1, hφ₁, hφ₂, ← Category.assoc, ← GlobalTheory.FramedBaseChange.spec_comp]
  have hint : ∀ x : c.F, la.valuation c.F x ≤ 1 → InV T₂ ((i₂.comp io₁) (dδ.eF x)) := fun x hx => by
    rw [RingHom.comp_apply, hio₁]
    exact (inV_map_iff (i₂.comp i₁) he₀ hv₀ _).2 (inV_of_overLa ho hx)
  have hth := fun t => GlobalTheory.T.shortThetaValue_bounded_goodReduction E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ dδ.nab₂ hnab T₂ (i₂.comp io₁) z₂ n d N La
    (fun q => dδ.eF (w t q)) (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) (u t) hgood₂ hun htr hN
    (fun q => hint _ (hw t q)) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map _ (hP t).1) ((hP t).2.1.map _)
    (fun q => by rw [coeff_map]; exact hint _ ((hP t).2.2 q))
    (shortValAt_of_map _ _ _ _ _ _ χ z₂.1 zk hm₃ (u t) (by
      have h := hv t
      rw [← hu t] at h
      exact h))
  have e1 : evR Xo c f yk = (ψ₁.comp φ₁) (evR Xo c f y.1) :=
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw l Xo c).2.2.1 f
      (cusp_le_sec Xo c U a n hf).1 _ y.1 y.2.1 yk (GlobalTheory.FramedBaseChange.trans φ₁ ψ₁ hm₁ hyk)
  have e2 : ∀ t, evR dδ.Xo₂ dδ.c₂ (cs t) zk = j (evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1) := fun t =>
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂).2.2.1 (cs t) (hcs t).1.1 χ z₂.1
      z₂.2.1 zk hm₃
  have e3 : (i₂.comp i₁) (evI y f) = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1 * u t := by
    apply j.injective
    have e4 : j ((i₂.comp i₁) (evI y f)) = (ψ₁.comp φ₁) (evR Xo c f y.1) := by
      show j (i₂ (i₁ (evR Xo c f y.1))) = algebraMap T₁.Fr k (φ₁.toRingHom (evR Xo c f y.1))
      rw [hφ₁, hj]
    rw [e4, ← e1, hev, map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [map_mul, e2, hu]
  rw [← inV_map_iff (i₂.comp i₁) he₀ hv₀, map_mul, e3, Finset.mul_sum]
  refine sum_mem (S := (algebraMap T₂.V T₂.Fr).range) fun t _ => ?_
  have h1 : InV T₂ (evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1) :=
    inV_of_pow_eq T₂ he (by rw [← evR_pow_succ, (hcs t).2])
  have h2 := mul_mem h1 (hth t)
  rw [map_mul, map_natCast, map_pow, map_intCast, map_mul, map_natCast, map_pow, map_intCast, mul_left_comm]
  exact h2

end GlobalTheory.CoverBound
