import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSphericalUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselian
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT
open Matrix

namespace GlobalTheory.BCT.UnitStable

section Ring

variable {O : Type} [CommRing O] {n : ℕ}

open GlobalTheory.ClassParam in

theorem exists_cyclic [IsLocalRing O] (M : Matrix (Fin n) (Fin n) O) (hs : M.charpoly.Separable) :
    ∃ v, IsUnit (krylov M v) := by
  haveI : Subsingleton (MaximalSpectrum O) := ⟨fun a b =>
    MaximalSpectrum.ext ((IsLocalRing.eq_maximalIdeal a.isMaximal).trans
      (IsLocalRing.eq_maximalIdeal b.isMaximal).symm)⟩
  obtain ⟨w, hw⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField _ (Fin n) M hs
  let σ : Equiv.Perm (Fin n) := (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))
  have hk : GlobalTheory.RegSS.krylov M w = (krylov M w).submatrix id σ := by
    ext i j
    simp [GlobalTheory.RegSS.krylov, krylov, σ]
  rw [hk, Matrix.det_permute'] at hw
  exact ⟨w, (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hw)⟩

theorem conj_of_charpoly [IsLocalRing O] (a b : GL (Fin n) O) (hs : a.val.charpoly.Separable)
    (h : b.val.charpoly = a.val.charpoly) : ∃ g, b = g⁻¹ * a * g := by
  obtain ⟨v, ka, hka⟩ := exists_cyclic a.val hs
  obtain ⟨u, kb, hkb⟩ := exists_cyclic b.val (h ▸ hs)
  have h1 := GlobalTheory.Orb.mul_krylov_eq a.val v
  have h2 := GlobalTheory.Orb.mul_krylov_eq b.val u
  rw [← hka] at h1
  rw [← hkb, h] at h2
  have h3 : ka⁻¹ * a * ka = kb⁻¹ * b * kb := by
    apply Units.ext
    simp only [Units.val_mul, mul_assoc, h1, h2, Units.inv_mul_cancel_left]
  refine ⟨ka * kb⁻¹, ?_⟩
  calc b = kb * (kb⁻¹ * b * kb) * kb⁻¹ := by group
    _ = _ := by rw [← h3]; group

open GlobalTheory.ClassParam in

theorem commute_of_commute [IsLocalRing O] (M s t : Matrix (Fin n) (Fin n) O) (hs : M.charpoly.Separable)
    (h1 : Commute M s) (h2 : Commute M t) : Commute s t := by
  obtain ⟨v, k, hk⟩ := exists_cyclic M hs
  have key : ∀ r : Matrix (Fin n) (Fin n) O, Commute M r → r * krylov M v = krylov M (r *ᵥ v) := by
    intro r hr
    ext i j
    have : (r * krylov M v) i j = (r *ᵥ ((M ^ (j : ℕ)) *ᵥ v)) i := rfl
    rw [this, mulVec_mulVec, ← (hr.pow_left j).eq, ← mulVec_mulVec]
    rfl
  let x := (k⁻¹).val *ᵥ (s *ᵥ v)
  let p : Matrix (Fin n) (Fin n) O := ∑ j : Fin n, x j • M ^ (j : ℕ)
  have hp : ∀ r, Commute M r → Commute p r := fun r hr =>
    Commute.sum_left _ _ _ fun j _ => (hr.pow_left j).smul_left _
  have hpv : p *ᵥ v = s *ᵥ v := by
    have e1 : p *ᵥ v = krylov M v *ᵥ x := by
      ext i
      simp only [p, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change _ = ∑ j : Fin n, _
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e1, ← hk, mulVec_mulVec, Units.mul_inv, one_mulVec]
  have : s * k.val = p * k.val := by rw [hk, key s h1, key p (hp M (Commute.refl M)).symm, hpv]
  rw [(Units.mul_left_inj k).1 this]
  exact hp t h2

def adjt (c : O →+* O) (b : Matrix (Fin n) (Fin n) O) : Matrix (Fin n) (Fin n) O :=
  GlobalTheory.Tw.Phi n O * (b.map c)ᵀ * (GlobalTheory.Tw.Phi n O)ᵀ

theorem adjt_mul (c : O →+* O) (a b : Matrix (Fin n) (Fin n) O) : adjt c (a * b) = adjt c b * adjt c a := by
  have h : (GlobalTheory.Tw.Phi n O)ᵀ * GlobalTheory.Tw.Phi n O = 1 := mul_eq_one_comm.1 (Phi_mul_transpose n O)
  simp only [adjt, Matrix.map_mul, transpose_mul, mul_assoc]
  rw [← mul_assoc (GlobalTheory.Tw.Phi n O)ᵀ, h, one_mul]

theorem adjt_add (c : O →+* O) (a b : Matrix (Fin n) (Fin n) O) : adjt c (a + b) = adjt c a + adjt c b := by
  simp only [adjt, Matrix.map_add _ (map_add c), transpose_add, mul_add, add_mul]

theorem adjt_smul (c : O →+* O) (r : O) (b : Matrix (Fin n) (Fin n) O) : adjt c (r • b) = c r • adjt c b := by
  ext i j
  simp only [adjt, GlobalTheory.ThetaPull.phi_mul_apply, transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  ring

theorem adjt_one (c : O →+* O) : adjt c (1 : Matrix (Fin n) (Fin n) O) = 1 := by
  rw [adjt, Matrix.map_one _ (map_zero c) (map_one c), transpose_one, mul_one, Phi_mul_transpose]

theorem adjt_adjt (c : O →+* O) (hc : ∀ x, c (c x) = x) (b : Matrix (Fin n) (Fin n) O) : adjt c (adjt c b) = b := by
  ext i j
  simp only [adjt, GlobalTheory.ThetaPull.phi_mul_apply, transpose_apply, map_apply, map_mul, map_pow, map_neg, map_one, hc,
    Fin.rev_rev]
  rw [← mul_assoc, GlobalTheory.ThetaPull.sign_rev, one_mul]

theorem adjt_val (c : O →+* O) (g : GL (Fin n) O) : adjt c g.val = (thetaGL n c g⁻¹).val := rfl

theorem twConj_of_norm_eq [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (O ⧸ IsLocalRing.maximalIdeal O)] (c : O →+* O) (hc : ∀ x, c (c x) = x)
    (hm : ∀ x ∈ IsLocalRing.maximalIdeal O, c x ∈ IsLocalRing.maximalIdeal O) (hω : ∃ ω, IsUnit (ω - c ω))
    (y z : GL (Fin n) O) (hs : (y * thetaGL n c y).val.charpoly.Separable)
    (h : z * thetaGL n c z = y * thetaGL n c y) : ∃ g, z = g⁻¹ * y * thetaGL n c g := by
  have hθ := GlobalTheory.ThetaPull.thetaGL_thetaGL (a := n) c hc
  set θ := thetaGL n c with hθdef
  have h' : θ z * z = θ y * y := by simpa only [map_mul, hθ] using congrArg θ h
  set N := y * θ y with hN
  let S := Subalgebra.centralizer O {N.val}
  have hS : ∀ b, b ∈ S ↔ Commute N.val b := fun b => by
    simp [S, Subalgebra.mem_centralizer_iff, Commute, SemiconjBy]
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun s t => Subtype.ext (commute_of_commute N.val s.1 t.1 hs ((hS _).1 s.2) ((hS _).1 t.2)).eq }
  let st : Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) O := fun b => y.val * adjt c b * (y⁻¹).val
  have st_mul : ∀ a b, st (a * b) = st b * st a := fun a b => by
    simp only [st, adjt_mul, mul_assoc, Units.inv_mul_cancel_left]
  have st_val : ∀ g : GL (Fin n) O, st g.val = (y * θ g⁻¹ * y⁻¹).val := fun g => rfl
  have st_N : st N.val = (N⁻¹).val := by
    rw [st_val]
    congr 1
    simp only [hN, map_inv, map_mul, hθ]
    group
  have st_mem : ∀ b ∈ S, st b ∈ S := fun b hb => by
    rw [hS] at hb ⊢
    have := congrArg st hb.eq
    rw [st_mul, st_mul, st_N] at this
    exact Commute.units_inv_left_iff.1 this.symm
  have st_st : ∀ b ∈ S, st (st b) = b := fun b hb => by
    rw [hS] at hb
    have e : st (st b) = N.val * b * (N⁻¹).val := by
      simp only [st, adjt_mul, adjt_adjt c hc, adjt_val, ← hθdef, hN, inv_inv, _root_.mul_inv_rev, map_inv, Units.val_mul,
        mul_assoc]
    rw [e, hb.eq, Units.mul_inv_cancel_right]
  let σ : S →+* S :=
    { toFun := fun b => ⟨st b.1, st_mem _ b.2⟩
      map_one' := Subtype.ext (by simp [st, adjt_one])
      map_mul' := fun a b => by rw [mul_comm a b]; exact Subtype.ext (st_mul _ _)
      map_zero' := Subtype.ext (by simp [st, adjt])
      map_add' := fun a b => Subtype.ext (by simp [st, adjt_add, mul_add, add_mul]) }
  have hσ : ∀ r : O, σ (algebraMap O S r) = algebraMap O S (c r) := fun r => Subtype.ext (by
    change st (algebraMap O _ r) = algebraMap O _ (c r)
    simp [st, Algebra.algebraMap_eq_smul_one, adjt_smul, adjt_one])
  haveI : Module.Finite O S := Module.Finite.of_injective S.val.toLinearMap Subtype.val_injective
  haveI := GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal O) S
  haveI := GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal O) S
  have ha : Commute N (z * y⁻¹) := by
    show N * (z * y⁻¹) = z * y⁻¹ * N
    calc N * (z * y⁻¹) = z * (θ z * z) * y⁻¹ := by rw [← h]; group
      _ = _ := by rw [h', hN]; group
  have ha1 : (z * y⁻¹).val ∈ S := (hS _).2 (Commute.units_val ha)
  have ha2 : (z * y⁻¹)⁻¹.val ∈ S := (hS _).2 (Commute.units_val ha.inv_right)
  obtain ⟨ω, hω⟩ := hω
  obtain ⟨x, hx⟩ := GlobalTheory.HenselianNorm.exists_norm_eq S ((IsLocalRing.maximalIdeal O).map (algebraMap O S)) σ
    (fun b => Subtype.ext (st_st _ b.2))
    (fun x hx => by
      have : (IsLocalRing.maximalIdeal O).map (algebraMap O S) ≤
          ((IsLocalRing.maximalIdeal O).map (algebraMap O S)).comap σ := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, Ideal.mem_comap, hσ]
        exact Ideal.mem_map_of_mem _ (hm a ha)
      exact this hx)
    ⟨algebraMap O _ ω, by rw [hσ, ← map_sub]; exact hω.map _⟩ ⟨_, ha1⟩
    (Subtype.ext (by
      change st (z * y⁻¹).val = (z * y⁻¹).val
      rw [st_val]
      congr 1
      calc y * θ (z * y⁻¹)⁻¹ * y⁻¹ = N * (θ z)⁻¹ * y⁻¹ := by simp only [hN, map_inv, map_mul]; group
        _ = _ := by rw [← h]; group))
    ⟨⟨⟨_, ha1⟩, ⟨_, ha2⟩, Subtype.ext (Units.mul_inv (z * y⁻¹)), Subtype.ext (Units.inv_mul (z * y⁻¹))⟩, rfl⟩
  have hx' : x.1 * st x.1 = (z * y⁻¹).val := congrArg Subtype.val hx
  have hu : IsUnit x.1 := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := (Matrix.isUnit_iff_isUnit_det _).1 (hx' ▸ (z * y⁻¹).isUnit)
    rw [det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨g, hg⟩ := hu
  rw [← hg, st_val, ← Units.val_mul, Units.val_inj] at hx'
  refine ⟨g⁻¹, ?_⟩
  calc z = z * y⁻¹ * y := by group
    _ = _ := by rw [← hx']; group

end Ring

section Group

variable {G : Type} [Group G]

theorem exists_rep (θ : G →* G) (y : G) : ∃ g, TwCl.rep (θ := θ) (Quot.mk _ y) = g⁻¹ * y * θ g := by
  have he : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g :=
    ⟨fun x => ⟨1, by simp⟩, fun ⟨g, h⟩ => ⟨g⁻¹, by rw [h, map_inv]; group⟩,
      fun ⟨g, h⟩ ⟨k, h'⟩ => ⟨g * k, by rw [h', h, map_mul]; group⟩⟩
  exact he.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ y)).symm)

theorem clSum_eq_one [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (f : G → ℂ)
    (hS : ∀ g, ∀ y ∈ S, g⁻¹ * y * θ g ∈ S)
    (hf : ∀ y ∈ S, twOrb θ K y f = if ∃ g, g⁻¹ * y * θ g ∈ K then 1 else 0)
    (hex : ∃ y ∈ S, y ∈ K) (hun : ∀ y ∈ S, ∀ z ∈ S, y ∈ K → z ∈ K → ∃ g, z = g⁻¹ * y * θ g) :
    clSum θ K S 1 f = 1 := by
  obtain ⟨y, hyS, hyK⟩ := hex
  obtain ⟨g, hg⟩ := exists_rep θ y
  rw [clSum, finsum_eq_single (α := TwCl θ) _ (Quot.mk _ y)]
  · have h1 := hS g y hyS
    rw [hg, if_pos h1, hf _ h1, if_pos ⟨g⁻¹, by
      have : g⁻¹⁻¹ * (g⁻¹ * y * θ g) * θ g⁻¹ = y := by rw [map_inv]; group
      rwa [this]⟩]
    simp
  · intro c hc
    split_ifs with h1
    · rw [hf _ h1, if_neg, mul_zero]
      rintro ⟨k, hk⟩
      obtain ⟨l, hl⟩ := hun _ (hS k _ h1) y hyS hk hyK
      apply hc
      rw [← Quot.out_eq c]
      exact Quot.sound ⟨k * l, by rw [hl, map_mul]; simp only [TwCl.rep]; group⟩
    · rfl

end Group

variable {E : Type} [Field E] [NumberField E]

theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

theorem eventually_lift (p : E[X]) : ∀ᶠ w : Pl E in cofinite, ∃ q : (w.adicCompletionIntegers E)[X],
    q.map (algebraMap _ (w.adicCompletion E)) = atPl w p := by
  have h : ∀ᶠ w : Pl E in cofinite, ∀ i ∈ p.support,
      algebraMap E (w.adicCompletion E) (p.coeff i) ∈ w.adicCompletionIntegers E := by
    rw [eventually_all_finset]
    exact fun i _ => eventually_int _
  filter_upwards [h] with w hw
  refine (Polynomial.mem_lifts _).1 ((Polynomial.lifts_iff_coeff_lifts _).2 fun i => ?_)
  rw [coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hw i hi⟩, rfl⟩
  · rw [notMem_support_iff.1 hi, map_zero]
    exact ⟨0, map_zero _⟩

theorem eventually_separable (P : E[X]) (hP : P.Separable) : ∀ᶠ w : Pl E in cofinite,
    ∀ q : (w.adicCompletionIntegers E)[X], q.map (algebraMap _ (w.adicCompletion E)) = atPl w P → q.Separable := by
  obtain ⟨u, v, huv⟩ := hP
  filter_upwards [eventually_lift u, eventually_lift v] with w ⟨u', hu⟩ ⟨v', hv⟩ q hq
  refine ⟨u', v', Polynomial.map_injective (algebraMap _ (w.adicCompletion E)) Subtype.val_injective ?_⟩
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, hq, hu, hv,
    Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, huv,
    Polynomial.map_one, Polynomial.map_one]

theorem mem_int {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KGL {n : ℕ} (g : GL (Fin n) E) : ∀ᶠ w : Pl E in cofinite,
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) g ∈ GlobalTheory.LFun.KGL w n := by
  have h : ∀ g : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]; exact fun i j => eventually_int _
  filter_upwards [h g, h g⁻¹] with w a b
  exact mem_int _ _ a (by rw [← map_inv]; exact b)

variable [IsCMField E]

theorem exists_isSection : ∃ S : Set (Pl E), IsSection S := by
  let f : Pl E → HeightOneSpectrum (𝓞 (maximalRealSubfield E)) := fun w => w.under _
  let s : Setoid (Pl E) := Setoid.ker f
  refine ⟨Set.range fun q : Quotient s => q.out, fun w => ⟨(Quotient.mk s w).out, ⟨⟨_, rfl⟩, Quotient.mk_out (s := s) w⟩, ?_⟩⟩
  rintro _ ⟨⟨u, rfl⟩, hu⟩
  rw [← Quotient.sound (s := s) hu, Quotient.out_eq]

theorem twConj_of_mem (hU : Unr E) (n : ℕ) (w : Pl E) (Q : (w.adicCompletion E)[X])
    (hQ : ∀ q : (w.adicCompletionIntegers E)[X], q.map (algebraMap _ (w.adicCompletion E)) = Q → q.Separable)
    (y z : GLw n w) (hy : (nrmL n w y).val.charpoly = Q) (hz : (nrmL n w z).val.charpoly = Q)
    (hyK : y ∈ GlobalTheory.LFun.KGL w n) (hzK : z ∈ GlobalTheory.LFun.KGL w n) : ∃ g, z = g⁻¹ * y * thL n w g := by
  let ι := algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨y', rfl⟩ : ∃ y' : GL (Fin n) (w.adicCompletionIntegers E), GeneralLinearGroup.map ι y' = y := hyK
  obtain ⟨z', rfl⟩ : ∃ z' : GL (Fin n) (w.adicCompletionIntegers E), GeneralLinearGroup.map ι z' = z := hzK
  have hch : ∀ a : GL (Fin n) (w.adicCompletionIntegers E),
      a.val.charpoly.map ι = (GeneralLinearGroup.map ι a).val.charpoly := fun a => (Matrix.charpoly_map _ _).symm
  have hconj : ∀ a b : GL (Fin n) (w.adicCompletionIntegers E), (GeneralLinearGroup.map ι a).val.charpoly = Q →
      (GeneralLinearGroup.map ι b).val.charpoly = Q → ∃ g, b = g⁻¹ * a * g := fun a b ha hb =>
    conj_of_charpoly a b (hQ _ ((hch a).trans ha))
      (Polynomial.map_injective ι hι (by rw [hch, hch, ha, hb]))
  by_cases hw : IsSplitAt w
  · simp only [nrmL, if_pos hw] at hy hz
    obtain ⟨g, rfl⟩ := hconj _ _ hy hz
    exact ⟨GeneralLinearGroup.map ι g, by rw [thL, if_pos hw, map_mul, map_mul, map_inv]; rfl⟩
  · obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
    have hcard' : Nat.card (w.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E))
      = q ^ 2 := hcard
    haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
    haveI : Finite (w.adicCompletionIntegers E ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
    let c : w.adicCompletionIntegers E →+* w.adicCompletionIntegers E :=
      (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
    have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
    have hmap : ∀ a, GeneralLinearGroup.map ι (thetaGL n c a) = thetaGL n (cj w) (GeneralLinearGroup.map ι a) :=
      GlobalTheory.ThetaPull.map_thetaGL ι c (cj w) (fun _ => rfl)
    simp only [nrmL, if_neg hw, ← hmap, ← map_mul] at hy hz
    obtain ⟨g, hg⟩ := hconj _ _ hy hz
    obtain ⟨k, hk⟩ := twConj_of_norm_eq c hc
      (fun x hx => by
        rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
        exact (hv _).trans_lt hx)
      ⟨⟨x₀, hx₀⟩, by
        rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
        change ¬ Valued.v (x₀ - cj w x₀) < 1
        rw [Valuation.map_sub_swap, hx₁]
        exact lt_irrefl _⟩
      y' (g * z' * thetaGL n c g⁻¹) (hQ _ ((hch _).trans hy)) (by
        simp only [map_mul, map_inv, GlobalTheory.ThetaPull.thetaGL_thetaGL c hc]
        calc _ = g * (z' * thetaGL n c z') * g⁻¹ := by group
          _ = _ := by rw [hg]; group)
    have hz' : z' = (k * g)⁻¹ * y' * thetaGL n c (k * g) := by
      calc z' = g⁻¹ * (g * z' * thetaGL n c g⁻¹) * thetaGL n c g := by rw [map_inv]; group
        _ = _ := by rw [hk, map_mul]; group
    refine ⟨GeneralLinearGroup.map ι (k * g), ?_⟩
    rw [thL, if_neg hw, ← hmap, ← map_inv, ← map_mul, ← map_mul, ← hz']

theorem stTw_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∀ᶠ w in (cofinite : Filter (Pl E)),
      stTw n w (atPl w P) ((GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1) = 1 := by
  intro E _ _ _ hU n P hP
  obtain ⟨S, hS⟩ := exists_isSection (E := E)
  obtain ⟨-, ⟨δ, hδ⟩, -⟩ := GlobalTheory.T.kappaConstant_mul_of_coprime_ellipticPolynomials E hU n 0 P 1 hP
    ⟨monic_one, natDegree_one, separable_one, fun τ z hz => by simp at hz⟩ isCoprime_one_right
  filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, eventually_separable P hP.2.2.1, eventually_mem_KGL δ,
    eventually_mem_KGL (δ * thE E n δ)] with w h1 h2 h3 h4
  refine clSum_eq_one _ _ _ _ (fun g y hy => ?_) h1 ⟨locEl n w δ, ?_, ?_⟩
    fun y hy z hz => twConj_of_mem hU n w _ h2 y z hy hz
  · change _ = _
    rw [ThBasic.nrmL_twist hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    exact hy
  · change _ = _
    rw [ThBasic.charpoly_nrmL hU, hδ]
  · unfold locEl
    split_ifs
    · exact h4
    · exact h3

end GlobalTheory.BCT.UnitStable
