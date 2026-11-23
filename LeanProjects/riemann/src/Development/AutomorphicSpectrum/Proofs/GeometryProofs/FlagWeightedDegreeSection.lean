import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFrames
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootGram

section Alg

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem ιMulti_eq_prod_smul {b₀ b : Fin r → V} {t : Fin r → Ω}
    (h : ∀ k : Fin r, b k - t k • b₀ k ∈ flagStep Ω b₀ k) :
    exteriorPower.ιMulti Ω r b = (∏ k, t k) • exteriorPower.ιMulti Ω r b₀ := by
  classical
  choose d hd1 hd2 using fun k => GrNorm.exists_coeff_of_mem_flagStep (h k)
  let a : Matrix (Fin r) (Fin r) Ω := fun k l => d k l + if k = l then t k else 0
  have hb : b = fun i => ∑ k, a i k • b₀ k := by
    funext i
    have e : b i = t i • b₀ i + ∑ l, d i l • b₀ l := by rw [← hd2 i]; abel
    simp only [a, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [e, add_comm]
  have hdet : a.det = ∏ k, t k := by
    rw [Matrix.det_of_lowerTriangular a]
    · refine Finset.prod_congr rfl fun k _ => ?_
      simp [a, hd1 k k le_rfl]
    · intro i j hij
      have hij' : i < j := hij
      simp [a, hd1 i j hij'.le, hij'.ne]
  rw [hb, GlobalTheory.alternating_map_sum_smul_eq_det_smul, hdet]

theorem diag_ne_zero {b₀ b : Fin r → V} {t : Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ s, flagStep Ω b s = flagStep Ω b₀ s) (k : Fin r) (h : b k - t • b₀ k ∈ flagStep Ω b₀ k) : t ≠ 0 := by
  rintro rfl
  have hk : b k ∈ flagStep Ω b k := by
    rw [hf]
    simpa using h
  exact hb.notMem_span_image (s := {l : Fin r | (l : ℕ) < k}) (x := k) (by simp) hk

end Alg

theorem sum_log_sqrt_leadMinor {r : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ} (hΓ : Γ.PosDef) :
    ∑ k : Fin r, Real.log (Real.sqrt (leadMinor Γ ((k : ℕ) + 1) / leadMinor Γ k)) = Real.log ‖Γ.det‖ / 2 := by
  have e : ∀ k : Fin r, Real.log (Real.sqrt (leadMinor Γ ((k : ℕ) + 1) / leadMinor Γ k)) =
      (Real.log (leadMinor Γ ((k : ℕ) + 1)) - Real.log (leadMinor Γ k)) / 2 := fun k => by
    have h1 := leadMinor_pos_of_posDef hΓ (s := (k : ℕ) + 1) k.2
    have h2 := leadMinor_pos_of_posDef hΓ (s := (k : ℕ)) k.2.le
    rw [Real.log_sqrt (div_pos h1 h2).le, Real.log_div h1.ne' h2.ne']
  simp only [e]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun k => Real.log (leadMinor Γ (k + 1)) - Real.log (leadMinor Γ k)) r,
    Finset.sum_range_sub (fun k => Real.log (leadMinor Γ k)), leadMinor_size_zero, Real.log_one, sub_zero,
    leadMinor_size_self]
  obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hΓ.det_pos
  have e2 : Γ.det = ((Γ.det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using h2.symm)
  have e3 : ‖Γ.det‖ = Γ.det.re := by
    rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h1)]
    simp
  rw [e3]

section Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem prod_roots (D : Datum H) (τ : CMType H) {M : Type} [CommMonoid M]
    (F : (Σ s : CMType H ⊕ CMType H, Fin (labelRk D s)) → ℤ → M) :
    ∏ i : Fin (D.p + D.q), F (HodgeCpt.rootIdx D (τ, i)) (HodgeCpt.rootSgn D (τ, i)) =
      (∏ k : Fin D.p, F ⟨.inl τ, k⟩ 1) * ∏ j : Fin D.q, F ⟨.inr τ, j⟩ (-1) := by
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun k _ => ?_
    have h : ((Fin.castAdd D.q k : Fin (D.p + D.q)) : ℕ) < D.p := k.2
    simp only [HodgeCpt.rootIdx, HodgeCpt.rootSgn, dif_pos h, if_pos h]
    rfl
  · refine Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_
    have h : ¬ ((Fin.natAdd D.p j : Fin (D.p + D.q)) : ℕ) < D.p := by simp
    simp only [HodgeCpt.rootIdx, HodgeCpt.rootSgn, dif_neg h, if_neg h]
    congr 2
    apply Fin.ext
    simp only [Fin.revPerm_apply, Fin.val_rev, Fin.val_natAdd]
    omega

end Roots

section Sec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {w : (Σ k, J k) → ℂ}

theorem zpow_sum_eq {G ι : Type} [CommGroupWithZero G] {a : G} (ha : a ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem exists_val_of_secNorm {ι : Type} [Fintype ι] (hx : ι → HermLine J) (e T : ι → Ω) (N : ι → ℝ) (A : HermLine J)
    (hN : ∀ i, 0 < N i) (hS : ∀ i, SecNorm ξ y (hx i) (e i) z w (T i) (N i)) (hA : A.a = ∑ i, (hx i).a)
    (hh : A.h w = ∏ i, (hx i).h w) (hw : CoordsAt ξ y z w) (hz : genPt ξ ⤳ centre z) (c₁ : Ω) (cc : (k : K) → J k)
    (hcc : ∀ k, w ⟨k, cc k⟩ ≠ 0) (u : ℂ)
    (hu : ValAt ξ z (c₁ / ((∏ k, y ⟨k, cc k⟩ ^ A.a k) * ∏ i, e i)) u) :
    ∃ u' : ℂ, ValAt ξ z (c₁ / ∏ i, T i) u' ∧
      ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = ‖u'‖ * (∏ i, N i) * A.h w := by
  classical
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hw.2 k (cc k) (IsUnit.mk0 _ (hcc k))).1
  choose v hv hv' using fun i => (hS i).2.2 cc hcc
  have hpos : ∀ i, 0 < (hx i).h w := fun i => (hx i).pos w fun k => ⟨cc k, hcc k⟩
  have hv0 : ∀ i, v i ≠ 0 := fun i h0 => by
    have h1 := hv' i
    rw [h0, norm_zero, zero_mul] at h1
    exact (mul_pos (hN i) (hpos i)).ne' h1
  have hprod : ∀ s : Finset ι, ValAt ξ z (∏ i ∈ s, T i / ((∏ k, y ⟨k, cc k⟩ ^ (hx i).a k) * e i)) (∏ i ∈ s, v i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact CxVal.mul (hv i) ih
  have hP0 : ∏ i, v i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hv0 i
  have hYe : (∏ k, y ⟨k, cc k⟩ ^ A.a k) = ∏ i, ∏ k, y ⟨k, cc k⟩ ^ (hx i).a k := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hA, Finset.sum_apply, zpow_sum_eq (hy k)]
  have hW : (∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k) = ∏ i, ∏ k, ‖w ⟨k, cc k⟩‖ ^ (hx i).a k := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hA, Finset.sum_apply, zpow_sum_eq (norm_ne_zero_iff.2 (hcc k))]
  have hne : (∏ k, y ⟨k, cc k⟩ ^ A.a k) * ∏ i, e i ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k))
      (Finset.prod_ne_zero_iff.2 fun i _ => (hS i).1)
  have hT : (∏ i, T i / ((∏ k, y ⟨k, cc k⟩ ^ (hx i).a k) * e i)) =
      (∏ i, T i) / ((∏ k, y ⟨k, cc k⟩ ^ A.a k) * ∏ i, e i) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hYe]
  refine ⟨u * (∏ i, v i)⁻¹, ?_, ?_⟩
  · have h1 := CxVal.mul hu (CxVal.inv (hprod Finset.univ) hP0)
    rwa [hT, inv_div, div_mul_div_cancel₀ hne] at h1
  · have key : (∏ i, ‖v i‖) * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = (∏ i, N i) * A.h w := by
      rw [hW, hh, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => (hv' i).symm
    have hn0 : (∏ i, ‖v i‖) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => norm_ne_zero_iff.2 (hv0 i)
    rw [norm_mul, norm_inv, norm_prod, _root_.mul_assoc, _root_.mul_assoc, ← key]
    field_simp

theorem degree_eq_sum {ι : Type} [Fintype ι] (hx : ι → HermLine J) (A : HermLine J) (hbl : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → A.h (fun p => c p.1 * w p) = ∏ i, (hx i).h (fun p => c p.1 * w p)) :
    A.a = ∑ i, (hx i).a := by
  classical
  funext k
  let c : K → ℂ := Function.update (fun _ => 1) k 2
  have hc : ∀ k', c k' ≠ 0 := fun k' => by
    by_cases e : k' = k
    · subst e; simp [c]
    · simp [c, e]
  have hc1 : ∀ a : K → ℤ, (∏ k', ‖c k'‖ ^ a k') = (2 : ℝ) ^ a k := fun a => by
    rw [Finset.prod_eq_single k]
    · simp [c]
    · intro k' _ e
      simp [c, e]
    · simp
  have h0 : A.h w = ∏ i, (hx i).h w := by simpa using h (fun _ => 1) (fun _ => one_ne_zero)
  have h1 := h c hc
  rw [A.smul c w hc, hc1] at h1
  simp only [(hx _).smul c w hc, hc1] at h1
  rw [Finset.prod_mul_distrib, ← h0, ← zpow_sum_eq two_ne_zero] at h1
  have hp : 0 < A.h w := A.pos w hbl
  have h2 := mul_right_cancel₀ hp.ne' h1
  rw [Finset.sum_apply]
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h2

end Sec

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem val_ne_zero_of_rank_zero {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {𝔐 : HodgeCpt Y S y}
    (Fl : 𝔐.Flag) (hβ : Function.Injective β) (hp : D.p = 0) (hq : D.q = 0) {f : Ω} (hf : f ≠ 0)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {u : ℂ} (hu : ValAt 𝔐.ξ z f u) : u ≠ 0 := by
  classical
  obtain ⟨-, ⟨x, hx⟩, hchar, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c O β Y 𝔐.Ω₀ 𝔐.ξ₀ Ω x 𝔐.fn hβ 𝔐.gen₀ (hx ▸ 𝔐.fn_over)
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  have hB := GlobalTheory.T.generic_flag_trdeg_formula 𝔐.Ω₀ Ω Fl.Li₀ 𝔐.Li Fl.j (CMType H ⊕ CMType H) (labelRk D) Fl.V₀ Fl.b Fl.deg Fl.generic
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).mpr hchar
  haveI : FaithfulSMul ℤ 𝔐.Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ 𝔐.Ω₀).mpr Int.cast_injective
  haveI : FaithfulSMul 𝔐.Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective 𝔐.Ω₀ Ω).mpr 𝔐.fn.injective
  have htow := trdeg_add_eq ℤ 𝔐.Ω₀ (A := Ω)
  have hz0 : (∑ σ : CMType H ⊕ CMType H, labelRk D σ * (labelRk D σ - 1) / 2) = 0 := by
    refine Finset.sum_eq_zero fun σ _ => ?_
    rcases σ with σ | σ <;> simp [labelRk, hp, hq]
  rw [hA, hB, hz0] at htow
  have htr : Algebra.trdeg ℤ Ω = 0 := by
    rw [← htow]
    simp [Datum.dim, hp]
  haveI : Algebra.IsAlgebraic ℤ Ω := trdeg_eq_zero_iff.1 htr
  obtain ⟨p, hp0, hpf⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℤ) f
  obtain ⟨g, hg, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  have hg0 : g.coeff 0 ≠ 0 := fun h => hnd (by simpa using Polynomial.X_dvd_iff.2 h)
  have hgf : Polynomial.eval₂ (Int.castRingHom Ω) f g = 0 := by
    rw [hg, map_mul, map_pow] at hpf
    have h1 := (mul_eq_zero.1 hpf).resolve_left (pow_ne_zero _ (by simpa using hf))
    rw [Polynomial.aeval_def] at h1
    rwa [show algebraMap ℤ Ω = Int.castRingHom Ω from Subsingleton.elim _ _] at h1
  intro h0
  obtain ⟨h, s, hs, hs'⟩ := hu
  have e : Polynomial.eval₂ (Int.castRingHom (𝔐.X.presheaf.stalk (centre z))) s g = 0 := by
    apply 𝔐.tie.gen.inj ⟨centre z, h⟩
    rw [map_zero, Polynomial.hom_eval₂, hs, Subsingleton.elim ((genMap 𝔐.ξ ⟨centre z, h⟩).comp _) (Int.castRingHom Ω)]
    exact hgf
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝔐.X.presheaf.stalk (centre z) →+* ℂ, φ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have hs2 : φ s = 0 := by rw [hφ]; exact hs'.trans h0
  have e2 : φ (Polynomial.eval₂ (Int.castRingHom (𝔐.X.presheaf.stalk (centre z))) s g) = 0 := by
    rw [e, map_zero]
  rw [Polynomial.hom_eval₂, hs2, Polynomial.eval₂_at_zero] at e2
  have e3 : ((g.coeff 0 : ℤ) : ℂ) = 0 := by simpa using e2
  exact hg0 (by exact_mod_cast e3)

theorem exists_gram [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} (𝔐 : HodgeCpt Y S y)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hz : 𝔐.Interior z) (s : CMType H ⊕ CMType H) {b : Fin (labelRk D s) → 𝔐.Li}
    (hb : (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩) :
    ∃ Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z b Γ ∧ Γ.PosDef := by
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, hchar, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  have hgen : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain ⟨hV, -, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, hgen⟩
    fun r hr => GrNorm.not_inFibre 𝔐.tie.gen hgen hr
  have hmem : ∀ k, b k ∈ 𝔐.Vgen s ⊔ 𝔐.Vgen s := fun k => by
    have h1 : b k ∈ 𝔐.V s ⟨centre z, hgen⟩ := by
      rw [hb.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [hV s] at h1
    exact Submodule.mem_sup_left h1.2
  let bb : Fin (labelRk D s) → ↥(𝔐.Vgen s ⊔ 𝔐.Vgen s) := fun k => ⟨b k, hmem k⟩
  have hspan : (Submodule.span (regAt 𝔐.ξ ⟨centre z, hgen⟩) (Set.range bb)).map
      ((𝔐.Vgen s ⊔ 𝔐.Vgen s).subtype.restrictScalars (regAt 𝔐.ξ ⟨centre z, hgen⟩)) =
      Submodule.span (regAt 𝔐.ξ ⟨centre z, hgen⟩) (Set.range b) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hfr : (Lat.comap (fun p => 𝔐.V s p ⊔ 𝔐.V s p) (𝔐.Vgen s ⊔ 𝔐.Vgen s).subtype).IsFrameAt bb
      ⟨centre z, hgen⟩ := by
    refine ⟨LinearIndependent.of_comp (𝔐.Vgen s ⊔ 𝔐.Vgen s).subtype hb.1, ?_⟩
    ext x
    constructor
    · intro hx
      have h1 : (x : 𝔐.Li) ∈ 𝔐.V s ⟨centre z, hgen⟩ ⊔ 𝔐.V s ⟨centre z, hgen⟩ := hx
      rw [sup_idem, hb.2, ← hspan] at h1
      obtain ⟨x', hx', e⟩ := h1
      have e' : x' = x := Subtype.ext e
      exact e' ▸ hx'
    · intro hx
      show (x : 𝔐.Li) ∈ 𝔐.V s ⟨centre z, hgen⟩ ⊔ 𝔐.V s ⟨centre z, hgen⟩
      rw [sup_idem, hb.2, ← hspan]
      exact ⟨x, hx, rfl⟩
  obtain ⟨Γ, h1, h2⟩ := GlobalTheory.T.pair_sum_frame_at_point E H D l Xo c Y S Ω K J y 𝔐 s s _ bb z hgen hpol hfr
  exact ⟨Γ, h1, h2⟩

theorem exists_flag_frame [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hz : 𝔐.Interior z) (s : CMType H ⊕ CMType H) :
    ∃ (b : Fin (labelRk D s) → 𝔐.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ)
      (t : Fin (labelRk D s) → Ω), (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩ ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b Γ ∧ Γ.PosDef ∧
      (∀ k, t k ≠ 0) ∧ exteriorPower.ιMulti Ω _ b = (∏ k, t k) • exteriorPower.ιMulti Ω _ (Fl.b s) ∧
      ∀ k, 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) k z (t k)
        (Real.sqrt (leadMinor Γ ((k : ℕ) + 1) / leadMinor Γ k)) := by
  obtain ⟨U, hU, b, hflag, hb⟩ := Fl.sub s ⟨centre z, 𝔐.all _⟩ trivial
  have hfr := hb ⟨centre z, 𝔐.all _⟩ trivial hU
  obtain ⟨Γ, hΓ, hP⟩ := exists_gram 𝔐 hz s hfr
  have ht : ∀ k : Fin (labelRk D s), ∃ a : Ω, b k - a • Fl.b s k ∈ flagStep Ω (Fl.b s) k := fun k =>
    GrNorm.exists_sub_mem_flagStep k (hflag _ ▸ Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩)
  choose t ht using ht
  exact ⟨b, Γ, t, hfr, hΓ, hP, fun k => diag_ne_zero hfr.1 hflag k (ht k), ιMulti_eq_prod_smul ht,
    fun k => ⟨𝔐.all _, b, Γ, hflag, hfr, ht k, hΓ, hP, rfl⟩⟩

theorem exists_doubled [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} (𝔐 : HodgeCpt Y S y)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hz : 𝔐.Interior z) (s : CMType H ⊕ CMType H) {b : Fin (labelRk D s) → 𝔐.Li}
    {Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ} (hb : (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩)
    (hG : 𝔐.M.GramAt 𝔐.t.PP.L z b Γ) (hP : Γ.PosDef) :
    ∃ Γ' : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ,
      (𝔐.V s).IsFrameAt (fun k => (2 : Ω) • b k) ⟨centre z, 𝔐.all _⟩ ∧
      𝔐.M.GramAt 𝔐.t.PP.L z (fun k => (2 : Ω) • b k) Γ' ∧ Γ'.PosDef ∧
      Real.log ‖Γ'.det‖ = Real.log ‖Γ.det‖ + labelRk D s * Real.log 4 := by
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, hchar, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  have hgen : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S Ω K J y 𝔐 z hz
  have hu2 : IsUnit (2 : 𝔐.X.presheaf.stalk (centre z)) :=
    CxVal.isUnit (z := z) 2 fun h =>
      (two_ne_zero : (2 : ℂ) ≠ 0) ((map_ofNat (Scheme.stalkClosedPointTo z).hom 2).symm.trans h)
  let ρ : 𝔐.X.presheaf.stalk (centre z) →+* regAt 𝔐.ξ ⟨centre z, hgen⟩ := (genMap 𝔐.ξ ⟨centre z, hgen⟩).rangeRestrict
  let u2 : (regAt 𝔐.ξ ⟨centre z, hgen⟩)ˣ := Units.map (ρ : _ →* _) hu2.unit
  have hu2c : ((u2 : regAt 𝔐.ξ ⟨centre z, hgen⟩) : Ω) = 2 := by
    show genMap 𝔐.ξ ⟨centre z, hgen⟩ 2 = 2
    exact map_ofNat _ 2
  obtain ⟨h1, h2, -⟩ := GrNorm.scale_frame (regAt 𝔐.ξ ⟨centre z, hgen⟩) hb.1 (fun _ => u2)
  simp only [hu2c] at h1 h2
  have hfr : (𝔐.V s).IsFrameAt (fun k => (2 : Ω) • b k) ⟨centre z, 𝔐.all _⟩ := ⟨h1, hb.2.trans h2.symm⟩
  obtain ⟨Γ', hG', hP'⟩ := exists_gram 𝔐 hz s hfr
  have v2 : ValAt 𝔐.ξ z (2 : Ω) (2 : ℂ) := ⟨hgen, 2, map_ofNat _ 2, map_ofNat _ 2⟩
  have v0 : ValAt 𝔐.ξ z (0 : Ω) (0 : ℂ) := ⟨hgen, 0, map_zero _, map_zero _⟩
  have e := HodgeMetric.gramAt_change E H D l Xo c Y S Ω K J y 𝔐 z _ b (fun k => (2 : Ω) • b k) Γ Γ'
    (Matrix.diagonal fun _ => 2) (Matrix.diagonal fun _ => 2) hpol hG hG'
    (fun q => by simp [Matrix.diagonal_apply]) (fun p q => by
      by_cases h : p = q
      · simpa [h] using v2
      · simpa [Matrix.diagonal_apply, h] using v0)
  have e2 : Γ'.det = 4 ^ (labelRk D s) * Γ.det := by
    rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have e3 : star ((2 : ℂ) ^ labelRk D s) = 2 ^ labelRk D s := by simp
    rw [e3, show (4 : ℂ) = 2 * 2 by norm_num, mul_pow]
    ring
  refine ⟨Γ', hfr, hG', hP', ?_⟩
  have hd : ‖Γ.det‖ ≠ 0 := norm_ne_zero_iff.2 hP.det_pos.ne'
  rw [e2, norm_mul, norm_pow, Real.log_mul (pow_ne_zero _ (by simp)) hd, Real.log_pow]
  simp
  ring

end Geo

theorem wedge_doubled {Ω : Type} [Field Ω] [CharZero Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ} {b : Fin r → V}
    {a : ⋀[Ω]^r V} {α : Ω} (h : a = α • exteriorPower.ιMulti Ω r b) :
    a = (α * 2 ^ (-(r : ℤ))) • exteriorPower.ιMulti Ω r (fun k => (2 : Ω) • b k) := by
  have e := ιMulti_eq_prod_smul (Ω := Ω) (b₀ := b) (b := fun k => (2 : Ω) • b k) (t := fun _ => 2) (fun k => by simp)
  rw [e, smul_smul, h]
  congr 1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_neg, zpow_natCast]
  field_simp

theorem norm_against_root_metrics : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (A : HermLine J) (τ : CMType H) (t₀ : ℝ) (c₁ : Ω) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), Fl.RootLines xdeg e → (∀ r, Fl.IsHodgeLine r (e r) (hx r)) → A.a = ∑ i, xdeg (τ, i) → (∀ w' : (Σ k, J k) → ℂ, CoordsAt 𝔐.ξ y z w' → A.h w' = ∏ i, (hx (τ, i)).h w') → CoordsAt 𝔐.ξ y z w → 𝔐.Interior z → c₁ ≠ 0 → (∀ (hc : genPt 𝔐.ξ ⤳ centre z) (bp : Fin D.p → 𝔐.Li) (bq : Fin D.q → 𝔐.Li) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ) (α κ : Ω) (u : ℂ), (𝔐.V (.inl τ)).IsFrameAt bp ⟨centre z, hc⟩ → (𝔐.V (.inr τ)).IsFrameAt bq ⟨centre z, hc⟩ → 𝔐.M.GramAt 𝔐.t.PP.L z bp Γ → 𝔐.M.GramAt 𝔐.t.PP.L z bq Δ → Γ.PosDef → Δ.PosDef → (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) = α • exteriorPower.ιMulti Ω _ bp → (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) = κ • exteriorPower.ιMulti Ω _ bq → ValAt 𝔐.ξ z (c₁ * α / κ) u → Real.log ‖u‖ + (Real.log ‖Γ.det‖ - Real.log ‖Δ.det‖) / 2 = t₀) → ∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt 𝔐.ξ z (c₁ / ((∏ k, y ⟨k, cc k⟩ ^ A.a k) * ∏ i, e (τ, i))) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = Real.exp t₀ * A.h w := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐 Fl xdeg e hx A τ t₀ c₁ z w hroot hhod hAa hAh hw hint hc₁ hfr cc u hcc hu
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, hchar, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  have hgen : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  choose b Γ t hbf hbG hbP ht hbw hbn using fun s => exists_flag_frame Fl hint s
  let ν : ∀ s, Fin (labelRk D s) → ℝ := fun s k => Real.sqrt (leadMinor (Γ s) ((k : ℕ) + 1) / leadMinor (Γ s) k)
  let T : Fin (D.p + D.q) → Ω := fun i =>
    t (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^ HodgeCpt.rootSgn D (τ, i)
  let N : Fin (D.p + D.q) → ℝ := fun i =>
    ν (HodgeCpt.rootIdx D (τ, i)).1 (HodgeCpt.rootIdx D (τ, i)).2 ^ HodgeCpt.rootSgn D (τ, i)
  have hν : ∀ s k, 0 < ν s k := fun s k => (hbn s k).pos
  have hS : ∀ i, SecNorm 𝔐.ξ y (hx (τ, i)) (e (τ, i)) z w (T i) (N i) := fun i =>
    hhod (τ, i) z w hw hint _ _ (hbn _ _)
  have hN : ∀ i, 0 < N i := fun i => zpow_pos (hν _ _) _
  have hA : A.a = ∑ i, (hx (τ, i)).a := degree_eq_sum (w := w) (fun i => hx (τ, i)) A (fun k => ⟨cc k, hcc k⟩)
    fun c' hc' => hAh _ (RootHt.ArchB.coordsAt_smul c' hc' hw)
  obtain ⟨u', hu', hnorm⟩ := exists_val_of_secNorm (fun i => hx (τ, i)) (fun i => e (τ, i)) T N A hN hS hA (hAh w hw) hw
    hgen c₁ cc hcc u hu
  obtain ⟨P, hPdef⟩ : ∃ P : Ω, P = ∏ k : Fin (labelRk D (.inl τ)), t (.inl τ) k := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Ω, Q = ∏ j : Fin (labelRk D (.inr τ)), t (.inr τ) j := ⟨_, rfl⟩
  have hP0 : P ≠ 0 := hPdef ▸ Finset.prod_ne_zero_iff.2 fun k _ => ht (.inl τ) k
  have hQ0 : Q ≠ 0 := hQdef ▸ Finset.prod_ne_zero_iff.2 fun k _ => ht (.inr τ) k
  have hPT : ∏ i, T i = P * Q⁻¹ := by
    have h1 := prod_roots D τ (fun x n => t x.1 x.2 ^ n)
    have e1 : (∏ k : Fin (labelRk D (.inl τ)), t (.inl τ) k ^ (1 : ℤ)) = P := by
      rw [hPdef]
      simp only [zpow_one]
    have e2 : (∏ j : Fin (labelRk D (.inr τ)), t (.inr τ) j ^ (-1 : ℤ)) = Q⁻¹ := by
      rw [hQdef, ← Finset.prod_inv_distrib]
      simp only [zpow_neg_one]
    rw [← e1, ← e2]
    exact h1
  have hPN : ∏ i, N i = (∏ k : Fin (labelRk D (.inl τ)), ν (.inl τ) k) *
      (∏ j : Fin (labelRk D (.inr τ)), ν (.inr τ) j)⁻¹ := by
    have h1 := prod_roots D τ (fun x n => ν x.1 x.2 ^ n)
    have e1 : (∏ k : Fin (labelRk D (.inl τ)), ν (.inl τ) k ^ (1 : ℤ)) = ∏ k, ν (.inl τ) k := by
      simp only [zpow_one]
    have e2 : (∏ j : Fin (labelRk D (.inr τ)), ν (.inr τ) j ^ (-1 : ℤ)) = (∏ j, ν (.inr τ) j)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      simp only [zpow_neg_one]
    rw [← e1, ← e2]
    exact h1
  have hval : ValAt 𝔐.ξ z (c₁ * P⁻¹ / Q⁻¹) u' := by
    have e1 : c₁ * P⁻¹ / Q⁻¹ = c₁ / ∏ i, T i := by
      rw [hPT]
      field_simp
    rw [e1]
    exact hu'
  have hw1 : exteriorPower.ιMulti Ω _ (Fl.b (.inl τ)) = P⁻¹ • exteriorPower.ιMulti Ω _ (b (.inl τ)) := by
    rw [hbw, ← hPdef, smul_smul, inv_mul_cancel₀ hP0, one_smul]
  have hw2 : exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)) = Q⁻¹ • exteriorPower.ιMulti Ω _ (b (.inr τ)) := by
    rw [hbw, ← hQdef, smul_smul, inv_mul_cancel₀ hQ0, one_smul]
  have heq : Real.log ‖u'‖ + (Real.log ‖(Γ (.inl τ)).det‖ - Real.log ‖(Γ (.inr τ)).det‖) / 2 = t₀ :=
    hfr hgen (b (.inl τ)) (b (.inr τ)) (Γ (.inl τ)) (Γ (.inr τ)) P⁻¹ Q⁻¹ u' (hbf _) (hbf _) (hbG _) (hbG _)
      (hbP _) (hbP _) hw1 hw2 hval
  have v2 : ValAt 𝔐.ξ z (2 : Ω) (2 : ℂ) := ⟨hgen, 2, map_ofNat _ 2, map_ofNat _ 2⟩
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hu0 : u' ≠ 0 := by
    intro h0
    rw [h0] at hval heq
    rcases Nat.eq_zero_or_pos D.p with hp | hp
    · rcases Nat.eq_zero_or_pos D.q with hq | hq
      · exact val_ne_zero_of_rank_zero Fl hβ hp hq
          (div_ne_zero (mul_ne_zero hc₁ (inv_ne_zero hP0)) (inv_ne_zero hQ0)) hval rfl
      · obtain ⟨Γ', f', g', p', hlog⟩ := exists_doubled 𝔐 hint (.inr τ) (hbf _) (hbG _) (hbP _)
        have hv : ValAt 𝔐.ξ z (c₁ * P⁻¹ / (Q⁻¹ * 2 ^ (-(D.q : ℤ)))) 0 := by
          have h1 := CxVal.mul hval (CxVal.zpow v2 two_ne_zero (D.q : ℤ))
          rw [zero_mul] at h1
          convert h1 using 1
          rw [zpow_neg]
          field_simp
        have h2 : Real.log ‖(0 : ℂ)‖ + (Real.log ‖(Γ (.inl τ)).det‖ - Real.log ‖Γ'.det‖) / 2 = t₀ :=
          hfr hgen (b (.inl τ)) (fun k => (2 : Ω) • b (.inr τ) k) (Γ (.inl τ)) Γ' P⁻¹ (Q⁻¹ * 2 ^ (-(D.q : ℤ))) 0
            (hbf _) f' (hbG _) g' (hbP _) p' hw1 (wedge_doubled hw2) hv
        have h3 : (0 : ℝ) < (labelRk D (.inr τ) : ℝ) * Real.log 4 :=
          mul_pos (Nat.cast_pos.2 (show 0 < labelRk D (.inr τ) from hq)) hl4
        rw [hlog] at h2
        linarith
    · obtain ⟨Γ', f', g', p', hlog⟩ := exists_doubled 𝔐 hint (.inl τ) (hbf _) (hbG _) (hbP _)
      have hv : ValAt 𝔐.ξ z (c₁ * (P⁻¹ * 2 ^ (-(D.p : ℤ))) / Q⁻¹) 0 := by
        have h1 := CxVal.mul hval (CxVal.zpow v2 two_ne_zero (-(D.p : ℤ)))
        rw [zero_mul] at h1
        convert h1 using 1
        ring
      have h2 : Real.log ‖(0 : ℂ)‖ + (Real.log ‖Γ'.det‖ - Real.log ‖(Γ (.inr τ)).det‖) / 2 = t₀ :=
        hfr hgen (fun k => (2 : Ω) • b (.inl τ) k) (b (.inr τ)) Γ' (Γ (.inr τ)) (P⁻¹ * 2 ^ (-(D.p : ℤ))) Q⁻¹ 0
          f' (hbf _) g' (hbG _) p' (hbP _) (wedge_doubled hw1) hw2 hv
      have h3 : (0 : ℝ) < (labelRk D (.inl τ) : ℝ) * Real.log 4 :=
        mul_pos (Nat.cast_pos.2 (show 0 < labelRk D (.inl τ) from hp)) hl4
      rw [hlog] at h2
      linarith
  have hexp : ∀ s, (∏ k, ν s k) = Real.exp (Real.log ‖(Γ s).det‖ / 2) := fun s => by
    rw [← sum_log_sqrt_leadMinor (hbP s), Real.exp_sum]
    exact Finset.prod_congr rfl fun k _ => (Real.exp_log (hν s k)).symm
  have hfin : ‖u'‖ * ∏ i, N i = Real.exp t₀ := by
    rw [hPN, ← heq, Real.exp_add, Real.exp_log (norm_pos_iff.2 hu0), sub_div, Real.exp_sub]
    rw [hexp, hexp, div_eq_mul_inv]
    ring
  rw [hnorm, hfin]

end GlobalTheory.CompanionTheory.Ar.RootGram
