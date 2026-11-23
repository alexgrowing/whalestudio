import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompare
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenOfUnit

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Gram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'}
  {f : X' ⟶ X} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {i : Ω →+* Ω'}
  {Li Li' : Type} [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li'] [Module Ω' Li']

theorem val_unique (hξ : IsCptGen ξ) (M : LieModel t.G ξ Li) {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) {e : Li}
    {w : epsAt z ⟶ t.G} (hw : M.ValAt z e w) : e ∈ M.lat ⟨centre z, hq⟩ ∧ ∀ w', M.ValAt z e w' → w' = w := by
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X t.G ℂ z
  obtain ⟨ev, hev1, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X t.G Ω ξ Li M ℂ z hq Vz MR hξ t.semi.smooth
  obtain ⟨x, rfl⟩ := MR.onto w (GrNorm.tan_of_valAt hw)
  obtain ⟨he, e2⟩ := (hev1 _ _).1 hw
  refine ⟨he, fun w' hw' => ?_⟩
  obtain ⟨x', rfl⟩ := MR.onto w' (GrNorm.tan_of_valAt hw')
  obtain ⟨_, e3⟩ := (hev1 _ _).1 hw'
  rw [← e2, ← e3]

theorem gram_up (m : SABMap t' t f) (hξ : IsCptGen ξ) (hξ' : IsCptGen ξ') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i)
    (M : LieModel t.G ξ Li) (M' : LieModel t'.G ξ' Li') (j : Li →+ Li')
    (hpt : ∀ e, (M'.pt (j e)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    (z : Sp ℂ ⟶ X') (hq : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) :
    ∃ φ : regAt ξ' ⟨centre z, hq⟩ →+* ℂ, (∀ a : regAt ξ' ⟨centre z, hq⟩, ValAt ξ' z (a : Ω') (φ a)) ∧
      ∀ (r : ℕ) (b : Fin r → Li) (Γ : Matrix (Fin r) (Fin r) ℂ) (b' : Fin r → Li')
        (P : Matrix (Fin r) (Fin r) (regAt ξ' ⟨centre z, hq⟩)), M.GramAt t.PP.L (z ≫ f) b Γ →
        (∀ k, b' k = ∑ l, (P l k : Ω') • j (b l)) → M'.GramAt t'.PP.L z b' ((P.map φ)ᴴ * Γ * P.map φ) := by
  classical
  set p' : Cpt ξ' := ⟨centre z, hq⟩ with hp'
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X' t'.G ℂ z
  obtain ⟨ev, hev1, hev2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X' t'.G Ω' ξ' Li' M' ℂ z hq Vz MR hξ' t'.semi.smooth
  let eA : X'.presheaf.stalk p'.1 ≃+* regAt ξ' p' :=
    RingEquiv.ofBijective (genMap ξ' p').rangeRestrict ⟨fun a b e => hξ'.inj p' (congrArg Subtype.val e),
      (genMap ξ' p').rangeRestrict_surjective⟩
  let φ : regAt ξ' p' →+* ℂ := (Scheme.stalkClosedPointTo z).hom.comp (eA.symm : regAt ξ' p' →+* X'.presheaf.stalk p'.1)
  have hφ : ∀ a : regAt ξ' p', ValAt ξ' z (a : Ω') (φ a) := fun a =>
    ⟨hq, eA.symm a, congrArg Subtype.val (eA.apply_symm_apply a), rfl⟩
  refine ⟨φ, hφ, fun r b Γ b' P ⟨v, hv, hI⟩ hP => ?_⟩
  let val : Li' → Vz := fun e => if he : e ∈ M'.lat p' then ev ⟨e, he⟩ else 0
  have hval : ∀ e (he : e ∈ M'.lat p'), val e = ev ⟨e, he⟩ := fun e he => dif_pos he
  have h0 : val 0 = 0 := by
    rw [hval 0 (zero_mem _)]
    exact map_zero ev
  have hadd : ∀ e ∈ M'.lat p', ∀ e' ∈ M'.lat p', val (e + e') = val e + val e' := fun e he e' he' => by
    rw [hval _ (add_mem he he'), hval e he, hval e' he']
    exact map_add ev ⟨e, he⟩ ⟨e', he'⟩
  have hsmul : ∀ a : regAt ξ' p', ∀ e ∈ M'.lat p', val ((a : Ω') • e) = φ a • val e := fun a e he => by
    have hm : (a : Ω') • e ∈ M'.lat p' := (M'.lat p').smul_mem a he
    rw [hval _ hm, hval e he]
    exact hev2 a (φ a) ⟨e, he⟩ (hφ a)
  have hpick : ∀ e (w : epsAt z ⟶ t'.G), M'.ValAt z e w → e ∈ M'.lat p' ∧ w = MR.pt (val e) := by
    intro e w hw
    obtain ⟨x, hx⟩ := MR.onto w (GrNorm.tan_of_valAt hw)
    rw [← hx] at hw ⊢
    obtain ⟨he, e2⟩ := (hev1 _ _).1 hw
    exact ⟨he, by rw [hval e he, e2]⟩
  have hu := fun k => val_unique hξ M (z := z ≫ f) hp (hv k)
  have hdown := fun k => HodgePull.value_pull (M' := M') (j := j) hd m.cart hpt hq hp (hu k).1
  choose w w' hw hw' hww using hdown
  have hwv : ∀ k, w k = v k := fun k => (hu k).2 _ (hw k)
  have hjL : ∀ k, j (b k) ∈ M'.lat p' := fun k => (hpick _ _ (hw' k)).1
  have hw'e : ∀ k, w' k = MR.pt (val (j (b k))) := fun k => (hpick _ _ (hw' k)).2
  have hb'L : ∀ k, b' k ∈ M'.lat p' := fun k => by
    rw [hP k]
    exact Submodule.sum_mem _ fun l _ => (M'.lat p').smul_mem (P l k) (hjL l)
  have hbv : ∀ k, val (b' k) = ∑ l, (P.map φ) l k • val (j (b l)) := fun k => by
    rw [hP k]
    exact GrNorm.val_sum h0 hadd hsmul hjL (fun l => P l k) Finset.univ
  refine ⟨fun k => MR.pt (val (b' k)), fun k => (hev1 _ _).2 ⟨hb'L k, (hval _ _).symm⟩, fun p q => ?_⟩
  simp only [hbv]
  refine HodgePull.gram_comb MR (fun l => val (j (b l))) Γ p (fun a c => ?_) (HodgePull.hodgeInnerProduct_unique m) _ p q
  rw [← hw'e, ← hw'e]
  refine ((GlobalTheory.T.hodge_inner_product_pullback_unique E H X' X t' t f m z (w' a) (w' c) (w a) (w c) (hww a) (hww c)).1 _).2 ?_
  rw [hwv, hwv]
  exact hI a c

end Gram

section Alg

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem det_tri {b₀ c : Fin r → V} (hb₀ : LinearIndependent Ω b₀) {t : Fin r → Ω}
    (ht : ∀ k : Fin r, c k - t k • b₀ k ∈ flagStep Ω b₀ k) (Q : Matrix (Fin r) (Fin r) Ω) (hQ : ∀ k, c k = ∑ l, Q l k • b₀ l) :
    Q.det = ∏ k, t k := by
  classical
  choose d hd0 hd using fun k => GrNorm.exists_coeff_of_mem_flagStep (ht k)
  have key : ∀ k, (fun l => Q l k) = fun l => d k l + (Pi.single k (t k) : Fin r → Ω) l := fun k =>
    GrNorm.coeff_eq_of_li hb₀ (by
      rw [← hQ k]
      simp only [add_smul, Finset.sum_add_distrib, ← hd k]
      simp [Pi.single_apply, ite_smul])
  have h1 : Q.BlockTriangular id := fun l k hlk => by
    have h := congrFun (key k) l
    have hlk' : k < l := hlk
    rw [hd0 k l hlk'.le, Pi.single_eq_of_ne hlk'.ne', add_zero] at h
    exact h
  rw [Matrix.det_of_upperTriangular h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h := congrFun (key k) k
  rwa [hd0 k k le_rfl, Pi.single_eq_same, zero_add] at h

theorem frame_mat (A : Subring Ω) {b b' : Fin r → V} (hb' : LinearIndependent Ω b')
    (hs : Submodule.span A (Set.range b) = Submodule.span A (Set.range b')) :
    ∃ P : Matrix (Fin r) (Fin r) A, (∀ k, b' k = ∑ l, (P l k : Ω) • b l) ∧ IsUnit P.det := by
  classical
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun A).1
    (show b' k ∈ Submodule.span A (Set.range b) from hs ▸ Submodule.subset_span ⟨k, rfl⟩)
  choose c' hc' using fun k => (Submodule.mem_span_range_iff_exists_fun A).1
    (show b k ∈ Submodule.span A (Set.range b') from hs ▸ Submodule.subset_span ⟨k, rfl⟩)
  let P : Matrix (Fin r) (Fin r) A := Matrix.of fun l k => c k l
  let P' : Matrix (Fin r) (Fin r) A := Matrix.of fun l k => c' k l
  have h1 : P' * P = 1 := by
    ext l k
    have key : (fun l => ((P' * P) l k : Ω)) = (Pi.single k 1 : Fin r → Ω) := GrNorm.coeff_eq_of_li hb' (by
      have e1 : ∑ l, (Pi.single k 1 : Fin r → Ω) l • b' l = b' k := by simp [Pi.single_apply, ite_smul]
      rw [e1, ← hc k]
      simp only [← hc', Finset.smul_sum, smul_smul, Matrix.mul_apply, P, P', Matrix.of_apply, AddSubmonoidClass.coe_finset_sum,
        Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
      rw [mul_comm]
      rfl)
    rw [congrFun key l, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  exact ⟨P, fun k => (hc k).symm, Matrix.isUnit_det_of_left_inverse h1⟩

theorem prod_sqrt_lead {Γ : Matrix (Fin r) (Fin r) ℂ} (h : Γ.PosDef) :
    ∏ k : Fin r, Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k) = Real.sqrt Γ.det.re := by
  have key : ∀ n, n ≤ r → ∏ k ∈ Finset.range n, Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k) =
      Real.sqrt (leadMinor Γ n) := by
    intro n hn
    induction n with
    | zero => simp [leadMinor_size_zero]
    | succ n ih =>
      have h1 := leadMinor_pos_of_posDef h (Nat.le_of_succ_le hn)
      rw [Finset.prod_range_succ, ih (Nat.le_of_succ_le hn), ← Real.sqrt_mul h1.le, mul_div_cancel₀ _ h1.ne']
  rw [Fin.prod_univ_eq_prod_range (fun k => Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k)), key r le_rfl,
    leadMinor_size_self]

theorem sqrt_det_conj (Γ C : Matrix (Fin r) (Fin r) ℂ) :
    Real.sqrt (Cᴴ * Γ * C).det.re = ‖C.det‖ * Real.sqrt Γ.det.re := by
  have e : (Cᴴ * Γ * C).det = ((‖C.det‖ ^ 2 : ℝ) : ℂ) * Γ.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_right_comm]
    congr 1
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [e, Complex.re_ofReal_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end Alg

section Sec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω}

theorem mono_sum {F : Type} [Field F] {I : Type} (z : K → F) (hz : ∀ k, z k ≠ 0) (s : Finset I) (a : I → K → ℤ) :
    ∏ k, z k ^ (∑ j ∈ s, a j) k = ∏ j ∈ s, ∏ k, z k ^ a j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, ← ih, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hz k) _ _

theorem valAt_prod {I : Type} {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) (s : Finset I) {a : I → Ω} {u : I → ℂ}
    (h : ∀ j, ValAt ξ z (a j) (u j)) : ValAt ξ z (∏ j ∈ s, a j) (∏ j ∈ s, u j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨hq, 1, by simp, by rw [Finset.prod_empty]; exact map_one _⟩
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact CxVal.mul (h j) ih

theorem secNorm_prod {I : Type} [Fintype I] {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt ξ y z w) {L : I → HermLine J} {e t : I → Ω} {ν : I → ℝ}
    (h : ∀ j, SecNorm ξ y (L j) (e j) z w (t j) (ν j)) {A : HermLine J} (ha : A.a = ∑ j, (L j).a)
    (hh : A.h w = ∏ j, (L j).h w) : SecNorm ξ y A (∏ j, e j) z w (∏ j, t j) (∏ j, ν j) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => (h j).1, hw, fun c hc => ?_⟩
  choose u hu hν using fun j => (h j).2.2 c hc
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).1
  refine ⟨∏ j, u j, ?_, ?_⟩
  · rw [ha, mono_sum _ hy, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    exact valAt_prod hq _ hu
  · rw [ha, mono_sum (fun k => ‖w ⟨k, c k⟩‖) (fun k => norm_ne_zero_iff.2 (hc k)), hh, norm_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hν j

end Sec

end LevelTowerAlt.Comparison₂
