import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpan
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgePull

open scoped ComplexOrder Matrix

section Val

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X}
  {i : Ω →+* Ω'}

theorem valAt_pull (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) {z : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre z) {a : Ω} {r : ℂ}
    (h : ValAt ξ (z ≫ f) a r) : ValAt ξ' z (i a) r := by
  obtain ⟨hp, s, rfl, rfl⟩ := h
  exact ⟨hq, (f.stalkMap (centre z)).hom s, RegAtDom.genMap_stalkMap hd _ hq hp s,
    (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z f)).symm⟩

variable {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
  [∀ k, Fintype (J' k)] {κ : K → K'} {v : (Σ k, J k) → (Σ k, J' k)} {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}

theorem ratio_update [DecidableEq K] (d : ∀ k, J k) (k : K) (e : J k) (h0 : ∏ l, y ⟨l, d l⟩ ≠ 0) :
    (∏ l, y ⟨l, Function.update d k e l⟩) / ∏ l, y ⟨l, d l⟩ = y ⟨k, e⟩ / y ⟨k, d k⟩ := by
  have h1 : ∏ l, y ⟨l, Function.update d k e l⟩ = y ⟨k, e⟩ * ∏ l ∈ Finset.univ.erase k, y ⟨l, d l⟩ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun l => y ⟨l, Function.update d k e l⟩) (Finset.mem_univ k),
      Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h2 : ∏ l, y ⟨l, d l⟩ = y ⟨k, d k⟩ * ∏ l ∈ Finset.univ.erase k, y ⟨l, d l⟩ :=
    (Finset.mul_prod_erase Finset.univ (fun l => y ⟨l, d l⟩) (Finset.mem_univ k)).symm
  rw [h2] at h0 ⊢
  rw [h1, mul_div_mul_right _ _ (right_ne_zero_of_mul h0)]

theorem coordsAt_pull (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hg' : IsCptGen ξ')
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    (hv : AI.I1.IsBlockMap κ v) (hy : ∀ q, y' (v q) = i (y q)) {z : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre z)
    (hp : genPt ξ ⤳ f (centre z)) {w : (Σ k, J' k) → ℂ} (hw : CoordsAt ξ' y' z w) :
    CoordsAt ξ y (z ≫ f) fun p => w (v p) := by
  classical
  choose c' hc' using hw.1
  obtain ⟨d, hdv⟩ := FlagPull.exists_chart hv c'
  have key : ∀ k e, ∃ r : ℂ, ValAt ξ' z (i (y ⟨k, e⟩ / y ⟨k, d k⟩)) r ∧ w (v ⟨k, e⟩) = r * w (v ⟨k, d k⟩) := by
    intro k e
    obtain ⟨-, hval⟩ := hw.2 (κ k) (c' (κ k)) (hc' _)
    have aux : ∀ s : Σ k', J' k', s.1 = κ k → ∃ r : ℂ, ValAt ξ' z (y' s / y' ⟨κ k, c' (κ k)⟩) r ∧
        w s = r * w ⟨κ k, c' (κ k)⟩ := by
      rintro ⟨k2, s2⟩ e2
      obtain rfl : k2 = κ k := e2
      exact hval s2
    obtain ⟨r, h1, h2⟩ := aux (v ⟨k, e⟩) (hv.2.2.1 ⟨k, e⟩)
    refine ⟨r, ?_, ?_⟩
    · rw [map_div₀, ← hy, ← hy, hdv k]
      exact h1
    · rw [hdv k]
      exact h2
  have hyd : ∀ k, y ⟨k, d k⟩ ≠ 0 := fun k h0 => by
    have h1 := (hw.2 (κ k) (c' (κ k)) (hc' _)).1
    rw [← hdv k, hy, h0, map_zero] at h1
    exact h1 rfl
  have hd0 : ∏ k, y ⟨k, d k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hyd k
  have hr : ∀ c : ∀ k, J k, i ((∏ k, y ⟨k, c k⟩) / ∏ k, y ⟨k, d k⟩) ∈ regAt ξ' ⟨centre z, hq⟩ := by
    intro c
    rw [← Finset.prod_div_distrib, map_prod]
    refine prod_mem fun k _ => ?_
    obtain ⟨r, ⟨_, s, e, -⟩, -⟩ := key k (c k)
    exact ⟨s, e⟩
  have hch := FlagPull.inChart_of_pull hd hg' hcov ⟨centre z, hq⟩ hp hd0 hr
  have reg : ∀ k (e : J k), y ⟨k, e⟩ / y ⟨k, d k⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := by
    intro k e
    have := hch.2 (Function.update d k e)
    simp only [] at this
    rwa [ratio_update d k e hd0] at this
  have val : ∀ k (e : J k), ∃ r : ℂ, ValAt ξ (z ≫ f) (y ⟨k, e⟩ / y ⟨k, d k⟩) r ∧
      w (v ⟨k, e⟩) = r * w (v ⟨k, d k⟩) := by
    intro k e
    obtain ⟨s, hs⟩ := reg k e
    obtain ⟨r', h1, h2⟩ := key k e
    have hv0 : ValAt ξ (z ≫ f) (y ⟨k, e⟩ / y ⟨k, d k⟩) _ := ⟨hp, s, hs, rfl⟩
    refine ⟨_, hv0, ?_⟩
    rw [h2, CxVal.unique (valAt_pull hd hq hv0) h1]
  refine ⟨fun k => ⟨d k, ?_⟩, fun k e he => ?_⟩
  · show IsUnit (w (v ⟨k, d k⟩))
    rw [hdv k]
    exact hc' _
  · have he' : w (v ⟨k, e⟩) ≠ 0 := he.ne_zero
    obtain ⟨re, h1, h2⟩ := val k e
    have hre : re ≠ 0 := fun h => he' (by rw [h2, h, zero_mul])
    have hye : y ⟨k, e⟩ ≠ 0 := by
      intro h0
      rw [h0, zero_div] at h1
      exact hre (CxVal.unique h1 (RootHt.ArchB.val_zero hp))
    refine ⟨hye, fun e2 => ?_⟩
    obtain ⟨r2, h3, h4⟩ := val k e2
    refine ⟨r2 * re⁻¹, ?_, ?_⟩
    · have h5 := CxVal.mul h3 (CxVal.inv h1 hre)
      have e3 : y ⟨k, e2⟩ / y ⟨k, e⟩ = y ⟨k, e2⟩ / y ⟨k, d k⟩ * (y ⟨k, e⟩ / y ⟨k, d k⟩)⁻¹ := by
        have := hyd k
        field_simp
      rw [e3]
      exact h5
    · show w (v ⟨k, e2⟩) = r2 * re⁻¹ * w (v ⟨k, e⟩)
      rw [h4, h2]
      field_simp

end Val

section Lie

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X}
  {i : Ω →+* Ω'} {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

theorem value_pull (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hG : IsGrpPullback G' G f φ)
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    {z : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) {e : V}
    (he : e ∈ M.lat ⟨f (centre z), hp⟩) :
    ∃ (w : epsAt (z ≫ f) ⟶ G) (w' : epsAt z ⟶ G'), M.ValAt (z ≫ f) e w ∧ M'.ValAt z (j e) w' ∧
      w'.left ≫ φ = w.left := by
  obtain ⟨v, hv⟩ := ((lieLat_carrier X G Ω ξ V M _).1 e).1 he
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ') ⟨centre z, hq⟩
  have hρ := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := centre z)
  have hρ' : (genMap ξ' ⟨centre z, hq⟩).comp (f.stalkMap (centre z)).hom = i.comp (genMap ξ ⟨f (centre z), hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd _ hq hp)
  obtain ⟨v', hv', hφ⟩ := LiePull.ext_up (ρ := (f.stalkMap (centre z)).hom) (g := genMap ξ ⟨f (centre z), hp⟩)
    (g' := genMap ξ' ⟨centre z, hq⟩) (x := X.fromSpecStalk (f (centre z))) (x' := X'.fromSpecStalk (centre z))
    (M := M) (M' := M') hG hj hρ hρ' hx' (v := v) hv
  have hc₁ : Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo z).hom) ≫ X'.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have hc₀ : Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo (z ≫ f)).hom) ≫ X.fromSpecStalk (f (centre z)) =
      z ≫ f := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (z ≫ f)
  refine ⟨LieCarrier.epsHom _ _ _ hc₀ ≫ v, LieCarrier.epsHom _ _ _ hc₁ ≫ v', ⟨hp, v, hv, rfl⟩, ⟨hq, v', hv', rfl⟩, ?_⟩
  have e0 : (Scheme.stalkClosedPointTo (z ≫ f)).hom =
      (Scheme.stalkClosedPointTo z).hom.comp (f.stalkMap (centre z)).hom :=
    congrArg (fun t => t.hom) (Scheme.stalkClosedPointTo_comp z f)
  show (Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v'.left) ≫ φ =
    Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ f)).hom)) ≫ v.left
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ t) hφ).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (fun t => t ≫ v.left) ?_
  have e1 : dualMap (Scheme.stalkClosedPointTo (z ≫ f)).hom =
      (dualMap (Scheme.stalkClosedPointTo z).hom).comp (dualMap (f.stalkMap (centre z)).hom) := by
    rw [e0]
    exact (LiePull.dualMap_comp _ _).symm
  have e2 := congrArg (fun t => Spec.map (CommRingCat.ofHom t)) e1
  exact Eq.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm e2.symm

end Lie

section Gram

open GlobalTheory.CompanionTheory.Ar.HodgeExt GlobalTheory.TangentOrigin

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isDiff_comb {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left} {L₀ : LB A.left} {g : ℕ} (Mz : LieModel G z V)
    (h : IsGrpPullback A G z φ) (u₀ : HolUnif A L₀ g) {r : ℕ} (a : Fin r → V) (d : Fin r → Fin g → ℂ)
    (hd : ∀ l, u₀.IsDiff (d l) (lft h (Mz.pt (a l)))) (i0 : Fin r) (x : Fin r → ℂ) :
    u₀.IsDiff (∑ l, x l • d l) (lft h (Mz.pt (∑ l, x l • a l))) := by
  classical
  have ht : ∀ a, IsTangent (lft h (Mz.pt a)) := fun a => isTangent_lft h (Mz.tan a)
  have hadd : ∀ a b, lft h (Mz.pt (a + b)) = lft h (Mz.pt a) * lft h (Mz.pt b) := fun a b => by
    rw [Mz.add, lft_mul]
  have hmul : ∀ {a b d d'}, u₀.IsDiff d (lft h (Mz.pt a)) → u₀.IsDiff d' (lft h (Mz.pt b)) →
      u₀.IsDiff (d + d') (lft h (Mz.pt (a + b))) := fun {a b d d'} e e' => by
    rw [hadd]
    exact GlobalTheory.UnifDifferential.isDiff_mul u₀ ((Chart.isTan_iff _).2 (ht a)) ((Chart.isTan_iff _).2 (ht b)) e e'
  have hsm : ∀ (c : ℂ) {a d}, u₀.IsDiff d (lft h (Mz.pt a)) → u₀.IsDiff (c • d) (lft h (Mz.pt (c • a))) :=
    fun c {a d} e => by
      refine GlobalTheory.CMNormIdentity.isDiff_of_isLieComb u₀ e c ⟨![lft h (Mz.pt (c • a))], fun i => ?_, by simp⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change (lft h (Mz.pt (c • a))).left = spMap (epsScaleR c) ≫ (lft h (Mz.pt a)).left
      refine h.1.hom_ext ?_ ?_
      · rw [lft_left, Category.assoc, lft_left]
        exact Mz.smul c a
      · have e1 : (lft h (Mz.pt (c • a))).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w _
        have e2 : (lft h (Mz.pt a)).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w _
        rw [e1, Category.assoc, e2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : (epsScaleR c).comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ (DualNumber ℂ) := by
          ext x <;> simp [epsScaleR]
        rw [this]
  have hz : u₀.IsDiff 0 (lft h (Mz.pt 0)) := by simpa using hsm 0 (hd i0)
  suffices H : ∀ s : Finset (Fin r), u₀.IsDiff (∑ l ∈ s, x l • d l) (lft h (Mz.pt (∑ l ∈ s, x l • a l))) from
    H Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | insert l s hl ih =>
    rw [Finset.sum_insert hl, Finset.sum_insert hl]
    exact hmul (hsm _ (hd l)) ih

theorem form_expand {g r : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (d : Fin r → Fin g → ℂ) (x y : Fin r → ℂ) :
    (Real.pi : ℂ) * ((∑ m, y m • d m) ⬝ᵥ Hm.mulVec (star (∑ l, x l • d l))) =
      ∑ m, (∑ l, star (x l) * ((Real.pi : ℂ) * (d m ⬝ᵥ Hm.mulVec (star (d l))))) * y m := by
  have e1 : star (∑ l, x l • d l) = ∑ l, star (x l) • star (d l) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun l _ => star_smul _ _
  have e2 : Hm.mulVec (∑ l, star (x l) • star (d l)) = ∑ l, star (x l) • Hm.mulVec (star (d l)) := by
    rw [← Matrix.mulVecLin_apply, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, Matrix.mulVecLin_apply]
  rw [e1, e2]
  simp only [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring

theorem gram_comb {L : LB G.left} (Mz : LieModel G z V) {r : ℕ} (a : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ)
    (i0 : Fin r) (hΓ : ∀ p q, HodgeIP G L z (Mz.pt (a p)) (Mz.pt (a q)) (Γ p q))
    (huniq : ∀ v w c c', HodgeIP G L z v w c → HodgeIP G L z v w c' → c = c') (C : Matrix (Fin r) (Fin r) ℂ) (p q : Fin r) :
    HodgeIP G L z (Mz.pt (∑ l, C l p • a l)) (Mz.pt (∑ l, C l q • a l)) ((Cᴴ * Γ * C) p q) := by
  obtain ⟨hLB, -, -, A₀, _, φ₀, g, u₀, Hm₀, χ₀, -, -, -, -, hpb, hAH, -, -, -, -, -⟩ := hΓ i0 i0
  have hc : ∀ l, ∃ d, u₀.IsDiff d (lft hpb (Mz.pt (a l))) := fun l => by
    obtain ⟨-, -, -, A, _, φ, g', u, Hm, χ, v', -, α, -, hpb', -, e1, -, d1, -, -⟩ := hΓ l l
    exact exists_coords hpb u₀ (Mz.tan _) hpb' u e1 d1
  choose d hd using hc
  have hw : ∀ x y : Fin r → ℂ, HodgeIP G L z (Mz.pt (∑ l, x l • a l)) (Mz.pt (∑ l, y l • a l))
      ((Real.pi : ℂ) * ((∑ m, y m • d m) ⬝ᵥ Hm₀.mulVec (star (∑ l, x l • d l)))) := fun x y =>
    ⟨hLB, Mz.tan _, Mz.tan _, A₀, _, φ₀, g, u₀, Hm₀, χ₀, lft hpb _, lft hpb _, _, _, hpb, hAH, lft_left hpb _,
      lft_left hpb _, isDiff_comb Mz hpb u₀ a d hd i0 x, isDiff_comb Mz hpb u₀ a d hd i0 y, rfl⟩
  have hτ : ∀ l m, (Real.pi : ℂ) * (d m ⬝ᵥ Hm₀.mulVec (star (d l))) = Γ l m := fun l m =>
    huniq _ _ _ _ ⟨hLB, Mz.tan _, Mz.tan _, A₀, _, φ₀, g, u₀, Hm₀, χ₀, lft hpb _, lft hpb _, _, _, hpb, hAH,
      lft_left hpb _, lft_left hpb _, hd l, hd m, rfl⟩ (hΓ l m)
  have := hw (fun l => C l p) (fun l => C l q)
  rw [form_expand] at this
  convert this using 1
  simp only [hτ, Matrix.mul_apply, Matrix.conjTranspose_apply]

end Gram

section Down

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem diag_eq {b₀ b b' : Fin r → E} (hb₀ : LinearIndependent Ω b₀) (P : Fin r → Fin r → Ω)
    (hP : ∀ k, b' k = ∑ l, P l k • b l) (hP0 : ∀ l k, k < l → P l k = 0)
    (hf : ∀ s, flagStep Ω b s = flagStep Ω b₀ s) (i : Fin r) {t t' : Ω}
    (h1 : b i - t • b₀ i ∈ flagStep Ω b₀ i) (h2 : b' i - t' • b₀ i ∈ flagStep Ω b₀ i) : P i i * t = t' := by
  classical
  have m1 : b' i - P i i • b i ∈ flagStep Ω b₀ i := by
    have e : b' i - P i i • b i = ∑ l ∈ Finset.univ.erase i, P l i • b l := by
      rw [hP i, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      abel
    rw [e]
    refine Submodule.sum_mem _ fun l hl => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hli | hli
    · exact Submodule.smul_mem _ _ (hf i ▸ Submodule.subset_span ⟨l, hli, rfl⟩)
    · rw [hP0 l i hli]
      simp
  have m2 : (t' - P i i * t) • b₀ i ∈ flagStep Ω b₀ i := by
    have e : (t' - P i i * t) • b₀ i =
        (b' i - P i i • b i) - (b' i - t' • b₀ i) + P i i • (b i - t • b₀ i) := by
      simp only [sub_smul, smul_sub, mul_smul]
      abel
    rw [e]
    exact add_mem (sub_mem m1 h2) (Submodule.smul_mem _ _ h1)
  obtain ⟨d, hd0, hx⟩ := GrNorm.exists_coeff_of_mem_flagStep m2
  have e2 : (Pi.single i (t' - P i i * t) : Fin r → Ω) = d :=
    GrNorm.coeff_eq_of_li hb₀ (by rw [← hx]; simp [Pi.single_apply, ite_smul])
  have e3 := congrFun e2 i
  rw [Pi.single_eq_same, hd0 i le_rfl] at e3
  exact (sub_eq_zero.1 e3).symm

end Down

section Norm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'}
  {f : X' ⟶ X} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {i : Ω →+* Ω'}
  {Li Li' : Type} [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li'] [Module Ω' Li']

def push (m : SABMap t' t f) {z : Sp ℂ ⟶ X'} (v : epsAt z ⟶ t'.G) : epsAt (z ≫ f) ⟶ t.G :=
  Over.homMk (v.left ≫ m.φ) (by
    have e := Over.w v
    simp only [Over.mk_hom] at e ⊢
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, e, Category.assoc])

theorem hodgeInnerProduct_unique (m : SABMap t' t f) {z : Sp ℂ ⟶ X'} (v w : epsAt z ⟶ t'.G) (c c' : ℂ)
    (h : HodgeIP t'.G t'.PP.L z v w c) (h' : HodgeIP t'.G t'.PP.L z v w c') : c = c' := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hodge_inner_product_pullback_unique E H X' X t' t f m z v w (push m v) (push m w) rfl rfl
  exact h2 c c' ((h1 c).1 h) ((h1 c').1 h')

theorem grNorm_down (m : SABMap t' t f) (hξ' : IsCptGen ξ') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i)
    (M : LieModel t.G ξ Li) (M' : LieModel t'.G ξ' Li') (j : Li →+ Li') (hj : IsExtOver i j)
    (hpt : ∀ e, (M'.pt (j e)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    (Vl : Lat ξ Li) {r : ℕ} (b₀ : Fin r → Li) (hb₀ : LinearIndependent Ω b₀) (idx : Fin r) (z : Sp ℂ ⟶ X')
    (hq : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) (b : Fin r → Li)
    (hbf : ∀ s, flagStep Ω b s = flagStep Ω b₀ s) (hbV : Vl.IsFrameAt b ⟨f (centre z), hp⟩)
    (hVL : Vl ⟨f (centre z), hp⟩ ≤ M.lat ⟨f (centre z), hp⟩) {t₁ : Ω'} {ν₁ : ℝ}
    (hn : M'.IsGrNorm t'.PP.L (Vl.pull ξ' f j) (fun k => j (b₀ k)) idx z t₁ ν₁) :
    ∃ (τ : Ω) (ν : ℝ) (c : Ω') (u : ℂ), M.IsGrNorm t.PP.L Vl b₀ idx (z ≫ f) τ ν ∧ u ≠ 0 ∧ ValAt ξ' z c u ∧
      t₁ = c * i τ ∧ ν₁ = ‖u‖ * ν := by
  classical
  obtain ⟨_, b', Γ', hfl', hfr', hti', ⟨v, hv, hI⟩, hpd', rfl⟩ := hn
  set p' : Cpt ξ' := ⟨centre z, hq⟩ with hp'

  have hmem : b idx ∈ flagStep Ω b₀ ((idx : ℕ) + 1) := by
    rw [← hbf]
    exact Submodule.subset_span ⟨idx, Nat.lt_succ_self _, rfl⟩
  obtain ⟨τ, hτ⟩ := GrNorm.exists_sub_mem_flagStep idx hmem

  have hfrJ := FlagPull.pull_isFrameAt hd hj p' hp hbV
  have hflJ := FlagPull.flagStep_map_eq hj.1 hbf
  obtain ⟨P, hP, hP0, hPu⟩ := GrNorm.frame_change (regAt ξ' p') hfr'.1 hfrJ.1 (hfr'.2.symm.trans hfrJ.2)
    fun s => (hfl' s).trans (hflJ s).symm

  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X' t'.G ℂ z
  obtain ⟨ev, hev1, hev2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X' t'.G Ω' ξ' Li' M' ℂ z hq Vz MR hξ' t'.semi.smooth
  let eA : X'.presheaf.stalk p'.1 ≃+* regAt ξ' p' :=
    RingEquiv.ofBijective (genMap ξ' p').rangeRestrict ⟨fun a b e => hξ'.inj p' (congrArg Subtype.val e),
      (genMap ξ' p').rangeRestrict_surjective⟩
  let φ : regAt ξ' p' →+* ℂ := (Scheme.stalkClosedPointTo z).hom.comp (eA.symm : regAt ξ' p' →+* X'.presheaf.stalk p'.1)
  have hφ : ∀ a : regAt ξ' p', ValAt ξ' z (a : Ω') (φ a) := fun a =>
    ⟨hq, eA.symm a, congrArg Subtype.val (eA.apply_symm_apply a), rfl⟩
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
  have hb'L : ∀ k, b' k ∈ M'.lat p' := fun k => (hpick _ _ (hv k)).1
  have hvk : ∀ k, v k = MR.pt (val (b' k)) := fun k => (hpick _ _ (hv k)).2
  let C : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun l k => φ (P l k)
  have hJval : ∀ k, val (j (b k)) = ∑ l, C l k • val (b' l) := fun k => by
    rw [hP k]
    exact GrNorm.val_sum h0 hadd hsmul hb'L (fun l => P l k) Finset.univ
  have hgram := gram_comb MR (fun l => val (b' l)) Γ' idx (fun p q => by
    rw [← hvk, ← hvk]
    exact hI p q) (hodgeInnerProduct_unique m) C

  have hbL : ∀ k, b k ∈ M.lat ⟨f (centre z), hp⟩ := fun k => hVL (hbV.2 ▸ Submodule.subset_span ⟨k, rfl⟩)
  have hdown := fun k => value_pull (M' := M') (j := j) hd m.cart hpt hq hp (hbL k)
  choose w w' hw hw' hww using hdown
  have hw'e : ∀ k, w' k = MR.pt (val (j (b k))) := fun k => (hpick _ _ (hw' k)).2
  have hC : ∀ l k, k < l → C l k = 0 := fun l k hkl => by simp [C, hP0 l k hkl]
  have hCd : ∀ k, C k k ≠ 0 := fun k => ((hPu k).map φ).ne_zero
  have hdet : C.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun a c hac => hC a c hac)]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hCd k
  have hinj : Function.Injective C.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hdet))
  have hu0 : ((P idx idx : regAt ξ' p') : Ω') ≠ 0 := fun h => by
    have := (hPu idx).ne_zero
    exact this (Subtype.ext h)
  have hdiag := diag_eq (hj.2 r b₀ hb₀) (fun l k => (P l k : Ω')) hP (fun l k h => by rw [hP0 l k h]; rfl)
    hfl' idx hti' (by
      have := FlagPull.map_mem_flagStep hj.1 b₀ idx hτ
      rwa [map_sub, hj.1] at this)
  refine ⟨τ, _, ((P idx idx : regAt ξ' p') : Ω')⁻¹, (C idx idx)⁻¹,
    ⟨hp, b, Cᴴ * Γ' * C, hbf, hbV, hτ, ⟨w, hw, fun p q => ?_⟩, hpd'.conjTranspose_mul_mul_same hinj, rfl⟩,
    inv_ne_zero (hCd idx), CxVal.inv (hφ _) (hCd idx), ?_, ?_⟩
  · refine ((GlobalTheory.T.hodge_inner_product_pullback_unique E H X' X t' t f m z (w' p) (w' q) (w p) (w q) (hww p) (hww q)).1 _).1 ?_
    rw [hw'e, hw'e, hJval, hJval]
    exact hgram p q
  · rw [← hdiag]
    exact (inv_mul_cancel_left₀ hu0 t₁).symm
  · rw [GrNorm.sqrt_ratio_conj Γ' C hC hCd idx, norm_inv, inv_mul_cancel_left₀ (norm_ne_zero_iff.2 (hCd idx))]

end Norm

section Sec

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X}
  {i : Ω →+* Ω'} {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
  [∀ k, Fintype (J' k)] {κ : K → K'} {v : (Σ k, J k) → (Σ k, J' k)} {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}

theorem secNorm_pull (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hv : AI.I1.IsBlockMap κ v) (hy : ∀ q, y' (v q) = i (y q))
    {L : HermLine J} {L' : HermLine J'} (hP : AI.I4.IsPullHerm κ v L L') {e₀ : Ω} {z : Sp ℂ ⟶ X'}
    (hq : genPt ξ' ⤳ centre z) {w : (Σ k, J' k) → ℂ} (hw : CoordsAt ξ' y' z w) {τ : Ω} {nn : ℝ}
    (h : SecNorm ξ y L e₀ (z ≫ f) (fun p => w (v p)) τ nn) {c : Ω'} {u : ℂ} (hu : ValAt ξ' z c u) (hu0 : u ≠ 0)
    (n : ℤ) : SecNorm ξ' y' L' (i e₀) z w (c ^ n * i τ) (‖u‖ ^ n * nn) := by
  obtain ⟨he, -, hs⟩ := h
  refine ⟨(map_ne_zero i).2 he, hw, fun c' hc' => ?_⟩
  obtain ⟨d, hdv⟩ := FlagPull.exists_chart hv c'
  have hdn : ∀ k, (fun p => w (v p)) ⟨k, d k⟩ ≠ 0 := fun k => by
    show w (v ⟨k, d k⟩) ≠ 0
    rw [hdv k]
    exact hc' _
  obtain ⟨u₁, h1, h2⟩ := hs d hdn
  have h2' : nn * L.h (fun p => w (v p)) = ‖u₁‖ * ∏ k, ‖w (v ⟨k, d k⟩)‖ ^ L.a k := h2
  have h3 := valAt_pull hd hq h1
  refine ⟨u ^ n * u₁, ?_, ?_⟩
  · have e : c ^ n * i τ / ((∏ k', y' ⟨k', c' k'⟩ ^ L'.a k') * i e₀) =
        c ^ n * i (τ / ((∏ k, y ⟨k, d k⟩ ^ L.a k) * e₀)) := by
      rw [hP.1, FlagPull.monomial_pull hv hy L.a hdv, map_div₀, map_mul, mul_div_assoc]
    rw [e]
    exact CxVal.mul (CxVal.zpow hu hu0 n) h3
  · have e1 : ∏ k', ‖w ⟨k', c' k'⟩‖ ^ L'.a k' = ∏ k, ‖w (v ⟨k, d k⟩)‖ ^ L.a k := by
      rw [hP.1]
      exact FlagPull.monomial_pull (i := RingHom.id ℝ) (y := fun p => ‖w (v p)‖) (y' := fun p => ‖w p‖) hv
        (fun _ => rfl) L.a hdv
    rw [hP.2 w, e1, norm_mul, norm_zpow, _root_.mul_assoc, h2', _root_.mul_assoc]

end Sec

theorem hodgeLine_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (h : A'.X ⟶ A.X) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t h) (κ : K → K') (v : (Σ k, J k) → (Σ k, J' k)) (Fl : A.Flag), AI.I1.IsBlockMap κ v → (∀ q, y' (v q) = i (y q)) → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ h i → A'.f = h ≫ A.f → A'.m.φ = m.φ ≫ A.m.φ → A'.cst = i.comp A.cst → IsExtOver i j → (∀ w, (A'.M.pt (j w)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt w).left) → (∀ s, A'.V s = (A.V s).pull A'.ξ h j) → ∀ Fl' : A'.Flag, (∀ s k, Fl'.b s k = j (Fl.b s k)) → ∀ r (e₀ : Ω) (L : HermLine J) (L' : HermLine J'), Fl.IsHodgeLine r e₀ L → AI.I4.IsPullHerm κ v L L' → Fl'.IsHodgeLine r (i e₀) L' := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ i K K' _ _ J J' _ _ y y' A A' g j m κ v Fl hv hy hdom _ _ _ hext hpt hV
    Fl' hb r e₀ L L' hL hP z w hco hint t₁ ν₁ hn
  have hq : genPt A'.ξ ⤳ centre z := A'.all _
  have hp : genPt A.ξ ⤳ g (centre z) := A.all _
  have hξ' := A'.tie.gen
  have hξ := A.tie.gen
  obtain ⟨U, hU, b, hbf, hfr⟩ := Fl.sub (HodgeCpt.rootIdx D r).1 ⟨g (centre z), hp⟩ trivial
  have hbV := hfr ⟨g (centre z), hp⟩ trivial hU
  have hb' : Fl'.b (HodgeCpt.rootIdx D r).1 = fun k => j (Fl.b (HodgeCpt.rootIdx D r).1 k) := funext (hb _)
  rw [hV, hb'] at hn
  have hVL : A.V (HodgeCpt.rootIdx D r).1 ⟨g (centre z), hp⟩ ≤ A.M.lat ⟨g (centre z), hp⟩ := by
    have hnot : ∀ p ∈ S, ¬ InFibre A.ξ p ⟨g (centre z), hp⟩ := fun p hpS =>
      GrNorm.not_inFibre hξ (z := z ≫ g) hp (A.S_prime p hpS)
    show Lat.patch S (A.dR _) (fun p => A.HT p _) _ ≤ _
    rw [Lat.patch_of_not S _ _ hnot]
    exact inf_le_left
  have hb₀ : LinearIndependent Ω (Fl.b (HodgeCpt.rootIdx D r).1) := by
    letI := A.fn.toAlgebra
    obtain ⟨_, _, _, _, _, hli, _⟩ := Fl.generic
    exact hli _
  obtain ⟨τ, ν, c₀, u, hgn, hu0, hcv, ht, hν⟩ := grNorm_down m hξ' hdom A.M A'.M j hext hpt (A.V _) _ hb₀ _ z hq hp b
    hbf hbV hVL hn
  have hco' := coordsAt_pull hdom hξ' A.tie.cover hv hy hq hp hco
  have hint' : A.Interior (z ≫ g) := (abLocus_pullback abLocusOne A.t.semi m.cart.1 _).2 hint
  have hs := hL (z ≫ g) _ hco' hint' τ ν hgn
  have hfin := secNorm_pull hdom hv hy hP hq hco hs hcv hu0 (HodgeCpt.rootSgn D r)
  rw [ht, hν, mul_zpow, mul_zpow, ← map_zpow₀]
  exact hfin

end GlobalTheory.CompanionTheory.Ar.HodgePull
