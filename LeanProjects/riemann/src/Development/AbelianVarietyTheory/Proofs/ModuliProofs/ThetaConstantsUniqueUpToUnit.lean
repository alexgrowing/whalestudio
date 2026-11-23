import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaUniq

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

theorem exists_unit_of_local {R I : Type} [CommRing R] {v v' : I → R} (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∀ (q : Ideal R) [q.IsMaximal], ∃ u : (Localization.AtPrime q)ˣ, ∀ a,
      algebraMap R (Localization.AtPrime q) (v' a) = u * algebraMap R (Localization.AtPrime q) (v a)) :
    ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 ((Ideal.eq_top_iff_one _).1 hv)
  have key : ∀ (q : Ideal R) [q.IsMaximal], ∃ u : (Localization.AtPrime q)ˣ,
      algebraMap R (Localization.AtPrime q) (c.sum fun i a => a * v' i) = u ∧ ∀ a,
      algebraMap R (Localization.AtPrime q) (v' a) = u * algebraMap R (Localization.AtPrime q) (v a) := fun q _ => by
    obtain ⟨u, hu⟩ := h q
    refine ⟨u, ?_, hu⟩
    have e := congrArg (algebraMap R (Localization.AtPrime q)) hc
    simp only [Finsupp.sum, map_sum, map_mul, map_one] at e ⊢
    simp only [hu, mul_left_comm _ (u : Localization.AtPrime q)]
    rw [← Finset.mul_sum, e, _root_.mul_one]
  have hu : IsUnit (c.sum fun i a => a * v' i) := by
    by_contra hn
    obtain ⟨q, hq, hm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hn)
    obtain ⟨u, e, -⟩ := key q
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).1 (e ▸ u.isUnit) hm
  refine ⟨hu.unit, fun a => Module.eq_of_localization_maximal (R := R) (fun q _ => Localization.AtPrime q)
    (fun q _ => Algebra.linearMap R (Localization.AtPrime q)) _ _ fun q _ => ?_⟩
  obtain ⟨u, e, e'⟩ := key q
  rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_mul, IsUnit.unit_spec, e, e']

theorem exists_ratio_base {X Y S₀ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = val u' r z J * gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := SymLiftOdd.exists_const hL p e he hp (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))
  refine ⟨c, fun Z r z J hJ => ?_⟩
  rw [← hc Z r z J hJ, val_mul hJ, val_inv, mul_comm, inv_mul_cancel_right]

variable {S : Scheme.{0}} {T : Over S}

theorem exists_unit_of_isGenSec_local {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} [IsLocalRing Γ(T.left, ⊤)]
    {th th' : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (H' : IsGenSec A L k th') :
    ∃ u : Γ(T.left, ⊤)ˣ, SecM.ofSec A th = (u : Γ(T.left, ⊤)) • SecM.ofSec A th' := by
  obtain ⟨r, hr⟩ := H' th
  obtain ⟨r', hr'⟩ := H th'
  have e : SecM.ofSec A th = r • SecM.ofSec A th' := Subtype.ext (funext hr)
  have e' : SecM.ofSec A th' = r' • SecM.ofSec A th := Subtype.ext (funext hr')
  by_cases hu : IsUnit r
  · exact ⟨hu.unit, e⟩
  have h₁ : IsUnit (1 - r * r') :=
    (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left fun h => hu (isUnit_of_mul_isUnit_left h)
  have h₂ : SecM.ofSec A th = 0 := h₁.smul_eq_zero.1 (by rw [sub_smul, one_smul, mul_smul, ← e', ← e, sub_self])
  exact ⟨1, by rw [e', h₂, smul_zero, smul_zero]⟩

theorem exists_unit_over (hG : GlobalFnsSt) (P : PolAV S) [IsLocalRing Γ(T.left, ⊤)] {k : ℕ} (hk : Odd k) {I : Type}
    {x : I → (T ⟶ P.A)} {v v' : I → Γ(T.left, ⊤)} (H : IsThetaPtOver P k x v) (H' : IsThetaPtOver P k x v') :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ i, v' i = u * v i := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨th', s₁', α', τ', U', s₂', w', u', hth', hα', hτ', hs₁', hU', hs₂', hw', hv'⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec_local hth' hth
  obtain ⟨c, hc⟩ := exists_ratio_base hL (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (SymLiftOdd.surj_fst hG P.isAb T) hα' hα
  obtain ⟨d, hd⟩ := exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun a => ⟨a, rfl⟩) hτ hτ'
  have key : ∀ i, w' i = (ρ * c * d : Γ(T.left, ⊤)ˣ) * w i := fun i => fn_ext fun z _ => by
    choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart hL (χ z)
    replace hJ : Good P.L z J := hJ
    have a₀ : tval (U' i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J = tval (U i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      val_corr hJ (SymLiftOdd.symLift_unique hG P.isAb hL hk.pow _ _ (hU' i) (hU i)) _
    have a₁ : bval (b := 1) α' (lift (𝟙 T) (x i)).left z J =
        bval (b := 1) α (lift (𝟙 T) (x i)).left z J * gm (𝟙 T.left) z ⊤ c := by
      have := hc _ (lift (𝟙 T) (x i)).left z J hJ
      rw [lift_fst_left] at this
      exact this
    have a₂ := hd _ (𝟙 _) z J hJ
    have a₃ : sv P.A th' (lift (𝟙 T) (x i ^ k)).left z J =
        gs (𝟙 T.left) z ⊤ ρ * sv P.A th (lift (𝟙 T) (x i ^ k)).left z J := by
      have := ThetaAct.sv_smul (ρ : Γ(T.left, ⊤)) (SecM.ofSec P.A th) (lift (𝟙 T) (x i ^ k)).left z hJ
      rw [← hρ, lift_fst_left] at this
      exact this
    have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 T) hJ 1
    have b₂ := sv_mulPull hs₁ (𝟙 T) hJ (x i)
    have b₃ := sv_of_isValueAt (hw i) (𝟙 T) hJ
    have c₁ := sv_act (hU' i).pt_eq (hs₂' i) (𝟙 T) hJ 1
    have c₂ := sv_mulPull hs₁' (𝟙 T) hJ (x i)
    have c₃ := sv_of_isValueAt (hw' i) (𝟙 T) hJ
    rw [Category.id_comp, _root_.mul_one] at b₁ c₁
    rw [Category.id_comp] at b₃ c₃ a₂
    rw [b₃, b₂] at b₁
    rw [c₃, c₂, a₀, a₁, a₃] at c₁
    simp only [Over.id_left] at b₁ c₁
    rw [a₂] at b₁
    refine (Units.mul_left_inj (val τ' (𝟙 T.left) z J)).1 ?_
    rw [c₁, gs_mul _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, map_mul, map_mul]
    simp only [Units.val_mul] at b₁ ⊢
    linear_combination (-(gm (𝟙 T.left) z ⊤ ρ).val * (gm (𝟙 T.left) z ⊤ c).val) * b₁
  refine ⟨u' * (ρ * c * d) * u⁻¹, fun i => ?_⟩
  rw [hv', hv, key, Units.val_mul _ u⁻¹, _root_.mul_assoc _ _ (u * w i), Units.inv_mul_cancel_left, Units.val_mul u',
    _root_.mul_assoc (u' : Γ(T.left, ⊤))]

theorem isThetaPtOver_of_local (P : PolAV S) {R : Type} [CommRing R] [IsLocalRing R] (y : Sp R ⟶ S) {n : ℕ} {I : Type}
    {x : I → (Over.mk y ⟶ P.A)} {v : I → Γ((Over.mk y).left, ⊤)} (H : IsThetaPt P n x v) : IsThetaPtOver P n x v := by
  obtain ⟨V, hp, H'⟩ := H.2.2 (IsLocalRing.closedPoint R)
  obtain rfl : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  let h : Over.mk y ⟶ overRes (T := Over.mk y) ⊤ := Over.homMk (Sp R).topIso.inv (by
    show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ y = y
    rw [Scheme.toIso_inv_ι_assoc])
  have hh : h ≫ overResι ⊤ = 𝟙 _ := Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))
  have := isThetaPtOver_pull P H' h (overResι ⊤) hh
  convert this using 2 with a a
  · rw [← Category.assoc, hh, Category.id_comp]
  · have q := congrArg (fun q => q.left.appTop.hom (v a)) hh
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
      Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
    exact q.symm

theorem exists_unit_local (hG : GlobalFnsSt) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S)
    {v v' : Ix g (N' ^ 2) → R} (H : t.HasTh x v) (H' : t.HasTh x v') : ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  let e : Γ(Sp R, ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := e.symm.isLocalRing
  obtain ⟨u, hu⟩ := exists_unit_over hG t.pol H.1 (isThetaPtOver_of_local _ x H) (isThetaPtOver_of_local _ x H')
  refine ⟨Units.map e.toMonoidHom u, fun a => ?_⟩
  have q := (congrArg e (hu a)).trans (map_mul e _ _)
  exact (e.apply_symm_apply (v' a)).symm.trans (q.trans (congrArg (_ * ·) (e.apply_symm_apply (v a))))

end GlobalTheory.ThetaUniq

namespace GlobalTheory

theorem hasTh_unique_unit : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh x v' → Ideal.span (Set.range v) = ⊤ → ∃ u : Rˣ, ∀ a, v' a = u * v a :=
  fun h₁ h₂ o _ g N' J b S s t R _ x v v' H H' hv => ThetaUniq.exists_unit_of_local hv fun q _ =>
    ThetaUniq.exists_unit_local h₁.globalFns t _
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ (algebraMap R (Localization.AtPrime q)) x v H)
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ (algebraMap R (Localization.AtPrime q)) x v' H')

end GlobalTheory
