import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedIotaGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.Gen0

section General

variable {X Y : Scheme.{0}}

def fs {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : FreeAbelianGroup (Y ⟶ X) :=
  ∑ k, ε k • FreeAbelianGroup.of (φ k)

theorem formEq_of_fs {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : fs φ ε = fs φ' ε') : FormEq φ ε φ' ε' := by
  intro U _ g
  have e := congrArg (FreeAbelianGroup.lift (fun ψ => Additive.ofMul (g ψ))) h
  simp only [fs, map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of] at e
  apply Additive.ofMul.injective
  simpa [ofMul_prod, ofMul_zpow] using e

theorem oneGen_isGen' (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

def genSub (L : LB X) (Y : Scheme.{0}) : AddSubgroup (FreeAbelianGroup (Y ⟶ X)) where
  carrier := {f | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), fs φ ε = f ∧
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen}
  zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, by simp [fs], LB.oneGen L, oneGen_isGen' L⟩
  add_mem' := by
    rintro _ _ ⟨K, _, φ, ε, rfl, t, ht⟩ ⟨K', _, φ', ε', rfl, t', ht'⟩
    exact ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', by simp [fs, Fintype.sum_sum_type],
      LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen L φ ε φ' ε' t t' ht ht'⟩
  neg_mem' := by
    rintro _ ⟨K, _, φ, ε, rfl, t, ht⟩
    exact ⟨K, inferInstance, φ, fun k => - ε k, by simp [fs, neg_smul, Finset.sum_neg_distrib],
      LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

variable {L : LB X}

theorem mem_of_gen {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) : fs φ ε ∈ genSub L Y := ⟨K, inferInstance, φ, ε, rfl, t, ht⟩

theorem gen_of_mem (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : fs φ ε ∈ genSub L Y) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨K', _, φ', ε', e, t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL (formEq_of_fs e) t ht
  exact ⟨t', ht'⟩

theorem exists_cl (hL : L.IsLB) (Y : Scheme.{0}) : ∃ (U : Type) (_ : CommGroup U) (c : (Y ⟶ X) → U),
    ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ),
      (∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) ↔ ∏ k, c (φ k) ^ ε k = 1 := by
  refine ⟨Multiplicative (FreeAbelianGroup (Y ⟶ X) ⧸ genSub L Y), inferInstance,
    fun ψ => Multiplicative.ofAdd (QuotientAddGroup.mk' _ (FreeAbelianGroup.of ψ)), fun K _ φ ε => ?_⟩
  have e : ∏ k, Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (FreeAbelianGroup.of (φ k))) ^ ε k =
      Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (fs φ ε)) := by
    simp only [fs, map_sum, map_zsmul, ofAdd_sum, ofAdd_zsmul]
  rw [e, ofAdd_eq_one, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨fun ⟨t, ht⟩ => mem_of_gen t ht, gen_of_mem hL⟩

end General

section Deg

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_gen_twist [IsLocalRing R] (a : D.P.A ⟶ D.P.A) [IsMonHom a] (n j : ℤ) (mu ν δ β : D.X)
    (hν : D.c ν = D.c mu ≫ a) (u : LB.Gen (IotaLB D a ν δ)) (hu : u.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a (β + (n • mu + j • δ)))
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a β k)) (dε n j)), u₀.IsGen := by
  obtain ⟨U, _, c, hc⟩ := exists_cl D.P.isLB D.P.A.left
  have k₀ : ∀ q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, c (toUnit D.P.A ≫ q).left = 1 := fun q => by
    obtain ⟨t, ht⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := PUnit) (fun _ => q.left) (fun _ => 1)
    have h := (hc PUnit (fun _ => (toUnit D.P.A).left ≫ q.left) (fun _ => 1)).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩
    rw [Fintype.prod_unique, zpow_one] at h
    exact h
  have k₁ : c (1 : D.P.A ⟶ D.P.A).left = 1 := k₀ _
  have k₂ : ∀ χ, c (DVR.cP D D.P.A χ).left = 1 := fun χ => k₀ _
  have sq : ∀ χ χ', c (𝟙 _ * DVR.cP D D.P.A (χ + χ')).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left =
      c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (c (𝟙 _ * DVR.cP D D.P.A χ').left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ χ' => by
    have h := (prod_cub (𝟙 D.P.A) (DVR.cP D _ χ) (DVR.cP D _ χ') c).symm.trans ((hc thK _ thε).1
      ⟨LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t _, DVR.pullGen_isGen _ _ _ _ D.cub.isGen _⟩)
    rw [_root_.mul_assoc (𝟙 D.P.A), ← DVR.cPoint_add, k₂, k₂, k₂, k₁] at h
    rw [← div_eq_one, ← h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
    abel
  let Φ : D.X →+ Additive U := AddMonoidHom.mk' (fun χ => Additive.ofMul
    (c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left)) (fun χ χ' => congrArg Additive.ofMul (sq χ χ'))
  have e : ∀ χ, Additive.ofMul (c (𝟙 _ * DVR.cP D D.P.A χ).left) =
      Φ χ + Additive.ofMul (c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ =>
    congrArg Additive.ofMul (div_mul_cancel _ _).symm
  clear_value Φ
  have e₃ : Additive.ofMul (c (a * DVR.cP D _ ν).left) = Φ δ + Additive.ofMul (c a.left) := by
    have h := (hc _ _ _).1 ⟨u, hu⟩
    rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four] at h
    have h' : c (𝟙 _ * DVR.cP D D.P.A δ).left ^ (1 : ℤ) * c (DVR.cP D D.P.A δ).left ^ (-1 : ℤ) *
        c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) *
        (c (a * DVR.cP D D.P.A ν).left ^ (-1 : ℤ) * c (DVR.cP D D.P.A ν).left ^ (1 : ℤ) * c a.left ^ (1 : ℤ) *
          c (1 : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ)) = 1 := h
    have h'' := congrArg Additive.ofMul h'
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, ofMul_one] at h''
    rw [eq_comm, ← sub_eq_zero, ← h'']
    module
  let T : D.P.A ⟶ D.P.A := 𝟙 _ * DVR.cP D _ mu
  have i₀ : T ≫ 𝟙 _ = 𝟙 _ * DVR.cP D _ mu := Category.comp_id _
  have i₁ : T ≫ (𝟙 _ * DVR.cP D _ β) = 𝟙 _ * DVR.cP D _ (mu + β) := by
    rw [MonObj.comp_mul, DVR.comp_cP, i₀, DVR.cPoint_add, _root_.mul_assoc]
  have i₂ : T ≫ DVR.cP D _ β = DVR.cP D _ β := DVR.comp_cP D _ _
  have i₃ : T ≫ (1 : D.P.A ⟶ D.P.A) = 1 := MonObj.comp_one _
  have i₄ : T ≫ a = a * DVR.cP D _ ν := by
    rw [MonObj.mul_comp, Category.id_comp, DVR.cP, DVR.cP, hν, Category.assoc]
  have h : c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * c (𝟙 _ * DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (1 : ℤ) *
      c (DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) * c a.left ^ j *
      (c (T ≫ 𝟙 _).left ^ (-(n - 1)) * c (T ≫ (𝟙 _ * DVR.cP D _ β)).left ^ (-1 : ℤ) *
        c (T ≫ DVR.cP D _ β).left ^ (-(-1) : ℤ) * c (T ≫ (1 : D.P.A ⟶ D.P.A)).left ^ (-1 : ℤ) * c (T ≫ a).left ^ (-j)) = 1 := by
    rw [i₀, i₁, i₂, i₃, i₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, e₃, ofMul_one, map_add, map_zsmul]
    module
  refine (hc _ _ _).2 ?_
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_five]
  exact h

end Deg

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (mu β β' : D.toPre.X), β' = β + shift h h' n j mu → ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j)), u₀.IsGen := by
  intro R _ _ _ hR D a a' h h' hE n j mu β β' hβ
  obtain ⟨u, hu, -⟩ := exists_iota R hR D a a' h h' hE (h mu)
  haveI := hE.1
  subst hβ
  exact exists_gen_twist D.toPre a n j mu (h mu) (h' (h mu)) β (hE.2.2.2.1 mu) u hu

end GlobalTheory.TwFam.Gen0
