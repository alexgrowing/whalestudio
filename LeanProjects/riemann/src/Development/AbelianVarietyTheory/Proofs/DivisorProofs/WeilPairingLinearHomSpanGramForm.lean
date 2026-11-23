import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLamEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersActionInjectiveOnAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamObjGoodOfCmObj
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType

set_option autoImplicit false

noncomputable section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

section Calc

variable {S : Scheme.{0}} {X Y A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj C] [IsCommMonObj C] {L : LB A.left} {M : LB B.left} {N : LB C.left}

theorem lamEq_symm' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq M g₁ g₂ L f₁ f₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).1

theorem lamEq_swap' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq L f₂ f₁ M g₂ g₁ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.1

theorem lamEq_trans' (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B}
    {g₂ : Y ⟶ B} {k₁ : X ⟶ C} {k₂ : Y ⟶ C} (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq M g₁ g₂ N k₁ k₂) :
    LamEq L f₁ f₂ N k₁ k₂ :=
  ((LamCalc.lamEq_calculus S X Y A B C L M N hL hM hN f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ k₁ k₂).2.1 h).2.2.1 h'

theorem lamEq_pre (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) {X' Y' : Over S} (a : X' ⟶ X) (b : Y' ⟶ Y) :
    LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂) :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.2.2.1 X' Y' a b

variable (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen)
include hL hM hT hT'

theorem lamEq_mul_left' {f₁ f₁' : X ⟶ A} {f₂ : Y ⟶ A} {g₁ g₁' : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq L f₁' f₂ M g₁' g₂) : LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁' f₂ f₂ g₁ g₁' g₂ g₂ g₁ g₂).2.2.1 hT hT' h).1 h'

theorem lamEq_prod_left {J : Type} (s : Finset J) (f : J → (X ⟶ A)) (g : J → (X ⟶ B)) (f₂ : Y ⟶ A) (g₂ : Y ⟶ B)
    (h0 : LamEq L (1 : X ⟶ A) f₂ M (1 : X ⟶ B) g₂) (h : ∀ i ∈ s, LamEq L (f i) f₂ M (g i) g₂) :
    LamEq L (s.prod f) f₂ M (s.prod g) g₂ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM (f i) (s.prod f) f₂ f₂ (g i) (s.prod g) g₂ g₂
      (g i) g₂).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).1
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lamEq_prod_right {J : Type} (s : Finset J) (f₁ : X ⟶ A) (g₁ : X ⟶ B) (f : J → (Y ⟶ A)) (g : J → (Y ⟶ B))
    (h0 : LamEq L f₁ (1 : Y ⟶ A) M g₁ (1 : Y ⟶ B)) (h : ∀ i ∈ s, LamEq L f₁ (f i) M g₁ (g i)) :
    LamEq L f₁ (s.prod f) M g₁ (s.prod g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ (f i) (s.prod f) g₁ g₁ (g i) (s.prod g)
      g₁ (g i)).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).2
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Calc

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G)

theorem act_zero' : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have := congrArg (fun u => (act.act 0)⁻¹ * u) h
  simpa using this.symm

theorem act_sum' {J : Type} (s : Finset J) (c : J → O) : act.act (s.sum c) = s.prod fun i : J => act.act (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using act_zero' act
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, act.add, ih]

end Act

theorem exists_thetaGen' (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) :
    ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hL.cube S P ⟨P.L, ρ, P.isLB, hρ⟩ rfl
  exact ⟨c.t, c.isGen⟩

theorem weilEq_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (m : ℕ), 0 < m → ∀ (z : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ (x : Fin p → 𝓞 E) (r : 𝓞 E), (m : 𝓞 E) * r = ∑ a, ∑ b, z a * gP a b * (H.bar (x b) : 𝓞 E) →
    GlobalTheory.CM.WeilEq X.B.t.PP.L f (∏ b, ((X.A true).t.act.act (x b) ≫ GlobalTheory.FlatCM.phiP X b))
      (X.A true).t.PP.L ((X.A true).t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG m hm z f hf hfm x r hr
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  have hβ : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have lA : (X.A true).t.PP.L.IsLB := (X.A true).t.PP.isLB
  have lB : X.B.t.PP.L.IsLB := X.B.t.PP.isLB
  have tA := exists_thetaGen' hL (X.A true).pol
  have tB := exists_thetaGen' hL X.B.pol
  haveI : IsMonHom f := hf.1
  haveI hφ : ∀ a, IsMonHom (phiP X a) := fun a => (X.lin (Sum.inl a)).1
  haveI hact : ∀ s, IsMonHom ((X.A true).t.act.act s) := (X.A true).t.act.hom
  have toLam : ∀ (f₁ f₂ : (X.A true).t.G ⟶ X.B.t.G) (g₁ g₂ : (X.A true).t.G ⟶ (X.A true).t.G), IsMonHom f₁ →
      IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
      WeilEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
      LamEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ := fun f₁ f₂ g₁ g₂ h₁ h₂ h₃ h₄ h =>
    (PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) (X.A true).pol (X.A true).pol X.B.pol (X.A true).pol f₁ f₂ g₁ g₂
      h₁ h₂ h₃ h₄ ℂ _).2 inferInstance hβ h

  have E1 : ∀ a b, LamEq X.B.t.PP.L ((X.A true).t.act.act (z a) ≫ phiP X a) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro a b
    have := lamEq_pre lB lA (toLam _ _ _ _ (hφ a) (hφ b) (hact _) inferInstance (hG.1 a b))
      ((X.A true).t.act.act (z a)) ((X.A true).t.act.act (x b))
    rwa [← (X.A true).t.act.mul, Category.comp_id] at this

  have S1 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (∑ a, z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro b
    have h0 : LamEq X.B.t.PP.L (1 : (X.A true).t.G ⟶ X.B.t.G) ((X.A true).t.act.act (x b) ≫ phiP X b)
        (X.A true).t.PP.L (1 : (X.A true).t.G ⟶ (X.A true).t.G) ((X.A true).t.act.act (x b)) := by
      have := lamEq_pre lB lA (E1 b b) (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
    have := lamEq_prod_left lB lA tB tA Finset.univ (fun a => (X.A true).t.act.act (z a) ≫ phiP X a)
      (fun a => (X.A true).t.act.act (z a * gP a b)) _ _ h0 (fun a _ => E1 a b)
    rwa [← hfm, ← act_sum'] at this

  have M1 : ∀ t y : 𝓞 E, LamEq (X.A true).t.PP.L ((X.A true).t.act.act t) ((X.A true).t.act.act y)
      (X.A true).t.PP.L ((X.A true).t.act.act (t * H.bar y)) (𝟙 _) := by
    intro t y
    have h2 := lamEq_pre lA lA (lamEq_swap' lA lA (LamF.lamEq_adj (X.A true).t y)) ((X.A true).t.act.act t) (𝟙 _)
    rwa [Category.comp_id, Category.id_comp, Category.id_comp, ← (X.A true).t.act.mul] at h2
  have F2 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b) (X.A true).t.PP.L (𝟙 _)
      ((X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) := fun b =>
    lamEq_trans' lB lA lA (lamEq_trans' lB lA lA (S1 b) (M1 _ _)) (LamF.lamEq_adj (X.A true).t _)

  obtain ⟨r', hr'⟩ := GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP f
    (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) hf (isLinearHom_prod X x)
  haveI hψ : IsMonHom (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) := (isLinearHom_prod X x).1
  have R := toLam _ _ _ _ inferInstance hψ (hact r') inferInstance hr'
  have Rm : ∀ n : ℕ, LamEq X.B.t.PP.L (f ^ n) (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act ((n : 𝓞 E) * r')) (𝟙 _) := by
    intro n
    induction n with
    | zero =>
      have := lamEq_pre lB lA R (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rw [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
      rwa [pow_zero, Nat.cast_zero, zero_mul, act_zero']
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ, add_mul, _root_.one_mul, (X.A true).t.act.add]
      exact lamEq_mul_left' lB lA tB tA ih R
  have RmA := lamEq_trans' lB lA lA (Rm m) (LamF.lamEq_adj (X.A true).t ((m : 𝓞 E) * r'))
  have base2 : LamEq X.B.t.PP.L (f ^ m) (1 : (X.A true).t.G ⟶ X.B.t.G) (X.A true).t.PP.L (𝟙 _)
      (1 : (X.A true).t.G ⟶ (X.A true).t.G) := by
    have := lamEq_pre lB lA RmA (𝟙 _) (1 : (X.A true).t.G ⟶ (X.A true).t.G)
    rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
  have S2 := lamEq_prod_right lB lA tB tA Finset.univ (f ^ m) (𝟙 _)
    (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) base2 (fun b _ => F2 b)
  have hsum : (∑ b, H.bar ((∑ a, z a * gP a b) * H.bar (x b))) = H.bar ((m : 𝓞 E) * r) := by
    rw [hr, ← map_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [← act_sum', hsum] at S2

  have U := lamEq_swap' lA lA (lamEq_trans' lA lB lA (lamEq_symm' lB lA S2) RmA)
  have e₁ := PairingInj.eq_of_lamEq hL _ (X.A true).pol _ _ _ U
  have hg : 1 ≤ (X.A true).pol.g := NumInh.dim_pos_of_hasType X.split X.ρ_sq (X.A true) X.typeP
  have e₂ := H.bar.injective (LamF.Faithful.act_injective hL E K (X.A true).pol (X.A true).t.act hg e₁)
  have e₃ : r = r' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hm.ne' : (m : 𝓞 E) ≠ 0) e₂
  rw [e₃]
  exact hr'

end GlobalTheory.FlatCM.HomLat

end
