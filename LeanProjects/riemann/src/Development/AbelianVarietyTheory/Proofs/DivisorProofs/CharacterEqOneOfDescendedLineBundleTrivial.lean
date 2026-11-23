import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem pullTop_pullTop_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    pullTop f (pullTop g u) = pullTop (f ≫ g) u := rfl

theorem exists_unit_of_triv {X Y Z : Scheme.{0}} (p : X ⟶ Y) (M : LB Y) (hM : M.IsLB)
    (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ) (he : IsPullGen p M e) (t : M.Gen) (ht : t.IsGen)
    (a b : Z ⟶ X) (hab : a ≫ p = b ≫ p) (c : Γ(Z, ⊤)ˣ)
    (hc : ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ a ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ b ⁻¹ᵁ (p ⁻¹ᵁ M.U k)),
      res h₁ (pullU a _ (e k)) = res le_top c * res h₂ (pullU b _ (e k))) :
    ∃ f : Γ(X, ⊤)ˣ, pullTop a f = c * pullTop b f := by
  obtain ⟨f, hf⟩ := glue_unit (X := X) ⊤ (fun k => p ⁻¹ᵁ M.U k) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨k, hk⟩ := exists_chart hM (p x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩)
    (fun k => e k * (pullU p _ (t.s k))⁻¹) (fun k l x hx => by
      have h₁ := congrArg (gm (𝟙 X) x _) (he k l (p ⁻¹ᵁ M.U k ⊓ p ⁻¹ᵁ M.U l) inf_le_left inf_le_right
        (p.preimage_inf (U := M.U k) (V := M.U l)).ge)
      have h₂ := congrArg (gm p x _) (ht k l)
      rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx, gm_pull (𝟙 X) p x (M.U k ⊓ M.U l) hx,
        Category.id_comp] at h₁
      rw [map_mul, gm_res p x _ hx, gm_res p x _ hx] at h₂
      rw [map_mul, map_mul, map_inv, map_inv, gm_pull (𝟙 X) p x _ hx.1, gm_pull (𝟙 X) p x _ hx.2,
        Category.id_comp, h₁, h₂,
        mul_inv_rev, mul_comm (gm p x _ (M.g k l)), _root_.mul_assoc, mul_comm (gm p x _ (t.s l))⁻¹,
        mul_inv_cancel_left])
  refine ⟨f, unit_ext fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM (p (a z))
  have hk' : p (b z) ∈ M.U k := by
    rwa [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply]
  have hz' : z ∈ a ⁻¹ᵁ (p ⁻¹ᵁ M.U k) ⊓ b ⁻¹ᵁ (p ⁻¹ᵁ M.U k) := ⟨hk, hk'⟩
  have h := congrArg (gm (𝟙 Z) z _) (hc k _ inf_le_left inf_le_right)
  rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz', gm_pull (𝟙 Z) a z (p ⁻¹ᵁ M.U k) hk,
    gm_pull (𝟙 Z) b z (p ⁻¹ᵁ M.U k) hk',
    Category.id_comp, Category.id_comp] at h
  have key : ∀ d : Z ⟶ X, p (d z) ∈ M.U k →
      gm (𝟙 Z) z ⊤ (pullTop d f) = gm d z _ (e k) * (gm (d ≫ p) z _ (t.s k))⁻¹ := fun d hd => by
    have h' := congrArg (gm d z _) (hf k)
    rw [gm_res d z _ hd, map_mul, map_inv, gm_pull d p z _ hd] at h'
    rw [← h']
    exact gm_pull (𝟙 Z) d z ⊤ trivial f
  rw [map_mul, key a hk, key b hk', h, hab, _root_.mul_assoc]

theorem exists_pullTop_snd {S : Scheme.{0}} (A T : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (f : Γ((A ⊗ T).left, ⊤)ˣ) : ∃ u : Γ(T.left, ⊤)ˣ, pullTop (snd A T).left u = f := by
  have hb : Function.Bijective (snd A T).left.appTop.hom :=
    GlobalTheory.SemiRigid.globalFns _ _ (Out.TLinPf.isAb_pullback T.hom A hA)
  let φ := RingEquiv.ofBijective _ hb
  exact ⟨Units.map (φ.symm : Γ((A ⊗ T).left, ⊤) →* Γ(T.left, ⊤)) f, Units.ext (φ.apply_symm_apply f.val)⟩

theorem character_eq_one_of_triv : ∀ (K : Type) [Field K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsMonHom q → IsPullback i (toUnit N) q η[A'] → M.IsLB → IsEquivGen i q χ M e → Triv M → χ = 1 := by
  intro K _ A A' N T _ _ _ i q χ M e hA hq hk hM he ⟨t, ht⟩
  have hab : actMap i T ≫ pmap q T = prMap A N T ≫ pmap q T := by
    have hi : i ≫ q = 1 := hk.w
    simp only [actMap, prMap, pmap, comp_lift, lift_fst_assoc, lift_snd, MonObj.mul_comp, Category.assoc, hi,
      MonObj.comp_one, _root_.mul_one]
  obtain ⟨f, hf⟩ := exists_unit_of_triv _ M hM e he.1 t ht (actMap i T).left (prMap A N T).left
    (congrArg (·.left) hab) _ he.2
  obtain ⟨u, rfl⟩ := exists_pullTop_snd A T hA f
  have h₁ : (actMap i T).left ≫ (snd A T).left = (prMap A N T).left ≫ (snd A T).left := by
    rw [← Over.comp_left, ← Over.comp_left, actMap, prMap, lift_snd, lift_snd]
  rw [pullTop_pullTop_comp, pullTop_pullTop_comp, h₁, right_eq_mul] at hf
  have h₂ : (lift (1 : N ⊗ T ⟶ A) (𝟙 (N ⊗ T))).left ≫ (snd A (N ⊗ T)).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have h₃ := congrArg (pullTop (lift (1 : N ⊗ T ⟶ A) (𝟙 (N ⊗ T))).left) hf
  rw [pullTop_pullTop_comp, h₂, map_one] at h₃
  exact h₃

end GlobalTheory.CharKer
