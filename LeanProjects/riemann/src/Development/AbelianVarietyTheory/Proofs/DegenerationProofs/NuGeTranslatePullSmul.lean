import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PrimitiveExpansionThetaPullbackHeisenbergTranslaStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem eq_mul_of_isTwistPull {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {m : T ⊗ A ⟶ A} {a b : ℤ} {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s s₀ : LB.Sec (LPow A L b T)} {t t₀ : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (e : ∀ j, s.f j = liftFun A _ c * s₀.f j)
    (h : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s t)
    (h₀ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s₀ t₀) (j) :
    t.f j = liftFun A _ c * t₀.f j := by
  have f₁ : (lift (fst T A) m).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, lift_fst]
  have key : (SecM.ofSec A t : SecM A L a T) = SecM.ofSec A (SecM.toSec A (c • SecM.ofSec A t₀)) :=
    VVRank.ofSec_ext A hL fun y J hJ => by
      rw [ThetaPtMove.sv_of_eq_mul (s := SecM.toSec A (c • SecM.ofSec A t₀)) (t := t₀) (c := c) (fun j => rfl) _ y hJ,
        VVRank.sv_of_isTwistPull A h _ y hJ, VVRank.sv_of_isTwistPull A h₀ _ y hJ,
        ThetaPtMove.sv_of_eq_mul e _ y hJ]
      simp only [Category.assoc, f₁]
      ring
  exact congrArg (fun q => q.1 j) key

theorem nuGe_translate_pull_smul : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th₀ : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th₀ ϑ → Prim D Q v ϑ → ∀ (m N : ℕ), N = m ^ 2 → Odd m → IsUnit (m : V) → ∀ (c : F) (r : ℚ) (th : SecA A F 1), (r : WithTop ℚ) ≤ v c → (∀ j, th.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * th₀.f j) → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left] ![(N : ℤ), -((1 : ℕ) : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := V) F) ((N : ℤ) - 1)) → ∀ (s₁ t : SecA A F N) (x : TFK (R := V) F ⟶ A.A) (θ : ThetaGrp A.A A.L N (TFK (R := V) F)) (s : Fam D.toPre F N), IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s₁ → x ^ N = 1 → SymLift A.A A.L N N x θ → IsActOf A.A A.L N θ s₁ t → U.ExpandsF F N w₀ t s → NuGe D Q F v N s r := by
  intro hLL hBC hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th₀ ϑ hth hprim m N hNm hm hmu
    c r th hr eth α hα hn s₁ t x θ s hs₁ hx hθ ht hs
  subst hNm
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨hB, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hA D A G hG U
  obtain ⟨hB₁, -⟩ := hB F (m ^ 2) hN1 w₀ hN.1
  let T := TFK (R := V) F
  let κ : F ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  obtain ⟨u₁, hu₁⟩ := VVRank.exists_isTwistPull A.A (ψ := mulT A.A T m) (hm := lift_snd _ _) A.isLB hα th₀
  obtain ⟨t₀, ht₀⟩ := VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (hm := lift_snd _ _) A.isLB θ.isGen u₁
  obtain ⟨c₀, hc₀⟩ := NormTheta.exists_value A.isLB hN.2.1 _ t₀
  obtain ⟨c', rfl⟩ := κ.surjective c₀
  obtain ⟨s₀, hs₀, -⟩ := hB₁ t₀
  have hP := GlobalTheory.T.primitive_expansion_thetaPullback_heisenbergTranslates hLL hBC hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th₀ ϑ hth hprim m hm hmu
    x t₀ c' s₀ hx ⟨α, u₁, θ, hα, hn, hu₁, hθ, ht₀, hc₀⟩ hs₀
  have e₁ := eq_mul_of_isTwistPull (c := κ c) A.isLB eth hs₁ hu₁
  have e₂ := eq_mul_of_isTwistPull (c := κ c) A.isLB e₁ ht ht₀
  have h₁ := hlin F (m ^ 2) w₀ t₀ t₀ t s₀ s₀ (c - 1) hs₀ hs₀ fun j => by
    refine (e₂ j).trans ?_
    have : κ c • SecM.ofSec A.A t₀ = κ (c - 1) • SecM.ofSec A.A t₀ + SecM.ofSec A.A t₀ := by
      rw [map_sub, map_one, sub_smul, one_smul, sub_add_cancel]
    exact congrArg (fun q => q.1 j) this
  rw [sub_smul, one_smul, sub_add_cancel] at h₁
  have := NuGe.smul Q hr ((isSmul_iff c s₀ s).2 ((hB₁ t).unique hs h₁)) hP.1
  rwa [zero_add] at this

end GlobalTheory.ZH
