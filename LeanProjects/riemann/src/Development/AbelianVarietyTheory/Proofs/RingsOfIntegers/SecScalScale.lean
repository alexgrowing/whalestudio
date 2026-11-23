import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumMatch
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsFSum

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpInt

theorem secScal_scale {R : Type} [CommRing R] {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (p : Y ⟶ Spec (CommRingCat.of R)) {p' : Y' ⟶ Spec (CommRingCat.of R)} (hp : h ≫ p = p') (a b c : R)
    (hc : c = a * b) (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h (scal p' b)) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ (SecOps.secScale (scal p a) s₂) h (scal p' c) := by
  unfold GeneratorPullback.SecScal at H ⊢
  intro j₁ j₂ hj
  have e1 : (SecOps.secScale (scal p a) s₂).f j₂ = resTop _ (scal p a) * s₂.f j₂ := rfl
  have e2 : h.appTop.hom (scal p a) = scal p' a := by
    subst hp
    simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [e1]
  erw [map_mul, map_mul, H j₁ j₂ hj, GlobalTheory.ExpansionLinear.app_resTop, SecOps.resTop_res]
  rw [e2, hc, GlobalTheory.ExpansionLinear.scal_mul, GlobalTheory.ExpansionLinear.resTop_mul]
  exact (_root_.mul_assoc _ _ _).symm

private theorem secIsMul_secScale_scal {R : Type} [CommRing R] {Y : Scheme.{0}} {L : LB Y}
    (p : Y ⟶ Spec (CommRingCat.of R)) (a : R) (s : LB.Sec L) :
    SecIsMul p a (SecOps.secScale (scal p a) s) s := by
  unfold SecIsMul
  intro j
  rfl

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∃ (c : V) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k), c ≠ 0 ∧ GeneratorPullback.SecScal P.U.LG.L (fun _ : Fin 1 => pullback.fst t.G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => ((k : ℕ) : ℤ)) τ (pullback.fst t.G.hom (jK V)) (scal (pullback.snd t.G.hom (jK V) ≫ jK V) c) ∧ GeneratorPullback.SecScal P.U.LG.L (fun _ : Fin 1 => pullback.fst t.G.hom (jK V)) (fun _ => ((k * N : ℕ) : ℤ)) u (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => ((k * N : ℕ) : ℤ)) σ'' (pullback.fst t.G.hom (jK V)) (scal (pullback.snd t.G.hom (jK V) ≫ jK V) c) ∧ ∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL')) := by
  intro hG V _ _ _ E _ _ _ H t P a N ha hN X hX hXc k s F u F' hs hu hpull
  letI := H.starRing
  have hR : RosatiAdj P.D.toPre.P.A P.D.toPre.P.L (P.oD.onB.act (star a)) (P.oD.onB.act a) := by
    have h0 := P.oD.onB.2 (star a)
    rwa [star_star] at h0
  haveI := P.oD.onB.toRingAct.2 (star a)
  haveI := P.oD.onB.toRingAct.2 a
  obtain ⟨uR, huR, huR0⟩ := Geo.Tor.exists_ros hG P.D.toPre.P.isAb P.D.toPre.P.isLB
    (P.oD.onB.act (star a)) (P.oD.onB.act a) hR
  obtain ⟨r₁, hr₁, τ₁, f₁, hτ₁, hf₁, he₁⟩ := hs
  obtain ⟨r₂, hr₂, σ₂, f₂, hσ₂, hf₂, he₂⟩ := hu
  have hpB : (DegPre.prB P.D.toPre (FractionRing V)).left ≫ P.D.toPre.P.A.hom =
      (DegPre.BF P.D.toPre (FractionRing V)).hom := Over.w _
  let f : ∀ α : P.D.toPre.X, P.D.toPre.SecB k α := fun α => SecOps.secScale (scal P.D.toPre.P.A.hom r₂) (f₁ α)
  let f'' : ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α :=
    fun α => SecOps.secScale (scal P.D.toPre.P.A.hom r₁) (f₂ α)
  let τ : H0 P.U.LG.L k := SecOps.secScale (scal t.G.hom r₂) τ₁
  let σ'' : H0 P.U.LG.L (k * N) := SecOps.secScale (scal t.G.hom r₁) σ₂
  have hτ := secScal_scale t.G.hom pullback.condition r₂ r₁ (r₁ * r₂) (mul_comm _ _) hτ₁
  have hσ := secScal_scale t.G.hom pullback.condition r₁ r₂ (r₁ * r₂) rfl hσ₂
  have hf : ∀ α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε k) (F.s α)
      (P.D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB P.D.toPre (FractionRing V)).left
      (scal (DegPre.BF P.D.toPre (FractionRing V)).hom (r₁ * r₂)) := fun α =>
    secScal_scale P.D.toPre.P.A.hom hpB r₂ r₁ (r₁ * r₂) (mul_comm _ _) (hf₁ α)
  have hf'' : ∀ α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε (k * N))
      (F'.s α) (P.D.toPre.famφB α) (DegPre.famε (k * N)) (f'' α) (DegPre.prB P.D.toPre (FractionRing V)).left
      (scal (DegPre.BF P.D.toPre (FractionRing V)).hom (r₁ * r₂)) := fun α =>
    secScal_scale P.D.toPre.P.A.hom hpB r₁ r₂ (r₁ * r₂) rfl (hf₂ α)
  have hrel := GlobalTheory.PullIntegral.main hG V E H t P a N ha hN X hX hXc uR huR huR0 k F F' hpull (r₁ * r₂) f'' f hf hf''
  refine ⟨r₁ * r₂, σ'', τ, mul_ne_zero hr₁ hr₂, hτ, hσ, fun e => ?_⟩
  have hE : P.U.ExpandsAt e k τ f :=
    GlobalTheory.expandsAt_secIsMul V (maximalIdeal V) P.D P.A t.G P.U.toUnifPre e k r₂ τ₁ τ f₁ f
      (secIsMul_secScale_scal _ _ _) (fun α => secIsMul_secScale_scal _ _ _) (he₁ e)
  have hE'' : P.U.ExpandsAt e (k * N) σ'' f'' :=
    GlobalTheory.expandsAt_secIsMul V (maximalIdeal V) P.D P.A t.G P.U.toUnifPre e (k * N) r₁ σ₂ σ'' f₂ f''
      (secIsMul_secScale_scal _ _ _) (fun α => secIsMul_secScale_scal _ _ _) (he₂ e)
  exact GlobalTheory.PullExpLoc.main hG V E H t P a N ha hN X uR huR huR0 e k σ'' τ f'' f hE'' hE hrel

end GlobalTheory.PullExpInt
