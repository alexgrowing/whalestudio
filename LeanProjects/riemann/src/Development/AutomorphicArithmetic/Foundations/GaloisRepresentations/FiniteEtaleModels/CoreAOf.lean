import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslateLocallyNoetherianBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

private theorem keyC {A B V U E₁ E₂ : Scheme.{0}} {ψ : A ⟶ B} {χ : B ⟶ V} {mv : V ⟶ U} {m : U ⟶ E₂} {ψ₂ : A ⟶ V} {c : A ⟶ E₁}
    {ψ₁ : E₁ ⟶ U} {n₁ : B ⟶ U} {n₂ : B ⟶ E₂} (h₁ : n₁ = χ ≫ mv) (h₂ : n₂ = n₁ ≫ m) (h₃ : ψ ≫ χ = ψ₂) (h₄ : ψ₂ ≫ mv = c ≫ ψ₁) :
    ψ ≫ n₂ = c ≫ ψ₁ ≫ m := by
  rw [h₂, h₁, ← Category.assoc, ← Category.assoc, h₃, h₄, Category.assoc]

private theorem keyL {X A B U Y₁ Y₂ E₁ E₂ : Scheme.{0}} {ψ : A ⟶ B} {n : B ⟶ E₂} {c : A ⟶ E₁} {ψ₁ : E₁ ⟶ U} {m : U ⟶ E₂}
    {x : X ⟶ A} {j : X ⟶ Y₁} {t : Y₁ ⟶ Y₂} {l₁ : Y₁ ⟶ E₁} {l₂ : Y₂ ⟶ E₂} (h₁ : ψ ≫ n = c ≫ ψ₁ ≫ m) (h₂ : x ≫ c = j ≫ l₁)
    (h₃ : (l₁ ≫ ψ₁) ≫ m = t ≫ l₂) : (x ≫ ψ) ≫ n = ((𝟙 X ≫ j) ≫ t) ≫ l₂ := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.id_comp, Category.assoc, Category.assoc, ← h₃, Category.assoc]

theorem coreA_of (hP : TrPull) (hS : TrSame) (hL : LevTr) (hR : LevRe) (hC : ClsEx) : CoreA := by
  intro q _ D R R' _ _ _ b gb β hm N κ c 𝔟₁ 𝔟₂ E₁ E₂ hno hN hNq hκ hck hle hq f u hs ρ hρ X s M₁ M₂ c₁ c₂ a₁ a₂ e₁ e₂ h₁ h₂ hg o₁ o₂ ψ
    hA hlv C₁ C₂
  have hc : c.Coprime q := Nat.Coprime.coprime_dvd_left hck (hκ.pow_left 2)
  obtain ⟨u', ψ₁, hT⟩ := GlobalTheory.T.exists_hecke_translate_locallyNoetherian_base q D R b f u c κ N hN hNq hc hκ hck hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 E₁.X E₁.s E₁.univ
  have hl := hR q D R b N 𝔟₁ 𝔟₂ ρ hle hρ _ _ u' _ (hL q D R b _ c κ N 𝔟₁ hκ hq _ _ E₁.univ u' ψ₁ E₁.lv hT E₁.isLev)
  obtain ⟨t, ⟨ht, m, hmlv⟩, -⟩ := E₂.rep E₁.X E₁.s u' _ hl
  let m₁ : ObjMap (ob hm o₁ (N * κ) c₁ e₁ h₁) E₁.univ C₁.j :=
    ⟨C₁.m.φ, C₁.m.φ₂, C₁.m.cart, C₁.m.sq, C₁.m.act, C₁.m.pol, C₁.m.eta⟩
  have hv : ∃ v : Obj b N (s ≫ spMap β), Nonempty (ObjMap v u' C₁.j) := by
    rw [← C₁.ov]; exact GlobalTheory.HTPull.exists_objMap_pull q D R b N _ _ E₁.s C₁.j u'
  obtain ⟨v, ⟨mv⟩⟩ := hv
  obtain ⟨ψ₂, hT₂, hψ₂⟩ := hP q D R b _ c κ N _ _ _ _ C₁.j E₁.univ u' ψ₁ _ v m₁ mv hT
  obtain ⟨χ, hχ⟩ := hS q D R b _ c κ N _ _ (ob hm o₁ (N * κ) c₁ e₁ h₁) (ob hm o₂ N c₂ e₂ h₂) v ψ ψ₂ hA hT₂
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ χ mv
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ n₁ m
  have key : ψ.left ≫ n₂.φ = C₁.m.φ ≫ ψ₁.left ≫ m.φ := keyC hn₁ hn₂ hχ hψ₂
  let B : Cls E₂ β o₂ c₂ a₂ :=
    { j := (𝟙 X ≫ C₁.j) ≫ t
      ov := by rw [Category.assoc, ht, Category.id_comp, C₁.ov]
      m := ⟨n₂.φ, n₂.φ₂, n₂.cart, n₂.sq, n₂.act, n₂.pol, n₂.eta⟩
      lv := fun y => by
        show (o₂.eta _).left ≫ n₂.φ = _
        rw [← hlv y]
        exact keyL key (C₁.lv (ρ y)) (hmlv y) }
  obtain ⟨ej, eφ⟩ := (hC q D R R' b gb β hm M₂ N c₂ a₂ 𝔟₂ e₂ h₂ hN hNq hg E₂ X s o₂).2 B C₂
  refine ⟨t, ψ₁.left ≫ m.φ, ht, ?_, ?_, ?_⟩
  · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]
  · rw [← ej]; show _ = (𝟙 X ≫ C₁.j) ≫ t; rw [Category.id_comp]
  · rw [← eφ]; exact key.symm

end UpperTheory.Gal.FiniteEtaleModels
