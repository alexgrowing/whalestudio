import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.CechPic GlobalTheory.UPel.HT.ES.PIsogExt

theorem UpperTheory.Gal.crystallineComparison.Mod.pullIsog_of :
    PullIsog := by
  intro p _ D R _ b N S S' s s' f hs c o o' ψ hψ o₁ m
  subst hs
  have hcpos : 0 < c := hψ.pos
  obtain ⟨hk, hmon, hact, heta, ⟨hiso⟩, ψ', hmon', h₁, h₂⟩ := hψ
  haveI := hmon
  haveI := hmon'
  obtain ⟨o₁', ⟨m'⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S S' s f o'
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk (m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom
    (by rw [Category.assoc, Over.w ψ, m.cart.1.w])) (m'.cart.1.lift_snd _ _ _)
  let ψ₁' : o₁'.A ⟶ o₁.A := Over.homMk (m.cart.1.lift (m'.φ ≫ ψ'.left) o₁'.A.hom
    (by rw [Category.assoc, Over.w ψ', m'.cart.1.w])) (m.cart.1.lift_snd _ _ _)
  have e : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := (m'.cart.1.lift_fst _ _ _).symm
  have e' : m'.φ ≫ ψ'.left = ψ₁'.left ≫ m.φ := (m.cart.1.lift_fst _ _ _).symm
  have pt : ∀ (T : Over S') (x : T ⟶ o₁.A), m'.ptEquiv T (x ≫ ψ₁) = m.ptEquiv T x ≫ ψ := fun T x =>
    Over.OverMorphism.ext (by
      rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, Category.assoc, e])
  have pt' : ∀ (T : Over S') (x : T ⟶ o₁'.A), m.ptEquiv T (x ≫ ψ₁') = m'.ptEquiv T x ≫ ψ' := fun T x =>
    Over.OverMorphism.ext (by
      rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, Category.assoc, e'])
  have mh : IsMonHom ψ₁ := GlobalTheory.GrpPullPow.isMonHom_of_mul_pts ψ₁ fun T x y => (m'.ptEquiv T).injective (by
    rw [map_mul, pt, pt, pt, map_mul, MonObj.mul_comp])
  have mh' : IsMonHom ψ₁' := GlobalTheory.GrpPullPow.isMonHom_of_mul_pts ψ₁' fun T x y => (m.ptEquiv T).injective (by
    rw [map_mul, pt', pt', pt', map_mul, MonObj.mul_comp])
  have hsq := isSquare_square_compatible_homs m.sq m'.sq e
  have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
    fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
  have hL₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
  have hM₁ : (o₁'.P.pull (sq2 ψ₁)).IsLB := pull_isLB o₁'.isLB _
  have e1 := (cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
  have e2 := (cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
  have hL₀ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have e3 : cls _ hL₀ = cls _ (pull_isLB o'.isLB (sq2 ψ)) := (cls_eq_iff hL₀ (pull_isLB o'.isLB (sq2 ψ))).2 hiso
  have ext₁ : ∀ {T : Over S'} (g h : T ⟶ o₁.A), g.left ≫ m.φ = h.left ≫ m.φ → g = h := fun g h H =>
    Over.OverMorphism.ext (m.cart.1.hom_ext H (by simp))
  have ext₂ : ∀ {T : Over S'} (g h : T ⟶ o₁'.A), g.left ≫ m'.φ = h.left ≫ m'.φ → g = h := fun g h H =>
    Over.OverMorphism.ext (m'.cart.1.hom_ext H (by simp))
  have hcls : cls _ hL₁ = cls _ hM₁ := by
    calc cls _ hL₁ = c • cls o₁.P o₁.isLB := hcL _ _ _
      _ = c • pull m.φ₂ (cls o.P o.isLB) := by rw [e2, cls_pull o.isLB]
      _ = pull m.φ₂ (c • cls o.P o.isLB) := (map_nsmul _ _ _).symm
      _ = pull m.φ₂ (cls _ (pull_isLB o'.isLB (sq2 ψ))) := by
        rw [← hcL o.P o.isLB hL₀, e3]
      _ = pull (m.φ₂ ≫ sq2 ψ) (cls o'.P o'.isLB) := by rw [cls_pull o'.isLB, pull_comp]
      _ = pull (sq2 ψ₁) (pull m'.φ₂ (cls o'.P o'.isLB)) := by rw [hsq, pull_comp]
      _ = pull (sq2 ψ₁) (cls o₁'.P o₁'.isLB) := by rw [e1, cls_pull o'.isLB]
      _ = cls _ hM₁ := (cls_pull o₁'.isLB _ _).symm
  refine ⟨o₁', m', ψ₁, ⟨hk, mh, fun c' => ?_, fun x => ?_, ⟨(cls_eq_iff hL₁ hM₁).1 hcls⟩, ψ₁', mh', ?_, ?_⟩, e⟩
  · refine ext₂ _ _ ?_
    have h := congrArg (fun q => m.φ ≫ q.left) (hact c')
    simp only [Over.comp_left] at h ⊢
    rw [Category.assoc, ← e, ← Category.assoc, m.act c', Category.assoc, h, Category.assoc, m'.act c',
      ← Category.assoc (Over.Hom.left ψ₁), ← e, Category.assoc]
  · refine ext₂ _ _ ?_
    rw [m'.eta x, heta x, Over.comp_left, Over.comp_left, Category.assoc, ← e,
      ← Category.assoc (Over.Hom.left (o₁.eta x)), m.eta x, Category.assoc]
  · refine ext₁ _ _ ?_
    rw [Over.comp_left, Category.assoc, ← e', ← Category.assoc, ← e, Category.assoc, ← Over.comp_left, h₁,
      pow_comp_of_isGrpPullback m.cart c hcpos]
  · refine ext₂ _ _ ?_
    rw [Over.comp_left, Category.assoc, ← e, ← Category.assoc, ← e', Category.assoc, ← Over.comp_left, h₂,
      pow_comp_of_isGrpPullback m'.cart c hcpos]
