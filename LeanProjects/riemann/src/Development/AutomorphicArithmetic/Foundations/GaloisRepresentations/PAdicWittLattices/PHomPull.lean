import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem square_map_isSquare {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (ψ : A ⟶ B) :
    Geo.Tor.IsSquare ψ.left (Hecke.sq2 ψ) := by
  constructor
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem UpperTheory.Gal.G3.pHomPull :
    HomPull := by
  intro G₀ R _ _ gb S S' s s' f N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ
  let g : Over.mk (o₁'.A.hom ≫ f) ⟶ o₂.A := GlobalTheory.ObjPull.pushEquiv m₁.cart o₁'.A (𝟙 o₁'.A) ≫ ψ
  refine ⟨(GlobalTheory.ObjPull.pushEquiv m₂.cart o₁'.A).symm g, ?_⟩
  set ψ' := (GlobalTheory.ObjPull.pushEquiv m₂.cart o₁'.A).symm g with hψ'eq
  have hψ' : ψ'.left ≫ m₂.φ = m₁.φ ≫ ψ.left := by
    rw [← GlobalTheory.ObjPull.pushEquiv_left m₂.cart, hψ'eq, MulEquiv.apply_symm_apply]
    simp only [g, Over.comp_left, GlobalTheory.ObjPull.pushEquiv_left, Over.id_left, Category.id_comp]
  have key : ∀ (T : Over S') (z : T ⟶ o₁'.A),
      GlobalTheory.ObjPull.pushEquiv m₂.cart T (z ≫ ψ') = GlobalTheory.ObjPull.pushEquiv m₁.cart T z ≫ ψ := by
    intro T z
    apply Over.OverMorphism.ext
    simp only [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Category.assoc, hψ']
  have inj : ∀ {T : Over S'} (u v : T ⟶ o₂'.A), u.left ≫ m₂.φ = v.left ≫ m₂.φ → u = v := by
    intro T u v huv
    apply (GlobalTheory.ObjPull.pushEquiv m₂.cart T).injective
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, GlobalTheory.ObjPull.pushEquiv_left, huv]
  have hsq : m₁.φ₂ ≫ Hecke.sq2 ψ = Hecke.sq2 ψ' ≫ m₂.φ₂ := by
    have a := MapComp.isSquare_comp m₁.sq (square_map_isSquare ψ)
    have b := MapComp.isSquare_comp (square_map_isSquare ψ') m₂.sq
    rw [hψ'] at b
    exact MapComp.isSquare_unique a b
  refine ⟨hψ', ?_, ?_, ?_⟩
  · intro hψ
    apply GlobalTheory.Serre.isMonHom_of_mul_comp
    intro T x y
    apply (GlobalTheory.ObjPull.pushEquiv m₂.cart T).injective
    rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]
  · intro hc c
    apply inj
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ', m₂.act,
      ← Category.assoc ψ'.left, hψ', ← Category.assoc, m₁.act, Category.assoc, Category.assoc,
      ← Over.comp_left, ← Over.comp_left, hc c]
  · intro c hc
    obtain ⟨e⟩ := hc
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o₁.isLB _ _) (pull_isLB o₂.isLB _)).2 e
    have hP1 := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o₁.isLB m₁.φ₂)).2 m₁.pol
    have hP2 := (GlobalTheory.CechPic.cls_eq_iff o₂'.isLB (pull_isLB o₂.isLB m₂.φ₂)).2 m₂.pol
    rw [GlobalTheory.CechPic.cls_pull o₁.isLB] at hP1
    rw [GlobalTheory.CechPic.cls_pull o₂.isLB] at hP2
    rw [GlobalTheory.CechPic.cls_pull o₂.isLB, GlobalTheory.CechPic.cls_linComb o₁.isLB] at h1
    simp only [GlobalTheory.CechPic.pull_id] at h1
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o₁'.isLB _ _) (pull_isLB o₂'.isLB _)).1 ?_⟩
    rw [GlobalTheory.CechPic.cls_linComb o₁'.isLB, GlobalTheory.CechPic.cls_pull o₂'.isLB, hP1, hP2]
    simp only [GlobalTheory.CechPic.pull_id]
    rw [← GlobalTheory.CechPic.pull_comp, ← hsq, GlobalTheory.CechPic.pull_comp, ← h1]
    simp [map_sum, map_zsmul]
