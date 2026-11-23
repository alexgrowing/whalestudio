import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelHomUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_comp {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} {e : S₁ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g)
    (he : f ≫ g = e) : ∃ m : GObjMap o₁ o₃ e, m.φ = h₁.φ ≫ h₂.φ := by
  subst he
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol
      (GlobalTheory.UPel.HT.MapComp.lbIso_pull_comp h₂.pol h₁.φ₂ rfl)
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem UpperTheory.Gal.G3.pPtOrbit :
    TransComp → TransPull → TransOfMap → TransOrbit → Rigid → PtOrbit := by
  intro hC hP hM hO hRg p _ D G L R _ _ gb N' N X' X π Φ w k _ _ x y hxy
  obtain ⟨e, o, ψ, φ, tψ, rfl⟩ := w
  have hs : y ≫ X'.s = x ≫ X'.s := by rw [← e, ← Category.assoc, ← hxy, Category.assoc]
  obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl X'.univ
  obtain ⟨oy, ⟨my⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) y hs X'.univ
  obtain ⟨ox', ⟨nx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl o
  obtain ⟨oy', ⟨ny⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) y hs o
  refine ⟨ox, oy, mx, my, hs, ?_⟩
  obtain ⟨ψx, tx, cx⟩ := hP p D G L R gb X'.X (Sp k) X'.s (x ≫ X'.s) x rfl _ _ X'.univ o ox ox' mx nx ψ 1 tψ
  obtain ⟨ψy, ty, cy⟩ := hP p D G L R gb X'.X (Sp k) X'.s (x ≫ X'.s) y hs _ _ X'.univ o oy oy' my ny ψ 1 tψ
  obtain ⟨A, hA⟩ := exists_comp nx φ (rfl : x ≫ π = x ≫ π)
  obtain ⟨B, hB⟩ := exists_comp ny φ hxy.symm
  obtain ⟨A', hA'⟩ := exists_comp nx φ (Category.id_comp (x ≫ π)).symm
  obtain ⟨c⟩ := BaseChange.gObjMap_cancel (f := 𝟙 (Sp k)) A' B
  obtain ⟨θ', hθ', tθ'⟩ := hM p D G L R gb (Sp k) (x ≫ X'.s) N ox' oy' c
  have i1 : Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (L.KN 1).one_mem
  have a1 : AdmK L N N 1 := fun v hv => by simpa using hv
  have t₂ := hC p D G L R gb (Sp k) (x ≫ X'.s) N' N N ox ox' oy' ψx θ' 1 1 i1 a1 tx tθ'
  rw [_root_.mul_one] at t₂
  obtain ⟨u, hu, θ, tθ, hθ⟩ := hO p D G L R gb k (x ≫ X'.s) N' N ox oy oy' (ψx ≫ θ') ψy t₂ ty
  refine ⟨u, hu, θ, tθ, ?_⟩
  have hr := hRg p D R gb X.X (Sp k) X.s (x ≫ X'.s) (x ≫ π) (by rw [Category.assoc, e]) N X.univ ox'
  obtain ⟨C, hC'⟩ := exists_comp c B (Category.id_comp (x ≫ π))
  have key : c.φ ≫ ny.φ ≫ φ.φ = nx.φ ≫ φ.φ := by
    have := hr C A
    rw [hC', hB, hA] at this
    exact this
  calc Over.Hom.left θ ≫ my.φ ≫ Over.Hom.left ψ ≫ φ.φ
      = Over.Hom.left θ ≫ (my.φ ≫ Over.Hom.left ψ) ≫ φ.φ := by rw [Category.assoc]
    _ = Over.Hom.left (θ ≫ ψy) ≫ ny.φ ≫ φ.φ := by rw [← cy]; simp
    _ = Over.Hom.left ψx ≫ c.φ ≫ ny.φ ≫ φ.φ := by rw [hθ, Over.comp_left, hθ', Category.assoc]
    _ = Over.Hom.left ψx ≫ nx.φ ≫ φ.φ := by rw [key]
    _ = mx.φ ≫ Over.Hom.left ψ ≫ φ.φ := by rw [← Category.assoc, cx, Category.assoc]
