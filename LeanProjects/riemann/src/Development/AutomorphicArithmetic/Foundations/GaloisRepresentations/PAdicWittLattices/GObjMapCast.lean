import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelHomUnique
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem gObjMap_comp_φ {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁}
    {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f)
    (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
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
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

private theorem gObjMap_cast {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {f f' : S₁ ⟶ S₂} (e : f = f') (m : GObjMap o₁ o₂ f) : ∃ m' : GObjMap o₁ o₂ f', m'.φ = m.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem UpperTheory.Gal.G3.pPtEq :
    TransSelf → TransComp → TransPull → TransUniqPt → Rigid → PtEq := by
  intro hS hC hP hU hRg p _ D G L R _ _ gb N₁ N₂ N X₁ X₂ X h₁ h₂ g u π₁ Φ₁ π₂ Φ₂ w₁ w₂ i₁ i₂ a₁ a₂ hu he
    k _ _ s x y hx hy ox oy mx my θ hθ
  obtain ⟨e₁, o₁, ψ₁, f₁, t₁, rfl⟩ := w₁
  obtain ⟨e₂, o₂, ψ₂, f₂, t₂, rfl⟩ := w₂
  obtain ⟨o₁x, ⟨n₁⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero s x hx o₁
  obtain ⟨o₂y, ⟨n₂⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero s y hy o₂
  obtain ⟨ψ₁', t₁', c₁⟩ := hP p D G L R gb X₁.X (Sp k) X₁.s s x hx _ _ X₁.univ o₁ ox o₁x mx n₁ ψ₁ h₁ t₁
  obtain ⟨ψ₂', t₂', c₂⟩ := hP p D G L R gb X₂.X (Sp k) X₂.s s y hy _ _ X₂.univ o₂ oy o₂y my n₂ ψ₂ h₂ t₂
  have iu : Integ L u := UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu)
  have au : AdmK L N N u := fun v hv =>
    (L.KN N).mul_mem ((L.KN N).mul_mem hu hv) ((L.KN N).inv_mem hu)
  have t₃ := hC p D G L R gb (Sp k) s N₁ N₂ N ox oy o₂y θ ψ₂' g h₂ i₂ a₂ hθ t₂'
  have t₄ := hC p D G L R gb (Sp k) s N₁ N N ox o₂y o₂y (θ ≫ ψ₂') (𝟙 _) (h₂ * g) u iu au t₃
    ((hS p D G L R gb (Sp k) s N).1 o₂y u hu)
  rw [← he] at t₄
  obtain ⟨m, hm⟩ := hU p D G L R gb k s N₁ N ox o₁x o₂y ψ₁' _ h₁ i₁ a₁ t₁' t₄
  obtain ⟨A, hA⟩ := gObjMap_comp_φ n₁ f₁
  obtain ⟨B₀, hB₀⟩ := gObjMap_comp_φ n₂ f₂
  obtain ⟨B, hB⟩ := gObjMap_comp_φ m B₀
  have hxs : (x ≫ π₁) ≫ X.s = s := by rw [Category.assoc, e₁, hx]
  have hys : (𝟙 (Sp k) ≫ y ≫ π₂) ≫ X.s = s := by simp [Category.assoc, e₂, hy]
  have hxy : x ≫ π₁ = 𝟙 (Sp k) ≫ y ≫ π₂ :=
    (X.rep (Sp k) s o₁x).unique ⟨hxs, ⟨A⟩⟩ ⟨hys, ⟨B⟩⟩
  obtain ⟨B', hB'⟩ := gObjMap_cast hxy.symm B
  have hAB := hRg p D R gb X.X (Sp k) X.s s (x ≫ π₁) hxs N X.univ o₁x A B'
  refine ⟨by simpa using hxy, ?_⟩
  rw [hB', hB, hB₀, hA] at hAB
  calc mx.φ ≫ Over.Hom.left ψ₁ ≫ f₁.φ = (mx.φ ≫ Over.Hom.left ψ₁) ≫ f₁.φ := by rw [Category.assoc]
    _ = Over.Hom.left ψ₁' ≫ n₁.φ ≫ f₁.φ := by rw [← c₁, Category.assoc]
    _ = Over.Hom.left ψ₁' ≫ m.φ ≫ n₂.φ ≫ f₂.φ := by rw [hAB]
    _ = Over.Hom.left ((θ ≫ ψ₂') ≫ 𝟙 _) ≫ n₂.φ ≫ f₂.φ := by rw [← hm, Category.assoc]
    _ = Over.Hom.left θ ≫ (Over.Hom.left ψ₂' ≫ n₂.φ) ≫ f₂.φ := by simp
    _ = Over.Hom.left θ ≫ my.φ ≫ Over.Hom.left ψ₂ ≫ f₂.φ := by rw [c₂, Category.assoc]
