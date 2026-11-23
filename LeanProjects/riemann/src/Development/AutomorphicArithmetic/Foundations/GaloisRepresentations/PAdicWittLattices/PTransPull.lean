import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pow_push {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (d : ℕ) :
    ((𝟙 G') ^ d : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ d : G ⟶ G).left := by
  obtain ⟨hpb, hm⟩ := h
  have hw : φ ≫ G.hom = G'.hom ≫ f := hpb.w
  let P : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using hw)
  have key : ∀ n : ℕ, ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = (P ^ n).left := by
    intro n
    induction n with
    | zero =>
      let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
        (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have e : (x₀ * x₀).left = x₀.left := by
        rw [hm G' 1 1 x₀ x₀ rfl rfl, _root_.mul_one (1 : G' ⟶ G')]
        rfl
      have e2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext e
      have e3 : x₀ = 1 := by simpa using e2
      rw [pow_zero, pow_zero]
      exact congrArg CommaMorphism.left e3
    | succ n ih =>
      rw [pow_succ, pow_succ, ← hm G' _ _ (P ^ n) P ih.symm (by simp [P])]
  rw [key d]
  have hP : P ≫ ((𝟙 G) ^ d) = P ^ d := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← hP]
  rfl

private theorem qinv_pull {S S' : Scheme.{0}} {A₁' A₂' : Over S'} {A₁ A₂ : Over S} [GrpObj A₁'] [GrpObj A₁] {f : S' ⟶ S}
    {φ₁ : A₁'.left ⟶ A₁.left} {φ₂ : A₂'.left ⟶ A₂.left} (c₁ : IsGrpPullback A₁' A₁ f φ₁) {ψ : A₁ ⟶ A₂} {χ : A₂ ⟶ A₁}
    {ψ' : A₁' ⟶ A₂'} {χ' : A₂' ⟶ A₁'} (e : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (e' : χ'.left ≫ φ₁ = φ₂ ≫ χ.left) {d : ℕ}
    (h : ψ ≫ χ = (𝟙 A₁) ^ d) : ψ' ≫ χ' = (𝟙 A₁') ^ d := by
  apply Over.OverMorphism.ext
  apply c₁.1.hom_ext
  · rw [Over.comp_left, Category.assoc, e', ← Category.assoc, e, Category.assoc, ← Over.comp_left, h, pow_push c₁]
  · rw [Over.w, Over.w]

theorem UpperTheory.Gal.G3.pTransPull :
    HomPull → TatePull → TransPull := by
  intro hHom hTate p _ D G L R _ _ gb S S' s s' f hf N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ h hT
  obtain ⟨hmon, hact, ⟨χ, d, hχmon, hχact, e1, e2, hd⟩, ⟨c, hc, ⟨lb⟩, tt⟩, hgeo⟩ := hT
  obtain ⟨ψ', hψ, hmon', hact', hlb'⟩ := hHom D.toG R gb S S' s s' f N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ
  obtain ⟨χ', hχ, hχmon', hχact', -⟩ := hHom D.toG R gb S S' s s' f N₂ N₁ o₂ o₁ o₂' o₁' m₂ m₁ χ
  refine ⟨ψ', ⟨hmon' hmon, hact' hact, ⟨χ', d, hχmon' hχmon, hχact' hχact, qinv_pull m₁.cart hψ hχ e1,
    qinv_pull m₂.cart hχ hψ e2, hd⟩, ⟨c, hc, hlb' c ⟨lb⟩, tt⟩, ?_⟩, hψ⟩
  intro k _ _ t β ht
  obtain ⟨I₁, I₂, hI₁, hI₂, hev⟩ := hgeo k (t ≫ f) β (by rw [Category.assoc, hf, ht])
  obtain ⟨I₁', hI₁', hev₁⟩ := (hTate p D R gb S S' s s' f N₁ o₁ o₁' m₁ k t).1 I₁
  obtain ⟨I₂', hI₂', hev₂⟩ := (hTate p D R gb S S' s s' f N₂ o₂ o₂' m₂ k t).1 I₂
  refine ⟨I₁', I₂', hI₁' hI₁, hI₂' hI₂, fun n hn hnp x y => ?_⟩
  rw [← hev n hn hnp x y]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    have key := congrArg (fun a => a.left ≫ m₂.φ) e
    simp only [Over.comp_left, Category.assoc, hψ] at key
    erw [← Category.assoc, hev₁ n x, hev₂ n y] at key
    rw [Over.comp_left]
    exact key
  · intro e
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc]
      erw [hev₁ n x, hev₂ n y]
      rw [← Over.comp_left, e]
    · rw [Over.w, Over.w]
