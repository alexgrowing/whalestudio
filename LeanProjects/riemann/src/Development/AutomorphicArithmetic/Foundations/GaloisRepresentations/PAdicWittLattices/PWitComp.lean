import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelHomUnique
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

section Maps

open GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

private theorem exists_map_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    ∃ m : GObjMap o o (𝟙 S), m.φ = 𝟙 _ :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }, rfl⟩

private theorem exists_map_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
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

end Maps

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pWitComp :
    TransSelf → TransComp → TransPull → WitComp := by
  intro hS hC hP
  intro p _ D G L R _ _ gb N₁ N₂ N₃ X₁ X₂ X₃ h h'
  refine ⟨fun u hu => ?_, fun hI hA π Φ π' Φ' hW hW' => ?_⟩
  · obtain ⟨m, hm⟩ := exists_map_id X₁.univ
    refine ⟨by simp, X₁.univ, 𝟙 _, m, (hS p D G L R gb X₁.X X₁.s N₁).1 X₁.univ u hu, ?_⟩
    rw [hm]
    simp
  · obtain ⟨hπ, o, ψ, φ, hT, hΦ⟩ := hW
    obtain ⟨hπ', o', ψ', φ', hT', hΦ'⟩ := hW'
    obtain ⟨o'', ⟨m''⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero X₁.s π hπ o'
    obtain ⟨ψ'', hT'', hsq⟩ := hP p D G L R gb X₂.X X₁.X X₂.s X₁.s π hπ _ _ X₂.univ o' o o'' φ m'' ψ' h' hT'
    have hTT := hC p D G L R gb X₁.X X₁.s N₁ N₂ N₃ X₁.univ o o'' ψ ψ'' h h' hI hA hT hT''
    obtain ⟨mm, hmm⟩ := exists_map_comp m'' φ'
    refine ⟨by rw [Category.assoc, hπ', hπ], o'', ψ ≫ ψ'', mm, hTT, ?_⟩
    rw [hmm, hΦ, hΦ', Over.comp_left, Category.assoc, Category.assoc, ← Category.assoc φ.φ, ← hsq,
      Category.assoc]
