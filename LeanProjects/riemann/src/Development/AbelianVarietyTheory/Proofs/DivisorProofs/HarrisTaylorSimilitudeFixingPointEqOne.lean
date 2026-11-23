import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTQuotRigid

theorem objMap_comp_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
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

theorem eq_one_of_fixes_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
      (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
      IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  intro p _ D R _ b N h M hN hNp hM X s s₁ u lev hlev ρ hρ k _ _ y a hya
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨-, -, m, hm⟩ := hρ a
  obtain ⟨o, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N X (Sp k) s y u
  obtain ⟨c, hc⟩ := objMap_comp_φ n m
  have key : ∀ (f : Sp k ⟶ X), f = y → ∀ mm : ObjMap o u f, mm.φ = n.φ := by
    intro f hf mm
    subst hf
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ _ mm n
  have hφ : n.φ ≫ m.φ = n.φ := by rw [← hc]; exact key _ hya c

  have hx : ∀ x, y ≫ (sympTwist a lev x).left = y ≫ (lev x).left := by
    intro x
    have ht : (y ≫ (sympTwist a lev x).left) ≫ u.A.hom = 𝟙 (Sp k) ≫ y := by
      rw [Category.assoc, Over.w]
      rfl
    have hσ := n.cart.1.lift_fst (y ≫ (sympTwist a lev x).left) (𝟙 _) ht
    have e1 : (y ≫ (sympTwist a lev x).left) ≫ m.φ = y ≫ (lev x).left := by
      rw [Category.assoc, hm x, ← Category.assoc, hya]
    rw [← e1, ← hσ, Category.assoc, hφ]

  let β : cycAway M →+* k := (Spec.preimage (y ≫ s₁)).hom
  have hβ : y ≫ s₁ = spMap β := by
    change y ≫ s₁ = Spec.map (CommRingCat.ofHom (Spec.preimage (y ≫ s₁)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hpow : β (zetaAway M) ^ M = 1 := by rw [← map_pow, zetaAway_pow_self hM.ne', map_one]
  let z : kˣ := Units.ofPowEqOne _ M hpow hM.ne'
  have hcl := (hlev.2.2 k y β z hβ rfl).1
  have hunit : ∀ x, (toUnit (Over.mk y) ≫ lev x).left = y ≫ (lev x).left := by
    intro x
    rw [Over.comp_left]
    congr 1
  have hfix : ∀ x, (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x) =
      reduceMod M x := by
    intro x
    set c := liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))
    have hsame : toUnit (Over.mk y) ≫ lev c = toUnit (Over.mk y) ≫ lev x := by
      ext1
      rw [hunit, hunit]
      exact hx x
    have hsplit : lev c = lev (c - x) * lev x := by rw [← hlev.1, sub_add_cancel]
    have h1 : toUnit (Over.mk y) ≫ lev (c - x) = 1 := by
      rw [hsplit, comp_mul] at hsame
      exact mul_eq_right.1 hsame
    obtain ⟨d, hd⟩ := (hcl (c - x)).1 h1
    have hr : reduceMod M c = reduceMod M x := by
      have : c = x + M • d := by rw [← hd]; abel
      rw [this]
      funext i
      simp [reduceMod]
    exact (reduceMod_liftMod _).symm.trans hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have := hfix (liftMod v)
  rw [reduceMod_liftMod] at this
  exact this

end GlobalTheory.HTQuotRigid
