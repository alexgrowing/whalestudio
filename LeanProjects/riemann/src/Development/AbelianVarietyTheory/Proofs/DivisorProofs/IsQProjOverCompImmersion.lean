import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

variable {O : Type} [Ring O]

def ActPB {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (z' : SiegPre h M ζ s') (act' : O → (z'.A ⟶ z'.A)) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A))
    (f : S' ⟶ S) : Prop :=
  ∃ (φ : z'.A.left ⟶ z.A.left) (φ₂ : (G2 z'.A).left ⟶ (G2 z.A).left),
    IsGrpPullback z'.A z.A f φ ∧ IsSquare φ φ₂ ∧ LBIso z'.P (z.P.pull φ₂) ∧
      (∀ a, (z'.lev a).left ≫ φ = f ≫ (z.lev a).left) ∧ ∀ o, (act' o).left ≫ φ = φ ≫ (act o).left

theorem ActPB.trans {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S' ⟶ Sp B} {s'' : S'' ⟶ Sp B} {z : SiegPre h M ζ s} {z' : SiegPre h M ζ s'} {z'' : SiegPre h M ζ s''}
    {act : O → (z.A ⟶ z.A)} {act' : O → (z'.A ⟶ z'.A)} {act'' : O → (z''.A ⟶ z''.A)} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m' : ActPB z'' act'' z' act' f') (m : ActPB z' act' z act f) :
    ActPB z'' act'' z act (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl, ha⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl', ha'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, GlobalTheory.TChart.AbPol.isSquare_comp hs' hs,
    GlobalTheory.TChart.AbLevel.lbIso_comp z.isLB z'.isLB z''.isLB hw hw', fun a => ?_, fun o => ?_⟩
  · rw [← Category.assoc, hl' a, Category.assoc, hl a, Category.assoc]
  · rw [← Category.assoc, ha' o, Category.assoc, ha o, Category.assoc]

def ZRel {h h' M : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {t : S ⟶ Sp B} (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) {n : ℕ} (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (c : SiegPre h M ζ t) (z : SiegPre h' M ζ t)
    (act : O → (z.A ⟶ z.A)) : Prop :=
  ∃ (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 c.A ∧ pr ≫ inc = act e ∧
    LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) ∧ (∀ a, c.lev a ≫ inc = z.lev (jl a)) ∧
    ∀ a, z.lev a = (List.ofFn fun k => c.lev (κ k a) ≫ inc ≫ act (o k)).prod

theorem isQProjOver_comp_immersion {R : Type} [CommRing R] {X Y : Scheme.{0}} (j : X ⟶ Y) (s : Y ⟶ Sp R)
    (hj : IsImmersion j) (hq : QuasiCompact j) (hs : IsQProjOver s) : IsQProjOver (j ≫ s) := by
  obtain ⟨N, i, hi, hiq, rfl⟩ := hs
  exact ⟨N, j ≫ i, inferInstance, inferInstance, (Category.assoc _ _ _).symm⟩

end GlobalTheory.UPel.HT
