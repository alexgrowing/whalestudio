import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumProd

def tensLB {X : Scheme.{0}} (L M : LB X) : LB X :=
  LB.mk (L.ι × M.ι) (fun p => L.U p.1 ⊓ M.U p.2) fun p q =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) *
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2)

abbrev extLB {X X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) : LB X :=
  tensLB (L₁.pull f₁) (L₂.pull f₂)

section MapsAt

variable {Y X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

def extIdx (j₁ : L₁.ι) (j₂ : L₂.ι) : (extLB L₁ L₂ f₁ f₂).ι :=
  ((fun _ => j₁, fun _ => j₂) : (PUnit → L₁.ι) × (PUnit → L₂.ι))

lemma mapsAt₂_le_a (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

lemma mapsAt₂_le_1 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₁ (fun _ : PUnit => p ≫ f₁) (fun _ => j₁) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.1 PUnit.unit
  exact h1

lemma mapsAt₂_le_2 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₂ (fun _ : PUnit => p ≫ f₂) (fun _ => j₂) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.2 PUnit.unit
  exact h1

def MapsAt₂ (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n)))
    (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n)))
    (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))) : Prop :=
  ∀ (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι),
    res (mapsAt₂_le_1 w p j₁ j₂ jL) (b₁.s fun _ => j₁) * res (mapsAt₂_le_2 w p j₁ j₂ jL) (b₂.s fun _ => j₂) =
      (pullU p _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL))) ^ n * res (mapsAt₂_le_a w p j₁ j₂ jL) (a.s fun _ => jL)

end MapsAt

structure IsSumPolAV {S : Scheme.{0}} (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A) : Prop where
  hom₁ : IsMonHom a₁
  hom₂ : IsMonHom a₂
  lim : IsIso (lift a₁ a₂)
  w : ∃ w : LB.Iso P.L (extLB P₁.L P₂.L a₁.left a₂.left), w.IsGen

variable {R : Type} [CommRing R] [IsDomain R]

structure IsSumDeg (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X)
    (q₂ : D.X →+ D₂.X) : Prop where
  hom₁ : IsMonHom p₁
  hom₂ : IsMonHom p₂
  lim : IsIso (lift p₁ p₂)
  xsum : Function.Bijective (q₁.prod q₂)
  c_pr₁ : ∀ x, D.c x ≫ p₁ = D₁.c (q₁ x)
  c_pr₂ : ∀ x, D.c x ≫ p₂ = D₂.c (q₂ x)
  w : ∃ w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left), w.IsGen ∧
    (∃ b₁ b₂, MapsAt₂ w (eSec D.P.A) 1 D.rig b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ D₁.rig ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ D₂.rig) ∧
    ∀ x, ∃ b₁ b₂, MapsAt₂ w (D.xK x) (-1) (D.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ (D₁.psi (q₁ x)) ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ (D₂.psi (q₂ x))

end GlobalTheory.MumProd
