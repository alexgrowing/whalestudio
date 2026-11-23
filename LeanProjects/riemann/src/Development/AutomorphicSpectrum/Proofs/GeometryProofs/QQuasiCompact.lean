import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

structure AbQuot (t : SAB H X) {k : Type} [Field k] (x : Sp k ⟶ X) where

  tB : SAB H (Sp k)
  proper : IsProper tB.G.hom
  ktriv : Out.KTriv tB.G tB.PP.L

  Ch : Type
  [acg : AddCommGroup Ch]
  [free : Module.Free ℤ Ch]
  [fin : Module.Finite ℤ Ch]

  q : (Over.pullback x).obj t.G ⟶ tB.G
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surjective : Surjective q.left
  q_quasiCompact : QuasiCompact q.left

  i : splitTorus (Sp k) Ch ⟶ (Over.pullback x).obj t.G
  i_hom : IsMonHom i

  isKernel : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ tB.G)

  act_q : ∀ a, (Over.pullback x).map (t.act.act a) ≫ q = q ≫ tB.act.act a

  bun : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (tB.PP.L.pull q.left)

attribute [instance] AbQuot.acg AbQuot.free AbQuot.fin

variable [StarRing (𝓞 E)]

def AbQuot.IsDiff {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} (Q : AbQuot t x) {d d' : ℕ} (g : GermAt t x d)
    (gB : GermAt Q.tB (𝟙 (Sp k)) d') (P : Matrix (Fin d') (Fin d) k) : Prop :=
  ∀ (l : Fin d) (v : Sp (DualNumber k) ⟶ ((Over.pullback x).obj t.G).left),
    v ≫ pullback.fst t.G.hom x = g.tg l → v ≫ ((Over.pullback x).obj t.G).hom = spMap (algebraMap k (DualNumber k)) →
      IsCombAtG Q.tB (𝟙 (Sp k)) gB.tg (fun i => P i l) (v ≫ Q.q.left)

end GlobalTheory.CompanionTheory.Ar.Flat
