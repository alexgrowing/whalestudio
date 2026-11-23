import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FResLe

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

noncomputable def fib_init {C : Type u} [Category.{v} C] (T : C) :
    Limits.IsInitial (StructuredArrow.mk (𝟙 T) : StructuredArrow T (𝟭 C)) :=
  StructuredArrow.mkIdInitial (T := 𝟭 C) (Y := T)

theorem fib_to {C : Type u} [Category.{v} C] (T : C) (y : StructuredArrow T (𝟭 C)) :
    ((fib_init T).to y).right = y.hom := by
  have := (fib_init T).hom_ext ((fib_init T).to y) (StructuredArrow.homMk y.hom (by simp))
  exact congrArg CommaMorphism.right this

theorem fib_aug {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (T : C) :
    (aug (relF (m.G ⋙ 𝟭 C) F' T) fun x => ((relMor (𝟭 C) m T).τ x) ∘ₗ
      ((relF (𝟭 C) F T).map ((fib_init T).to ((relMor (𝟭 C) m T).G.obj x))).hom) =
    (aug (StructuredArrow.proj T m.G ⋙ F') fun x => (m.τ x.right) ∘ₗ (F.map x.hom).hom) := by
  apply LinearMap.ext; intro a; funext c
  change m.τ _ ((F.map ((fib_init T).to ((relMor (𝟭 C) m T).G.obj (c.obj (Fin.last 0)))).right).hom a) = m.τ _ ((F.map (c.obj (Fin.last 0)).hom).hom a)
  rw [fib_to]
  rfl

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.fib : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (s : R), (∀ T : C, (cx (StructuredArrow.proj T m.G ⋙ F')).ResUpTo s (aug (StructuredArrow.proj T m.G ⋙ F') fun x => (m.τ x.right) ∘ₗ (F.map x.hom).hom)) → ∀ n, IsoLe (s ^ (2 * n + 3)) n m := by
  intro R _ C _ C' _ F F' m s hT n
  have key : ∀ (T : C) q, UpTo s ((relMor (𝟭 C) m T).pull q) := by
    intro T
    refine (CrystallineSemistableComparison.B.P.res_le _ _ (relMor (𝟭 C) m T) _ (CrystallineSemistableComparison.B.fib_init T) s).1 ?_
    rw [CrystallineSemistableComparison.B.fib_aug m T]
    exact hT T
  intro j hj
  have h1 := CrystallineSemistableComparison.P.rel (𝟭 C) m s j (fun i q _ => key i q)
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  have e : s ^ (2 * (j + k) + 3) = s ^ (2 * j + 3) * s ^ (2 * k) := by rw [← pow_add]; ring_nf
  rw [e]
  exact (CrystallineSemistableComparison.P.upTo_alg (m.pull j) LinearMap.id _ _).2.2.2.1 h1
