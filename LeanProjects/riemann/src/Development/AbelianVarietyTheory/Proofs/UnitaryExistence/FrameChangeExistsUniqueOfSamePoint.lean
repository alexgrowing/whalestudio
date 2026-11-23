import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.ChgOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem scal_mul' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem gen_unit' {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul', _root_.mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one', _root_.one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

theorem appLE_id' {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (f : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom f = f := by
  simp only [Scheme.Hom.appLE]
  have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [e]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem spMap_id' (S : Type) [CommRing S] : spMap (RingHom.id S) = 𝟙 (Sp S) := by
  unfold spMap
  exact Spec.map_id _

theorem secBC_id_iff {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s t : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i := by
  constructor
  · rintro ⟨pm, h1, h2, h3⟩ i
    have hp : pm = 𝟙 _ := by
      rw [spMap_id'] at h2
      erw [Category.comp_id] at h2
      refine pullback.hom_ext ?_ ?_
      · exact h2.trans (Category.id_comp _).symm
      · exact h1.trans (Category.id_comp _).symm
    subst hp
    rw [← h3 i le_rfl]
    exact appLE_id' _ _ _
  · intro h
    refine ⟨𝟙 _, Category.id_comp _, ?_, fun i hi => ?_⟩
    · rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm
    · rw [h i]; exact appLE_id' _ _ _

end GlobalTheory.Frames.ChgOf

open GlobalTheory.Frames.ChgOf in

theorem GlobalTheory.Frames.frChg_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), (y'.x = y.x → ∃ (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) ∧ FrChg g (a : S) y y') ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y y' → g = g' ∧ a = a' := by
  intro E _ _ _ H Dw l Xo c S _ _ y y'
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  constructor
  · intro hx
    simp only at hx
    subst hx
    obtain ⟨N, _, _, v, ρ, hv, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S y.x
    choose g hg using fun τ i => (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).exists
    choose h hh using fun τ i => (basis' τ (y.u τ i) (y.tan τ i) (y.eig τ i)).exists
    obtain ⟨a, ha⟩ := gen_unit' y.s s' y.gen gen'
    refine ⟨fun τ => Matrix.of (g τ), a, fun τ => ?_, rfl, fun τ i => hg τ i, (secBC_id_iff _ _ _ _).2 ha⟩
    choose b hb using fun i => (htan _).1 (y.tan τ i)
    choose b' hb' using fun i => (htan _).1 (tan' τ i)
    have eb : y.u τ = fun i => v (b i) := funext fun i => (hb i).symm
    have eb' : u' τ = fun i => v (b' i) := funext fun i => (hb' i).symm
    have h1 : ∀ i, b' i = ∑ j, g τ i j • b j := fun i => by
      have := hg τ i
      rw [eb, hcomb, ← hb' i] at this
      exact hv this
    have h2 : ∀ i, b i = ∑ j, h τ i j • b' j := fun i => by
      have := hh τ i
      rw [eb', hcomb, ← hb i] at this
      exact hv this
    have hm : Matrix.of (h τ) * Matrix.of (g τ) = 1 := by
      funext i
      refine (y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique ?_ ?_
      · rw [← hb i, eb, hcomb]
        congr 1
        rw [h2 i]
        simp only [h1, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
        exact Finset.sum_comm
      · rw [← hb i, eb, hcomb]
        congr 1
        simp [Matrix.one_apply]
    exact Matrix.isUnit_det_of_left_inverse hm
  · rintro g g' a a' ⟨hx, h1, h2⟩ ⟨-, h1', h2'⟩
    simp only at hx h1 h2 h1' h2'
    subst hx
    refine ⟨funext fun τ => funext fun i => ?_, ?_⟩
    · exact (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).unique (h1 τ i) (h1' τ i)
    · exact (y.gen s').unique ((secBC_id_iff _ _ _ _).1 h2) ((secBC_id_iff _ _ _ _).1 h2')
