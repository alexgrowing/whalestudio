import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.DescStepPf

def Bounds : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  ((chains R).obj E).IsStrictlyLE 0 ∧ (res R F).IsStrictlyGE 0 ∧ ∀ m, Injective ((res R F).X m)

def LevelIdent : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (p : ℕ) (j : ℤ),
  (Function.Bijective (pull R (disc.map (f.app (op (SimplexCategory.mk p)))) F j) ↔
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (((chains R).map f).f (-(p : ℤ)))) (res R F) j)) ∧
  (Function.Injective (pull R (disc.map (f.app (op (SimplexCategory.mk p)))) F j) ↔
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (((chains R).map f).f (-(p : ℤ)))) (res R F) j))

def CxDesc : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (n : ℤ),
  (∀ (p : ℕ) (j : ℤ), j < n → Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-(p : ℤ)))) I j)) →
  (∀ p : ℕ, Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-(p : ℤ)))) I n)) →
  (∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
  (∀ j : ℤ, j < n + 1 → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I (n + 1))

theorem DescStep_of (hB : Bounds) (hL : LevelIdent) (hX : CxDesc) : LateralTheory.E.t_E1Cut.DescStep := by
  intro _ R _ F E E' f n hc he
  obtain ⟨h1, h2, h3⟩ := hB R F E
  obtain ⟨h1', -, -⟩ := hB R F E'
  have := h2
  have := h1
  have := h1'
  exact hX R (res R F) h3 ((chains R).map f) n
    (fun p j hj => ((hL R F f p j).1).1 ((hc (op (SimplexCategory.mk p))).1 j hj))
    (fun p => ((hL R F f p n).2).1 (hc (op (SimplexCategory.mk p))).2)
    (fun j => ((hL R F f 0 j).1).1 (he j))

end LateralTheory.E.DescStepPf

end
