import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentNongenericQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CuspStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def EmbW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Representation ℂ (GL (Fin N) k) V)
    (W : List (IrrGL k)) : Prop :=
  ∃ (h : ∑ a, (W.get a).1 = N) (f : G.IntertwiningMap (prodIrr W.get h)), Function.Injective f

def Good (W : List (IrrGL k)) : Prop := W.Pairwise fun u v => v ≠ u.nu 1

def prod₂MapR {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (π₁ : Representation ℂ (GL (Fin r) k) U)
    {π₂ : Representation ℂ (GL (Fin t) k) X} {π₂' : Representation ℂ (GL (Fin t) k) Y}
    (f : π₂.IntertwiningMap π₂') : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁ π₂') :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁ π₂')
    ⟨TensorProduct.map LinearMap.id f.toLinearMap, fun g => by
      ext u x
      exact congrArg (fun b => π₁ g.1 u ⊗ₜ[ℂ] b) (f.isIntertwining _ _ g.2 x)⟩ _)

def prod₂MapL {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {π₁ : Representation ℂ (GL (Fin r) k) X}
    {π₁' : Representation ℂ (GL (Fin r) k) Y} (f : π₁.IntertwiningMap π₁')
    (π₂ : Representation ℂ (GL (Fin t) k) U) : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁' π₂) :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁' π₂)
    ⟨TensorProduct.map f.toLinearMap LinearMap.id, fun g => by
      ext x u
      exact congrArg (fun b => b ⊗ₜ[ℂ] π₂ g.2 u) (f.isIntertwining _ _ g.1 x)⟩ _)

def HasNG {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin N) k) V) (π' : Representation ℂ (GL (Fin N) k) W) : Prop :=
  ∃ F : π.IntertwiningMap π', ¬ IsGeneric F.ker.toRepresentation

def KerNG (W W' : List (IrrGL k)) : Prop :=
  ∀ (N : ℕ) (h : ∑ a, (W.get a).1 = N) (h' : ∑ a, (W'.get a).1 = N), HasNG (prodIrr W.get h) (prodIrr W'.get h')

theorem prodIrr_congr {p q N : ℕ} (hpq : p = q) (x : Fin p → IrrGL k) (y : Fin q → IrrGL k)
    (hxy : ∀ i, x i = y (Fin.cast hpq i)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) :
    Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst hpq
  obtain rfl : x = y := funext hxy
  exact ⟨.refl _⟩

theorem append_get {α : Type*} (A B : List α) (i : Fin (A.length + B.length)) :
    Fin.append A.get B.get i = (A ++ B).get (Fin.cast (List.length_append (as := A) (bs := B)).symm i) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    simp [List.getElem_append]
  · rw [Fin.append_right]
    simp [List.getElem_append]

theorem word_append_aux₁ (A B : List (IrrGL k)) {r t : ℕ} (hA : ∑ a, (A.get a).1 = r) (hB : ∑ a, (B.get a).1 = t)
    (h' : ∑ a, (Fin.append A.get B.get a).1 = r + t) :
    Nonempty ((prod₂ (prodIrr A.get hA) (prodIrr B.get hB)).Equiv (prodIrr (Fin.append A.get B.get) h')) :=
  GlobalTheory.T.product_irreducible_append_equiv k _ _ r t A.get B.get hA hB h'

theorem word_append_aux₂ (A B : List (IrrGL k)) {N : ℕ} (h : ∑ a, ((A ++ B).get a).1 = N)
    (h' : ∑ a, (Fin.append A.get B.get a).1 = N) :
    Nonempty ((prodIrr (Fin.append A.get B.get) h').Equiv (prodIrr (A ++ B).get h)) :=
  prodIrr_congr (List.length_append (as := A) (bs := B)).symm (Fin.append A.get B.get) (A ++ B).get
    (append_get A B) h' h

end GlobalTheory.CompanionTheory.CuspStd
