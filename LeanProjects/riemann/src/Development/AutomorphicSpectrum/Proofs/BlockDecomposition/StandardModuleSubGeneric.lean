import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents Zc Zc.Seg GlobalTheory.BZSeg
open GlobalTheory.Parabolic (Embeds)

namespace GlobalTheory.CompanionTheory.StdSubCusp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def top (Δ : Segment k) : IrrGL k := Δ.first.nu ((Δ.len - 1 : ℕ) : ℂ)

def Emb {p q : ℕ} (a : Fin p → IrrGL k) (b : Fin q → IrrGL k) : Prop :=
  ∃ (N : ℕ) (ha : ∑ i, (a i).1 = N) (hb : ∑ i, (b i).1 = N)
    (f : (prodIrr a ha).IntertwiningMap (prodIrr b hb)), Function.Injective f

theorem Emb.of_equiv {p q N : ℕ} {a : Fin p → IrrGL k} {b : Fin q → IrrGL k} (ha : ∑ i, (a i).1 = N)
    (hb : ∑ i, (b i).1 = N) (h : Nonempty ((prodIrr a ha).Equiv (prodIrr b hb))) : Emb a b := by
  obtain ⟨E⟩ := h
  exact ⟨N, ha, hb, E.toIntertwiningMap, E.toLinearEquiv.injective⟩

theorem Emb.trans {p q r : ℕ} {a : Fin p → IrrGL k} {b : Fin q → IrrGL k} {c : Fin r → IrrGL k} (h : Emb a b)
    (h' : Emb b c) : Emb a c := by
  obtain ⟨N, ha, hb, f, hf⟩ := h
  obtain ⟨N', hb', hc, g, hg⟩ := h'
  obtain rfl : N = N' := hb.symm.trans hb'
  exact ⟨N, ha, hc, g.comp f, hg.comp hf⟩

theorem prod₂_map_injective_right {r t : ℕ} {U W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (g : ρ.IntertwiningMap ρ') (hg : Function.Injective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ ρ'), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom), GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

end GlobalTheory.CompanionTheory.StdSubCusp

end
