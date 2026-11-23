import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import GroundTheory.PAdicHodge.BdRLattice
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

def latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) : Subring (Formalism.Per6.BdRp l) :=
  Subring.closure (Set.range (wB l) ∪ (rB l) '' {x | x ∈ K' ∧ IsIntegral ℤ_[l] x})

theorem wB_mem_latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) (a : Wl l) :
    wB l a ∈ latS K' :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem rB_mem_latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) {x : Om l}
    (hx : x ∈ K') (hi : IsIntegral ℤ_[l] x) : rB l x ∈ latS K' :=
  Subring.subset_closure (Or.inr ⟨x, ⟨hx, hi⟩, rfl⟩)

theorem ker_thB_eq {l : ℕ} [Fact l.Prime] :
    RingHom.ker (thB l) = IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) :=
  (GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm

end GlobalTheory.CompanionTheory.LTPer
