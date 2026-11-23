import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarMemIntegralLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentIntegralValuedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersEmbeddingFixedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormElementCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayPrimeOfNormIntegerCongruentOneStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.ElemAtStates

theorem allSt_and {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h1 : AllSt p) (h2 : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  EvG.imp (Step.and h1 h2) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => ⟨(G a b c).1 w hw P x, (G a b c).2 w hw P x⟩

theorem allSt_mono {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : AllSt p) (hq : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) : AllSt q :=
  EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => hq _ _ _ _ _ _ _ (G a b c w hw P x)

theorem elem_all : PrN → AllSt fun _ _ _ _ _ _ x => Elem (Dof x) ∧ ValLL0 (Dof x) (cfOf x) ∧ (Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y) ∧ ∃ (h : HostTied (Dof x)) (jE : (Dof x).host.E →+* Qb), (∀ y, jE y = h.fr.j y) ∧ ∀ k, IsRayPrime (GlobalTheory.HeightCounting.KQbar (Dof x) jE) ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) ((Dof x).host.g k) := by
  intro hP
  have h := allSt_and (allSt_and (allSt_and (GlobalTheory.T.star_mem_integral_lattice hP) (GlobalTheory.T.exponent_integral_valued hP)) (allSt_and (GlobalTheory.T.auxiliary_places_split hP) (GlobalTheory.T.valuation_fixed_lattice hP)))
    (allSt_and (GlobalTheory.T.ring_of_integers_embedding_fixed hP) (GlobalTheory.T.exists_norm_element_congruence hP))
  refine allSt_mono h ?_
  rintro K B f T w P x ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩
  refine ⟨⟨h1, h2, h3⟩, h4, h5, ?_⟩
  obtain ⟨hT⟩ := HostTied.exists (Dof x)
  exact ⟨hT, hT.fr.j.toRingHom, fun y => rfl, fun k => GlobalTheory.T.isRayPrime_of_norm_integer_congruent_one (Dof x) k _ (h6 k).1 (h6 k).2⟩

end GlobalTheory.ElemAtStates
