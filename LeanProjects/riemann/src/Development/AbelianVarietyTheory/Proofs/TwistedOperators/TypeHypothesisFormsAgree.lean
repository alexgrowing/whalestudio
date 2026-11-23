import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TypeHypForms

open GlobalTheory.SmGL in

theorem unipBlock_subset_radicalTwo {k : Type} [Field k] {a b r : ℕ} (h : a + b = r) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock k r a ⊆ (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.radicalTwo k h : Set (GL (Fin r) k)) := by
  intro g hg
  rw [SetLike.mem_coe, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.radicalTwo, mem_unipRad]
  refine ⟨(mem_parab_two k).2 fun j i => ?_, ?_⟩
  · have hj := j.isLt
    have hi := i.isLt
    rw [hg (stdSum h (.inr j)) (stdSum h (.inl i)) (by simp only [stdSum_inl, stdSum_inr]; omega),
      Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp only [stdSum_inl, stdSum_inr] at this
    omega
  · rintro (_ | _) i j
    · have hj := j.isLt
      have hi := i.isLt
      show (g : Matrix (Fin r) (Fin r) k) (stdSum h (.inl i)) (stdSum h (.inl j)) = (1 : Matrix (Fin a) (Fin a) k) i j
      rw [hg _ _ (by simp only [stdSum_inl, stdSum_inr]; omega)]
      simp only [Matrix.one_apply, (stdSum h).injective.eq_iff, Sum.inl.injEq]
    · have hj := j.isLt
      have hi := i.isLt
      show (g : Matrix (Fin r) (Fin r) k) (stdSum h (.inr i)) (stdSum h (.inr j)) = (1 : Matrix (Fin b) (Fin b) k) i j
      rw [hg _ _ (by simp only [stdSum_inl, stdSum_inr]; omega)]
      simp only [Matrix.one_apply, (stdSum h).injective.eq_iff, Sum.inr.injEq]

theorem noRadicalFixed_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (hT : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T := by
  intro a b h ha hb
  obtain ⟨v, hv⟩ := hT.2 a ha (by omega)
  refine ⟨v, (Submodule.eq_bot_iff _).2 fun y hy => hv y fun g hg => ?_⟩
  have := hy ⟨g, unipBlock_subset_radicalTwo h hg⟩
  simpa using this

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem hypH_and_noRadicalFixed : ∀ (D : D7) (V : HSp D) (T : TypeDataG V), NoFixed T → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T :=
  fun _ _ T h => ⟨hypH_of_noFixed T h, noRadicalFixed_of_noFixed T h⟩

end GlobalTheory.TypeHypForms

end
