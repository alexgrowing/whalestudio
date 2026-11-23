import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalCuspSectionsVanishingOffDomainStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjectiveStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

open NumberField AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
set_option synthInstance.maxHeartbeats 400000 in

theorem _root_.GlobalTheory.cuspForms_finiteDimensional_of_isUnf : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt → ∀ (E : Type) [Field E]
    [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, _root_.Formalism.L2.PjFree.Unf Xo c σ r)
    (σ : c.F →+* ℂ), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf (U σ) → _root_.Formalism.L2.PjFree.CuspFD Xo c U := by
  intro hB E _ _ _ H Dw l Xo c r U σ hgood hunf
  unfold _root_.Formalism.L2.PjFree.CuspFD
  intro a n _
  obtain ⟨hind, -⟩ := _root_.GlobalTheory.reading_linearIndependent_and_injective hB E H Dw l Xo c σ r (U σ) hunf a n
  set V := _root_.Formalism.L2.PjFree.cusp Xo c U a n with hV
  set W : Submodule ℂ (_root_.Formalism.L2.PjFree.FDSec (U σ).X) :=
    Submodule.span ℂ ((_root_.Formalism.L2.PjFree.rdU (U σ)) '' (V : Set (_root_.Formalism.L2.Pj.Rul Xo c))) with hWdef
  have hWle : W ≤ _root_.Formalism.L2.PjFree.holSub (U σ).X (_root_.Formalism.L2.PjFree.laU (U σ) a n) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ((_root_.Formalism.L2.PjFree.mem_cusp Xo c U a n f).mp hf).2 σ hgood
  have hoff : ∀ P ∈ W, ∀ k, ∀ x ∉ ((U σ).X k).dom, P k x = 0 := by
    intro P hP k x hx
    induction hP using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, -, rfl⟩ := hg
      simp [_root_.Formalism.L2.PjFree.rdU, hx]
    | zero => rfl
    | add g h _ _ hg hh =>
      show g k x + h k x = 0
      rw [hg, hh, add_zero]
    | smul z g _ hg =>
      show z • g k x = 0
      rw [hg, smul_zero]
  haveI : FiniteDimensional ℂ W :=
    _root_.GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub E r (U σ).Comp (U σ).X
      (_root_.Formalism.L2.PjFree.laU (U σ) a n) W hWle hoff
  have hrank : Module.rank c.F V ≤ Module.finrank ℂ W := by
    apply rank_le
    intro s hs
    let e := s.equivFin
    let b : Fin s.card → _root_.Formalism.L2.Pj.Rul Xo c := fun i => ((e.symm i : s) : V).1
    have hbV : ∀ i, b i ∈ _root_.Formalism.L2.Pj.sec Xo c a n := fun i =>
      _root_.Formalism.L2.PjFree.cusp_le_sec Xo c U a n ((e.symm i : s) : V).2
    have hbind : LinearIndependent c.F b :=
      (hs.comp e.symm e.symm.injective).map' V.subtype V.ker_subtype
    have himg := hind s.card b hbV hbind
    let b' : Fin s.card → W := fun i =>
      ⟨_root_.Formalism.L2.PjFree.rdU (U σ) (b i), Submodule.subset_span ⟨b i, ((e.symm i : s) : V).2, rfl⟩⟩
    have hb' : LinearIndependent ℂ b' := LinearIndependent.of_comp W.subtype himg
    simpa using hb'.fintype_card_le_finrank
  exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.nat_lt_aleph0 _))

end GlobalTheory
