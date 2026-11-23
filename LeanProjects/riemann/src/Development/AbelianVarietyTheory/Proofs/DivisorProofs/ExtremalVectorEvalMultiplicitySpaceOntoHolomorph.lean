import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspFormOfExtremalVectorMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCuspFormTransvectionConstantTermsZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedSectionOfBoundedHolomorphicFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicCuspFormOfAdelicConstantTermsZeroStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem HolForm.congr_level {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {w : D.what₂.Tau → Fin V.rank → ℤ} {J : Set (GA D V)} {χ χ' φ : GA D V → ℂ} (h : HolForm θ M w J χ φ)
    (e : ∀ k ∈ J, χ k = χ' k) : HolForm θ M w J χ' φ :=
  ⟨h.aut, h.bdd, fun k hk g => by rw [← e k hk]; exact h.lev k hk g, h.hol⟩

theorem mult_eval_eq_adel_holSub0 : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → WtIs M w → ∀ v : M.Vec, IsExtVec M v → ∀ χ : GA D V → ℂ, (∀ k ∈ Kf, χ k = 1) → (∀ P ∈ Formalism.L2.Pj.holSub0 X la, ∃ T ∈ Mult θ M (Kf : Set (GA D V)) χ, T v = adel V dict (muPin V dict mu c) P) ∧ ∀ T ∈ Mult θ M (Kf : Set (GA D V)) χ, ∃ P ∈ Formalism.L2.Pj.holSub0 X la, adel V dict (muPin V dict mu c) P = T v := by
  intro hdec hvol D θ V S M w r hr Comp X la dict mu c Kf hS hG hw v hv χ hχ
  refine ⟨fun P hP => ?_, fun T hT => ?_⟩
  · have hP1 : P ∈ Submodule.span ℂ {P | IsHolCusp X la P} := hP.1
    clear hP
    induction hP1 using Submodule.span_induction with
    | mem P hP =>
      have h1 := GlobalTheory.T.holomorphicAdelicForm_of_boundedSection D θ V S M w r hr Comp X la dict mu c Kf hS hG P (fun k => (hP k).1)
      have h2 := GlobalTheory.T.adelicCuspForm_transvection_constantTerms_zero D θ V S M w r hr Comp X la dict mu c Kf hS hG P hP
      obtain ⟨T, hT, hTv⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D θ V S M w v hG.inf hS hw hv (exists_finPair hvol D V)
        (Kf : Set (GA D V)) χ _ hG.levFin (h1.congr_level fun k hk => (hχ k hk).symm) h2
      exact ⟨T, Submodule.subset_span hT, hTv⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add P Q _ _ hP hQ =>
      obtain ⟨T, hT, hTv⟩ := hP
      obtain ⟨T', hT', hTv'⟩ := hQ
      exact ⟨T + T', Submodule.add_mem _ hT hT', by rw [map_add, _root_.add_apply, hTv, hTv']⟩
    | smul a P _ hP =>
      obtain ⟨T, hT, hTv⟩ := hP
      exact ⟨a • T, Submodule.smul_mem _ a hT, by rw [map_smul, _root_.smul_apply, hTv]⟩
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphic_cusp_form_of_extremal_vector_multiplicity hdec D θ V S M w v hG.inf hS hw hv (Kf : Set (GA D V)) χ T hT
    obtain ⟨P, hP0, hPb, hPe⟩ := GlobalTheory.T.exists_boundedSection_of_boundedHolomorphicForm D θ V S M w r hr Comp X la dict mu c Kf hS hG (T v)
      (h1.congr_level hχ)
    have hc := GlobalTheory.T.isHolomorphicCuspForm_of_adelic_constantTerms_zero D θ V S M w r hr Comp X la dict mu c Kf hS hG P hPb (hPe ▸ h2)
    exact ⟨P, ⟨holCusp_mem_holSub X la hc, hP0⟩, hPe⟩

end GlobalTheory.HolDict
