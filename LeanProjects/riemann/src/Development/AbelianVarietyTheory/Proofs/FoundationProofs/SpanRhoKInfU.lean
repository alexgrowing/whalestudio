import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.RealSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

theorem exists_cEmb_pi (σ : ι → (E →+* ℂ)) (hσ : Function.Injective (fun τ => InfinitePlace.mk (σ τ)))
    (g : ι → GL (Fin n) ℂ) (hg : ∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ y : infU E n, (MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) y.1 = g := by
  classical
  let J : Subgroup (ι → GL (Fin n) ℂ) :=
    ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype).range
  let Hs : ι → Subgroup (GL (Fin n) ℂ) := fun _ => (GlobalTheory.Branching.unitaryIncl n).range
  have hle : Subgroup.pi Set.univ Hs ≤ J := by
    rw [Subgroup.pi_le_iff]
    intro τ
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n (σ τ)
    let x := e.symm u
    have hx := Subgroup.mem_inf.1 x.2
    refine ⟨⟨x.1, hx.1⟩, ?_⟩
    funext τ'
    by_cases h : τ' = τ
    · subst h
      change cEmb (σ τ') x.1 = _
      rw [← he, e.apply_symm_apply]
      simp
    · have hne : InfinitePlace.mk (σ τ') ≠ InfinitePlace.mk (σ τ) := fun e' => h (hσ e')
      have h5 : x.1 ∈ (cEmb (E := E) (n := n) (σ τ')).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 (σ τ')) hne
      change cEmb (σ τ') x.1 = _
      rw [MonoidHom.mem_ker.1 h5]
      simp [h]
  obtain ⟨y, hy⟩ : g ∈ J := hle fun τ _ => ⟨⟨(g τ).val, hg τ⟩, Units.ext rfl⟩
  exact ⟨y, hy⟩

theorem span_rhoK_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι]
    (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) →
    FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) ∧ Submodule.span ℂ (Set.range ((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp
      ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype))) = ⊤ := by
  intro E _ _ _ n ι _ σ lam hσ
  haveI : ∀ τ, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  haveI hfd : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  refine ⟨hfd, ?_⟩
  rcases subsingleton_or_nontrivial (Formalism.L2.DIV.VV ℂ lam) with hs | hs
  · haveI : Subsingleton (Module.End ℂ (Formalism.L2.DIV.VV ℂ lam)) := inferInstance
    exact Subsingleton.elim _ _
  · exact GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ ((CuspRep.isIrreducible_iff _).2 ⟨inferInstance,
      fun U hU => GlobalTheory.CoefIrred.vv_irreducible_unitary ι n lam U fun g hg x hx => by
        obtain ⟨y, hy⟩ := exists_cEmb_pi (E := E) σ hσ g hg
        have := hU y x hx
        simpa [hy] using this⟩)

end GlobalTheory.RealSpan

end
