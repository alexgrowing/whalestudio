import Formalism.AdmissibleDesigns.FiniteClassesRowEqGeneric
import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT' w)] [∀ w, TopologicalSpace (VT' w)] [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)]
  {T₁ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁]

def RowTop1 : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c

theorem rowTop_of
    (hT : ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
      KBKa.TopMatch (eK (D.nbr i _ hn)) (VT' n))
    (h1 : RowTop1 i dc (T₁ := T₁)) : RowTop i dc VT' (T₁ := T₁) := by
  intro n hn hpl
  refine ⟨fun c hc => ?_, h1 n hn hpl⟩
  have h := hT n hn hpl
  have h2 := (KBKa.cont_iff _ h _).1 hc
  have h3 : Continuous fun g => c (Br.iota D.nbr i _ hpl g) := h2
  obtain ⟨hm, hhm⟩ := KBKa.iotaHomeo_rec (i := i) (dc := dc) hpl
  have hc' : c = (fun g => c (Br.iota D.nbr i _ hpl g)) ∘ hm.symm := by
    funext x
    simp only [Function.comp, ← hhm]
    exact congrArg c (hm.apply_symm_apply x).symm
  rw [hc']
  exact h3.comp hm.symm.continuous

end Rec

end Formalism.MainNotions.N.KRow

end
