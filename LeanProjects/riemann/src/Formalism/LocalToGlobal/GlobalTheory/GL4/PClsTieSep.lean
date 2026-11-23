import Formalism.LocalToGlobal.GlobalTheory.GL4.Statement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.UG IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem ClassTie.eq_of_mul {hc : CMData F E} {S : HSpace E} {Lb : Submodule (𝓞 E) (Fin S.rank → E)}
    {U : Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F))} {cls : Type} {stab : cls → Type}
    [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}
    (X : Formalism.L2.Herm.ClassTie hc S Lb U stab lat) {c c' : cls} (a k : Formalism.L2.Herm.UAf hc S)
    (ha : a ∈ Formalism.L2.Herm.UFin hc S) (hk : (k : GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ U)
    (h : X.y c' = a * X.y c * k) : c = c' := by
  apply X.y_bij.1
  show DoubleCoset.mk _ _ (X.y c) = DoubleCoset.mk _ _ (X.y c')
  exact (DoubleCoset.eq _ _ _ _).2 ⟨a, ha, k, Subgroup.mem_subgroupOf.2 hk, h⟩

end General

theorem ColLevel.eq_of_mul {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)
    {c c' : C.cls 0} (a k : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    (ha : a ∈ (ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf
      (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
    (hk : (k : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ L.U)
    (h : L.y c' = a * L.y c * k) : c = c' := by
  apply L.y_bij.1
  show DoubleCoset.mk _ _ (L.y c) = DoubleCoset.mk _ _ (L.y c')
  exact (DoubleCoset.eq _ _ _ _).2 ⟨a, ha, k, Subgroup.mem_subgroupOf.2 hk, h⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
