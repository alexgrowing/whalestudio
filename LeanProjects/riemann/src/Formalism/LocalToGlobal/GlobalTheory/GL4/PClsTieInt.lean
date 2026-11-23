import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieLoc
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale

noncomputable section

open NumberField Formalism.UG IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem pair_of_mem_dualL (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) {b : Fin S.rank → E} (hb : b ∈ Formalism.L2.Herm.dualL hc S Λ) :
    ∀ a ∈ Λ, hform (hc.sig : E →+* E) S.gram a b ∈ (algebraMap (𝓞 E) E).range := by
  intro a ha
  unfold Formalism.L2.Herm.dualL at hb
  induction hb using Submodule.span_induction with
  | mem b hb => exact hb a ha
  | zero => rw [Formalism.UG.P.csScale_hform_zero_right]; exact zero_mem _
  | add b b' _ _ h h' => rw [Formalism.UG.P.csScale_hform_add_right]; exact add_mem h h'
  | smul r b _ h =>
    rw [← algebraMap_smul E r b, Formalism.UG.P.csScale_hform_smul_right]
    exact mul_mem ⟨r, rfl⟩ h

theorem ClassTie.lat_int {hc : Formalism.BasicNotions.CMData F E} {S : Formalism.BasicNotions.HSpace E} {Lb : Submodule (𝓞 E) (Fin S.rank → E)}
    {U : Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F))} {cls : Type} {stab : cls → Type}
    [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}
    (X : Formalism.L2.Herm.ClassTie hc S Lb U stab lat) (hLb : Lb ≤ Formalism.L2.Herm.dualL hc S Lb) (c : cls)
    {x y : S.V} (hx : x ∈ lat c) (hy : y ∈ lat c) : S.hT x y ∈ (algebraMap (𝓞 E) E).range := by
  have : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  apply mem_intOE_of_inclE F E
  have hm : ∀ a ∈ Lb, ∀ b ∈ Lb, IsIntegral ℤ (((1 : ℤ) : E) * hform (hc.sig : E →+* E) S.gram a b) := by
    intro a ha b hb
    obtain ⟨o, ho⟩ := pair_of_mem_dualL hc S Lb (hLb hb) a ha
    rw [Int.cast_one, one_mul, ← ho]
    exact RingOfIntegers.isIntegral_coe o
  have hglob : ∀ z ∈ lat c, Formalism.L2.Herm.crd S z ∈ Formalism.UG.CS.globLat (X.y c : GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)) Lb := by
    intro z hz
    show _ ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) _ Lb
    refine ((X.y_lat c _).1 ?_)
    exact Submodule.subset_span ⟨Formalism.L2.Herm.crd S z, ⟨z, hz, rfl⟩, rfl⟩
  have key := Formalism.UG.P.csScale_glob hc.sig S.gram Lb 1 hm (X.y c) (X.y c).2 (hglob x hx) (hglob y hy)
  rw [Int.cast_one, one_mul] at key
  rw [Formalism.L2.Herm.hT_crd hc]
  exact key

theorem ColLevel.lat_int {R : Formalism.BasicNotions.Ranks} {sp : Formalism.BasicNotions.Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hcp : ι → Formalism.BasicNotions.HCParam R} {C : Formalism.BasicNotions.ColumnChain R ι hcp}
    {A : Formalism.BasicNotions.ColumnsAtT R C} {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    (L : Formalism.BasicNotions.ColLevel R F E sp gp C A clsLat) (c : C.cls 0)
    {x y : (sp.X 0).V} (hx : x ∈ clsLat 0 c) (hy : y ∈ clsLat 0 c) :
    (sp.X 0).hT x y ∈ (algebraMap (𝓞 E) E).range := by
  have : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  apply mem_intOE_of_inclE F E
  have hm : ∀ a ∈ L.Lb, ∀ b ∈ L.Lb,
      IsIntegral ℤ (((1 : ℤ) : E) * hform (sp.cm.sig : E →+* E) sp.gram0 a b) := by
    intro a ha b hb
    obtain ⟨o, ho⟩ := L.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← ho]
    exact RingOfIntegers.isIntegral_coe o
  have hglob : ∀ z ∈ clsLat 0 c,
      sp.crd0 z ∈ Formalism.UG.CS.globLat (L.y c : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) L.Lb := by
    intro z hz
    show _ ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) _ L.Lb
    refine ((L.y_lat c _).1 ?_)
    exact Submodule.subset_span ⟨sp.crd0 z, ⟨z, hz, rfl⟩, rfl⟩
  have key := Formalism.UG.P.csScale_glob sp.cm.sig sp.gram0 L.Lb 1 hm (L.y c) (L.y c).2 (hglob x hx) (hglob y hy)
  rw [Int.cast_one, one_mul] at key
  rw [sp.hermitianForm_base_coordinates]
  exact key

end General

open Formalism.BasicNotions in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem clsLat_int {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m)
    (c : (D.mem u).C.cls i) :
    ∀ x ∈ D.clsLat u i c, x ∈ Formalism.MainNotions.flipTwoThree.dualSub (D.sp.X i) (D.clsLat u i c) := by
  intro x hx y hy
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact ColLevel.lat_int (X.base.lev0 u) c hy hx
  · exact ClassTie.lat_int (X.base.cls u i h1 hi) (X.base.lev u i h1 hi).Lb_int c hy hx

open Formalism.BasicNotions in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem clsLatP_int {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) (c : (D.fm u).clsP) :
    ∀ x ∈ (X.atT u).lattice₂ c, x ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' ((X.atT u).lattice₂ c) := by
  intro x hx y hy
  refine ClassTie.lat_int (X.atT u).clsP ?_ c hy hx
  rw [Formalism.L2.Herm.coordinate_lattice_self_dual]

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
