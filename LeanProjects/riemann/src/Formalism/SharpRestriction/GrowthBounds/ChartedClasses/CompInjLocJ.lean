import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocTiesOf

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m)

section One

variable {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
  (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)
  {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad)

set_option maxHeartbeats 4000000 in

theorem compInj_locJ (hU : SameUlocJ hi S Uloc) : CompInj S (locJ hi t B) := by
  intro c c' δ hδ hoff
  have hδ0 : (reGL (rankN D (i + 1) hi) D.host.E).symm δ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram :=
    reGL_symm_mem_UJ (rankN D (i + 1) hi) _ _ _ (gramN_apply D (i + 1) hi) δ hδ
  have eδ : δ = reGL (rankN D (i + 1) hi) D.host.E ((reGL (rankN D (i + 1) hi) D.host.E).symm δ) :=
    (MulEquiv.apply_symm_apply _ _).symm
  set δ0 := (reGL (rankN D (i + 1) hi) D.host.E).symm δ with hδ0def
  have hz : ((t.yG c').1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1 ∈
      awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) := by
    rw [mem_awayG]
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (t.yG c').2) (bc_mem hδ0)) (t.yG c).2, fun w' hw' => ?_⟩
    have h1 := hoff w' hw'
    have e1 : ((locJ hi t B).yG c')⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * (locJ hi t B).yG c =
        reGL (rankN D (i + 1) hi) _ (((t.yG c').1)⁻¹ *
          bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1) := by
      rw [eδ, map_mul, map_mul, map_inv, ← bc_reGL]
      rfl
    rw [e1, bc_reGL, hU w'] at h1
    exact (Subgroup.mem_map_iff_mem (f := (reGL (rankN D (i + 1) hi) _).toMonoidHom)
      (reGL (rankN D (i + 1) hi) _).injective).1 h1
  apply t.yG_bij.1
  show (Quotient.mk'' (t.yG c) : compG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w)) = Quotient.mk'' (t.yG c')
  have hz' := Subgroup.inv_mem _ hz
  refine (DoubleCoset.eq _ _ _ _).2 ⟨⟨_, bc_mem hδ0⟩, Subgroup.mem_subgroupOf.2 ⟨δ0, hδ0, rfl⟩,
    ⟨_, ((mem_awayG _ _ _ _ _).1 hz').1⟩, Subgroup.mem_subgroupOf.2 hz', Subtype.ext ?_⟩
  show (t.yG c').1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1 *
    (((t.yG c').1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * (t.yG c).1)⁻¹
  group

end One

variable {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

set_option maxHeartbeats 4000000 in

theorem chX_stepInOf (Fo : FormsIn M (i + 1) hi) (Lc : LocIn X u w hg Lv i Fo.Ch)
    (pos : (Σ v : Fin (Fl.Pj (i + 1)).nV, Fin ((Fl.Pj (i + 1)).n' v)) ≃ D.what₂.Tau)
    (hU : ∀ β, SameUlocJ hi (Fo.K β).lev (Lc.Uloc β)) (hB : ∀ β, FrRatJ (Lc.t β) Lc.B) (hTc : ∀ β, HypTJC (Lc.t β)) :
    ChX (stepInOf hi Fo Lc pos) where
  hypC := fun (β : Fo.Ch) => locHypC_locJ hi (Lc.t β) Lc.B (Fo.K β).lev (hU β) (hB β) (hTc β)
  inj := fun (β : Fo.Ch) a => gamI_inj_locJ hi (Lc.t β) Lc.B a
  onto := fun (β : Fo.Ch) a => gamOnto_locJ hi (Lc.t β) Lc.B (Fo.K β).lev (hU β) a
  cinj := fun (β : Fo.Ch) => compInj_locJ hi (Lc.t β) Lc.B (Fo.K β).lev (hU β)

end Formalism.MainNotions.G.KAat

end
