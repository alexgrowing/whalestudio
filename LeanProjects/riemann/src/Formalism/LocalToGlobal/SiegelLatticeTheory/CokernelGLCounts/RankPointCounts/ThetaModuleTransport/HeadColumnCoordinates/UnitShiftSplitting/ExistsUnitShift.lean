import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DetUpdateRowLastSingle
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ThetaMbeG

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem e_alg (g : SplitG M.L) (s : F) : g.e (algebraMap F E s) = (s, s) := by
  rw [AlgEquiv.commutes]
  rfl

theorem cj_alg (s : F) : M.L.cj (algebraMap F E s) = algebraMap F E s := M.L.cj.commutes s

theorem comp_mem_O (g : SplitG M.L) {x : E} (hx : x ∈ M.L.O) :
    (g.e x).1 ∈ 𝒪[F] ∧ (g.e x).2 ∈ 𝒪[F] := by
  have hxI : IsIntegral 𝒪[F] x := (M.L.O_def x).mp hx
  have key : ∀ f : E →ₐ[F] F, f x ∈ 𝒪[F] := fun f =>
    (Valuation.integer.integers (valuation F)).mem_of_integral (hxI.map (f.restrictScalars 𝒪[F]))
  exact ⟨key ((AlgHom.fst F F F).comp g.e.toAlgHom), key ((AlgHom.snd F F F).comp g.e.toAlgHom)⟩

theorem mem_R_of {g : SplitG M.L} (hs : M.split = some g) {x : E} (h1 : (g.e x).1 ∈ 𝒪[F])
    (h2 : (g.e x).2 ∈ 𝒪[F]) (h3 : ∃ c ∈ 𝒪[F], (g.e x).1 - (g.e x).2 = (g.q : F) * c) : x ∈ M.R := by
  obtain ⟨c, hc, hce⟩ := h3
  unfold Model.R
  rw [hs]
  dsimp only
  rw [Subring.mem_comap, Subring.mem_map]
  refine ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, rfl⟩
  rw [RingHom.mem_eqLocus, RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq,
    Ideal.mem_span_singleton']
  refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
  show c * (g.q : F) = (g.e x).1 - (g.e x).2
  rw [hce, mul_comm]

theorem alg_mem_R {g : SplitG M.L} (hs : M.split = some g) (a : 𝒪[F]) : algebraMap F E a ∈ M.R := by
  have he := e_alg g (a : F)
  refine mem_R_of hs ?_ ?_ ⟨0, zero_mem _, ?_⟩ <;> rw [he]
  · exact a.2
  · exact a.2
  · simp

theorem isUnit_of_comp (g : SplitG M.L) {y : E} (h1 : (g.e y).1 ≠ 0) (h2 : (g.e y).2 ≠ 0) : IsUnit y := by
  have hu : IsUnit (g.e y) := Prod.isUnit_iff.mpr ⟨h1.isUnit, h2.isUnit⟩
  exact (isUnit_map_iff g.e y).mp hu

theorem exists_unit_shift (g : SplitG M.L) (u : E) : ∃ a : 𝒪[F], IsUnit (u + algebraMap F E a) := by
  have hq0 : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have hq1 : (g.q : F) ≠ 1 := fun h => g.q_irr.not_isUnit (by
    rw [show g.q = 1 from Subtype.ext h]
    exact isUnit_one)
  have hsh : ∀ a : 𝒪[F], IsUnit (u + algebraMap F E a) ∨
      ((g.e u).1 + (a : F) = 0 ∨ (g.e u).2 + (a : F) = 0) := by
    intro a
    by_cases h1 : (g.e u).1 + (a : F) = 0
    · exact Or.inr (Or.inl h1)
    by_cases h2 : (g.e u).2 + (a : F) = 0
    · exact Or.inr (Or.inr h2)
    left
    apply isUnit_of_comp g
    · rw [map_add, e_alg g]
      exact h1
    · rw [map_add, e_alg g]
      exact h2
  rcases hsh 0 with h0 | h0
  · exact ⟨0, h0⟩
  rcases hsh 1 with h1 | h1
  · exact ⟨1, h1⟩
  rcases hsh g.q with h2 | h2
  · exact ⟨g.q, h2⟩
  exfalso
  push_cast at h0 h1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first
    | exact one_ne_zero (by linear_combination h1 - h0)
    | exact hq0 (by linear_combination h2 - h0)
    | exact hq1 (by linear_combination h2 - h1)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
