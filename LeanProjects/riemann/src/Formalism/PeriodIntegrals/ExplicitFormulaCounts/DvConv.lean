import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice

noncomputable section

namespace ChkDv

open Formalism.BasicNotions

def toT {K : Type} [Field K] {G : Type} [Group G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) : PI.Dv.GoodSet K G :=
  { S := T.S, finS := T.finS, decS := T.decS, W := T.W, acgW := T.acgW, modW := T.modW, fdW := T.fdW, ntW := T.ntW,
    tau := T.tau, irr := T.irr, inj := T.inj }

def toP {K : Type} [Field K] {G : Type} [Group G] (P : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) : PI.Dv.Pair K G := ⟨P.H, P.chi⟩

def toM {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G}
    {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
    (M : Formalism.MainNotions.PrimeDegreeVariant.GMap K σ G T EE ρE) : PI.Dv.GMap K σ G (toT T) EE ρE :=
  { VK := M.VK, acgK := M.acgK, modK := M.modK, fdK := M.fdK, rhoK := M.rhoK, V := M.V, acgV := M.acgV, modV := M.modV,
    rho := M.rho, j := M.j, j_indep := M.j_indep, j_span := M.j_span, j_eq := M.j_eq, good := M.good, io := M.io,
    io_eq := M.io_eq }

theorem c8 : PI.Dv.Conclusion8 → Formalism.MainNotions.PrimeDegreeVariant.Conclusion8 :=
  fun H K _ σ G _ _ T P0 h EE _ _ ρE M hr => H K σ G (toT T) (toP P0) h EE ρE (toM M) hr

theorem c8b : PI.Dv.SameFormAllLevels → Formalism.MainNotions.PrimeDegreeVariant.SameFormAllLevels :=
  fun H K _ σ G _ _ T P0 h EE _ _ ρE M M' hr =>
    ⟨(H K σ G (toT T) (toP P0) h EE ρE (toM M) (toM M') hr).1,
     fun P => (H K σ G (toT T) (toP P0) h EE ρE (toM M) (toM M') hr).2 (toP P)⟩

theorem c2E : PI.Dv.projection_lemma_base_level ↔ Formalism.MainNotions.PrimeDegreeVariant.projection_lemma_base_level := Iff.rfl
theorem c2dE : PI.Dv.gram_det_kernel_base_level ↔ Formalism.MainNotions.PrimeDegreeVariant.gram_det_kernel_base_level := Iff.rfl
theorem c7E : PI.Dv.division_rows_base_level ↔ Formalism.MainNotions.PrimeDegreeVariant.division_rows_base_level := Iff.rfl

theorem c2E' : PI.Dv.ProjA → PI.Dv.ProjB → PI.Dv.ProjC → Formalism.MainNotions.PrimeDegreeVariant.projection_lemma_base_level :=
  fun a b c K _ _ _ _ A e n h => ⟨a K A e n h, b K A e n h, c K A e n h⟩

theorem c2a : PI.Dv.ProjA → PI.Dv.GLatProj → Formalism.MainNotions.PrimeDegreeVariant.projection_sandwich_lattice :=
  fun a g K _ _ _ _ G _ _ T A ρ h => a K A _ _ (g K G (toT T) A ρ h)
theorem c2b : PI.Dv.ProjB → PI.Dv.GLatProj → Formalism.MainNotions.PrimeDegreeVariant.MassRatio₂ :=
  fun a g K _ _ _ _ G _ _ T A ρ h => a K A _ _ (g K G (toT T) A ρ h)
theorem c2c : PI.Dv.ProjC → PI.Dv.GLatProj → Formalism.MainNotions.PrimeDegreeVariant.kernel_index_full_lattice :=
  fun a g K _ _ _ _ G _ _ T A ρ h => a K A _ _ (g K G (toT T) A ρ h)

theorem c2d : PI.Dv.gram_det_kernel_base_level → PI.Dv.GLatProj → PI.Dv.GLatHerm → Formalism.MainNotions.PrimeDegreeVariant.gram_det_kernel_dual_lattice :=
  fun a g gh K _ _ _ _ G _ _ T A ρ h hs hg hh =>
    a K A _ _ h hs (g K G (toT T) A ρ hg) (gh K G (toT T) A ρ h hs hh).1

theorem c7 : PI.Dv.division_rows_base_level → PI.Dv.GLatProj → PI.Dv.GLatHerm → Formalism.MainNotions.PrimeDegreeVariant.division_rows_rational_lattice :=
  fun a g gh K _ _ _ _ _ G _ _ T A ρ h hs hg hh hc hd =>
    a K A _ _ h hs (g K G (toT T) A ρ hg) (gh K G (toT T) A ρ h hs hh).1 ((gh K G (toT T) A ρ h hs hh).2 hc) hd

theorem c4a : PI.Dv.Conclusion4a → Formalism.MainNotions.PrimeDegreeVariant.Conclusion4a :=
  fun H K _ _ _ _ G _ _ T P0 P h A ρ hg => H K G (toT T) (toP P0) (toP P) h A ρ hg

theorem c4b (C : ℝ) : PI.Dv.Conclusion4b C → Formalism.MainNotions.PrimeDegreeVariant.Conclusion4b C :=
  fun H K _ _ _ _ G _ _ T P0 P h => H K G (toT T) (toP P0) (toP P) h

end ChkDv
