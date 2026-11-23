import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowClassOfSplit

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adjust

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def IsDual0 (g : Fin D.R.rS → (VS D).V) : Prop :=
  ∀ a b, (VS D).hT (F0.e a) (g b) = if a = b then 1 else 0

def AggOK (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : Fin D.R.rS → (VS D).V) : Prop :=
  ∀ v ∈ Λ, ycL F0 g v ∈ Λ

variable {F0}

theorem int_smul_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {c : D.host.E}
    (hc : c ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) {v : (VS D).V} (hv : v ∈ Λ) : c • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hc
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ o hv

theorem hT_g_e {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (a b : Fin D.R.rS) :
    (VS D).hT (g a) (F0.e b) = if b = a then 1 else 0 := by
  rw [hT_swap D, hg b a]
  split_ifs <;> simp

theorem hT_g_xc {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (a : Fin D.R.rS) (v : (VS D).V) :
    (VS D).hT (g a) (xcL F0 g v) = (VS D).hT (g a) v := by
  rw [xcL_apply, map_sum]
  simp [hT_g_e hg]

theorem hT_xc_yc (g : Fin D.R.rS → (VS D).V) (l w : (VS D).V) :
    (VS D).hT l (xcL F0 g w) = (VS D).hT (ycL F0 g l) w := by
  rw [xcL_apply, ycL_apply, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_smul, smul_eq_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hT_swap D,
    mul_comm]

theorem xc_agg {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V}
    (hok : AggOK F0 Λ g) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {w : (VS D).V} (hw : w ∈ Λ) :
    xcL F0 g w ∈ Λ := by
  have h : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hu
  rw [← h, mem_dual_iff]
  intro l hl
  rw [hT_xc_yc]
  exact int_of_unimod hu (hok l hl) hw

theorem isSplitF_of {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f : Fin D.R.rS → (VS D).V}
    (hf : IsDualF F0 f) (hz : ∀ a, (VS D).hT (f a) F0.z = 0) (hok : AggOK F0 Λ f)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) : IsSplitF F0 Λ f := by
  refine ⟨hf, hz, ?_⟩
  intro v hv
  have hy : ycL F0 f v ∈ Λ := hok v hv
  have hw : v - ycL F0 f v ∈ Λ := Submodule.sub_mem _ hv hy
  have hx : xcL F0 f (v - ycL F0 f v) ∈ Λ := xc_agg hok hu hw
  refine ⟨xcL F0 f (v - ycL F0 f v), v - ycL F0 f v - xcL F0 f (v - ycL F0 f v), ycL F0 f v,
    hx, xc_mem_X _, Submodule.sub_mem _ hw hx, ?_, ?_, hy, yc_mem_span _, by abel⟩
  · intro a
    rw [map_sub, map_sub, hT_e_yc hf, sub_self, zero_sub, hX_X F0 (e_mem_X F0 a) (xc_mem_X _), neg_zero]
  · intro a
    rw [map_sub, hT_f_xc hf, sub_self]

end Adjust

def RowDualFrame : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∃ g : Fin D.R.rS → (VS D).V, IsDual0 F0 g ∧ AggOK F0 Λ g

def RowZUnit : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∃ l0 ∈ Λ, l0 ∈ perpS (VS D) F0.X ∧ (VS D).hT l0 F0.z = 1

def TraceOne : Prop :=
  ∀ D : D7, ∃ t : 𝓞 D.host.E, (t : D.host.E) + star (t : D.host.E) = 1

section Assembly

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}

def gz (g : Fin D.R.rS → (VS D).V) (l0 : (VS D).V) : Fin D.R.rS → (VS D).V :=
  fun b => g b - (VS D).hT F0.z (g b) • l0

def giso (F0 : FlagG (VS D) D.R.rS T) (g : Fin D.R.rS → (VS D).V) (t : D.host.E) : Fin D.R.rS → (VS D).V :=
  fun b => g b - t • xcL F0 g (g b)

theorem gz_dual {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) {l0 : (VS D).V}
    (hl : l0 ∈ perpS (VS D) F0.X) : IsDual0 F0 (gz (F0 := F0) g l0) := by
  intro a b
  rw [gz, map_sub, map_smul, hl _ (e_mem_X F0 a), smul_zero, sub_zero, hg a b]

theorem hermForm_shifted_vector_zero {g : Fin D.R.rS → (VS D).V} {l0 : (VS D).V} (hl1 : (VS D).hT l0 F0.z = 1) (b : Fin D.R.rS) :
    (VS D).hT (gz (F0 := F0) g l0 b) F0.z = 0 := by
  rw [gz, map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, hl1, starRingEnd_apply, smul_eq_mul,
    mul_one, ← hT_swap D, sub_self]

theorem yc_gz (g : Fin D.R.rS → (VS D).V) (l0 v : (VS D).V) :
    ycL F0 (gz (F0 := F0) g l0) v = ycL F0 g v - (VS D).hT F0.z (ycL F0 g v) • l0 := by
  rw [ycL_apply, ycL_apply, map_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [gz, smul_sub, map_smul, smul_eq_mul, smul_smul]

theorem gz_ok {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V} (hok : AggOK F0 Λ g)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (hzΛ : F0.z ∈ Λ) {l0 : (VS D).V} (hl0 : l0 ∈ Λ) :
    AggOK F0 Λ (gz (F0 := F0) g l0) := by
  intro v hv
  rw [yc_gz]
  exact Submodule.sub_mem _ (hok v hv) (int_smul_mem (int_of_unimod hu hzΛ (hok v hv)) hl0)

theorem giso_dual {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) (t : D.host.E) : IsDual0 F0 (giso F0 g t) := by
  intro a b
  rw [giso, map_sub, map_smul, hX_X F0 (e_mem_X F0 a) (xc_mem_X _), smul_zero, sub_zero, hg a b]

theorem hT_giso_z_eq_zero_of_hT_z_eq_zero {g : Fin D.R.rS → (VS D).V} (hz : ∀ b, (VS D).hT (g b) F0.z = 0) (t : D.host.E) (b : Fin D.R.rS) :
    (VS D).hT (giso F0 g t b) F0.z = 0 := by
  rw [giso, map_sub, LinearMap.sub_apply, hz b, map_smulₛₗ, LinearMap.smul_apply,
    hX_perp F0 (xc_mem_X _) (z_mem_perp D F0), smul_zero, sub_zero]

theorem yc_giso (g : Fin D.R.rS → (VS D).V) (t : D.host.E) (v : (VS D).V) :
    ycL F0 (giso F0 g t) v = ycL F0 g v - t • xcL F0 g (ycL F0 g v) := by
  rw [ycL_apply, ycL_apply, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [giso, smul_sub, map_smul, smul_comm]

theorem giso_ok {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : Fin D.R.rS → (VS D).V} (hok : AggOK F0 Λ g)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (t : 𝓞 D.host.E) : AggOK F0 Λ (giso F0 g (t : D.host.E)) := by
  intro v hv
  rw [yc_giso]
  refine Submodule.sub_mem _ (hok v hv) ?_
  rw [show ((t : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, algebraMap_smul]
  exact Submodule.smul_mem _ t (xc_agg hok hu (hok v hv))

theorem giso_iso {g : Fin D.R.rS → (VS D).V} (hg : IsDual0 F0 g) {t : D.host.E} (ht : t + star t = 1) :
    ∀ a b, (VS D).hT (giso F0 g t a) (giso F0 g t b) = 0 := by
  intro a b
  have h1 : (VS D).hT (g a) (xcL F0 g (g b)) = (VS D).hT (g a) (g b) := hT_g_xc hg a (g b)
  have h2 : (VS D).hT (xcL F0 g (g a)) (g b) = (VS D).hT (g a) (g b) := by
    rw [hT_swap D, hT_g_xc hg b (g a), ← hT_swap D]
  have h3 : (VS D).hT (xcL F0 g (g a)) (xcL F0 g (g b)) = 0 := hX_X F0 (xc_mem_X _) (xc_mem_X _)
  simp only [giso, map_sub, LinearMap.sub_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, h1, h2, h3, mul_zero]
  linear_combination (-(VS D).hT (g a) (g b)) * ht

end Assembly

theorem rowSplitF_of (h1 : RowDualFrame) (h2 : RowZUnit) (h3 : TraceOne) : RowSplitF := by
  intro D u F0 Λ hΛ
  obtain ⟨g, hg, hok⟩ := h1 D u F0 Λ hΛ
  obtain ⟨l0, hl0, hlp, hl1⟩ := h2 D u F0 Λ hΛ
  obtain ⟨t, ht⟩ := h3 D
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hzΛ : F0.z ∈ Λ := hΛ.2.1.2.2.1.1
  have hg' := gz_dual hg hlp
  have hok' := gz_ok hok hu hzΛ hl0
  have hz' := hermForm_shifted_vector_zero (F0 := F0) (g := g) hl1
  have hd := giso_dual hg' (t : D.host.E)
  exact ⟨giso F0 (gz (F0 := F0) g l0) (t : D.host.E),
    isSplitF_of ⟨hd, giso_iso hg' ht⟩ (hT_giso_z_eq_zero_of_hT_z_eq_zero hz' _) (giso_ok hok' hu t) hu⟩

theorem rowClass_of_three (h1 : RowDualFrame) (h2 : RowZUnit) (h3 : TraceOne) : RowClass :=
  rowClass_of_split (rowSplitF_of h1 h2 h3)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
