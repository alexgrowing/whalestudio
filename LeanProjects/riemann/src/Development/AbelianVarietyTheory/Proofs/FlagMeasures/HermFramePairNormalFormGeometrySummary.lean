import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P

noncomputable section

namespace GlobalTheory.DegCnt.NFGeom

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem c_ne : N.c ≠ 0 := fun h => by simpa [h] using N.c_norm

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.Dl_ne :
    _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' N.j
      (N.j_le.trans (Nat.le_succ r)) ≠ 0 := by
  rw [_root_.Formalism.HermitianLatticeCounting.P.Dl_eq]
  have hmat : (Matrix.of fun a b => H.B (N.F.e
      (Fin.castLE (N.j_le.trans (Nat.le_succ r)) a))
      (N.F'.e (Fin.castLE (N.j_le.trans (Nat.le_succ r)) b))) =
      N.w.mat *
        Matrix.diagonal (fun b => (((N.sgn b : ℤˣ) : ℤ) : K)) := by
    ext a b
    simp [Matrix.mul_diagonal, N.pair]
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (_root_.GlobalTheory.SgLoc.PtAlg.isUnit_det _).ne_zero (Finset.prod_ne_zero_iff.2 fun b _ => ?_)
  exact_mod_cast (N.sgn b).ne_zero

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.e_eq (a : Fin (r + 1))
    (h : N.j ≤ a.val) :
    N.F.e a = N.c⁻¹ • N.F'.e a := by
  have hc : N.c ≠ 0 := left_ne_zero_of_mul_eq_one N.c_norm
  rw [N.same a h, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem z'_eq : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simpa using N.j_le)

theorem z_eq : N.F.z = N.c⁻¹ • N.F'.z := e_eq N (Fin.last r) (by simpa using N.j_le)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.e_mem_II (a : Fin r)
    (h : N.j ≤ a.val) :
    N.F.e a.castSucc ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.II
  refine Submodule.mem_inf.2 ⟨_root_.Formalism.HermitianLatticeCounting.P.e_mem_X _ a, ?_⟩
  rw [_root_.GlobalTheory.DegCnt.NFGeom.e_eq N a.castSucc h]
  exact Submodule.smul_mem _ _ (_root_.Formalism.HermitianLatticeCounting.P.e_mem_X _ a)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.e'_mem_II (a : Fin r)
    (h : N.j ≤ a.val) :
    N.F'.e a.castSucc ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
  rw [N.same a.castSucc h]
  exact Submodule.smul_mem _ _ (_root_.GlobalTheory.DegCnt.NFGeom.e_mem_II N a h)

def proj : V →ₗ[K] V :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin r => N.j ≤ b.val),
    (H.B.flip (N.ist b)).smulRight (N.F.e b.castSucc)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.proj_apply (y : V) :
    _root_.GlobalTheory.DegCnt.NFGeom.proj N y =
      ∑ b ∈ Finset.univ.filter (fun b : Fin r => N.j ≤ b.val),
        H.B y (N.ist b) • N.F.e b.castSucc := by
  simp [_root_.GlobalTheory.DegCnt.NFGeom.proj, LinearMap.sum_apply]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.proj_mem (y : V) :
    _root_.GlobalTheory.DegCnt.NFGeom.proj N y ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
  rw [_root_.GlobalTheory.DegCnt.NFGeom.proj_apply]
  exact Submodule.sum_mem _ fun b hb =>
    Submodule.smul_mem _ _ (_root_.GlobalTheory.DegCnt.NFGeom.e_mem_II N b (Finset.mem_filter.1 hb).2)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.proj_zero {y : V}
    (h : ∀ u ∈ N.Ist, H.B y u = 0) : _root_.GlobalTheory.DegCnt.NFGeom.proj N y = 0 := by
  rw [_root_.GlobalTheory.DegCnt.NFGeom.proj_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hu : N.ist b ∈ N.Ist := by
    unfold _root_.GlobalTheory.DegCnt.NF.Ist
    exact Submodule.subset_span ⟨b, (Finset.mem_filter.1 hb).2, rfl⟩
  rw [h _ hu, zero_smul]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem sub_proj_mem_perp_Ist (y : V) :
    y - _root_.GlobalTheory.DegCnt.NFGeom.proj N y ∈ _root_.GlobalTheory.HermLat.perp H N.Ist := by
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
  intro u hu
  have hle : N.Ist ≤
      LinearMap.ker (H.B (y - _root_.GlobalTheory.DegCnt.NFGeom.proj N y)) := by
    unfold _root_.GlobalTheory.DegCnt.NF.Ist
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : N.j ≤ b.val := hb
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply,
      _root_.GlobalTheory.DegCnt.NFGeom.proj_apply, map_sum, LinearMap.sum_apply]
    simp_rw [map_smul, LinearMap.smul_apply, N.ist_e _ _ hb']
    simp [hb']
  exact LinearMap.mem_ker.1 (hle hu)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.proj_II {x : V}
    (hx : x ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F') :
    _root_.GlobalTheory.DegCnt.NFGeom.proj N x = x := by
  set d := x - _root_.GlobalTheory.DegCnt.NFGeom.proj N x with hd_def
  have hdII : d ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' :=
    Submodule.sub_mem _ hx (_root_.GlobalTheory.DegCnt.NFGeom.proj_mem N x)
  have hdperp := sub_proj_mem_perp_Ist N x
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hdperp
  have hdX : d ∈ N.F.X := by
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hdII
    exact (Submodule.mem_inf.1 hdII).1
  have hdXa : d ∈ N.F.Xa N.j := by
    have hX : N.F.X = Submodule.span K (Set.range
        (fun a : Fin r => N.F.e a.castSucc)) := by
      unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.X _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa
      congr 1
      ext v
      simp
    rw [hX, Submodule.mem_span_range_iff_exists_fun] at hdX
    obtain ⟨c, hc⟩ := hdX
    have hcz : ∀ b : Fin r, N.j ≤ b.val → c b = 0 := by
      intro b hb
      have h1 := hdperp (N.ist b) (by
        unfold _root_.GlobalTheory.DegCnt.NF.Ist
        exact Submodule.subset_span ⟨b, hb, rfl⟩)
      rw [← hd_def, ← hc, _root_.Formalism.HermitianLatticeCounting.P.B_sum_left] at h1
      simp_rw [N.ist_e _ _ hb] at h1
      simpa using h1
    rw [← hc]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : a.val < N.j
    · exact Submodule.smul_mem _ _ (_root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa _ a ha)
    · rw [hcz a (not_lt.1 ha), zero_smul]
      exact Submodule.zero_mem _
  have hd0 : d = 0 := by
    refine _root_.Formalism.HermitianLatticeCounting.P.Dl_injL _ _ N.j_le
      (_root_.GlobalTheory.DegCnt.NFGeom.Dl_ne N) hdXa fun u hu => ?_
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hdII
    exact _root_.Formalism.HermitianLatticeCounting.P.X_iso _ (Submodule.mem_inf.1 hdII).2 (_root_.Formalism.HermitianLatticeCounting.P.Xa_le_X _ _ hu)
  exact (sub_eq_zero.1 hd0).symm

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem F_aniso : N.F.Aniso := by
  intro w hw hww
  by_contra hX
  have hpos := N.posdef (Classical.arbitrary (K →+* ℂ)) w hw hX
  rw [hww, map_zero, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem mem_F_Xa_of_mem_F_X_of_B_Ist_eq_zero {y : V} (hy : y ∈ N.F.X)
    (hperp : ∀ u ∈ N.Ist, H.B y u = 0) :
    y ∈ N.F.Xa N.j := by
  have hX : N.F.X = Submodule.span K (Set.range
      (fun a : Fin r => N.F.e a.castSucc)) := by
    unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.X _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa
    congr 1
    ext v
    simp
  rw [hX, Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨c, hc⟩ := hy
  have hcz : ∀ b : Fin r, N.j ≤ b.val → c b = 0 := by
    intro b hb
    have h1 := hperp (N.ist b) (by
      unfold _root_.GlobalTheory.DegCnt.NF.Ist
      exact Submodule.subset_span ⟨b, hb, rfl⟩)
    rw [← hc, _root_.Formalism.HermitianLatticeCounting.P.B_sum_left] at h1
    simp_rw [N.ist_e _ _ hb] at h1
    simpa using h1
  rw [← hc]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a.val < N.j
  · exact Submodule.smul_mem _ _ (_root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa _ a ha)
  · rw [hcz a (not_lt.1 ha), zero_smul]
    exact Submodule.zero_mem _

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem F'_aniso : N.F'.Aniso := by
  intro w hw hww
  have hwX' : ∀ u ∈ N.F'.X, H.B u w = 0 :=
    _root_.Formalism.HermitianLatticeCounting.P.perp_X _ (fun b => hw b.castSucc)
  have hjr : N.j ≤ r + 1 := N.j_le.trans (Nat.le_succ r)
  have hDl' : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F' N.F N.j hjr
      ≠ 0 := by
    rw [_root_.Formalism.HermitianLatticeCounting.P.Dl_swap]
    exact star_ne_zero.2 (_root_.GlobalTheory.DegCnt.NFGeom.Dl_ne N)
  obtain ⟨x, hx, hxe⟩ := _root_.Formalism.HermitianLatticeCounting.P.Dl_solveL N.F' N.F
    N.j_le hDl'
    (fun b => H.B w (N.F.e (Fin.castLE hjr b)))
  have hxX' : x ∈ N.F'.X := _root_.Formalism.HermitianLatticeCounting.P.Xa_le_X _ _ hx
  have hyF : ∀ a : Fin (r + 1), H.B (N.F.e a) (w - x) = 0 := by
    intro a
    by_cases ha : a.val < N.j
    · apply _root_.Formalism.HermitianLatticeCounting.P.B_swap0
      have h1 := hxe ⟨a.val, ha⟩
      have hcast : Fin.castLE hjr (⟨a.val, ha⟩ : Fin N.j) = a := Fin.ext rfl
      simp only [hcast] at h1
      rw [map_sub, LinearMap.sub_apply, h1, sub_self]
    · rw [_root_.GlobalTheory.DegCnt.NFGeom.e_eq N a (not_lt.1 ha), map_smul,
        LinearMap.smul_apply, map_sub, hw a, _root_.Formalism.HermitianLatticeCounting.P.e_X _ a hxX', sub_zero, smul_zero]
  have hyy : H.B (w - x) (w - x) = 0 := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hww, hwX' x hxX', _root_.Formalism.HermitianLatticeCounting.P.B_swap0 H (hwX' x hxX'), _root_.Formalism.HermitianLatticeCounting.P.X_iso _ hxX' hxX']
    simp
  have hyX : w - x ∈ N.F.X := F_aniso N (w - x) hyF hyy
  have hpX : _root_.GlobalTheory.DegCnt.NFGeom.proj N (w - x) ∈ N.F.X := by
    have := _root_.GlobalTheory.DegCnt.NFGeom.proj_mem N (w - x)
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at this
    exact (Submodule.mem_inf.1 this).1
  have hpX' : _root_.GlobalTheory.DegCnt.NFGeom.proj N (w - x) ∈ N.F'.X := by
    have := _root_.GlobalTheory.DegCnt.NFGeom.proj_mem N (w - x)
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at this
    exact (Submodule.mem_inf.1 this).2
  have hd : w - x - _root_.GlobalTheory.DegCnt.NFGeom.proj N (w - x) = 0 := by
    have hperp := sub_proj_mem_perp_Ist N (w - x)
    rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hperp
    refine _root_.Formalism.HermitianLatticeCounting.P.Dl_injL _ _ N.j_le (_root_.GlobalTheory.DegCnt.NFGeom.Dl_ne N)
      (mem_F_Xa_of_mem_F_X_of_B_Ist_eq_zero N (Submodule.sub_mem _ hyX hpX) hperp) fun u hu => ?_
    have huX' := _root_.Formalism.HermitianLatticeCounting.P.Xa_le_X _ _ hu
    apply _root_.Formalism.HermitianLatticeCounting.P.B_swap0
    rw [map_sub (H.B u) (w - x), map_sub (H.B u) w x, hwX' u huX', _root_.Formalism.HermitianLatticeCounting.P.X_iso _ huX' hxX',
      _root_.Formalism.HermitianLatticeCounting.P.X_iso _ huX' hpX']
    simp
  have hw' : w = _root_.GlobalTheory.DegCnt.NFGeom.proj N (w - x) + x := by
    rw [← sub_eq_zero, ← hd]
    abel
  rw [hw']
  exact Submodule.add_mem _ hpX' hxX'

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem II_inf_F_Xa_eq_bot :
    _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ⊓
      N.F.Xa N.j = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hII, hXa⟩ := Submodule.mem_inf.1 hx
  unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hII
  rw [Submodule.mem_bot]
  exact _root_.Formalism.HermitianLatticeCounting.P.Dl_injL _ _ N.j_le (_root_.GlobalTheory.DegCnt.NFGeom.Dl_ne N) hXa
    fun u hu => _root_.Formalism.HermitianLatticeCounting.P.X_iso _ (Submodule.mem_inf.1 hII).2 (_root_.Formalism.HermitianLatticeCounting.P.Xa_le_X _ _ hu)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem II_inf_F'_Xa_eq_bot :
    _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ⊓
      N.F'.Xa N.j = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hII, hXa⟩ := Submodule.mem_inf.1 hx
  unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hII
  rw [Submodule.mem_bot]
  have hjr : N.j ≤ r + 1 := N.j_le.trans (Nat.le_succ r)
  have hDl' : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F' N.F N.j hjr
      ≠ 0 := by
    rw [_root_.Formalism.HermitianLatticeCounting.P.Dl_swap]
    exact star_ne_zero.2 (_root_.GlobalTheory.DegCnt.NFGeom.Dl_ne N)
  exact _root_.Formalism.HermitianLatticeCounting.P.Dl_injL _ _ N.j_le hDl' hXa
    fun u hu => _root_.Formalism.HermitianLatticeCounting.P.X_iso _ (Submodule.mem_inf.1 hII).1 (_root_.Formalism.HermitianLatticeCounting.P.Xa_le_X _ _ hu)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem F_X_eq_Xa_sup_II :
    N.F.X = N.F.Xa N.j ⊔
      _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
  refine le_antisymm (fun y hy => ?_) (sup_le (_root_.Formalism.HermitianLatticeCounting.P.Xa_le_X _ _) (by unfold _root_.Formalism.HermitianLatticeCounting.S6.II; exact inf_le_left))
  have hp := _root_.GlobalTheory.DegCnt.NFGeom.proj_mem N y
  have hperp := sub_proj_mem_perp_Ist N y
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hperp
  have hpX : _root_.GlobalTheory.DegCnt.NFGeom.proj N y ∈ N.F.X := by
    have := hp
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at this
    exact (Submodule.mem_inf.1 this).1
  exact Submodule.mem_sup.2 ⟨_, mem_F_Xa_of_mem_F_X_of_B_Ist_eq_zero N (Submodule.sub_mem _ hy hpX)
    hperp, _, hp, sub_add_cancel _ _⟩

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem mem_F'_Xa_of_mem_F'_X_of_B_Ist_eq_zero {y : V}
    (hy : y ∈ N.F'.X)
    (hperp : ∀ u ∈ N.Ist, H.B y u = 0) :
    y ∈ N.F'.Xa N.j := by
  have hc0 : N.c ≠ 0 := left_ne_zero_of_mul_eq_one N.c_norm
  have hX : N.F'.X = Submodule.span K (Set.range
      (fun a : Fin r => N.F'.e a.castSucc)) := by
    unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.X _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa
    congr 1
    ext v
    simp
  rw [hX, Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨c, hc⟩ := hy
  have hpair : ∀ a b : Fin r, N.j ≤ b.val →
      H.B (N.F'.e a.castSucc) (N.ist b) =
        if a = b then N.c else 0 := by
    intro a b hb
    by_cases ha : a.val < N.j
    · rw [N.ist_e' a b ha hb]
      have : a ≠ b := fun h => by subst h; omega
      simp [this]
    · rw [N.same a.castSucc (not_lt.1 ha), map_smul,
        LinearMap.smul_apply, N.ist_e _ _ hb]
      split_ifs <;> simp
  have hcz : ∀ b : Fin r, N.j ≤ b.val → c b = 0 := by
    intro b hb
    have h1 := hperp (N.ist b) (by
      unfold _root_.GlobalTheory.DegCnt.NF.Ist
      exact Submodule.subset_span ⟨b, hb, rfl⟩)
    rw [← hc, _root_.Formalism.HermitianLatticeCounting.P.B_sum_left] at h1
    simp_rw [hpair _ _ hb] at h1
    simpa [hc0] using h1
  rw [← hc]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a.val < N.j
  · exact Submodule.smul_mem _ _ (_root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa _ a ha)
  · rw [hcz a (not_lt.1 ha), zero_smul]
    exact Submodule.zero_mem _

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem F'_X_eq_Xa_sup_II :
    N.F'.X = N.F'.Xa N.j ⊔
      _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
  refine le_antisymm (fun y hy => ?_)
    (sup_le (_root_.Formalism.HermitianLatticeCounting.P.Xa_le_X _ _) (by unfold _root_.Formalism.HermitianLatticeCounting.S6.II; exact inf_le_right))
  have hp := _root_.GlobalTheory.DegCnt.NFGeom.proj_mem N y
  have hperp := sub_proj_mem_perp_Ist N y
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hperp
  have hpX : _root_.GlobalTheory.DegCnt.NFGeom.proj N y ∈ N.F'.X := by
    have := hp
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at this
    exact (Submodule.mem_inf.1 this).2
  exact Submodule.mem_sup.2 ⟨_, mem_F'_Xa_of_mem_F'_X_of_B_Ist_eq_zero N
    (Submodule.sub_mem _ hy hpX) hperp, _, hp, sub_add_cancel _ _⟩

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem mem_F'_Xa_of_mem_II_of_mem_F_Xa {y : V} {a : ℕ}
    (ha : N.j ≤ a)
    (hy : y ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F')
    (hya : y ∈ N.F.Xa a) : y ∈ N.F'.Xa a := by
  rw [← _root_.GlobalTheory.DegCnt.NFGeom.proj_II N hy, _root_.GlobalTheory.DegCnt.NFGeom.proj_apply]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hb' : N.j ≤ b.val := (Finset.mem_filter.1 hb).2
  by_cases hba : b.val < a
  · rw [_root_.GlobalTheory.DegCnt.NFGeom.e_eq N b.castSucc hb', smul_smul]
    exact Submodule.smul_mem _ _ (_root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa _ b hba)
  · have h0 : H.B y (N.ist b) = 0 := by
      refine _root_.Formalism.HermitianLatticeCounting.P.perp_Xa _ (fun b' hb'a => ?_) y hya
      rw [N.ist_e _ _ hb']
      have : b' ≠ b := fun h => by subst h; omega
      simp [this]
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem NFShape_F_F' [FiniteDimensional K V] :
    _root_.Formalism.HermitianLatticeCounting.S6.NFShape N.F N.F' N.j
      N.c := by
  have hc0 : N.c ≠ 0 := left_ne_zero_of_mul_eq_one N.c_norm
  unfold _root_.Formalism.HermitianLatticeCounting.S6.NFShape
  refine ⟨hc0, ?_, ?_, ?_, II_inf_F_Xa_eq_bot N, II_inf_F'_Xa_eq_bot N,
    F_X_eq_Xa_sup_II N, F'_X_eq_Xa_sup_II N, ?_⟩
  · exact _root_.Formalism.HermitianLatticeCounting.P.finrank_compl _ N.j_le _ (F_X_eq_Xa_sup_II N)
      (II_inf_F_Xa_eq_bot N)
  · intro x hx hx0
    have hxX : x ∈ N.F.X := by
      have := hx
      unfold _root_.Formalism.HermitianLatticeCounting.S6.II at this
      exact (Submodule.mem_inf.1 this).1
    obtain ⟨a, al, hl⟩ := _root_.Formalism.HermitianLatticeCounting.P.level_exists _ hxX hx0
    have hja : N.j ≤ a.val := by
      by_contra hlt
      have hmem : x ∈ N.F.Xa N.j :=
        _root_.Formalism.HermitianLatticeCounting.P.Xa_mono _ (by omega) (_root_.Formalism.HermitianLatticeCounting.P.level_mem _ hl)
      have : x ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ⊓
          N.F.Xa N.j := Submodule.mem_inf.2 ⟨hx, hmem⟩
      rw [II_inf_F_Xa_eq_bot N, Submodule.mem_bot] at this
      exact hx0 this
    refine ⟨a, al, N.c⁻¹ * al, hl, ?_, hja, by field_simp⟩
    have hl' := hl
    unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel at hl' ⊢
    refine ⟨mul_ne_zero (inv_ne_zero hc0) hl'.1, ?_⟩
    have heq : x - (N.c⁻¹ * al) • N.F'.e a.castSucc =
        x - al • N.F.e a.castSucc := by
      rw [N.same a.castSucc hja, smul_smul]
      congr 2
      field_simp
    rw [heq]
    refine mem_F'_Xa_of_mem_II_of_mem_F_Xa N hja (Submodule.sub_mem _ hx
      (Submodule.smul_mem _ _ (_root_.GlobalTheory.DegCnt.NFGeom.e_mem_II N a hja))) hl'.2
  · intro a ha
    refine ⟨_, _root_.GlobalTheory.DegCnt.NFGeom.e_mem_II N a ha, 1, N.c⁻¹,
      _root_.Formalism.HermitianLatticeCounting.P.e_level _ a, ?_⟩
    unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
    refine ⟨inv_ne_zero hc0, ?_⟩
    rw [← _root_.GlobalTheory.DegCnt.NFGeom.e_eq N a.castSucc ha, sub_self]
    exact Submodule.zero_mem _
  · have hlast : N.j ≤ (Fin.last r).val := N.j_le
    unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.z
    rw [N.same _ hlast, sub_self]
    exact Submodule.zero_mem _

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.full [FiniteDimensional K V] :
    _root_.Formalism.HermitianLatticeCounting.S6.NFFull N.F N.F' N.j
      N.j_le N.c :=
  _root_.Formalism.HermitianLatticeCounting.P.nf_full _ _ (F_aniso N) (F'_aniso N) _ _ _ (NFShape_F_F' N)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
omit [NumberField K] in
theorem _root_.GlobalTheory.DegCnt.NFGeom.mem_perp' (S : Submodule K V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.perp H S ↔ ∀ x ∈ S, H.B x y = 0 := by
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
  exact ⟨fun h x hx => _root_.Formalism.HermitianLatticeCounting.P.B_swap0 H (h x hx), fun h x hx => _root_.Formalism.HermitianLatticeCounting.P.B_swap0 H (h x hx)⟩

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
omit [NumberField K] in
theorem _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup (S T : Submodule K V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.perp H (S ⊔ T) ↔
      y ∈ _root_.GlobalTheory.HermLat.perp H S ∧ y ∈ _root_.GlobalTheory.HermLat.perp H T := by
  simp only [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp']
  refine ⟨fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx),
    fun x hx => h x (Submodule.mem_sup_right hx)⟩, fun h => ?_⟩
  intro x hx
  exact _root_.Formalism.HermitianLatticeCounting.P.perp_sup H h.1 h.2 x hx

omit [NumberField K] in
theorem perp_perp [FiniteDimensional K V] (S : Submodule K V) : perp H (perp H S) = S := by
  refine le_antisymm (fun w hw => memOfOrthogonalOrthogonal K V H S w fun v hv => ?_) fun s hs => ?_
  · exact (mem_perp_iff H _ _).1 hw v ((mem_perp' S v).2 hv)
  · exact (mem_perp_iff H _ _).2 fun x hx => (mem_perp' S x).1 hx s hs

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.Pi_eq [FiniteDimensional K V] :
    N.Pi =
      _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' ⊔ N.Ist := by
  apply le_antisymm
  · intro w hw
    unfold _root_.GlobalTheory.DegCnt.NF.Pi at hw
    rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hw
    exact _root_.Formalism.HermitianLatticeCounting.P.memOfOrthogonalOrthogonal K V H _ w fun v hv => hw v (by
      unfold _root_.GlobalTheory.DegCnt.NF.Wt
      exact (_root_.GlobalTheory.DegCnt.NFGeom.mem_perp' _ _).2 hv)
  · intro w hw
    unfold _root_.GlobalTheory.DegCnt.NF.Pi
    rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
    intro u hu
    unfold _root_.GlobalTheory.DegCnt.NF.Wt at hu
    exact (_root_.GlobalTheory.DegCnt.NFGeom.mem_perp' _ _).1 hu w hw

theorem II_le_wSp : II N.F N.F' ≤ wSp N.F N.F' := fun _ hx =>
  (mem_perp' _ _).2 (pairing_jointSpan_isotropicMeet _ _ hx)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.sub_proj_perp (y : V) :
    y - _root_.GlobalTheory.DegCnt.NFGeom.proj N y ∈ _root_.GlobalTheory.HermLat.perp H N.Ist :=
  sub_proj_mem_perp_Ist N y

theorem wSp_eq : wSp N.F N.F' = N.Wt ⊔ II N.F N.F' := by
  refine le_antisymm (fun w hw => ?_)
    (sup_le (fun w hw => ((mem_perp_sup _ _ _).1 hw).1) (II_le_wSp N))
  have h : w - proj N w ∈ N.Wt := (mem_perp_sup _ _ _).2
    ⟨Submodule.sub_mem _ hw (II_le_wSp N (proj_mem N w)), sub_proj_perp N w⟩
  simpa using Submodule.add_mem_sup h (proj_mem N w)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.isLift :
    _root_.Formalism.HermitianLatticeCounting.S6.IsLift N.F N.F' N.Wt := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.IsLift
  refine ⟨fun w hw y hy => ?_, ?_, fun w hw => ?_⟩
  · unfold _root_.GlobalTheory.DegCnt.NF.Wt at hw
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp'] at hw
    exact hw.1 y hy
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hW, hII⟩ := Submodule.mem_inf.1 hx
    unfold _root_.GlobalTheory.DegCnt.NF.Wt at hW
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hW
    have h2 := hW.2
    rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at h2
    rw [Submodule.mem_bot, ← _root_.GlobalTheory.DegCnt.NFGeom.proj_II N hII]
    exact _root_.GlobalTheory.DegCnt.NFGeom.proj_zero N h2
  · have hp := _root_.GlobalTheory.DegCnt.NFGeom.proj_mem N w
    refine Submodule.mem_sup.2 ⟨w - _root_.GlobalTheory.DegCnt.NFGeom.proj N w, ?_,
      _root_.GlobalTheory.DegCnt.NFGeom.proj N w, hp, sub_add_cancel _ _⟩
    unfold _root_.GlobalTheory.DegCnt.NF.Wt
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
    refine ⟨(_root_.GlobalTheory.DegCnt.NFGeom.mem_perp' _ _).2 fun y hy => ?_,
      sub_proj_mem_perp_Ist N w⟩
    rw [map_sub, hw y hy, _root_.Formalism.HermitianLatticeCounting.P.pairing_jointSpan_isotropicMeet _ _ hp y hy, sub_zero]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.II_le_uPerp :
    _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ≤
      _root_.GlobalTheory.HermLat.uPerp N.F N.F' := by
  intro x hx
  unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hx
  unfold _root_.GlobalTheory.HermLat.uPerp
  rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp']
  exact _root_.Formalism.HermitianLatticeCounting.P.perp_sup H (fun s hs => _root_.Formalism.HermitianLatticeCounting.P.X_iso _ hs (Submodule.mem_inf.1 hx).1)
    (fun s hs => _root_.Formalism.HermitianLatticeCounting.P.X_iso _ hs (Submodule.mem_inf.1 hx).2)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.uPerp_eq :
    _root_.GlobalTheory.HermLat.uPerp N.F N.F' =
      N.Wn ⊔ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
  apply le_antisymm
  · intro v hv
    unfold _root_.GlobalTheory.HermLat.uPerp at hv
    have hp := _root_.GlobalTheory.DegCnt.NFGeom.proj_mem N v
    have hp' := hp
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hp'
    obtain ⟨hpX, hpX'⟩ := Submodule.mem_inf.1 hp'
    refine Submodule.mem_sup.2 ⟨v - _root_.GlobalTheory.DegCnt.NFGeom.proj N v, ?_,
      _root_.GlobalTheory.DegCnt.NFGeom.proj N v, hp, sub_add_cancel _ _⟩
    unfold _root_.GlobalTheory.DegCnt.NF.Wn
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
    refine ⟨?_, sub_proj_mem_perp_Ist N v⟩
    rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hv ⊢
    intro u hu
    have h0 : H.B u (_root_.GlobalTheory.DegCnt.NFGeom.proj N v) = 0 :=
      _root_.Formalism.HermitianLatticeCounting.P.perp_sup H (fun s hs => _root_.Formalism.HermitianLatticeCounting.P.X_iso _ hs hpX) (fun s hs => _root_.Formalism.HermitianLatticeCounting.P.X_iso _ hs hpX') u hu
    rw [map_sub, LinearMap.sub_apply, hv u hu, _root_.Formalism.HermitianLatticeCounting.P.B_swap0 H h0, sub_zero]
  · refine sup_le (fun v hv => ?_) (_root_.GlobalTheory.DegCnt.NFGeom.II_le_uPerp N)
    unfold _root_.GlobalTheory.DegCnt.NF.Wn at hv
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hv
    unfold _root_.GlobalTheory.HermLat.uPerp
    exact hv.1

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem mem_perp_span_of_forall_B_eq_zero {S : Set V} {y : V} (h : ∀ s ∈ S, H.B y s = 0) :
    y ∈ _root_.GlobalTheory.HermLat.perp H (Submodule.span K S) := by
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
  intro u hu
  have hle : Submodule.span K S ≤ LinearMap.ker (H.B y) :=
    Submodule.span_le.2 fun s hs => LinearMap.mem_ker.2 (h s hs)
  exact LinearMap.mem_ker.1 (hle hu)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.z_mem_Wn :
    N.F.z ∈ N.Wn := by
  have hc0 : N.c ≠ 0 := left_ne_zero_of_mul_eq_one N.c_norm
  unfold _root_.GlobalTheory.DegCnt.NF.Wn
  rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
    exact fun u hu => _root_.Formalism.HermitianLatticeCounting.P.z_X _ hu
  · rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
    intro u hu
    have h1 := _root_.Formalism.HermitianLatticeCounting.P.z_X N.F' hu
    have hz : N.F'.z = N.c • N.F.z :=
      N.same (Fin.last r) N.j_le
    rw [hz, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  · unfold _root_.GlobalTheory.DegCnt.NF.Ist
    refine mem_perp_span_of_forall_B_eq_zero fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    exact N.normalForm_dual_orthogonal_last b hb

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.Wn_eq :
    N.Wn =
      N.Wt ⊔ Submodule.span K {N.F.z} := by
  have hzz : H.B N.F.z N.F.z ≠ 0 := by
    rw [_root_.Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]
    exact neg_ne_zero.2 N.F.hT
  have hz' : N.F'.z = N.c • N.F.z :=
    N.same (Fin.last r) N.j_le
  apply le_antisymm
  · intro v hv
    set t := H.B v N.F.z / H.B N.F.z N.F.z
      with ht
    refine Submodule.mem_sup.2 ⟨v - t • N.F.z, ?_, t • N.F.z,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), sub_add_cancel _ _⟩
    unfold _root_.GlobalTheory.DegCnt.NF.Wn at hv
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hv
    obtain ⟨⟨hX, hX'⟩, hI⟩ := hv
    have hzW := _root_.GlobalTheory.DegCnt.NFGeom.z_mem_Wn N
    unfold _root_.GlobalTheory.DegCnt.NF.Wn at hzW
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hzW
    obtain ⟨⟨zX, zX'⟩, zI⟩ := hzW
    unfold _root_.GlobalTheory.DegCnt.NF.Wt
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
    refine ⟨?_, Submodule.sub_mem _ hI (Submodule.smul_mem _ _ zI)⟩
    unfold _root_.Formalism.HermitianLatticeCounting.S6.V0
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
    refine ⟨⟨Submodule.sub_mem _ hX (Submodule.smul_mem _ _ zX),
      Submodule.sub_mem _ hX' (Submodule.smul_mem _ _ zX')⟩, ?_⟩
    have key : H.B (v - t • N.F.z) N.F.z = 0 := by
      rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ht,
        div_mul_cancel₀ _ hzz, sub_self]
    refine mem_perp_span_of_forall_B_eq_zero fun s hs => ?_
    rcases hs with rfl | hs
    · exact key
    · rw [Set.mem_singleton_iff] at hs
      rw [hs, hz', map_smulₛₗ, key, smul_zero]
  · refine sup_le (fun v hv => ?_)
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 (_root_.GlobalTheory.DegCnt.NFGeom.z_mem_Wn N)))
    unfold _root_.GlobalTheory.DegCnt.NF.Wt at hv
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hv
    obtain ⟨hV, hI⟩ := hv
    unfold _root_.Formalism.HermitianLatticeCounting.S6.V0 at hV
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hV
    unfold _root_.GlobalTheory.DegCnt.NF.Wn
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
    exact ⟨hV.1, hI⟩

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.Wt_pos [FiniteDimensional K V] (σ : K →+* ℂ) {x : V}
    (hx : x ∈ N.Wt) (h0 : x ≠ 0) : 0 < (σ (H.B x x)).re := by
  have hfull := _root_.GlobalTheory.DegCnt.NFGeom.full N
  unfold _root_.Formalism.HermitianLatticeCounting.S6.NFFull at hfull
  unfold _root_.GlobalTheory.DegCnt.NF.Wt at hx
  rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hx
  obtain ⟨hV0, hIst⟩ := hx
  have hV0' := (_root_.GlobalTheory.DegCnt.NFGeom.mem_perp' _ _).1 hV0
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hIst
  refine N.posdef σ x (fun a => ?_) (fun hxX => h0 ?_)
  · rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
    · exact hV0' _ (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left _ _ (_root_.Formalism.HermitianLatticeCounting.P.e_mem_X _ b))
    · exact hV0' _ (_root_.Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_left _ _)
  · have hII := (hfull.2.2.2.2.2.1 x hxX).1 hV0'
    rw [← _root_.GlobalTheory.DegCnt.NFGeom.proj_II N hII]
    exact _root_.GlobalTheory.DegCnt.NFGeom.proj_zero N hIst

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.Wt_inf_Pi [FiniteDimensional K V] {x : V}
    (hx : x ∈ N.Wt) (hx' : x ∈ N.Pi) : x = 0 := by
  by_contra h0
  have hpos := _root_.GlobalTheory.DegCnt.NFGeom.Wt_pos N (Classical.arbitrary (K →+* ℂ)) hx h0
  unfold _root_.GlobalTheory.DegCnt.NF.Pi at hx'
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hx'
  rw [hx' x hx, map_zero, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.isCompl [FiniteDimensional K V] :
    IsCompl N.Wt N.Pi := by
  have hfull := _root_.GlobalTheory.DegCnt.NFGeom.full N
  unfold _root_.Formalism.HermitianLatticeCounting.S6.NFFull at hfull
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
    exact (Submodule.mem_bot K).2 (_root_.GlobalTheory.DegCnt.NFGeom.Wt_inf_Pi N h1 h2)
  · have hDl := _root_.GlobalTheory.DegCnt.NFGeom.Dl_ne N
    have hbII : ∀ b : Fin r, N.j ≤ b.val → ∀ u ∈ N.F'.X,
        H.B (N.F.e b.castSucc) u = 0 := by
      intro b hb u hu
      have hm := _root_.GlobalTheory.DegCnt.NFGeom.e_mem_II N b hb
      unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hm
      exact _root_.Formalism.HermitianLatticeCounting.P.X_iso _ (Submodule.mem_inf.1 hm).2 hu
    have hF8 := hfull.2.2.2.2.2.2.2.1
    have hL3 : ∀ (w : V), (∀ y ∈ _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F',
        (H.B y) w = 0) → w ∈ N.Wt ⊔
          _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
      have hL := _root_.GlobalTheory.DegCnt.NFGeom.isLift N
      unfold _root_.Formalism.HermitianLatticeCounting.S6.IsLift at hL
      exact hL.2.2
    have hPi := _root_.GlobalTheory.DegCnt.NFGeom.Pi_eq N
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hc0 : N.c ≠ 0 := left_ne_zero_of_mul_eq_one N.c_norm
    have hzz : H.B N.F.z N.F.z ≠ 0 := by
      rw [_root_.Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]
      exact neg_ne_zero.2 N.F.hT
    have hz' : N.F'.z = N.c • N.F.z :=
      N.same (Fin.last r) N.j_le
    have hjr : N.j ≤ r + 1 := N.j_le.trans (Nat.le_succ r)
    have hDl' : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F' N.F N.j hjr
        ≠ 0 := by
      rw [_root_.Formalism.HermitianLatticeCounting.P.Dl_swap]
      exact star_ne_zero.2 hDl
    set p2 : V := ∑ a ∈ Finset.univ.filter (fun a : Fin r => N.j ≤ a.val),
      star (H.B (N.F.e a.castSucc) v) • N.ist a with hp2
    set s : K := star (H.B N.F.z v / H.B N.F.z
      N.F.z) with hs
    have hp2I : p2 ∈ N.Ist := by
      unfold _root_.GlobalTheory.DegCnt.NF.Ist
      exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨a, (Finset.mem_filter.1 ha).2, rfl⟩)
    have hi : ∀ b : Fin r, N.j ≤ b.val →
        H.B (N.F.e b.castSucc) (v - p2 - s • N.F.z) = 0 := by
      intro b hb
      rw [map_sub, map_sub, map_smulₛₗ, _root_.Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector _ (_root_.Formalism.HermitianLatticeCounting.P.e_mem_X _ b), smul_zero, sub_zero, hp2, map_sum,
        Finset.sum_eq_single_of_mem b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)]
      · rw [map_smulₛₗ, N.ist_e _ _ hb, if_pos rfl, starRingEnd_apply,
          star_star, smul_eq_mul, mul_one, sub_self]
      · intro a ha hab
        rw [map_smulₛₗ, N.ist_e _ _ (Finset.mem_filter.1 ha).2,
          if_neg (fun h => hab h.symm), smul_zero]
    have hii : H.B N.F.z (v - p2 - s • N.F.z) = 0 := by
      rw [map_sub, map_sub, map_smulₛₗ, hp2, map_sum]
      have h0 : ∀ a ∈ Finset.univ.filter (fun a : Fin r => N.j ≤ a.val),
          H.B N.F.z (star (H.B (N.F.e a.castSucc) v) •
            N.ist a) = 0 := by
        intro a ha
        rw [map_smulₛₗ, N.normalForm_dual_orthogonal_last a (Finset.mem_filter.1 ha).2, smul_zero]
      rw [Finset.sum_eq_zero h0, hs, starRingEnd_apply, star_star, smul_eq_mul,
        div_mul_cancel₀ _ hzz]
      simp
    obtain ⟨p1, hp1, hp1e⟩ := _root_.Formalism.HermitianLatticeCounting.P.Dl_solveL N.F' N.F
      N.j_le hDl'
      (fun b => H.B (v - p2 - s • N.F.z)
        (N.F.e (Fin.castLE hjr b)))
    have hp1X : p1 ∈ N.F'.X := _root_.Formalism.HermitianLatticeCounting.P.Xa_le_X _ _ hp1
    have hw : ∀ a : Fin (r + 1),
        H.B (N.F.e a) (v - p2 - s • N.F.z - p1) = 0 := by
      intro a
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · by_cases hb : b.val < N.j
        · apply _root_.Formalism.HermitianLatticeCounting.P.B_swap0
          have h1 := hp1e ⟨b.val, hb⟩
          have hcast : Fin.castLE hjr (⟨b.val, hb⟩ : Fin N.j) = b.castSucc :=
            Fin.ext rfl
          simp only [hcast] at h1
          rw [LinearMap.map_sub, LinearMap.sub_apply, h1, sub_self]
        · rw [map_sub, hi b (not_lt.1 hb), hbII b (not_lt.1 hb) p1 hp1X, sub_zero]
      · have h2 : H.B N.F.z p1 = 0 := by
          have h3 := _root_.Formalism.HermitianLatticeCounting.P.z_X N.F' hp1X
          rw [hz', map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
          exact (mul_eq_zero.1 h3).resolve_left hc0
        exact (by rw [map_sub, hii, h2, sub_zero] :
          H.B N.F.z (v - p2 - s • N.F.z - p1) = 0)
    obtain ⟨x, hxX, hx⟩ := hF8 _ hw
    have hrest := hL3 _ hx
    have hP : x + p1 + s • N.F.z + p2 ∈ N.Pi := by
      rw [hPi]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ (Submodule.add_mem _
        (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left _ _ hxX) (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right _ _ hp1X)) (Submodule.smul_mem _ _ (_root_.Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_left _ _))))
        (Submodule.mem_sup_right hp2I)
    have hrest' : v - p2 - s • N.F.z - p1 - x ∈
        N.Wt ⊔ N.Pi := by
      have hle : _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ≤
          N.Pi := by
        intro y hy
        rw [hPi]
        unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hy
        exact Submodule.mem_sup_left (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left _ _ (Submodule.mem_inf.1 hy).1)
      exact sup_le_sup_left hle _ hrest
    have hv : v = (v - p2 - s • N.F.z - p1 - x) +
        (x + p1 + s • N.F.z + p2) := by abel
    rw [hv]
    exact Submodule.add_mem _ hrest' (Submodule.mem_sup_right hP)

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
theorem _root_.GlobalTheory.DegCnt.NFGeom.finrank_Wt [FiniteDimensional K V] :
    Module.finrank K N.Wt + 2 * r + 1 = Module.finrank K V := by
  have hfull := _root_.GlobalTheory.DegCnt.NFGeom.full N
  unfold _root_.Formalism.HermitianLatticeCounting.S6.NFFull at hfull
  have hCompl := _root_.GlobalTheory.DegCnt.NFGeom.isCompl N
  have hV0 := hfull.2.2.2.2.1
  have hPi := _root_.GlobalTheory.DegCnt.NFGeom.Pi_eq N
  have hpair : ∀ (g : {b : Fin r // N.j ≤ b.val} → K)
      (i : {b : Fin r // N.j ≤ b.val}),
      H.B (N.F.e i.1.castSucc) (∑ a, g a • N.ist a.1) =
        star (g i) := by
    intro g i
    rw [map_sum, Finset.sum_eq_single i]
    · rw [map_smulₛₗ, N.ist_e _ _ i.2, if_pos rfl, smul_eq_mul, mul_one,
        starRingEnd_apply]
    · intro a _ hai
      rw [map_smulₛₗ, N.ist_e _ _ a.2,
        if_neg (fun h => hai (Subtype.ext h).symm), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hIst : N.Ist = Submodule.span K (Set.range
      (fun a : {b : Fin r // N.j ≤ b.val} => N.ist a.1)) := by
    unfold _root_.GlobalTheory.DegCnt.NF.Ist
    congr 1
    ext v
    simp
  have hli : LinearIndependent K
      (fun a : {b : Fin r // N.j ≤ b.val} => N.ist a.1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := hpair g i
    rw [hg, map_zero] at this
    exact star_eq_zero.1 this.symm
  have hfI : Module.finrank K N.Ist = r - N.j := by
    rw [hIst, finrank_span_eq_card hli, Fintype.card_subtype]
    have : (Finset.univ.filter (fun b : Fin r => N.j ≤ b.val)) =
        (Finset.Ico N.j r).attachFin (fun n hn => (Finset.mem_Ico.1 hn).2) := by
      ext b
      simp [Finset.mem_attachFin, b.2]
    rw [this, Finset.card_attachFin, Nat.card_Ico]
  have hdisj : _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' ⊓ N.Ist = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyV, hyI⟩ := Submodule.mem_inf.1 hy
    rw [hIst, Submodule.mem_span_range_iff_exists_fun] at hyI
    obtain ⟨g, rfl⟩ := hyI
    have hg : ∀ i, g i = 0 := by
      intro i
      have h1 := hpair g i
      rw [_root_.Formalism.HermitianLatticeCounting.P.B_swap0 H (_root_.Formalism.HermitianLatticeCounting.P.pairing_jointSpan_isotropicMeet _ _ (_root_.GlobalTheory.DegCnt.NFGeom.e_mem_II N i.1 i.2) _ hyV)] at h1
      exact star_eq_zero.1 h1.symm
    simp [hg]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (_root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F') N.Ist
  rw [hdisj, finrank_bot, add_zero, hV0, hfI, ← hPi] at hsum
  have hc := Submodule.finrank_add_eq_of_isCompl hCompl
  have hj := N.j_le
  omega

end GlobalTheory.DegCnt.NFGeom

namespace GlobalTheory.DegCnt

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in

theorem _root_.GlobalTheory.DegCnt.NF.geometry : ∀ (K V : Type) [Field K]
    [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (r : ℕ) (N : _root_.GlobalTheory.DegCnt.NF H r),
      _root_.Formalism.HermitianLatticeCounting.S6.NFFull N.F N.F' N.j
          N.j_le N.c ∧
        _root_.Formalism.HermitianLatticeCounting.S6.IsLift N.F N.F' N.Wt ∧
        IsCompl N.Wt N.Pi ∧
        Module.finrank K N.Wt + 2 * r + 1 = Module.finrank K V ∧
        N.Wn =
          N.Wt ⊔ Submodule.span K {N.F.z} ∧
        _root_.GlobalTheory.HermLat.uPerp N.F N.F' =
          N.Wn ⊔ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ∧
        _root_.GlobalTheory.HermLat.wSp N.F N.F' =
          N.Wt ⊔ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ∧
        _root_.GlobalTheory.HermLat.wSp N.F' N.F =
          _root_.GlobalTheory.HermLat.wSp N.F N.F' ∧
        _root_.GlobalTheory.Mass.PD
          (_root_.GlobalTheory.Mass.hRes H.B.flip N.Wt) ∧
        1 ≤ N.T ∧
        N.nD N.j ≠ 0 ∧
        N.Pi =
          _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' ⊔ N.Ist := by
  intro K V _ _ _ _ _ _ _ _ H _ r N
  have hfull := _root_.GlobalTheory.DegCnt.NFGeom.full N
  have hWt : _root_.GlobalTheory.HermLat.wSp N.F N.F' =
      N.Wt ⊔ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
    apply le_antisymm
    · intro w hw
      unfold _root_.GlobalTheory.HermLat.wSp at hw
      rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp'] at hw
      have hL := _root_.GlobalTheory.DegCnt.NFGeom.isLift N
      unfold _root_.Formalism.HermitianLatticeCounting.S6.IsLift at hL
      exact hL.2.2 w hw
    · refine sup_le (fun w hw => ?_) (fun x hx => ?_)
      · unfold _root_.GlobalTheory.DegCnt.NF.Wt at hw
        rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hw
        unfold _root_.GlobalTheory.HermLat.wSp
        exact hw.1
      · unfold _root_.GlobalTheory.HermLat.wSp
        rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp']
        exact _root_.Formalism.HermitianLatticeCounting.P.pairing_jointSpan_isotropicMeet _ _ hx
  refine ⟨hfull, _root_.GlobalTheory.DegCnt.NFGeom.isLift N,
    _root_.GlobalTheory.DegCnt.NFGeom.isCompl N, _root_.GlobalTheory.DegCnt.NFGeom.finrank_Wt N,
    _root_.GlobalTheory.DegCnt.NFGeom.Wn_eq N,
    _root_.GlobalTheory.DegCnt.NFGeom.uPerp_eq N, hWt, ?_, ?_, ?_, ?_,
    _root_.GlobalTheory.DegCnt.NFGeom.Pi_eq N⟩
  · unfold _root_.GlobalTheory.HermLat.wSp
    rw [_root_.Formalism.HermitianLatticeCounting.P.jointSpan_comm]
  · unfold _root_.GlobalTheory.Mass.PD
    intro τ x hx
    have hx' : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
    exact _root_.GlobalTheory.DegCnt.NFGeom.Wt_pos N τ x.2 hx'
  · by_contra h
    push_neg at h
    have hT0 : N.T = 0 := by omega
    apply N.F.hT
    rw [N.hT, hT0, Nat.cast_zero]
  · unfold _root_.GlobalTheory.DegCnt.NF.nD
    rw [dif_pos (N.j_le.trans (Nat.le_succ r))]
    have hI : (Ideal.absNorm N.𝔡 : ℝ) ≠ 0 := by
      exact_mod_cast mt Ideal.absNorm_eq_zero_iff.1 N.𝔡_ne
    refine mul_ne_zero ?_ ?_
    · rw [abs_ne_zero]
      exact_mod_cast Algebra.norm_ne_zero_iff.2 (_root_.GlobalTheory.DegCnt.NFGeom.Dl_ne N)
    · first
        | exact zpow_ne_zero _ hI
        | exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hI)) _).ne'

end GlobalTheory.DegCnt
