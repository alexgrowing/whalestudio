import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y : Scheme.{0}}

def IsGenerated (L : LB X) : Prop :=
  ∃ (n : ℕ) (s : Fin n → L.Sec), ⨆ i, nonzeroLocus (s i) = ⊤

structure IsAmpleLB (L : LB X) : Prop where

  isLB : L.IsLB

  compactSpace : CompactSpace X

  exists_affine : ∀ x : X, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, x ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)

variable {L M : LB X}

section Generated

theorem isGenerated_of_finite {ι : Type*} [Finite ι] (s : ι → L.Sec) (h : ⨆ i, nonzeroLocus (s i) = ⊤) :
    IsGenerated L := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact ⟨n, fun i => s (e.symm i), (e.symm.iSup_comp (g := fun i => nonzeroLocus (s i))).trans h⟩

theorem IsGenerated.exists_mem (h : IsGenerated L) (x : X) : ∃ s : L.Sec, x ∈ nonzeroLocus s := by
  obtain ⟨n, s, hs⟩ := h
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
  exact ⟨s i, hi⟩

theorem exists_finset_iSup_eq_top [CompactSpace X] (U : X → X.Opens) (hU : ∀ x, x ∈ U x) :
    ∃ T : Finset X, ⨆ x : T, U x = ⊤ := by
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set X)) (fun y => (U y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hU y⟩)
  refine ⟨T, top_le_iff.1 fun y _ => ?_⟩
  obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
  exact Opens.mem_iSup.2 ⟨⟨a, ha⟩, h⟩

theorem isGenerated_iff_forall [CompactSpace X] : IsGenerated L ↔ ∀ x : X, ∃ s : L.Sec, x ∈ nonzeroLocus s := by
  refine ⟨fun h => h.exists_mem, fun h => ?_⟩
  choose s hs using h
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun x => nonzeroLocus (s x)) hs
  exact isGenerated_of_finite (fun x : T => s x) hT

theorem IsGenerated.exists_fin_succ (h : IsGenerated L) :
    ∃ (N : ℕ) (s : Fin (N + 1) → L.Sec), ⨆ i, nonzeroLocus (s i) = ⊤ := by
  obtain ⟨n, s, hs⟩ := h
  exact ⟨n, Fin.cons DVR.SecOps.secZero s, top_le_iff.1 (hs.ge.trans (iSup_le fun i =>
    le_iSup_of_le i.succ le_rfl))⟩

theorem IsGenerated.isLB (h : IsGenerated L) : L.IsLB := by
  have coc : ∀ (y : X) i j k, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k →
      gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 X) y (L.U j ⊓ L.U k) (L.g j k) =
        gm (𝟙 X) y (L.U i ⊓ L.U k) (L.g i k) := fun y i j k hi hj hk => by
    obtain ⟨s, hs⟩ := h.exists_mem y
    have u := (mem_nonzeroLocus_iff_isUnit s hk).1 hs
    refine Units.ext (u.mul_right_cancel ?_)
    rw [Units.val_mul, mul_assoc, ← gs_compat s (𝟙 X) y hj hk, ← gs_compat s (𝟙 X) y hi hj,
      ← gs_compat s (𝟙 X) y hi hk]
  refine ⟨top_le_iff.1 fun y _ => ?_, fun i => unit_ext fun y hy => ?_, fun i j k => unit_ext fun y hy => ?_⟩
  · obtain ⟨s, hs⟩ := h.exists_mem y
    exact Opens.mem_iSup.2 (exists_chart_of_mem_nonzeroLocus hs)
  · rw [gm_res (𝟙 X) y _ hy, map_one]
    exact mul_eq_left.1 (coc y i i i hy hy hy)
  · rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    exact coc y i j k hy.1.1 hy.1.2 hy.2

theorem isGenerated_of_gen (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) : IsGenerated L :=
  ⟨1, fun _ => DVR.genSec t ht, by simp only [nonzeroLocus_genSec hL, iSup_const]⟩

theorem isGenerated_triv (X : Scheme.{0}) : IsGenerated (LB.triv X) :=
  isGenerated_of_gen (LB.isLB_triv X) ⟨fun _ => 1⟩ fun _ _ => by simp only [map_one, mul_one]

theorem IsGenerated.pull (h : IsGenerated L) (f : Y ⟶ X) : IsGenerated (L.pull f) := by
  obtain ⟨n, s, hs⟩ := h
  refine ⟨n, fun i => secPull (s i) f, top_le_iff.1 fun y _ => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ (f y)))
  exact Opens.mem_iSup.2 ⟨i, (nonzeroLocus_secPull (s i) f).ge hi⟩

theorem IsGenerated.of_lbIso (h : IsGenerated M) (hL : L.IsLB) (H : LBIso L M) : IsGenerated L := by
  have hM := h.isLB
  obtain ⟨n, s, hs⟩ := h
  choose t ht using fun i => exists_sec_nonzeroLocus_eq_of_lbIso hL hM H (s i)
  exact ⟨n, t, by simp only [ht, hs]⟩

theorem IsGenerated.pow (h : IsGenerated L) (k : ℕ) : IsGenerated (lbPow L k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, fun _ => secOfFn L 1, by
      simp only [nonzeroLocus_secOfFn h.isLB, Scheme.basicOpen_one, iSup_const]⟩
  · obtain ⟨n, s, hs⟩ := h
    exact ⟨n, fun i => secToPow (s i) k, by simp only [nonzeroLocus_secToPow _ hk, hs]⟩

theorem IsGenerated.pow_add {m n : ℕ} (hm : IsGenerated (lbPow L m)) (hn : IsGenerated (lbPow L n)) :
    IsGenerated (lbPow L (m + n)) := by
  obtain ⟨a, s, hs⟩ := hm
  obtain ⟨b, t, ht⟩ := hn
  refine isGenerated_of_finite (fun p : Fin a × Fin b => secMul (s p.1) (t p.2)) (top_le_iff.1 fun y _ => ?_)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
  exact Opens.mem_iSup.2 ⟨(i, j), (nonzeroLocus_secMul (s i) (t j)).ge ⟨hi, hj⟩⟩

theorem isGenerated_of_isQuasiAffine [X.IsQuasiAffine] (hL : L.IsLB) : IsGenerated L := by
  refine isGenerated_iff_forall.2 fun x => ?_
  obtain ⟨k, hk⟩ := exists_chart hL x
  obtain ⟨_, ⟨r, -, rfl⟩, hx, hle⟩ := Opens.isBasis_iff_nbhd.1 (Scheme.IsQuasiAffine.isBasis_basicOpen X) hk
  obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_basicOpen hL r k hle
  exact ⟨u, hu.ge hx⟩

end Generated

section Ample

theorem exists_common_pow {ι : Type*} [Finite ι] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (s : ∀ i, (lbPow L (n i)).Sec) :
    ∃ N, 1 ≤ N ∧ ∃ t : ι → (lbPow L N).Sec, ∀ i, nonzeroLocus (t i) = nonzeroLocus (s i) := by
  classical
  have := Fintype.ofFinite ι
  have hpos : 0 < ∏ i, n i := Finset.prod_pos fun i _ => hn i
  choose k hk using fun i => Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  refine ⟨∏ i, n i, hpos, fun i => secCast (hk i).symm (secPow (s i) (k i)), fun i => ?_⟩
  rw [nonzeroLocus_secCast, nonzeroLocus_secPow]
  exact Nat.pos_of_mul_pos_left ((hk i) ▸ hpos)

theorem IsAmpleLB.exists_cover (h : IsAmpleLB L) :
    ∃ n, 1 ≤ n ∧ ∃ (N : ℕ) (s : Fin (N + 1) → (lbPow L n).Sec),
      (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  have := h.compactSpace
  choose n hn s hx ha using h.exists_affine
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun x => nonzeroLocus (s x)) hx
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow (fun x : T => n x) (fun x => hn x) (fun x => s x)
  obtain ⟨c, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨N, hN, c, Fin.cons DVR.SecOps.secZero fun i => t (e.symm i), top_le_iff.1 (hT.ge.trans (iSup_le fun x =>
    le_iSup_of_le (e x).succ ?_)), fun i => ?_⟩
  · rw [Fin.cons_succ, e.symm_apply_apply, ht]
  · refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero, nonzeroLocus_secZero]
      exact isAffineOpen_bot X
    · rw [Fin.cons_succ, ht]
      exact ha _

theorem IsAmpleLB.exists_cover_mul (h : IsAmpleLB L) :
    ∃ n, 1 ≤ n ∧ ∀ k, 1 ≤ k → ∃ (N : ℕ) (s : Fin (N + 1) → (lbPow L (n * k)).Sec),
      (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  obtain ⟨n, hn, N, s, hs, ha⟩ := h.exists_cover
  refine ⟨n, hn, fun k hk => ⟨N, fun i => secPow (s i) k, ?_, fun i => ?_⟩⟩
  · simp only [nonzeroLocus_secPow _ hk, hs]
  · rw [nonzeroLocus_secPow _ hk]
    exact ha i

theorem isAmpleLB_of_cover (hL : L.IsLB) {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Finite ι] (s : ι → (lbPow L n).Sec)
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) : IsAmpleLB L where
  isLB := hL
  compactSpace := ⟨by
    have e : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) := by
      rw [← Opens.coe_iSup, hs, Opens.coe_top]
    rw [e]
    exact isCompact_iUnion fun i => (ha i).isCompact⟩
  exists_affine x := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
    exact ⟨n, hn, s i, hi, ha i⟩

theorem isAmpleLB_iff_cover : IsAmpleLB L ↔ L.IsLB ∧ ∃ n, 1 ≤ n ∧ ∃ (N : ℕ) (s : Fin (N + 1) → (lbPow L n).Sec),
    (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) :=
  ⟨fun h => ⟨h.isLB, h.exists_cover⟩, fun ⟨hL, _, hn, _, s, hs, ha⟩ => isAmpleLB_of_cover hL hn s hs ha⟩

theorem IsAmpleLB.exists_isGenerated_pow (h : IsAmpleLB L) : ∃ n, 1 ≤ n ∧ IsGenerated (lbPow L n) := by
  obtain ⟨n, hn, N, s, hs, -⟩ := h.exists_cover
  exact ⟨n, hn, N + 1, s, hs⟩

theorem IsAmpleLB.quasiSeparatedSpace (h : IsAmpleLB L) : QuasiSeparatedSpace X := by
  obtain ⟨n, -, N, s, hs, ha⟩ := h.exists_cover
  refine quasiSeparatedSpace_iff_forall_affineOpens.2 fun U V => ?_
  have hL := isLB_lbPow h.isLB n
  have e : ((U : X.Opens) ∩ (V : X.Opens) : Set X) =
      ⋃ i, ((nonzeroLocus (s i) ⊓ U : X.Opens) : Set X) ∩ ((nonzeroLocus (s i) ⊓ V : X.Opens) : Set X) := by
    refine Set.Subset.antisymm (fun y hy => ?_) (Set.iUnion_subset fun i y hy => ⟨hy.1.2, hy.2.2⟩)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨i, ⟨hi, hy.1⟩, ⟨hi, hy.2⟩⟩
  rw [e]
  exact isCompact_iUnion fun i => (ha i).isQuasiSeparated _ _ (fun _ hy => hy.1) (nonzeroLocus (s i) ⊓ U).isOpen
    (isAffineOpen_nonzeroLocus_inf hL (s i) U.2).isCompact (fun _ hy => hy.1) (nonzeroLocus (s i) ⊓ V).isOpen
    (isAffineOpen_nonzeroLocus_inf hL (s i) V.2).isCompact

theorem IsAmpleLB.exists_affine_le (h : IsAmpleLB L) {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, x ∈ nonzeroLocus s ∧ nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s) := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  obtain ⟨n, hn, s, hs, ha⟩ := h.exists_affine x
  obtain ⟨f, hf, hxf⟩ := ha.exists_basicOpen_le (V := U) ⟨x, hx⟩ hs
  obtain ⟨k, hk, u, hu⟩ := exists_nonzeroLocus_eq_basicOpen h.isLB s f
  exact ⟨n * k, Nat.mul_pos hn hk, u, hu.ge hxf, hu.le.trans hf, hu ▸ ha.basicOpen f⟩

theorem isAmpleLB_of_forall_le [CompactSpace X] (hL : L.IsLB)
    (h : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, x ∈ nonzeroLocus s ∧ nonzeroLocus s ≤ U) :
    IsAmpleLB L := by
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  obtain ⟨n, hn, s, hs, hle⟩ := h x W hx
  have ha := isAffineOpen_nonzeroLocus_inf (isLB_lbPow hL n) s hW
  rw [inf_eq_left.2 hle] at ha
  exact ⟨n, hn, s, hs, ha⟩

theorem IsAmpleLB.of_lbIso (h : IsAmpleLB M) (hL : L.IsLB) (H : LBIso L M) : IsAmpleLB L := by
  refine ⟨hL, h.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := h.exists_affine x
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow hL n) (isLB_lbPow h.isLB n) (lbIso_lbPow H n) s
  exact ⟨n, hn, t, ht.ge hs, ht ▸ ha⟩

theorem isAmpleLB_pow_iff (hL : L.IsLB) {k : ℕ} (hk : 1 ≤ k) : IsAmpleLB (lbPow L k) ↔ IsAmpleLB L := by
  refine ⟨fun h => ⟨hL, h.compactSpace, fun x => ?_⟩, fun h => ⟨isLB_lbPow hL k, h.compactSpace, fun x => ?_⟩⟩
  · obtain ⟨n, hn, s, hs, ha⟩ := h.exists_affine x
    have e := nonzeroLocus_secOfPowPow s
    exact ⟨k * n, Nat.mul_pos hk hn, secOfPowPow s, e.ge hs, e ▸ ha⟩
  · obtain ⟨n, hn, s, hs, ha⟩ := h.exists_affine x
    have e : nonzeroLocus (secToPowPow (secCast (Nat.mul_comm n k) (secPow s k))) = nonzeroLocus s := by
      rw [nonzeroLocus_secToPowPow, nonzeroLocus_secCast, nonzeroLocus_secPow s hk]
    exact ⟨n, hn, _, e.ge hs, e ▸ ha⟩

theorem IsAmpleLB.pull_of_isAffineHom (h : IsAmpleLB L) (f : Y ⟶ X) [IsAffineHom f] : IsAmpleLB (L.pull f) := by
  have := h.compactSpace
  refine ⟨LB.isLB_pull h.isLB f, QuasiCompact.compactSpace_of_compactSpace f, fun y => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := h.exists_affine (f y)
  have e := nonzeroLocus_secPowPull s f
  exact ⟨n, hn, secPowPull s f, e.ge hs, e ▸ ha.preimage f⟩

theorem IsAmpleLB.pull_of_isOpenImmersion (h : IsAmpleLB L) (f : Y ⟶ X) [IsOpenImmersion f] [CompactSpace Y] :
    IsAmpleLB (L.pull f) := by
  refine ⟨LB.isLB_pull h.isLB f, inferInstance, fun y => ?_⟩
  obtain ⟨n, hn, s, hs, hle, ha⟩ := h.exists_affine_le (x := f y) (U := f.opensRange) ⟨y, rfl⟩
  have e := nonzeroLocus_secPowPull s f
  exact ⟨n, hn, secPowPull s f, e.ge hs, e ▸ ha.preimage_of_isOpenImmersion f hle⟩

theorem isAmpleLB_of_relAmple {S : Scheme.{0}} (A : Over S) {L : LB A.left} (hL : L.IsLB) (h : RelAmple A L)
    (U : S.Opens) (hU : IsAffineOpen U) : IsAmpleLB (L.pull (A.hom ⁻¹ᵁ U).ι) := by
  obtain ⟨N, hN, K, s, hs, ha⟩ := h U hU
  have e : ∀ i, nonzeroLocus (secOfFinPow (s i)) = nonzeroLocus (s i) := fun i => nonzeroLocus_secOfFinPow hN (s i)
  exact isAmpleLB_of_cover (LB.isLB_pull hL _) hN (fun i => secOfFinPow (s i)) ((iSup_congr e).trans hs)
    fun i => (e i).symm ▸ (ha i).1

theorem lbIso_pull_id (hL : L.IsLB) : LBIso (L.pull (𝟙 X)) L := lbIso_of_chartPull (chartPullPull L (𝟙 X)) hL

theorem isAmpleLB_of_relAmple_of_isAffine {S : Scheme.{0}} [IsAffine S] (A : Over S) {L : LB A.left} (hL : L.IsLB)
    (h : RelAmple A L) : IsAmpleLB L := by
  have h₁ := isAmpleLB_of_relAmple A hL h ⊤ (isAffineOpen_top S)
  have : IsIso (A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso A.left.topIso.hom)
  let j := inv (A.hom ⁻¹ᵁ ⊤).ι
  let a : ChartPull L (L.pull (A.hom ⁻¹ᵁ ⊤).ι) j := chartPullSec L _ j (IsIso.inv_hom_id _)
  have h₂ := h₁.pull_of_isAffineHom j
  exact h₂.of_lbIso hL (LBIso.chartPull a (chartPullPull _ j) (lbIso_refl h₁.isLB))

theorem polAV_isAmpleLB {S : Scheme.{0}} (P : PolAV S) (U : S.Opens) (hU : IsAffineOpen U) :
    IsAmpleLB (P.L.pull (P.A.hom ⁻¹ᵁ U).ι) :=
  isAmpleLB_of_relAmple P.A P.isLB P.ample U hU

end Ample

section Inhabitants

theorem isAmpleLB_of_isQuasiAffine [X.IsQuasiAffine] (hL : L.IsLB) : IsAmpleLB L := by
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hL x
  obtain ⟨_, ⟨r, hr, rfl⟩, hx, hle⟩ := Opens.isBasis_iff_nbhd.1 (Scheme.IsQuasiAffine.isBasis_basicOpen X) hk
  obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_basicOpen hL r k hle
  have e : nonzeroLocus (secToPow u 1) = X.basicOpen r := (nonzeroLocus_secToPow u le_rfl).trans hu
  exact ⟨1, le_rfl, secToPow u 1, e.ge hx, e ▸ hr⟩

theorem isAmpleLB_of_isAffine [IsAffine X] (hL : L.IsLB) : IsAmpleLB L := isAmpleLB_of_isQuasiAffine hL

theorem isAmpleLB_triv_iff : IsAmpleLB (LB.triv X) ↔ X.IsQuasiAffine := by
  refine ⟨fun h => ?_, fun _ => isAmpleLB_of_isQuasiAffine (LB.isLB_triv X)⟩
  have := h.compactSpace
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x => ?_
  obtain ⟨n, -, s, hs, ha⟩ := h.exists_affine x
  have e : nonzeroLocus s = X.basicOpen (U := ⊤) (powSecFn s PUnit.unit) :=
    (inf_top_eq _).symm.trans (nonzeroLocus_inf_powSecFn s PUnit.unit)
  exact ⟨powSecFn s PUnit.unit, e ▸ ha, e.le hs⟩

theorem isGenerated_O1 (R : Type) [CommRing R] (N : ℕ) : IsGenerated (ProjSpace.O1 R N) :=
  ⟨N + 1, ProjSpace.coord R N, ProjSpace.iSup_nonzeroLocus_coord R N⟩

theorem isAmple_projective_O_one (R : Type) [CommRing R] (N : ℕ) : IsAmpleLB (ProjSpace.O1 R N) :=
  isAmpleLB_of_cover (ProjSpace.O1_isLB R N) le_rfl (fun k => secToPow (ProjSpace.coord R N k) 1)
    (by simp only [nonzeroLocus_secToPow _ le_rfl, ProjSpace.iSup_nonzeroLocus_coord])
    fun k => by
      rw [nonzeroLocus_secToPow _ le_rfl, ProjSpace.nonzeroLocus_coord]
      exact ProjSpace.isAffineOpen_chart R N k

example [Nonempty X] (L : LB X) [IsEmpty L.ι] : ¬ IsGenerated L ∧ ¬ IsAmpleLB L := by
  have h : ¬ L.IsLB := fun h => by
    obtain ⟨i, -⟩ := exists_chart h (Classical.arbitrary X)
    exact isEmptyElim i
  exact ⟨fun h' => h h'.isLB, fun h' => h h'.isLB⟩

example : IsAmpleLB (LB.triv (Sp ℤ)) ∧ IsGenerated (LB.triv (Sp ℤ)) :=
  ⟨isAmpleLB_of_isAffine (LB.isLB_triv _), isGenerated_triv _⟩

example (h : ¬ X.IsSeparated) : IsGenerated (LB.triv X) ∧ ¬ IsAmpleLB (LB.triv X) :=
  ⟨isGenerated_triv X, fun h' => h (have := isAmpleLB_triv_iff.1 h'; inferInstance)⟩

example : IsAmpleLB (lbPow (ProjSpace.O1 ℚ 2) 3) :=
  (isAmpleLB_pow_iff (ProjSpace.O1_isLB ℚ 2) (by norm_num)).2 (isAmple_projective_O_one ℚ 2)

end Inhabitants

end GlobalTheory
