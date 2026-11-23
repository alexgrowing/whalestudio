import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def HermLine.inv (B : HermLine ι) : HermLine ι where
  a := -B.a
  h z := (B.h z)⁻¹
  pos z hz := inv_pos.mpr (B.pos z hz)
  smul c z hc := by
    rw [B.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, zpow_neg]

theorem logNorm_inv_one (B : HermLine ι) (z : (Σ k, ι k) → ℂ) :
    logNorm B.inv 1 z = Real.log (B.h z) := by
  simp [logNorm, HermLine.inv]

theorem isSmoothHerm_inv {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm B.inv := (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} from hB).inv
  fun z hz => (B.pos z hz).ne'

theorem isSectionOn_inv_one {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι}
    (hB : B.a = 0) : IsSectionOn P B.inv 1 := by
  classical
  refine ⟨0, fun k => ?_, ?_, ?_⟩
  · simp [HermLine.inv, hB]
  · intro m hm k
    have hm0 : m = 0 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])
    subst hm0
    simp
  · intro h
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h)

theorem h_eq_of_sameOrbit {B : HermLine ι} (hB : B.a = 0) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : B.h z = B.h z' := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [B.smul c z' hc, hB]
  simp

theorem maDens_congr {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) : ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ i, ReciprocityTheory.AnForm.hessC (φ i) z = ReciprocityTheory.AnForm.hessC (ψ i) z := by
    intro i
    have h2 : fderiv ℝ (fderiv ℝ (φ i)) z = fderiv ℝ (fderiv ℝ (ψ i)) z :=
      ((h i).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  simp only [ReciprocityTheory.AnForm.maDens, hH]

theorem mInt_congr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Φ' : Fin e → LocPot X} {g g' : X → ℝ}
    (hΦ : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Φ' j y)
    (hg : ∀ x, g x = g' x) : mInt A Φ g = mInt A Φ' g' := by
  unfold ReciprocityTheory.AnForm.M.mInt
  by_cases h : Nonempty (ChartPartition A)
  · rw [dif_pos h, dif_pos h]
    unfold ReciprocityTheory.AnForm.M.integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [hg, hΦ j y hy]
  · rw [dif_neg h, dif_neg h]

theorem locDens_cons_congr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X)
    {Q Q' : LocPot X} (Φ : Fin e → LocPot X)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y'))
      =ᶠ[𝓝 y] fun y' => Q'.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    ∀ j, ∀ y ∈ (A.chart j).target,
      locDens A (Fin.cons Q Φ) j y = locDens A (Fin.cons Q' Φ) j y := by
  intro j y hy
  unfold ReciprocityTheory.AnForm.M.locDens
  apply maDens_congr
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero]
    exact h j y hy
  | succ i =>
    simp only [Fin.cons_succ]
    exact Filter.EventuallyEq.rfl

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem contDiffOn_lift (R : AnLogRes P J e) (x : R.X) (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hopen : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  rw [contDiffOn_pi]
  intro p
  exact ((R.holo x p j).contDiffOn hopen.uniqueDiffOn).restrict_scalars ℝ

theorem contDiffOn_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X)
    (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => Real.log (L.h (R.lift x ((R.A.chart j).symm y))))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hl := contDiffOn_lift R x j
  have hmaps : Set.MapsTo (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    fun y hy => (R.mem x _ hy.2).1
  have hL' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hL
  exact (hL'.comp hl hmaps).log fun y hy => (L.pos _ (hmaps hy)).ne'

theorem smoothOn_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X) :
    R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := fun j => contDiffOn_potOf R hL x j

theorem smooth_diag (R : AnLogRes P J e) {B : HermLine ι} (hB : IsSmoothHerm B) (hB0 : B.a = 0) :
    R.A.Smooth (fun x => Real.log (B.h (R.lift x x))) := by
  intro j
  apply contDiffOn_of_locally_contDiffOn
  intro y hy
  have hyt : y ∈ (R.A.chart j).target := hy.1
  refine ⟨(R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U ((R.A.chart j).symm y),
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U _), ⟨hyt, R.mem_U _⟩, ?_⟩
  have hc := contDiffOn_potOf R hB ((R.A.chart j).symm y) j
  refine (hc.mono Set.inter_subset_right).congr fun y' hy' => ?_
  change Real.log (B.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y'))) =
    Real.log (B.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y')))
  rw [h_eq_of_sameOrbit hB0 (R.compat _ _ _ ⟨R.mem_U _, hy'.2.2⟩)]

theorem potOf_germ (R : AnLogRes P J e) {B : HermLine ι} (hB0 : B.a = 0) (j : Fin R.A.n)
    (y : Fin e → ℂ) (hy : y ∈ (R.A.chart j).target) :
    (fun y' => (potOf R B).φ ((R.A.chart j).symm y) ((R.A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => (LocPot.ofFun fun x => Real.log (B.h (R.lift x x))).φ ((R.A.chart j).symm y)
        ((R.A.chart j).symm y') := by
  have hev : ∀ᶠ y' in 𝓝 y, (R.A.chart j).symm y' ∈ R.U ((R.A.chart j).symm y) :=
    ((R.A.chart j).continuousAt_symm hy).preimage_mem_nhds
      ((R.isOpen_U _).mem_nhds (R.mem_U _))
  filter_upwards [hev] with y' hy'
  change Real.log (B.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))) =
    Real.log (B.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y')))
  rw [h_eq_of_sameOrbit hB0 (R.compat _ _ _ ⟨hy', R.mem_U _⟩)]

def PotOfPotentialStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnLogRes P J e) (L : HermLine ι), IsSmoothHerm L → IsPotential R.A (potOf R L)

end ReciprocityTheory.ChartRestriction.G.Geo
