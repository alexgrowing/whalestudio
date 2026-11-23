import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Filter Topology

noncomputable section

namespace GlobalTheory.CuspCoef

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

theorem blk_two_stdSum {N r t : ℕ} (h : r + t = N) (i : Fin N) :
    blk (two (stdSum h)) i = decide (r ≤ (i : ℕ)) := by
  by_cases hi : (i : ℕ) < r
  · have e : i = two (stdSum h) ⟨false, (⟨i, hi⟩ : Fin r)⟩ := Fin.ext (by simp)
    conv_lhs => rw [e]
    rw [blk_apply]
    simp only [Bool.false_eq, decide_eq_false_iff_not, not_le]
    exact hi
  · have e : i = two (stdSum h) ⟨true, (⟨i - r, by omega⟩ : Fin t)⟩ := Fin.ext (by simp; omega)
    conv_lhs => rw [e]
    rw [blk_apply]
    simp only [Bool.true_eq, decide_eq_true_eq]
    omega

theorem contraction {N r t : ℕ} (h : r + t = N) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    (u : GL (Fin N) k) (hu : u ∈ unipRad k (two (stdSum h))) (U : Set (GL (Fin N) k))
    (hU : U ∈ 𝓝 (1 : GL (Fin N) k)) :
    ∃ M : ℕ, ∀ ν : Fin N → ℤ, (∀ i j : Fin N, (i : ℕ) < r → r ≤ (j : ℕ) → (M : ℤ) ≤ ν i - ν j) →
      GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * u * (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν)⁻¹ ∈ U := by
  obtain ⟨γ, hγ, hsub⟩ := GlobalTheory.CentralExponent.exists_cong_subset (n := Fin N) hU
  have hγ0 : (0 : ValueGroupWithZero k) < γ := zero_lt_iff.2 γ.ne_zero
  have key : ∀ x : k, ∀ᶠ m : ℕ in atTop, valuation k ((ϖ : k) ^ m * x) < γ := by
    intro x
    by_cases hx : x = 0
    · exact Filter.Eventually.of_forall fun m => by simpa [hx] using hγ0
    · have hvx : valuation k x ≠ 0 := by simpa using hx
      obtain ⟨n, hn⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) (γ * (Units.mk0 _ hvx)⁻¹)
      filter_upwards [eventually_ge_atTop n] with m hm
      rw [map_mul, map_pow, hϖ]
      have h1 : uniformizer k ^ m ≤ uniformizer k ^ n :=
        pow_le_pow_right_of_le_one' uniformizer_lt_one.le hm
      have h2 : uniformizer k ^ m < γ * (valuation k x)⁻¹ := by simpa using h1.trans_lt hn
      exact (lt_mul_inv_iff₀ (zero_lt_iff.2 hvx)).1 h2
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i j : Fin N,
      valuation k ((ϖ : k) ^ m * (u : Matrix (Fin N) (Fin N) k) i j) < γ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => key _
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hall
  refine ⟨M, fun ν hν => hsub _ fun i j => ?_⟩
  have hinv : ((GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν)⁻¹ : GL (Fin N) k) =
      GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (-ν) := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, GlobalTheory.GLDoubling.val_torusElt, GlobalTheory.GLDoubling.val_torusElt,
      Matrix.diagonal_mul_diagonal, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ (Units.ne_zero ϖ)]
    simp
  rw [hinv, Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt, GlobalTheory.GLDoubling.val_torusElt,
    Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hb := CuspMax.mem_unipRad_iff_entries.1 hu i j
  simp only [blk_two_stdSum] at hb
  by_cases hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · have hne : i ≠ j := by
      rintro rfl
      omega
    have hd := hν i j hij.1 hij.2
    obtain ⟨d, hdd⟩ : ∃ d : ℕ, ν i + (-ν) j = d := ⟨(ν i - ν j).toNat, by simp only [Pi.neg_apply]; omega⟩
    have e : (ϖ : k) ^ ν i * (u : Matrix (Fin N) (Fin N) k) i j * (ϖ : k) ^ ((-ν) j) =
        (ϖ : k) ^ d * (u : Matrix (Fin N) (Fin N) k) i j := by
      rw [mul_right_comm, ← zpow_add₀ (Units.ne_zero ϖ), hdd, zpow_natCast]
    rw [Matrix.one_apply_ne hne, sub_zero, e]
    exact hM d (by simp only [Pi.neg_apply] at hdd; omega) i j
  · have hu1 : (u : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
      refine hb fun hlt => hij ?_
      have key : ∀ x y : Bool, x < y → x = false ∧ y = true := by decide
      obtain ⟨h1, h2⟩ := key _ _ hlt
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, not_le] at h1 h2
      exact ⟨h1, h2⟩
    rw [hu1]
    by_cases hij' : i = j
    · subst hij'
      rw [Matrix.one_apply_eq, mul_one, Pi.neg_apply, zpow_neg,
        mul_inv_cancel₀ (zpow_ne_zero _ (Units.ne_zero ϖ)), sub_self, map_zero]
      exact hγ0
    · rw [Matrix.one_apply_ne hij']
      simpa using hγ0

theorem fix_mem_nhds {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (l : Module.Dual ℂ V) (hl : IsOpen {g | π.dual g l = l}) :
    {g : GL (Fin N) k | ∀ y, l (π g y) = l y} ∈ 𝓝 (1 : GL (Fin N) k) := by
  have ho : IsOpen ((fun g : GL (Fin N) k => g⁻¹) ⁻¹' {g | π.dual g l = l}) :=
    hl.preimage continuous_inv
  refine Filter.mem_of_superset (ho.mem_nhds (by
    simp only [Set.mem_preimage, inv_one, Set.mem_setOf_eq, map_one, Module.End.one_apply])) fun g hg y => ?_
  have := LinearMap.congr_fun (show π.dual g⁻¹ l = l from hg) y
  simpa [Representation.dual_apply, Module.Dual.transpose_apply] using this

theorem vanishing {N r t : ℕ} (h : r + t = N) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hJ : twKer π (unipRad k (two (stdSum h))) 1 = ⊤) (l : Module.Dual ℂ V)
    (hl : IsOpen {g | π.dual g l = l}) (w : V) :
    ∃ M : ℕ, ∀ ν : Fin N → ℤ, (∀ i j : Fin N, (i : ℕ) < r → r ≤ (j : ℕ) → (M : ℤ) ≤ ν i - ν j) →
      l (π (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν) w) = 0 := by
  have hw : w ∈ twKer π (unipRad k (two (stdSum h))) 1 := hJ ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, y, rfl⟩ := hx
    obtain ⟨M, hM⟩ := contraction h hϖ u.1 u.2 _ (fix_mem_nhds π l hl)
    refine ⟨M, fun ν hν => ?_⟩
    have hfix := hM ν hν
    set T := GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν
    have e : π T (π u y) = π (T * u * T⁻¹) (π T y) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, e]
    rw [hfix (π T y), sub_self]
  | zero => exact ⟨0, fun _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M1, h1⟩ := hx
    obtain ⟨M2, h2⟩ := hy
    refine ⟨max M1 M2, fun ν hν => ?_⟩
    rw [map_add, map_add, h1 ν fun i j hi hj => le_trans (by simp) (hν i j hi hj),
      h2 ν fun i j hi hj => le_trans (by simp) (hν i j hi hj), add_zero]
  | smul c x _ hx =>
    obtain ⟨M, hM⟩ := hx
    exact ⟨M, fun ν hν => by rw [map_smul, map_smul, hM ν hν, smul_zero]⟩

theorem eventually_vanish {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hJ : ∀ (r t : ℕ) (h : r + t = N), 0 < r → 0 < t →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h)))))
    (x : V) (m : Module.Dual ℂ V) (hm : IsOpen {g | π.dual g m = m}) (r : ℕ) (hr0 : 0 < r) (hrN : r < N) :
    ∀ᶠ M : ℕ in atTop, ∀ ν : Fin N → ℤ, Antitone ν → (M : ℤ) ≤ ν ⟨r - 1, by omega⟩ - ν ⟨r, hrN⟩ →
      m (π (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν) x) = 0 := by
  have h : r + (N - r) = N := by omega
  obtain ⟨M0, hM0⟩ := vanishing h hϖ π
    (Submodule.Quotient.subsingleton_iff.1 (hJ r (N - r) h hr0 (by omega))) m hm x
  filter_upwards [eventually_ge_atTop M0] with M hM ν hν hgap
  refine hM0 ν fun i j hi hj => ?_
  have h1 : ν ⟨r - 1, by omega⟩ ≤ ν i := hν (Fin.mk_le_mk.2 (by omega))
  have h2 : ν j ≤ ν ⟨r, hrN⟩ := hν (Fin.mk_le_mk.2 (by omega))
  have h3 : (M0 : ℤ) ≤ M := by exact_mod_cast hM
  omega

theorem gap_sum {N : ℕ} (M : ℕ) (ν : Fin N → ℤ)
    (hg : ∀ (r : ℕ) (h0 : 0 < r) (h1 : r < N), ν ⟨r - 1, by omega⟩ - ν ⟨r, h1⟩ < M) :
    ∀ (d i : ℕ) (hi : i + d < N), ν ⟨i, by omega⟩ - ν ⟨i + d, hi⟩ ≤ d * M := by
  intro d
  induction d with
  | zero => intro i hi; simp
  | succ d ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := hg (i + d + 1) (by omega) (by omega)
    have e1 : (⟨i + d + 1 - 1, by omega⟩ : Fin N) = ⟨i + d, by omega⟩ := Fin.ext (by simp)
    have e2 : (⟨i + (d + 1), hi⟩ : Fin N) = ⟨i + d + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1] at h2
    rw [e2]
    push_cast
    linarith

theorem torusElt_const_mem_center {N : ℕ} (ϖ : kˣ) (c : ℤ) :
    GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (fun _ => c) ∈ Subgroup.center (GL (Fin N) k) := by
  refine Subgroup.mem_center_iff.2 fun g => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem torusElt_eq_mul {N : ℕ} (ϖ : kˣ) (ν : Fin N → ℤ) (c : ℤ) :
    GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν = GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (fun _ => c) *
      GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (fun i => ν i - c) := by
  refine Units.ext ?_
  rw [Units.val_mul, GlobalTheory.GLDoubling.val_torusElt, GlobalTheory.GLDoubling.val_torusElt,
    GlobalTheory.GLDoubling.val_torusElt, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← zpow_add₀ (Units.ne_zero ϖ)]
  congr 1
  ring

end Lemmas

open GlobalTheory.GLDoubling in

theorem isSupercuspidal_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π → GlobalTheory.PRep.IsSupercuspidal π := by
  intro k _ _ _ _ N V _ _ π hπ
  obtain ⟨hsm, hJ⟩ := (CuspMax.isCuspidal_iff_maximal k N V π).1 hπ
  refine ⟨hsm, fun v l hl => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := exists_unif k
  have hKc : IsCompact (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have hOv : ((fun g => π g v) '' (KO k (Fin N) : Set (GL (Fin N) k))).Finite :=
    GlobalTheory.SmoothRiesz.finite_orbit π hsm _ hKc v
  have hOl : ((fun g => π.dual g l) '' (KO k (Fin N) : Set (GL (Fin N) k))).Finite := by
    refine ((GlobalTheory.SmoothRiesz.finite_orbit (smoothRep π.dual) (isSmooth_smoothRep _) _ hKc
      ⟨l, hl⟩).image Subtype.val).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  have hS := hOv.prod (hOl.prod (Set.finite_Ioo 0 N))
  have hall : ∀ᶠ M : ℕ in atTop, ∀ p ∈ ((fun g => π g v) '' (KO k (Fin N) : Set (GL (Fin N) k))) ×ˢ
      (((fun g => π.dual g l) '' (KO k (Fin N) : Set (GL (Fin N) k))) ×ˢ Set.Ioo 0 N),
      ∀ ν : Fin N → ℤ, Antitone ν → ∀ (h0 : 0 < p.2.2) (h1 : p.2.2 < N),
        (M : ℤ) ≤ ν ⟨p.2.2 - 1, by omega⟩ - ν ⟨p.2.2, h1⟩ → p.2.1 (π (torusElt k (Fin N) ϖ ν) p.1) = 0 := by
    refine (Filter.eventually_all_finite hS).2 fun p hp => ?_
    have hm : IsOpen {g | π.dual g p.2.1 = p.2.1} := by
      obtain ⟨g, -, hg⟩ := hp.2.1
      rw [← hg]
      exact smoothPart_stable π.dual g l hl
    filter_upwards [eventually_vanish hϖ π hJ p.1 p.2.1 hm p.2.2 hp.2.2.1 hp.2.2.2] with M hM ν hν h0 h1 hgp
    exact hM ν hν hgp
  obtain ⟨M, hM⟩ := hall.exists
  let F : Finset (Fin N → ℤ) := Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) (N * M)
  let C : Set (GL (Fin N) k) := ⋃ μ ∈ F,
    (fun p : GL (Fin N) k × GL (Fin N) k => p.1 * torusElt k (Fin N) ϖ μ * p.2) ''
      ((KO k (Fin N) : Set (GL (Fin N) k)) ×ˢ (KO k (Fin N) : Set (GL (Fin N) k)))
  refine ⟨C, F.isCompact_biUnion fun μ _ => (hKc.prod hKc).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨ν, hν, κ, hκ, κ', hκ', rfl⟩ := GlobalTheory.SortedCartan.cartan_antitone k N ϖ hϖ g

  have hgap : ∀ (r : ℕ) (h0 : 0 < r) (h1 : r < N), ν ⟨r - 1, by omega⟩ - ν ⟨r, h1⟩ < M := by
    intro r h0 h1
    by_contra hc
    refine hg ?_
    have := hM (π κ' v, π.dual κ⁻¹ l, r) ⟨⟨κ', hκ', rfl⟩, ⟨κ⁻¹, inv_mem hκ, rfl⟩, h0, h1⟩ ν hν h0 h1 (not_lt.1 hc)
    simpa [Representation.dual_apply, Module.Dual.transpose_apply, ← Module.End.mul_apply,
      ← map_mul, mul_assoc] using this
  by_cases hN : N = 0
  · subst hN
    refine ⟨1, one_mem _, κ * torusElt k (Fin 0) ϖ ν * κ', ?_, by simp⟩
    exact Set.mem_biUnion (x := ν) (Fintype.mem_piFinset.2 fun i => i.elim0) ⟨(κ, κ'), ⟨hκ, hκ'⟩, rfl⟩
  · let c : ℤ := ν ⟨N - 1, by omega⟩
    have hμ : (fun i => ν i - c) ∈ F := by
      refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨?_, ?_⟩
      · have := hν (show i ≤ (⟨N - 1, by omega⟩ : Fin N) from Fin.le_iff_val_le_val.2 (by simp; omega))
        simp only [c]
        omega
      · have h := gap_sum M ν hgap (N - 1 - i) i (by omega)
        have e : (⟨(i : ℕ) + (N - 1 - i), by omega⟩ : Fin N) = ⟨N - 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [e] at h
        have h2 : ((N - 1 - (i : ℕ) : ℕ) : ℤ) * M ≤ (N : ℤ) * M :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        simp only [c]
        exact le_trans (by simpa using h) h2
    refine ⟨torusElt k (Fin N) ϖ (fun _ => c), torusElt_const_mem_center ϖ c,
      κ * torusElt k (Fin N) ϖ (fun i => ν i - c) * κ',
      Set.mem_biUnion hμ ⟨(κ, κ'), ⟨hκ, hκ'⟩, rfl⟩, ?_⟩
    rw [torusElt_eq_mul ϖ ν c]
    have hz := Subgroup.mem_center_iff.1 (torusElt_const_mem_center (k := k) (N := N) ϖ c) κ
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hz]

end GlobalTheory.CuspCoef
