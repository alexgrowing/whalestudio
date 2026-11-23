import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCountStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstIntegralCoordsLatticeSectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsPolyGrowthOfBoundedCoisotropicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalyticStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalyticStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatLinearIndependentCoordsOfRealIndependentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedCombinationOfSpanCoordinateRowsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem dvd_of_exp_eq_one (k : ℤ) (N : ℕ) (hN : 0 < N)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (k : ℂ) / N) = 1) : (N : ℤ) ∣ k := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_eq_iff hN'] at hm
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : (2 * Real.pi * Complex.I) * ((k : ℂ) + m * N) = 0 := by linear_combination -hm
  have h4 : ((k + m * N : ℤ) : ℂ) = 0 := by push_cast; exact (mul_eq_zero.1 h3).resolve_left hpi
  have h5 : k + m * N = 0 := by exact_mod_cast h4
  exact ⟨-m, by linarith⟩

theorem eq_of_exp_eq (m m' : ℤ) (h : ∀ N : ℕ, 0 < N → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / N) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (m' : ℂ) / N)) : m = m' := by
  have hN : 0 < (m - m').natAbs + 1 := Nat.succ_pos _
  have h1 := h _ hN
  have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (((m - m' : ℤ)) : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ)) = 1 := by
    have e : -(2 * Real.pi * Complex.I) * (((m - m' : ℤ)) : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) =
        -(2 * Real.pi * Complex.I) * (m : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) -
          -(2 * Real.pi * Complex.I) * (m' : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 := dvd_of_exp_eq_one _ _ hN h2
  have h4 : m - m' = 0 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [Int.abs_eq_natAbs]; push_cast; omega)
  omega

theorem hermForm_im_sum (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (x y : Fin r → ℤ) :
    (hermForm Hm (∑ j, x j • lam j) (∑ j, y j • lam j)).im =
      ∑ i, ∑ j, (x i : ℝ) * (y j : ℝ) * (hermForm Hm (lam i) (lam j)).im := by
  have hs : ∀ (k : ℤ) (v : Fin g → ℂ), k • v = (k : ℂ) • v := fun k v => (Int.cast_smul_eq_zsmul ℂ k v).symm
  simp only [hermForm, hs, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, star_intCast, Finset.mul_sum, Complex.im_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem logDom_facts (n a : ℕ) : IsOpen (logDom n a) ∧ Convex ℝ (logDom n a) ∧
    (∀ s, AnalyticAt ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧
    Set.MapsTo (logExp a) (logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) :=
  GlobalTheory.T.punctPolydiscUniversalCover_open_convex_exp_analytic n a

theorem logExp_ne_zero (n a : ℕ) (s : Fin n → ℂ) (k : Fin n) (hk : (k : ℕ) < a) : logExp a s k ≠ 0 := by
  simp [logExp, hk, Complex.exp_ne_zero]

theorem isLatFam_comp (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) : IsLatFam B K → IsOpen B' →
    AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B → IsLatFam B' (fun b => K (φ b)) :=
  GlobalTheory.T.isLatFam_comp_of_analyticOnNhd m n g B B' K φ

theorem det_ne_zero_of_herm (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ)
    (M : Matrix (Fin r) (Fin r) ℤ) : (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ lam →
    Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 :=
  GlobalTheory.T.det_ne_zero_of_imHermForm_integral_real_basis g r Hm lam M

theorem linIndep_rows (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) :
    LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) :=
  GlobalTheory.T.rat_linearIndependent_coords_of_real_independent g r r₀ lam u A

theorem bounded_span (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ)
    (A : Fin r₀ → Fin r → ℤ) (C : ℝ) : (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) →
    ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' :=
  GlobalTheory.T.bounded_combination_of_span_coordinate_rows X g r r₀ T lam u A C

theorem mem_of_isLatBasis {g r : ℕ} {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (h : IsLatBasis K b) (i : Fin r) :
    b i ∈ K :=
  (h.2 (b i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩

theorem span_top_of_isLatBasis {g r : ℕ} {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (h : IsLatBasis K b)
    (hK : Submodule.span ℝ K = ⊤) : Submodule.span ℝ (Set.range b) = ⊤ := by
  rw [eq_top_iff, ← hK, Submodule.span_le]
  intro w hw
  obtain ⟨m, rfl⟩ := (h.2 w).1 hw
  exact Submodule.sum_mem _ fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := b) j)) _

end GlobalTheory.ShFam.Hor.LogCh.Core

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem core : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ (∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r₀ K ζ Pair hK hζan hζli hζK hζ0 hζbd hstd huniq hprop hinner hS
  obtain ⟨hDo, hDc, hEa, hEm⟩ := logDom_facts n a
  have hDp : IsPreconnected (logDom n a) := hDc.isPreconnected
  have hEd : Differentiable ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) := fun s => (hEa s).differentiableAt
  have hK' : IsLatFam (logDom n a) (fun s => K (logExp a s)) :=
    isLatFam_comp n n g _ _ K (logExp a) hK hDo (fun s _ => hEa s) hEm
  have hin := fun s (hs : s ∈ logDom n a) => hinner _ (hEm hs) (fun k hk => logExp_ne_zero n a s k hk)
  obtain ⟨lam, hlamD, hlamB⟩ := GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex n g (2 * g) (logDom n a) (fun s => K (logExp a s)) hDo hDc
    (fun s hs => GlobalTheory.T.exists_analytic_local_lattice_basis n g (logDom n a) (fun s => K (logExp a s)) s hK' hs (hin s hs).choose_spec.2.2.1)
  have hmem : ∀ s ∈ logDom n a, ∀ i, lam s i ∈ K (logExp a s) := fun s hs i => mem_of_isLatBasis (hlamB s hs) i
  have hlamDi : ∀ i, DifferentiableOn ℂ (fun s => lam s i) (logDom n a) := fun i => differentiableOn_pi.1 hlamD i
  let s₀ : Fin n → ℂ := fun _ => (-1 / 2 : ℂ)
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    split_ifs <;> norm_num [s₀]
  obtain ⟨Hm₀, -, hpos₀, hspan₀, hint₀, hpair₀⟩ := hin s₀ hs₀
  have hMex : ∀ i j, ∃ m : ℤ, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = m := fun i j =>
    hint₀ _ (hmem s₀ hs₀ i) _ (hmem s₀ hs₀ j)
  obtain ⟨M, hM₀⟩ : ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ, ∀ i j, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = M i j :=
    ⟨fun i j => (hMex i j).choose, fun i j => (hMex i j).choose_spec⟩

  have hM : ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) →
      (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) →
        Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
          (Complex.exp_ne_zero _))) →
      ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j := by
    intro s hs Hm hint hpair i j
    obtain ⟨m', hm'⟩ := hint _ (hmem s hs i) _ (hmem s hs j)
    have key : m' = M i j := by
      apply eq_of_exp_eq
      intro N hN
      have h1 := hpair₀ N _ _ hN (hmem s₀ hs₀ i) (hmem s₀ hs₀ j)
      have h2 := hprop n N (logDom n a) (logExp a) (fun s => lam s i) (fun s => lam s j) _ s₀ s hN hDo hDp
        hEd.differentiableOn hEm (hlamDi i) (hlamDi j) (fun b hb => ⟨hmem b hb i, hmem b hb j⟩) hs₀ hs h1
      have h3 := hpair N _ _ hN (hmem s hs i) (hmem s hs j)
      have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
      simp only [Units.val_mk0, hm', hM₀, Complex.ofReal_intCast] at h4
      exact h4
    rw [hm', key]

  have hstdK : ∀ j : Fin g, ∀ s ∈ logDom n a, (Pi.single j 1 : Fin g → ℂ) ∈ K (logExp a s) := by
    intro j s hs
    obtain ⟨i, hi⟩ := hstd j
    rw [← hi _ (hEm hs)]
    exact hζK _ (hEm hs) i
  have hρex : ∀ j : Fin g, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a,
      (Pi.single j 1 : Fin g → ℂ) = ∑ k, m k • lam s k := fun j =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun _ => Pi.single j 1) s₀ hDp
      hlamD.continuousOn continuousOn_const hlamB (fun s hs => hstdK j s hs) hs₀
  choose mρ hmρ using hρex

  have hζc : ContinuousOn ζ (Metric.ball 0 1) := hζan.continuousOn
  have hζEc : ∀ i, ContinuousOn (fun s => ζ (logExp a s) i) (logDom n a) := fun i =>
    (continuousOn_pi.1 (hζc.comp hEd.continuous.continuousOn hEm)) i
  have hAex : ∀ i, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a, ζ (logExp a s) i = ∑ k, m k • lam s k := fun i =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun s => ζ (logExp a s) i) s₀ hDp
      hlamD.continuousOn (hζEc i) hlamB (fun s hs => hζK _ (hEm hs) i) hs₀
  choose A hA using hAex

  have hz₁ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := hEm hs₀
  have hsumK : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ z j ∈ K z := by
    intro z hz c
    obtain ⟨H, hH⟩ := hK.2.1 z hz
    have hj : ∀ j, ζ z j ∈ H := fun j => by rw [← SetLike.mem_coe, hH]; exact hζK z hz j
    rw [← hH]
    exact H.sum_mem fun j _ => H.zsmul_mem (hj j) _
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζan.differentiableOn
  have hsumD : ∀ c : Fin r₀ → ℤ, DifferentiableOn ℂ (fun z => ∑ j, c j • ζ z j) (Metric.ball 0 1) := by
    intro c
    have h : ∀ j ∈ (Finset.univ : Finset (Fin r₀)), DifferentiableOn ℂ (fun z => c j • ζ z j) (Metric.ball 0 1) :=
      fun j _ => (differentiableOn_pi.1 hζd j).const_smul (c j)
    refine (DifferentiableOn.sum h).congr fun z _ => ?_
    simp [Finset.sum_apply]
  have hsum_eq : ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ (logExp a s₀) j = ∑ k, (∑ i, c i • A i) k • lam s₀ k := by
    intro c
    simp only [fun i => hA i s₀ hs₀, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hform : ∀ x y : Fin (2 * g) → ℤ, (hermForm Hm₀ (∑ k, x k • lam s₀ k) (∑ k, y k • lam s₀ k)).im =
      ((x ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ y : ℤ) : ℝ) := by
    intro x y
    rw [hermForm_im_sum]
    simp only [hM₀, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ c c' : Fin r₀ → ℤ, (fun j => (c j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, c i • A i) ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ (∑ i, c' i • A i) := by
    intro N hN
    obtain ⟨S, hcard, hSp⟩ := hS N hN
    refine ⟨S, hcard, fun c c' hc => ?_⟩
    have h1 := hSp c c' hc
    have h2 := hprop n N (Metric.ball 0 1) id (fun z => ∑ j, c j • ζ z j) (fun z => ∑ j, c' j • ζ z j) 1 0
      (logExp a s₀) hN Metric.isOpen_ball (convex_ball 0 1).isPreconnected differentiableOn_id (Set.mapsTo_id _)
      (hsumD c) (hsumD c') (fun b hb => ⟨hsumK b hb c, hsumK b hb c'⟩) (Metric.mem_ball_self one_pos) hz₁ h1
    have h3 := hpair₀ N _ _ hN (hsumK _ hz₁ c) (hsumK _ hz₁ c')
    have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
    simp only [Units.val_mk0, Units.val_one, id, hsum_eq, hform, Complex.ofReal_intCast] at h4
    exact dvd_of_exp_eq_one _ N hN h4
  have hdet : (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ).det ≠ 0 :=
    det_ne_zero_of_herm g (2 * g) Hm₀ (lam s₀) M hpos₀ (hlamB s₀ hs₀).1
      (span_top_of_isLatBasis (hlamB s₀ hs₀) hspan₀) hM₀
  have hlinQ := linIndep_rows g (2 * g) r₀ (lam s₀) (ζ (logExp a s₀)) A (hζli _ hz₁) (fun i => hA i s₀ hs₀)
  have hco := GlobalTheory.T.coisotropic_sublattice_of_torsion_count (2 * g) r₀ M A hdet hlinQ hdvd

  obtain ⟨C, hC⟩ := hζbd
  have hgr := GlobalTheory.T.periods_polyGrowth_of_bounded_coisotropic n a g (2 * g) lam ((M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ).map (Int.cast : ℤ → ℝ))
    (Submodule.span ℝ (Set.range fun i j => (A i j : ℝ))) hlamD
    (fun s hs => by
      obtain ⟨Hm, hH, hpos, hspan, hint, hpair⟩ := hin s hs
      exact ⟨(hlamB s hs).1, span_top_of_isLatBasis (hlamB s hs) hspan, Hm, hH, hpos, fun i j => by
        rw [hM s hs Hm hint hpair i j]; simp⟩)
    (fun v hv => hco v fun i => hv _ (Submodule.subset_span (Set.mem_range_self (f := fun i j => (A i j : ℝ)) i)))
    (fun w hw => by
      obtain ⟨C', hC'⟩ := bounded_span (Fin n → ℂ) g (2 * g) r₀ (logDom n a) lam (fun s => ζ (logExp a s)) A C
        (fun s hs i => hA i s hs) (fun s hs => hC _ (hEm hs)) w hw
      exact ⟨C', fun s hs _ => hC' s hs⟩)
  refine ⟨2 * g, lam, fun j k => (mρ j k : ℂ), hlamD.continuousOn,
    fun s hs => ⟨(hlamB s hs).1.restrict_scalars' ℤ, (hlamB s hs).2, fun j => ?_⟩, hgr⟩
  rw [hmρ j s hs]
  exact Finset.sum_congr rfl fun k _ => Int.cast_smul_eq_zsmul ℂ _ _

end GlobalTheory.ShFam.Hor.LogCh.Core
