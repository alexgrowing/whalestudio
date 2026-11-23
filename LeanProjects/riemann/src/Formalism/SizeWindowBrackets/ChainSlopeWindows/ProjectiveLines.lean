import Formalism.SizeWindowBrackets.JointDPublishedSizes
import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.ProjectiveLineModels

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates

theorem b_ramified_grouped_holds : BRamGrouped := by
  constructor
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      s u U HH δ Dstar sg η0 η1 e0 de bb x c
    rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23⟩
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      s u U HH δ Dstar sg η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      s u U HH δ Dstar sg η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      s u U HH δ Dstar sg η0 η1 e0 de bb x c
      ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23⟩

theorem b_power_grouped_holds : BPowGrouped := by
  constructor
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      s u U HH δ Dstar η0 η1 e0 de bb x c
    rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      s u U HH δ Dstar η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      s u U HH δ Dstar η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      s u U HH δ Dstar η0 η1 e0 de bb x c
      ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩

theorem c_grouped_form_holds : CGrouped := by
  constructor
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      muMaxM muM dr BE Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c
    rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29⟩
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      muMaxM muM dr BE Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      muMaxM muM dr BE Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      muMaxM muM dr BE Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c
      ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29⟩

theorem d_grouped_form_holds : DGrouped := by
  constructor
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      σ τ M N0 β dr Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c
    rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      σ τ M N0 β dr Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      σ τ M N0 β dr Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      σ τ M N0 β dr Sg0 A A' Vh HH δ Dstar sg η0 η1 e0 de bb x c
      ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩

theorem power_hyp_to_ramified : HypPowToRam := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
    s u U HH δ Dstar η0 η1 e0 de bb x c
  rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hinv : x ^ (-c) = (x ^ c)⁻¹ := Real.rpow_neg hx0.le c
  refine ⟨a0, a1, a2, a3, a4, a5, Real.rpow_pos_of_pos hx0 _, a6, ?_, a8, a9, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, ?_, a19, a20, a21⟩
  · rw [hinv, div_inv_eq_mul]; exact a7
  · rw [hinv, div_inv_eq_mul, mul_comm]; exact a19

theorem flatness_iff_holds : FlatIff := by
  constructor
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
      a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a17, a18, a19, a20⟩ ⟨a12, a13, a14, a15, a16⟩
      a21 a22 a23 a24 a25 a26
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a17, a18, a19, a20⟩ ⟨a12, a13, a14, a15, a16⟩
      a21 a22 a23 a24 a25 a26
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
      a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26

theorem standard_lattice_fg (K n : Type) [Field K] [NumberField K] [Fintype n] : (stdLat K n).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem standard_lattice_span_eq_top (K n : Type) [Field K] [NumberField K] [Fintype n] :
    Submodule.span K ((stdLat K n : Submodule (𝓞 K) (n → K)) : Set (n → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K n).span_eq]
  exact Submodule.span_mono Submodule.subset_span

section Lines

variable (p : ℕ) [Fact p.Prime]

theorem line_point_injective (i : Option (ZMod p) × ZMod p) : Function.Injective (linePt p i) := by
  rcases i with ⟨_ | m, b⟩ <;> intro t s h <;> simp [linePt] at h
  · exact h
  · exact h.1

theorem distinct_lines_meet_at_most_once (i j : Option (ZMod p) × ZMod p) (hij : i ≠ j) (t t' s s' : ZMod p)
    (h1 : linePt p i t = linePt p j t') (h2 : linePt p i s = linePt p j s') : t = s ∧ t' = s' := by
  rcases i with ⟨_ | m, b⟩ <;> rcases j with ⟨_ | m', b'⟩ <;> simp [linePt] at h1 h2 hij ⊢
  · exact absurd h1.1 hij
  · obtain ⟨a1, a2⟩ := h1
    obtain ⟨c1, c2⟩ := h2
    subst a1
    subst c1
    exact ⟨by rw [a2, c2], rfl⟩
  · obtain ⟨a1, a2⟩ := h1
    obtain ⟨c1, c2⟩ := h2
    subst a1
    subst c1
    exact ⟨rfl, by rw [← a2, ← c2]⟩
  · obtain ⟨a1, a2⟩ := h1
    obtain ⟨c1, c2⟩ := h2
    subst a1
    subst c1
    by_cases hm : m = m'
    · subst hm
      exact absurd (add_left_cancel a2) (hij rfl)
    · have h3 : (m - m') * (t - s) = 0 := by linear_combination a2 - c2
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (sub_eq_zero.1 h4) hm
      · exact ⟨sub_eq_zero.1 h4, sub_eq_zero.1 h4⟩

theorem line_matrix_gram (i j : Option (ZMod p) × ZMod p) :
    (lineMat p i)ᴴ * lineMat p j
      = Matrix.of fun t t' => if linePt p i t = linePt p j t' then (1 : ℂ) else 0 := by
  ext t t'
  simp [lineMat, Matrix.mul_apply, eq_comm]

theorem distinct_lines_gram_hs_le_one (i j : Option (ZMod p) × ZMod p) (hij : i ≠ j) :
    hsSq ((lineMat p i)ᴴ * lineMat p j) ≤ 1 := by
  have h : hsSq ((lineMat p i)ᴴ * lineMat p j)
      = (((Finset.univ : Finset (ZMod p × ZMod p)).filter
          (fun x => linePt p i x.1 = linePt p j x.2)).card : ℝ) := by
    rw [line_matrix_gram, Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
    simp [hsSq, apply_ite]
  rw [h]
  have : ((Finset.univ : Finset (ZMod p × ZMod p)).filter
      (fun x => linePt p i x.1 = linePt p j x.2)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha c hc
    rw [Finset.mem_filter] at ha hc
    obtain ⟨e1, e2⟩ := distinct_lines_meet_at_most_once p i j hij a.1 a.2 c.1 c.2 ha.2 hc.2
    exact Prod.ext e1 e2
  exact_mod_cast this

theorem line_matrix_gram_self (i : Option (ZMod p) × ZMod p) : (lineMat p i)ᴴ * lineMat p i = 1 := by
  rw [line_matrix_gram]
  ext t t'
  simp [Matrix.one_apply, (line_point_injective p i).eq_iff]

theorem line_model_input_sizes :
    InputSG (I := Option (ZMod p) × ZMod p) (ι := fun _ => ZMod p) (lineMat p) (fun _ => 1)
      ((p : ℝ) ^ 2) 0 0 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_⟩
  · have := distinct_lines_gram_hs_le_one p i j hij
    simp only [KpG, mul_one, Real.sqrt_one, Complex.ofReal_one, one_smul, ZMod.card]
    have e : (1 + 0) * (p : ℝ) * (p : ℝ) / (p : ℝ) ^ 2 = 1 := by
      rw [add_zero, one_mul, sq]
      exact div_self (by positivity)
    rw [e]
    exact this
  · simp [KdG, KpG, line_matrix_gram_self, hsSq]
  · simp [ZMod.card, sq]

theorem line_rank_sum_eq : RsG (fun _ : Option (ZMod p) × ZMod p => ZMod p) = (p : ℝ) ^ 2 * ((p : ℝ) + 1) := by
  simp [RsG, ZMod.card]
  ring

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

theorem line_map_ne_zero (i : Option (ZMod p) × ZMod p) : lineMap K p i ≠ 0 := by
  intro h0
  have h1 : lineMap K p i (Pi.basisFun K (ZMod p) 0) (linePt p i 0) = 0 := by rw [h0]; rfl
  unfold lineMap at h1
  rw [Matrix.toLin_self] at h1
  simp [Finset.sum_apply, ite_apply] at h1

theorem projective_lines_geometry (v : InfinitePlace K) :
    LatGeom (κ₁ := Empty) (V := fun _ : Option (ZMod p) × ZMod p => ZMod p → K) (ι := fun _ => ZMod p)
      (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p))
      (fun _ => Pi.basisFun K (ZMod p)) (fun _ _ => 1) (fun _ => stdLat K (ZMod p)) (lineMap K p)
      (fun i => htMap (Pi.basisFun K (ZMod p)) (fun _ => 1) (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1)
        (lineMap K p i)) v (fun _ => 1) 1 (lineMat p) 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨by simp, by simp, by simp, by simp, standard_lattice_fg K _, standard_lattice_span_eq_top K _,
    fun _ => standard_lattice_fg K _, fun _ => standard_lattice_span_eq_top K _, ?_, ?_, fun _ _ => le_rfl, le_rfl,
    one_pos, by simp, ?_⟩
  · simp only [ZMod.card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_pos Fintype.card_pos hp
  · intro i
    unfold stdLat
    rw [Submodule.map_span_le]
    rintro _ ⟨t, rfl⟩
    rw [LinearMap.coe_restrictScalars]
    unfold lineMap
    rw [Matrix.toLin_self]
    refine Submodule.sum_mem _ fun q _ => ?_
    by_cases hq : q = linePt p i t
    · simp only [Matrix.of_apply, hq, if_true, one_smul]
      exact Submodule.subset_span ⟨_, rfl⟩
    · simp only [Matrix.of_apply, hq, if_false, zero_smul]
      exact Submodule.zero_mem _
  · intro i k j
    simp only [lineMap, LinearMap.toMatrix_toLin, inv_one, Matrix.one_mul, Matrix.mul_one,
      Matrix.map_apply, Matrix.of_apply, lineMat, Sum.inl.injEq]
    split_ifs <;> simp

theorem projective_lines_power_hypothesis (hp19 : 19 ≤ p) (v : InfinitePlace K) :
    ∃ (h : Option (ZMod p) × ZMod p → ℝ) (s u : ℝ), 0 ≤ u ∧ ∀ HH U : ℝ,
      s - muMinDef (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p)) ≤ HH →
      0 < HH → u ≤ U →
      HypBPow (κ₁ := Empty) (V := fun _ : Option (ZMod p) × ZMod p => ZMod p → K) (ι := fun _ => ZMod p)
        (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p))
        (fun _ => Pi.basisFun K (ZMod p)) (fun _ _ => 1) (fun _ => stdLat K (ZMod p)) (lineMap K p) h v
        (fun _ => 1) 1 (lineMat p) (fun _ => 1) (ιf := fun _ => ZMod p) (lineMat p) (fun _ => 1)
        s u U HH 0 ((p : ℝ) ^ 2) 0 0 0 0 (HH / ((p : ℝ) + 1)) ((p : ℝ) + 1) 1 := by
  have hpR : (19 : ℝ) ≤ p := by exact_mod_cast hp19
  set hh : Option (ZMod p) × ZMod p → ℝ := fun i => htMap (Pi.basisFun K (ZMod p)) (fun _ => 1)
    (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (lineMap K p i) with hhh
  set mu : Option (ZMod p) × ZMod p → ℝ :=
    fun i => muDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i with hmu
  set s : ℝ := (∑ i : Option (ZMod p) × ZMod p, (Fintype.card (ZMod p) : ℝ) * mu i)
    / ∑ _i : Option (ZMod p) × ZMod p, (Fintype.card (ZMod p) : ℝ) with hs
  set u : ℝ := ∑ i : Option (ZMod p) × ZMod p,
    |muMaxDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i - s| with hu
  have hR : (0 : ℝ) < ∑ _i : Option (ZMod p) × ZMod p, (Fintype.card (ZMod p) : ℝ) := by
    have := line_rank_sum_eq p
    unfold RsG at this
    rw [this]
    positivity
  have hu0 : 0 ≤ u := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨hh, s, u, hu0, fun HH U h1 h2 h3 => ?_⟩
  have num : LatNum (V := fun _ : Option (ZMod p) × ZMod p => ZMod p → K) (ι := fun _ => ZMod p)
      (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p))
      (fun _ => Pi.basisFun K (ZMod p)) (fun _ _ => 1) (fun _ => stdLat K (ZMod p)) hh s u HH := by
    refine ⟨?_, hu0, fun i => ?_, h1, h2.le⟩
    · rw [hs, div_mul_cancel₀ _ hR.ne']
    · have k1 := le_abs_self (muMaxDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i - s)
      have k2 : |muMaxDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i - s| ≤ u :=
        Finset.single_le_sum
          (f := fun i => |muMaxDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i - s|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
  have hx0 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
  have hx : ((p : ℝ) + 1) ^ (-(1 : ℝ)) = 1 / ((p : ℝ) + 1) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_one, one_div]
  have hx20 : 1 / ((p : ℝ) + 1) ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hxp : 0 < 1 / ((p : ℝ) + 1) := by positivity
  refine ⟨projective_lines_geometry p K v, num, fun _ => one_pos, fun _ => by simp, fun _ => by simp, by positivity,
    by rw [hx]; exact hx20, ?_, by norm_num, by rw [hx]; positivity, by rw [hx]; positivity, le_rfl, le_rfl,
    ?_, ?_, line_model_input_sizes p, by linarith, by norm_num, by positivity, ?_, h3, by norm_num⟩
  · rw [Real.rpow_one, line_rank_sum_eq]
  · rw [hx]; simpa using hxp.le
  · simp
  · rw [Real.rpow_one, mul_div_cancel₀ _ hx0.ne']

end Lines

theorem projective_lines_all_cases : ModelLinesAll := by
  intro p _ hp19 K _ _ _ _ v
  obtain ⟨h, s, u, -, H⟩ := projective_lines_power_hypothesis p K hp19 v
  have hpR : (19 : ℝ) ≤ p := by exact_mod_cast hp19
  set HH : ℝ := |s - muMinDef (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1)
    (stdLat K (ZMod p × ZMod p))| + 1 with hHH
  have h0 : 0 < HH := by positivity
  refine ⟨h, s, u, u, HH, HH / ((p : ℝ) + 1), H HH u ?_ h0 le_rfl, ?_, line_map_ne_zero p K⟩
  · have := le_abs_self (s - muMinDef (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1)
      (stdLat K (ZMod p × ZMod p)))
    linarith
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith

theorem projective_lines_model : ModelLines := by
  intro K _ _ _ _ v
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨h, s, u, U, HH, bb, H, h1, h2⟩ := projective_lines_all_cases 19 le_rfl K v
  have e1 : ((19 : ℕ) : ℝ) ^ 2 = 361 := by norm_num
  have e2 : ((19 : ℕ) : ℝ) + 1 = 20 := by norm_num
  rw [e1, e2] at H
  exact ⟨h, s, u, U, HH, bb, H, h1, h2⟩

theorem projective_lines_model₂ : ExistsModelLines := by
  intro K _ _ _ _ v
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨h, s, u, hu0, H⟩ := projective_lines_power_hypothesis 19 K le_rfl v
  have e1 : ((19 : ℕ) : ℝ) ^ 2 = 361 := by norm_num
  have e2 : ((19 : ℕ) : ℝ) + 1 = 20 := by norm_num
  rw [e1, e2] at H
  set k : ℝ := Real.log (Fintype.card (Option (ZMod 19) × ZMod 19) : ℝ) with hk
  have hk0 : 0 ≤ k := Real.log_natCast_nonneg _
  set t : ℝ := |s - muMinDef (Pi.basisFun K (ZMod 19 × ZMod 19)) (fun _ => 1)
    (stdLat K (ZMod 19 × ZMod 19))| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hx : (20 : ℝ) ^ (-(1 : ℝ)) = 1 / 20 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
  have H1 := H (t + 1 + 20 * k) (1 * (1 * (20 * ((t + 1 + 20 * k) / 20)) * 1 + 0 + u))
    (by have := le_abs_self (s - muMinDef (Pi.basisFun K (ZMod 19 × ZMod 19)) (fun _ => 1)
          (stdLat K (ZMod 19 × ZMod 19)))
        linarith)
    (by positivity) (by linarith)
  have H2 := power_hyp_to_ramified _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1
  rw [hx] at H2
  exact ⟨h, s, u, t + 1 + 20 * k, (t + 1 + 20 * k) / 20, k, 1, 1, 20 * ((t + 1 + 20 * k) / 20), 1, 0, u, H2,
    rfl, le_rfl, le_rfl, le_rfl, hu0, le_rfl, by linarith⟩

theorem inclusion_matrix_isometry (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁] :
    (inclMat κ κ₁)ᴴ * inclMat κ κ₁ = 1 := by
  ext k l
  simp [inclMat, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem hs_sq_one (n : Type) [Fintype n] [DecidableEq n] :
    hsSq (1 : Matrix n n ℂ) = Fintype.card n := by
  simp [hsSq, Matrix.one_apply, apply_ite]

theorem local_length_self_eq_zero {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (w : slopeLatticeData.FinPl K) (L : Submodule (𝓞 K) V) : slopeLatticeData.lenAt w L L = 0 := by
  have := w.2.isPrime
  have hs : Subsingleton (L ⧸ L.comap L.subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_self]
  unfold slopeLatticeData.lenAt
  rw [Module.length_eq_zero_iff]
  infer_instance

theorem standard_lattice_ne_bot (K n : Type) [Field K] [NumberField K] [Fintype n] [Nonempty n] :
    stdLat K n ≠ ⊥ := by
  intro h0
  obtain ⟨i⟩ := (inferInstance : Nonempty n)
  have h1 : Pi.basisFun K n i ∈ stdLat K n := Submodule.subset_span ⟨i, rfl⟩
  rw [h0] at h1
  exact (Pi.basisFun K n).ne_zero i ((Submodule.mem_bot _).1 h1)

end Formalism.LFunctionChainParameters.ProjectiveLineModels
