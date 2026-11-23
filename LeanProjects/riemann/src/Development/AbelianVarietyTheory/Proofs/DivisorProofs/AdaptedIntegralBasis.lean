import Mathlib
open PowerSeries

namespace GlobalTheory.LaurentFlagBasis

variable {F : Type} [Field F]

noncomputable def red {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → F := fun a => constantCoeff (y a)

noncomputable def lift {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → LaurentSeries F :=
  fun a => (y a : LaurentSeries F)

lemma exists_primitive {n : ℕ} (u : Fin n → LaurentSeries F) (hu : u ≠ 0) :
    ∃ (i : Fin n) (y : Fin n → PowerSeries F), lift y = (u i)⁻¹ • u ∧ y i = 1 := by
  obtain ⟨l, hl⟩ : ∃ l, u l ≠ 0 := by
    by_contra h; push_neg at h; exact hu (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun a => Valued.v (u a))
    ⟨l, Finset.mem_univ _⟩
  have hvl : Valued.v (u l) ≠ 0 := (Valuation.ne_zero_iff _).mpr hl
  have hvi : 0 < Valued.v (u i) := by
    have := hi l (Finset.mem_univ _)
    exact lt_of_lt_of_le (zero_lt_iff.mpr hvl) this
  have hui : u i ≠ 0 := (Valuation.ne_zero_iff _).mp hvi.ne'
  have key : ∀ a, ∃ P : PowerSeries F, (P : LaurentSeries F) = (u i)⁻¹ * u a := by
    intro a
    have := (LaurentSeries.val_le_one_iff_eq_coe F ((u i)⁻¹ * u a)).mp (by
      rw [map_mul, map_inv₀, inv_mul_le_one₀ hvi]
      exact hi a (Finset.mem_univ _))
    exact this
  choose y hy using key
  refine ⟨i, y, funext fun a => ?_, ?_⟩
  · simp [lift, hy]
  · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change ((y i : PowerSeries F) : LaurentSeries F) = ((1 : PowerSeries F) : LaurentSeries F)
    rw [hy, inv_mul_cancel₀ hui, map_one]

lemma exists_indep {n : ℕ} : ∀ (d : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)),
    d ≤ Module.finrank (LaurentSeries F) U →
    ∃ y : Fin d → (Fin n → PowerSeries F), (∀ b, lift (y b) ∈ U) ∧
      LinearIndependent F (fun b => red (y b))
  | 0, U, _ => ⟨Fin.elim0, fun b => b.elim0, linearIndependent_empty_type⟩
  | d+1, U, hd => by
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := U) (by
      intro h; rw [h, finrank_bot] at hd; omega)
    obtain ⟨i, y0, hy0, hy0i⟩ := exists_primitive u hu0
    let f : U →ₗ[LaurentSeries F] LaurentSeries F := (LinearMap.proj i).comp U.subtype
    let U' : Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := (LinearMap.ker f).map U.subtype
    have hU' : d ≤ Module.finrank (LaurentSeries F) U' := by
      have h1 := LinearMap.finrank_range_add_finrank_ker f
      have h2 : Module.finrank (LaurentSeries F) (LinearMap.range f) ≤ 1 := by
        simpa using Submodule.finrank_le (LinearMap.range f)
      have h3 : Module.finrank (LaurentSeries F) U' =
          Module.finrank (LaurentSeries F) (LinearMap.ker f) :=
        (Submodule.equivMapOfInjective _ U.injective_subtype _).finrank_eq.symm
      omega
    obtain ⟨y, hyU, hyi⟩ := exists_indep d U' hU'
    refine ⟨Fin.cons y0 y, ?_, ?_⟩
    · intro b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp only [Fin.cons_zero]; rw [hy0]; exact U.smul_mem _ huU
      · simp only [Fin.cons_succ]
        obtain ⟨z, -, hz⟩ := Submodule.mem_map.mp (hyU b)
        rw [← hz]; exact z.2
    · have e : (fun b => red ((Fin.cons y0 y : Fin (d+1) → Fin n → PowerSeries F) b)) =
          Fin.cons (red y0) (fun b => red (y b)) := by
        ext b; refine Fin.cases ?_ (fun b => ?_) b <;> simp
      rw [e, linearIndependent_finCons]
      refine ⟨hyi, fun hmem => ?_⟩
      have hsub : Submodule.span F (Set.range fun b => red (y b)) ≤
          LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin n => F) i) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨z, hz, hzz⟩ := Submodule.mem_map.mp (hyU b)
        have hz0 : (z : Fin n → LaurentSeries F) i = 0 := hz
        have h0 : ((y b i : PowerSeries F) : LaurentSeries F) = 0 := by
          have := congrFun hzz i
          simp only [Submodule.subtype_apply] at this
          rw [← hz0, this]; rfl
        have h00 : y b i = 0 := by
          apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
          rw [map_zero]; exact h0
        simp [red, h00]
      have := hsub hmem
      simp [red, hy0i] at this

lemma greedy {n : ℕ} (V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j)) :
    ∀ m, m ≤ n → ∃ c : Fin m → (Fin n → PowerSeries F), (∀ j : Fin m, lift (c j) ∈ V j) ∧
      LinearIndependent F (fun j => red (c j))
  | 0, _ => ⟨Fin.elim0, fun j => j.elim0, linearIndependent_empty_type⟩
  | m+1, hm => by
    obtain ⟨c, hcV, hci⟩ := greedy V hV m (by omega)
    obtain ⟨y, hyV, hyi⟩ := exists_indep (Module.finrank (LaurentSeries F) (V m)) (V m) le_rfl
    have : ∃ b, red (y b) ∉ Submodule.span F (Set.range fun j => red (c j)) := by
      by_contra h; push_neg at h
      have h1 : Submodule.span F (Set.range fun b => red (y b)) ≤
          Submodule.span F (Set.range fun j => red (c j)) :=
        Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact h b)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hyi, finrank_span_eq_card hci] at h2
      simp at h2
      have := hV m (by omega)
      omega
    obtain ⟨b, hb⟩ := this
    refine ⟨Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b), ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last]; exact hyV b
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]; exact hcV j
    · have e : (fun j => red ((Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b)) j)) =
          Fin.snoc (α := fun _ => Fin n → F) (fun j => red (c j)) (red (y b)) := by
        ext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      rw [e, linearIndependent_finSnoc]
      exact ⟨hci, hb⟩

end GlobalTheory.LaurentFlagBasis

open GlobalTheory.LaurentFlagBasis in

theorem GlobalTheory.LaurentFlagBasis.adapted_integral_basis : ∀ (F : Type) [Field F] (n R : ℕ)
    (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W →
    ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n),
      (j : ℕ) < Module.finrank (LaurentSeries F) (W k) →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) :
        LaurentSeries F)) ∈ W k := by
  intro F _ n R W hW
  let V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := fun j =>
    ⨅ (k : Fin (R + 1)) (_ : j < Module.finrank (LaurentSeries F) (W k)), W k
  have hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j) := by
    intro j hj
    by_cases h : ∃ k, j < Module.finrank (LaurentSeries F) (W k)
    · obtain ⟨k, hk⟩ := h
      obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun k => j < Module.finrank (LaurentSeries F) (W k)) id
        ⟨k, by simp [hk]⟩
      have hle : W k0 ≤ V j := le_iInf₂ fun k hk => hW (hmin k (by simp [hk]))
      have := Submodule.finrank_mono hle
      simp at hk0
      omega
    · push_neg at h
      have hle : ⊤ ≤ V j := le_iInf₂ fun k hk => absurd hk (not_lt.mpr (h k))
      have := Submodule.finrank_mono hle
      rw [finrank_top, Module.finrank_fin_fun] at this
      omega
  obtain ⟨c, hcV, hci⟩ := greedy V hV n le_rfl
  let g : Matrix (Fin n) (Fin n) (PowerSeries F) := Matrix.of fun a j => c j a
  have hunit : IsUnit g := by
    rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    convert hci using 1
    funext j a
    simp [g, red, Matrix.col]
  refine ⟨hunit.unit, fun k j hj => ?_⟩
  have hmem := hcV j
  have hVk : V j ≤ W k := iInf₂_le k hj
  exact hVk hmem
