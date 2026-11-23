import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExistsMinNorm

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def actHom {dim : (E →+* ℂ) → ℕ} (y : Vsp dim) : 𝓞 E →+ Vsp dim where
  toFun α := act α y
  map_zero' := by ext i; simp [act_apply]
  map_add' α β := act_add_left α β y

lemma act_omega_expand {dim : (E →+* ℂ) → ℕ} (ω : Fin (Module.finrank ℚ E) → 𝓞 E)
    (hω : LinearIndependent ℚ (fun j => (ω j : E))) (α : 𝓞 E) (y : Vsp dim) :
    act α y ∈ Submodule.span ℝ (Set.range fun j => act (ω j) y) := by
  classical
  have hsp : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ :=
    by
      first
      | exact hω.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)
      | (haveI : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
         exact hω.span_eq_top_of_card_eq_finrank (Fintype.card_fin _))
  have hα : (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℚ E) → ℚ, ∑ j, c j • (ω j : E) = α := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 hα
    | exact Submodule.mem_span_range_iff_exists_fun.1 hα
  have key : act α y = ∑ j, ((c j : ℝ)) • act (ω j) y := by
    ext i
    simp only [act, ← hc]
    simp [map_sum, Rat.smul_def, map_mul, map_ratCast, Finset.sum_mul, Complex.real_smul, mul_assoc]
  rw [key]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma rank_bound {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim))
    (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (hact : ∀ (α : 𝓞 E) u, u ∈ Xg L I → act α u ∈ Xg L I)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (σ : E →+* ℂ) (b : Set (Vsp dim)) [Fintype b] (hb : b ⊆ prj σ '' (Xg L I))
    (hli : LinearIndependent ℂ (fun s : b => (s : Vsp dim))) :
    Module.finrank ℚ E * Fintype.card b ≤ Module.finrank ℝ (IR I) := by
  classical
  have hpre : ∀ s : b, ∃ u, u ∈ Xg L I ∧ prj σ u = (s : Vsp dim) := by
    intro s
    obtain ⟨u, hu, h⟩ := hb s.2
    exact ⟨u, hu, h⟩
  choose u hu hus using hpre
  let v : Fin (Module.finrank ℚ E) × b → Vsp dim := fun p => act (ω p.1) (u p.2)
  have hvX : ∀ p, v p ∈ Xg L I := fun p => hact _ _ (hu p.2)
  have hvIR : ∀ p, v p ∈ IR I := by
    intro p
    have h : ∃ x ∈ L, IsU I x (v p) := hvX p
    obtain ⟨x, _, hx⟩ := h
    exact hx.1
  have hprj : ∀ (α : 𝓞 E) (w : Vsp dim), prj σ (act α w) = σ (α : E) • prj σ w := by
    intro α w
    ext i
    by_cases h : i.1 = σ
    · simp [prj, act_apply, h]
    · simp [prj, h]

  have hZ : ∀ m : Fin (Module.finrank ℚ E) × b → ℤ, ∑ p, m p • v p = 0 → ∀ p, m p = 0 := by
    intro m hm
    have h1 : ∑ s : b, (∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) • (s : Vsp dim) = 0 := by
      have := congrArg (prj σ) hm
      rw [map_sum, map_zero] at this
      rw [← this, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ = prj σ (m (j, s) • act (ω j) (u s))
      rw [map_zsmul, hprj, hus, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    rintro ⟨j, s⟩
    have h2 := Fintype.linearIndependent_iff.mp hli
      (fun s => ∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) h1 s
    have h3 : σ (∑ j, ((m (j, s) : E)) * (ω j : E)) = 0 := by
      rw [map_sum]; simpa [map_mul, map_intCast] using h2
    have h4 : ∑ j, ((m (j, s) : ℚ)) • (ω j : E) = 0 := by
      have h5 := (map_eq_zero_iff σ σ.injective).mp h3
      simpa [Rat.smul_def] using h5
    have h6 := Fintype.linearIndependent_iff.mp hω (fun j => (m (j, s) : ℚ)) h4 j
    exact_mod_cast h6

  have hR : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p
    by_contra hcp
    let y : ℕ → Vsp dim := fun k => -(∑ q, ⌊(k : ℝ) * c q⌋ • v q)
    have hyX : ∀ k, y k ∈ Xg L I := fun k =>
      neg_mem (sum_mem fun q _ => zsmul_mem (hvX q) _)
    have hyeq : ∀ k : ℕ, y k = ∑ q, Int.fract ((k : ℝ) * c q) • v q := by
      intro k
      have h0 : ∑ q, ((k : ℝ) * c q) • v q = 0 := by
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, hc, smul_zero]
      simp only [y, Int.fract, sub_smul, Finset.sum_sub_distrib, h0, zero_sub]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
    have hyn : ∀ k, ‖y k‖ ≤ ∑ q, ‖v q‖ := by
      intro k
      rw [hyeq]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    have hfin : {x | x ∈ (Xg L I : Set (Vsp dim)) ∧ ‖x‖ ≤ ∑ q, ‖v q‖}.Finite :=
      finite_sep _ (sep_of_group (Xg L I) hsep _ subset_rfl) _
    let g : ℕ → (Fin (Module.finrank ℚ E) × b → ℤ) := fun k q => ⌊(k : ℝ) * c q⌋
    let Φ : (Fin (Module.finrank ℚ E) × b → ℤ) → Vsp dim := fun m => -(∑ q, m q • v q)
    have hΦ : Function.Injective Φ := by
      intro m m' h
      have h' : ∑ q, m q • v q = ∑ q, m' q • v q := neg_inj.mp h
      have h'' : ∑ q, (m q - m' q) • v q = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, h', sub_self]
      funext q
      exact sub_eq_zero.mp (hZ _ h'' q)
    have hrg : (Set.range g).Finite := by
      refine Set.Finite.of_finite_image ?_ hΦ.injOn
      refine hfin.subset ?_
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨hyX k, hyn k⟩
    have hrp : (Set.range fun k : ℕ => ⌊(k : ℝ) * c p⌋).Finite :=
      (hrg.image (fun m => m p)).subset (by rintro _ ⟨k, rfl⟩; exact ⟨g k, ⟨k, rfl⟩, rfl⟩)
    obtain ⟨B, hB⟩ := hrp.bddAbove
    obtain ⟨B', hB'⟩ := hrp.bddBelow
    have hcpos : 0 < |c p| := abs_pos.mpr hcp
    obtain ⟨k, hk⟩ := exists_nat_gt ((|(B : ℝ)| + |(B' : ℝ)| + 2) / |c p|)
    have hkc : |(B : ℝ)| + |(B' : ℝ)| + 2 < (k : ℝ) * |c p| := by
      rwa [div_lt_iff₀ hcpos] at hk
    have hup : ⌊(k : ℝ) * c p⌋ ≤ B := hB ⟨k, rfl⟩
    have hlo : B' ≤ ⌊(k : ℝ) * c p⌋ := hB' ⟨k, rfl⟩
    have h1 : (k : ℝ) * c p - 1 < (⌊(k : ℝ) * c p⌋ : ℝ) := Int.sub_one_lt_floor _
    have h2 : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ (k : ℝ) * c p := Int.floor_le _
    have hup' : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ B := by exact_mod_cast hup
    have hlo' : (B' : ℝ) ≤ ⌊(k : ℝ) * c p⌋ := by exact_mod_cast hlo
    have hB0 := abs_nonneg (B : ℝ)
    have hB'0 := abs_nonneg (B' : ℝ)
    rcases lt_or_gt_of_ne hcp with hneg | hpos
    · rw [abs_of_neg hneg, mul_neg] at hkc
      have := neg_abs_le (B' : ℝ)
      linarith
    · rw [abs_of_pos hpos] at hkc
      have := le_abs_self (B : ℝ)
      linarith
  have hw : LinearIndependent ℝ (fun p => (⟨v p, hvIR p⟩ : IR I)) :=
    LinearIndependent.of_comp (IR I).subtype hR
  have := hw.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fin] using this

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
