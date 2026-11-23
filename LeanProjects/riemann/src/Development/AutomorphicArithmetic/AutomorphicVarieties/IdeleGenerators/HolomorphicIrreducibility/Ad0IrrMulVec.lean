import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

open UpperTheory.V.Af UpperTheory.V.Sd Matrix

namespace UpperTheory.V.Sd

private theorem ad0Irr_factor {k : Type} [Field k] [CharZero k] [IsAlgClosed k] (A B C : k)
    (h : ¬ (A = 0 ∧ B = 0 ∧ C = 0)) :
    ∃ a0 a1 b0 b1 : k, ¬ (a0 = 0 ∧ a1 = 0) ∧ ¬ (b0 = 0 ∧ b1 = 0) ∧
      ∀ x y : k, A * x ^ 2 + B * x * y + C * y ^ 2 = (x * a1 - y * a0) * (x * b1 - y * b0) := by
  by_cases hA : A = 0
  · subst hA
    refine ⟨-1, 0, -C, B, by simp, ?_, ?_⟩
    · rintro ⟨h1, h2⟩
      exact h ⟨rfl, h2, by simpa using h1⟩
    · intro x y
      ring
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (B ^ 2 - 4 * A * C) (n := 2) (by norm_num)
    refine ⟨A * ((-B + s) / (2 * A)), A, (-B - s) / (2 * A), 1, fun h' => hA h'.2, fun h' => one_ne_zero h'.2, ?_⟩
    have hC : C = (B ^ 2 - s ^ 2) / (4 * A) := by
      rw [hs]
      field_simp
      ring
    intro x y
    rw [hC]
    field_simp
    ring

private theorem ad0Irr_par {k : Type} [Field k] {a0 a1 x y : k} (ha : ¬ (a0 = 0 ∧ a1 = 0))
    (h : x * a1 - y * a0 = 0) : ∃ c : k, x = c * a0 ∧ y = c * a1 := by
  by_cases h0 : a0 = 0
  · have h1 : a1 ≠ 0 := fun h1 => ha ⟨h0, h1⟩
    subst h0
    have hx : x * a1 = 0 := by simpa using h
    refine ⟨y / a1, ?_, by field_simp⟩
    simp [(mul_eq_zero.mp hx).resolve_right h1]
  · refine ⟨x / a0, by field_simp, ?_⟩
    field_simp
    linear_combination -h

private def lineStab {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (a : Fin 2 → k) (ha : a ≠ 0) :
    Subgroup Γ where
  carrier := {g | ∃ c : k, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ a = c • a}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨d * c, ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_smul, hc, smul_smul]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    have h1 : (ρ g⁻¹ : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]
    rw [hc, Matrix.mulVec_smul] at h1
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact ha (by simpa using h1.symm)
    refine ⟨c⁻¹, ?_⟩
    conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

private theorem ad0Irr_line {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (a : Fin 2 → k) (ha : a ≠ 0) :
    ¬ IsIrr (ρ.comp (lineStab ρ a ha).subtype) := by
  rintro ⟨-, -, h⟩
  have hinv : Formalism.MainNotions.N.IsInv (ρ.comp (lineStab ρ a ha).subtype) (Submodule.span k {a}) := by
    rintro ⟨g, hg⟩ v hv
    obtain ⟨c, hc⟩ := hg
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [Matrix.mulVec_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  rcases h _ le_top hinv with h0 | h1
  · exact ha (by simpa using h0)
  · have e0 : (Pi.single 0 1 : Fin 2 → k) ∈ Submodule.span k {a} := h1 ▸ Submodule.mem_top
    have e1 : (Pi.single 1 1 : Fin 2 → k) ∈ Submodule.span k {a} := h1 ▸ Submodule.mem_top
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp e0
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp e1
    have h00 := congrFun hs 0
    have h01 := congrFun hs 1
    have h10 := congrFun ht 0
    have h11 := congrFun ht 1
    simp at h00 h01 h10 h11
    rcases h01 with h' | h' <;> rcases h10 with h'' | h'' <;> simp_all

private theorem ad0Irr_core {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k]
    [IsAlgClosed k] [TopologicalSpace k] [IsTopologicalRing k] [T1Space k] (ρ : Γ →* GL (Fin 2) k) (hρ : Continuous ρ)
    (hi : IrrOpen ρ) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (A B C : k) (h : ¬ (A = 0 ∧ B = 0 ∧ C = 0))
    (hQ : ∀ g ∈ H, ∀ x y : k, A * x ^ 2 + B * x * y + C * y ^ 2 = 0 →
      A * (ρ g 0 0 * x + ρ g 0 1 * y) ^ 2 + B * (ρ g 0 0 * x + ρ g 0 1 * y) * (ρ g 1 0 * x + ρ g 1 1 * y)
        + C * (ρ g 1 0 * x + ρ g 1 1 * y) ^ 2 = 0) : False := by
  obtain ⟨a0, a1, b0, b1, ha, hb, hf⟩ := ad0Irr_factor A B C h
  have hav : (![a0, a1] : Fin 2 → k) ≠ 0 := by
    intro h0
    exact ha ⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩
  have hc : ∀ i j, Continuous fun g => (ρ g : Matrix (Fin 2) (Fin 2) k) i j :=
    fun i j => (Units.continuous_val.comp hρ).matrix_elem i j
  have hmv : ∀ g : Γ, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ ![a0, a1] =
      ![ρ g 0 0 * a0 + ρ g 0 1 * a1, ρ g 1 0 * a0 + ρ g 1 1 * a1] := by
    intro g
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hmem : ∀ g, g ∈ lineStab ρ ![a0, a1] hav ↔
      (ρ g 0 0 * a0 + ρ g 0 1 * a1) * a1 - (ρ g 1 0 * a0 + ρ g 1 1 * a1) * a0 = 0 := by
    intro g
    show (∃ c : k, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ ![a0, a1] = c • ![a0, a1]) ↔ _
    rw [hmv]
    constructor
    · rintro ⟨c, hc'⟩
      have e0 := congrFun hc' 0
      have e1 := congrFun hc' 1
      simp at e0 e1
      rw [e0, e1]
      ring
    · intro h'
      obtain ⟨c, h0, h1⟩ := ad0Irr_par ha h'
      exact ⟨c, by ext i; fin_cases i <;> simp [h0, h1]⟩
  have hnz : ∀ g, ¬ ((ρ g 0 0 * a0 + ρ g 0 1 * a1) = 0 ∧ (ρ g 1 0 * a0 + ρ g 1 1 * a1) = 0) := by
    rintro g ⟨h0, h1⟩
    apply hav
    have h2 : (ρ g⁻¹ : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ ![a0, a1]) = ![a0, a1] := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]
    have hz : (![0, 0] : Fin 2 → k) = 0 := by
      ext i
      fin_cases i <;> rfl
    rw [← h2, hmv, h0, h1, hz, Matrix.mulVec_zero]
  have hzero : ∀ g ∈ H, ((ρ g 0 0 * a0 + ρ g 0 1 * a1) * a1 - (ρ g 1 0 * a0 + ρ g 1 1 * a1) * a0) *
      ((ρ g 0 0 * a0 + ρ g 0 1 * a1) * b1 - (ρ g 1 0 * a0 + ρ g 1 1 * a1) * b0) = 0 := by
    intro g hg
    rw [← hf]
    exact hQ g hg a0 a1 (by rw [hf]; ring)
  have hopen : IsOpen ((H ⊓ lineStab ρ ![a0, a1] hav : Subgroup Γ) : Set Γ) := by
    by_cases hab : a0 * b1 - a1 * b0 = 0
    · have hle : H ≤ lineStab ρ ![a0, a1] hav := by
        intro g hg
        rw [hmem]
        obtain ⟨c, hc0, hc1⟩ := ad0Irr_par ha (x := b0) (y := b1) (by linear_combination -hab)
        rcases mul_eq_zero.mp (hzero g hg) with h1 | h1
        · exact h1
        · have hc2 : c ≠ 0 := by
            rintro rfl
            exact hb ⟨by simpa using hc0, by simpa using hc1⟩
          rw [hc0, hc1] at h1
          have h3 : c * ((ρ g 0 0 * a0 + ρ g 0 1 * a1) * a1 - (ρ g 1 0 * a0 + ρ g 1 1 * a1) * a0) = 0 := by
            linear_combination h1
          exact (mul_eq_zero.mp h3).resolve_left hc2
      rw [inf_eq_left.mpr hle]
      exact hH
    · have hset : ((H ⊓ lineStab ρ ![a0, a1] hav : Subgroup Γ) : Set Γ) = (H : Set Γ) ∩
          (fun g => (ρ g 0 0 * a0 + ρ g 0 1 * a1) * b1 - (ρ g 1 0 * a0 + ρ g 1 1 * a1) * b0) ⁻¹' {0}ᶜ := by
        ext g
        simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_preimage, Set.mem_compl_iff,
          Set.mem_singleton_iff]
        rw [hmem]
        constructor
        · rintro ⟨hg, h1⟩
          refine ⟨hg, fun h2 => ?_⟩
          obtain ⟨c, hc0, hc1⟩ := ad0Irr_par ha h1
          apply hnz g
          rw [hc0, hc1] at h2 ⊢
          have h3 : c * (a0 * b1 - a1 * b0) = 0 := by linear_combination h2
          have hc2 : c = 0 := (mul_eq_zero.mp h3).resolve_right hab
          simp [hc2]
        · rintro ⟨hg, h2⟩
          exact ⟨hg, (mul_eq_zero.mp (hzero g hg)).resolve_right h2⟩
      rw [hset]
      refine hH.inter (IsOpen.preimage ?_ isOpen_compl_singleton)
      exact ((((hc 0 0).mul continuous_const).add ((hc 0 1).mul continuous_const)).mul continuous_const).sub
        ((((hc 1 0).mul continuous_const).add ((hc 1 1).mul continuous_const)).mul continuous_const)
  have hopen' : IsOpen ((lineStab ρ ![a0, a1] hav : Subgroup Γ) : Set Γ) :=
    Subgroup.isOpen_mono inf_le_right hopen
  exact ad0Irr_line ρ _ hav (hi _ hopen')

private theorem ad0Irr_mulVec {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (g : Γ) :
    ∃ d : k, d ≠ 0 ∧ ∀ v : Fin 3 → k, (ad0 ρ g : Matrix (Fin 3) (Fin 3) k) *ᵥ v =
      d • ![ρ g 0 0 ^ 2 * v 0 + ρ g 0 0 * ρ g 0 1 * v 1 + ρ g 0 1 ^ 2 * v 2,
        2 * ρ g 0 0 * ρ g 1 0 * v 0 + (ρ g 0 0 * ρ g 1 1 + ρ g 0 1 * ρ g 1 0) * v 1 + 2 * ρ g 0 1 * ρ g 1 1 * v 2,
        ρ g 1 0 ^ 2 * v 0 + ρ g 1 0 * ρ g 1 1 * v 1 + ρ g 1 1 ^ 2 * v 2] := by
  refine ⟨((GeneralLinearGroup.det.comp ρ)⁻¹ g : kˣ), Units.ne_zero _, ?_⟩
  intro v
  rw [ad0, tw_val, Matrix.smul_mulVec]
  congr 1
  ext i
  fin_cases i <;> simp [symSquareMatrixHom, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end UpperTheory.V.Sd

private theorem exists_ad0_mulVec_veronese_eq_smul {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (g : Γ) (x y : k) :
    ∃ d : k, d ≠ 0 ∧ (ad0 ρ g : Matrix (Fin 3) (Fin 3) k) *ᵥ ![x ^ 2, 2 * x * y, y ^ 2] =
      d • ![(ρ g 0 0 * x + ρ g 0 1 * y) ^ 2, 2 * (ρ g 0 0 * x + ρ g 0 1 * y) * (ρ g 1 0 * x + ρ g 1 1 * y),
        (ρ g 1 0 * x + ρ g 1 1 * y) ^ 2] := by
  obtain ⟨d, hd, h⟩ := ad0Irr_mulVec ρ g
  refine ⟨d, hd, ?_⟩
  rw [h]
  congr 1
  ext i
  fin_cases i <;> simp <;> ring

private theorem ad0_mulVec_pairing_eq_mul_pairing {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (g : Γ) (u v : Fin 3 → k) :
    ∃ e : k, 2 * ((ad0 ρ g : Matrix (Fin 3) (Fin 3) k) *ᵥ u) 2 * ((ad0 ρ g : Matrix (Fin 3) (Fin 3) k) *ᵥ v) 0
      - ((ad0 ρ g : Matrix (Fin 3) (Fin 3) k) *ᵥ u) 1 * ((ad0 ρ g : Matrix (Fin 3) (Fin 3) k) *ᵥ v) 1
      + 2 * ((ad0 ρ g : Matrix (Fin 3) (Fin 3) k) *ᵥ u) 0 * ((ad0 ρ g : Matrix (Fin 3) (Fin 3) k) *ᵥ v) 2
      = e * (2 * u 2 * v 0 - u 1 * v 1 + 2 * u 0 * v 2) := by
  obtain ⟨d, -, h⟩ := ad0Irr_mulVec ρ g
  refine ⟨d ^ 2 * (ρ g 0 0 * ρ g 1 1 - ρ g 0 1 * ρ g 1 0) ^ 2, ?_⟩
  rw [h u, h v]
  simp
  ring

private theorem finrank_lt_three_of_proper_submodule {k : Type} [Field k] (W : Submodule k (Fin 3 → k)) (ht : W ≠ ⊤) :
    Module.finrank k W < 3 := by
  have := Submodule.finrank_lt ht
  simpa using this

theorem UpperTheory.V.Sd.ad0Irr :
    UpperTheory.V.Sd.Ad0Irr := by
  intro l _ Γ _ _ _ ρ hρ hi H hH
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, ?_⟩
  intro W _ hW
  by_contra hne
  push_neg at hne
  obtain ⟨hb, ht⟩ := hne
  have hWg : ∀ g ∈ H, ∀ v ∈ W, (ad0 ρ g : Matrix (Fin 3) (Fin 3) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v ∈ W :=
    fun g hg v hv => hW ⟨g, hg⟩ v hv
  have key : ∀ α β γ : Formalism.ConjugateSelfDual.Qbar l, ¬ (α = 0 ∧ β = 0 ∧ γ = 0) →
      (∀ g ∈ H, ∀ v : Fin 3 → Formalism.ConjugateSelfDual.Qbar l, α * v 0 + β * v 1 + γ * v 2 = 0 →
        α * ((ad0 ρ g : Matrix (Fin 3) (Fin 3) _) *ᵥ v) 0 + β * ((ad0 ρ g : Matrix (Fin 3) (Fin 3) _) *ᵥ v) 1
          + γ * ((ad0 ρ g : Matrix (Fin 3) (Fin 3) _) *ᵥ v) 2 = 0) → False := by
    intro α β γ hne hinv
    refine ad0Irr_core ρ hρ hi H hH α (2 * β) γ ?_ ?_
    · rintro ⟨h1, h2, h3⟩
      exact hne ⟨h1, by simpa using h2, h3⟩
    · intro g hg x y hxy
      obtain ⟨d, hd, hφ⟩ := exists_ad0_mulVec_veronese_eq_smul ρ g x y
      have h1 := hinv g hg ![x ^ 2, 2 * x * y, y ^ 2] (by simp; linear_combination hxy)
      rw [hφ] at h1
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h1
      have h2 : d * (α * (ρ g 0 0 * x + ρ g 0 1 * y) ^ 2
          + 2 * β * (ρ g 0 0 * x + ρ g 0 1 * y) * (ρ g 1 0 * x + ρ g 1 1 * y)
          + γ * (ρ g 1 0 * x + ρ g 1 1 * y) ^ 2) = 0 := by
        linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_left hd
  have hn0 : Module.finrank (Formalism.ConjugateSelfDual.Qbar l) W ≠ 0 := fun h0 => hb (Submodule.finrank_eq_zero.mp h0)
  have hn3 : Module.finrank (Formalism.ConjugateSelfDual.Qbar l) W < 3 := finrank_lt_three_of_proper_submodule W ht
  rcases (by omega : Module.finrank (Formalism.ConjugateSelfDual.Qbar l) W = 1 ∨ Module.finrank (Formalism.ConjugateSelfDual.Qbar l) W = 2) with h1 | h2
  · obtain ⟨⟨w, hwW⟩, hw0, hw⟩ := finrank_eq_one_iff'.mp h1
    have hw'0 : w ≠ 0 := fun h => hw0 (Subtype.ext h)
    apply key (2 * w 2) (-(w 1)) (2 * w 0)
    · rintro ⟨e1, e2, e3⟩
      apply hw'0
      ext i
      fin_cases i <;> simp_all
    · intro g hg v hv
      have hin : (ad0 ρ g⁻¹ : Matrix (Fin 3) (Fin 3) _) *ᵥ w ∈ W := hWg g⁻¹ (H.inv_mem hg) w hwW
      obtain ⟨c, hc⟩ := hw ⟨_, hin⟩
      have hc' : (ad0 ρ g⁻¹ : Matrix (Fin 3) (Fin 3) _) *ᵥ w = c • w := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      have hback : (ad0 ρ g : Matrix (Fin 3) (Fin 3) _) *ᵥ ((ad0 ρ g⁻¹ : Matrix (Fin 3) (Fin 3) _) *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
      obtain ⟨e, he⟩ := ad0_mulVec_pairing_eq_mul_pairing ρ g ((ad0 ρ g⁻¹ : Matrix (Fin 3) (Fin 3) _) *ᵥ w) v
      rw [hback, hc'] at he
      simp only [Pi.smul_apply, smul_eq_mul] at he
      linear_combination he + e * c * hv
  · obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr ht) inferInstance
    have hle : W ≤ LinearMap.ker f := by
      intro v hv
      have hm : f v ∈ Submodule.map f W := Submodule.mem_map_of_mem hv
      rw [hfW] at hm
      simpa using hm
    have hrange : LinearMap.range f = ⊤ := by
      obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hf0 (LinearMap.ext hcon)
      refine LinearMap.range_eq_top.mpr fun t => ⟨(t / f u) • u, ?_⟩
      simp [hu]
    have hker : Module.finrank (Formalism.ConjugateSelfDual.Qbar l) (LinearMap.ker f) = 2 := by
      have := LinearMap.finrank_range_add_finrank_ker f
      rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
      omega
    have heq : W = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, hker])
    have hexp : ∀ v : Fin 3 → Formalism.ConjugateSelfDual.Qbar l,
        f v = f (Pi.single 0 1) * v 0 + f (Pi.single 1 1) * v 1 + f (Pi.single 2 1) * v 2 := by
      intro v
      have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
        ext i
        fin_cases i <;> simp
      conv_lhs => rw [hv]
      simp only [map_add, map_smul, smul_eq_mul]
      ring
    apply key (f (Pi.single 0 1)) (f (Pi.single 1 1)) (f (Pi.single 2 1))
    · rintro ⟨e1, e2, e3⟩
      exact hf0 (LinearMap.ext fun v => by rw [hexp, e1, e2, e3]; simp)
    · intro g hg v hv
      rw [← hexp] at hv ⊢
      have hvW : v ∈ W := by
        rw [heq]
        exact hv
      have hm := hWg g hg v hvW
      rw [heq] at hm
      exact hm
