import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.OneChar

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def partSub {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

variable {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

lemma sep_X (hI : IsSplit P I) : ∀ g ∈ Xg X.L I, g ≠ 0 → 1 ≤ ‖g‖ := by
  intro g hg hg0
  obtain ⟨x, hx, hu⟩ := hg
  have h1 := hI.sep x hx g hu hg0
  have h2 : (1:ℝ) ≤ ‖g‖ ^ 2 := P.C2.trans h1
  nlinarith [norm_nonneg g]

lemma exists_short_real_span (hI : IsSplit P I) : ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim,
    (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧
    Submodule.span ℝ (Set.range u) = IR I ∧
    ∀ j, ‖u j‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) := by
  obtain ⟨x, u, hxu, hli, hb⟩ := hI.u1
  refine ⟨x, u, hxu, ?_, hb⟩
  have hle : Submodule.span ℝ (Set.range u) ≤ IR I := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hxu j).2.1
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hli, Fintype.card_fin]

lemma span_inf_partSub_le {σ : E →+* ℂ} (u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim)
    (hu : Submodule.span ℝ (Set.range u) = IR I) (W : Submodule ℂ (Vsp X.dim))
    (hW : ∀ j, prj σ (u j) ∈ W) :
    ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim))) ≤ W := by
  rintro v ⟨hvI, hvσ⟩
  have hvσ' : ∀ j : Idx X.dim, j.1 ≠ σ → v j = 0 := hvσ
  have hfix : prj σ v = v := by
    ext i
    by_cases h : i.1 = σ
    · simp [prj, h]
    · simp [prj, h, hvσ' i h]
  have hspan : Submodule.span ℂ (I : Set (Vsp X.dim)) ≤ Submodule.span ℂ (Set.range u) := by
    rw [Submodule.span_le]
    intro y hy
    have hyR : y ∈ IR I := Submodule.subset_span hy
    rw [← hu] at hyR
    exact Submodule.span_le_restrictScalars ℝ ℂ (Set.range u) hyR
  have hv : v ∈ Submodule.span ℂ (Set.range u) := hspan hvI
  rw [← hfix]
  have hmap : Submodule.map (prj σ) (Submodule.span ℂ (Set.range u)) ≤ W := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hW j
  exact hmap (Submodule.mem_map_of_mem hv)

lemma exists_out {σ : E →+* ℂ} {ρ : ℕ}
    (hρ : Module.finrank ℂ (((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim)))) = ρ)
    (u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim)
    (hu : Submodule.span ℝ (Set.range u) = IR I) (W : Submodule ℂ (Vsp X.dim))
    (hW : Module.finrank ℂ W < ρ) : ∃ j, prj σ (u j) ∉ W := by
  by_contra hcon
  push_neg at hcon
  have hle := span_inf_partSub_le u hu W hcon
  have h2 : Module.finrank ℂ ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ :
      Submodule ℂ (Vsp X.dim))) ≤ Module.finrank ℂ W := Submodule.finrank_mono hle
  rw [hρ] at h2
  omega

lemma rho_le [IsCMField E] (hI : IsSplit P I) (ω : Fin (Module.finrank ℚ E) → 𝓞 E)
    (hω : LinearIndependent ℚ (fun j => (ω j : E))) {σ : E →+* ℂ} {ρ : ℕ}
    (hρ : Module.finrank ℂ (((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim)))) = ρ) :
    ρ ≤ P.m := by
  classical
  obtain ⟨x, u, hxu, hspan, -⟩ := exists_short_real_span hI
  set S := prj σ '' (Xg X.L I : Set (Vsp X.dim))
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ S
  have hbfin : b.Finite := hbli.setFinite
  have := hbfin.fintype
  have hV1 : ((Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ partSub σ : Submodule ℂ (Vsp X.dim))) ≤ Submodule.span ℂ b := by
    rw [hbspan]
    exact span_inf_partSub_le u hspan _ fun j => Submodule.subset_span ⟨u j, ⟨x j, (hxu j).1, (hxu j).2⟩, rfl⟩
  have h1 : ρ ≤ Fintype.card b := by
    have := Submodule.finrank_mono hV1
    rw [hρ] at this
    have h2 := finrank_span_eq_card hbli
    rw [Subtype.range_coe] at h2
    have h3 : Fintype.card {x // x ∈ b} = Fintype.card b := Fintype.card_congr (Equiv.refl _)
    omega
  have h2 := rank_bound X.L I (sep_X hI) (fun α u hu => Xg_act X.stable hI.stable α hu) ω hω σ b hbS hbli
  obtain ⟨ρ', hρ'm, hρ'⟩ := hI.rank
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hf : 2 * PT.f E ≤ Module.finrank ℚ E := by unfold PT.f; omega
  have h3 : Module.finrank ℚ E * Fintype.card b ≤ Module.finrank ℚ E * ρ' := by
    rw [hρ'] at h2; nlinarith
  have h4 := Nat.le_of_mul_le_mul_left h3 hn
  omega

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
