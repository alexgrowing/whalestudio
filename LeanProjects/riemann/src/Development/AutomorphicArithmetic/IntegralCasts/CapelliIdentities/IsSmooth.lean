import Mathlib

noncomputable def UpperTheory.Reformulated.B.DYka2.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.DYka2.main :
    ∀ {Γ V W : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : _root_.Module ℂ W] {ρ : Representation ℂ Γ V}
      {σ : Representation ℂ Γ W},
      UpperTheory.Reformulated.B.DYka2.IsSmooth ρ →
        ∀ (f : ρ.IntertwiningMap σ) {L : Subgroup Γ},
          IsCompact (↑L : Set Γ) →
            ∀ (χ : Γ → ℂ) (u : V),
              (f : V → W) u ≠ (0 : W) →
                (∀ g ∈ L, ((σ : Γ → W →ₗ[ℂ] W) g : W → W) ((f : V → W) u) = χ g • (f : V → W) u) →
                  ∃ (v : V), v ≠ (0 : V) ∧ ∀ g ∈ L, ((ρ : Γ → V →ₗ[ℂ] V) g : V → V) v = χ g • v := by
  intro Γ V W _ _ _ _ _ _ _ ρ σ hρ f L hL χ u hu hχ
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hint : ∀ (g : Γ) (v : V), f (ρ g v) = σ g (f v) := fun g v => Representation.IntertwiningMap.isIntertwining ρ σ f g v
  have hmul : ∀ g ∈ L, ∀ h ∈ L, χ (g * h) = χ g * χ h := by
    intro g hg h hh
    have key : χ (g * h) • f u = (χ g * χ h) • f u := by
      rw [← hχ (g * h) (L.mul_mem hg hh), map_mul, Module.End.mul_apply, hχ h hh, map_smul,
        hχ g hg, smul_smul, mul_comm]
    exact smul_left_injective ℂ hu key
  have h1 : χ 1 = 1 := by
    have key : χ 1 • f u = (1 : ℂ) • f u := by
      rw [← hχ 1 L.one_mem, map_one, one_smul]; rfl
    exact smul_left_injective ℂ hu key
  have hne : ∀ g ∈ L, χ g ≠ 0 := by
    intro g hg h0
    have := hmul g hg g⁻¹ (L.inv_mem hg)
    rw [mul_inv_cancel, h1, h0, zero_mul] at this
    exact one_ne_zero this
  let H : Subgroup L :=
    { carrier := {g | ρ (g : Γ) u = u}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : ρ ((a : Γ)⁻¹) (ρ (a : Γ) u) = u := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rw [ha] at this
        simpa using this }
  have hHopen : IsOpen (H : Set L) := (hρ u).preimage continuous_subtype_val
  haveI : Finite (L ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  haveI : Fintype (L ⧸ H) := Fintype.ofFinite _
  have hχH : ∀ h : L, h ∈ H → χ (h : Γ) = 1 := by
    intro h hh
    have e : ρ (h : Γ) u = u := hh
    have key : χ (h : Γ) • f u = (1 : ℂ) • f u := by
      rw [← hχ h h.2, ← hint, e, one_smul]
    exact smul_left_injective ℂ hu key
  let φ : L → V := fun g => (χ (g : Γ))⁻¹ • ρ (g : Γ) u
  have hφ : ∀ a b : L, QuotientGroup.leftRel H a b → φ a = φ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hb : (b : Γ) = a * ((a⁻¹ * b : L) : Γ) := by simp
    have e : ρ ((a⁻¹ * b : L) : Γ) u = u := hab
    have c := hχH _ hab
    simp only [φ]
    rw [hb, hmul _ a.2 _ (a⁻¹ * b).2, c, mul_one, map_mul, Module.End.mul_apply, e]
  let ψ : L ⧸ H → V := Quotient.lift φ hφ
  have hψ : ∀ g : L, ψ (g : L ⧸ H) = φ g := fun g => rfl
  have hfψ : ∀ q : L ⧸ H, f (ψ q) = f u := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [hψ]
      simp only [φ]
      rw [map_smul, hint, hχ g g.2, smul_smul, inv_mul_cancel₀ (hne g g.2), one_smul]
  have hact : ∀ (l : L) (q : L ⧸ H), ρ (l : Γ) (ψ q) = χ (l : Γ) • ψ (l • q) := by
    intro l q
    induction q using QuotientGroup.induction_on with
    | H g =>
      have : l • (g : L ⧸ H) = ((l * g : L) : L ⧸ H) := rfl
      rw [this, hψ, hψ]
      simp only [φ]
      rw [map_smul, Subgroup.coe_mul, hmul _ l.2 _ g.2, map_mul, Module.End.mul_apply, smul_smul,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ (hne l l.2), one_mul]
  refine ⟨∑ q : L ⧸ H, ψ q, ?_, ?_⟩
  · intro h0
    have e : f (∑ q : L ⧸ H, ψ q) = (Fintype.card (L ⧸ H) : ℂ) • f u := by
      rw [map_sum]
      simp only [hfψ]
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [h0, map_zero] at e
    have hc : (Fintype.card (L ⧸ H) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (smul_ne_zero hc hu) e.symm
  · intro g hg
    rw [map_sum, Finset.smul_sum]
    simp only [hact ⟨g, hg⟩]
    exact (Equiv.sum_comp (MulAction.toPerm (⟨g, hg⟩ : L)) (fun q => χ g • ψ q))
