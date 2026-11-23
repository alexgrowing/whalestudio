import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV TensorProduct

namespace UpperTheory.V.SmallClassNumbers

theorem QO_eq (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] :
    QO l O = (O ⊗[ℤ_[l]] (ℚ_[l] ⧸ ZlSub l)) := rfl

theorem ZlSub_eq (l : ℕ) [Fact l.Prime] : ZlSub l = (1 : Submodule ℤ_[l] ℚ_[l]) := by
  first | rfl | exact (Submodule.one_eq_range).symm | (ext x; simp [ZlSub, Submodule.mem_one])

variable (Ω : Type) [Field Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ)

def chi (g : Ω ≃ₐ[ℚ] Ω) : c.O := algebraMap ℤ_[l] c.O ((cyclotomicCharacter Ω l g.toRingEquiv ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l])

def Vanish : Prop :=
  ∀ z : (Ω ≃ₐ[ℚ] Ω) → QO l c.O, Continuous z → (∀ g h, z (g * h) = z g + chi Ω l c e g • z h) →
    (∀ A : ValuationSubring Ω, A.valuation ((l * 2 : ℕ) : Ω) < 1 →
      ∃ m, ∀ g ∈ A.decompositionSubgroup ℚ, z g = chi Ω l c e g • m - m) →
    (∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ A.decompositionSubgroup ℚ, (∀ x, A.valuation x ≤ 1 → A.valuation (g x - x) < 1) →
      z g = chi Ω l c e g • m - m) →
    ∃ m, ∀ g, z g = chi Ω l c e g • m - m

theorem act (g : Ω ≃ₐ[ℚ] Ω) (m : QO l c.O) : twist₂ l (chiO ℚ Ω l c.O ^ (-(e : ℤ))) g m = chi Ω l c e g • m := by
  have h : (((chiO ℚ Ω l c.O ^ (-(e : ℤ))) g : c.Oˣ) : c.O) = chi Ω l c e g := by
    rw [MonoidHom.zpow_apply, chiO, MonoidHom.comp_apply, ← map_zpow]
    rfl
  rw [scalRep_apply, h]

theorem len_eq_zero_iff : len Ω l c e = 0 ↔ Vanish Ω l c e := by
  rw [len, Module.length_eq_zero_iff, Submodule.subsingleton_iff_eq_bot, Submodule.eq_bot_iff]
  constructor
  · intro H z hz hc hD hI
    have hZ : (fun u : (⊤ : Subgroup (G ℚ Ω)) => z u.1) ∈ Z1U (twist₂ l (chiO ℚ Ω l c.O ^ (-(e : ℤ)))) ⊤ := by
      rw [mem_Z1_iff_cocycle]
      exact ⟨hz.comp continuous_subtype_val, fun g h => (hc g.1 h.1).trans (congrArg (z g.1 + ·) (act Ω l c e g.1 _).symm)⟩
    have h0 := H (Submodule.Quotient.mk ⟨_, hZ⟩) (mk_mem_locSel.2 (by
      rintro D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
      · obtain ⟨m, hm⟩ := hD A hA
        exact ⟨m, fun u hu => (hm u.1 hu).trans (congrArg (· - m) (act Ω l c e u.1 m).symm)⟩
      · obtain ⟨m, hm⟩ := hI A
        exact ⟨m, fun u hu => (hm u.1 hu.1 hu.2).trans (congrArg (· - m) (act Ω l c e u.1 m).symm)⟩))
    obtain ⟨m, hm⟩ := (mk_eq_mk _ ⊤ ⟨_, hZ⟩ 0).1 h0
    exact ⟨m, fun g => by
      have := hm ⟨g, trivial⟩
      rw [act] at this
      simpa using this⟩
  · intro H x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hz := (mem_Z1_iff_cocycle _ _).1 z.2
    have hl := mk_mem_locSel.1 hx
    obtain ⟨m, hm⟩ := H (fun g => z.1 ⟨g, trivial⟩) (hz.1.comp (continuous_id.subtype_mk _))
      (fun g h => (hz.2 ⟨g, trivial⟩ ⟨h, trivial⟩).trans (congrArg (z.1 ⟨g, trivial⟩ + ·) (act Ω l c e g _)))
      (fun A hA => (hl _ (Or.inl ⟨A, hA, rfl⟩)).imp fun m hm g hg =>
        (hm ⟨g, trivial⟩ hg).trans (congrArg (· - m) (act Ω l c e g m)))
      (fun A => (hl _ (Or.inr ⟨A, rfl⟩)).imp fun m hm g hg hi =>
        (hm ⟨g, trivial⟩ ⟨hg, hi⟩).trans (congrArg (· - m) (act Ω l c e g m)))
    refine (mk_eq_mk _ ⊤ z 0).2 ⟨m, fun u => ?_⟩
    rw [act]
    simpa using hm u.1

def Large : Prop :=
  ∃ C A : ℕ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), 1 ≤ e → Even e →
    ∀ (c : ∀ l : Nat.Primes, Coef l) (l : Nat.Primes), 5 ≤ (l : ℕ) → ¬ (l : ℕ) - 1 ∣ 2 * e → eO l (c l).O = 1 →
      C * ((e : ℝ) + 1) ^ A < Real.log (l : ℕ) → Vanish Ω l (c l) e

theorem large_of (h : Bound) : Large := by
  obtain ⟨C, A, h⟩ := h
  refine ⟨C, A, fun Ω _ _ _ e he hev c l h5 hg h1 hlt => (len_eq_zero_iff Ω l (c l) e).1 ?_⟩
  obtain ⟨ha, hb⟩ := h Ω e he hev c {l} (fun l' hl' => by rw [Finset.mem_singleton.1 hl']; exact ⟨h5, hg⟩)
  rw [Finset.sum_singleton, h1] at hb
  have hf := ha l (Finset.mem_singleton_self _)
  by_contra h0
  have h2 : 1 ≤ (len Ω l (c l) e).toNat := Nat.one_le_iff_ne_zero.2 fun h' => by
    rcases ENat.toNat_eq_zero.1 h' with h' | h'
    · exact h0 h'
    · exact hf h'
  have h3 : (1 : ℝ) ≤ (len Ω l (c l) e).toNat := by exact_mod_cast h2
  have h4 := Real.log_natCast_nonneg (l : ℕ)
  simp only [ENat.toNat_one, Nat.cast_one, div_one] at hb
  nlinarith

theorem exists_coef (l : ℕ) [Fact l.Prime] : ∃ c : Coef l, c.O = ⊥ := by
  let e := Algebra.botEquivOfInjective (R := ℤ_[l]) (A := PadicAlgCl l) (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  exact ⟨⟨⊥, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm,
    Module.Finite.equiv e.symm.toLinearEquiv⟩, rfl⟩

end UpperTheory.V.SmallClassNumbers

end
