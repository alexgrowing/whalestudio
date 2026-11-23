import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem twist_triv {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    (D : Dat Ω K c e ψ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {C : Type} [Group C]
    (φ : G K Ω →* C) (hφ : (cycBar K Ω l).ker ≤ φ.ker) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A → φ s ≠ 1 → D.ΨQ (galEmb ℚ K Ω s) ^ m = 1) (g : G K Ω) :
    φ g = 1 := by
  have hl : l.Prime := Fact.out
  have hI : Ine (F := ℚ) A ≤ (galEmb ℚ K Ω).range := by
    rw [range_galEmb, ← D.η_ker]
    exact ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1
  have hsur : ∀ u : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A ∧ cycZ K Ω l s = u := fun u => by
    obtain ⟨σ, hσ, hu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
    obtain ⟨s, rfl⟩ := hI hσ
    exact ⟨s, hσ, hu⟩
  by_contra hg
  obtain ⟨s, hs, hsg⟩ := hsur (cycZ K Ω l g)
  have hs1 : φ s ≠ 1 := by
    intro h1
    have : φ (g * s⁻¹) = 1 := hφ (by
      rw [MonoidHom.mem_ker, cycBar, MonoidHom.comp_apply, map_mul, map_inv, hsg, mul_inv_cancel, map_one])
    rw [map_mul, map_inv, h1, inv_one, mul_one] at this
    exact hg this
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  obtain ⟨t, ht, htu⟩ := hsur hu.unit
  have ht1 : D.ΨQ (galEmb ℚ K Ω t) ^ m = 1 := by
    by_cases h1 : φ t = 1
    · have h2 := h (s * t) (by rw [map_mul]; exact mul_mem hs ht) (by rwa [map_mul, h1, mul_one])
      rwa [map_mul, map_mul, mul_pow, h s hs hs1, one_mul] at h2
    · exact h t ht h1
  have hn : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hc : (chiO ℚ Ω l c.O (galEmb ℚ K Ω t) : c.O) = ((1 + l : ℕ) : c.O) := by
    have : cycZ ℚ Ω l (galEmb ℚ K Ω t) = hu.unit := htu
    rw [chiO, MonoidHom.comp_apply, this]
    simp
  have h3 : ((D.Ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : c.Oˣ) : c.O) = ((1 + l : ℕ) : c.O) ^ (e * Nat.card (ZMod N)ˣ) := by
    rw [Dat.Ψ, Chr.Psi, MonoidHom.mul_apply, mul_pow, hn, mul_one, zpow_natCast, MonoidHom.pow_apply, ← pow_mul,
      Units.val_pow_eq_pow_val, hc]
  have h4 : ((D.ΨQ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ) := by
    have := congrArg (algebraMap c.O (PadicAlgCl l)) h3
    rw [map_pow, map_natCast] at this
    rw [← this, Dat.ΨQ, MonoidHom.comp_apply, ← map_pow]
    rfl
  have h5 : ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by
    rw [pow_mul, ← h4, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ht1, one_pow, Units.val_one]
  have h6 : (1 + l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by exact_mod_cast h5
  have he := D.gd.e_pos
  have hN : 0 < Nat.card (ZMod N)ˣ := Nat.card_pos
  rcases Nat.pow_eq_one.1 h6 with h7 | h7
  · exact hl.ne_zero (by omega)
  · exact (mul_ne_zero (mul_ne_zero (by omega) hN.ne') hm) h7

theorem UpperTheory.V.U3.typeI_irr_cyc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      TypeI D.η r → Af.IsIrr ((D.rhoK r h.mult).comp (cycBar K Ω l).ker.subtype) := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hg r h hI
  have hirr : MatIrr ⊤ fun g => (D.rhoK r h.mult g : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
    intro W hW
    refine hI W fun g hg v hv => ?_
    rw [D.η_ker, ← range_galEmb] at hg
    obtain ⟨s, rfl⟩ := hg
    exact hW s trivial v hv
  have key : MatIrr (cycBar K Ω l).ker fun g => (D.rhoK r h.mult g : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
    by_contra hred
    obtain ⟨φ, hφ1, hker, -, M, hM⟩ := exists_selfTwist (D.rhoK r h.mult) (cycBar K Ω l).ker
      (fun a b => by simp [MonoidHom.mem_ker, mul_comm (cycBar K Ω l a)]) hirr hred
    obtain ⟨A, hA⟩ := (Chr.placesQ Ω).1 l Fact.out
    refine hφ1 (MonoidHom.ext (twist_triv D A hA φ hker 3 (by norm_num) fun s hs h1 => ?_))
    have hch := (pt_inertia_above hC D hg h A hA).1 _ hs
    have htr : (D.rhoK r h.mult s : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)).trace =
        (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, ← hch]
      rfl
    have h2 := congrArg (fun X => (X * ((M⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).trace)
      (hM s trivial)
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul] at h2
    rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, htr,
      smul_eq_mul] at h2
    have h3 : (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace = 0 := by
      by_contra h0
      exact h1 (Units.ext (mul_right_cancel₀ h0 (h2.trans (one_mul _).symm)))
    rw [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three] at h3
    generalize D.ΨQ (galEmb ℚ K Ω s) = a at h3 ⊢
    have h4 : (a : PadicAlgCl l) + 1 + (a : PadicAlgCl l)⁻¹ = 0 := by simpa [wt1] using h3
    have ha : (a : PadicAlgCl l) * (a : PadicAlgCl l)⁻¹ = 1 := mul_inv_cancel₀ a.ne_zero
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination (a : PadicAlgCl l) * (a - 1) * h4 - ((a : PadicAlgCl l) - 1) * ha
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => key W fun g hg v hv => hW ⟨g, hg⟩ v hv⟩
