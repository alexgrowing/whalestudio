import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LiftInt

section Val

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

def ltIdeal : Ideal v.integer where
  carrier := {x | v (x : K) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul] at *
    calc v (c : K) * v (x : K) ≤ 1 * v (x : K) := by gcongr; exact c.2
      _ < 1 := by rwa [one_mul]

theorem det_sub_lt {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1)
    (hB : ∀ i j, v (B i j) ≤ 1) (h : ∀ i j, v (A i j - B i j) < 1) : v (A.det - B.det) < 1 := by
  let A0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  let B0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨B i j, hB i j⟩
  have eA : A0.map v.integer.subtype = A := by ext i j; rfl
  have eB : B0.map v.integer.subtype = B := by ext i j; rfl
  have hm : A0.map (Ideal.Quotient.mk (ltIdeal v)) = B0.map (Ideal.Quotient.mk (ltIdeal v)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq]
    exact h i j
  have hd := congrArg Matrix.det hm
  have d1 : Ideal.Quotient.mk (ltIdeal v) A0.det = (A0.map (Ideal.Quotient.mk (ltIdeal v))).det :=
    RingHom.map_det _ _
  have d2 : Ideal.Quotient.mk (ltIdeal v) B0.det = (B0.map (Ideal.Quotient.mk (ltIdeal v))).det :=
    RingHom.map_det _ _
  rw [← d1, ← d2, Ideal.Quotient.eq] at hd
  have e1 : v.integer.subtype A0.det = (A0.map v.integer.subtype).det := RingHom.map_det _ _
  have e2 : v.integer.subtype B0.det = (B0.map v.integer.subtype).det := RingHom.map_det _ _
  rw [eA] at e1
  rw [eB] at e2
  have : v ((A0.det - B0.det : v.integer) : K) < 1 := hd
  rw [← e1, ← e2, ← map_sub]
  exact this

theorem adjugate_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1) :
    ∀ i j, v (A.adjugate i j) ≤ 1 := by
  let A0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  have eA : A0.map v.integer.subtype = A := by ext i j; rfl
  have e : A0.adjugate.map v.integer.subtype = (A0.map v.integer.subtype).adjugate :=
    RingHom.map_adjugate _ _
  rw [eA] at e
  intro i j
  rw [← e]
  exact (A0.adjugate i j).2

end Val

section Place

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem intCast_le_one (s : SplitPlace L) (m : ℤ) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) ≤ 1 := by
  have h := s.split_le_one (m : 𝓞 L)
  simpa using h

theorem natCast_lt_one (s : SplitPlace L) (g : ℕ) (hg : ((g : 𝓞 L) ∈ s.w.asIdeal)) :
    Valued.v ((g : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
  have h : Valued.v (s.i ((g : 𝓞 L) : L)) < 1 := hg
  simpa using h

theorem intCast_eq_one (s : SplitPlace L) (g : ℕ) (hp : g.Prime) (hg : ((g : 𝓞 L) ∈ s.w.asIdeal)) (m : ℤ)
    (hm : ¬ (g : ℤ) ∣ m) : Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  have hcop : IsCoprime (g : ℤ) m := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : ¬ g ∣ m.natAbs := fun h => hm (Int.natCast_dvd.mpr h)
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 h1
  obtain ⟨a, b, hab⟩ := hcop
  refine le_antisymm (intCast_le_one s m) (not_lt.mp fun hlt => ?_)
  have e : ((a : s.v.adicCompletion (maximalRealSubfield L))) * (g : s.v.adicCompletion (maximalRealSubfield L)) +
      (b : s.v.adicCompletion (maximalRealSubfield L)) * (m : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : s.v.adicCompletion (maximalRealSubfield L))) hab
  have h1 : Valued.v ((a : s.v.adicCompletion (maximalRealSubfield L)) * (g : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v ((g : s.v.adicCompletion (maximalRealSubfield L))) := by gcongr; exact intCast_le_one s a
      _ < 1 := by rw [one_mul]; exact natCast_lt_one s g hg
  have h2 : Valued.v ((b : s.v.adicCompletion (maximalRealSubfield L)) * (m : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) := by gcongr; exact intCast_le_one s b
      _ < 1 := by rwa [one_mul]
  have h3 := lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h1 h2)
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

end Place

theorem mem_Umax_of_isLift : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ((g : 𝓞 L) ∈ s.w.asIdeal) → ∀ (x : Formalism.AUTREP.GAf L n) (γ : GL (Fin n) (ZMod g)), GlobalTheory.LabPin.IsLift s x γ → x ∈ ReciprocityTheory.Aut.Umax L n := by
  intro L _ _ _ n s g hp hg x γ hx
  obtain ⟨htriv, hred⟩ := hx
  haveI : Fact g.Prime := ⟨hp⟩
  set A : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
      Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) with hAdef
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => (((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ)
  let B : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    M.map (Int.castRingHom _)
  have hB : ∀ i j, Valued.v (B i j) ≤ 1 := fun i j => intCast_le_one s _
  have hAB : ∀ i j, Valued.v (A i j - B i j) < 1 := by
    intro i j
    have := hred i j
    have e : B i j = ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) :
        s.v.adicCompletion (maximalRealSubfield L)) := by
      change (((M i j : ℤ)) : s.v.adicCompletion (maximalRealSubfield L)) = _
      exact Int.cast_natCast _
    rw [e]
    exact this
  have hA : ∀ i j, Valued.v (A i j) ≤ 1 := by
    intro i j
    have e : A i j = (A i j - B i j) + B i j := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (hAB i j).le (hB i j))
  have hdetB : B.det = ((M.det : ℤ) : s.v.adicCompletion (maximalRealSubfield L)) :=
    (RingHom.map_det (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) M).symm
  have hMγ : M.map (Int.castRingHom (ZMod g)) = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext i j
    change (((M i j : ℤ)) : ZMod g) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdetM : ((M.det : ℤ) : ZMod g) = (γ : Matrix (Fin n) (Fin n) (ZMod g)).det := by
    rw [← hMγ]
    exact RingHom.map_det (Int.castRingHom (ZMod g)) M
  have hne : ¬ (g : ℤ) ∣ M.det := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hdetM]
    exact (Matrix.isUnits_det_units γ).ne_zero
  have hvB : Valued.v B.det = 1 := by rw [hdetB]; exact intCast_eq_one s g hp hg _ hne
  have hvA : Valued.v A.det = 1 := by
    have hd := det_sub_lt Valued.v A B hA hB hAB
    have e : A.det = (A.det - B.det) + B.det := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hvB]; exact hd), hvB]
  refine GlobalTheory.TSetFin.mem_Umax_of_loc s x htriv hA ?_
  intro i j
  rw [map_inv, Matrix.coe_units_inv, ← hAdef, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul,
    Ring.inverse_eq_inv', map_inv₀, hvA, inv_one, one_mul]
  exact adjugate_le_one Valued.v A hA i j

end GlobalTheory.LiftInt
