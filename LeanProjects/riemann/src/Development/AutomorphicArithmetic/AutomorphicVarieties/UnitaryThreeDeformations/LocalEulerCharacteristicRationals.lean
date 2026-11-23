import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

private theorem ef_eq_one (v : Pl) : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  haveI : Fintype ((v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (v.asIdeal.under ℤ) (NumberField.RingOfIntegers ℚ)
  rw [NumberField.RingOfIntegers.rank, Module.finrank_self] at hsum
  have hmem : v.asIdeal ∈ (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) :=
    ⟨inferInstance, ⟨rfl⟩⟩
  have hle := Finset.single_le_sum
    (f := fun q : (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨v.asIdeal, hmem⟩ : (v.asIdeal.under ℤ).primesOver _))
  have he := Ideal.ramificationIdx_pos v.asIdeal ℤ
  have hf := Ideal.inertiaDeg_pos v.asIdeal ℤ
  simp only at hle
  rw [hsum] at hle
  have := Nat.mul_pos he hf
  omega

theorem UpperTheory.local_euler_characteristic_rationals :
    LocalFiniteness → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : Pl) (ρ : Representation k (Dec (F := ℚ) A) M),
        Formalism.ConjugateSelfDual.IsPlaceOver A v → ContAction ρ →
        Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
          (((l : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M) ∧
          (((l : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ)) := by
  intro hFin hEC Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ A v ρ hv hc
  classical
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  let φ : ZMod (l ^ 1) →+* k := ZMod.castHom (dvd_refl _) k
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M φ
  haveI : LinearMap.CompatibleSMul M M (ZMod (l ^ 1)) k := ⟨fun f c x => f.map_smul (φ c) x⟩
  let ρ' : Representation (ZMod (l ^ 1)) (Dec (F := ℚ) A) M :=
    { toFun := fun g => (ρ g).restrictScalars (ZMod (l ^ 1))
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }
  have hc' : ContAction ρ' := hc
  have hF := hFin ℚ Ω l 1 M A ρ' v one_pos hv hc'
  have hE := hEC ℚ Ω l 1 M A ρ' v one_pos hv hc'
  have e1 : H1 ρ' ≃ H1 ρ := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ' ≃ H2 ρ := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e0 : ↥(H0 ρ') ≃ ↥(H0 ρ) := Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  haveI := hF.2.1
  haveI := hF.2.2.1
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2
  haveI : Module.Finite k (H1 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k (H2 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k M := Module.Finite.of_finite
  haveI : Module.Finite k ↥(H0 ρ) := Module.Finite.of_finite
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have inj := Nat.pow_right_injective (show 2 ≤ Nat.card k by omega)
  have c1 : Nat.card (H1 ρ') = Nat.card k ^ finrank k (H1 ρ) := by
    rw [Nat.card_congr e1]; exact Module.natCard_eq_pow_finrank
  have c2 : Nat.card (H2 ρ') = Nat.card k ^ finrank k (H2 ρ) := by
    rw [Nat.card_congr e2]; exact Module.natCard_eq_pow_finrank
  have c0 : Nat.card ↥(H0 ρ') = Nat.card k ^ finrank k ↥(H0 ρ) := by
    rw [Nat.card_congr e0]; exact Module.natCard_eq_pow_finrank
  have cM : Nat.card M = Nat.card k ^ finrank k M := Module.natCard_eq_pow_finrank
  have hd : locDeg v = 1 := ef_eq_one v
  refine ⟨inferInstance, inferInstance, fun hl => ?_, fun hl => ?_⟩
  · have h := hE.1 hl
    rw [c1, c0, c2, cM, hd, pow_one, ← pow_add, ← pow_add] at h
    exact inj h
  · have h := hE.2 hl
    rw [c1, c0, c2, ← pow_add] at h
    exact inj h
