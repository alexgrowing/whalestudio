import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgTwist

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private noncomputable def UpperTheory.V.Fr.lauT (K : Type) [CommRing K] : Multiplicative ℤ →* (AddMonoidAlgebra K ℤ)ˣ :=
  (AddMonoidAlgebra.of K ℤ).toHomUnits

private theorem UpperTheory.V.Fr.lauT_zpow (K : Type) [CommRing K] (m : ℤ) :
    ((lauT K (Multiplicative.ofAdd 1) ^ m : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) =
      AddMonoidAlgebra.single m 1 := by
  rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  rfl

theorem UpperTheory.V.Fr.alg_lau :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∃ ρD : NRep F n (lauSub (ρ.part C)), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) ∧ (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc
  obtain ⟨χ, -, hχ⟩ := hc.psi
  obtain ⟨ρ', hr, hψ⟩ := alg_twist (lauT K (Multiplicative.ofAdd 1))
    (NRep.map (AddMonoidAlgebra.singleZeroRingHom : K →+* AddMonoidAlgebra K ℤ) ρ)
  have hr' : ∀ g i j, ρ'.r g i j = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) := by
    intro g i j
    rw [hr, lauT_zpow, NRep.map_r]
    simp [AddMonoidAlgebra.single_mul_single]
  have hψ' : ∀ v i g, ((ρ'.ψ v i g : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) =
      AddMonoidAlgebra.single 0 (ρ.ψ v i g : K) := by
    intro v i g
    rw [hψ]
    rfl
  have h1 : ∀ g i j, ρ'.r g i j ∈ lauSub (ρ.part C) := by
    intro g i j
    rw [hr']
    exact single_mem_lauSub _ (NRep.r_mem_part C ρ g i j)
  have h2 : ∀ v i g, ((ρ'.ψ v i g : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) ∈
      lauSub (ρ.part C) := by
    intro v i g
    rw [hψ']
    apply single_mem_lauSub
    rw [← hχ, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  exact ⟨NRep.restrict ρ' (lauSub (ρ.part C)) h1 h2, fun g i j => hr' g i j,
    fun v i g => hψ' v i g⟩
