import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

open GroundTheory.PAdicHodge GroundTheory.PAdicHodge.EigenChar

theorem cycloChar_inertia_image_infinite : ∀ {l : ℕ} [Fact l.Prime],
    (∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x) →
    ∀ (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
      ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite := by
  intro l _ h L _
  let H : Subgroup Gal(Om l/↥L) :=
    { carrier := {σ | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}
      mul_mem' := by
        intro a b ha hb w hw
        show a (b w) = w
        rw [hb w hw, ha w hw]
      one_mem' := by
        intro w _
        rfl
      inv_mem' := by
        intro a ha w hw
        have haw : a w = w := ha w hw
        calc a⁻¹ w = a⁻¹ (a w) := by rw [haw]
          _ = w := by simp [AlgEquiv.aut_inv] }
  intro hfin
  obtain ⟨M, hM⟩ : ∃ M : Subgroup ℤ_[l]ˣ, M = H.map (GroundTheory.PAdicHodge.cycloChar L) := ⟨_, rfl⟩
  have hMfin : Finite M := by
    have hs : (M : Set ℤ_[l]ˣ).Finite := by
      rw [hM, Subgroup.coe_map]
      exact hfin
    exact hs.to_subtype
  obtain ⟨n, hnM⟩ : ∃ n : ℕ, n = Nat.card M := ⟨_, rfl⟩
  have hn : 0 < n := by
    rw [hnM]
    exact Nat.card_pos
  have hpow : ∀ σ ∈ H, (GroundTheory.PAdicHodge.cycloChar L σ) ^ n = 1 := by
    intro σ hσ
    have hmem : GroundTheory.PAdicHodge.cycloChar L σ ∈ M := by
      rw [hM]
      exact Subgroup.mem_map_of_mem _ hσ
    have h1 : (⟨GroundTheory.PAdicHodge.cycloChar L σ, hmem⟩ : M) ^ n = 1 := by
      rw [hnM]
      exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hroots : ∀ σ : Gal(Om l/↥L), GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → σ ∈ H := by
    intro σ hσ
    have hfix := (GroundTheory.LocalField.unramifiedDegree_eq_one_iff σ).mp hσ
    have hS : ∀ y ∈ GroundTheory.PAdicHodge.primeToPRoots l, σ y = y := by
      rintro y ⟨m, hm0, hmcop, hym⟩
      apply hfix
      have hcop : Nat.Coprime l m := Nat.Coprime.symm hmcop
      have hmod : l ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
      have hle : 1 ≤ l ^ Nat.totient m := Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)
      have hdvd : m ∣ l ^ Nat.totient m - 1 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      obtain ⟨c, hc⟩ := hdvd
      refine GroundTheory.PAdicHodge.EigenWitt.mem_unramifiedRoots_of_pow_eq_one (L := L)
        (Nat.totient_pos.2 hm0) ?_
      rw [hc, pow_mul, hym, one_pow]
    have hσ' : (σ.restrictScalars ℚ_[l]) ∈
        (IntermediateField.adjoin ℚ_[l] (GroundTheory.PAdicHodge.primeToPRoots l)).fixingSubgroup :=
      GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff.mpr (fun y hy => hS y hy)
    show ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w
    intro w hw
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ' w hw
  let ψ : Gal(Om l/↥L) →* ℤ_[l]ˣ := (powMonoidHom n).comp (GroundTheory.PAdicHodge.cycloChar L)
  have hψc : Continuous ψ := (GroundTheory.PAdicHodge.continuous_cycloChar L).pow n
  have hψu : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → ψ σ = 1 := by
    intro σ hσ
    exact hpow σ (hroots σ hσ)
  obtain ⟨f, hf, x, hx0, hx⟩ := h L ψ hψc hψu
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -((n * f : ℕ) : ℤ) := ⟨_, rfl⟩
  have hj0 : j ≠ 0 := by
    rw [hj, neg_ne_zero, Nat.cast_ne_zero]
    exact Nat.mul_ne_zero hn.ne' hf.ne'
  have hinv : x ∈ (GroundTheory.PAdicHodge.cpTwistRep L j).invariants := by
    change ∀ σ, (GroundTheory.PAdicHodge.cpTwistRep L j σ) x = x
    intro σ
    have key : (((GroundTheory.PAdicHodge.cycloChar L σ ^ j : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
        ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ^ f = 1 := by
      have hψσ : ψ σ = GroundTheory.PAdicHodge.cycloChar L σ ^ n := rfl
      have hu : GroundTheory.PAdicHodge.cycloChar L σ ^ j * (GroundTheory.PAdicHodge.cycloChar L σ ^ n) ^ f = 1 := by
        rw [hj, ← pow_mul, zpow_neg, zpow_natCast, inv_mul_cancel]
      rw [hψσ, ← PadicInt.coe_pow, ← PadicInt.coe_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hu]
      simp
    rw [GroundTheory.PAdicHodge.cpTwistRep_apply, hx σ, GroundTheory.PAdicHodge.twistScalar, ← mul_assoc, ← map_mul, key,
      map_one, one_mul]
  rw [GroundTheory.PAdicHodge.cpTwistRep_invariants_eq_bot L hj0] at hinv
  exact hx0 ((Submodule.mem_bot _).mp hinv)

end GlobalTheory.CompanionTheory.LTPer
