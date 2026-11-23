import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.LocalUnram

open GroundTheory.LocalField.Abstract in

theorem continuous_of_additive_of_frobenius_eq_one :
    ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (χ : Gal(Ω/K) → ZMod n),
      (∀ g h, χ (g * h) = χ g + χ h) →
      (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → Continuous χ := by
  intro K Ω _ _ _ _ _ _ _ n _ χ hadd h1
  obtain ⟨hcont, hsurj, -⟩ := unramifiedDegree_spec (K := K) (Ω := Ω)
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, NeZero.pos n⟩, rfl⟩
  have hone : χ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hinv : ∀ g, χ g⁻¹ = -χ g := fun g => by
    have h := hadd g⁻¹ g
    rw [inv_mul_cancel, hone] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hpow : ∀ (g : Gal(Ω/K)) (k : ℕ), χ (g ^ k) = k • χ g := fun g k => by
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  obtain ⟨f, hf⟩ := hsurj (Multiplicative.ofAdd 1)
  have hχf : χ f = 1 := h1 f hf
  have hker : ∀ g, unramifiedDegree K Ω g = 1 → χ g = 0 := fun g hg => by
    have h := h1 (g * f) (by rw [map_mul, hg, one_mul, hf])
    rw [hadd, hχf] at h
    exact add_eq_right.mp h
  have key : ∀ g, χ g = ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω g)) := by
    intro g
    set x := Multiplicative.toAdd (unramifiedDegree K Ω g) with hx
    set k : ℕ := (ProfiniteInteger.proj N x).val with hk
    have hkc : ((k : ℕ) : ZMod (N : ℕ)) = ProfiniteInteger.proj N x := ZMod.natCast_zmod_val _
    have hz : ProfiniteInteger.proj N (x - (k : ProfiniteInteger)) = 0 := by
      rw [map_sub, map_natCast, hkc, sub_self]
    obtain ⟨w, hw⟩ := ProfiniteInteger.exists_eq_nsmul_of_proj_eq_zero hz
    obtain ⟨t, ht⟩ := hsurj (Multiplicative.ofAdd w)
    have hdeg : unramifiedDegree K Ω (g * (f ^ k)⁻¹ * (t ^ (N : ℕ))⁻¹) = 1 := by
      simp only [_root_.map_mul, _root_.map_inv, _root_.map_pow, hf, ht]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_mul, toAdd_inv, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd,
        toAdd_one, ← hx, ← hw, nsmul_eq_mul, mul_one]
      ring
    have h0 := hker _ hdeg
    rw [hadd, hadd, hinv, hinv, hpow, hpow, hχf] at h0
    have hN : (N : ℕ) • χ t = 0 := by simp
    rw [hN, neg_zero, add_zero, nsmul_eq_mul, mul_one, hkc] at h0
    exact add_neg_eq_zero.mp h0
  have hχ : χ = fun g => ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω g)) :=
    funext key
  rw [hχ]
  exact (ProfiniteInteger.continuous_proj N).comp (continuous_toAdd.comp hcont)

end GlobalTheory.CompanionTheory.LocalUnram
