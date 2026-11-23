import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.locOnto
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RootEqOfSubMem

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

section
open Formalism.HC.Der Formalism.TwoAdicCyclotomicDecomposition

private theorem stab_iff (N : ℕ) [NeZero N] (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime]
    [Q.LiesOver (span {(l : ℤ)})] (u : (ZMod N)ˣ) :
    tauN N u ∈ MulAction.stabilizer _ Q ↔ ∃ k : ℕ, (u : ZMod N).val ≡ l ^ k [MOD ordCompl[l] N] := by
  set M := ordCompl[l] N with hM
  have hMN : M ∣ N := Nat.ordCompl_dvd N l
  have hlM : l.Coprime M := Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)
  obtain ⟨u0, hu0⟩ := exists_unit_modEq (N := N) hMN l hlM
  have hF : IsArithFrobAt ℤ (tauN N u0) Q := tauN_frob N l Q u0 hu0
  have hu0' : ((ZMod.unitsMap hMN u0 : (ZMod M)ˣ) : ZMod M) = (l : ZMod M) :=
    (val_modEq_iff hMN u0 l).mp hu0
  constructor
  · intro hs
    obtain ⟨k, ρ, hρ, hρeq⟩ := Decomp.stab_eq_inertia_mul l Q (tauN N u0) (tauN N u) hF hs
    obtain ⟨w, rfl⟩ := (tauN N).surjective ρ
    refine ⟨k, ?_⟩
    have hw1 : ZMod.unitsMap hMN w = 1 :=
      (val_modEq_one_iff hMN w).mp ((tauN_inertia_iff N l Q w).mp hρ)
    have huw : u = w * u0 ^ k := (tauN N).injective (by rw [map_mul, map_pow]; exact hρeq)
    rw [val_modEq_iff hMN, huw, map_mul, map_pow, hw1, one_mul, Units.val_pow_eq_pow_val, hu0',
      Nat.cast_pow]
  · rintro ⟨k, hk⟩
    have hw1 : ZMod.unitsMap hMN (u * (u0 ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one]
      apply Units.ext
      rw [(val_modEq_iff hMN u _).mp hk, Units.val_pow_eq_pow_val, hu0', Nat.cast_pow]
    have hwin := (tauN_inertia_iff N l Q (u * (u0 ^ k)⁻¹)).mpr ((val_modEq_one_iff hMN _).mpr hw1)
    have hwst := Decomp.mem_stab_of _ Q (smul_mem_of_inertia _ Q hwin)
    have hFst := IsArithFrobAt.mem_stabilizer hF
    have hu : u = (u * (u0 ^ k)⁻¹) * u0 ^ k := by rw [inv_mul_cancel_right]
    rw [hu, map_mul, map_pow]
    exact Subgroup.mul_mem _ hwst (Subgroup.pow_mem _ hFst k)

private theorem act_of (N : ℕ) [NeZero N] {K : Type*} [Field K] (J : Cond.Cyc N →+* K) (σ : K →+* K) (u : (ZMod N)ˣ)
    (h : ∀ x, σ (J x) = J (tauN N u x)) (x : K) (hx : x ^ N = 1) : σ x = x ^ (u : ZMod N).val := by
  have hζ := (zO_prim N).map_of_injective (f := algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N))
    (FaithfulSMul.algebraMap_injective _ _)
  have hJ := hζ.map_of_injective J.injective
  obtain ⟨i, -, rfl⟩ := hJ.eq_pow_of_pow_eq_one hx
  have hg : IsCyclotomicExtension.Rat.galEquivZMod N (Cond.Cyc N) (tauN N u) = u :=
    MulEquiv.apply_symm_apply _ _
  have hτ : tauN N u (algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N) (zO N)) =
      (algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N) (zO N)) ^ (u : ZMod N).val := by
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (Cond.Cyc N) (tauN N u) hζ.pow_eq_one,
      hg]
  rw [map_pow, h, hτ, map_pow]
  ring

end

theorem UpperTheory.HF.loc_roots :
    ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → (∀ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∃ (u : (ZMod M)ˣ) (j : ℕ), (u : ZMod M).val ≡ l ^ j [MOD ordCompl[l] M] ∧ ∀ x : PadicAlgCl l, x ^ M = 1 → σ x = x ^ (u : ZMod M).val) ∧ ∀ (u : (ZMod M)ˣ) (j : ℕ), (u : ZMod M).val ≡ l ^ j [MOD ordCompl[l] M] → ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ x : PadicAlgCl l, x ^ M = 1 → σ x = x ^ (u : ZMod M).val := by
  intro l _ M hM
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI := Formalism.HC.Der.cyc_isGalois M
  let J : Cond.Cyc M →+* PadicAlgCl l := (IsAlgClosed.lift : Cond.Cyc M →ₐ[ℚ] PadicAlgCl l).toRingHom
  obtain ⟨P, hPp, hPlo, -, hstab, hsurj, -⟩ := UpperTheory.HF.loc_onto l (Cond.Cyc M) J
  haveI := hPp
  haveI := hPlo
  constructor
  · intro σ
    obtain ⟨τ, hτ⟩ := hsurj σ
    obtain ⟨u, rfl⟩ := (Formalism.HC.Der.tauN M).surjective τ
    have hst : Formalism.HC.Der.tauN M u ∈ MulAction.stabilizer _ P := (hstab _).mpr ⟨σ, hτ⟩
    obtain ⟨k, hk⟩ := (stab_iff M l P u).mp hst
    exact ⟨u, k, hk, fun x hx => act_of M J (σ : PadicAlgCl l →+* PadicAlgCl l) u hτ x hx⟩
  · intro u j hj
    obtain ⟨σ, hσ⟩ := (hstab (Formalism.HC.Der.tauN M u)).mp ((stab_iff M l P u).mpr ⟨j, hj⟩)
    exact ⟨σ, fun x hx => act_of M J (σ : PadicAlgCl l →+* PadicAlgCl l) u hσ x hx⟩
