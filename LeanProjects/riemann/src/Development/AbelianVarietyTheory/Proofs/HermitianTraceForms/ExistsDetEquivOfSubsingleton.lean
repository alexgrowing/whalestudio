import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemHomogIffIsHomogeneous

open TensorProduct Module Function

namespace GlobalTheory
namespace TopExt

variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]

variable (R H) in

noncomputable def wedgeMul (a b : ℕ) : (⋀[R]^a H) ⊗[R] (⋀[R]^b H) →ₗ[R] ⋀[R]^(a + b) H :=
  LinearMap.codRestrict _
    (LinearMap.mul' R (ExteriorAlgebra R H) ∘ₗ
      TensorProduct.map (⋀[R]^a H).subtype (⋀[R]^b H).subtype) fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul x y =>
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        ExteriorAlgebra.exteriorPower, pow_add]
      exact Submodule.mul_mem_mul x.2 y.2

@[simp] theorem coe_wedgeMul_tmul {a b : ℕ} (x : ⋀[R]^a H) (y : ⋀[R]^b H) :
    (wedgeMul R H a b (x ⊗ₜ y) : ExteriorAlgebra R H) = (x : ExteriorAlgebra R H) * y := rfl

theorem wedgeMul_ιMulti {a b : ℕ} (x : Fin a → H) (y : Fin b → H) :
    wedgeMul R H a b (exteriorPower.ιMulti R a x ⊗ₜ exteriorPower.ιMulti R b y) =
      exteriorPower.ιMulti R (a + b) (Fin.append x y) :=
  Subtype.ext (by simp [ExteriorAlgebra.ιMulti_mul_ιMulti])

theorem coe_map (n : ℕ) (i : F →ₗ[R] H) (x : ⋀[R]^n F) :
    (exteriorPower.map n i x : ExteriorAlgebra R H) =
      ExteriorAlgebra.map i (x : ExteriorAlgebra R F) := by
  have : (⋀[R]^n H).subtype ∘ₗ exteriorPower.map n i =
      (ExteriorAlgebra.map i).toLinearMap ∘ₗ (⋀[R]^n F).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp
  exact LinearMap.congr_fun this x

noncomputable def wedgeMap (i : F →ₗ[R] H) (s : L →ₗ[R] H) (a b : ℕ) :
    (⋀[R]^a F) ⊗[R] (⋀[R]^b L) →ₗ[R] ⋀[R]^(a + b) H :=
  wedgeMul R H a b ∘ₗ TensorProduct.map (exteriorPower.map a i) (exteriorPower.map b s)

theorem coe_wedgeMap_tmul (i : F →ₗ[R] H) (s : L →ₗ[R] H) {a b : ℕ} (x : ⋀[R]^a F)
    (y : ⋀[R]^b L) : (wedgeMap i s a b (x ⊗ₜ y) : ExteriorAlgebra R H) =
      ExteriorAlgebra.map i (x : ExteriorAlgebra R F) *
        ExteriorAlgebra.map s (y : ExteriorAlgebra R L) := by
  simp [wedgeMap, coe_map]

theorem range_pow_eq_map (i : F →ₗ[R] H) (n : ℕ) :
    LinearMap.range (ExteriorAlgebra.ι R ∘ₗ i) ^ n =
      (⋀[R]^n F).map (ExteriorAlgebra.map i).toLinearMap := by
  rw [ExteriorAlgebra.exteriorPower, Submodule.map_pow, ← LinearMap.range_comp,
    ExteriorAlgebra.map_comp_ι]

theorem mul_ιMulti_congr (i : F →ₗ[R] H) {b : ℕ} (x : ExteriorAlgebra R H)
    (hx : ∀ f, x * ExteriorAlgebra.ι R (i f) = 0) (h h' : Fin b → H)
    (hh : ∀ k, h k - h' k ∈ LinearMap.range i) :
    x * ExteriorAlgebra.ιMulti R b h = x * ExteriorAlgebra.ιMulti R b h' := by
  induction b generalizing x with
  | zero => simp
  | succ b ih =>
    obtain ⟨f, hf⟩ := hh 0
    have h0 : x * ExteriorAlgebra.ι R (h 0) = x * ExteriorAlgebra.ι R (h' 0) := by
      rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← hf, hx]
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc,
      ← mul_assoc, h0]
    refine ih _ (fun g => ?_) _ _ fun k => hh k.succ
    rw [mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (h' 0) (i g)),
      mul_neg, ← mul_assoc, hx, zero_mul, neg_zero]

theorem ιMulti_eq_zero_of_mem_span {r n : ℕ} (hn : r < n) (v : Fin r → F) (w : Fin n → F)
    (hw : ∀ k, w k ∈ Submodule.span R (Set.range v)) : exteriorPower.ιMulti R n w = 0 := by
  simp only [Submodule.mem_span_range_iff_exists_fun] at hw
  choose u hu using hw
  have : IsEmpty (Set.powersetCard (Fin r) n) := ⟨fun s => by
    have h1 := s.1.card_le_univ
    have h2 : s.1.card = n := s.2
    simp only [Fintype.card_fin] at h1
    omega⟩
  have h0 : exteriorPower.ιMulti R n u = 0 :=
    ((Pi.basisFun R (Fin r)).exteriorPower n).ext_elem fun s => this.elim s
  have hw : w = Fintype.linearCombination R v ∘ u := funext fun k => (hu k).symm
  rw [hw, ← exteriorPower.map_apply_ιMulti, h0, map_zero]

section Exact

variable {i : F →ₗ[R] H} {π : H →ₗ[R] L}

end Exact

section Dual

theorem pairingDual_map_dualMap (φ : F →ₗ[R] H) (n : ℕ) (ξ : ⋀[R]^n (Dual R H)) :
    exteriorPower.pairingDual R F n (exteriorPower.map n φ.dualMap ξ) =
      (exteriorPower.map n φ).dualMap (exteriorPower.pairingDual R H n ξ) := by
  have : exteriorPower.pairingDual R F n ∘ₗ exteriorPower.map n φ.dualMap =
      (exteriorPower.map n φ).dualMap ∘ₗ exteriorPower.pairingDual R H n := by
    apply exteriorPower.linearMap_ext
    refine AlternatingMap.ext fun f => ?_
    apply exteriorPower.linearMap_ext
    refine AlternatingMap.ext fun v => ?_
    simp
  exact LinearMap.congr_fun this ξ

theorem pairingDual_bijective_of_basis {κ : Type*} [Finite κ] [LinearOrder κ] (b : Basis κ R F)
    (n : ℕ) : Bijective (exteriorPower.pairingDual R F n) := by
  classical
  have : exteriorPower.pairingDual R F n =
      ((b.dualBasis.exteriorPower n).equiv (b.exteriorPower n).dualBasis (Equiv.refl _)).toLinearMap := by
    refine (b.dualBasis.exteriorPower n).ext fun s => ?_
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, Basis.coe_dualBasis,
      exteriorPower.basis_coord, exteriorPower.basis_apply, Basis.coe_dualBasis]
    rfl
  rw [this]
  exact LinearEquiv.bijective _

variable (R F) in

theorem pairingDual_bijective [Module.Finite R F] [Module.Projective R F] (n : ℕ) :
    Bijective (exteriorPower.pairingDual R F n) := by
  obtain ⟨k, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R F
  have hb := pairingDual_bijective_of_basis (Pi.basisFun R (Fin k)) n
  have h₁ : ∀ ξ : ⋀[R]^n (Dual R F),
      exteriorPower.map n g.dualMap (exteriorPower.map n f.dualMap ξ) = ξ := fun ξ => by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, LinearMap.dualMap_comp_dualMap, hfg,
      LinearMap.dualMap_id, exteriorPower.map_id, LinearMap.id_apply]
  have h₂ : ∀ ξ : Dual R (⋀[R]^n F),
      (exteriorPower.map n g).dualMap ((exteriorPower.map n f).dualMap ξ) = ξ := fun ξ => by
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← exteriorPower.map_comp, hfg,
      exteriorPower.map_id, LinearMap.dualMap_id, LinearMap.id_apply]
  constructor
  · intro x y hxy
    rw [← h₁ x, ← h₁ y]
    congr 1
    apply hb.1
    rw [pairingDual_map_dualMap, pairingDual_map_dualMap, hxy]
  · intro ξ
    obtain ⟨x, hx⟩ := hb.2 ((exteriorPower.map n f).dualMap ξ)
    exact ⟨exteriorPower.map n g.dualMap x, by rw [pairingDual_map_dualMap, hx, h₂]⟩

variable (R F) in

noncomputable def dualEquiv [Module.Finite R F] [Module.Projective R F] (n : ℕ) :
    (⋀[R]^n (Dual R F)) ≃ₗ[R] Dual R (⋀[R]^n F) :=
  LinearEquiv.ofBijective _ (pairingDual_bijective R F n)

@[simp] theorem dualEquiv_apply [Module.Finite R F] [Module.Projective R F] (n : ℕ)
    (ξ : ⋀[R]^n (Dual R F)) : dualEquiv R F n ξ = exteriorPower.pairingDual R F n ξ := rfl

variable (F) in

theorem rankAtStalk_dual [Module.Finite R F] [Module.Projective R F] (p : PrimeSpectrum R) :
    rankAtStalk (Dual R F) p = rankAtStalk F p := by
  let S := p.asIdeal.primeCompl
  have h₁ := LocalizedModule.isBaseChange S F
  have h₂ := LocalizedModule.isBaseChange S (Dual R F)
  have : Module.Free (Localization S) (LocalizedModule S F) :=
    Module.free_of_flat_of_isLocalRing
  have e := h₂.equiv.symm ≪≫ₗ (SymAlg.isBaseChange_dual h₁).equiv
  exact e.finrank_eq.trans (Module.finrank_linearMap_self _ _ _)

end Dual

end TopExt
end GlobalTheory
