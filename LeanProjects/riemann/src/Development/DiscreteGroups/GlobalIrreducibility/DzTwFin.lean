import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open Polynomial GlobalTheory.GLq GlobalTheory.SmGL CategoryTheory

namespace DiscreteGroups.sglob.DzTw

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

def twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) : FDRep ℂ (Gn g n) :=
  FDRep.of (twist τ.ρ (detChar (Fin n) χ₀))

theorem character_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (y : Gn g n) :
    (twFD τ χ₀).character y = ((χ₀ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * τ.character y := by
  change LinearMap.trace ℂ τ (((detChar (Fin n) χ₀ y : ℂˣ) : ℂ) • τ.ρ y) =
    ((χ₀ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * LinearMap.trace ℂ τ (τ.ρ y)
  rw [map_smul, smul_eq_mul, detChar_apply]

theorem simple_of_char {G : Type} [Group G] [Fintype G] {V W : FDRep ℂ G} (hV : Simple V)
    (h : ∀ x, W.character x * W.character x⁻¹ = V.character x * V.character x⁻¹) : Simple W := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hc' : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_pos.ne'
  have := invertibleOfNonzero hc
  have := invertibleOfNonzero hc'
  rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
  simpa only [h] using hV

theorem char_twFD_mul (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (x : Gn g n) :
    (twFD τ χ₀).character x * (twFD τ χ₀).character x⁻¹ = τ.character x * τ.character x⁻¹ := by
  have hu : ((χ₀ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * ((χ₀ (Matrix.GeneralLinearGroup.det x⁻¹) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Units.val_one]
  rw [character_twFD, character_twFD]
  calc _ = (((χ₀ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * ((χ₀ (Matrix.GeneralLinearGroup.det x⁻¹) : ℂˣ) : ℂ)) *
        (τ.character x * τ.character x⁻¹) := by ring
    _ = _ := by rw [hu, one_mul]

theorem det_eq_one_of_mem {N a : ℕ} {u : GL (Fin N) (ZMod g)}
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks N a)) : Matrix.GeneralLinearGroup.det u = 1 := by
  have hu' := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  have hmono : ∀ i j : Fin N, j < i → GlobalTheory.FiniteGL.twoBlocks N a j ≤ GlobalTheory.FiniteGL.twoBlocks N a i := by
    intro i j hij
    have : (j : ℕ) < i := hij
    simp only [GlobalTheory.FiniteGL.twoBlocks]
    split_ifs <;> omega
  have hT : (u : Matrix (Fin N) (Fin N) (ZMod g)).BlockTriangular id := by
    intro i j hij
    have h := hu' i j (hmono i j hij)
    have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h
  have hd : ∀ i, (u : Matrix (Fin N) (Fin N) (ZMod g)) i i = 1 := by
    intro i
    have h := hu' i i le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular hT]
  simp [hd]

theorem res_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) {a : ℕ} (ha : a < n) :
    res a (n - a) (twFD τ χ₀).character 1 1 = res a (n - a) τ.character 1 1 := by
  unfold res
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
      br a (n - a) (x : Mt g n) = ((1 : Gn g (n - a)) : Mt g (n - a))
  · rw [if_pos hx, if_pos hx, character_twFD,
      det_eq_one_of_mem ((GlobalTheory.SerSys.TameGen.mem_unipRadical_iff ha x).2 hx), map_one, Units.val_one, one_mul]
  · rw [if_neg hx, if_neg hx]

theorem isCusp_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (hτ : IsCusp τ.character) :
    IsCusp (twFD τ χ₀).character := by
  obtain ⟨hn, ⟨V, hV, hVc⟩, hres⟩ := hτ
  have hsτ : Simple τ := simple_of_char hV (fun x => by rw [hVc, hVc])
  refine ⟨hn, ⟨twFD τ χ₀, simple_of_char hsτ (fun x => char_twFD_mul τ χ₀ x), fun _ => rfl⟩, fun a h0 ha => ?_⟩
  rw [res_twFD τ χ₀ ha]
  exact hres a h0 ha

theorem det_eq_norm (K : Type) [Field K] [Algebra (ZMod g) K] (hK : Nat.card K = g ^ n) (hn : 0 < n) (y : Gn g n)
    (hy : Irreducible (y : Mt g n).charpoly) (z : Kˣ) (hz : aeval (z : K) (y : Mt g n).charpoly = 0) :
    Matrix.GeneralLinearGroup.det y = Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by omega))
  letI : Fintype K := Fintype.ofFinite K
  haveI : Module.Finite (ZMod g) K := by
    first
    | exact Module.finite_of_finite (ZMod g)
    | exact inferInstance
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 : Fintype.card K = Fintype.card (ZMod g) ^ Module.finrank (ZMod g) K := by
      first
      | exact Module.card_eq_pow_finrank
      | exact card_eq_pow_finrank
    rw [ZMod.card] at h1
    have h2 : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_right_injective hg (h1.symm.trans h2)
  have hmon : ((y : Mt g n).charpoly).Monic := Matrix.charpoly_monic _
  have hdeg : ((y : Mt g n).charpoly).natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmin : (y : Mt g n).charpoly = minpoly (ZMod g) (z : K) := minpoly.eq_of_irreducible_of_monic hy hz hmon
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  have hfr2 : Module.finrank (IntermediateField.adjoin (ZMod g) {(z : K)}) K = 1 := by
    have h3 := IntermediateField.adjoin.finrank hint
    have h4 := Module.finrank_mul_finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {(z : K)}) K
    rw [h3, ← hmin, hdeg, hfr] at h4
    exact Nat.eq_of_mul_eq_mul_left hn (h4.trans (mul_one n).symm)
  have hnorm : Algebra.norm (ZMod g) (z : K) = (-1) ^ n * ((y : Mt g n).charpoly).coeff 0 := by
    rw [Algebra.norm_eq_norm_adjoin (ZMod g) (z : K), hfr2, pow_one]
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen] at this
    rw [this, ← hmin, hdeg]
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
  exact hnorm.symm

theorem units_pow_card_pow (u : (ZMod g)ˣ) (j : ℕ) : u ^ g ^ j = u :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, ZMod.pow_card_pow])

theorem nmChar_pow (K : Type) [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) (j : ℕ) :
    (DiscreteGroups.sglob.DzType.nmChar K χ₀) ^ g ^ j = DiscreteGroups.sglob.DzType.nmChar K χ₀ := by
  refine MonoidHom.ext fun z => ?_
  rw [MonoidHom.pow_apply]
  show (χ₀ (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z)) ^ g ^ j =
    χ₀ (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z)
  rw [← map_pow, units_pow_card_pow]

theorem isRegularChar_mul (K : Type) [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) {θ : Kˣ →* ℂˣ}
    (hθ : GlobalTheory.Published.IsRegularChar g n θ) : GlobalTheory.Published.IsRegularChar g n (θ * DiscreteGroups.sglob.DzType.nmChar K χ₀) := by
  intro i j hi hj h
  apply hθ i j hi hj
  rw [mul_pow, mul_pow, nmChar_pow, nmChar_pow] at h
  exact mul_right_cancel h

theorem char_twFD (K : Type) [Field K] [Algebra (ZMod g) K] (hK : Nat.card K = g ^ n) (hn : 0 < n)
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (θ : Kˣ →* ℂˣ) (τ : FDRep ℂ (Gn g n))
    (hτ : ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
      (twFD τ χ₀).character y =
        (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (((θ * DiscreteGroups.sglob.DzType.nmChar K χ₀) (z ^ g ^ j) : ℂˣ) : ℂ) := by
  intro y hy z hz
  have hN : ∀ j, DiscreteGroups.sglob.DzType.nmChar K χ₀ (z ^ g ^ j) = χ₀ (Matrix.GeneralLinearGroup.det y) := by
    intro j
    rw [det_eq_norm K hK hn y hy z hz, map_pow, ← MonoidHom.pow_apply, nmChar_pow]
    try rfl
  rw [character_twFD, hτ y hy z hz]
  simp only [MonoidHom.mul_apply, Units.val_mul, hN]
  rw [← Finset.sum_mul]
  ring

end DiscreteGroups.sglob.DzTw
