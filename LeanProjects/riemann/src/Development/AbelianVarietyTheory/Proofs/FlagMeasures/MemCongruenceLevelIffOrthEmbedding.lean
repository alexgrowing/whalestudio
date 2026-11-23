import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualOfAnisotropicOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSplitUnitVectorOrthComplement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

private theorem exists_intertwiner_decomp_of_kernel_intertwines {R : Type} [CommRing R] {n m : ℕ} (x u : Fin n → R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h5 : vecMulVec x u + A * A' = 1) (z : Fin n → R) :
    z = (u ⬝ᵥ z) • x + A *ᵥ (A' *ᵥ z) := by
  have h : (vecMulVec x u + A * A') *ᵥ z = z := by rw [h5, Matrix.one_mulVec]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] at h
  conv_lhs => rw [← h]
  congr 1
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem coords_smul_add_mulVec {R : Type} [CommRing R] {n m : ℕ} (x u : Fin n → R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h1 : A' * A = 1) (h2 : A' *ᵥ x = 0) (h3 : u ᵥ* A = 0) (h4 : u ⬝ᵥ x = 1) (a : R) (w : Fin m → R) :
    u ⬝ᵥ (a • x + A *ᵥ w) = a ∧ A' *ᵥ (a • x + A *ᵥ w) = w := by
  constructor
  · rw [dotProduct_add, dotProduct_smul, h4, Matrix.dotProduct_mulVec, h3, zero_dotProduct, smul_eq_mul,
      mul_one, add_zero]
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, h2, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, smul_zero,
      zero_add]

theorem conj_stab_and_cong_of_split {R : Type} [CommRing R] (S : Subring R) {n m : ℕ}
    (L : Submodule S (Fin n → R)) (L' : Submodule S (Fin m → R))
    (X Xi G : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) R)
    (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (hX : X * Xi = 1) (hXi : Xi * X = 1)
    (h1 : A' * A = 1) (h2 : A' *ᵥ x = 0) (h3 : u ᵥ* A = 0) (h4 : u ⬝ᵥ x = 1)
    (h5 : vecMulVec x u + A * A' = 1)
    (hL : ∀ z, Xi *ᵥ z ∈ L ↔ ∃ a ∈ S, ∃ w ∈ L', z = a • x + A *ᵥ w)
    (hGx : G *ᵥ x = x) (hGA : G * A = A * g) :
    ((∀ w, w ∈ L' ↔ g *ᵥ w ∈ L') ↔ ∀ y, y ∈ L ↔ (Xi * G * X) *ᵥ y ∈ L) ∧
      ∀ c : R, (∀ w ∈ L', ∃ w' ∈ L', (g - 1) *ᵥ w = c • w') ↔
        ∀ y ∈ L, ∃ z ∈ L, (Xi * G * X - 1) *ᵥ y = c • z := by
  have hu0 : ∀ w, u ⬝ᵥ (A *ᵥ w) = 0 := fun w => by
    rw [Matrix.dotProduct_mulVec, h3, zero_dotProduct]
  have hA0 : ∀ w, A' *ᵥ (A *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hM : ∀ z, Xi *ᵥ z ∈ L ↔ u ⬝ᵥ z ∈ S ∧ A' *ᵥ z ∈ L' := by
    intro z
    rw [hL]
    constructor
    · rintro ⟨a, ha, w, hw, rfl⟩
      obtain ⟨e1, e2⟩ := coords_smul_add_mulVec x u A A' h1 h2 h3 h4 a w
      rw [e1, e2]
      exact ⟨ha, hw⟩
    · rintro ⟨ha, hw⟩
      exact ⟨_, ha, _, hw, exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 z⟩
  have hG : ∀ z, G *ᵥ z = (u ⬝ᵥ z) • x + A *ᵥ (g *ᵥ (A' *ᵥ z)) := by
    intro z
    conv_lhs => rw [exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 z]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hGx, Matrix.mulVec_mulVec, hGA, ← Matrix.mulVec_mulVec]
  have hXiX : ∀ y, Xi *ᵥ (X *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hXi, Matrix.one_mulVec]
  have hXXi : ∀ y, X *ᵥ (Xi *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]
  have hconj : ∀ y, (Xi * G * X) *ᵥ y = Xi *ᵥ (G *ᵥ (X *ᵥ y)) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hGm : ∀ p, (G - 1) *ᵥ p = A *ᵥ ((g - 1) *ᵥ (A' *ᵥ p)) := by
    intro p
    have hp := exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 p
    calc (G - 1) *ᵥ p = G *ᵥ p - p := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = ((u ⬝ᵥ p) • x + A *ᵥ (g *ᵥ (A' *ᵥ p))) - ((u ⬝ᵥ p) • x + A *ᵥ (A' *ᵥ p)) := by
          rw [← hp, hG]
      _ = A *ᵥ ((g - 1) *ᵥ (A' *ᵥ p)) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
          abel
  have hsub : ∀ y, (Xi * G * X - 1) *ᵥ y = Xi *ᵥ (A *ᵥ ((g - 1) *ᵥ (A' *ᵥ (X *ᵥ y)))) := by
    intro y
    rw [← hGm]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, hconj, Matrix.one_mulVec, hXiX]
  refine ⟨⟨fun hg y => ?_, fun h w => ?_⟩, fun c => ⟨fun hc y hy => ?_, fun h w hw => ?_⟩⟩
  · rw [hconj y]
    conv_lhs => rw [← hXiX y]
    rw [hM, hM, hG, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).1, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).2]
    exact Iff.and Iff.rfl (hg _)
  · have hw := h (Xi *ᵥ (A *ᵥ w))
    rw [hconj, hXXi, hM, hM, hG, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).1,
      (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).2, hu0, hA0] at hw
    simpa [S.zero_mem] using hw
  · rw [← hXiX y, hM] at hy
    obtain ⟨w', hw', hgw⟩ := hc _ hy.2
    refine ⟨Xi *ᵥ (A *ᵥ w'), ?_, ?_⟩
    · rw [hM, hu0, hA0]
      exact ⟨S.zero_mem, hw'⟩
    · rw [hsub, hgw, Matrix.mulVec_smul, Matrix.mulVec_smul]
  · have hy : Xi *ᵥ (A *ᵥ w) ∈ L := by
      rw [hM, hu0, hA0]
      exact ⟨S.zero_mem, hw⟩
    obtain ⟨z, hz, hcz⟩ := h _ hy
    rw [hsub, hXXi, hA0] at hcz
    have e := congrArg (fun v => A' *ᵥ (X *ᵥ v)) hcz
    simp only [hXXi, hA0, Matrix.mulVec_smul] at e
    refine ⟨A' *ᵥ (X *ᵥ z), ?_, e⟩
    have hz' : Xi *ᵥ (X *ᵥ z) ∈ L := by rw [hXiX]; exact hz
    exact ((hM _).1 hz').2

theorem mem_level_iff_of_isFinEmb (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hp : IsPerp D s x A xf)
    (jf : D.inst.Gf →* I.Gf) (hj : IsFinEmb D x A jf) :
    (∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset) ∧
      ∀ (N : ℕ) (g : D.inst.Gf), g ∈ D.inst.Kg N ↔ xf⁻¹ * jf g * xf ∈ I.Kg N := by
  obtain ⟨hn, hβ, hxJA, hAJA, hp5, hp6⟩ := hp
  have hJ : I.Jᴴ = I.J := by
    have h := I.J_herm
    unfold Formalism.UG.IsHerm at h
    conv_rhs => rw [← h]
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, starRingEnd_apply]
  have hβ' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]
    cases s <;> simp [sgn]
  obtain ⟨u, A', e1, e2, e3, e4, e5, -⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ' hxJA hAJA
  have h1 : afMat I A' * afMat I A = 1 := by
    simp only [afMat]
    rw [← Matrix.map_mul, e1, Matrix.map_one _ (Formalism.UG.inclE (F := I.F) (Af I.F)).map_zero (Formalism.UG.inclE (F := I.F) (Af I.F)).map_one]
  have h2 : afMat I A' *ᵥ afVec I x = 0 := by
    funext i
    have := RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) A' x i
    rw [e2, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h3 : afVec I u ᵥ* afMat I A = 0 := by
    funext i
    have := RingHom.map_vecMul (Formalism.UG.inclE (F := I.F) (Af I.F)) A u i
    rw [e3, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h4 : afVec I u ⬝ᵥ afVec I x = 1 := by
    have := RingHom.map_dotProduct (Formalism.UG.inclE (F := I.F) (Af I.F)) u x
    rw [e4, map_one] at this
    exact this.symm
  have h5 : vecMulVec (afVec I x) (afVec I u) + afMat I A * afMat I A' = 1 := by
    have hv : vecMulVec (afVec I x) (afVec I u) = (vecMulVec x u).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
      ext i j
      simp [afVec, vecMulVec]
    rw [hv]
    simp only [afMat]
    rw [← Matrix.map_mul, ← Matrix.map_add _ (map_add (Formalism.UG.inclE (F := I.F) (Af I.F))), e5, Matrix.map_one _ (Formalism.UG.inclE (F := I.F) (Af I.F)).map_zero (Formalism.UG.inclE (F := I.F) (Af I.F)).map_one]
  have hX : I.fmat xf * I.fmat xf⁻¹ = 1 := by simp [AutInst.fmat]
  have hXi : I.fmat xf⁻¹ * I.fmat xf = 1 := by simp [AutInst.fmat]
  have hprod : ∀ g, I.fmat (xf⁻¹ * jf g * xf) = I.fmat xf⁻¹ * I.fmat (jf g) * I.fmat xf := by
    intro g
    simp [AutInst.fmat]
  have key := fun g => conj_stab_and_cong_of_split (IntAf I.F I.E) I.Lf D.inst.Lf (I.fmat xf) (I.fmat xf⁻¹)
    (I.fmat (jf g)) (D.inst.fmat g) (afVec I x) (afVec I u) (afMat I A) (afMat I A') hX hXi h1 h2 h3 h4 h5
    (adelicLattice_split I D s x A xf ⟨hn, hβ, hxJA, hAJA, hp5, hp6⟩) (hj g).1 (hj g).2
  have hK : ∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset := by
    intro g
    show (∀ w, w ∈ D.inst.Lf ↔ D.inst.fmat g *ᵥ w ∈ D.inst.Lf) ↔
      ∀ y, y ∈ I.Lf ↔ I.fmat (xf⁻¹ * jf g * xf) *ᵥ y ∈ I.Lf
    rw [hprod]
    exact (key g).1
  refine ⟨hK, fun N g => ?_⟩
  show (g ∈ D.inst.Kset ∧ ∀ y ∈ D.inst.Lf, ∃ z ∈ D.inst.Lf,
      (D.inst.fmat g - 1) *ᵥ y = (N : I.E ⊗[I.F] Af I.F) • z) ↔
    (xf⁻¹ * jf g * xf ∈ I.Kset ∧ ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (I.fmat (xf⁻¹ * jf g * xf) - 1) *ᵥ y = (N : I.E ⊗[I.F] Af I.F) • z)
  rw [hprod]
  exact Iff.and (hK g) ((key g).2 _)

end GlobalTheory.StabUnfold
