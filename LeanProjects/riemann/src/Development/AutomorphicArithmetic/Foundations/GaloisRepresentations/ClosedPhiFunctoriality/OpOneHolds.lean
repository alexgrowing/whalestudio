import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem opOne_comm {A B : Type*} [CommRing A] [CommRing B] (i : A →+* B) (hi : Function.Injective i) {d : ℕ}
    (M M' : Matrix (Fin d) (Fin d) A) (c : A) (hc : IsUnit (i c))
    (h : M * M' = c • (1 : Matrix (Fin d) (Fin d) A)) : M' * M = c • (1 : Matrix (Fin d) (Fin d) A) := by
  obtain ⟨u, hu⟩ := hc
  have h1 : M.map i * M'.map i = i c • (1 : Matrix (Fin d) (Fin d) B) := by
    rw [← Matrix.map_mul, h]
    ext a b
    simp [Matrix.smul_apply, Matrix.one_apply, apply_ite i]
  have h2 : M.map i * (((u⁻¹ : Bˣ) : B) • M'.map i) = 1 := by
    rw [Matrix.mul_smul, h1, ← hu, smul_smul, Units.inv_mul, one_smul]
  have h3 := mul_eq_one_comm.mp h2
  have h4 : M'.map i * M.map i = i c • (1 : Matrix (Fin d) (Fin d) B) := by
    rw [Matrix.smul_mul] at h3
    have := congrArg (fun X => (u : B) • X) h3
    simp only [smul_smul, Units.mul_inv, one_smul] at this
    rw [this, hu]
  ext a b
  apply hi
  have := congrFun (congrFun h4 a) b
  rw [← Matrix.map_mul] at this
  simpa [Matrix.smul_apply, Matrix.one_apply, apply_ite i] using this

private theorem opOne_core {B : Type*} [CommRing B] {d : ℕ} (φ₁ φ₂ : B →+* B) (Z Zs U : Matrix (Fin d) (Fin d) B)
    (a L : B) (N : ℕ) (hL : φ₂ L = L) (ht : IsUnit (φ₂ a))
    (hU : a ^ N • U = Z) (hZ : Zs * Z = (a ^ (2 * N) * L) • (1 : Matrix (Fin d) (Fin d) B)) :
    (φ₂ (a ^ (2 * N) * L) • (Z.map φ₁ * Zs.map φ₂)) * U.map φ₂ =
      (φ₂ a ^ (3 * N) * L ^ 2 * φ₁ a ^ N) • U.map φ₁ := by
  have hm : ∀ (φ : B →+* B), Z.map φ = φ a ^ N • U.map φ := by
    intro φ
    subst hU
    ext i j
    simp [Matrix.smul_apply]
  have hZZ : Zs.map φ₂ * Z.map φ₂ = φ₂ (a ^ (2 * N) * L) • (1 : Matrix (Fin d) (Fin d) B) := by
    rw [← Matrix.map_mul, hZ]
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply, apply_ite φ₂]
  have hs : φ₂ (a ^ (2 * N) * L) = φ₂ a ^ (2 * N) * L := by rw [map_mul, map_pow, hL]
  apply (ht.pow N).smul_left_cancel.mp
  calc φ₂ a ^ N • ((φ₂ (a ^ (2 * N) * L) • (Z.map φ₁ * Zs.map φ₂)) * U.map φ₂)
      = φ₂ (a ^ (2 * N) * L) • (Z.map φ₁ * (Zs.map φ₂ * (φ₂ a ^ N • U.map φ₂))) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_smul, mul_comm]
    _ = (φ₂ (a ^ (2 * N) * L) * φ₂ (a ^ (2 * N) * L)) • Z.map φ₁ := by
        rw [← hm, hZZ, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    _ = φ₂ a ^ N • ((φ₂ a ^ (3 * N) * L ^ 2 * φ₁ a ^ N) • U.map φ₁) := by
        rw [hm φ₁, hs, smul_smul, smul_smul]
        congr 1
        ring

private theorem opOne_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (y : Per.Acris l) :
    (Per.φB l ^ n) (iB l y) = iB l ((phiA l ^ n) y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, RingHom.mul_def, RingHom.mul_def, RingHom.comp_apply, RingHom.comp_apply]
    rw [show Per.φB l (iB l y) = iB l (phiA l y) from GlobalTheory.MemLoc.PhiInj.φB_alg l y, ih]

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.opOne_holds :
    OpOne2 := by
  intro l _ τ₁ hτ K N k n₁ n₂ d ρ y y' Q Q' U hy hQ hU hZ
  have hinj : Function.Injective (iB l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
  have hlB : IsUnit (iB l (l : Per.Acris l)) := by
    rw [map_natCast]; exact isUnit_l_Bcris l
  have h1 : (y * Q) * (Q' * y') = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hy, smul_smul, mul_comm]
  have hc : IsUnit (iB l (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k))) := by
    rw [map_mul, map_pow, map_pow]
    exact (hτ.pow _).mul (hlB.pow _)
  have h2 := opOne_comm (iB l) hinj _ _ _ hc h1
  have hφ : ∀ n, (Per.φB l ^ n) (iB l (l : Per.Acris l)) = iB l (l : Per.Acris l) := by
    intro n; rw [opOne_pow, map_natCast]
  have ht : ∀ n, IsUnit (iB l ((phiA l ^ n) τ₁)) := by
    intro n; rw [← opOne_pow]; exact hτ.map (Per.φB l ^ n)
  refine ⟨h1, h2, ?_, U, hU, ?_⟩
  · rw [map_mul, map_mul, map_pow, map_pow, map_pow]
    exact (((ht n₂).pow _).mul (hlB.pow _)).mul ((ht n₁).pow _)
  · have key := opOne_core (Per.φB l ^ n₁) (Per.φB l ^ n₂) ((y * Q).map (iB l)) ((Q' * y').map (iB l)) U
      (iB l τ₁) (iB l (l : Per.Acris l) ^ (2 * k)) N (by rw [map_pow, hφ])
      (by rw [opOne_pow]; exact ht n₂) hZ
      (by
        rw [← Matrix.map_mul, h2]
        ext a b
        simp [Matrix.smul_apply, Matrix.one_apply, apply_ite (iB l)])
    have hmap : ∀ (n : ℕ) (M : Matrix (Fin d) (Fin d) (Per.Acris l)),
        (M.map ⇑(phiA l ^ n)).map (iB l) = (M.map (iB l)).map ⇑(Per.φB l ^ n) := by
      intro n M
      ext a b
      exact (opOne_pow l n (M a b)).symm
    have hsm : ∀ (c : Per.Acris l) (M : Matrix (Fin d) (Fin d) (Per.Acris l)),
        (c • M).map (iB l) = iB l c • M.map (iB l) := by
      intro c M
      ext a b
      simp [Matrix.smul_apply]
    have hsc : iB l ((phiA l ^ n₂) (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k))) =
        (Per.φB l ^ n₂) (iB l τ₁ ^ (2 * N) * iB l (l : Per.Acris l) ^ (2 * k)) := by
      rw [← opOne_pow, map_mul (iB l), map_pow (iB l), map_pow (iB l)]
    have hs : iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N) =
        (Per.φB l ^ n₂) (iB l τ₁) ^ (3 * N) * (iB l (l : Per.Acris l) ^ (2 * k)) ^ 2 *
          (Per.φB l ^ n₁) (iB l τ₁) ^ N := by
      rw [opOne_pow, opOne_pow, map_mul, map_mul, map_pow, map_pow, map_pow, ← pow_mul,
        show 2 * k * 2 = 4 * k by ring]
    rw [hsm, Matrix.map_mul, hmap, hmap, hsc, hs]
    exact key
