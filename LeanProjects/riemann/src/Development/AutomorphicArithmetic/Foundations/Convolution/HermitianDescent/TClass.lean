import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GramBasic

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section
variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem ct_mul' (c : R ≃ₐ[k] R) (X Y : Matrix (Fin n) (Fin n) R) :
    ct c (X * Y) = ct c Y * ct c X := by
  rw [ct, ct, ct, Matrix.map_mul, Matrix.transpose_mul]

private theorem ct_ct' {c : R ≃ₐ[k] R} (h : IsGal c 2) (X : Matrix (Fin n) (Fin n) R) :
    ct c (ct c X) = X := by
  ext i j
  have := DFunLike.congr_fun h.pow (X i j)
  simpa [ct, pow_two] using this

private theorem comm_gram (G B M X : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det)
    (h1 : X * G * M = G) (h2 : X * B * M = B) : G⁻¹ * B * M = M * (G⁻¹ * B) := by
  have a1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hG
  have a2 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  have hN : (G⁻¹ * X * G) * M = 1 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc X, h1, a1]
  have hN' : M * (G⁻¹ * X * G) = 1 := mul_eq_one_comm.1 hN
  have e : M * (G⁻¹ * X) = G⁻¹ := by
    calc M * (G⁻¹ * X) = M * (G⁻¹ * X * G) * G⁻¹ := by simp only [mul_assoc, a2, mul_one]
      _ = G⁻¹ := by rw [hN', one_mul]
  calc G⁻¹ * B * M = (M * (G⁻¹ * X)) * B * M := by rw [e]
    _ = M * (G⁻¹ * (X * B * M)) := by simp only [mul_assoc]
    _ = M * (G⁻¹ * B) := by rw [h2]

private theorem comm_inv (Y Z M : Matrix (Fin n) (Fin n) R) (h1 : Y * Z = 1) (h2 : Z * Y = 1)
    (h : Y * M = M * Y) : Z * M = M * Z := by
  calc Z * M = Z * (M * (Y * Z)) := by rw [h1, mul_one]
    _ = Z * (M * Y) * Z := by simp only [mul_assoc]
    _ = Z * (Y * M) * Z := by rw [h]
    _ = (Z * Y) * (M * Z) := by simp only [mul_assoc]
    _ = M * Z := by rw [h2, one_mul]

end

section
variable {k R A : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing A] [Algebra k A]

private theorem comm_io (c : R ≃ₐ[k] R) (z : R ⊗[k] A) :
    (Algebra.TensorProduct.congr AlgEquiv.refl c : A ⊗[k] R ≃ₐ[A] A ⊗[k] R)
        (Algebra.TensorProduct.comm k R A z) = Algebra.TensorProduct.comm k R A (io c A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [io]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem fixed_tmul {c : R ≃ₐ[k] R}
    (h : IsGal (Algebra.TensorProduct.congr AlgEquiv.refl c : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) 2)
    (z : R ⊗[k] A) (hz : io c A z = z) : ∃ a : A, z = (1 : R) ⊗ₜ[k] a := by
  obtain ⟨a, ha⟩ := h.fix _ ((comm_io c z).trans (by rw [hz]))
  refine ⟨a, ?_⟩
  apply (Algebra.TensorProduct.comm k R A).injective
  rw [← ha]
  simp [Algebra.TensorProduct.algebraMap_apply]

private theorem fixed_unit {c : R ≃ₐ[k] R}
    (h : IsGal (Algebra.TensorProduct.congr AlgEquiv.refl c : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) 2)
    (u : (R ⊗[k] A)ˣ) (hu : io c A u.val = u.val) :
    ∃ x : Aˣ, (1 : R) ⊗ₜ[k] (x : A) = u.val := by
  have hu' : io c A (u⁻¹).val = (u⁻¹).val := by
    have e : io c A (u⁻¹).val * u.val = 1 := by
      conv_lhs => rw [← hu]
      rw [← map_mul, Units.inv_mul, map_one]
    calc io c A (u⁻¹).val = io c A (u⁻¹).val * (u.val * (u⁻¹).val) := by rw [Units.mul_inv, mul_one]
      _ = (u⁻¹).val := by rw [← mul_assoc, e, one_mul]
  obtain ⟨a, ha⟩ := fixed_tmul h _ hu
  obtain ⟨a', ha'⟩ := fixed_tmul h _ hu'
  have hm : a * a' = 1 := by
    apply h.inj
    have e1 : (1 : R) ⊗ₜ[k] (a * a') = 1 := by
      have := u.mul_inv
      rw [ha, ha', Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
      exact this
    have e2 := congrArg (Algebra.TensorProduct.comm k R A) e1
    rw [map_one]
    simpa [Algebra.TensorProduct.algebraMap_apply] using e2
  exact ⟨⟨a, a', hm, by rw [mul_comm, hm]⟩, ha.symm⟩

private theorem mat_mul' {n : ℕ} (b : Module.Basis (Fin n) k A) (s t : R ⊗[k] A) :
    mat b (s * t) = mat b s * mat b t := map_mul _ _ _

private theorem mat_inj {n : ℕ} (b : Module.Basis (Fin n) k A) :
    Function.Injective (mat (R := R) b) := Algebra.leftMulMatrix_injective _

private theorem mat_one' {n : ℕ} (b : Module.Basis (Fin n) k A) :
    mat (R := R) b 1 = 1 := map_one _

end

end UpperTheory.ConvolutionTheory.D

open UpperTheory.ConvolutionTheory.D in
theorem UpperTheory.ConvolutionTheory.D.tClass :
    UpperTheory.ConvolutionTheory.D.TClass := by
  intro k R _ _ _ _ A _ _ n b c hc g hg w hw d hd
  obtain ⟨hfin, -, -, hgal⟩ := galBase k R A c 2 hc
  obtain ⟨hG1, -, hG3⟩ := gramBasic k R A n b c hc
  obtain ⟨hunit, hinj, hcomm⟩ := hG3 g hg
  have hsep : (mat b g.val).charpoly.Separable := hg.2
  obtain ⟨x0, hx0⟩ := (conjSep k R n (mat b g.val) hsep).1 (d * th c d).val hd
  obtain ⟨y, hy⟩ : ∃ y : GL (Fin n) R, (d * th c d).val * y.val = y.val * mat b g.val := by
    refine ⟨x0⁻¹, ?_⟩
    have e1 : (x0⁻¹).val * x0.val = 1 := Units.inv_mul x0
    have e2 : x0.val * (x0⁻¹).val = 1 := Units.mul_inv x0
    calc (d * th c d).val * (x0⁻¹).val = ((x0⁻¹).val * x0.val) * (d * th c d).val * (x0⁻¹).val := by
          rw [e1, one_mul]
      _ = (x0⁻¹).val * (x0.val * (d * th c d).val) * (x0⁻¹).val := by simp only [mul_assoc]
      _ = (x0⁻¹).val * (mat b g.val * x0.val) * (x0⁻¹).val := by rw [hx0]
      _ = (x0⁻¹).val * mat b g.val * (x0.val * (x0⁻¹).val) := by simp only [mul_assoc]
      _ = (x0⁻¹).val * mat b g.val := by rw [e2, mul_one]
  obtain ⟨U, hU⟩ : ∃ U : GL (Fin n) R, U = (thConj c y d)⁻¹ := ⟨_, rfl⟩
  have hUv : U.val = ct c y.val * (d⁻¹ : GL (Fin n) R).val * y.val := by
    rw [hU, thConj, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, mul_assoc]
    rfl
  have hBG : (d⁻¹ : GL (Fin n) R).val * (d * th c d).val = ct c (d⁻¹ : GL (Fin n) R).val := by
    have e : (d * th c d).val = d.val * ct c (d⁻¹ : GL (Fin n) R).val := rfl
    rw [e, ← mul_assoc, Units.inv_mul, one_mul]
  have hUM : U.val * mat b g.val = ct c U.val := by
    rw [hUv]
    calc ct c y.val * (d⁻¹ : GL (Fin n) R).val * y.val * mat b g.val
        = ct c y.val * (d⁻¹ : GL (Fin n) R).val * (y.val * mat b g.val) := by rw [mul_assoc]
      _ = ct c y.val * (d⁻¹ : GL (Fin n) R).val * ((d * th c d).val * y.val) := by rw [hy]
      _ = ct c y.val * ((d⁻¹ : GL (Fin n) R).val * (d * th c d).val) * y.val := by
          simp only [mul_assoc]
      _ = ct c y.val * ct c (d⁻¹ : GL (Fin n) R).val * y.val := by rw [hBG]
      _ = ct c (ct c y.val * (d⁻¹ : GL (Fin n) R).val * y.val) := by
          rw [ct_mul', ct_mul', ct_ct' hc]; simp only [mul_assoc]
  have hXU : ct c (mat b g.val) * U.val * mat b g.val = U.val := by
    calc ct c (mat b g.val) * U.val * mat b g.val = ct c (mat b g.val) * (U.val * mat b g.val) := by
          rw [mul_assoc]
      _ = ct c (mat b g.val) * ct c U.val := by rw [hUM]
      _ = ct c (U.val * mat b g.val) := (ct_mul' c _ _).symm
      _ = U.val := by rw [hUM, ct_ct' hc]
  have hGu : IsUnit (gramL b (1 : R ⊗[k] A)).det := by
    rw [gram, ← Algebra.TensorProduct.one_def] at hunit
    exact hunit
  have hXG : ct c (mat b g.val) * gramL b (1 : R ⊗[k] A) * mat b g.val = gramL b (1 : R ⊗[k] A) := by
    rw [(hG1 1 g.val).1, (hG1 _ g.val).2.1, mul_one, mul_comm, hg.1]
  have hY := comm_gram _ U.val _ _ hGu hXG hXU
  obtain ⟨s, hs⟩ := hcomm _ hY
  have a1 := Matrix.nonsing_inv_mul _ hGu
  have a2 := Matrix.mul_nonsing_inv _ hGu
  have u1 : U.val * (U⁻¹).val = 1 := Units.mul_inv U
  have u2 : (U⁻¹).val * U.val = 1 := Units.inv_mul U
  have hYZ : (gramL b (1 : R ⊗[k] A))⁻¹ * U.val * ((U⁻¹).val * gramL b (1 : R ⊗[k] A)) = 1 := by
    calc _ = (gramL b (1 : R ⊗[k] A))⁻¹ * (U.val * (U⁻¹).val) * gramL b (1 : R ⊗[k] A) := by
          simp only [mul_assoc]
      _ = 1 := by rw [u1, mul_one, a1]
  have hZY : (U⁻¹).val * gramL b (1 : R ⊗[k] A) * ((gramL b (1 : R ⊗[k] A))⁻¹ * U.val) = 1 := by
    calc _ = (U⁻¹).val * (gramL b (1 : R ⊗[k] A) * (gramL b (1 : R ⊗[k] A))⁻¹) * U.val := by
          simp only [mul_assoc]
      _ = 1 := by rw [a2, mul_one, u2]
  obtain ⟨t, ht⟩ := hcomm _ (comm_inv _ _ _ hYZ hZY hY)
  have hst : s * t = 1 := by
    apply mat_inj (R := R) b
    rw [mat_mul', mat_one', ← hs, ← ht, hYZ]
  have hUs : U.val = gramL b s := by
    have := (hG1 1 s).2.1
    rw [one_mul, ← hs, ← mul_assoc, a2, one_mul] at this
    exact this
  have hfix : io c A s = s * g.val := by
    apply hinj
    rw [← (hG1 s s).2.2.1, ← (hG1 s g.val).2.1, ← hUs, hUM]
  have h1 : w.val * (g.val * io c A (w⁻¹).val) = 1 := by
    rw [← mul_assoc, mul_comm w.val, ← hw, ← map_mul, Units.mul_inv, map_one]
  have h2 : g.val * io c A (w⁻¹).val = (w⁻¹).val := by
    calc g.val * io c A (w⁻¹).val = (w⁻¹).val * (w.val * (g.val * io c A (w⁻¹).val)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = (w⁻¹).val := by rw [h1, mul_one]
  let su : (R ⊗[k] A)ˣ := ⟨s, t, hst, by rw [mul_comm, hst]⟩
  have hu : io c A (su * w⁻¹).val = (su * w⁻¹).val := by
    change io c A (s * (w⁻¹).val) = s * (w⁻¹).val
    rw [map_mul, hfix, mul_assoc, h2]
  obtain ⟨x, hx⟩ := fixed_unit hgal _ hu
  refine ⟨x, y, ?_⟩
  rw [← hU, hUs, hx]
  change gramL b s = gramL b (s * (w⁻¹).val * w.val)
  rw [mul_assoc, Units.inv_mul, mul_one]
