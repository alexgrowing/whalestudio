import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmPoly

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem cent_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem cent_nm_sg (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ q (sg σ d) = sg σ (nm σ q d) := by
  unfold nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ext a b
  change (σ ^ m) (σ _) = σ ((σ ^ m) _)
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_succ, ← pow_succ']

private theorem cent_up_inj (h : Function.Injective (algebraMap k R)) :
    Function.Injective (up R : GL (Fin n) k → GL (Fin n) R) := by
  intro s t hst
  ext a b
  exact h (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hst)

private theorem cent_descend {σ : R ≃ₐ[k] R} {q : ℕ} (hσ : IsGal σ q) (x : GL (Fin n) R) (hx : sg σ x = x) :
    ∃ t : GL (Fin n) k, x = up R t := by
  have key : ∀ y : GL (Fin n) R, sg σ y = y → ∃ M : Matrix (Fin n) (Fin n) k,
      M.map (algebraMap k R) = (y : Matrix (Fin n) (Fin n) R) := by
    intro y hy
    have h : ∀ a b, ∃ c, algebraMap k R c = (y : Matrix (Fin n) (Fin n) R) a b := fun a b =>
      hσ.fix _ (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hy)
    choose M hM using h
    exact ⟨Matrix.of M, by ext a b; exact hM a b⟩
  obtain ⟨M, hM⟩ := key x hx
  obtain ⟨N, hN⟩ := key x⁻¹ (by rw [map_inv, hx])
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) hσ.inj
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext hM.symm⟩
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.mul_inv]
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.inv_mul]

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.nmCent :
    UpperTheory.ConvolutionTheory.D.NmCent := by
  intro k R _ _ _ _ σ q hσ n a γ hsep ha x
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rw [cp, ← Matrix.charpoly_map] at h
    exact h
  have hc := (conjSep k R n _ hs).2.1
  have hfix : ∀ y, nm σ q (sgConj σ y a) = up R γ → y * up R γ = up R γ * y := by
    intro y hy
    rw [(nmPoly k R σ q hσ n a).2 y, ha, mul_assoc, inv_mul_eq_iff_eq_mul] at hy
    exact hy.symm
  have hag : a * up R γ = up R γ * a := by
    apply hfix
    rw [sgConj, inv_mul_cancel, one_mul, cent_nm_sg, ha, cent_sg_up]
  have hcomm : ∀ y : GL (Fin n) R, y * up R γ = up R γ * y → a * y = y * a := by
    intro y hy
    obtain ⟨p, hp⟩ := hc a.val (by simpa using congrArg Units.val hag)
    obtain ⟨p', hp'⟩ := hc y.val (by simpa using congrArg Units.val hy)
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hp, hp', ← map_mul, ← map_mul, mul_comm]
  constructor
  · intro hx
    have h1 := hfix x (by rw [hx, ha])
    have h2 := hcomm x h1
    have h3 : sg σ x = x := by
      rw [sgConj, mul_assoc, inv_mul_eq_iff_eq_mul, ← h2] at hx
      exact mul_left_cancel hx
    obtain ⟨t, rfl⟩ := cent_descend hσ x h3
    refine ⟨t, cent_up_inj hσ.inj ?_, rfl⟩
    rw [map_mul, map_mul, h1]
  · rintro ⟨t, ht, rfl⟩
    have h2 := hcomm (up R t) (by rw [← map_mul, ← map_mul, ht.eq])
    rw [sgConj, cent_sg_up, mul_assoc, h2, inv_mul_cancel_left]
