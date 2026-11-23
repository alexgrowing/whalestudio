import Formalism.LocalToGlobal.AlgebraicTheory.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.IntOpTwoFreeOf

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4 opU taylorMv)
open Formalism.L2.Th1.Top (IsLatH thetaZ)
open Formalism.L2.Th1.G (linSub)
open Formalism.L2.Th1.CM (omegaK)

namespace TensorIntegralTorsion

theorem odd_b {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) : ∃ k : ℤ, b = 2 * k + 1 := by
  obtain ⟨h1, -, h7, -⟩ := hOK
  rcases Int.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k ^ 2) := by
      rw [hk] at h1
      linear_combination -h1
    generalize (a : ℤ) * c - k ^ 2 = X at h2
    omega
  · exact ⟨k, hk⟩

theorem qint_smul_mem {n : Type} (Λ : AddSubgroup (n → ℂ)) (b : ℤ) (d : ℕ) (hb : ∃ k : ℤ, b = 2 * k + 1)
    (hSt : ∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b d • x ∈ Λ) (α : ℂ) (hα : IsQInt d α) (x : n → ℂ) (hx : x ∈ Λ) :
    α • x ∈ Λ := by
  obtain ⟨k, hk⟩ := hb
  obtain ⟨m, n', rfl⟩ := hα
  have hθ := hSt x hx
  have key : ((m : ℂ) + (n' : ℂ) * omegaK d) • x
      = (m - n' * k) • x + n' • (Formalism.L2.Th1.F.cmTheta b d • x) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, omegaK,
      Formalism.L2.Th1.F.cmTheta, hk, Pi.mul_apply, Pi.sub_apply, Pi.intCast_apply]
    push_cast
    ring
  rw [key]
  exact Λ.add_mem (Λ.zsmul_mem hx _) (Λ.zsmul_mem hθ _)

theorem img_smul_mem {n : Type} [Fintype n] (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (α : ℂ) (hΛ : ∀ x ∈ Λ, α • x ∈ Λ) (y : Fin 4 × n → ℂ)
    (hy : y ∈ imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) :
    α • y ∈ imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
  rw [imgLat, AddSubgroup.mem_map] at hy ⊢
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' : ∀ a, Formalism.L2.Th1.H.slice a z ∈ Λ := hz
  refine ⟨α • z, ?_, ?_⟩
  · show ∀ a, Formalism.L2.Th1.H.slice a (α • z) ∈ Λ
    intro a
    exact hΛ _ (hz' a)
  · simp [map_smul]

theorem idx_coord_mem (L : PeriodPair) {m : Type} (Λb : AddSubgroup (m → ℂ)) (v : m → ℂ) (hv : v ∈ Λb) (w : m) :
    (relIdx (stdLat L m) Λb : ℂ) * v w ∈ L.lattice := by
  have h := AddSubgroup.nsmul_index_mem ((stdLat L m).addSubgroupOf Λb) ⟨v, hv⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h
  have h2 : (relIdx (stdLat L m) Λb) • v ∈ stdLat L m := by
    simpa [relIdx, AddSubgroup.relIndex] using h
  have h3 := (AddSubgroup.mem_pi _).mp h2 w (Set.mem_univ _)
  simpa [nsmul_eq_mul] using h3

end TensorIntegralTorsion

open TensorIntegralTorsion

open Formalism.L2.Th1.H Formalism.L2.Th1.H.FormalGroupLawNegation Formalism.L2.Th1.GD in
theorem tensor_integral_torsion : TensZEt := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hOK n _ _ h Λ hSD hSt θ hθ p _ ι g₁ ε hIso hp hidx2 hε hT t αq M hαq hM hαt hMt
  have hidx1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 := by
    intro h0
    exact hp (h0 ▸ dvd_zero p)
  have hStd := stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hOK.1 hOK.2.1 hOK.2.2.1 n h Λ g₁ hIso hSD hSt hidx1 hidx2
  obtain ⟨S, hS⟩ := (cosetRepsExist _ _ _ hidx1).1
  have hΛα : ∀ x ∈ Λ, αq • x ∈ Λ := fun x hx => qint_smul_mem Λ b₀ dK (odd_b hOK) hSt αq hαq x hx
  have huM := smul_img_mem Λ g₁ t _ hMt
  have huα := smul_img_mem Λ g₁ t _ hαt
  let cx : (Fin 4 × n → ℂ) → ℂ := fun x => ε * (↑√↑(relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))))⁻¹
      * alphaQ (√↑dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) x
      * Complex.exp (-↑Real.pi * Complex.I * ↑(Formalism.L2.Th1.H.altE (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
          (g₁ fun w : Fin 4 × n => t w.2) x))
  let fx : (Fin 4 × n → ℂ) → Fin 4 × n → ℂ → ℂ := fun x w => Formalism.L2.Th1.F.opU (cmL a₀ b₀ dK ha hdK lam hlam)
      ((g₁ fun w : Fin 4 × n => t w.2) w + x w) (Formalism.L2.Th1.F.th0 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * ↑a₀ / 2))
  refine ⟨↥S, inferInstance, fun x => ι (cx x),
    fun x => (g₁ fun w : Fin 4 × n => t w.2) + (x : Fin 4 × n → ℂ),
    relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)), ?_, Nat.pos_of_ne_zero hidx1, hp, ?_, ?_, ?_⟩
  · intro x
    exact norm_coeff ι _ _ hStd.selfDual _ hStd.betaSemi _ hp ε hε _ _ M hM huM (hS.1 x x.2)
  · intro x w
    have hx := img_smul_mem Λ g₁ αq hΛα x (hS.1 x x.2)
    have hv := (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)).add_mem huα hx
    have := idx_coord_mem (cmL a₀ b₀ dK ha hdK lam hlam) _ _ hv w
    simpa [Pi.add_apply, smul_eq_mul, mul_add, mul_assoc] using this
  · intro x w
    have := trans_mem (cmL a₀ b₀ dK ha hdK lam hlam) _ _ _ M huM (hS.1 x x.2) w
    rw [Nat.mul_comm] at this
    simpa [Pi.add_apply] using this
  · let M₀ : Matrix (Fin 4 × n) (Fin 4 × n) ℂ := fun w w' => g₁.symm (Pi.single w' 1) w
    have hmv : ∀ y : Fin 4 × n → ℂ, M₀.mulVec y = g₁.symm y := by
      intro y
      have hy : y = ∑ w' : Fin 4 × n, y w' • (Pi.single w' (1 : ℂ) : Fin 4 × n → ℂ) := by
        ext w
        simp [Finset.sum_apply, Pi.single_apply]
      ext w
      conv_rhs => rw [hy]
      simp [Matrix.mulVec, dotProduct, map_sum, map_smul, Finset.sum_apply, M₀, mul_comm]
    have hF : AnalyticAt ℂ (opU (matH h) t θ) 0 :=
      heisenbergAnalytic (n → ℂ) (matH h) t θ hθ.1 0 (Set.mem_univ _)
    have hth0 := (Formalism.L2.Th1.F.th0Basic _ _ hStd.per hStd.half).1
    have hfac : ∀ x : Fin 4 × n → ℂ, ∀ w : Fin 4 × n, AnalyticAt ℂ (fx x w) 0 :=
      fun x w => analyticAt_opU _ _ hth0
    have hfun : (fun y => Formalism.L2.Th1.H.tens4 (opU (matH h) t θ) (M₀.mulVec y))
        = fun y => ∑ x ∈ S, cx x * Formalism.L2.Th1.H.prodFn (fx x) y := by
      funext y
      rw [hmv, quadraticSemicharacter_identity_reformulated₂ _ _ n h Λ _ _ g₁ hStd ε θ hT S hS t y]
      rfl
    have step1 : Formalism.L2.Th1.H.linSubst M₀ (Formalism.L2.Th1.E.tensor4 (taylorMv (opU (matH h) t θ)))
        = taylorMv (fun y => Formalism.L2.Th1.H.tens4 (opU (matH h) t θ) (M₀.mulVec y)) := by
      rw [taylorMvComp _ _ M₀ _ (analyticAt_tens4 hF), taylorMvTens4 _ _ hF]
    have e1 : taylorMv (fun y => Formalism.L2.Th1.H.tens4 (opU (matH h) t θ) (M₀.mulVec y))
        = ∑ x ∈ S, MvPowerSeries.C (cx x) * taylorMv (Formalism.L2.Th1.H.prodFn (fx x)) := by
      rw [hfun]
      exact (taylorMv_sum taylorMvLinear S cx (fun x => Formalism.L2.Th1.H.prodFn (fx x))
        (fun x => analyticAt_prodFn (hfac x))).2
    calc _ = MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
          (Formalism.L2.Th1.H.linSubst M₀ (Formalism.L2.Th1.E.tensor4 (taylorMv (opU (matH h) t θ)))) := by
          rw [map_linSubst, map_tensor4]
          rfl
      _ = MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (∑ x ∈ S, MvPowerSeries.C (cx x) *
            ∏ w : Fin 4 × n, Formalism.InvariantFactorPaths.G7.at1 w (Formalism.L2.Th1.F.taylor0 (fx x w))) := by
          rw [step1, e1]
          congr 1
          exact Finset.sum_congr rfl (fun x _ => by rw [taylorMvProd _ _ (hfac x)])
      _ = _ := by
          rw [map_sumProd, Formalism.L2.Th1.Top.thetaZ, Formalism.L2.Th1.E.thetaProd]
          exact (Finset.sum_coe_sort S _).symm

end Formalism.L2.AlgTh
