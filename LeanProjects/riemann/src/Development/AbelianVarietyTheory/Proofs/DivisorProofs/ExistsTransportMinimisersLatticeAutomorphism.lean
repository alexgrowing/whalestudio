import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory

theorem relabel_cong {N r : ℕ} (e : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (x y : Fin r → ℤ)
    (h : ∀ i, ((x i : ℤ) : ZMod N) = y i) : ∀ i, ((e x i : ℤ) : ZMod N) = e y i := by
  have hd : ∀ i, (N : ℤ) ∣ x i - y i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i).symm
  choose w hw using hd
  have hxy : x - y = (N : ℤ) • w := by ext i; simp [hw i]
  have he : e x - e y = (N : ℤ) • e w := by rw [← map_sub, hxy, map_smul]
  intro i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(e w i), by linarith⟩

theorem qW_pull {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (f : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ))
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (y : Fin s → Fin r → ℤ) :
    qW W (pull f b) y = qW W b (fun u => f (y u)) := rfl

theorem relabel_minimisers : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ) (μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∃ σ : Equiv.Perm (Fin 8 → Fin r → ZMod N), (∀ c u i, ((e.symm (μ (σ c) u) i : ℤ) : ZMod N) = c u i) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b') ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W (pull e.toLinearMap b') α) := by
  intro W N _ r μ hμ e
  have key : ∀ (f g : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)), (∀ x, g (f x) = x) → ∀ c u i,
      ((g (μ (fun u i => ((f (μ c u) i : ℤ) : ZMod N)) u) i : ℤ) : ZMod N) = c u i := by
    intro f g hgf c u i
    rw [relabel_cong g _ (f (μ c u)) (fun j => hμ _ u j) i, hgf, hμ]
  let σ : Equiv.Perm (Fin 8 → Fin r → ZMod N) :=
    { toFun := fun c u i => ((e (μ c u) i : ℤ) : ZMod N)
      invFun := fun c u i => ((e.symm (μ c u) i : ℤ) : ZMod N)
      left_inv := fun c => by
        funext u i
        exact key e.toLinearMap e.symm.toLinearMap (fun x => e.symm_apply_apply x) c u i
      right_inv := fun c => by
        funext u i
        exact key e.symm.toLinearMap e.toLinearMap (fun x => e.apply_symm_apply x) c u i }
  refine ⟨σ, fun c u i => key e.toLinearMap e.symm.toLinearMap (fun x => e.symm_apply_apply x) c u i, ?_⟩
  intro b' hmin c α hα
  rw [qW_pull, qW_pull]
  have h1 : (fun u => e.toLinearMap ((fun c u => e.symm (μ (σ c) u)) c u)) = μ (σ c) := by
    funext u; simp
  rw [h1]
  apply hmin (σ c) (fun u => e.toLinearMap (α u))
  intro u i
  show _ = ((e (μ c u) i : ℤ) : ZMod N)
  exact relabel_cong e.toLinearMap (α u) (μ c u) (fun j => (hα u j).trans (hμ c u j).symm) i

end GlobalTheory
