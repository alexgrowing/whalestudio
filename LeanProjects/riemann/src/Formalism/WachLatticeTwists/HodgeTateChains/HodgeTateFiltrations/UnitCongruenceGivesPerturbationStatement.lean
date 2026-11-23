import Formalism.WachLatticeTwists.HodgeTateChains.UnitCongruenceGivesPerturbation
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MemSmulTopOf

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

theorem wSandwich : StatWSandwich := by
  intro ℓ _ As AA WC OC _ _ _ _ _ jA ι φ Gg _ H act r ρ πs ξ x M0 h0 W ϑ c hL hinj hx hξ hc
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨⟨A, hA⟩, ⟨A', hA'⟩⟩ := sandwichAA AA WC ι φ (jA x) (jA ξ) r M0 h0 W.Xx W.Xi W.P
    (W.P1.map jA) (W.Q1.map jA) hL hx hξ W.inv1 W.inv2 W.W1 W.map_eq_xi_power_smul (by
      rw [← Matrix.map_mul, W.product_eq_xi_power_smul_one, Matrix.map_smul' jA _ _ (map_mul jA),
        Matrix.map_one jA (map_zero jA) (map_one jA), map_pow])
  have hminj : Function.Injective (fun M : Matrix (Fin r) (Fin r) AA => M.map ι) := by
    intro M M' h
    ext i j
    exact hinj (congrFun (congrFun h i) j)
  have hscal : (((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA)).map ι
      = (ι (jA x)) ^ (M0 + h0) • (1 : Matrix (Fin r) (Fin r) WC) := by
    rw [Matrix.map_smul' ι _ _ (map_mul ι), Matrix.map_one ι (map_zero ι) (map_one ι), map_pow]
  have h1 : A * A' = ((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) := by
    apply hminj
    show (A * A').map ι = (((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA)).map ι
    rw [Matrix.map_mul, hA, hA', hscal, Matrix.smul_mul, Matrix.mul_smul, W.inv1, smul_smul, ← pow_add]
  have h2 : A' * A = ((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) := by
    apply hminj
    show (A' * A).map ι = (((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA)).map ι
    rw [Matrix.map_mul, hA, hA', hscal, Matrix.smul_mul, Matrix.mul_smul, W.inv2, smul_smul, ← pow_add,
      add_comm]
  obtain ⟨Y', hY1, hY2⟩ := sandwichOC ℓ hℓ AA OC ϑ (jA x) c r M0 h0 A A' hc h1 h2
  exact ⟨A, Y', hA, hY1, hY2⟩

theorem unitCongruenceGivesPerturbation_statement : UnitCongruenceGivesPerturbation := by
  intro ℓ _ R _ _ Xm _ _ _ _ ϖ z z' r V g0 hzz hc hz hinj hsur hV
  choose B hB using hV
  let g : (Fin r → Xm) →ₗ[R] (Fin r → Xm) := LinearMap.pi (fun k => g0 ∘ₗ LinearMap.proj k)
  let Bop : (Fin r → Xm) →ₗ[R] (Fin r → Xm) :=
    LinearMap.pi (fun k => ∑ t, B k t • LinearMap.proj t)
  have hg : ∀ v k, g v k = g0 (v k) := fun v k => rfl
  have hBop : ∀ v k, Bop v k = ∑ t, B k t • v t := by
    intro v k
    simp [Bop, LinearMap.pi_apply, LinearMap.sum_apply]
  have hkey : ∀ v : Fin r → Xm, (fun k => ∑ t, V k t • g0 (v t)) = g v + (z * ϖ) • Bop (g v) := by
    intro v
    ext k
    rw [Pi.add_apply, Pi.smul_apply, hBop, hg, Finset.smul_sum]
    have e1 : g0 (v k) = ∑ t, (1 : Matrix (Fin r) (Fin r) R) k t • g0 (v t) := by
      simp [Matrix.one_apply]
    rw [e1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hg, smul_smul, ← hB k t, ← add_smul, Matrix.sub_apply]
    congr 1
    ring
  obtain ⟨h1, h2⟩ := unit_congruence_gives_perturbation ℓ R (Fin r → Xm) ϖ z z' hzz hc
    (fun v hv => funext fun k => hz _ (congrFun hv k)) g Bop
    (fun v hv => funext fun k => hinj _ (congrFun hv k))
    (fun v => by
      choose y hy using fun k => hsur (v k)
      exact ⟨y, funext fun k => hy k⟩)
  refine ⟨fun v hv => h1 v (by rw [← hkey]; exact hv), fun v => ?_⟩
  obtain ⟨y, hy⟩ := h2 v
  exact ⟨y, by rw [hkey]; exact hy⟩

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
