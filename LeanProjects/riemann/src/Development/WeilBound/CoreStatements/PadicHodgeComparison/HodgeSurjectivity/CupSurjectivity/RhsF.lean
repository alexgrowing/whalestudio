import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.CastTRfl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.T2a
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.GenPb

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem eid (hC : CupLaws) (hS : Slant) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {d : ℕ} (Dt : Dat hC P M d)
    {a' n : ℕ} (x : Hdg M.q a' n) {α : ℕ} (φ' : Module.Dual K (Hdg M.q α (2 + 2 * d))) :
    lhsF hC P Dt x φ' = rhsF hC P Dt x φ' := by
  funext β ψ
  have hL : lhsF hC P Dt x φ' β ψ =
      (∑ s, if h : 0 = n then kap hC P x φ' (Dt.a₀ s) * P.h M β n (M.toV n (castT h (Dt.b₀ s))) ψ else 0) +
      ∑ s, if h : Dt.j s = n then kap hC P x φ' (Dt.a s) * P.h M β n (M.toV n (castT h (Dt.b s))) ψ else 0 := by
    simp only [lhsF, Pi.add_apply, Finset.sum_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun s _ => ?_ <;> split_ifs <;> rfl
  rw [hL]
  simp only [rhsF]
  by_cases hlt : a' ≤ α + β
  · obtain ⟨A, hA⟩ : ∃ A, α + β = A + a' := ⟨α + β - a', by omega⟩
    have hPM := sm_gen hM
    have := hPM.1
    have := hPM.2
    obtain ⟨sl, hsl⟩ := slantR hS K M.gen M.gen Dt.S.P.gen M.q M.q (Model.genMap Dt.S.p₁ Dt.S.h₁)
      (Model.genMap Dt.S.p₂ Dt.S.h₂) (gen_pb _ _ _ _ Dt.S.prod) Dt.S.P.q (Model.genMap_q _ _) (Model.genMap_q _ _)
      α (2 + 2 * d) β n (A + a') (2 + 2 * d + n) hA rfl φ'
    have hsl' : IsSl Dt.S hA φ' sl := hsl
    have hy : pullH (Model.genMap Dt.S.Δ Dt.S.hΔ) (Model.genMap_q Dt.S.Δ Dt.S.hΔ) a' n
        (Dt.S.pl₁ a' n x - Dt.S.pl₂ a' n x) = 0 := by
      rw [map_sub, sub_eq_zero]
      have c7 := (hC K M.gen M.q).2.2.2.2.2.2
      rw [c7 _ _ _ _ _ _ _ _ (𝟙 _) (Category.id_comp _) (gen_sec _ _ _ _ Dt.S.Δ₁) a' n x,
        c7 _ _ _ _ _ _ _ _ (𝟙 _) (Category.id_comp _) (gen_sec _ _ _ _ Dt.S.Δ₂) a' n x]
    have hk := Dt.kill A a' n _ hy (ψ ∘ₗ sl)
    have split : (ψ ∘ₗ sl) ∘ₗ (cupL hC Dt.S.P.q (a := A) (a' := a') (i := 2 + 2 * d) (j := n) rfl rfl).flip
        (Dt.S.pl₁ a' n x - Dt.S.pl₂ a' n x) = th hC Dt.S sl ψ (Dt.S.pl₁ a' n x) - th hC Dt.S sl ψ (Dt.S.pl₂ a' n x) := by
      ext C
      simp [th]
    rw [split, map_sub, sub_eq_zero, Dt.dec] at hk
    simp only [map_add, map_sum, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply] at hk
    have e1 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (Dt.ab₀ s)) (th hC Dt.S sl ψ (Dt.S.pl₁ a' n x)) =
        if h : 0 = n then kap hC P x φ' (Dt.a₀ s) * P.h M β n (M.toV n (castT h (Dt.b₀ s))) ψ else 0 :=
      fun s => t1 hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a₀ s) (Dt.b₀ s) (Dt.ab₀ s) (Dt.cup₀ s) rfl
    have e2 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (castT (Dt.hij s) (Dt.ab s)))
        (th hC Dt.S sl ψ (Dt.S.pl₁ a' n x)) =
        if h : Dt.j s = n then kap hC P x φ' (Dt.a s) * P.h M β n (M.toV n (castT h (Dt.b s))) ψ else 0 :=
      fun s => t1 hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a s) (Dt.b s) (Dt.ab s) (Dt.cup s) (Dt.hij s)
    have f1 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (Dt.ab₀ s)) (th hC Dt.S sl ψ (Dt.S.pl₂ a' n x)) =
        P.h M α _ (M.toV _ (Dt.a₀ s)) φ' * P.h M 0 0 (M.toV 0 (Dt.b₀ s)) (Gx hC x ψ) :=
      fun s => t2z hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a₀ s) (Dt.b₀ s) (Dt.ab₀ s) (Dt.cup₀ s)
    have f2 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (castT (Dt.hij s) (Dt.ab s)))
        (th hC Dt.S sl ψ (Dt.S.pl₂ a' n x)) = 0 :=
      fun s => t2a hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a s) (Dt.b s) (Dt.ab s) (Dt.cup s) (Dt.hij s) (Dt.jne s)
    simp only [e1, e2, f1, f2, Finset.sum_const_zero, add_zero] at hk
    exact hk
  · have hk : ∀ {i : ℕ} (X : M.T i), kap hC P x φ' X = 0 := by
      intro i X
      rw [kap, Fx, dif_neg (fun h => hlt (by omega)), map_zero, smul_zero]
    have hg : Gx hC x ψ = 0 := by
      rw [Gx, dif_neg (by omega)]
    simp only [hk, hg, zero_mul, map_zero, mul_zero, dite_eq_ite, ite_self, Finset.sum_const_zero, add_zero]

end CrystallineSemistableComparison.Onto

end
