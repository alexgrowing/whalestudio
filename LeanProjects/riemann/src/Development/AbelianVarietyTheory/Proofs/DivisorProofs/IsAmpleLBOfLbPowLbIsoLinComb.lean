import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmple

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePowLinComb

open GlobalTheory.CechPic

def genClasses (X : Scheme.{0}) : AddSubmonoid (Pic X) where
  carrier := {c | ∃ (A : LB X) (hA : A.IsLB), IsGenerated A ∧ cls A hA = c}
  zero_mem' := ⟨_, LB.isLB_triv X, isGenerated_triv X, rfl⟩
  add_mem' := by
    rintro _ _ ⟨A, hA, gA, rfl⟩ ⟨B, hB, gB, rfl⟩
    exact ⟨tens A B, isLB_tens hA hB, AmpleModelPos.isGenerated_tens gA gB, cls_tens hA hB _⟩

theorem isAmpleLB_of_lbPow_lbIso_linComb : ∀ (X : Scheme.{0}) (L M : LB X), IsAmpleLB M → L.IsLB →
    ∀ (N a₀ r : ℕ) (a : Fin r → ℕ) (β : Fin r → (X ⟶ X)), 1 ≤ N → 1 ≤ a₀ →
    LBIso (lbPow L N) (LB.LinComb M (K := Option (Fin r)) (fun o => o.elim (𝟙 X) fun i => β i)
      fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) → IsAmpleLB L := by
  intro X L M hM hL N a₀ r a β hN ha₀ H
  obtain ⟨k, hk, gk⟩ := hM.exists_isGenerated_pow
  have hMk := isLB_lbPow hM.isLB k

  set c : Pic X := ∑ i, a i • pull (β i) (cls _ hMk) with hc
  have hcmem : c ∈ genClasses X := by
    refine AddSubmonoid.sum_mem _ fun i _ => AddSubmonoid.nsmul_mem _ ?_ _
    exact ⟨_, pull_isLB hMk (β i), gk.pull (β i), cls_pull hMk (β i) _⟩
  obtain ⟨A, hA, gA, hAc⟩ := hcmem
  have hLN := isLB_lbPow hL (N * k)
  have hMa := isLB_lbPow hM.isLB (a₀ * k)
  have hAmp : IsAmpleLB (lbPow M (a₀ * k)) :=
    (isAmpleLB_pow_iff hM.isLB (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).2 hM
  have h₁ := LB.isLB_div hLN hMa
  have h₂ := LB.isLB_div h₁ hA
  have hLpow : IsAmpleLB (lbPow L (N * k)) := hAmp.tensor_isGenerated gA hLN ((cls_eq_zero_iff h₂).1 ?_)
  · exact (isAmpleLB_pow_iff hL (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).1 hLpow
  have hE := (cls_eq_iff (isLB_lbPow hL N) (LB.isLB_linComb hM.isLB _ _)).2 H
  rw [cls_lbPow hL, cls_linComb hM.isLB, Fintype.sum_option] at hE
  rw [cls_div h₁ hA, cls_div hLN hMa, hAc, hc, cls_lbPow hL, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  simp only [Option.elim, pull_id] at hE
  simp only [map_nsmul]
  have e1 : (N * k) • cls L hL = k • (N • cls L hL) := by rw [smul_smul, mul_comm]
  rw [e1, hE]
  simp only [natCast_zsmul, smul_add, Finset.smul_sum, smul_smul]
  rw [sub_sub, sub_eq_zero, mul_comm a₀ k]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

end GlobalTheory.AmplePowLinComb
