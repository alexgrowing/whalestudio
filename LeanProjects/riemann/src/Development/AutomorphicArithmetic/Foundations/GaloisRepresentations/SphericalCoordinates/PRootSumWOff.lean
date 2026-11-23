import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2
open scoped Classical

namespace UpperTheory.Gal.W2.RootOff

open UpperTheory.Gal.Schur

private theorem rts_conj {F : Type} [Field F] [NumberField F] (χ : F[X]) (τ : F →+* ℂ) :
    rts χ τ = (rts χ (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ) := by
  have h : rts χ (ComplexEmbedding.conjugate τ) = (rts χ τ).map (starRingEnd ℂ) := by
    unfold rts
    have e : χ.map (ComplexEmbedding.conjugate τ) = (χ.map τ).map (starRingEnd ℂ) := by
      rw [Polynomial.map_map]
      congr 1
    rw [e, (IsAlgClosed.splits (χ.map τ)).roots_map]
  rw [h, Multiset.map_map]
  conv_lhs => rw [← Multiset.map_id (rts χ τ)]
  congr 1
  funext z
  simp

private theorem ball_eq {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ : F →+* ℂ) (χ : F[X])
    (g₀ g₁ : Fin n → ℂ) (y q : ℂ) (hr : rts χ t₀ = Finset.univ.val.map g₀)
    (hi : Function.Injective g₀) (h0 : ∀ k, g₀ k ≠ 0) (h1 : ∀ k, g₁ k ≠ 0)
    (hq : ∀ k, g₀ k * g₁ k = q) (i : Fin n) :
    ballW t₀ y χ (g₀ i) =
      ∏ j ∈ Finset.univ.erase i, ((g₁ i - y * g₁ j) * Ring.inverse (g₁ i - g₁ j)) := by
  have hqne : q ≠ 0 := by
    rw [← hq i]
    exact mul_ne_zero (h0 i) (h1 i)
  have hg : ∀ k, g₀ k = q / g₁ k := by
    intro k
    rw [← hq k]
    field_simp [h1 k]
  unfold ballW
  rw [hr, ← Multiset.map_erase _ hi, ← Finset.erase_val, Multiset.map_map, Finset.prod_map_val]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hne : g₁ i - g₁ j ≠ 0 := by
    intro h
    apply hji
    apply hi
    rw [hg, hg, sub_eq_zero.mp h]
  simp only [Function.comp, Ring.inverse_eq_inv']
  rw [hg j, hg i]
  have hj1 := h1 j
  have hi1 := h1 i
  have hden : q / g₁ j - q / g₁ i ≠ 0 := by
    rw [div_sub_div _ _ hj1 hi1]
    refine div_ne_zero ?_ (mul_ne_zero hj1 hi1)
    rw [mul_comm (g₁ j) q, ← mul_sub]
    exact mul_ne_zero hqne hne
  rw [div_eq_iff hden]
  field_simp

private theorem fib_eq {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ t₁ : F →+* ℂ)
    (ht₁ : t₁ = ComplexEmbedding.conjugate t₀) (hne : t₀ ≠ t₁) (ε : (F →+* ℂ) → ℕ) (χ : F[X])
    (g : (F →+* ℂ) → Fin n → ℂ) (y : ℂ) (x : F)
    (hr : ∀ τ, rts χ τ = Finset.univ.val.map (g τ))
    (hi : Function.Injective (g t₀)) (hc : ∀ k, g t₁ k = (starRingEnd ℂ) (g t₀ k)) (i : Fin n) :
    fibW t₀ ε x y χ (g t₀ i) = ∏ τ, detOne (τ x) (twist t₀ t₁ ε y i g τ) := by
  subst ht₁
  have herase : ∀ f : ℂ → ℂ, (Multiset.map f ((rts χ t₀).erase (g t₀ i))).prod
      = ∏ j ∈ Finset.univ.erase i, f (g t₀ j) := by
    intro f
    rw [hr, ← Multiset.map_erase _ hi, ← Finset.erase_val, Multiset.map_map, Finset.prod_map_val]
    rfl
  have hA : detOne (t₀ x) (twist t₀ (ComplexEmbedding.conjugate t₀) ε y i g t₀)
      = (1 - t₀ x * (y * g t₀ i)) * ∏ j ∈ Finset.univ.erase i, (1 - t₀ x * g t₀ j) := by
    unfold detOne twist scaleAt
    rw [if_pos rfl, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  have hB : detOne ((ComplexEmbedding.conjugate t₀) x) (twist t₀ (ComplexEmbedding.conjugate t₀) ε y i g (ComplexEmbedding.conjugate t₀))
      = (1 - (starRingEnd ℂ) (t₀ x) * (starRingEnd ℂ) (g t₀ i)) *
        ∏ j ∈ Finset.univ.erase i, (1 - (starRingEnd ℂ) (t₀ x) * (y * (starRingEnd ℂ) (g t₀ j))) := by
    unfold detOne twist scaleOff
    rw [if_neg (Ne.symm hne), if_pos rfl, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl,
      ComplexEmbedding.conjugate_coe_eq, hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj), hc]
  have hC : ∀ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀),
      detOne (τ x) (twist t₀ (ComplexEmbedding.conjugate t₀) ε y i g τ)
        = (Multiset.map (fun r => 1 - τ x * (y ^ ε τ * r)) (rts χ τ)).prod := by
    intro τ hτ
    have h1 := Finset.ne_of_mem_erase hτ
    have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)
    unfold detOne twist
    rw [if_neg h2, if_neg h1, hr τ, Multiset.map_map, Finset.prod_map_val]
    rfl
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t₀),
    ← Finset.mul_prod_erase (Finset.univ.erase t₀) _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩),
    hA, hB, Finset.prod_congr rfl hC]
  unfold fibW
  rw [herase, herase]
  ring

end UpperTheory.Gal.W2.RootOff

theorem UpperTheory.Gal.W2.rootSumWOff_of :
    UpperTheory.Gal.W2.RootSumWOff := by
  intro F _ _ n t₀ ε lam m hconj hlam
  obtain ⟨k₀, hk₀⟩ := UpperTheory.Gal.Schur.FibreSum_holds F ℂ n lam
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨c, hcs, hc⟩ := hk₀ k hk 2 two_ne_zero ∅
  refine ⟨c, fun α hα s => ⟨(hcs α hα s).1, (hcs α hα s).2.1⟩, ?_⟩
  intro χ r hsep hr hc0 hqe y
  obtain ⟨q, hq⟩ := hqe
  set t₁ := ComplexEmbedding.conjugate t₀ with ht₁
  have hne : t₀ ≠ t₁ := Ne.symm hconj
  let g : (F →+* ℂ) → Fin n → ℂ := fun τ => if τ = t₀ then (fun k => starRingEnd ℂ (r t₁ k)) else r τ
  have hg0 : g t₀ = fun k => starRingEnd ℂ (r t₁ k) := if_pos rfl
  have hg1 : ∀ τ, τ ≠ t₀ → g τ = r τ := fun τ h => if_neg h
  have hrg : ∀ τ, rts χ τ = Multiset.map (g τ) Finset.univ.val := by
    intro τ
    by_cases h : τ = t₀
    · rw [h, hg0, RootOff.rts_conj χ t₀, hr, Multiset.map_map]
      rfl
    · rw [hg1 τ h]
      exact hr τ
  have hinj : ∀ τ, Function.Injective (g τ) := by
    intro τ a b hab
    have hnd : (rts χ τ).Nodup := Polynomial.nodup_roots (hsep.map)
    rw [hrg τ] at hnd
    exact Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  have hmem : ∀ τ k, g τ k ∈ rts χ τ := by
    intro τ k
    rw [hrg τ]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ k)
  have hnz : ∀ τ k, g τ k ≠ 0 := by
    intro τ k h0
    have hm := hmem τ k
    unfold rts at hm
    rw [Polynomial.mem_roots', h0] at hm
    obtain ⟨_, hroot⟩ := hm
    apply hc0
    have hz := hroot.eq_zero
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at hz
    exact (map_eq_zero τ).mp hz
  have hcc : ∀ k, g t₁ k = starRingEnd ℂ (g t₀ k) := by
    intro k
    rw [hg1 t₁ hconj, hg0]
    simp
  have hq' : ∀ k, g t₀ k * g t₁ k = (q : ℂ) := by
    intro k
    rw [hcc k]
    exact hq _ (hmem t₀ k)
  have hunit : ∀ i j : Fin n, j ≠ i → IsUnit (g t₁ j - g t₁ i) :=
    fun i j h => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun e => h (hinj t₁ e)))
  have key := (hc ℂ t₀ t₁ hne ε m g y).2 hlam hunit
  have hsch : ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ) = ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (g τ) := by
    apply Finset.prod_congr rfl
    intro τ _
    by_cases h : τ = t₀
    · have hl : lam τ = fun i => (fun _ => 0) i + m := by
        funext i
        simp [h, hlam]
      have e1 : (rts χ t₀).prod = ∏ k, r t₀ k := by
        rw [hr]
        exact Finset.prod_map_val _ _
      have e2 : (rts χ t₀).prod = ∏ k, g t₀ k := by
        rw [hrg]
        exact Finset.prod_map_val _ _
      rw [hl, (UpperTheory.Gal.Schur.SchurDet_holds ℂ n (r τ)).2 _ m, (UpperTheory.Gal.Schur.SchurDet_holds ℂ n (g τ)).2 _ m,
        (UpperTheory.Gal.Schur.SchurDet_holds ℂ n (r τ)).1, (UpperTheory.Gal.Schur.SchurDet_holds ℂ n (g τ)).1, h, ← e1, ← e2]
    · rw [hg1 τ h]
  rw [hsch, ← key]
  apply Finsupp.sum_congr
  intro α _
  rw [smul_eq_mul]
  congr 1
  rw [hrg t₀, Multiset.map_map, Finset.sum_map_val]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp, locW]
  rw [RootOff.ball_eq t₀ χ (g t₀) (g t₁) y q (hrg t₀) (hinj t₀) (hnz t₀) (hnz t₁) hq' i]
  have hf : ∀ s, fibW t₀ ε (↑(α s)) y χ (g t₀ i)
      = ∏ τ, UpperTheory.Gal.Schur.detOne (τ ↑(α s)) (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ) :=
    fun s => RootOff.fib_eq t₀ t₁ rfl hne ε χ g y _ hrg (hinj t₀) hcc i
  rw [Finset.prod_congr rfl (fun s _ => hf s), Finset.prod_comm]
  exact mul_comm _ _
