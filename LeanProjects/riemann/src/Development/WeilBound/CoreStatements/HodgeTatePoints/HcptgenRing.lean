import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor

noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem aeval_scale {σ K R A : Type} [Fintype K] [CommRing R] [CommRing A] [Algebra R A] (w : σ → K → ℕ)
    (c : K → A) (z : σ → A) {f : MvPolynomial σ R} {d : K → ℕ} (hf : IsWeightedHomogeneous w f d) :
    aeval (fun p => (∏ k, c k ^ w p k) * z p) f = (∏ k, c k ^ d k) * aeval z f := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => rw [map_add, map_add, hp, hq, mul_add]
  | monomial m r hm =>
    rw [aeval_monomial, aeval_monomial, ← hm]
    have e : (∏ k, c k ^ (Finsupp.weight w m) k) = m.prod fun p n => (∏ k, c k ^ w p k) ^ n := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow,
        ← pow_mul, mul_comm]
      exact Finset.prod_comm
    rw [e]
    simp only [mul_pow, Finsupp.prod_mul]
    ring

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K] {J : K → Type}

theorem ratio_eq [DecidableEq K] (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) (k : K) (i : J k) :
    y ⟨k, i⟩ / y ⟨k, s k⟩ = mseg y (Function.update s k i) / mseg y s := by
  have hk : y ⟨k, s k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  rw [div_eq_div_iff hk hs]
  unfold mseg
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    Function.update_self]
  have e : ∏ j ∈ Finset.univ.erase k, y ⟨j, Function.update s k i j⟩ = ∏ j ∈ Finset.univ.erase k, y ⟨j, s j⟩ :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [e]
  ring

open GroundTheory.Heights₂.Heights.NumbersDVR in

theorem chartRing_mseg (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) :
    chartRing o (mseg y) s = Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) := by
  classical
  refine le_antisymm (fun u hu => ?_) (Algebra.adjoin_le ?_)
  · have hk : ∀ k, y ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
    obtain ⟨n, U, hU, hv⟩ := GenericProjClosureDivisor.chart_form (O := o) (Φ := Ω) y (Pi.basisFun Ω (Fin 0))
      (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 s hs hu
    let c : Option (Option K) → Ω := fun b => b.elim 1 fun b' => b'.elim 1 fun k => y ⟨k, s k⟩
    let z : (Σ b, bundleIdx (bundleIdx J 0) 0 b) → Ω := fun p =>
      pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 p / c p.1
    have hc : ∀ b, c b ≠ 0 := by
      rintro (_ | _ | k)
      · exact one_ne_zero
      · exact one_ne_zero
      · exact hk k
    have h := aeval_scale _ c z hU
    have e1 : (fun p => (∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b) * z p) =
        pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 := by
      funext p
      have : ∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b = c p.1 := by
        rw [Finset.prod_eq_single p.1]
        · simp [blockWeight]
        · intro b _ hb
          simp [blockWeight, Pi.single_eq_of_ne hb]
        · simp
      rw [this]
      exact mul_div_cancel₀ _ (hc _)
    have e2 : ∏ b, c b ^ GenericProjClosureDivisor.vdeg (fun _ : K => n) b = segreVec y s ^ n := by
      simp [Fintype.prod_option, c, GenericProjClosureDivisor.vdeg, segreVec, Finset.prod_pow]
    rw [e1, e2, hv, Algebra.algebraMap_self_apply, mul_comm] at h
    have hu' : u = aeval z U := mul_left_cancel₀ (pow_ne_zero n hs) h
    have hz : aeval z U ∈ Algebra.adjoin o (Set.range z) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨U, rfl⟩
    rw [hu']
    refine Algebra.adjoin_mono ?_ hz
    rintro _ ⟨⟨_ | _ | k, i⟩, rfl⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · exact ⟨Function.update s k i, (ratio_eq y s hs k i).symm⟩
  · rintro _ ⟨j, rfl⟩
    exact div_mem_chartRing _ _ _

end PositivityTheory.HtPt.Hcptgen
