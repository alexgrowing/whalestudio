import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCupOneFormsZeroImpCoordinatesZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSumClosedGlobalOneFormsEqZeroIffSumWedgeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2GeneratedByCupsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgeGlobalOneFormsEqZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareKerOfSurjectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Wedge

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem update_pair_vector_zero (a b x : M) : Function.update ![a, b] 0 x = ![x, b] := by
  funext i; fin_cases i <;> simp

theorem update_pair_vector_one (a b x : M) : Function.update ![a, b] 1 x = ![a, x] := by
  funext i; fin_cases i <;> simp

def ιTwo : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 0 a a'
      simpa only [update_pair_vector_zero] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 0 r a
      simpa only [update_pair_vector_zero] using h)
    (fun a b b' ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 1 b b'
      simpa only [update_pair_vector_one] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 1 r b
      simpa only [update_pair_vector_one] using h)

theorem ιTwo_apply (a b : M) : ιTwo a b = exteriorPower.ιMulti R 2 ![a, b] := by
  rw [ιTwo, LinearMap.mk₂_apply]

theorem ιTwo_self (a : M) : ιTwo (R := R) a a = 0 := by
  rw [ιTwo_apply]
  exact (exteriorPower.ιMulti R 2 (M := M)).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)

theorem ιTwo_swap (a b : M) : ιTwo (R := R) b a = -ιTwo a b := by
  have h := ιTwo_self (R := R) (a + b)
  simp only [map_add, LinearMap.add_apply, ιTwo_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem sum_sum_ιTwo_of_symm {n : ℕ} (x : Fin n → M) (c : Fin n → Fin n → R)
    (hc : ∀ a b, c a b = c b a) : ∑ a, ∑ b, c a b • ιTwo (R := R) (x a) (x b) = 0 := by
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun a b ↦ c a b • ιTwo (R := R) (x a) (x b))]
  refine Finset.sum_involution (fun p _ ↦ p.swap) (fun p _ ↦ ?_) (fun p _ hp ↦ ?_)
    (fun p _ ↦ by simp) (fun p _ ↦ Prod.swap_swap p)
  · simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hc p.2 p.1, ιTwo_swap (x p.1), smul_neg, add_neg_cancel]
  · intro he
    apply hp
    have : p.1 = p.2 := (Prod.ext_iff.1 he).2
    simp only [this, ιTwo_self, smul_zero]

end Wedge

section Forget

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fnZZ2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hypercohomologyTwoToAlgebraCohomology : Hyp2 F →ₗ[R] CatCoh.H2 F :=
  Submodule.mapQ _ _ (fnZZ2 F) (by rintro _ ⟨e, rfl⟩; exact ⟨e.1, rfl⟩)

theorem hypercohomologyTwo_cup_forget_forms (a b : Hyp1 F) : hypercohomologyTwoToAlgebraCohomology F (cupHyp F a b) = cup F (toO F a) (toO F b) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rfl

def cupProductWedge (halt : ∀ a, cupHyp F a a = 0) : Hyp1 F [⋀^Fin 2]→ₗ[R] Hyp2 F where
  toFun v := cupHyp F (v 0) (v 1)
  map_update_add' v i a b := by fin_cases i <;> simp
  map_update_smul' v i r a := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all

def cupWedge (halt : ∀ a, cupHyp F a a = 0) : ⋀[R]^2 (Hyp1 F) →ₗ[R] Hyp2 F :=
  exteriorPower.alternatingMapLinearEquiv (cupProductWedge F halt)

theorem cupWedge_ιTwo (halt : ∀ a, cupHyp F a a = 0) (a b : Hyp1 F) :
    cupWedge F halt (ιTwo a b) = cupHyp F a b := by
  rw [ιTwo_apply, cupWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem exact_clAll_toO (hc : Closed1 F = ⊤) : Function.Exact (clAll F hc) (toO F) := by
  intro y
  constructor
  · intro hy
    have h : y ∈ Fil1 F := hy
    rw [Fil1_eq_range] at h
    obtain ⟨ω, rfl⟩ := h
    exact ⟨ω.1, rfl⟩
  · rintro ⟨w, rfl⟩
    have h : clAll F hc w ∈ Fil1 F := by
      rw [Fil1_eq_range]; exact ⟨_, rfl⟩
    exact h

end Forget

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem exists_wedge_hyp_equiv : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F →
    (∀ a, cupHyp F a a = 0) → ∃ e : ⋀[R]^2 (Hyp1 F) ≃ₗ[R] Hyp2 F,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := by
  intro R _ C _ F hF h0 hc hs hw halt
  let e₀ := cupWedge F halt
  have e₀_ι : ∀ a b, e₀ (ιTwo a b) = cupHyp F a b := cupWedge_ιTwo F halt
  have hsurj : Function.Surjective e₀ := by
    intro z
    obtain ⟨n, a, b, rfl⟩ := GlobalTheory.T.hyper_h2_generated_by_cups R C F hF h0 hc hs hw z
    exact ⟨∑ k, ιTwo (a k) (b k), by simp only [map_sum, e₀_ι]⟩
  have hex := exact_clAll_toO F hc
  have hinj : Function.Injective e₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    obtain ⟨ew, hew⟩ := hw

    have hcomm : ew.toLinearMap ∘ₗ exteriorPower.map 2 (toO F) = hypercohomologyTwoToAlgebraCohomology F ∘ₗ e₀ := by
      refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
      have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
      have hv' : (toO F) ∘ v = ![toO F (v 0), toO F (v 1)] := by funext i; fin_cases i <;> rfl
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, exteriorPower.map_apply_ιMulti, hv', hew]
      rw [hv, ← ιTwo_apply, e₀_ι, hypercohomologyTwo_cup_forget_forms]
      rfl
    have h1 : exteriorPower.map 2 (toO F) t = 0 := by
      apply ew.injective
      have := LinearMap.congr_fun hcomm t
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
      rw [this, ht, map_zero, map_zero]
    obtain ⟨m, a, w, rfl⟩ := GlobalTheory.T.exists_sum_ιMulti_of_exteriorSquare_map_eq_zero R (Glob1 F) (Hyp1 F) (CatCoh.H1 F) (clAll F hc) (toO F) hs hex t h1
    simp only [← ιTwo_apply] at ht ⊢
    have hsum : ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 := by
      simpa only [map_sum, e₀_ι] using ht
    obtain ⟨N, ⟨Φ⟩⟩ := hF
    obtain ⟨l, -, hl⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 N Φ
    let x : Fin N → Hyp1 F := fun i ↦ clAll F hc (Φ.w i)
    have hcl : ∀ v : Glob1 F, clAll F hc v = ∑ i, l i v • x i := by
      intro v
      conv_lhs => rw [hl v]
      simp only [map_sum, map_smul, x]

    let Mi : Fin N → Hyp1 F := fun i ↦ ∑ k, l i (w k) • a k
    have ht1 : ∑ k, ιTwo (R := R) (a k) (clAll F hc (w k)) = ∑ i, ιTwo (Mi i) (x i) := by
      simp only [hcl, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Mi]
      exact Finset.sum_comm
    have hM0 : ∀ i, toO F (Mi i) = 0 := by
      intro i
      have := GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero R C F ⟨N, ⟨Φ⟩⟩ h0 hc hs m a w hsum (l i)
      simpa only [Mi, map_sum, map_smul] using this
    have hMu : ∀ i, ∃ u, clAll F hc u = Mi i := fun i ↦ (hex (Mi i)).1 (hM0 i)
    choose u hu using hMu
    rw [ht1]
    simp only [← hu]
    have hcup : ∑ i, cupHyp F (clAll F hc (u i)) (clAll F hc (Φ.w i)) = 0 := by
      rw [← ht, ht1]
      simp only [← hu, map_sum, e₀_ι, x]
    have hw2 := (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R C F hc hs N u Φ.w).1 hcup
    have hsym := (GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff R C F ⟨N, ⟨Φ⟩⟩ h0 N u Φ.w).1 hw2
    let c : Fin N → Fin N → R := fun p q ↦ ∑ i, l p (u i) * l q (Φ.w i)
    have hc' : ∀ p q, c p q = c q p := by
      intro p q
      have := hsym (l p) (l q)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c]
      rw [this]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    have step : ∀ i, ιTwo (R := R) (clAll F hc (u i)) (x i) =
        ∑ p, ∑ q, (l p (u i) * l q (Φ.w i)) • ιTwo (R := R) (x p) (x q) := by
      intro i
      rw [hcl (u i)]
      conv_lhs => rw [show x i = ∑ q, l q (Φ.w i) • x q from hcl (Φ.w i)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by rw [mul_comm]
    have hexp : ∑ i, ιTwo (R := R) (clAll F hc (u i)) (x i) = ∑ p, ∑ q, c p q • ιTwo (R := R) (x p) (x q) := by
      simp only [step]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp only [c, Finset.sum_smul]
    rw [hexp]
    exact sum_sum_ιTwo_of_symm x c hc'
  refine ⟨LinearEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun a b ↦ ?_⟩
  have := e₀_ι a b
  rw [ιTwo_apply] at this
  exact this

end GlobalTheory.AbCoh
