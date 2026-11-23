import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem pol_comp_equiv {ι : Type} [Fintype ι] (τ : ι ≃ ι) (φ : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => φ (n ∘ τ.symm)) = FibreProj.pol φ := by
  classical
  unfold FibreProj.pol
  refine Fintype.sum_equiv (Equiv.finsetCongr τ) _ _ fun S => ?_
  simp only [Equiv.finsetCongr_apply, Finset.card_map]
  congr 2
  funext j
  simp only [Function.comp_apply, Finset.mem_map_equiv]

theorem mixArch_iso_symm_congr : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → mixArch L M hr = mixArch L' M hr) ∧ (∀ τ : Equiv.Perm (Fin e), mixArch (fun a => L (τ a)) M hr = mixArch L M hr) ∧ ∀ (M' : HermLB q) (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), M'.div hr' = M.div hr → (∀ σ, Set.EqOn (logNorm (M'.φ σ) r') (logNorm (M.φ σ) r) (offSupp q σ (M.div hr))) → mixArch L M' hr' = mixArch L M hr := by
  intro k _ Y _ q e L M r hr
  refine ⟨fun L' hL => ?_, fun τ => ?_, fun M' r' hr' hd hn => ?_⟩
  · have h : ∀ n, (comb L n).archInt M e hr = (comb L' n).archInt M e hr := fun n =>
      by simp only [HermLB.archInt, (isometric_comb_congr hL n).chernInt_eq]
    simp only [mixArch, h]
  · have h : ∀ n, (comb (fun a => L (τ a)) (n ∘ τ)).archInt M e hr = (comb L n).archInt M e hr := fun n => by
      have iso : (comb (fun a => L (τ a)) (n ∘ τ)).Isometric (comb L n) := by
        refine HermLB.icls_eq_iff.1 ?_
        rw [icls_comb, icls_comb]
        exact Fintype.sum_equiv τ _ _ fun a => by simp
      simp only [HermLB.archInt, iso.chernInt_eq]
    simp only [mixArch]
    rw [← pol_comp_equiv τ.symm (fun n => (comb (fun a => L (τ a)) n).archInt M e hr)]
    simp only [Equiv.symm_symm, h]
  · have h : ∀ n, (comb L n).archInt M' e hr' = (comb L n).archInt M e hr := fun n => by
      simp only [HermLB.archInt, hd]
      exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (hn σ)
    simp only [mixArch, h]

end GlobalTheory.MixHt
