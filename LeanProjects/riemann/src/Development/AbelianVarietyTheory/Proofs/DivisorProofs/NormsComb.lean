import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalizationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y}

theorem norms_zp {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (m : ℤ) :
    Norms V (ArInt.zp L m) (fun x => f x ^ m) (fun σ y => m * a σ y) (fun v e y => m * l v e y) := by
  have h₁ := GlobalTheory.T.norms_tensor_power F Y V L f a l m.toNat h
  have h₂ := GlobalTheory.T.norms_dual_bundle F Y V _ _ _ _ (GlobalTheory.T.norms_tensor_power F Y V L f a l (-m).toNat h)
  refine (GlobalTheory.T.norms_tensor_product F Y V _ _ _ _ _ _ _ _ h₁ h₂).congr (fun x => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · rcases m with n | n
    · simp
    · rw [zpow_negSucc]
      have : (Int.negSucc n).toNat = 0 := rfl
      have h' : (-Int.negSucc n).toNat = n + 1 := rfl
      rw [this, h', pow_zero, one_mul]
  · have := Int.toNat_sub_toNat_neg m
    have hE : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = m := by exact_mod_cast this
    linear_combination a σ y * hE
  · have := Int.toNat_sub_toNat_neg m
    have hE : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = m := by exact_mod_cast this
    linear_combination l v e y * hE

theorem norms_comb {ι : Type} [Fintype ι] {L : ι → HermLB V.p} {f : ι → Y.X → Y.Fn} {a : ι → ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ι → ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : ∀ i, Norms V (L i) (f i) (a i) (l i)) (n : ι → ℤ) :
    Norms V (ArInt.comb L n) (fun x => ∏ i, f i x ^ n i) (fun σ y => ∑ i, (n i : ℝ) * a i σ y)
      (fun v e y => ∑ i, (n i : ℝ) * l i v e y) := by
  have key : ∀ s : List ι, Norms V (s.foldr (fun i M => (ArInt.zp (L i) (n i)).tens M) (HermLB.triv V.p))
      (fun x => (s.map fun i => f i x ^ n i).prod) (fun σ y => (s.map fun i => (n i : ℝ) * a i σ y).sum)
      (fun v e y => (s.map fun i => (n i : ℝ) * l i v e y).sum) := by
    intro s
    induction s with
    | nil => exact (GlobalTheory.T.conjugate_weight_smooth_normalization F Y V).1
    | cons i s ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, List.sum_cons]
      exact GlobalTheory.T.norms_tensor_product F Y V _ _ _ _ _ _ _ _ (norms_zp (h i) (n i)) ih
  refine (key Finset.univ.toList).congr (fun x => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · exact Finset.prod_map_toList _ _
  · exact Finset.sum_map_toList _ _
  · exact Finset.sum_map_toList _ _

end GlobalTheory.CoverNorm
