import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem cst_id_eq_stalkOf {W : Type} [CommRing W] (z : Sp W) (a : W) : cst (𝟙 (Sp W)) z a = stalkOf z a :=
  gs_eq (𝟙 _) z ⊤ trivial _

open GlobalTheory.ExpansionValueZero in

theorem expandsAt_origVal : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (D' : DegData W (maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal W) D' A G) (k e : ℕ) (σ' : H0 U.LG.L k) (f' : ∀ x, D'.toPre.SecB k x) (w : D'.toPre.X → W), (∀ x, OrigVal D'.toPre (f' x) (w x)) → U.ExpandsAt e k σ' f' → ∃ S : Finset D'.toPre.X, (∀ x ∉ S, w x ∈ maximalIdeal W ^ (e + 1)) ∧ ∀ J', Good U.LG.L (cpt W) J' → ∃ c ∈ maximalIdeal W ^ (e + 1), sval σ' (unitW G) (cpt W) J' = stalkOf (cpt W) (∑ x ∈ S, w x + c) * (val U.LG.rig (idW W) (cpt W) J').val ^ k := by
  intro W _ _ _ D' A G _ _ U k e σ' f' w hw hE
  classical
  choose a ha using fun α => exists_value D'.toPre k α (f' α)
  obtain rfl : w = a := funext fun α => stalkOf_injective (cpt W) (by
    choose J hJ using fun ψ : Sp W ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (ψ (cpt W))
    have h₁ := ha α _ (𝟙 (Sp W)) (cpt W) J hJ
    have h₂ := hw α (cpt W) J hJ
    rw [cst_id_eq_stalkOf] at h₁
    rw [← Units.val_pow_eq_pow_val] at h₂
    have h₃ : sval (f' α) (𝟙 (Sp W) ≫ eSec D'.toPre.P.A) (cpt W) J = sval (f' α) (unitW D'.toPre.P.A) (cpt W) J :=
      congrArg (fun q => sval (f' α) q (cpt W) J) (Category.id_comp (unitW D'.toPre.P.A))
    exact (Units.mul_left_inj _).1 (h₂.symm.trans (h₃.symm.trans h₁)))
  obtain ⟨x, hx⟩ := exists_coeff (A := W) U.LG.isLB σ' (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (DVR.powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (J), Good U.LG.L z J →
      sval σ' (r ≫ eSec G) z J = cst r z x * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun Z r z J hJ => (hx Z r z J hJ).trans (by rw [DVR.val_pow])
  obtain ⟨S, hS⟩ := value_sub_sum_mem U e k σ' f' hE x hx' w ha
  refine ⟨S, fun y hy => ?_, fun J' hJ' => ⟨x - ∑ α ∈ S, w α, hS S le_rfl, ?_⟩⟩
  · have h := Ideal.sub_mem _ (hS S le_rfl) (hS (insert y S) (Finset.subset_insert _ _))
    rw [Finset.sum_insert hy] at h
    convert h using 1
    ring
  · have h₁ := hx' _ (𝟙 (Sp W)) (cpt W) J' hJ'
    rw [cst_id_eq_stalkOf, Units.val_pow_eq_pow_val] at h₁
    rw [add_sub_cancel]
    exact (congrArg (fun q => sval σ' q (cpt W) J') (Category.id_comp (unitW G))).symm.trans h₁

end GlobalTheory.Mum
