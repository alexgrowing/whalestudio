import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGenSecIffFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionFirstPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ThetaOfJet

open GlobalTheory.MBLow.JetUniq

theorem isGenSec_of_polAVSectionInverseImage {K : Type} [Field K] (x : KeyIn K)
    (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
    (h : IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th) : IsGenSec x.P.A x.P.L 1 th := by
  have e : th = TrSec.thSec x.P x.th := by
    refine NormTheta.sec_ext fun j => ?_
    obtain ⟨i, rfl⟩ : ∃ i : x.P.L.ι, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact (h i (TrSec.chart_le x.P _)).trans (TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th i (TrSec.chart_le x.P _)).symm
  subst e
  haveI : Subsingleton (Over.mk (𝟙 (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine (GenSecFibre.isGenSec_iff_fibres firstFiveLaws.2.1 (Sp K) x.P K (𝟙 _) _).2 fun p => ?_
  obtain ⟨z, -, hz⟩ := x.th_ne p
  exact ⟨_, Subsingleton.elim _ _, TrSec.nonzero_thSec x.P x.th z hz⟩

theorem ptSecT_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (z : baseOver (Sp R) ⟶ A) :
    (ptSecT A z).left = z.left ≫ toProd A := by
  rw [toProd, ← Over.comp_left, comp_lift, Category.comp_id, ptSecT]
  congr 2
  ext
  simpa using (Over.w z).symm

open GlobalTheory.MBLow.JetUniq

theorem fnOf_valR_id {K : Type} [Field K] (f : Γ(Sp K, ⊤)) : GlobalTheory.Ex.fnOf (valR (𝟙 (Sp K)) ⊤ f) = f := by
  have h : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  rw [valR, dif_pos h]
  simp [GlobalTheory.Ex.fnOf, Scheme.Hom.appLE]
  rfl

theorem isThetaPt_of_thJet : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ : I → K) (J : I → Fin g → K), ThJet x hg m pt ϑ J → IsThetaPt x.P m pt fun i => fnOf (ϑ i) := by
  intro K _ x g hg m hm hK I pt ϑ J hJ
  obtain ⟨th, hth, U, t, i₀, c, hUT, hi₀, H⟩ := hJ
  have hLaw : Laws := firstFiveLaws.1
  have hL := x.P.isLB
  let T : Over (Sp K) := baseOver (Sp K)
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ x.P m
  have e₁ : (snd T x.P.A).left ≫ (mulA x.P.A m).left = (snd T x.P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T x.P.A).left, (snd T x.P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen x.P.L ![𝟙 x.P.A.left, (mulA x.P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T x.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A T m) (snd T x.P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT x.P.A (U i).pt) (translPt x.P.A (U i).pt)
    (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) (U i).φ (U i).isGen s₁
  have ht : ∀ i, t i = s₂ i := fun i => NormTheta.sec_ext (tr_unique x.P x.rig hm (fun _ => rfl) (hUT i).1 (hUT i).1
    (hUT i).2 ⟨α, s₁, hα, hn, hs₁, hs₂ i⟩)
  let τ := rigT x.P.A x.P.L x.rig T ((m ^ 2 : ℕ) : ℤ)
  have hτ : τ.IsGen := NormTheta.rigT_isGen x.rig_gen _
  choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) 1 τ hτ
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := fun z hz => hi₀ hz
  let r : K := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val
  have hr₀ : r ≠ 0 := (isUnit_valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀)
    (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  let V₁ := (x.P.L.LinComb (fun _ : Fin 1 => (1 : T ⟶ x.P.A).left) fun _ => ((m ^ 2 : ℕ) : ℤ)).U fun _ => i₀
  let q : K := valR (𝟙 (Sp K)) V₁ (τ.s fun _ => i₀).val
  have hq₀ : q ≠ 0 := (isUnit_valR (𝟙 (Sp K)) V₁ (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  have hp : (ptSecT x.P.A (1 : T ⟶ x.P.A)).left = eSec x.P.A ≫ toProd x.P.A := by
    rw [ptSecT_left, NormTheta.one_left]
    exact congrArg (· ≫ toProd x.P.A) (Category.id_comp _)
  let j₀ : Fin g := ⟨0, hg ▸ x.g_pos⟩
  have hval : ∀ i, valR (𝟙 (Sp K)) ⊤ (w i) * q = r ^ (m ^ 2) * ϑ i := fun i => by
    have e2 := GlobalTheory.ZH.TorsReg.valR_valueAt x.P.A x.P.L _ (hw i) (𝟙 (Sp K)) i₀ (by
      rintro _ ⟨z, rfl⟩; exact k₀ trivial)
    rw [Category.id_comp, hp, ← ht i] at e2
    let V := LB.wchart x.P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) x.P.A).left) fun _ => i₀
    have e : (valR (epsLift (x.v (Fin.cast hg.symm j₀))) V ((t i).f fun _ => i₀)).fst = r ^ (m ^ 2) * ϑ i := by
      have := congrArg TrivSqZeroExt.fst (H i j₀)
      simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr,
        add_zero] at this
      exact this
    rw [epsLift_eq] at e
    erw [GlobalTheory.HolHom.valR_comp (A := DualNumber K) (x.v (Fin.cast hg.symm j₀)).left (toProd x.P.A) V] at e
    rw [fst_valR (x.basis.1 _) (le_toProd k₀)] at e
    erw [← GlobalTheory.HolHom.valR_comp (A := K) (eSec x.P.A) (toProd x.P.A) V] at e
    exact e2.symm.trans e
  have un : ∀ a : K, a ≠ 0 → IsUnit (fnOf a) := fun a ha =>
    (IsUnit.mk0 _ ha).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hmu : IsUnit (m : Γ(T.left, ⊤)) := by
    have := un m hK
    rwa [GlobalTheory.Ex.fnOf, map_natCast] at this
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ThetaSeries.isThetaPt_of_data x.P hm hmu (Nat.cast_pow m 2) th s₁ α τ U s₂ w
    (un _ (div_ne_zero hq₀ (pow_ne_zero (m ^ 2) hr₀))).unit
    ⟨isGenSec_of_polAVSectionInverseImage x th hth, hα, hτ, hs₁, fun i => (hUT i).1, hs₂, hw, fun i => ?_⟩
  rw [IsUnit.unit_spec, ← fnOf_valR_id (w i), ← map_mul]
  congr 1
  field_simp
  linear_combination (hval i).symm

end GlobalTheory.MBLow.ThetaOfJet
