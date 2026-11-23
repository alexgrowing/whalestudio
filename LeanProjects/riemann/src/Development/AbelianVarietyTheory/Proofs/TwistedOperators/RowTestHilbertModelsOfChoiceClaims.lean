import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThThGAct

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim

namespace GlobalTheory.RowTestFromClaims

open GlobalTheory.RowTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_gE (R : RealDat D A Ks) (hE : R.models_HE) (hg : R.models_gE) (y : R.HE.H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  have hmem : R.HE.e y ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ _
  have hfix := ((mem_goodPart _ _ _ _ _ _).1 hmem).2
  apply hE.1
  rw [map_sum]
  simp_rw [map_smul, hg]
  ext v
  rw [← hfix v]
  simp only [RealDat.e0, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.sum_apply, MultilinearMap.smul_apply, postOn_apply]
  rfl

theorem rat_of_formula {K : Type} [Field K] (σ : K →+* ℂ) {z : K} {c c₀ κ p w : ℂ} (hz : σ z ≠ 0) (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (hκ : κ ≠ 0) (h : σ z * c * p = κ * w) (hw : w ∈ Set.range σ) (hr : c / c₀ ∈ Set.range σ) : ∃ y, σ y = c₀ * κ⁻¹ * p := by
  obtain ⟨w', rfl⟩ := hw
  obtain ⟨r', hr'⟩ := hr
  refine ⟨w' / (z * r'), ?_⟩
  rw [map_div₀, map_mul, hr']
  have hp : p = κ * σ w' / (σ z * c) := by
    rw [eq_div_iff (mul_ne_zero hz hc), ← h]
    ring
  rw [hp]
  field_simp

set_option maxHeartbeats 1000000 in

theorem exists_good (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) (t : T0)
    (x : A.fam.amb.FR t) :
    ∃ x' : A.fam.amb.FR t, x' ∈ (A.fam.R t).goodF A.fam.X ∧ R.Th t (R.jX t x') = R.Th t (R.jX t x) := by
  obtain ⟨hth, -⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hP R F hC
  have hga : goodAt A.fam.X (⊥ : Subgroup G) 1 = idemOf A.X := Formalism.IndefR.CxPass.LevelOperators.goodAt_bot _ _
  have hmem : (A.fam.R t).S.gaOp (A.fam.R t).r (idemOf A.X) x ∈ (A.fam.R t).goodF A.fam.X := by
    unfold BlockDat.goodF
    rw [hga]
    exact LinearMap.mem_range_self _ x
  refine ⟨_, hmem, ?_⟩
  conv_rhs => rw [← sum_gE R hC.models.HE hC.models.gE (R.Th t (R.jX t x))]
  simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, map_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hth t g x]

private theorem exists_linearMap_eq_psiK {R : RealDat D A Ks} (ch : Choice R) (hlin : ∀ a u, ConvK ch a u) :
    ∃ f : Fin ch.n → (R.HE.H →ₗ[ℂ] ℂ), ∀ a u, f a u = psiK ch a u :=
  ⟨fun a =>
    { toFun := psiK ch a
      map_add' := fun u u' => by
        simp only [psiK, map_add]
        exact GlobalTheory.FunObj.fPsiPhi_add ch.W ch.M (hlin a u) (hlin a u')
      map_smul' := fun b u => by
        have h1 := GlobalTheory.FunObj.fPsiPhi_smul ch.W ch.M ch.ρ ch.ξ 1 b (ch.col a) (ch.Phi a) (ch.form u)
        rw [one_smul, one_mul] at h1
        simp only [psiK, map_smul, RingHom.id_apply, smul_eq_mul]
        exact h1 }, fun _ _ => rfl⟩

private theorem rowTestModel_of_scaled_values_rational {R : RealDat D A Ks} (ch : Choice R) (hlin : ∀ a u, ConvK ch a u)
    (hinj : ∀ u, (∀ a, psiK ch a u = 0) → u = 0) {k : ℂ} (hk : k ≠ 0)
    (hval : ∀ t x a, ∃ z : D.what₂.LL, D.what₂.embLL z = k * psiK ch a (R.Th t (R.jX t x))) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  obtain ⟨f, hf⟩ := exists_linearMap_eq_psiK ch hlin
  refine ⟨ch.n, fun a => k • f a, ?_, ?_⟩
  · intro e he
    apply hinj
    intro a
    have h1 := he a
    rw [LinearMap.smul_apply, hf, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hk
  · intro t x a
    obtain ⟨z, hz⟩ := hval t x a
    refine ⟨z, hz.trans ?_⟩
    exact (((LinearMap.smul_apply k (f a) _).trans (congrArg (k • ·) (hf a _))).trans (smul_eq_mul k _)).symm

set_option maxHeartbeats 1600000 in
private theorem exists_embLL_mul_psiK_eq_vK_of_formulaAt (hP : GlobalTheory.Published.CuspRapidDecay) {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (ch : Choice R) {κ : ℂ} {ze : T0 → D.what₂.LL} (hF : FormulaAt ch κ ze) (t : T0) (x : A.fam.amb.FR t) (a : Fin ch.n) :
    ∃ x' : A.fam.amb.FR t, D.what₂.embLL (ze t) * cTot ch t * psiK ch a (R.Th t (R.jX t x)) = κ * vK ch t x' a := by
  obtain ⟨x', hx', hxx⟩ := exists_good hP R F hC t x
  refine ⟨x', ?_⟩
  rw [← hxx]
  exact hF.2 t x' hx' a

set_option maxHeartbeats 1600000 in

theorem rowTest_of_choice (hP : GlobalTheory.Published.CuspRapidDecay) {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (ch : Choice R) (hlin : ∀ a u, ConvK ch a u) (hinj : ∀ u, (∀ a, psiK ch a u = 0) → u = 0)
    (hc : ∀ i j t, ch.c i j t ≠ 0) {κ : ℂ} {ze : T0 → D.what₂.LL} (hF : FormulaAt ch κ ze)
    (hv : ∀ t x a, vK ch t x a ∈ Set.range D.what₂.embLL) (hr : ∀ i j t, sqRatio ch i j t ∈ Set.range D.what₂.embLL) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  have hcT : ∀ t, cTot ch t ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hc i j t
  have hz0 : ∀ t, D.what₂.embLL (ze t) ≠ 0 := by
    intro t
    obtain ⟨n, hn, hze⟩ := hF.1 t
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hn.ne'] at hze
    exact zero_ne_one hze
  by_cases hκ : κ = 0
  · subst hκ
    refine rowTestModel_of_scaled_values_rational ch hlin hinj one_ne_zero fun t x a => ?_
    obtain ⟨x', hfo⟩ := exists_embLL_mul_psiK_eq_vK_of_formulaAt hP hC ch hF t x a
    have hp : psiK ch a (R.Th t (R.jX t x)) = 0 :=
      (mul_eq_zero.1 (hfo.trans (zero_mul _))).resolve_left (mul_ne_zero (hz0 t) (hcT t))
    exact ⟨0, (map_zero D.what₂.embLL).trans (hp.symm.trans (one_mul _).symm)⟩
  · refine rowTestModel_of_scaled_values_rational ch hlin hinj (mul_ne_zero (hcT A.μ0) (inv_ne_zero hκ)) fun t x a => ?_
    obtain ⟨x', hfo⟩ := exists_embLL_mul_psiK_eq_vK_of_formulaAt hP hC ch hF t x a
    have hrat : cTot ch t / cTot ch A.μ0 ∈ Set.range D.what₂.embLL := by
      have he : cTot ch t / cTot ch A.μ0 = ∏ i, ∏ j, sqRatio ch i j t := by
        simp only [cTot, sqRatio, Finset.prod_div_distrib]
      rw [he]
      exact RingHom.mem_fieldRange.1 (Subfield.prod_mem _ fun i _ =>
        Subfield.prod_mem _ fun j _ => RingHom.mem_fieldRange.2 (hr i j t))
    exact rat_of_formula D.what₂.embLL (hz0 t) (hcT t) (hcT _) hκ hfo (hv t x' a) hrat

set_option maxHeartbeats 1000000 in

theorem rowTestModel_of_claims : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.RowClaim.HidaSetting large₂ R F → (∃ ch : GlobalTheory.RowTest.Choice R, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  intro hP hL hI hC _ hF hR hRa
  obtain ⟨CF0, h⟩ := Big.and (Big.and (Big.and (Big.and (Big.and hL hI) hC) hF) hR) hRa
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ hε hxl G _ _ Pl0 T0 A Ks _ _ _ R F hSet => ?_⟩
  rintro ⟨ch, hch, hsc, hfld⟩
  obtain ⟨⟨⟨⟨⟨hlin, hinj⟩, hcst⟩, hfor⟩, hrat⟩, hra⟩ := hx D large₂ hε hxl G Pl0 T0 A Ks R F hSet ch hch hsc
  obtain ⟨κ, ze, hFo⟩ := hfor hfld
  exact rowTest_of_choice hP hSet.core ch hlin hinj (fun i j t => (hcst i j t).2) hFo (hrat hfld) (hra hfld)

end GlobalTheory.RowTestFromClaims
