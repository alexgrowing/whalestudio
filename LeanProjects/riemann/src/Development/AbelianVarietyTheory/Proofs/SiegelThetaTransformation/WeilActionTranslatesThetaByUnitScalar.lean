import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchurHeisG
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KZeroOnFrConstEntire
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasicStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivarStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestFunctionOfFockVacuumThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InnerProductTranslatedVacuaEqGaussianKernelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.RealScalar

variable {D : D7} {S T : HSp D}

theorem mul_tmul_eq_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] {a : (A × B) ⊗[F] E}
    (ha : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) a = 0) (y : E) :
    a * (((0, 1) : A × B) ⊗ₜ[F] y) = 0 := by
  have key : ∀ a : (A × B) ⊗[F] E, a * (((0, 1) : A × B) ⊗ₜ[F] y) =
      TensorProduct.map (LinearMap.inr F A B) LinearMap.id
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) a * ((1 : B) ⊗ₜ[F] y)) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [add_mul, ha, hb, map_add, add_mul, map_add]
    | tmul x e =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  rw [key, ha, zero_mul, map_zero]

theorem mul_mul_eq_self {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R') {m n : ℕ}
    {a : Matrix (Fin m) (Fin m) R} {b : Matrix (Fin n) (Fin n) R} {x : Matrix (Fin m) (Fin n) R}
    (ha : a.map p = 1) (hb : b.map p = 1) (hx : ∀ c, p c = 0 → ∀ i j, c * x i j = 0) : a * x * b = x := by
  have k : ∀ {l : ℕ} {c : Matrix (Fin l) (Fin l) R}, c.map p = 1 → ∀ i j, p ((c - 1) i j) = 0 := by
    intro l c hc i j
    have h2 : p (c i j) = (1 : Matrix (Fin l) (Fin l) R') i j := congrFun (congrFun hc i) j
    rw [Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e1 : (a - 1) * x = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun l _ => hx _ (k ha i l) _ _
  have e2 : x * (b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun l _ => by
      rw [mul_comm]
      exact hx _ (k hb l j) _ _
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at e1
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at e2
  rw [e1, e2]

theorem map_finPart_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) : (mt V g).map (finPart D) = 1 := by
  have h1 : finHom V g = 1 := hg
  exact congrArg Units.val h1

theorem actO_finW {h : GA D S} (hh : h ∈ GinfC S) {g : GA D T} (hg : g ∈ GinfC T)
    (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : actO S T h g (finW S T y) = finW S T y :=
  mul_mul_eq_self (finPart D) (map_finPart_mt hg) (map_finPart_mt (inv_mem hh)) fun _ hc i j =>
    mul_tmul_eq_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) hc (y j i)

theorem rho_zero (C : Ctx S T) (f : WO S T → ℂ) : C.rho 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem zOf_zero (C : Ctx S T) (x : Frame C.X.Ψ T.rank) : C.zOf x 0 = 0 := by
  have h0 : C.realPt 0 = 0 := by
    funext σ k a
    simp [Ctx.realPt, compAt]
  funext k i
  simp [Ctx.zOf, h0, zR, hermC]

theorem gaussR_zero (C : Ctx S T) (x : Frame C.X.Ψ T.rank) :
    gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
  simp [gaussR, hx]

theorem exists_ipO_Th (C : Ctx S T) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ →
      ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ) = a * SW.ip φ φ := by
  obtain ⟨a, ha, b, hab⟩ := GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank
    C.sympl C.even
  obtain ⟨⟨κ, hκ, hk⟩, -⟩ := GlobalTheory.Ker.kZero_onFr_const_entire D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx
    S.rank C.sympl C.even
  refine ⟨a * κ, mul_ne_zero ha (by exact_mod_cast hκ.ne'), fun B hB φ hφ => ?_⟩
  obtain ⟨hon, hdom, -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  have h0 : IsRealPt (0 : WO S T) := by
    ext i j
    simp
  have := GlobalTheory.T.innerProduct_translated_vacua_eq_gaussianKernel D S T C μ 𝓕 hμ _ hdom _ hdom φ φ hφ hφ 0 0 h0 h0
  have e : (fun (k : Fin S.rank) (i : Fin C.g) => conj ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [rho_zero, zOf_zero, gaussR_zero, e, (hk _ hon).2, (hab.2 φ φ hφ hφ).1] at this
  rw [this]
  simp only [map_one]
  ring

theorem om_real_Th : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ h ∈ GinfC S, ∀ g ∈ GinfC T, ∀ B, C.IsB B → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ : TF S.rank C.g, SW.IsSB φ → om (h, g) (C.Th (C.xB B) φ) = c • (C.Th (C.xB (C.mvB g B)) φ) := by
  intro D S T C om hom h hh g hg B hB
  obtain ⟨-, hdom, -, -, -, hmv⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  have hB' : C.IsB (C.mvB g B) := (hmv g).1
  obtain ⟨-, hdom', -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 _ hB'
  have hth : ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th x φ) :=
    fun x hx φ hφ => (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x hx φ hφ).1.1
  have hex : ∀ φ : TF S.rank C.g, ∃ φ' : TF S.rank C.g, SW.IsSB φ →
      SW.IsSB φ' ∧ om (h, g) (C.Th (C.xB B) φ) = C.Th (C.xB (C.mvB g B)) φ' := by
    intro φ
    by_cases hφ : SW.IsSB φ
    · obtain ⟨φ', h'⟩ := GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction D S T C _ hB' _ (hom.om_pres (h, g) _ (hth _ hdom φ hφ))
        (((GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors D S T C om hom h g _ (hth _ hdom φ hφ)).2 B hB).1
          ((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB φ hφ).1)
      exact ⟨φ', fun _ => h'⟩
    · exact ⟨φ, fun h' => absurd h' hφ⟩
  choose A hA using hex
  have L := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C
  have hadd : ∀ φ ψ : TF S.rank C.g, SW.IsSB φ → SW.IsSB ψ → SW.IsSB (φ + ψ) :=
    fun φ ψ h h' => (isSB_algebra_haar_linear _ _ _ _ _ h h').1
  have hsm : ∀ (a : ℂ) (φ : TF S.rank C.g), SW.IsSB φ → SW.IsSB (a • φ) :=
    fun a φ h => (isSB_algebra_haar_linear _ _ _ _ _ h h).2.1 _
  have hhe : ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (φ : TF S.rank C.g), SW.IsSB φ →
      SW.IsSB (heisG C.X C.bas y φ) := fun y φ h =>
    ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ h).1
  obtain ⟨c, hc⟩ := GlobalTheory.Ker.schur_heisG D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even A
    (fun φ hφ => (hA φ hφ).1)
    (fun φ ψ hφ hψ => by
      have h1 := hA _ (hadd _ _ hφ hψ)
      refine ((L _ hdom' _ h1.1).1 _ (hadd _ _ (hA φ hφ).1 (hA ψ hψ).1)).2 ?_
      rw [← h1.2, ((L _ hdom _ hφ).1 _ hψ).1, map_add, (hA φ hφ).2, (hA ψ hψ).2,
        ((L _ hdom' _ (hA φ hφ).1).1 _ (hA ψ hψ).1).1])
    (fun a φ hφ => by
      have h1 := hA _ (hsm a _ hφ)
      refine ((L _ hdom' _ h1.1).1 _ (hsm a _ (hA φ hφ).1)).2 ?_
      rw [← h1.2, (L _ hdom _ hφ).2.1, map_smul, (hA φ hφ).2, (L _ hdom' _ (hA φ hφ).1).2.1])
    (fun y φ hφ => by
      have h1 := hA _ (hhe y _ hφ)
      refine ((L _ hdom' _ h1.1).1 _ (hhe y _ (hA φ hφ).1)).2 ?_
      have e1 := (L _ hdom _ hφ).2.2.1 (-y)
      have e2 := (L _ hdom' _ (hA φ hφ).1).2.2.1 (-y)
      rw [neg_neg] at e1 e2
      rw [← h1.2, ← e1, ← e2, ← (hA φ hφ).2, hom.om_heis h g _ _ (hth _ hdom φ hφ), actO_finW hh hg])
  have hc' : ∀ φ : TF S.rank C.g, SW.IsSB φ →
      om (h, g) (C.Th (C.xB B) φ) = c • (C.Th (C.xB (C.mvB g B)) φ) := fun φ hφ => by
    rw [(hA φ hφ).2, hc φ hφ, (L _ hdom' _ hφ).2.1]
  by_cases hne : ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ φ ≠ 0
  · obtain ⟨φ, hφ, h0⟩ := hne
    refine ⟨c, ?_, hc'⟩
    obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.T.thetaFunction_fundamentalDomain_innerProduct_basic D S T C
    obtain ⟨a, ha, hn⟩ := exists_ipO_Th C hμ
    have t1 := hth _ hdom φ hφ
    have t2 := hth _ hdom' φ hφ
    have t3 : C.IsTh (c • (C.Th (C.xB (C.mvB g B)) φ)) := hc' φ hφ ▸ hom.om_pres (h, g) _ t1
    have u := ((hip μ 𝓕 hμ _ t1).2.2.2 _ t1).2.2.2.2.2 om hom (h, g)
    rw [hc' φ hφ, ((hip μ 𝓕 hμ _ t2).2.2.2 _ t3).2.2.1, ((hip μ 𝓕 hμ _ t3).2.2.2 _ t2).2.1,
      ((hip μ 𝓕 hμ _ t2).2.2.2 _ t2).2.2.1, map_mul, ← ((hip μ 𝓕 hμ _ t2).2.2.2 _ t2).2.1,
      hn _ hB φ hφ, hn _ hB' φ hφ, ← mul_assoc, Complex.mul_conj'] at u
    have hz := mul_ne_zero ha (GlobalTheory.SW.DblZero.ip_self_ne_zero hφ h0)
    have u' : ((‖c‖ : ℂ)) ^ 2 = 1 := mul_right_cancel₀ hz (by rw [u, one_mul])
    have u'' : ‖c‖ ^ 2 = 1 := by exact_mod_cast u'
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 u''
  · refine ⟨1, norm_one, fun φ hφ => ?_⟩
    have h0 : φ = (0 : ℂ) • φ := by
      by_contra h0
      exact hne ⟨φ, hφ, fun e => h0 (by rw [e, smul_zero])⟩
    rw [h0, (L _ hdom _ hφ).2.1, (L _ hdom' _ hφ).2.1]
    simp

end GlobalTheory.Ker.RealScalar
