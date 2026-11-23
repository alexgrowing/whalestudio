import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaNormalFormKeyDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalFormStatement
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationThetaSectionNonvanishingFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.AbCl

theorem exists_te {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] (v : epsR R ⟶ D.P.A) :
    ∃ bb : TE R ℂ ⟶ D.P.A, bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ v.left := by
  refine ⟨Over.homMk (spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ v.left) ?_, rfl⟩
  rw [Category.assoc, Over.w v]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isD_unique {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {ν : NumOf D ℂ N} {g : ℕ} {d : AB N.toNumB g} {b₀ b : TE R ℂ ⟶ D.P.A} {W₀ W₁ W₂ : Fin g → ℂ}
    (h₀ : ∀ W', IsD ν d W' b₀ ↔ W' = W₀) (h₁ : IsD ν d W₁ b) (h₂ : IsD ν d W₂ b) : W₁ = W₂ := by
  have key : IsD ν d (W₀ + (W₁ - W₂)) b₀ := by
    intro U f hU
    rw [(h₀ W₀).2 rfl U f hU]
    have e := congrArg TrivSqZeroExt.snd ((h₁ U f hU).symm.trans (h₂ U f hU))
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at e
    rw [map_add, map_sub, e, sub_self, add_zero]
  have := (h₀ _).1 key
  have h3 : W₁ - W₂ = 0 := by simpa using this
  exact sub_eq_zero.1 h3

theorem exists_ab_keyOK : ∀ κ : Rule, Rule4 κ → AllC fun {R} _ _ {D} _ {N} ν => 1 ≤ D.P.g → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  intro κ hκ R _ _ _ _ D hψ hτ _ N ν hg
  obtain ⟨th, hth, hcomp⟩ := GlobalTheory.T.exists_degenerationThetaSection_nonvanishingFibres R D ℂ N ν
  obtain ⟨vB₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.P.A D.P.smoothDim
  let y₀ : KeyIn R := ⟨D.P, hg, D.rig, D.rig_gen, th, hth, vB₀, hv₀⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.exists_keyPB y₀ ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))
  have hg₀ : x₀.P.g = D.P.g := by obtain ⟨_, _, _, hgg, _⟩ := hx₀; exact hgg
  obtain ⟨u, τ, a, b, c, W, hNF⟩ := GlobalTheory.T.exists_classicalThetaNormalForm_keyDatum D.P.g x₀ hg₀
  obtain ⟨d, G, hdc, huniq⟩ := GlobalTheory.T.exists_classical_abelianPart_values_of_normalForm R D hψ hτ N ν y₀ rfl HEq.rfl ⟨th, HEq.rfl, hcomp⟩ x₀ hg₀ rfl u τ a b c W hx₀ hNF
  refine ⟨d, G, ?_⟩
  intro vB bs MB k₀ hv hbs hIsD hBK
  have hM : ∀ i, ∃ c : Fin D.P.g → R, IsLieComb c vB₀ (vB i) := fun i => (hv₀.2 (vB i) (hv.1 i)).exists
  choose M' hMc using hM
  let M : Matrix (Fin D.P.g) (Fin D.P.g) R := Matrix.of M'
  obtain ⟨x, hKx, hκx⟩ := GlobalTheory.T.exists_keyDatumBaseChange_lieBasisChange_detPow κ hκ.1 R y₀ x₀ _ hx₀ vB hv M hMc
  have hk : (κ ℂ x : ℂ) = k₀ := hBK.2 hg D.rig_gen th hth hv x hcomp hKx
  choose b₀ hb₀ using fun j => exists_te (D := D) (vB₀ j)
  have hW : ∀ j, ∀ W', IsD ν d W' (b₀ j) ↔ W' = W j := fun j => huniq vB₀ (fun i => HEq.rfl) j (b₀ j) (hb₀ j)
  have hlin : ∀ i, IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (M i j)) • W j) (bs i) :=
    fun i => GlobalTheory.T.tangentVectorOfDualPoint_additive_lieComb R D N ν D.P.g d D.P.g (M i) vB₀ (vB i) W b₀ (bs i) hv₀.1 (hMc i) hb₀ (hbs i) (fun j => (hW j _).2 rfl)
  have hrow : ∀ i, (2 * Real.pi * Complex.I : ℂ)⁻¹ • MB i =
      ∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (M i j)) • W j :=
    fun i => isD_unique (hW ⟨0, hg⟩) (hIsD i) (hlin i)
  have h2π : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let Mx : Matrix (Fin D.P.g) (Fin D.P.g) ℂ := Matrix.of fun j k => (2 * Real.pi * Complex.I : ℂ) * W j k
  have hNF' : NF x₀ hg₀ u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) := by
    have e : (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) = W := by
      funext j k
      show (2 * Real.pi * Complex.I : ℂ)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * W j k) = W j k
      rw [← _root_.mul_assoc, inv_mul_cancel₀ h2π, _root_.one_mul]
    rw [e]; exact hNF
  obtain ⟨hdet, hval⟩ := GlobalTheory.T.thetaKeyRule_value_classicalNormalForm κ hκ.1 hκ.2.2.1 D.P.g x₀ hg₀ u τ a b c Mx hNF'
  have hMB : MB = (M.map ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) * Mx := by
    ext i k
    have e := congrFun (hrow i) k
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at e
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Mx, Matrix.of_apply, RingHom.comp_apply]
    calc MB i k = (2 * Real.pi * Complex.I : ℂ) * ((2 * Real.pi * Complex.I : ℂ)⁻¹ * MB i k) := by field_simp
      _ = _ := by rw [e, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by simp [M]; ring
  have hne : (κ ℂ x : ℂ) ≠ 0 := Units.ne_zero _
  rw [hMB, Matrix.det_mul]
  rw [hκx] at hk hne
  have hf : (M.map ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))).det ≠ 0 := by
    intro h0; apply hne; rw [h0]; ring
  refine ⟨mul_ne_zero hf hdet, ?_⟩
  rw [← hk, hdc, _root_.mul_assoc, hval]
  ring

end GlobalTheory.MBLow.AbCl
