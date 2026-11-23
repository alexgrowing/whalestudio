import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsClosedEmbeddingSlVal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.SgZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.WeilActionUnipotentNull
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.WeilLiftEquivariance
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.NonzeroPlacesInvariant
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ThetaIntegralExistsBilinear
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.FstDetFin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PtL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Cols
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.JExExists
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private noncomputable def trB {F : Type} [Field F] [NumberField F] {v : P F} (x : GLv v)
    (a : SB (M2 v)) : SB (M2 v) :=
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => (x⁻¹).val * m * (dd x).val
      invFun := fun m => x.val * m * ((dd x)⁻¹).val
      left_inv := fun m => by
        show x.val * ((x⁻¹).val * m * (dd x).val) * ((dd x)⁻¹).val = m
        have h1 : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h2 : (dd x).val * ((dd x)⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      right_inv := fun m => by
        show (x⁻¹).val * (x.val * m * ((dd x)⁻¹).val) * (dd x).val = m
        have h1 : (x⁻¹).val * x.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have h2 : ((dd x)⁻¹).val * (dd x).val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  ⟨fun m => a.1 (e m), a.2.1.comp_continuous e.continuous, a.2.2.comp_homeomorph e⟩

private theorem exT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (D : Dat F E) (v : P F) (θ : Kv v) (u : V4 F → ℂ) (hu : GoodU v D.δ θ u) :
    ∃ T : SB (M2 v) →ₗ[ℂ] Fock (F := F) D.δ, ∀ a, (T a).1.1 = ten v θ u (Pt a.1) := by
  obtain ⟨P, hP⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have h : ∀ a : SB (M2 v), ∃ φ : Fock (F := F) D.δ, φ.1.1 = ten v θ u (Pt a.1) := by
    intro a
    obtain ⟨φ, hφ, e⟩ := hu (P a) (P a).2
    exact ⟨⟨φ, hφ⟩, by rw [e, hP]⟩
  choose t ht using h
  refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩
  · intro a b
    apply Subtype.ext
    apply Subtype.ext
    show (t (a + b)).1.1 = (t a).1.1 + (t b).1.1
    rw [ht, ht, ht, ← hP, ← hP, ← hP, map_add]
    funext X
    simp [ten, mul_add]
  · intro c a
    apply Subtype.ext
    apply Subtype.ext
    show (t (c • a)).1.1 = c • (t a).1.1
    rw [ht, ht, ← hP, ← hP, map_smul]
    funext X
    simp [ten, mul_left_comm]

private theorem L_nbar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (v : P F) (θ : Kv v)
    (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (hθ0 : θ ≠ 0) (u : V4 F → ℂ) (a a' : M2 v → ℂ) (s : Kv v)
    (ha' : ∀ m, a' m = ψl v (-(s * m.det)) * a m) (φ φ' : S4 F)
    (hφ : φ.1 = ten v θ u (Pt a)) (hφ' : φ'.1 = ten v θ u (Pt a')) :
    W.L (nbar D v θ s) φ = φ' := by
  obtain ⟨hnu, hact⟩ := UpperTheory.ConvolutionTheory.R2.I.actN F E D v θ hθ hθ0 s
  apply Subtype.ext
  funext X
  obtain ⟨e1, e2⟩ := hact X
  have hab : ab (1 : (A F)ˣ) = 1 := by simp [ab]
  have ha2 : a' = fun m => ψl v (-(s * m.det)) * a m := funext ha'
  rw [W.L_apply, hφ, hφ', hnu, hab]
  simp only [ten]
  rw [e1, e2, (UpperTheory.ConvolutionTheory.R2.I.ptN F v a (mat v θ X)).2 s, ha2]
  simp

private theorem L_J {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (v : P F) (θ : Kv v)
    (J : GLv v →* GL (Fin 2) (A E)) (hJ : Splt D v θ J) (u : V4 F → ℂ) (a : M2 v → ℂ) (x : GLv v)
    (φ φ' : S4 F) (hφ : φ.1 = ten v θ u (Pt a))
    (hφ' : φ'.1 = ten v θ u (Pt fun m => a ((x⁻¹).val * m * (dd x).val))) :
    W.L (J x) φ = φ' := by
  obtain ⟨hnu, hact⟩ := UpperTheory.ConvolutionTheory.R2.I.actJ F E D v θ J hJ x
  apply Subtype.ext
  funext X
  obtain ⟨e1, e2⟩ := hact X
  have hab : ((ab (idl v (Matrix.GeneralLinearGroup.det x)) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ab (idl v (Matrix.GeneralLinearGroup.det x)) := (IdeleGroup.ideleModule F _).2
    exact_mod_cast this.ne'
  rw [W.L_apply, hφ, hφ', hnu]
  simp only [ten]
  rw [e1, e2, UpperTheory.ConvolutionTheory.R2.I.ptL F v a x (mat v θ X)]
  push_cast
  field_simp

private theorem psi_nbar {F : Type} [Field F] [NumberField F] (v : P F) (s : Kv v) :
    ψ (-(2 * sg v (s / 2))) = ψl v (-s) := by
  have hadd := (sgLaws F v).1
  have h0 : sg v 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have e : -(2 * sg v (s / 2)) = sg v (-s) := by
    have h1 := hadd (s / 2) (s / 2)
    have h2 := hadd s (-s)
    rw [add_neg_cancel, h0] at h2
    rw [add_halves] at h1
    rw [two_mul, ← h1]
    exact neg_eq_of_add_eq_zero_right h2.symm
  rw [e]
  exact (UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.1 _

theorem UpperTheory.ConvolutionTheory.R2.I.keyPure :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J →
      ∀ h', (∀ s, Commute h' (nbar D v θ s)) → ∀ u, Mod v θ W u → ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
      ∀ f ∈ π.V, (fun x => W1 W M f.1 φ (h' * J x)) ∈ MC (π.locRep v) := by
  intro F E _ _ _ _ _ _ _ D W M π v θ J hJ h' hcomm u hu a ha φ hφ f hf
  obtain ⟨hsm, hloc, -⟩ := UpperTheory.ConvolutionTheory.R2.I.locSm F π v
  obtain ⟨T, hT⟩ := exT D v θ u hu.1
  obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.R2.I.thetaIntegral_exists_bilinear F E D W M π h'
  have hfun : ∀ (x : GLv v) (f : π.V), (fun g => f.1.1 (g * lc v x)) = (π.locRep v x f).1.1 :=
    fun x f => funext fun g => (hloc x f g).symm
  have hyp1 : ∀ (g : SL v) f (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m * g.1)) →
      (B.compl₂ T) (π.locRep v (Matrix.SpecialLinearGroup.toGL g) f) a' = (B.compl₂ T) f a := by
    intro g f a a' ha'
    obtain ⟨j, hj⟩ := (jEx F v).1
    have h1 : W.Om (j g) (T a).1 = (T a').1 := by
      apply Subtype.ext
      rw [hu.2 j hj g a.1 a.2 (T a).1 (hT a), hT a']
      congr 2
      exact (funext ha').symm
    have h2 := UpperTheory.ConvolutionTheory.R2.I.weilLift_invariance F E D W M π f.1 f.2 (T a).1 (T a).2 h' (j g)
    rw [hj g, hfun, h1] at h2
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, hB, hB]
    exact h2
  have hyp2 : ∀ f (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) →
      (B.compl₂ T) f a' = ψl v (-s) * (B.compl₂ T) f a := by
    intro f s a a' ha'
    have h1 := L_nbar W v θ hJ.sq hJ.ne u a.1 a'.1 s ha' (T a).1 (T a').1 (hT a) (hT a')
    have h2 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1.1 (T a).1 h').1 (nbar D v θ s))
    have h3 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1.1 (T a).1 h').2 (sg v (s / 2)) (sg v (-(s / (2 * θ)))))
    have hnu := (UpperTheory.ConvolutionTheory.R2.I.actN F E D v θ hJ.sq hJ.ne s).1
    have hd1 : dM (1 : (A F)ˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dM]
    rw [hnu, hd1, h1] at h2
    simp only [mul_one] at h2
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, hB, hB, ← h2, (hcomm s).eq]
    rw [← psi_nbar]
    exact h3
  have key := UpperTheory.ConvolutionTheory.R2.I.absM F v π.V (π.locRep v) hsm (B.compl₂ T) hyp1 hyp2 ⟨f, hf⟩ ⟨a, ha⟩
    (fun x => trB x ⟨a, ha⟩) (fun x m => rfl)
  have hfin : (fun x => W1 W M f.1 φ (h' * J x)) =
      fun x => (B.compl₂ T) (π.locRep v (dd x) ⟨f, hf⟩) (trB x ⟨a, ha⟩) := by
    funext x
    have h1 := L_J W v θ J hJ u a x φ (T (trB x ⟨a, ha⟩)).1 hφ (hT _)
    have h2 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1 φ h').1 (J x))
    have h3 : dM (nu F (J x)) = lc v (dd x) := by
      rw [(UpperTheory.ConvolutionTheory.R2.I.actJ F E D v θ J hJ x).1]
      exact ((lcLaws F v).2.2.1 _).symm
    rw [h3, h1] at h2
    rw [h2, LinearMap.compl₂_apply, hB, ← hfun]
  rw [hfin]
  exact key
