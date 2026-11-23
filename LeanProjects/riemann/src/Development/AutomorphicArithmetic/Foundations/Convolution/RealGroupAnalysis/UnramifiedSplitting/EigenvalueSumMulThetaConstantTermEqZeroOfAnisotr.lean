import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.IntegralThetaRowZeroEqZeroOfIwahoriInvariant
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.RightInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.JExExists
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem memK {K : Type} [Field K] [NumberField K] (v : P K)
    (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) (h : ∀ i j, IsInt (x i j)) :
    Matrix.SpecialLinearGroup.toGL x ∈ GlobalTheory.LFun.KGL v 2 := by
  let a : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov K v) := fun i j => ⟨x i j, h i j⟩
  have ha : a.det = 1 := by
    apply Subtype.ext
    have hx := x.det_coe
    rw [Matrix.det_fin_two] at hx ⊢
    simpa [a] using hx
  exact ⟨Matrix.SpecialLinearGroup.toGL ⟨a, ha⟩, Units.ext (Matrix.ext fun i j => rfl)⟩

private theorem exU {K : Type} [Field K] [NumberField K] (v : P K) : ∃ ϖ : (Kv v)ˣ, IsU ϖ := by
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.IsUnifV K v p := v.valuedAdicCompletion_surjective K _
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  exact ⟨Units.mk0 p hp0, hp⟩

private theorem q_ne {K : Type} [Field K] [NumberField K] (v : P K) : q v ^ (1 / 2 : ℂ) ≠ 0 := by
  have hq : q v ≠ 0 := by
    unfold q
    exact Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  intro h0
  exact hq ((Complex.cpow_eq_zero_iff _ _).1 h0).1

private theorem int_one {K : Type} [Field K] [NumberField K] (v : P K) : IsInt (1 : Kv v) :=
  (map_one (Valued.v : Valuation (Kv v) _)).le
private theorem int_zero {K : Type} [Field K] [NumberField K] (v : P K) : IsInt (0 : Kv v) := by
  unfold IsInt
  rw [map_zero]
  exact zero_le'
private theorem int_neg_one {K : Type} [Field K] [NumberField K] (v : P K) : IsInt (-1 : Kv v) := by
  unfold IsInt
  rw [Valuation.map_neg, map_one]

private noncomputable def xN {K : Type} [Field K] [NumberField K] {v : P K} (b : Kv v) : Matrix.SpecialLinearGroup (Fin 2) (Kv v) :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

private noncomputable def xW {K : Type} [Field K] [NumberField K] (v : P K) : Matrix.SpecialLinearGroup (Fin 2) (Kv v) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

private noncomputable def xC {K : Type} [Field K] [NumberField K] {v : P K} (ϖ : (Kv v)ˣ) (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) :
    Matrix.SpecialLinearGroup (Fin 2) (Kv v) :=
  ⟨!![x 0 0, ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * x 0 1; (ϖ : Kv v) * x 1 0, x 1 1], by
    have hx := x.det_coe
    rw [Matrix.det_fin_two] at hx
    rw [Matrix.det_fin_two_of]
    have e : ((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * x 0 1 * ((ϖ : Kv v) * x 1 0) = x 0 1 * x 1 0 := by
      have := ϖ.inv_mul
      linear_combination (x 0 1 * x 1 0) * this
    rw [e]
    exact hx⟩

private theorem xC_conj {K : Type} [Field K] [NumberField K] {v : P K} (ϖ : (Kv v)ˣ) (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) :
    Matrix.SpecialLinearGroup.toGL x * dL ϖ 1 = dL ϖ 1 * Matrix.SpecialLinearGroup.toGL (xC ϖ x) := by
  apply Units.ext
  have hm := ϖ.mul_inv
  have e1 : ((1 : (Kv v)ˣ) : Kv v) = 1 := Units.val_one
  refine Matrix.ext fun i k => ?_
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases k
  · show x 0 0 * (ϖ : Kv v) + x 0 1 * 0 = (ϖ : Kv v) * x 0 0 + 0 * ((ϖ : Kv v) * x 1 0)
    ring
  · show x 0 0 * 0 + x 0 1 * ((1 : (Kv v)ˣ) : Kv v) = (ϖ : Kv v) * (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * x 0 1) + 0 * x 1 1
    rw [e1]
    linear_combination (-x 0 1) * hm
  · show x 1 0 * (ϖ : Kv v) + x 1 1 * 0 = 0 * x 0 0 + ((1 : (Kv v)ˣ) : Kv v) * ((ϖ : Kv v) * x 1 0)
    rw [e1]
    ring
  · show x 1 0 * 0 + x 1 1 * ((1 : (Kv v)ˣ) : Kv v) = 0 * (((ϖ⁻¹ : (Kv v)ˣ) : Kv v) * x 0 1) + ((1 : (Kv v)ˣ) : Kv v) * x 1 1
    rw [e1]
    ring

private theorem w_conj {K : Type} [Field K] [NumberField K] {v : P K} (ϖ : (Kv v)ˣ) :
    dL 1 ϖ * Matrix.SpecialLinearGroup.toGL (xW v) = Matrix.SpecialLinearGroup.toGL (xW v) * dL ϖ 1 := by
  apply Units.ext
  have e1 : ((1 : (Kv v)ˣ) : Kv v) = 1 := Units.val_one
  refine Matrix.ext fun i k => ?_
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases k
  · show ((1 : (Kv v)ˣ) : Kv v) * 0 + 0 * (-1) = 0 * (ϖ : Kv v) + 1 * 0
    ring
  · show ((1 : (Kv v)ˣ) : Kv v) * 1 + 0 * 0 = 0 * 0 + 1 * ((1 : (Kv v)ˣ) : Kv v)
    ring
  · show 0 * 0 + (ϖ : Kv v) * (-1) = (-1) * (ϖ : Kv v) + 0 * 0
    ring
  · show 0 * 1 + (ϖ : Kv v) * 0 = (-1) * 0 + 0 * ((1 : (Kv v)ˣ) : Kv v)
    ring

theorem UpperTheory.ConvolutionTheory.R2.H.eigenvalue_sum_mul_thetaConstantTerm_eq_zero_of_anisotropic :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (v : P F), Gd D.δ v → Aniso D.δ v →
      ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ (h : GL (Fin 2) (A E)) (α β : ℂˣ), EigAt v {α, β} f.1 → KAt v (dM (nu F h)) →
      (∀ g, At v g → IntAt v g → W.Om g (W.L h φ) = W.L h φ) → ((α : ℂ) + β) * T0 W M f.1 φ h = 0 := by
  intro F E _ _ _ _ _ _ _ D W M π v hG hA f hf φ hφ h α β hE hK hL
  have hE₁ : EigAt v {α, β} (fun g => f.1 (g * dM (nu F h))) := (fixTr F v f.1 _ hK).2 _ hE
  obtain ⟨ϖ, hϖ⟩ := exU v
  obtain ⟨R, -, hRi, hR⟩ := heckeExpl F v ϖ hϖ
  obtain ⟨⟨j, hj⟩, hjj⟩ := jEx F v
  obtain ⟨-, hAt, hInt, -⟩ := hjj j hj
  have hFix : ∀ (G : GL (Fin 2) (A F)), ∀ z ∈ GlobalTheory.LFun.KGL v 2, f.1 (G * lc v z * dM (nu F h)) = f.1 (G * dM (nu F h)) := by
    intro G z hz
    have h1 : f.1 (G * lc v (1 * z) * dM (nu F h)) = f.1 (G * lc v 1 * dM (nu F h)) := (hE₁ G).inv 1 z hz
    rwa [one_mul, map_one, mul_one] at h1
  have hgl : ∀ (g : G1 F) x, gl (g * j x) = gl g * lc v (Matrix.SpecialLinearGroup.toGL x) := fun g x =>
    (map_mul Matrix.SpecialLinearGroup.toGL g (j x)).trans (congrArg (fun t => gl g * t) (hj x))
  have hOm : ∀ (g : G1 F) x, (∀ i k, IsInt (x i k)) → W.Om (g * j x) (W.L h φ) = W.Om g (W.L h φ) := by
    intro g x hx
    rw [map_mul, Module.End.mul_apply, hL _ (hAt x) (hInt x hx)]
  have hrow : ∀ γ (φ' : S4 F), ThRow 0 0 (W.Om (ratS F γ) φ').1 = ThRow 0 0 φ'.1 := by
    intro γ φ'
    simpa using (hatSt F E D W).row γ 0 φ'
  have hl1 : ∀ γ (g : G1 F), f.1 (gl (ratS F γ * g) * lc v (dL ϖ 1) * dM (nu F h)) = f.1 (gl g * lc v (dL ϖ 1) * dM (nu F h)) := by
    intro γ g
    have e : gl (ratS F γ * g) = ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * gl g :=
      (map_mul Matrix.SpecialLinearGroup.toGL (ratS F γ) g).trans (congrArg (· * gl g) (Units.ext rfl))
    rw [e, mul_assoc (ratGL F 2 _), mul_assoc (ratGL F 2 _), (π.cusp f hf).1.left, mul_assoc]
  let U : G1 F → ℂ := fun g => f.1 (gl g * lc v (dL ϖ 1) * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1
  have hlU : ∀ γ g, U (ratS F γ * g) = U g := by
    intro γ g
    show f.1 (gl (ratS F γ * g) * lc v (dL ϖ 1) * dM (nu F h)) * ThRow 0 0 (W.Om (ratS F γ * g) (W.L h φ)).1 =
      f.1 (gl g * lc v (dL ϖ 1) * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1
    rw [hl1, map_mul, Module.End.mul_apply, hrow]
  have hlaw := (lcLaws F v).2.2.2.2.2.2 (dM (nu F h)) (dL ϖ 1)
  have hUi : IntegrableOn U M.D M.μ := by
    have hc := (conv F E D W M π _ (π.stable (.fin (locGL F 2 v ((Matrix.GeneralLinearGroup.map (cp v) (dM (nu F h)))⁻¹ * dL ϖ 1 * Matrix.GeneralLinearGroup.map (cp v) (dM (nu F h))))) f hf) φ hφ h).2.1
    have e : U = fun g => (TR.act (.fin (locGL F 2 v ((Matrix.GeneralLinearGroup.map (cp v) (dM (nu F h)))⁻¹ * dL ϖ 1 * Matrix.GeneralLinearGroup.map (cp v) (dM (nu F h))))) f).1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 := funext fun g => by
      show f.1 (gl g * lc v (dL ϖ 1) * dM (nu F h)) * _ = f.1 (gl g * dM (nu F h) * lc v ((Matrix.GeneralLinearGroup.map (cp v) (dM (nu F h)))⁻¹ * dL ϖ 1 * Matrix.GeneralLinearGroup.map (cp v) (dM (nu F h)))) * _
      rw [mul_assoc (gl g), hlaw, mul_assoc (gl g)]
    rw [e]
    exact hc
  have hI : ∫ g in M.D, U g ∂M.μ = 0 := by
    refine integral_thetaRowZero_eq_zero_of_iwahori_invariant F E D W M v ϖ hϖ hG hA j hj (fun g => f.1 (gl g * lc v (dL ϖ 1) * dM (nu F h))) (W.L h φ) hl1 ?_ hUi
    intro g x h00 h11 h01 h10
    have hz : Matrix.SpecialLinearGroup.toGL (xC ϖ x) ∈ GlobalTheory.LFun.KGL v 2 := by
      refine memK v _ fun i k => ?_
      fin_cases i <;> fin_cases k
      exacts [h00, h01, h10, h11]
    show f.1 (gl (g * j x) * lc v (dL ϖ 1) * dM (nu F h)) = _
    rw [hgl, mul_assoc (gl g), ← map_mul, xC_conj, map_mul, ← mul_assoc]
    exact hFix _ _ hz
  have hk : ∀ x, ∫ g in M.D, U (g * j x) ∂M.μ = 0 := fun x => ((rightInv F M U hlU hUi (j x)).2).trans hI
  have hki : ∀ x, IntegrableOn (fun g => U (g * j x)) M.D M.μ := fun x => (rightInv F M U hlU hUi (j x)).1
  have hpt : ∀ g : G1 F, q v ^ (1 / 2 : ℂ) * ((α : ℂ) + β) * (f.1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1) =
      ∑ b ∈ R, U (g * j (xN b)) + U (g * j (xW v)) := by
    intro g
    have hEig : Eig v {α, β} (fun y => f.1 (gl g * lc v y * dM (nu F h))) := hE₁ (gl g)
    have h1 := (hR α β _ hEig 1).1
    beta_reduce at h1
    have a0 : f.1 (gl g * lc v 1 * dM (nu F h)) = f.1 (gl g * dM (nu F h)) := by rw [map_one, mul_one]
    have hwI : ∀ i k, IsInt (xW v i k) := by
      intro i k
      fin_cases i <;> fin_cases k
      exacts [int_zero v, int_one v, int_neg_one v, int_zero v]
    have ab : ∀ b ∈ R, f.1 (gl g * lc v (1 * UpperTheory.ConvolutionTheory.R2.H.nL b * dL ϖ 1) * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 = U (g * j (xN b)) := by
      intro b hb
      have hbI : ∀ i k, IsInt (xN b i k) := by
        intro i k
        fin_cases i <;> fin_cases k
        exacts [int_one v, hRi b hb, int_zero v, int_one v]
      have hN : Matrix.SpecialLinearGroup.toGL (xN b) = UpperTheory.ConvolutionTheory.R2.H.nL b := Units.ext rfl
      show _ = f.1 (gl (g * j (xN b)) * lc v (dL ϖ 1) * dM (nu F h)) * ThRow 0 0 (W.Om (g * j (xN b)) (W.L h φ)).1
      rw [hOm _ _ hbI, hgl, hN, one_mul, map_mul]
      simp only [mul_assoc]
    have aw : f.1 (gl g * lc v (1 * dL 1 ϖ) * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 = U (g * j (xW v)) := by
      show _ = f.1 (gl (g * j (xW v)) * lc v (dL ϖ 1) * dM (nu F h)) * ThRow 0 0 (W.Om (g * j (xW v)) (W.L h φ)).1
      have e1 : gl g * lc v (dL 1 ϖ) * lc v (Matrix.SpecialLinearGroup.toGL (xW v)) =
          gl g * lc v (Matrix.SpecialLinearGroup.toGL (xW v)) * lc v (dL ϖ 1) := by
        rw [mul_assoc, ← map_mul, w_conj, map_mul, mul_assoc]
      rw [hOm _ _ hwI, hgl, one_mul, ← hFix (gl g * lc v (dL 1 ϖ)) _ (memK v (xW v) hwI), e1]
    rw [← a0, ← mul_assoc, h1, add_mul, Finset.sum_mul, Finset.sum_congr rfl ab, aw]
  have hq := q_ne v
  have key : q v ^ (1 / 2 : ℂ) * (((α : ℂ) + β) * T0 W M f.1 φ h) = 0 := by
    rw [← mul_assoc]
    unfold T0
    rw [← integral_const_mul]
    simp only [hpt]
    rw [integral_add (integrable_finset_sum _ fun b _ => hki _) (hki _), integral_finset_sum _ fun b _ => hki _]
    simp [hk]
  exact (mul_eq_zero.1 key).resolve_left hq
