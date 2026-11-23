import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmoothAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensOp
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.IntPow
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactCv
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommInt

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section Ops

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma one_ok : (0 : H →L[ℂ] H) ≤ 1 ∧ ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
  ⟨by simpa using star_mul_self_nonneg (1 : H →L[ℂ] H), ContinuousLinearMap.norm_id_le⟩

private lemma mul_ok {S T : H →L[ℂ] H} (hS : 0 ≤ S ∧ ‖S‖ ≤ 1) (hT : 0 ≤ T ∧ ‖T‖ ≤ 1)
    (h : Commute S T) : 0 ≤ S * T ∧ ‖S * T‖ ≤ 1 :=
  ⟨h.mul_nonneg hS.1 hT.1, (norm_mul_le S T).trans (mul_le_one₀ hS.2 (norm_nonneg _) hT.2)⟩

private lemma prod_ok (L : List (H →L[ℂ] H)) (h : ∀ T ∈ L, 0 ≤ T ∧ ‖T‖ ≤ 1) (hc : L.Pairwise Commute) :
    0 ≤ L.prod ∧ ‖L.prod‖ ≤ 1 := by
  induction L with
  | nil => simpa using one_ok (H := H)
  | cons T L ih =>
    rw [List.prod_cons]
    rw [List.pairwise_cons] at hc
    exact mul_ok (h T (by simp)) (ih (fun S hS => h S (by simp [hS])) hc.2)
      (Commute.list_prod_right _ _ hc.1)

private lemma pow_ok {T : H →L[ℂ] H} (h : 0 ≤ T ∧ ‖T‖ ≤ 1) (k : ℕ) : 0 ≤ T ^ k ∧ ‖T ^ k‖ ≤ 1 := by
  induction k with
  | zero => simpa using one_ok (H := H)
  | succ k ih => rw [pow_succ]; exact mul_ok ih h ((Commute.refl T).pow_left k)

end Ops

private lemma smooth_pow {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ}
    (ν : Measure (archGroup F n)) [ν.IsHaarMeasure] (a : TI F n) (h1 : SmoothT a) (h2 : LeftFin a) (k : ℕ) :
    ∃ c : TI F n, (∀ g, c g = cvPow ν (a : archGroup F n → ℂ) k g) ∧ SmoothT c ∧ LeftFin c := by
  induction k with
  | zero => exact ⟨a, fun _ => rfl, h1, h2⟩
  | succ k ih =>
    obtain ⟨c, hc, -, -⟩ := ih
    have hb := UpperTheory.ConvolutionTheory.L1.cvBasic (archGroup F n) ν a c c a.continuous a.hasCompactSupport c.continuous
      c.hasCompactSupport c.continuous c.hasCompactSupport
    let γ : TI F n := ⟨⟨cv ν a c, hb.1⟩, hb.2.1⟩
    have hγ : ∀ g, γ g = cv ν a c g := fun _ => rfl
    have hl := UpperTheory.ConvolutionTheory.L1.lactCv F n ν a c γ h1 hγ
    refine ⟨γ, fun g => ?_, hl.1, hl.2.1 h2⟩
    have : (c : archGroup F n → ℂ) = cvPow ν (a : archGroup F n → ℂ) k := funext hc
    rw [hγ, this]
    rfl

private lemma single_comm {G : Type} [Group G] {k : ℕ} {i j : Fin k} (hij : i ≠ j) (x y : G) :
    (Pi.mulSingle i x : Fin k → G) * Pi.mulSingle j y = Pi.mulSingle j y * Pi.mulSingle i x :=
  by
  have h : Pairwise fun i j : Fin k => ∀ (x : G) (y : G), Commute (Pi.mulSingle i x : Fin k → G) (Pi.mulSingle j y) :=
    Pi.mulSingle_commute (f := fun _ => G)
  exact (h hij x y).eq

private lemma position_comm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {m : ℕ} {D : InfD σ m} {n : ℕ} {s : Fin (m + 1) → archGroup F n →* archGroup E n}
    (hs : IsBlockElement D n s) (hmul : ∀ g h, glueA D n (g * h) = glueA D n g * glueA D n h)
    {i j : Fin (m + 1)} (hij : i ≠ j) (x y : archGroup F n) : s i x * s j y = s j y * s i x := by
  have hcm := single_comm (G := archGroup F n) hij x y
  have h1 : s i x * s j y = glueA D n (Pi.mulSingle i x * Pi.mulSingle j y) := by
    rw [hmul, ← hs i x, ← hs j y]
  have h2 : s j y * s i x = glueA D n (Pi.mulSingle j y * Pi.mulSingle i x) := by
    rw [hmul, ← hs i x, ← hs j y]
  rw [h1, h2, hcm]

private lemma tens_ok {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {m : ℕ} {D : InfD σ m} {n : ℕ} {νE : Measure (archGroup E n)} [νE.IsHaarMeasure]
    {νF : Measure (archGroup F n)} [νF.IsHaarMeasure] {b a c : TI F n} {aE : TI E n}
    (hmeas : νE = Measure.map (glueA D n) (Measure.pi fun _ => νF))
    (hsq : ∀ g, a g = cv νF b (fun x => conj (b x⁻¹)) g) (hc : ∀ g, c g = cvPow νF a m g)
    (hnorm : ∫ g, ‖b g‖ ∂νF ≤ 1) (htens : IsTens D (fun _ => a) aE)
    {s : Fin (m + 1) → archGroup F n →* archGroup E n} (hs : IsBlockElement D n s) (hsc : ∀ i, Continuous (s i))
    (hmul : ∀ g h, glueA D n (g * h) = glueA D n g * glueA D n h)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep (archGroup E n) H) :
    0 ≤ π.integrated νE (UnitaryRep.ccToL1 νE aE) ∧ ‖π.integrated νE (UnitaryRep.ccToL1 νE aE)‖ ≤ 1 := by
  rw [UpperTheory.ConvolutionTheory.L1.tensOp F E σ m D n νE νF hmeas s hsc hs H π (fun _ => a) aE htens]
  refine prod_ok _ ?_ ?_
  · intro T hT
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    have := UpperTheory.ConvolutionTheory.L1.sqOp F n νF b a c m hsq hc hnorm H (π.compHom (s i) (hsc i))
    exact ⟨this.2.1, this.2.2.1⟩
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact (UpperTheory.ConvolutionTheory.Tf.commInt (archGroup E n) (archGroup F n) (archGroup F n) H π (s i) (hsc i)
      (s j) (hsc j) νF νF a a).2 (position_comm hs hmul hij.ne)

private lemma pow_op {F : Type} [Field F] [NumberField F] {n m : ℕ} {νF : Measure (archGroup F n)} [νF.IsHaarMeasure]
    {b a c : TI F n} (hsq : ∀ g, a g = cv νF b (fun x => conj (b x⁻¹)) g) (hc : ∀ g, c g = cvPow νF a m g)
    (hnorm : ∫ g, ‖b g‖ ∂νF ≤ 1) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep (archGroup F n) H) :
    0 ≤ π.integrated νF (UnitaryRep.ccToL1 νF c) ∧ ‖π.integrated νF (UnitaryRep.ccToL1 νF c)‖ ≤ 1 := by
  have := UpperTheory.ConvolutionTheory.L1.sqOp F n νF b a c m hsq hc hnorm H π
  rw [this.2.2.2]
  exact pow_ok ⟨this.2.1, this.2.2.1⟩ _

theorem _root_.UpperTheory.ConvolutionTheory.L1.ampPosition :
    UpperTheory.ConvolutionTheory.L1.AmpSlot := by
  intro F E _ _ _ _ _ _ _ σ m D n νE _ νF _ b a aE aF h
  have hbc : Continuous fun x : archGroup F n => conj (b x⁻¹) :=
    Complex.continuous_conj.comp (b.continuous.comp continuous_inv)
  have hbs : HasCompactSupport fun x : archGroup F n => conj (b x⁻¹) := by
    have h0 : HasCompactSupport fun x : archGroup F n => b x⁻¹ :=
      b.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
    exact h0.comp_left (g := starRingEnd ℂ) (map_zero _)
  let bs : TI F n := ⟨⟨fun x => conj (b x⁻¹), hbc⟩, hbs⟩
  have hsq : ∀ g, a g = cv νF b bs g := fun g => h.sq g
  have hA := UpperTheory.ConvolutionTheory.L1.lactCv F n νF b bs a h.smooth hsq
  have hsa : SmoothT a := hA.1
  have hla : LeftFin a := hA.2.1 h.fin
  have hE := UpperTheory.ConvolutionTheory.L1.tensSmooth F E σ m D n (fun _ => a) aE h.tens
  obtain ⟨c, hc, hcs, hcl⟩ := smooth_pow νF a hsa hla m
  have hcF : c = aF := by
    ext g
    rw [hc, h.pow]
  subst hcF
  obtain ⟨-, -, hmul, -, -, ⟨s, hs, hsc⟩, -, -⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  refine ⟨fun μE _ => ?_, fun μF _ => ?_⟩
  · have hok := tens_ok h.meas h.sq hc h.norm h.tens hs hsc hmul (LL μE)
      ((rightRegularRep (rationalGLOne E n) μE).compHom (archP E n) continuous_archP)
    exact ⟨hE.1 fun _ => hsa, hE.2 fun _ => hla, hok.1, hok.2⟩
  · have hok := pow_op h.sq hc h.norm (LL μF)
      ((rightRegularRep (rationalGLOne F n) μF).compHom (archP F n) continuous_archP)
    exact ⟨hcs, hcl, hok.1, hok.2⟩

end UpperTheory.ConvolutionTheory.L1
