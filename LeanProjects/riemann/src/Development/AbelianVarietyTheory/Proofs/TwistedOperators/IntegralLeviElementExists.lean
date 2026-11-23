import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.LeviIntegral

open scoped Matrix TensorProduct
open Formalism.UG (cT hform)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (sigR inclR JR hR HR HA)

section Generic

variable {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ}

theorem cT_add' {m p : Type} (X Y : Matrix m p A) : cT s (X + Y) = cT s X + cT s Y := by
  ext i j; simp [cT]

theorem cT_sub' {m p : Type} (X Y : Matrix m p A) : cT s (X - Y) = cT s X - cT s Y := by
  ext i j; simp [cT]

theorem cT_cT' (hs : ∀ x, s (s x) = x) {m p : Type} (X : Matrix m p A) : cT s (cT s X) = X := by
  ext i j; simp [cT, hs]

theorem cT_mul_mulVec_apply {k : Type} [Fintype k] (X : Matrix (Fin n) k A) (J : Matrix (Fin n) (Fin n) A)
    (y : Fin n → A) (i : k) : ((cT s X * J) *ᵥ y) i = hform s J (fun l => X l i) y := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, cT, hform, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

def frameLevi (J : Matrix (Fin n) (Fin n) A) (E0 F0 : Matrix (Fin n) (Fin r) A) (a b : Matrix (Fin r) (Fin r) A) :
    Matrix (Fin n) (Fin n) A :=
  1 + E0 * a * cT s F0 * J + F0 * b * cT s E0 * J

variable {s} {J : Matrix (Fin n) (Fin n) A} {E0 F0 : Matrix (Fin n) (Fin r) A}

theorem frameLevi_mul (hEE : cT s E0 * J * E0 = 0) (hFF : cT s F0 * J * F0 = 0) (hFE : cT s F0 * J * E0 = 1)
    (hEF : cT s E0 * J * F0 = 1) (a b a' b' : Matrix (Fin r) (Fin r) A) :
    frameLevi s J E0 F0 a b * frameLevi s J E0 F0 a' b' = frameLevi s J E0 F0 (a + a' + a * a') (b + b' + b * b') := by
  have e1 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s F0 * (J * (E0 * Z)) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFE, Matrix.one_mul]
  have e2 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s F0 * (J * (F0 * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFF, Matrix.zero_mul]
  have e3 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s E0 * (J * (E0 * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE, Matrix.zero_mul]
  have e4 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s E0 * (J * (F0 * Z)) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEF, Matrix.one_mul]
  simp only [frameLevi, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, e1, e2, e3, e4,
    Matrix.mul_zero, add_zero, zero_add]
  abel

theorem frameLevi_zero : frameLevi s J E0 F0 0 0 = 1 := by
  simp [frameLevi]

theorem frameLevi_mul_isotropic (hEE : cT s E0 * J * E0 = 0) (hFE : cT s F0 * J * E0 = 1) (a b : Matrix (Fin r) (Fin r) A) :
    frameLevi s J E0 F0 a b * E0 = E0 * (1 + a) := by
  have e1 : cT s F0 * (J * E0) = 1 := by rw [← Matrix.mul_assoc, hFE]
  have e3 : cT s E0 * (J * E0) = 0 := by rw [← Matrix.mul_assoc, hEE]
  simp only [frameLevi, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, e1, e3,
    Matrix.mul_zero, add_zero]

theorem frameLevi_unitary (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (hEE : cT s E0 * J * E0 = 0)
    (hFF : cT s F0 * J * F0 = 0) (hFE : cT s F0 * J * E0 = 1) (hEF : cT s E0 * J * F0 = 1)
    {a b : Matrix (Fin r) (Fin r) A} (ha : a + cT s b + cT s b * a = 0) (hb : b + cT s a + cT s a * b = 0) :
    cT s (frameLevi s J E0 F0 a b) * J * frameLevi s J E0 F0 a b = J := by
  have e1 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s F0 * (J * (E0 * Z)) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFE, Matrix.one_mul]
  have e2 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s F0 * (J * (F0 * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFF, Matrix.zero_mul]
  have e3 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s E0 * (J * (E0 * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE, Matrix.zero_mul]
  have e4 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s E0 * (J * (F0 * Z)) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEF, Matrix.one_mul]
  have key : J * (E0 * ((a + cT s b + cT s b * a) * (cT s F0 * J))) +
      J * (F0 * ((b + cT s a + cT s a * b) * (cT s E0 * J))) = 0 := by
    rw [ha, hb]; simp
  calc cT s (frameLevi s J E0 F0 a b) * J * frameLevi s J E0 F0 a b
      = J + (J * (E0 * ((a + cT s b + cT s b * a) * (cT s F0 * J))) +
          J * (F0 * ((b + cT s a + cT s a * b) * (cT s E0 * J)))) := by
        simp only [frameLevi, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_one, cT_cT' s hs, hJ, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, e1, e2, e3, e4, Matrix.mul_zero, add_zero, zero_add]
        abel
    _ = J := by rw [key, add_zero]

end Generic

end GlobalTheory.LeviIntegral

noncomputable section

namespace GlobalTheory.LeviIntegral

open scoped Matrix TensorProduct
open Formalism.UG (cT hform)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (sigR inclR JR hR HR HA)
open GlobalTheory.TruncKer

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

def frameMat (R : Type) [CommRing R] [Algebra F R] {k : ℕ} (x : Fin k → V.V) :
    Matrix (Fin V.rank) (Fin k) (R ⊗[F] E) :=
  Matrix.of fun y i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (x i) y

theorem sig_sig (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    sigR R hc.sig (sigR R hc.sig z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, CMData.sig]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem cT_JR (R : Type) [CommRing R] [Algebra F R] : cT (sigR R hc.sig) (JR R V.gram) = JR R V.gram := by
  have h := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_gram hc V
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at hij ⊢
  simp only [JR, Matrix.map_apply, inclR, sigR]
  rw [← hij]
  simp

theorem hform_coordR (R : Type) [CommRing R] [Algebra F R] (x y : V.V) :
    hform (sigR R hc.sig) (JR R V.gram) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R x) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R y) =
      inclR R (V.hT x y) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hform, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR, JR, inclR, sigR, CMData.sig, TensorProduct.tmul_sum, starRingEnd_apply]

theorem cT_frameMat_mul (R : Type) [CommRing R] [Algebra F R] {k l : ℕ} (x : Fin k → V.V) (y : Fin l → V.V) :
    cT (sigR R hc.sig) (frameMat (F := F) V R x) * JR (F := F) R V.gram * frameMat (F := F) V R y =
      Matrix.of fun i j => inclR R (V.hT (x i) (y j)) := by
  ext i j
  rw [Matrix.of_apply, ← hform_coordR hc V R]
  simp only [Matrix.mul_apply, cT, hform, Matrix.transpose_apply, Matrix.map_apply, frameMat, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end Frame

end GlobalTheory.LeviIntegral

end

noncomputable section

namespace GlobalTheory.LeviIntegral

open scoped Matrix TensorProduct
open Formalism.UG (cT hform)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (sigR inclR JR hR HR HA)
open GlobalTheory.TruncKer

section Wf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {V : HSpace E} (Φ : WittFrame V) (R : Type) [CommRing R] [Algebra F R]

theorem frame_ee : cT (sigR R hc.sig) (frameMat (F := F) V R Φ.e) * JR (F := F) R V.gram *
    frameMat (F := F) V R Φ.e = 0 := by
  rw [cT_frameMat_mul]
  ext i j
  rw [Matrix.of_apply, Matrix.zero_apply, show V.hT (Φ.e i) (Φ.e j) = 0 from Φ.ee j i, map_zero]

theorem frame_ff : cT (sigR R hc.sig) (frameMat (F := F) V R Φ.f) * JR (F := F) R V.gram *
    frameMat (F := F) V R Φ.f = 0 := by
  rw [cT_frameMat_mul]
  ext i j
  rw [Matrix.of_apply, Matrix.zero_apply, show V.hT (Φ.f i) (Φ.f j) = 0 from Φ.ff j i, map_zero]

theorem frame_fe : cT (sigR R hc.sig) (frameMat (F := F) V R Φ.f) * JR (F := F) R V.gram *
    frameMat (F := F) V R Φ.e = 1 := by
  rw [cT_frameMat_mul]
  ext i j
  rw [Matrix.of_apply, show V.hT (Φ.f i) (Φ.e j) = _ from Φ.ef j i, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem frame_ef : cT (sigR R hc.sig) (frameMat (F := F) V R Φ.e) * JR (F := F) R V.gram *
    frameMat (F := F) V R Φ.f = 1 := by
  have h := congrArg (cT (sigR R hc.sig)) (frame_fe hc Φ R)
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT' _ (sig_sig hc R), cT_JR, Formalism.UG.cT_one, ← Matrix.mul_assoc] at h
  exact h

end Wf

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {V : HSpace E} {L : Submodule (𝓞 E) (Fin V.rank → E)} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)}

theorem coordR_mem_latLoc {x : V.V} (hx : V.frame.equivFun x ∈ L) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V (Fv F v) x ∈ GlobalTheory.AdelicU.latLoc F L v := by
  have := GlobalTheory.AdelicU.tmul_mem_latLoc (F := F) (v := v) (one_mem (v.adicCompletionIntegers F)) hx
  convert this using 1
  funext i
  simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR, inclR]

theorem frameMat_mulVec_mem {k : ℕ} (x : Fin k → V.V) (hx : ∀ i, V.frame.equivFun (x i) ∈ L)
    (c : Fin k → Fv F v ⊗[F] E) (hcv : ∀ i, c i ∈ intLoc F E v) :
    frameMat (F := F) V (Fv F v) x *ᵥ c ∈ GlobalTheory.AdelicU.latLoc F L v := by
  have e : frameMat (F := F) V (Fv F v) x *ᵥ c =
      ∑ i, (⟨c i, hcv i⟩ : intLoc F E v) • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V (Fv F v) (x i) := by
    funext y
    simp [Matrix.mulVec, dotProduct, frameMat, Finset.sum_apply, Subring.smul_def, mul_comm]
  rw [e]
  exact sum_mem fun i _ => Submodule.smul_mem _ _ (coordR_mem_latLoc (hx i))

theorem coef_mem (hsd : IsSelfDualAt hc.sig V.gram L v) {k : ℕ} (x : Fin k → V.V)
    (hx : ∀ i, V.frame.equivFun (x i) ∈ L) {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.AdelicU.latLoc F L v)
    (i : Fin k) :
    ((cT (sigR (Fv F v) hc.sig) (frameMat (F := F) V (Fv F v) x) * JR (F := F) (Fv F v) V.gram) *ᵥ y) i ∈
      intLoc F E v := by
  rw [cT_mul_mulVec_apply]
  have hy' : y ∈ dualLoc hc.sig V.gram L v := hsd ▸ hy
  exact hy' _ (coordR_mem_latLoc (hx i))

theorem mulVec_mem_intLoc {k l : ℕ} (a : Matrix (Fin k) (Fin l) (Fv F v ⊗[F] E)) (ha : ∀ i j, a i j ∈ intLoc F E v)
    (w : Fin l → Fv F v ⊗[F] E) (hw : ∀ j, w j ∈ intLoc F E v) (i : Fin k) : (a *ᵥ w) i ∈ intLoc F E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (ha i j) (hw j)

theorem sub_one_mem_intLoc {k : ℕ} (a : Matrix (Fin k) (Fin k) (Fv F v ⊗[F] E)) (ha : ∀ i j, a i j ∈ intLoc F E v)
    (i j : Fin k) : (a - 1) i j ∈ intLoc F E v := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  refine sub_mem (ha i j) ?_
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem levi_mulVec_mem (hsd : IsSelfDualAt hc.sig V.gram L v) (Φ : WittFrame V)
    (he : ∀ i, V.frame.equivFun (Φ.e i) ∈ L) (hf : ∀ i, V.frame.equivFun (Φ.f i) ∈ L)
    {a b : Matrix (Fin (wittIndex V)) (Fin (wittIndex V)) (Fv F v ⊗[F] E)} (ha : ∀ i j, a i j ∈ intLoc F E v)
    (hb : ∀ i j, b i j ∈ intLoc F E v) {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.AdelicU.latLoc F L v) :
    frameLevi (sigR (Fv F v) hc.sig) (JR (F := F) (Fv F v) V.gram) (frameMat (F := F) V (Fv F v) Φ.e)
      (frameMat (F := F) V (Fv F v) Φ.f) a b *ᵥ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  set s := sigR (Fv F v) hc.sig
  set J := JR (F := F) (Fv F v) V.gram
  set E0 := frameMat (F := F) V (Fv F v) Φ.e
  set F0 := frameMat (F := F) V (Fv F v) Φ.f
  have e : frameLevi s J E0 F0 a b *ᵥ y =
      y + E0 *ᵥ (a *ᵥ ((cT s F0 * J) *ᵥ y)) + F0 *ᵥ (b *ᵥ ((cT s E0 * J) *ᵥ y)) := by
    simp only [frameLevi, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  refine add_mem (add_mem hy ?_) ?_
  · exact frameMat_mulVec_mem Φ.e he _ (mulVec_mem_intLoc a ha _ (coef_mem hc hsd Φ.f hf hy))
  · exact frameMat_mulVec_mem Φ.f hf _ (mulVec_mem_intLoc b hb _ (coef_mem hc hsd Φ.e he hy))

end Lat

end GlobalTheory.LeviIntegral

end

noncomputable section

namespace GlobalTheory.LeviIntegral

open scoped Matrix TensorProduct
open Formalism.UG (cT hform)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (sigR inclR JR hR HR HA)
open GlobalTheory.TruncKer

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_mem_stabLoc_mul_frame (hc : CMData F E) {V : HSpace E} (Φ : WittFrame V)
    (L : Submodule (𝓞 E) (Fin V.rank → E)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hsd : GlobalTheory.AdelicU.IsSelfDualAt hc.sig V.gram L v)
    (he : ∀ i, V.frame.equivFun (Φ.e i) ∈ L) (hf : ∀ i, V.frame.equivFun (Φ.f i) ∈ L)
    (α : GL (Fin (wittIndex V)) (Fv F v ⊗[F] E)) (hα : ∀ i j, α.1 i j ∈ intLoc F E v)
    (hα' : ∀ i j, (α⁻¹).1 i j ∈ intLoc F E v) :
    ∃ m : GlobalTheory.AdelicU.GLoc hc.sig V.gram v, m ∈ GlobalTheory.AdelicU.stabLoc hc.sig V.gram L v ∧
      (HA.mat (F := F) (Fv F v) hc.sig V.gram m).1 * frameMat (F := F) V (Fv F v) Φ.e =
        frameMat (F := F) V (Fv F v) Φ.e * α.1 := by
  set s := sigR (Fv F v) hc.sig
  set J := JR (F := F) (Fv F v) V.gram
  set E0 := frameMat (F := F) V (Fv F v) Φ.e
  set F0 := frameMat (F := F) V (Fv F v) Φ.f
  have hs : ∀ z, s (s z) = z := sig_sig hc (Fv F v)
  have hJ : cT s J = J := cT_JR hc V (Fv F v)
  have hEE : cT s E0 * J * E0 = 0 := frame_ee hc Φ (Fv F v)
  have hFF : cT s F0 * J * F0 = 0 := frame_ff hc Φ (Fv F v)
  have hFE : cT s F0 * J * E0 = 1 := frame_fe hc Φ (Fv F v)
  have hEF : cT s E0 * J * F0 = 1 := frame_ef hc Φ (Fv F v)
  let Mof : GL (Fin (wittIndex V)) (Fv F v ⊗[F] E) → Matrix (Fin V.rank) (Fin V.rank) (Fv F v ⊗[F] E) :=
    fun X => frameLevi s J E0 F0 (X.1 - 1) (cT s (X⁻¹).1 - 1)
  have hmul : ∀ X, Mof X * Mof X⁻¹ = 1 := by
    intro X
    simp only [Mof]
    rw [frameLevi_mul hEE hFF hFE hEF, inv_inv]
    have h1 : X.1 - 1 + ((X⁻¹).1 - 1) + (X.1 - 1) * ((X⁻¹).1 - 1) = 0 := by
      have : X.1 - 1 + ((X⁻¹).1 - 1) + (X.1 - 1) * ((X⁻¹).1 - 1) = X.1 * (X⁻¹).1 - 1 := by noncomm_ring
      rw [this, Units.mul_inv, sub_self]
    have h2 : cT s (X⁻¹).1 - 1 + (cT s X.1 - 1) + (cT s (X⁻¹).1 - 1) * (cT s X.1 - 1) = 0 := by
      have : cT s (X⁻¹).1 - 1 + (cT s X.1 - 1) + (cT s (X⁻¹).1 - 1) * (cT s X.1 - 1) =
          cT s (X⁻¹).1 * cT s X.1 - 1 := by noncomm_ring
      rw [this, ← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one, sub_self]
    rw [h1, h2, frameLevi_zero]
  have hmul' : Mof α⁻¹ * Mof α = 1 := by
    have := hmul α⁻¹
    rwa [inv_inv] at this
  have hunit : cT s (Mof α) * J * Mof α = J := by
    refine frameLevi_unitary hs hJ hEE hFF hFE hEF ?_ ?_
    · rw [cT_sub', cT_cT' s hs, Formalism.UG.cT_one]
      have : α.1 - 1 + ((α⁻¹).1 - 1) + ((α⁻¹).1 - 1) * (α.1 - 1) = (α⁻¹).1 * α.1 - 1 := by noncomm_ring
      rw [this, Units.inv_mul, sub_self]
    · rw [cT_sub', Formalism.UG.cT_one]
      have : cT s (α⁻¹).1 - 1 + (cT s α.1 - 1) + (cT s α.1 - 1) * (cT s (α⁻¹).1 - 1) =
          cT s α.1 * cT s (α⁻¹).1 - 1 := by noncomm_ring
      rw [this, ← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one, sub_self]
  have hstab : ∀ X : GL (Fin (wittIndex V)) (Fv F v ⊗[F] E), (∀ i j, X.1 i j ∈ intLoc F E v) →
      (∀ i j, (X⁻¹).1 i j ∈ intLoc F E v) → ∀ y, y ∈ GlobalTheory.AdelicU.latLoc F L v →
        Mof X *ᵥ y ∈ GlobalTheory.AdelicU.latLoc F L v := fun X hX hX' y hy =>
    levi_mulVec_mem hc hsd Φ he hf (sub_one_mem_intLoc _ hX)
      (sub_one_mem_intLoc _ fun i j => GlobalTheory.AdelicU.sigR_mem_intLoc hc.sig (hX' j i)) hy
  let u : GL (Fin V.rank) (Fv F v ⊗[F] E) := ⟨Mof α, Mof α⁻¹, hmul α, hmul'⟩
  have hu : u ∈ HR (Fv F v) hc.sig V.gram := hunit
  let m : GlobalTheory.AdelicU.GLoc hc.sig V.gram v := (⟨u, hu⟩ : HR (Fv F v) hc.sig V.gram)
  refine ⟨m, ?_, ?_⟩
  · rw [GlobalTheory.AdelicU.mem_stabLoc]
    intro y
    change y ∈ _ ↔ Mof α *ᵥ y ∈ _
    constructor
    · exact hstab α hα hα' y
    · intro hy
      have := hstab α⁻¹ hα' (by rw [inv_inv]; exact hα) _ hy
      rwa [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec] at this
  · change Mof α * E0 = E0 * α.1
    simp only [Mof]
    rw [frameLevi_mul_isotropic hEE hFE, add_sub_cancel]

end Main

end GlobalTheory.LeviIntegral

end

namespace GlobalTheory.LeviIntegral

theorem exists_stabLoc_mul_frame_of_isGood : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) → (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) → ∃ m : GLoc D.sp.cm.sig V.gram v, m ∈ stabLoc D.sp.cm.sig V.gram L v ∧ (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram m).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * α.1 := by
  intro D V Φ L a hgood v α hα hα'
  exact exists_mem_stabLoc_mul_frame D.sp.cm Φ L v (hgood.2.1 v) (fun i => (hgood.2.2.1 i).1)
    (fun i => (hgood.2.2.1 i).2) α hα hα'

end GlobalTheory.LeviIntegral
