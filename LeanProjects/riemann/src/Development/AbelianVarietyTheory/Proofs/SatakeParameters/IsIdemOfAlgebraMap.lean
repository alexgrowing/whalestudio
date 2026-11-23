import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.StatementG
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHost
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivial
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

def infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def intA : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

variable {F}

def evF (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom

def ordAt (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def sgT (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] Af F ⊗[F] E :=
  TensorProduct.map (GlobalTheory.AutFunCompare.sgV v) LinearMap.id

def IsIdemOf (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) : Prop :=
  infP F E e = 0 ∧ evF E v (finP F E e) = 1 ∧ ∀ w, w ≠ v → evF E w (finP F E e) = 0

variable {E}

omit [NumberField E] in
theorem evF_sgT_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) : evF E v (sgT E v y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_same]

omit [NumberField E] in
theorem evF_sgT_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v ⊗[F] E) : evF E w (sgT E v y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]

omit [NumberField E] in
theorem evF_ext {z z' : Af F ⊗[F] E} (h : ∀ v, evF E v z = evF E v z') : z = z' :=
  GlobalTheory.LatticeLocalGlobal.ext_components z z' h

omit [NumberField E] in
theorem evF_finP_incl (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    evF E v (finP F E (inclR (AF F) x)) = inclR (Fv F v) x := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F 1) ⊗ₜ x = (1 : Fv F v) ⊗ₜ x
  rw [map_one, map_one]

omit [NumberField E] in

theorem isIdemOf_algebraMap {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α = 0) :
    IsIdemOf E v (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α)) := by
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · show (0 : Ainf F) ⊗ₜ (1 : E) = 0
    exact TensorProduct.zero_tmul _ _
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α ⊗ₜ (1 : E) = 1
    rw [h1]; rfl
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α ⊗ₜ (1 : E) = 0
    rw [h2 w hw]; exact TensorProduct.zero_tmul _ _

variable [StarRing E] (hc : CMData F E) (V : HSpace E)

abbrev lamHat (F : Type) [Field F] [NumberField F] [Algebra F E] (V : HSpace E) :
    AddSubgroup (Fin V.rank → Af F ⊗[F] E) :=
  latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0}

def locMat (v : HeightOneSpectrum (𝓞 F)) : HA (AF F) hc.sig V.gram →* GL (Fin V.rank) (Fv F v ⊗[F] E) :=
  (Formalism.UG.bc (evF E v)).comp ((Formalism.UG.bc (finP F E)).comp (HR (AF F) hc.sig V.gram).subtype)

def Supp (f : AF F ⊗[F] E) (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ i j, f * ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j = ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j

def IsFin (g : HA (AF F) hc.sig V.gram) : Prop :=
  Formalism.UG.bc (infP F E) (HA.mat (AF F) hc.sig V.gram g) = 1

def Stab (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ y, y ∈ lamHat F V ↔ (finMat hc.sig V.gram g).mulVec y ∈ lamHat F V

def DivG (e : AF F ⊗[F] E) (ϖ : E) (d : Fin V.rank → ℤ) (α : HA (AF F) hc.sig V.gram) : Prop :=
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E),
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → (fun a => finP F E e * B.mulVec z a) ∈ lamHat F V) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * y a) = fun a => finP F E e * B.mulVec z a) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) ∧
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∃ y ∈ lamHat F V,
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a)

theorem locMat_val (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    (locMat hc V v g).1 = (finMat hc.sig V.gram g).map (evF E v) := rfl

theorem locMat_mem (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    locMat hc V v g ∈ HR (Fv F v) hc.sig V.gram :=
  (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V v (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g)).2

theorem mem_lamHat_iff (y : Fin V.rank → Af F ⊗[F] E) :
    y ∈ lamHat F V ↔ ∀ v, (fun i => evF E v (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v :=
  GlobalTheory.LatticeLocalGlobal.mem_latHat_iff F E V y

def IsFrameAt (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) : Prop :=
  ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ ∀ i, (h⁻¹).1.mulVec x i ∈ ordAt E v

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

theorem mem_ordAt_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (z : LocAlg v) :
    z ∈ ordAt E v ↔ z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le (t := (locOrder v).toSubring)).2 ?_ hz
    rintro _ ⟨a, ha, x, rfl⟩
    have := mul_mem ((locOrder v).algebraMap_mem ⟨a, ha⟩) (locEmb_mem_locOrder v x)
    have e : algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (LocAlg v) ⟨a, ha⟩ * locEmb v (x : E) =
        a ⊗ₜ (x : E) := by
      show (a ⊗ₜ 1 : LocAlg v) * (1 ⊗ₜ (x : E)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e] at this
    exact this
  · intro hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Subring.subset_closure ⟨1, one_mem _, a, rfl⟩
    | algebraMap r => exact Subring.subset_closure ⟨r, r.2, 1, rfl⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_orthonormal (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ h : GL (Fin V.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), IsFrameAt V v h ∧
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 * JR (Fv (maximalRealSubfield E) v) V.gram * h.1 = 1 := by
  haveI := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (V.gramᵀ a b) = V.gramᵀ b a :=
    fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd
    (GlobalTheory.LocalConjugacy.isLattice_coordLat V V.L0 V.standardTuple_isLattice)
    (GlobalTheory.LocalConjugacy.selfDual_coordLat V V.L0 V.baseLattice_isUnimodular) v
  refine ⟨h, fun x => (GlobalTheory.LocalConjugacy.mem_latLoc_iff V v x).trans ((h2 x).trans
    (forall_congr' fun i => (mem_ordAt_iff v _).symm)), ?_⟩
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  exact h3

end CM

end GlobalTheory.PlaceComp
