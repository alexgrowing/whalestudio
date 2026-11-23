import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical

open NumberField IsDedekindDomain Matrix
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.IwasawaFinAd

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def coordV (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def locM (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  RingHom.mapMatrix (coordV v) M

def locGL (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin n) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (coordV v)).toMonoidHom

theorem locM_mul (v : HeightOneSpectrum (𝓞 F)) (M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    locM v (M * N) = locM v M * locM v N := map_mul _ _ _

theorem locM_one (v : HeightOneSpectrum (𝓞 F)) :
    locM v (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) = 1 := map_one _

theorem matrix_ext_loc {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ v, locM v M = locM v N) : M = N := by
  refine Matrix.ext fun i j => FiniteAdeleRing.ext F fun v => ?_
  exact congrFun (congrFun (h v) i) j

theorem gl_ext_loc {g h : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)} (e : ∀ v, locGL v g = locGL v h) :
    g = h :=
  Units.ext (matrix_ext_loc fun v => congrArg Units.val (e v))

def IntAt (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ v.adicCompletionIntegers F

theorem intAt_one (v : HeightOneSpectrum (𝓞 F)) : IntAt v (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (v.adicCompletionIntegers F).one_mem
  · exact (v.adicCompletionIntegers F).zero_mem

def glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    (⟨fun v => x v i j, hx.mono fun v h => h i j⟩ :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem locM_glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) (v : HeightOneSpectrum (𝓞 F)) :
    locM v (glueM x hx) = x v := by
  ext i j
  rfl

def glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) where
  val := glueM (fun v => (x v).val) (hx.mono fun _ h => h.1)
  inv := glueM (fun v => (x v)⁻¹.val) (hx.mono fun _ h => h.2)
  val_inv := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.mul_inv (x v)
  inv_val := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.inv_mul (x v)

theorem locGL_glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) (v : HeightOneSpectrum (𝓞 F)) :
    locGL v (glueGL x hx) = x v :=
  Units.ext (locM_glueM _ (hx.mono fun _ h => h.1) v)

theorem eventually_intAt (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v in Filter.cofinite, IntAt v (locM v M) := by
  unfold IntAt
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact (M i j).2

theorem upper_eq_uni_mul_diag {K : Type} [Field K] (b : GL (Fin n) K) (hb : b.val.BlockTriangular id) :
    ∃ u t : GL (Fin n) K, PIW.ClassFinD.IsUpperUni u.val ∧ PIW.ClassFinD.IsDiagM t.val ∧ b = u * t := by
  have hdet0 : b.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  have hne : ∀ i, b.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let t : GL (Fin n) K :=
    ⟨diagonal (fun i => b.val i i), diagonal (fun i => (b.val i i)⁻¹),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (b * t⁻¹).val i j = b.val i j * (b.val j j)⁻¹ := by
    intro i j
    change (b.val * diagonal (fun i => (b.val i i)⁻¹)) i j = _
    rw [mul_diagonal]
  refine ⟨b * t⁻¹, t, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, by group⟩
  · rw [hU, hb hij, zero_mul]
  · rw [hU, mul_inv_cancel₀ (hne i)]
  · exact diagonal_apply_ne _ hij

theorem isUpperUni_one {K : Type} [CommRing K] : PIW.ClassFinD.IsUpperUni (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun i j hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem isDiagM_one {K : Type} [CommRing K] : PIW.ClassFinD.IsDiagM (1 : Matrix (Fin n) (Fin n) K) :=
  fun i j hij => Matrix.one_apply_ne hij

theorem intAt_of_glint (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (v.adicCompletion F))
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) : IntAt v k.val ∧ IntAt v k⁻¹.val := by
  obtain ⟨K, rfl⟩ := hk
  refine ⟨fun i j => (K.val i j).2, fun i j => ?_⟩
  rw [← map_inv]
  exact ((K⁻¹).val i j).2

end GlobalTheory.IwasawaFinAd

namespace GlobalTheory.IwasawaFinAd

open PIW.ClassFinD

theorem iwasawaAf : PIW.ClassFinD.IwasawaAf := by
  classical
  intro F _ _ n g
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    IntAt v (locGL v g).val ∧ IntAt v (locGL v g)⁻¹.val
  have hgood : ∀ᶠ v in Filter.cofinite, good v := by
    refine (eventually_intAt g.val).and ((eventually_intAt (g⁻¹).val).mono fun v h => ?_)
    rw [← map_inv]
    exact h
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u t k : GL (Fin n) (v.adicCompletion F),
      IsUpperUni u.val ∧ IsDiagM t.val ∧ IntAt v k.val ∧ IntAt v k⁻¹.val ∧ locGL v g = u * t * k ∧
      (good v → u = 1 ∧ t = 1 ∧ k = locGL v g) := by
    intro v
    by_cases hv : good v
    · exact ⟨1, 1, locGL v g, isUpperUni_one, isDiagM_one, hv.1, hv.2, by rw [one_mul, one_mul],
        fun _ => ⟨rfl, rfl, rfl⟩⟩
    · obtain ⟨b, k, hb, hk, hbk⟩ := Formalism.UG.P.spherical_iwasawa F v (locGL v g)
      obtain ⟨u, t, hu, ht, rfl⟩ := upper_eq_uni_mul_diag b hb
      obtain ⟨hk1, hk2⟩ := intAt_of_glint v k hk
      exact ⟨u, t, k, hu, ht, hk1, hk2, hbk, fun h => absurd h hv⟩
  choose uL tL kL huL htL hkL hkL' hgL hgoodL using hloc
  have hu : ∀ᶠ v in Filter.cofinite, IntAt v (uL v).val ∧ IntAt v (uL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have ht : ∀ᶠ v in Filter.cofinite, IntAt v (tL v).val ∧ IntAt v (tL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).2.1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have hk : ∀ᶠ v in Filter.cofinite, IntAt v (kL v).val ∧ IntAt v (kL v)⁻¹.val :=
    Filter.Eventually.of_forall fun v => ⟨hkL v, hkL' v⟩
  refine ⟨glueGL uL hu, glueGL tL ht, glueGL kL hk, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_,
    ⟨fun i j v => hkL v i j, fun i j v => hkL' v i j⟩, ?_⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i j) = coordV v 0
    rw [map_zero]
    exact (huL v).1 i j hij
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i i) = coordV v 1
    rw [map_one]
    exact (huL v).2 i
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL tL ht).val i j) = coordV v 0
    rw [map_zero]
    exact htL v i j hij
  · refine gl_ext_loc fun v => ?_
    rw [map_mul, map_mul, locGL_glueGL, locGL_glueGL, locGL_glueGL]
    exact hgL v

end GlobalTheory.IwasawaFinAd
