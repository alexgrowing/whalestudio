import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeTame

def invTranspose {R : Type} [CommRing R] (n : ℕ) : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).val.transpose, g.val.transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invTranspose_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    (invTranspose n g).val = (g⁻¹).val.transpose := rfl

theorem invTranspose_inv_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((invTranspose n g)⁻¹).val = g.val.transpose := rfl

theorem invTranspose_invTranspose {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    invTranspose n (invTranspose n g) = g := by
  apply Units.ext
  rw [invTranspose_val, invTranspose_inv_val, Matrix.transpose_transpose]

theorem continuous_invTranspose {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (invTranspose (R := R) n) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invTranspose_mem_GLint {F : Type} [Field F] (n : ℕ) (O : Subring F) {g : GL (Fin n) F}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) : invTranspose n g ∈ Formalism.UG.GLint (Fin n) O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨invTranspose n h, Units.ext rfl⟩

theorem conjSP_proj {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : AL L) :
    (conjSP s).proj x = s.proj (conjAL L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem conjSP_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (κ : GA L n) :
    (conjSP s).loc n κ = invTranspose n (s.loc n κ) := by
  have hm : κ.1.val * conjT (conjAL L) κ.1.val = 1 := κ.2
  have h1 : (κ.1⁻¹).val = conjT (conjAL L) κ.1.val := Units.inv_eq_of_mul_eq_one_right hm
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (conjSP s).proj (κ.1.val i j) = s.proj ((κ.1⁻¹).val j i)
  rw [h1, conjSP_proj]
  rfl

theorem exists_conj_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∃ (K' : Subgroup (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L)))) (θ' : K' →* ℂˣ), (∀ g ∈ K', g ∈ Formalism.UG.GLint (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ'.ker : Set K') ∧ (∀ κ : GAf L n, (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K' ↔ s.loc n κ ∈ K) ∧ (∀ (κ : GAf L n) (h : s.loc n κ ∈ K) (h' : (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K'), θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc n κ, h'⟩ = θ ⟨s.loc n κ, h⟩) ∧ ∀ g (hg : g ∈ K) (g' : GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L))), g'.val = (g⁻¹).val.transpose → ∃ h' : g' ∈ K', θ' ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
  intro L _ _ _ n s K θ hK hθ
  have key : ∀ (g' : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g) (hg : g ∈ K),
      g' = invTranspose n g → ∃ h' : g' ∈ K.comap (invTranspose n),
        θ.comp ((invTranspose n).subgroupComap K) ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
    rintro g' g hg rfl
    refine ⟨by rw [Subgroup.mem_comap, invTranspose_invTranspose]; exact hg, ?_⟩
    rw [MonoidHom.comp_apply]
    exact congrArg θ (Subtype.ext (invTranspose_invTranspose n g))
  refine ⟨K.comap (invTranspose n), θ.comp ((invTranspose n).subgroupComap K), ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have := invTranspose_mem_GLint n _ (hK _ hg)
    rwa [invTranspose_invTranspose] at this
  · have hc : Continuous ((invTranspose n).subgroupComap K) :=
      Continuous.subtype_mk ((continuous_invTranspose n).comp continuous_subtype_val) _
    exact hθ.preimage hc
  · intro κ
    rw [conjSP_loc]
    change invTranspose n (invTranspose n (s.loc n κ)) ∈ K ↔ _
    rw [invTranspose_invTranspose]
  · intro κ h h'
    exact (key _ _ h (conjSP_loc n s κ)).2
  · intro g hg g' hg'
    exact key g' g hg (Units.ext hg')

end GlobalTheory.TypeTame
