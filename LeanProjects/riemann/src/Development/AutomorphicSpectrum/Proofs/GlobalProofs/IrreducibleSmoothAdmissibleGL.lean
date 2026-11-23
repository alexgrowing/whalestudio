import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import GroundTheory.AutomorphicForms.JacquetAdmissible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.SmGLBridge

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

def glReindex {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    GL a k ≃* GL b k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv

theorem continuous_glReindex {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) : Continuous (glReindex (k := k) e) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun g : GL a k => Matrix.reindex e e (g : Matrix a a k)
    exact Units.continuous_val.matrix_reindex e e
  · show Continuous fun g : GL a k => Matrix.reindex e e ((g⁻¹ : GL a k) : Matrix a a k)
    exact Units.continuous_coe_inv.matrix_reindex e e

theorem glReindex_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) (g : GL b k) : (glReindex (k := k) e).symm g = glReindex e.symm g := by
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.CompanionTheory.SmGLBridge

namespace GlobalTheory.CompanionTheory.SmGLBridge

theorem irreducibleAdmissible :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.SmGL.IrreducibleAdmissible k := by
  intro k _ _ _ _ n _ _ V _ _ π hsm hirr
  let e : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  let ψ : GL (Fin (Fintype.card n)) k ≃* GL n k := glReindex e
  have hψ : Continuous ψ := continuous_glReindex e
  have hψs : Continuous ψ.symm :=
    (continuous_glReindex (k := k) e.symm).congr (fun g => (glReindex_symm e g).symm)
  let π' : Representation ℂ (GL (Fin (Fintype.card n)) k) V := π.comp ψ.toMonoidHom
  have hsm' : GroundTheory.Automorphic.IsSmooth π' := by
    intro v
    have hs : (↑(GroundTheory.Automorphic.stabilizerOf π' v) : Set (GL (Fin (Fintype.card n)) k)) =
        ψ ⁻¹' {g | π g v = v} := by
      ext g
      simp only [SetLike.mem_coe, GroundTheory.Automorphic.mem_stabilizerOf, Set.mem_preimage, Set.mem_setOf_eq]
      exact Iff.rfl
    rw [hs]
    exact (hsm v).preimage hψ
  haveI : IsSimpleOrder (Subrepresentation π) := hirr
  let f : Subrepresentation π' ≃o Subrepresentation π :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
          have h := W.apply_mem_toSubmodule (ψ.symm g) hv
          simpa [π'] using h⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (ψ g) hv⟩
      left_inv := fun W => rfl
      right_inv := fun W => rfl
      map_rel_iff' := Iff.rfl }
  haveI : π'.IsIrreducible := f.isSimpleOrder
  have had := GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible hsm'
  refine ⟨hsm, fun K hKo hKc => ?_⟩
  let K' : Subgroup (GL (Fin (Fintype.card n)) k) := K.comap ψ.toMonoidHom
  let Hm : GL (Fin (Fintype.card n)) k ≃ₜ GL n k :=
    { toEquiv := ψ.toEquiv, continuous_toFun := hψ, continuous_invFun := hψs }
  have hK'o : IsOpen (K' : Set (GL (Fin (Fintype.card n)) k)) := hKo.preimage hψ
  have hK'c : IsCompact (K' : Set (GL (Fin (Fintype.card n)) k)) := Hm.isCompact_preimage.mpr hKc
  have hfd := had.2 K' hK'c hK'o
  have heq : GlobalTheory.PRep.fixed π K = GroundTheory.Automorphic.fixedVectors π' K' := by
    ext v
    rw [GroundTheory.Automorphic.mem_fixedVectors]
    show (∀ h : ↥K, π (h : GL n k) v = ((1 : ↥K →* ℂˣ) h : ℂ) • v) ↔ _
    constructor
    · intro hv g hg
      have h1 := hv ⟨ψ g, hg⟩
      simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
      exact h1
    · intro hv h
      have h1 := hv (ψ.symm h) (by simpa [K'] using h.2)
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      simpa [π'] using h1
  rw [heq]
  exact hfd

end GlobalTheory.CompanionTheory.SmGLBridge
