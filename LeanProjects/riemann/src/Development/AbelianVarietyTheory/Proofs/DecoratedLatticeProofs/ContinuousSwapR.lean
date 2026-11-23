import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPartIso

section Swap

theorem continuous_bc {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (φ : A →+* B) (h : Continuous φ) : Continuous (bc (n := Fin n) φ) :=
  Continuous.units_map _ (continuous_id.matrix_map h)

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') {g : GL (Fin n) A} (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' J' := by
  have hg' : cT σ g.1 * J * g.1 = J := hg
  have h2 := congrArg (fun M => M.map φ) hg'
  simp only [Matrix.map_mul, hJ] at h2
  have e1 : cT σ' (g.1.map φ) = (cT σ g.1).map φ := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, h]
  change cT σ' (g.1.map φ) * J' * g.1.map φ = J'
  rw [e1]; exact h2

def ujEquiv {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (σ : A →+* A) (σ' : B →+* B) (φ : A ≃+* B) (hc : Continuous φ) (hc' : Continuous φ.symm)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') : UJ σ J ≃ₜ* UJ σ' J' where
  toFun g := ⟨bc φ.toRingHom g.1, bc_mem _ _ φ.toRingHom h _ _ hJ g.2⟩
  invFun g := ⟨bc φ.symm.toRingHom g.1, bc_mem _ _ φ.symm.toRingHom (fun x => φ.injective (by
      change φ (σ (φ.symm x)) = φ (φ.symm (σ' x))
      rw [← h, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])) _ _
      (hJ ▸ Matrix.ext fun _ _ => φ.symm_apply_apply _) g.2⟩
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.symm_apply_apply _))
  right_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.apply_symm_apply _))
  map_mul' g h := Subtype.ext (map_mul (bc φ.toRingHom) g.1 h.1)
  continuous_toFun := ((continuous_bc φ.toRingHom hc).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_bc φ.symm.toRingHom hc').comp continuous_subtype_val).subtype_mk _

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

def swapR : R ⊗[F] E ≃+* E ⊗[F] R := (Algebra.TensorProduct.comm F R E).toRingEquiv

theorem continuous_swapR :
    @Continuous _ _ _ (tensTopL (F := F) (E := E) R) (swapR (F := F) (E := E) R) ∧
    @Continuous _ _ (tensTopL (F := F) (E := E) R) _ (swapR (F := F) (E := E) R).symm := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) R
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd R (E ⊗[F] R)
  haveI := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let L : R ⊗[F] E ≃ₗ[R] E ⊗[F] R :=
    { (swapR (F := F) (E := E) R).toAddEquiv with
      map_smul' := fun c y => by
        change swapR (F := F) (E := E) R (c • y) = c • swapR (F := F) (E := E) R y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl }
  exact ⟨IsModuleTopology.continuous_of_linearMap L.toLinearMap,
    IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [TopologicalSpace R] in
theorem swapR_sig (x : R ⊗[F] E) :
    Formalism.UG.sigR σ R (swapR R x) = swapR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def swapU : letI := tensTopL (F := F) (E := E) R; HA R σ J ≃ₜ* UPts σ J R :=
  letI := tensTopL (F := F) (E := E) R
  ujEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (Formalism.UG.sigR σ R) (swapR R) (continuous_swapR R).1 (continuous_swapR R).2
    (swapR_sig R σ) (JR R J) (J.map (inclE (F := F) R)) (Matrix.ext fun _ _ => rfl)

end Swap

section Fin

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def finEquiv : finPts σ J ≃ₜ* GFin σ J where
  toFun g := projFin σ J g.1
  invFun y := ⟨ofFin σ J y, mem_finPts.2 (projInf_ofFin σ J y)⟩
  left_inv g := Subtype.ext (ext_inf_fin σ J ((projInf_ofFin σ J _).trans (mem_finPts.1 g.2).symm)
    (projFin_ofFin σ J _))
  right_inv y := projFin_ofFin σ J y
  map_mul' g h := map_mul (projFin σ J) g.1 h.1
  continuous_toFun := (continuous_projFin σ J).comp continuous_subtype_val
  continuous_invFun := (continuous_ofFin σ J).subtype_mk _

end Fin

theorem exists_finIso : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F); ∃ e : ↥(GfC V) ≃ₜ* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), ∀ g, (e g).1.1 = finM V hn g.1 := by
  intro D V n hn
  subst hn
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  exact ⟨(finEquiv D.sp.cm.sig V.gram).trans
    (swapU (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.sp.cm.sig V.gram), fun g => rfl⟩

end GlobalTheory.FinPartIso
