import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevChiAt

section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eq_comp (s : SplitPlace L) :
    s.proj = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom.comp
      (compAt L s.v) := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem locM_eq_one (s : SplitPlace L) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (κ : GAf L n)
    (hκ : TrivOutside {v} κ) (hne : s.v ≠ v) : NX.locM s κ = 1 := by
  have h := hκ s.v (by simpa using hne)
  have e : NX.locM s κ = ((κ.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)).map
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom := by
    rw [Matrix.map_map, ← RingHom.coe_comp, ← proj_eq_comp]
    rfl
  rw [e, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end Gen

variable {D : D7}

section Red
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem intLift_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    NX.intLift v (1 : v.adicCompletion (maximalRealSubfield L)) = 1 := by
  unfold NX.intLift
  split_ifs with h
  · rfl
  · exact absurd (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem h

theorem intLift_zero (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    NX.intLift v (0 : v.adicCompletion (maximalRealSubfield L)) = 0 := by
  unfold NX.intLift
  split_ifs with h
  · rfl
  · rfl

theorem redMat_topR_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) {n r : ℕ} (h : r ≤ n) :
    NX.redMat v red (NX.topR h (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))) = 1 := by
  ext a c
  simp only [NX.redMat, NX.topR, Matrix.submatrix_apply]
  by_cases hac : a = c
  · subst hac; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne (fun e => hac (Fin.castLE_injective _ e)), Matrix.one_apply_ne hac, intLift_zero, map_zero]

theorem detT_one {R : Type} [CommRing R] (n r : ℕ) : NX.detT r (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold NX.detT
  have : (1 : Matrix (Fin n) (Fin n) R).submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) = 1 := by
    ext a c
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

end Red

theorem gVal_one (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  classical
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 := by
    apply Units.ext
    rw [NX.glOf_val _ (by simp)]
    rfl
  have hpsi : NX.psiUTot D i b (1 : G0g D.nd) = 1 := by
    unfold NX.psiUTot
    rw [dif_pos (Subgroup.one_mem _)]
    have : (⟨1, Subgroup.one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [this, map_one]; rfl
  unfold NX.gVal
  erw [redMat_topR_one, hgl, Pi.mulSingle_one, hpsi, detT_one, intLift_one, map_one red, map_one, one_mul]
  rw [dif_pos isUnit_one]
  have : (isUnit_one : IsUnit (1 : ZMod (D.host.g kv.1))).unit = 1 := Units.ext rfl
  rw [this, map_one]
  exact map_one _

theorem loc_one_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) :
    NX.locM s (1 : GAf L n) = 1 := by
  simp [NX.locM]

theorem chi_eq_at : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ (h : κ ∈ M.J), TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      ((M.χ ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) =
        NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hkv hQ hD κ h hκ
  have hG : ∀ kv, kv ≠ kv0 → NX.locM (M.sp (NX.pG D kv)) κ = 1 := fun kv hne => locM_eq_one _ κ hκ (hkv kv hne)
  have hQl : ∀ P ∈ M.QP, NX.locM (M.sp P) κ = 1 := fun P hP => locM_eq_one _ κ hκ (hQ P hP)
  have hDl : ∀ P ∈ M.DP, NX.locM (M.sp P) κ = 1 := fun P hP => locM_eq_one _ κ hκ (hD P hP)
  have h1 := M.chi_eq 1 M.J.one_mem
  have e1 : (⟨1, M.J.one_mem⟩ : M.J) = 1 := rfl
  rw [e1, map_one, Units.val_one] at h1
  simp only [loc_one_eq, gVal_one, Finset.prod_const_one, one_mul] at h1
  rw [M.chi_eq κ h, Fintype.prod_eq_single kv0 (fun kv hne => by rw [hG kv hne, gVal_one]), mul_assoc]
  conv_rhs => rw [← mul_one (NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ))]
  congr 1
  rw [h1]
  congr 1
  · exact Finset.prod_congr rfl fun P hP => by rw [hQl P hP]
  · exact Finset.prod_congr rfl fun P hP => by rw [hDl P hP]

end GlobalTheory.LevChiAt
