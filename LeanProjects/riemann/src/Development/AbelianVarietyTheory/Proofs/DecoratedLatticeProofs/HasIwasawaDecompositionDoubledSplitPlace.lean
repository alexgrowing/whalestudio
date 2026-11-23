import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

noncomputable section

namespace GlobalTheory.Core.Rk.IwSplit

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
open Formalism.UG (bc stabGL GLint cT)

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

def shear : GL ι A :=
  ⟨(Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm, (Matrix.fromBlocks 1 0 (-1) 1).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp,
    by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp⟩

theorem shear_mulVec (x y : m → A) : (shear e).1 *ᵥ pairVec e x y = pairVec e x (x + y) := by
  simp [mulVec_pairVec, shear]

theorem bc_shear {B : Type} [CommRing B] (f : A →+* B) : bc f (shear e) = shear e :=
  Units.ext (by
    change ((Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm).map f =
      (Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm
    simp [← Matrix.submatrix_map, Matrix.fromBlocks_map])

omit [DecidableEq m] [DecidableEq ι] in
theorem pair_dblGram (J : Matrix m m A) (x y x' y' : m → A) :
    pairVec e x y ⬝ᵥ dblGram e J *ᵥ pairVec e x' y' = x ⬝ᵥ J *ᵥ x' - y ⬝ᵥ J *ᵥ y' := by
  rw [dblGram, blkMat_mulVec, Matrix.neg_mulVec]
  simp [dotProduct, ← e.sum_comp, sub_eq_add_neg]

theorem keepsDiag_of_pairing {J : Matrix m m A} (hJ : IsUnit J.det) {x : Matrix ι ι A} {y : GL ι A}
    (h : ∀ u' u, (x *ᵥ u') ⬝ᵥ dblGram e J *ᵥ (y.1 *ᵥ u) = u' ⬝ᵥ dblGram e J *ᵥ u) (hy : y ∈ stabGL (diagSub A e)) :
    KeepsDiag e x := by
  refine keepsDiag_of_mulVec fun w hw => ?_
  obtain ⟨a, rfl⟩ := (mem_diagSub e).1 hw
  obtain ⟨s, t, hst⟩ : ∃ s t, x *ᵥ pairVec e a a = pairVec e s t := ⟨_, _, (pairVec_eta e _).symm⟩
  rw [hst, pairVec_mem_diagSub, ← sub_eq_zero]
  have h1 : ∀ b, (s - t) ⬝ᵥ J *ᵥ b = 0 := fun b => by
    obtain ⟨c, hc⟩ := (mem_diagSub e).1 ((inv_mem hy (pairVec e b b)).1 ((pairVec_mem_diagSub e).2 rfl))
    have h2 := h (pairVec e a a) ((y⁻¹).1 *ᵥ pairVec e b b)
    rw [Matrix.mulVec_mulVec _ y.1, Units.mul_inv, Matrix.one_mulVec, hst, hc, pair_dblGram, pair_dblGram,
      sub_self] at h2
    rw [sub_dotProduct, h2]
  funext i
  have h3 := h1 (J⁻¹ *ᵥ Pi.single i 1)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec, dotProduct_single, mul_one] at h3

end Pure

theorem iwasawa_diag {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {n : ℕ} (x : GL (Fin (n + n)) K) : ∃ k : GL (Fin (n + n)) V,
    x * bc (algebraMap V K) k ∈ stabGL (diagSub K (finSumFinEquiv (m := n) (n := n))) := by
  obtain ⟨k, b, hb, h⟩ := GlobalTheory.ValIwasawa.iwasawa V K (n + n) (x⁻¹ * shear finSumFinEquiv)
  refine ⟨k * (shear finSumFinEquiv)⁻¹, inv_mem_iff.1 (mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun w hw => ?_))⟩
  obtain ⟨a, rfl⟩ := (mem_diagSub _).1 hw
  have h1 : (x * bc (algebraMap V K) (k * (shear finSumFinEquiv)⁻¹))⁻¹ * shear finSumFinEquiv =
      shear finSumFinEquiv * b := by
    rw [map_mul, map_inv, bc_shear, mul_inv_rev, mul_assoc, h, mul_inv_rev, inv_inv, mul_assoc]
    exact congrArg _ (inv_mul_cancel_left _ _)
  have h2 : (b.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    refine hb ?_
    change (Fin.castAdd n j : ℕ) < Fin.natAdd n i
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h3 : pairVec finSumFinEquiv a a = (shear finSumFinEquiv).1 *ᵥ pairVec finSumFinEquiv a 0 := by
    rw [shear_mulVec, add_zero]
  rw [h3, Matrix.mulVec_mulVec, ← Units.val_mul, h1, Units.val_mul, ← Matrix.mulVec_mulVec,
    mulVec_pairVec _ b.1, h2, shear_mulVec, pairVec_mem_diagSub]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_siegelH_of_split (h : IsCMExt F E σ) (hQ : Q = dblGram finSumFinEquiv J) (hJ : J.det ≠ 0)
    (τ : E →ₐ[F] Fv F v) {g : GLoc σ Q v} (hg : splitHom σ Q τ g ∈ stabGL (diagSub (Fv F v) finSumFinEquiv)) :
    g ∈ siegelH (Fv F v) σ Q := by
  have e : Q.map τ = dblGram finSumFinEquiv (J.map τ) := by
    rw [hQ, dblGram, blkMat_map _ _ (map_zero _), dblGram, Matrix.map_neg _ (map_neg _)]
  have hu : IsUnit (J.map τ).det := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact ((map_ne_zero τ).2 hJ).isUnit
  have h1 := (keepsDiag_iff _).1 (mem_stabGL_diagSub.1 hg)
  have h2 := (keepsDiag_iff _).1 (keepsDiag_of_pairing finSumFinEquiv hu (x := (splitHom σ Q (τ.comp σ) g).1)
    (fun u' u => e ▸ pairing_splitHom τ g u' u) hg)
  refine mem_siegelOf.2 ((keepsDiag_iff _).2 fun i j => split_ext h τ ?_ ?_)
  · rw [map_add, map_add]; exact h1 i j
  · rw [map_add, map_add]; exact h2 i j

theorem hasIwasawa_of_algHom (h : IsCMExt F E σ) (hQ : Q = dblGram finSumFinEquiv J) (hJ : IsHermND σ J)
    (hQ' : IsHermND σ Q) (τ : E →ₐ[F] Fv F v) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hβ := (isLatticeFrame_dbl ha).isSplitBasis τ h
  rw [bc_blkGL, bc_blkGL] at hβ
  generalize bc (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (bc (compFin F E v) a) = β at hβ
  have hd : blkGL finSumFinEquiv (β, β) ∈ stabGL (diagSub (Fv F v) finSumFinEquiv) :=
    mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)
  obtain ⟨k, hk⟩ := iwasawa_diag (V := v.adicCompletionIntegers F) (splitEquivIn h hQ' τ (blkGL finSumFinEquiv (β, β)) g)
  obtain ⟨κ, hκ⟩ := (splitEquivIn h hQ' τ (blkGL finSumFinEquiv (β, β))).surjective
    (bc (algebraMap (v.adicCompletionIntegers F) (Fv F v)) k)
  have h1 : κ ∈ KFin σ Q L v :=
    (mem_stabLoc_iff_GLint h hQ' (isSelfDualAt_dbl hQ hL) hβ).2 (hκ ▸ ⟨k, rfl⟩)
  rw [← hκ, ← map_mul, splitEquivIn_apply] at hk
  have h2 := mul_mem (mul_mem hd hk) (inv_mem hd)
  rw [← mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right] at h2
  exact ⟨⟨g * κ, mem_siegelH_of_split h hQ hJ.2 τ h2⟩, κ⁻¹, inv_mem h1, (mul_inv_cancel_right g κ).symm⟩

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSelfDualAt_of_isSelfDualC {D : D7} {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) (v : FinPl D) :
    IsSelfDualAt D.sp.cm.sig A.gram L v :=
  (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2 hL.1).2
    (fun y => hL.2 y) v

theorem hasIwasawa_split : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D,
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v →
    HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  intro D A L hL v ⟨P, P', hne, hP, hP'⟩
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI := hL.1
  exact hasIwasawa_of_algHom (isCMExt_host D) (gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
    (GlobalTheory.Doubling.isHermND_gram (dblSp A)) τ L (isSelfDualAt_of_isSelfDualC hL v)

end Record

end GlobalTheory.Core.Rk.IwSplit

end
