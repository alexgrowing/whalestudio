import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevProd

open GlobalTheory.MtInProd
open Formalism.L2.NX (locM InLevG InParah inParah_one)
open Classical

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eA (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    s.proj (eA L v) = if s.v = v then 1 else 0 := by
  show s.i 1 * (idemF (L := L) v) s.v = _
  rw [map_one, one_mul, idemF_apply]

theorem locM_cut (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n) :
    locM s (cutGA (eA_mul v) (conj_eA v) κ) = if s.v = v then locM s κ else 1 := by
  show ((cutGA (eA_mul v) (conj_eA v) κ).1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj = _
  rw [cutGA_val, map_cutMat, proj_eA]
  split_ifs
  · rw [cutMat_one_left]; rfl
  · rw [cutMat_zero_left]

theorem inLevG_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) :
    InLevG v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) := by
  refine ⟨inParah_one v r, fun a b _ _ => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · have h : a ≠ b := fun e => by subst e; exact lt_irrefl _ hba
    rw [Matrix.one_apply_ne h, map_zero]
    exact WithZero.zero_lt_coe _
  · subst hab
    rw [Matrix.one_apply_eq, sub_self, map_zero]
    exact WithZero.zero_lt_coe _

end Gen

theorem main : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  intro D X i b k Q ψ hA j κ hκ v
  obtain ⟨hU, hG, hQ, hD⟩ := ((cell X b hA j).J_mem κ).1 hκ
  refine ⟨cutGA (eA_mul v) (conj_eA v) κ, ((cell X b hA j).J_mem _).2 ⟨cutGA_mem_Umax _ _ (eA_mem v) hU, fun kv => ?_,
    fun P hP => ?_, fun P hP => ?_⟩, triv_cut_eA v κ, cut_eA_at v κ⟩
  · rw [locM_cut]; split_ifs
    · exact hG kv
    · exact inLevG_one _ _
  · rw [locM_cut]; split_ifs
    · exact hQ P hP
    · exact inParah_one _ _
  · rw [locM_cut]; split_ifs
    · exact hD P hP
    · exact inParah_one _ _

end GlobalTheory.LevProd

end
