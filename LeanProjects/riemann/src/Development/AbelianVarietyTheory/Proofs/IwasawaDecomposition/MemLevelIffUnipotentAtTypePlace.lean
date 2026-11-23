import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharac
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
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

namespace GlobalTheory.LevUniLoc

theorem mem_iff_uniRT : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ, TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      (κ ∈ M.J ↔ NG.UniRT (M.sp (NX.pG D kv0)) D.R.r ((M.sp (NX.pG D kv0)).loc D.R.nV κ)) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hG hQ hD κ hκ
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, hL, -, -⟩
    obtain ⟨⟨_, hll⟩, huni⟩ := hL kv0
    exact ⟨⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, hll⟩, huni⟩
  · rintro ⟨⟨hGL, hll⟩, huni⟩
    refine ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, fun kv => ?_, fun P hP => ?_, fun P hP => ?_⟩
    · by_cases hk : kv = kv0
      · subst hk
        exact ⟨⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩, huni⟩
      · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hG kv hk)]; exact NX.inLevG_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hQ P hP)]; exact NX.inParah_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hD P hP)]; exact NX.inParah_one _ _

end GlobalTheory.LevUniLoc

end
