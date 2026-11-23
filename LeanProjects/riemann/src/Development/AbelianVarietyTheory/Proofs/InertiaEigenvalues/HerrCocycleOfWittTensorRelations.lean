import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.HerrCocycleCriterion

theorem herr_of_tie {O D M : Type} [CommRing O] [AddCommGroup D] [Module O D] [AddCommGroup M]
    [Module O M] (γ φ : D →ₗ[O] D) (g Φ : M →ₗ[O] M) (j : D →ₗ[O] M) (hj : Function.Injective j)
    (y z : D) (b t : M) (hγ : j (γ y) = g (j y)) (hφ : j (φ z) = Φ (j z))
    (hc : Φ (g b) = g (Φ b)) (ht : Φ t = t) (hy : Φ b - b = j y) (hz : t + (g b - b) = j z) :
    (y, z) ∈ herrCocycles γ φ := by
  simp only [herrCocycles, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply]
  apply hj
  rw [map_zero, map_add, map_neg, map_sub, map_sub, hγ, hφ, ← hy, ← hz, map_add, map_sub, map_sub,
    hc, ht]
  abel

theorem TWmap_one {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R]
    [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (t : ↥T.L.T) :
    TWmap f T ((1 : R) ⊗ₜ[O] t) = (1 : R) ⊗ₜ[O] t := by
  simp [TWmap]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cocyc : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T := by
  intro D HW F l _ K s LL h T c b y z g₀ hg hy hz
  have h1 := ((F l).E K s LL h).tie.jD_act T (g₀ : ↥(GK K)) y
  rw [hg] at h1
  exact herr_of_tie _ _ _ _ _ (((F l).E K s LL h).tie.jD_inj T) y z b _ h1
    (((F l).E K s LL h).tie.jD_φ T z)
    (GlobalTheory.HerrClassMaps.TWmap_act _ _ (GlobalTheory.HerrClassMaps.phi_gRW (D.locA l) LL _) T _ b)
    (TWmap_one _ T _) hy hz

end GlobalTheory.NL.HerrCocycleCriterion
