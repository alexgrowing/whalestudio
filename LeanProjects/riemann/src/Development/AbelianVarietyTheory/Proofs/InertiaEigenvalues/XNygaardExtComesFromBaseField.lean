import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SepOfHausdorff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.XNTransfer

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem exists_aN_iff (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (r : RA) (hr : E.io a = r) (w : TW RW T) :
    (∃ z ∈ aN W T a, E.jD T z = w) ↔ ∃ y ∈ E.jD T '' (W.N T : Set (W.DD T)), w = inclR r • y := by
  have hs : ∀ x : W.DD T, E.jD T (a • x) = inclR r • E.jD T x := fun x => by
    rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext, hr]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, hs x⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨x, hx, rfl⟩, hs x⟩

end Generic

theorem image_map_refl {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R] [AddCommGroup M]
    [Module O M] (S : Set (R ⊗[O] M)) :
    (TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap) '' S = S := by
  have : TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap = LinearMap.id :=
    TensorProduct.map_id
  rw [this]
  exact Set.image_id S

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X → ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, ((F l).E K s LL h).tie.jD T z = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) z') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT z' hz'
  have hN := ((GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0).2.2 T
    (resLt (K := K) (K' := K') (LL := LL) hle T) (LinearEquiv.refl ↥(OL LL) ↥T.L.T) (fun _ _ => rfl)).2 hT
    (restrict_crys D hle T hT)
  have hN2 := (image_map_refl (O := ↥(OL LL)) (R := RW LL) (M := ↥T.L.T) _).symm.trans hN
  have h1 := (exists_aN_iff ((F l).E K' s LL h').tie (resLt (K := K) (K' := K') (LL := LL) hle T) _ _
    (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').1 _).1 ⟨z', hz', rfl⟩
  refine (exists_aN_iff ((F l).E K s LL h).tie T _ _ (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).1 _).2 ?_
  refine h1.elim fun y hy => ⟨toTW hle T y, ?_, hy.2⟩
  exact hN2.subset hy.1

end GlobalTheory.NL.XNTransfer
