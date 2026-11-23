import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section General

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_right {ι : Type} (s : Finset ι) (c : ι → E) (g : ι → V) (u : V) :
    H.h u (∑ i ∈ s, c i • g i) = ∑ i ∈ s, M.L.cj (c i) * H.h u (g i) := by
  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem span_eq_sum (g : ι → V) (hG : IsUnit (gramH H g).det) (u : V)
    (hu : u ∈ Submodule.span E (Set.range g)) :
    u = ∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i := by
  have hs : (∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i) ∈
      Submodule.span E (Set.range g) :=
    (Submodule.mem_span_range_iff_exists_fun E).2 ⟨_, rfl⟩
  have h' : pairSpan H g ⟨u, hu⟩ = pairSpan H g ⟨_, hs⟩ := by
    show pairing H g u = pairing H g (∑ i, (Matrix.vecMul (fun j => H.h u (g j)) (gramH H g)⁻¹) i • g i)
    rw [pairing_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
    rfl
  exact congrArg Subtype.val ((pairSpan_bij H g hG).1 h')

theorem h_eq_form (g : ι → V) (hG : IsUnit (gramH H g).det) (u w : V)
    (hu : u ∈ Submodule.span E (Set.range g)) :
    H.h u w = ∑ i, ∑ j, H.h u (g i) * (gramH H g)⁻¹ i j * M.L.cj (H.h w (g j)) := by
  refine (congrArg (fun x => H.h x w) (span_eq_sum H g hG u hu)).trans ?_
  rw [h_sum_left]
  simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [H.h_herm w (g j)]

end General

section Term

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def GoodL {r : ℕ} (t : Term V M r) : Prop :=
  M.split = none ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' ∧
    IsUnit (H.Dl t.f t.f' (r + 1)) ∧ H.Dl t.f t.f' r = 0

theorem mmfam_none (hs : M.split = none) {r : ℕ} (t : Term V M r) :
    H.MMfam t = Sum.elim t.f t.f' := by
  unfold HermSp.MMfam; rw [hs]

theorem gramH_eq {r : ℕ} {t : Term V M r} (hg : GoodL H t) :
    gramH H (H.MMfam t) = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  rw [gramC_eq H _ _ _ _ hg.2.1 hg.2.2.1, mmfam_none H hg.1]
  ext i j
  rfl

theorem unit_gramH {r : ℕ} {t : Term V M r} (hg : GoodL H t) :
    IsUnit (gramH H (H.MMfam t)).det := by
  rw [gramH_eq H hg]
  exact unit_gramC H _ _ _ _ hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2

theorem relSub_eq {r : ℕ} {t : Term V M r} (hg : GoodL H t) :
    relSub H t = relC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  ext y
  show (∃ c : Ix r → M.L.O, ∀ j, (y j : E) = ∑ i, (c i : E) * gramH H (H.MMfam t) i j) ↔ _
  rw [gramH_eq H hg]
  rfl

def Psi {r : ℕ} {t : Term V M r} (hg : GoodL H t) :
    DDt H t ≃ₗ[M.L.O] DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') :=
  (ddEquiv H t (unit_gramH H hg)).trans (Submodule.quotEquivOfEq _ _ (relSub_eq H hg))

theorem Psi_mk {r : ℕ} {t : Term V M r} (hg : GoodL H t) (u : ↥(MMsharp H t)) :
    Psi H hg (ddMk H t u) = Submodule.Quotient.mk (sharpEquiv H t (unit_gramH H hg) u) := rfl

theorem h_eq_formC {r : ℕ} {t : Term V M r} (hg : GoodL H t) (u w : ↥(MMsharp H t)) :
    H.h u w = formC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') (sharpEquiv H t (unit_gramH H hg) u)
      (sharpEquiv H t (unit_gramH H hg) w) := by
  rw [h_eq_form H (H.MMfam t) (unit_gramH H hg) u w ((mem_MMsharp_iff H t u).1 u.2).1, formC,
    ← gramH_eq H hg]
  rfl

end Term

end Formalism.L2.SG.LocalCountModules.LocCntCommon
