import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameProj

variable {D : D7}

noncomputable def bU (U : Submodule D.host.E (VS D).V) : Fin (Module.finrank D.host.E U) → (VS D).V :=
  fun i => (Module.finBasis D.host.E U i : (VS D).V)

noncomputable def gram (U : Submodule D.host.E (VS D).V) :
    Matrix (Fin (Module.finrank D.host.E U)) (Fin (Module.finrank D.host.E U)) D.host.E :=
  Matrix.of fun i j => (VS D).hT (bU U i) (bU U j)

noncomputable def pairs (U : Submodule D.host.E (VS D).V) :
    (VS D).V →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E) :=
  LinearMap.pi fun j => (VS D).hT (bU U j)

noncomputable def proj (U : Submodule D.host.E (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  Fintype.linearCombination D.host.E (bU U) ∘ₗ (gram U)⁻¹.mulVecLin ∘ₗ pairs U

theorem proj_apply (U : Submodule D.host.E (VS D).V) (x : (VS D).V) :
    proj U x = ∑ i, (Matrix.mulVec (gram U)⁻¹ (fun j => (VS D).hT (bU U j) x)) i • bU U i := by
  simp only [proj, pairs, LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply]
  rfl

variable (Z : LocDat D) (p : PlF D)

noncomputable def hR (v : Vp D p) : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep where
  toFun y := (locH Z p).h y v
  map_add' x y := (locH Z p).h_add_left x y v
  map_smul' a x := (locH Z p).h_smul_left a x v

noncomputable def pairsP (U : Submodule D.host.E (VS D).V) :
    Vp D p →ₗ[(D.s.atP p).Ep] (Fin (Module.finrank D.host.E U) → (D.s.atP p).Ep) :=
  LinearMap.pi fun j => hR Z p (baseChange₂ D p (bU U j))

noncomputable def projP (U : Submodule D.host.E (VS D).V) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  Fintype.linearCombination (D.s.atP p).Ep (fun i => baseChange₂ D p (bU U i)) ∘ₗ
    ((gram U)⁻¹.map (D.s.atP p).ιE).mulVecLin ∘ₗ pairsP Z p U

theorem projP_apply (U : Submodule D.host.E (VS D).V) (y : Vp D p) :
    projP Z p U y = ∑ i, (Matrix.mulVec ((gram U)⁻¹.map (D.s.atP p).ιE) (fun j => (locH Z p).h y (baseChange₂ D p (bU U j)))) i •
      baseChange₂ D p (bU U i) := by
  simp only [projP, pairsP, LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply]
  rfl

theorem baseChangeAt_proj (U : Submodule D.host.E (VS D).V) (x : (VS D).V) :
    baseChange₂ D p (proj U x) = projP Z p U (baseChange₂ D p x) := by
  rw [proj_apply, projP_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [baseChange_smul₂, RingHom.map_mulVec]
  congr 2
  funext j
  change _ = LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p (bU U j))
  rw [baseChangeAt_form Z.M p (Z.hcj p)]
  rfl

end GlobalTheory.FrameProj

namespace GlobalTheory.FrameProj
variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem localLattice_mono {Λ₁ Λ₂ : LV D} (h : Λ₁ ≤ Λ₂) : lattice₂ D Z.M p Λ₁ ≤ lattice₂ D Z.M p Λ₂ := by
  unfold lattice₂
  refine Submodule.span_mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem localLattice_sup (Λ₁ Λ₂ : LV D) : lattice₂ D Z.M p (Λ₁ ⊔ Λ₂) = lattice₂ D Z.M p Λ₁ ⊔ lattice₂ D Z.M p Λ₂ := by
  refine le_antisymm ?_ (sup_le (localLattice_mono Z p le_sup_left) (localLattice_mono Z p le_sup_right))
  rw [lattice₂, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, rfl⟩))
    (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))

theorem localLattice_map (f : (VS D).V →ₗ[D.host.E] (VS D).V) (fp : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p)
    (hf : ∀ x, baseChange₂ D p (f x) = fp (baseChange₂ D p x)) (Λ : LV D) :
    lattice₂ D Z.M p (Λ.map (f.restrictScalars (𝓞 D.host.E))) =
      (lattice₂ D Z.M p Λ).map (fp.restrictScalars (Z.M p).L.O) := by
  unfold lattice₂
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact hf x

end GlobalTheory.FrameProj

namespace GlobalTheory.FrameProj
variable {D : D7}

theorem bU_mem (U : Submodule D.host.E (VS D).V) (i) : bU U i ∈ U := (Module.finBasis D.host.E U i).2

theorem exists_sum_bU (U : Submodule D.host.E (VS D).V) {u : (VS D).V} (hu : u ∈ U) :
    ∃ c : Fin (Module.finrank D.host.E U) → D.host.E, u = ∑ i, c i • bU U i := by
  refine ⟨(Module.finBasis D.host.E U).repr ⟨u, hu⟩, ?_⟩
  have h := congrArg Subtype.val ((Module.finBasis D.host.E U).sum_repr ⟨u, hu⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h.symm

theorem mem_orth_iff (U : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    y ∈ orth (VS D) U ↔ ∀ u ∈ U, (VS D).hT u y = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem mem_orth_of_bU (U : Submodule D.host.E (VS D).V) (y : (VS D).V)
    (h : ∀ i, (VS D).hT (bU U i) y = 0) : y ∈ orth (VS D) U := by
  rw [mem_orth_iff]
  intro u hu
  obtain ⟨c, rfl⟩ := exists_sum_bU U hu
  simp [map_sum, LinearMap.sum_apply, h]

theorem gram_det_isUnit (U : Submodule D.host.E (VS D).V)
    (hU : ∀ y ∈ U, y ∈ orth (VS D) U → y = 0) : IsUnit (gram U).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hyU : (∑ j, v j • bU U j) ∈ U := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bU_mem U j)
  have hyo : (∑ j, v j • bU U j) ∈ orth (VS D) U := by
    apply mem_orth_of_bU
    intro i
    have h1 : (VS D).hT (bU U i) (∑ j, v j • bU U j) = ∑ j, gram U i j * v j := by
      simp only [map_sum, map_smul, smul_eq_mul, gram, Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h1]
    simpa [Matrix.mulVec, dotProduct] using congrFun hv i
  have hy0 := hU _ hyU hyo
  have hli := Fintype.linearIndependent_iff.mp (Module.finBasis D.host.E U).linearIndependent
  funext j
  refine hli v ?_ j
  apply Subtype.ext
  simpa [Submodule.coe_sum, Submodule.coe_smul, bU] using hy0

theorem proj_mem (U : Submodule D.host.E (VS D).V) (x : (VS D).V) : proj U x ∈ U := by
  rw [proj_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bU_mem U i)

theorem sub_proj_mem_orth (U : Submodule D.host.E (VS D).V) (hG : IsUnit (gram U).det) (x : (VS D).V) :
    x - proj U x ∈ orth (VS D) U := by
  apply mem_orth_of_bU
  intro k
  have key : ∀ w : Fin (Module.finrank D.host.E U) → D.host.E,
      Matrix.mulVec (gram U) w k = ∑ i, w i * (VS D).hT (bU U k) (bU U i) := by
    intro w
    simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [map_sub, proj_apply, map_sum, sub_eq_zero]
  simp only [map_smul, smul_eq_mul]
  rw [← key (Matrix.mulVec (gram U)⁻¹ fun j => (VS D).hT (bU U j) x), Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]

end GlobalTheory.FrameProj

namespace GlobalTheory.FrameProj
variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem Xplus_le_span {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    Xplus F ≤ Submodule.span D.host.E (Set.range (frame F)) := by
  have hf : ∀ a, frame F a ∈ Submodule.span D.host.E (Set.range (frame F)) :=
    fun a => Submodule.subset_span ⟨a, rfl⟩
  show F.fl.X ⊔ Submodule.span D.host.E {F.fl.z} ≤ _
  refine sup_le ?_ ?_
  · show Submodule.span D.host.E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    convert hf a.castSucc using 1
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    convert hf (Fin.last _) using 1
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]

def fixSub (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Submodule D.host.E (VS D).V where
  carrier := {u | g (baseChange₂ D p u) = baseChange₂ D p u}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, map_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [baseChange_smul₂, map_smul, ha]

def commSub (P : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) : Subgroup (Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) where
  carrier := {g | ∀ y, P (g y) = g (P y)}
  mul_mem' := by
    intro a b ha hb y
    simp only [Set.mem_setOf_eq] at *
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]
  one_mem' := by intro y; rfl
  inv_mem' := by
    intro a ha y
    simp only [Set.mem_setOf_eq] at *
    apply a.injective
    rw [← ha]
    simp

theorem localOrthogonalProj_comm_complementUnitary {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (FP : LocNG.FPair (locH Z p) D.R.rS)
    (hA : FP.A.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame F a))
    (hB : FP.B.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame F' a))
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hg : g ∈ FP.UW0) (y : Vp D p) :
    projP Z p (Xplus F ⊔ Xplus F') (g y) = g (projP Z p (Xplus F ⊔ Xplus F') y) := by
  have hunit : ∀ a, IsUnit (frFac Z.δ p a) := by
    intro a
    have hδ : Z.δ p ≠ 0 := (Z.agree p).2.1
    have hu : ((uP p : ℚ) : D.host.E) ≠ 0 := by
      rw [Rat.cast_ne_zero]
      unfold uP gpart
      refine div_ne_zero ?_ ?_
      · rw [Nat.cast_ne_zero]
        split_ifs
        · exact (D.host.g_prime 0).ne_zero
        · exact (D.host.g_prime 1).ne_zero
        · exact one_ne_zero
      · rw [Nat.cast_ne_zero]
        exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    have hx : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) :=
      ((isUnit_iff_ne_zero.mpr hδ).map _).mul ((isUnit_iff_ne_zero.mpr hu).map _)
    obtain ⟨w, hw⟩ := hx.pow (D.R.rS - a.val)
    unfold frFac
    rw [← hw, Ring.inverse_unit]
    exact Units.isUnit _
  revert y
  suffices h : FP.UW0 ≤ commSub p (projP Z p (Xplus F ⊔ Xplus F')) from fun y => h hg y
  rw [LocNG.FPair.UW0, Subgroup.closure_le]
  rintro g ⟨hu, hfix⟩ y
  have hfixU : Xplus F ⊔ Xplus F' ≤ fixSub p g := by
    refine sup_le ((Xplus_le_span F).trans (Submodule.span_le.mpr ?_))
      ((Xplus_le_span F').trans (Submodule.span_le.mpr ?_))
    · rintro _ ⟨a, rfl⟩
      show g (baseChange₂ D p (frame F a)) = baseChange₂ D p (frame F a)
      have h1 := (hfix a).1
      simp only [hA, map_smul] at h1
      exact (hunit a).smul_left_cancel.mp h1
    · rintro _ ⟨a, rfl⟩
      show g (baseChange₂ D p (frame F' a)) = baseChange₂ D p (frame F' a)
      have h1 := (hfix a).2
      simp only [hB, map_smul] at h1
      exact (hunit a).smul_left_cancel.mp h1
  have hb : ∀ i, g (baseChange₂ D p (bU (Xplus F ⊔ Xplus F') i)) = baseChange₂ D p (bU (Xplus F ⊔ Xplus F') i) :=
    fun i => hfixU (bU_mem _ i)
  rw [projP_apply, projP_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hb i]
  congr 2
  funext j
  have h2 := hu y (baseChange₂ D p (bU (Xplus F ⊔ Xplus F') j))
  rw [hb j] at h2
  exact h2

end GlobalTheory.FrameProj

namespace GlobalTheory.FrameProj
variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem img_map_le (Qp : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
    (hc : ∀ y, Qp (h y) = h (Qp y)) (L₀ : Submodule (Z.M p).L.O (Vp D p))
    (hL : L₀.map (Qp.restrictScalars (Z.M p).L.O) ≤ L₀) :
    (LocNG.img h L₀).map (Qp.restrictScalars (Z.M p).L.O) ≤ LocNG.img h L₀ := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  unfold LocNG.img at hw ⊢
  obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp hw
  refine Submodule.mem_map.mpr ⟨Qp l, hL (Submodule.mem_map_of_mem hl), ?_⟩
  simpa using (hc l).symm

end GlobalTheory.FrameProj
