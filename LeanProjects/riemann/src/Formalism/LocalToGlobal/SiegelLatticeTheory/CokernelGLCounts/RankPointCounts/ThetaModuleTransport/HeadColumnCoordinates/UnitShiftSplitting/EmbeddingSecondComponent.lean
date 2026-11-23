import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L}

theorem fst_mem (g : SplitG M.L) (x : M.L.O) : (g.e (x : E)).1 ∈ 𝒪[F] := (Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.comp_mem_O g x.2).1

theorem snd_mem (g : SplitG M.L) (x : M.L.O) : (g.e (x : E)).2 ∈ 𝒪[F] := (Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.comp_mem_O g x.2).2

def c1 (g : SplitG M.L) (x : M.L.O) : 𝒪[F] := ⟨_, fst_mem g x⟩

def c2 (g : SplitG M.L) (x : M.L.O) : 𝒪[F] := ⟨_, snd_mem g x⟩

def rOf (hs : M.split = some g) (a b : 𝒪[F]) : M.R :=
  ⟨g.e.symm ((a : F), (a : F) + (g.q : F) * b),
    mem_R_of hs _ a (a + g.q * b) (-b) (by simp) (by push_cast; ring)⟩

theorem e_rOf (hs : M.split = some g) (a b : 𝒪[F]) :
    g.e ((rOf hs a b : M.R) : E) = ((a : F), (a : F) + (g.q : F) * b) := by
  simp [rOf]

variable (hs : M.split = some g) {r : ℕ}

def cmp1 : (Ix r → M.L.O) →+ (Fin (r + 1) → M.R) where
  toFun Y a := rOf hs (c1 g (Y (Sum.inl a))) (c1 g (Y (Sum.inr a)))
  map_zero' := by
    funext a; apply Subtype.ext; apply g.e.injective
    rw [e_rOf]; simp [c1]
  map_add' Y W := by
    funext a; apply Subtype.ext; apply g.e.injective
    simp only [Pi.add_apply, Subring.coe_add, map_add, e_rOf, c1, Prod.fst_add]
    refine Prod.ext ?_ ?_ <;> simp; ring

def cmp2 : (Ix r → M.L.O) →+ (Fin (r + 1) → M.R) where
  toFun Y a := rOf hs (c2 g (Y (Sum.inl a))) (c2 g (Y (Sum.inr a)))
  map_zero' := by
    funext a; apply Subtype.ext; apply g.e.injective
    rw [e_rOf]; simp [c2]
  map_add' Y W := by
    funext a; apply Subtype.ext; apply g.e.injective
    simp only [Pi.add_apply, Subring.coe_add, map_add, e_rOf, c2, Prod.snd_add]
    refine Prod.ext ?_ ?_ <;> simp; ring

theorem embedding_firstComponent (Y : Ix r → M.L.O) (a : Fin (r + 1)) :
    g.e ((cmp1 hs Y a : M.R) : E) = ((g.e (Y (Sum.inl a) : E)).1,
      (g.e (Y (Sum.inl a) : E)).1 + (g.q : F) * (g.e (Y (Sum.inr a) : E)).1) := by
  show g.e ((rOf hs _ _ : M.R) : E) = _
  rw [e_rOf]
  rfl

theorem embedding_secondComponent (Y : Ix r → M.L.O) (a : Fin (r + 1)) :
    g.e ((cmp2 hs Y a : M.R) : E) = ((g.e (Y (Sum.inl a) : E)).2,
      (g.e (Y (Sum.inl a) : E)).2 + (g.q : F) * (g.e (Y (Sum.inr a) : E)).2) := by
  show g.e ((rOf hs _ _ : M.R) : E) = _
  rw [e_rOf]
  rfl

theorem e_iota1_inl (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    g.e ((iota1 hs l (Sum.inl a) : M.L.O) : E) = ((g.e (l a : E)).1, 0) := by
  simp [iota1]

theorem e_iota1_inr (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    g.e ((iota1 hs l (Sum.inr a) : M.L.O) : E) = (((g.e (l a : E)).2 - (g.e (l a : E)).1) / (g.q : F), 0) := by
  simp [iota1]

theorem e_iota2 (l : Fin (r + 1) → M.R) (i : Ix r) :
    g.e ((iota2 hs l i : M.L.O) : E) = (0, (g.e (iota1 hs l i : E)).1) := by
  show g.e (M.L.cj (iota1 hs l i : E)) = _
  rw [g.e_cj]
  rcases i with a | a
  · rw [e_iota1_inl]
    rfl
  · rw [e_iota1_inr]
    rfl

theorem firstComponent_iotaOne (l : Fin (r + 1) → M.R) : cmp1 hs (iota1 hs l) = l := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext (by simpa using h))
  funext a
  apply Subtype.ext
  apply g.e.injective
  rw [embedding_firstComponent, e_iota1_inl, e_iota1_inr]
  ext
  · rfl
  · simp only
    field_simp
    ring

theorem secondComponent_iotaOne (l : Fin (r + 1) → M.R) : cmp2 hs (iota1 hs l) = 0 := by
  funext a
  apply Subtype.ext
  apply g.e.injective
  rw [embedding_secondComponent, e_iota1_inl, e_iota1_inr]
  simp

theorem firstComponent_iotaTwo (l : Fin (r + 1) → M.R) : cmp1 hs (iota2 hs l) = 0 := by
  funext a
  apply Subtype.ext
  apply g.e.injective
  rw [embedding_firstComponent, e_iota2, e_iota2]
  simp

theorem secondComponent_iotaTwo (l : Fin (r + 1) → M.R) : cmp2 hs (iota2 hs l) = l := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext (by simpa using h))
  funext a
  apply Subtype.ext
  apply g.e.injective
  rw [embedding_secondComponent, e_iota2, e_iota2, e_iota1_inl, e_iota1_inr]
  ext
  · rfl
  · simp only
    field_simp
    ring

theorem iota_cmp (Y : Ix r → M.L.O) : iota1 hs (cmp1 hs Y) + iota2 hs (cmp2 hs Y) = Y := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext (by simpa using h))
  funext i
  apply Subtype.ext
  apply g.e.injective
  rw [Pi.add_apply, Subring.coe_add, map_add, e_iota2]
  rcases i with a | a
  · rw [e_iota1_inl, e_iota1_inl, embedding_firstComponent, embedding_secondComponent]
    ext <;> simp
  · rw [e_iota1_inr, e_iota1_inr, embedding_firstComponent, embedding_secondComponent]
    ext <;> simp <;> field_simp

theorem iotaOne_add (l w : Fin (r + 1) → M.R) : iota1 hs (l + w) = iota1 hs l + iota1 hs w := by
  funext i
  apply Subtype.ext
  apply g.e.injective
  rw [Pi.add_apply, Subring.coe_add, map_add]
  rcases i with a | a
  · rw [e_iota1_inl, e_iota1_inl, e_iota1_inl, Pi.add_apply, Subring.coe_add, map_add]
    ext <;> simp
  · rw [e_iota1_inr, e_iota1_inr, e_iota1_inr, Pi.add_apply, Subring.coe_add, map_add]
    ext <;> simp <;> ring

theorem iotaTwo_add (l w : Fin (r + 1) → M.R) : iota2 hs (l + w) = iota2 hs l + iota2 hs w := by
  funext i
  apply Subtype.ext
  apply g.e.injective
  rw [Pi.add_apply, Subring.coe_add, map_add, e_iota2, e_iota2, e_iota2, iotaOne_add, Pi.add_apply,
    Subring.coe_add, map_add]
  ext <;> simp

def splitE : (Ix r → M.L.O) ≃+ (Fin (r + 1) → M.R) × (Fin (r + 1) → M.R) where
  toFun Y := (cmp1 hs Y, cmp2 hs Y)
  invFun p := iota1 hs p.1 + iota2 hs p.2
  left_inv Y := iota_cmp hs Y
  right_inv p := by
    simp only [map_add, firstComponent_iotaOne, secondComponent_iotaOne, firstComponent_iotaTwo, secondComponent_iotaTwo, add_zero, zero_add]
  map_add' Y W := by simp only [map_add, Prod.mk_add_mk]

theorem firstComponent_smul (c : M.L.O) (Y : Ix r → M.L.O) : cmp1 hs (c • Y) = dgR hs (c1 g c) • cmp1 hs Y := by
  funext a
  apply Subtype.ext
  apply g.e.injective
  rw [embedding_firstComponent]
  simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, map_mul]
  rw [embedding_firstComponent]
  simp [dgR, c1, AlgEquiv.commutes]
  ring

theorem secondComponent_smul (c : M.L.O) (Y : Ix r → M.L.O) : cmp2 hs (c • Y) = dgR hs (c2 g c) • cmp2 hs Y := by
  funext a
  apply Subtype.ext
  apply g.e.injective
  rw [embedding_secondComponent]
  simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, map_mul]
  rw [embedding_secondComponent]
  simp [dgR, c2, AlgEquiv.commutes]
  ring

end Formalism.L2.SG.LocalCountModules.AlgGSplit
