import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ConjMapSecondProj

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

def pdat (g : SplitG M.L) (k : E) (η : M.R) (la : E) (η' : M.R) (la' : E) : (E × E) × (E × E) :=
  ((g.e.symm (p1 g η, p1 g η'), g.e.symm (p2 g k * p2 g η - p2 g la, p1 g k * p2 g η' - p2 g la')),
    (g.e.symm (p1 g k * p1 g η - p1 g la, p2 g k * p1 g η' - p1 g la'), g.e.symm (p2 g η, p2 g η')))

theorem components_of_firstComponent_eq {Y : Ix r → M.L.O} {u : Fin (r + 1) → M.R} (h : cmp1 hs Y = u) (b : Fin (r + 1)) :
    p1 g (Y (Sum.inl b)) = p1 g (u b) ∧
      p1 g (Y (Sum.inl b)) + (g.q : F) * p1 g (Y (Sum.inr b)) = p2 g (u b) := by
  subst h
  have he := e_rOf hs (c1 g (Y (Sum.inl b))) (c1 g (Y (Sum.inr b)))
  have hc : (cmp1 hs Y b : M.R) = rOf hs (c1 g (Y (Sum.inl b))) (c1 g (Y (Sum.inr b))) := rfl
  constructor
  · show (g.e (Y (Sum.inl b) : E)).1 = (g.e ((cmp1 hs Y b : M.R) : E)).1
    rw [hc, he]
    rfl
  · show (g.e (Y (Sum.inl b) : E)).1 + (g.q : F) * (g.e (Y (Sum.inr b) : E)).1 = (g.e ((cmp1 hs Y b : M.R) : E)).2
    rw [hc, he]
    rfl

theorem components_of_secondComponent_eq {Y : Ix r → M.L.O} {u : Fin (r + 1) → M.R} (h : cmp2 hs Y = u) (b : Fin (r + 1)) :
    p2 g (Y (Sum.inl b)) = p1 g (u b) ∧
      p2 g (Y (Sum.inl b)) + (g.q : F) * p2 g (Y (Sum.inr b)) = p2 g (u b) := by
  subst h
  have he := e_rOf hs (c2 g (Y (Sum.inl b))) (c2 g (Y (Sum.inr b)))
  have hc : (cmp2 hs Y b : M.R) = rOf hs (c2 g (Y (Sum.inl b))) (c2 g (Y (Sum.inr b))) := rfl
  constructor
  · show (g.e (Y (Sum.inl b) : E)).2 = (g.e ((cmp2 hs Y b : M.R) : E)).1
    rw [hc, he]
    rfl
  · show (g.e (Y (Sum.inl b) : E)).2 + (g.q : F) * (g.e (Y (Sum.inr b) : E)).2 = (g.e ((cmp2 hs Y b : M.R) : E)).2
    rw [hc, he]
    rfl

theorem firstProj_unit_vector_eq (η : M.R) (l : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    p1 g ((((η • (eV r : Fin (r + 1) → M.R) + q2 hs • l) : Fin (r + 1) → M.R) b : M.R) : E) = p1 g η * dl r b := by
  show (g.e _).1 = _
  rw [e_ueq hs η l b]

theorem secondProj_unit_vector_eq (η : M.R) (l : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    p2 g ((((η • (eV r : Fin (r + 1) → M.R) + q2 hs • l) : Fin (r + 1) → M.R) b : M.R) : E) =
      p2 g η * dl r b + (g.q : F) * p2 g (l b) := by
  show (g.e _).2 = _
  rw [e_ueq hs η l b]

theorem dl_last (r : ℕ) : dl (F := F) r (Fin.last r) = 1 := by
  simp [dl]

theorem firstProj_algebraMap_split (a : F) : p1 g (algebraMap F E a) = a := by
  show (g.e (algebraMap F E a)).1 = a
  rw [AlgEquiv.commutes]
  rfl
theorem secondProj_algebraMap_split (a : F) : p2 g (algebraMap F E a) = a := by
  show (g.e (algebraMap F E a)).2 = a
  rw [AlgEquiv.commutes]
  rfl

variable {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F)
  {Y Y' Y'' : Ix r → M.L.O} {η η' : M.R} {l l' : Fin (r + 1) → M.R}
  (h1 : cmp1 hs Y = η • (eV r : Fin (r + 1) → M.R) + q2 hs • l)
  (h2 : cmp2 hs Y = η' • (eV r : Fin (r + 1) → M.R) + q2 hs • l')
  (h3 : cmp1 hs Y'' = l) (h4 : cmp2 hs Y'' = l')
  (hY : ∀ i, (Y i : E) - Y' i = algebraMap F E (g.q : F) * Y'' i)

include hZh h1 h2 h3 h4 hY in
theorem vals :
    (((Y (Sum.inl (Fin.last r)) : E),
        lamStarC (M.L.cj : E →+* E) Zh (fun b => (Y (Sum.inl b) : E) + algebraMap F E (g.q : F) * Y (Sum.inr b))),
      (lamC Zh (fun a => (Y' (Sum.inl a) : E)),
        (Y' (Sum.inl (Fin.last r)) : E) + algebraMap F E (g.q : F) * Y' (Sum.inr (Fin.last r)))) =
      pdat g (Zh⁻¹ (Fin.last r) (Fin.last r)) η (laG (ZZm g Zh T T') l) η'
        (laG (ZZm g (Zh.map M.L.cj) T T') l') := by
  have hZc : IsUnit (Zh.map M.L.cj).det := by
    have := hZh.map (M.L.cj : E →+* E)
    rwa [RingHom.map_det] at this
  have fY := components_of_firstComponent_eq hs h1
  have gY := components_of_secondComponent_eq hs h2
  have fZ := components_of_firstComponent_eq hs h3
  have gZ := components_of_secondComponent_eq hs h4
  have hW1 : ∀ i, p1 g (Y' i) = p1 g (Y i) - (g.q : F) * p1 g (Y'' i) := fun i => by
    have := congrArg (p1 g) (hY i); rw [map_sub, map_mul, firstProj_algebraMap_split] at this; linear_combination -this
  have hW2 : ∀ i, p2 g (Y' i) = p2 g (Y i) - (g.q : F) * p2 g (Y'' i) := fun i => by
    have := congrArg (p2 g) (hY i); rw [map_sub, map_mul, secondProj_algebraMap_split] at this; linear_combination -this
  simp only [firstProj_unit_vector_eq hs, secondProj_unit_vector_eq hs] at fY gY
  simp only [pdat]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp only <;> apply g.e.injective <;>
    rw [AlgEquiv.apply_symm_apply] <;> refine Prod.ext ?_ ?_ <;> simp only [← adeleInfiniteComponent_apply, ← adele_ext_components]
  · rw [(fY _).1, dl, if_pos rfl, mul_one]
  · rw [(gY _).1, dl, if_pos rfl, mul_one]
  · rw [lambdaStar_firstProj hs hZh, lastCoordinate_secondProj hs hZh, corner_inverse_secondProj hs hZh]
    have e : ∀ b, (Zh.map (p2 g))⁻¹ b (Fin.last r) *
        p1 g ((Y (Sum.inl b) : E) + algebraMap F E (g.q : F) * Y (Sum.inr b)) =
        (Zh.map (p2 g))⁻¹ b (Fin.last r) * p2 g η * dl r b +
          -(-(g.q : F) * (Zh.map (p2 g))⁻¹ b (Fin.last r) * p2 g (l b)) := fun b => by
      rw [map_add, map_mul, firstProj_algebraMap_split, (fY b).2]; ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_dl]
    ring
  · rw [lambdaStar_secondProj hs hZh, lastCoordinate_secondProj hs hZc, corner_inverse_firstProj hs hZh, conj_map_secondProj]
    have e : ∀ b, (Zh.map (p1 g))⁻¹ b (Fin.last r) *
        p2 g ((Y (Sum.inl b) : E) + algebraMap F E (g.q : F) * Y (Sum.inr b)) =
        (Zh.map (p1 g))⁻¹ b (Fin.last r) * p2 g η' * dl r b +
          -(-(g.q : F) * (Zh.map (p1 g))⁻¹ b (Fin.last r) * p2 g (l' b)) := fun b => by
      rw [map_add, map_mul, secondProj_algebraMap_split, (gY b).2]; ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_dl]
    ring
  · rw [lambda_firstProj hs hZh, lastCoordinate_firstProj hs hZh, corner_inverse_firstProj hs hZh]
    have e : ∀ b, (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (Y' (Sum.inl b) : E) =
        (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g η * dl r b +
          -((g.q : F) * (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (l b)) := fun b => by
      rw [hW1, (fY b).1, (fZ b).1]; ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_dl]
    ring
  · rw [lambda_secondProj hs hZh, lastCoordinate_firstProj hs hZc, corner_inverse_secondProj hs hZh, conj_map_firstProj]
    have e : ∀ b, (Zh.map (p2 g))⁻¹ (Fin.last r) b * p2 g (Y' (Sum.inl b) : E) =
        (Zh.map (p2 g))⁻¹ (Fin.last r) b * p1 g η' * dl r b +
          -((g.q : F) * (Zh.map (p2 g))⁻¹ (Fin.last r) b * p1 g (l' b)) := fun b => by
      rw [hW2, (gY b).1, (gZ b).1]; ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_dl]
    ring
  · rw [map_add, map_mul, firstProj_algebraMap_split, hW1, hW1]
    linear_combination (fY (Fin.last r)).2 - (g.q : F) * (fZ (Fin.last r)).2 +
      p2 g η * (dl_last (F := F) r)
  · rw [map_add, map_mul, secondProj_algebraMap_split, hW2, hW2]
    linear_combination (gY (Fin.last r)).2 - (g.q : F) * (gZ (Fin.last r)).2 +
      p2 g η' * (dl_last (F := F) r)

end Formalism.L2.SG.LocalCountModules.AlgGSplit
