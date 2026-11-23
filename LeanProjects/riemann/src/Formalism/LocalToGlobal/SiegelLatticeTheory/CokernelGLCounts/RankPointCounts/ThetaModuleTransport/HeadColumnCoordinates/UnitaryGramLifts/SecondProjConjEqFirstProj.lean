import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section DuU

theorem firstProj_conj_eq_secondProj (x : E) : ph1 g ((M.L.cj : E →+* E) x) = ph2 g x := by
  simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem secondProj_conj_eq_firstProj (x : E) : ph2 g ((M.L.cj : E →+* E) x) = ph1 g x := by
  simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem firstProj_algebraMap (a : F) : ph1 g (algebraMap F E a) = a := by
  simp [firstProj_apply]

theorem ph2_algebraMap_eq (a : F) : ph2 g (algebraMap F E a) = a := by
  simp [secondProj_apply]

theorem firstProj_corner (a b : Fin (r + 1)) (X : E) : ph1 g (cor r a b X) = cor r a b (ph1 g X) := by
  unfold cor; split_ifs <;> simp

theorem firstProj_iotaOne_inl (hs : M.split = some g) (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    ph1 g ((iota1 hs l (Sum.inl a) : M.L.O) : E) = ph1 g (l a : E) := by
  simp [iota1, firstProj_apply]

theorem firstProj_iotaOne_inr (hs : M.split = some g) (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    ph1 g ((iota1 hs l (Sum.inr a) : M.L.O) : E) = (ph2 g (l a : E) - ph1 g (l a : E)) / (g.q : F) := by
  simp [iota1, firstProj_apply, secondProj_apply]

theorem firstProj_conj_iotaTwo (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g ((M.L.cj : E →+* E) ((iota2 hs l i : M.L.O) : E)) = ph1 g ((iota1 hs l i : M.L.O) : E) := by
  simp [iota2, firstProj_apply, g.e_cj, M.L.cj_cj]

theorem duU_formG_sub (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y W W' : Ix r → O) :
    formG O cj qi Z T T' Y W - formG O cj qi Z T T' Y W' =
      ∑ i, (Y i : E) * (Matrix.mulVec (gramG cj qi Z T T')⁻¹ fun j => cj (W j) - cj (W' j)) i := by
  unfold formG
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub, mul_assoc]

theorem firstProj_sum_iotaOne (hs : M.split = some g) (l : Fin (r + 1) → M.R) (c : Ix r → E) :
    ph1 g (∑ i, ((iota1 hs l i : M.L.O) : E) * c i) =
      ∑ a, ph1 g (l a : E) * ph1 g (c (Sum.inl a)) +
        ∑ a, (ph2 g (l a : E) - ph1 g (l a : E)) / (g.q : F) * ph1 g (c (Sum.inr a)) := by
  rw [map_sum, Fintype.sum_sum_type]
  simp only [map_mul, firstProj_iotaOne_inl, firstProj_iotaOne_inr]

theorem duU_sum_single1 (a : Fin (r + 1)) (x : M.R) (f : Fin (r + 1) → F) :
    ∑ b, ph1 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E) * f b = ph1 g (x : E) * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem duU_sum_single2 (a : Fin (r + 1)) (x : M.R) (f : Fin (r + 1) → F) :
    ∑ b, (ph2 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E) - ph1 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E)) / (g.q : F) * f b =
      (ph2 g (x : E) - ph1 g (x : E)) / (g.q : F) * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem ph1_mem_integers_of_mem_O {y : E} (hy : y ∈ M.L.O) : ph1 g y ∈ 𝒪[F] := by
  have hidem : (g.e.symm (1, 0) : E) * g.e.symm (1, 0) = g.e.symm (1, 0) := by
    rw [← map_mul]
    simp
  have hu : y * g.e.symm (1, 0) ∈ M.L.O := M.L.O.mul_mem hy (idem_mem_O M.L hidem)
  have hw : y * g.e.symm (1, 0) + M.L.cj (y * g.e.symm (1, 0)) ∈ M.L.O :=
    M.L.O.add_mem hu (cj_mem_O M.L hu)
  have heq : y * g.e.symm (1, 0) + M.L.cj (y * g.e.symm (1, 0)) = algebraMap F E (ph1 g y) := by
    apply g.e.injective
    refine Prod.ext ?_ ?_ <;> simp [g.e_cj, firstProj_apply]
  haveI : Nontrivial E := g.e.toEquiv.nontrivial
  exact Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (heq ▸ hw)

theorem duU_c_int (hs : M.split = some g) (c : Ix r → E)
    (h : ∀ l : Fin (r + 1) → M.R, ∑ i, ((iota1 hs l i : M.L.O) : E) * c i ∈ M.L.O) :
    ∀ i, ph1 g (c i) ∈ 𝒪[F] := by
  have hq : (g.q : F) ≠ 0 := by
    intro h0
    exact g.q_irr.ne_zero (Subtype.ext h0)
  intro i
  rcases i with a | a
  · have h1 := ph1_mem_integers_of_mem_O (g := g) (h (Pi.single a 1))
    rw [firstProj_sum_iotaOne hs] at h1
    simp only [duU_sum_single1, duU_sum_single2] at h1
    simpa using h1
  · have h1 := ph1_mem_integers_of_mem_O (g := g) (h (Pi.single a (q2 hs)))
    rw [firstProj_sum_iotaOne hs] at h1
    simp only [duU_sum_single1, duU_sum_single2] at h1
    simpa [firstProj_apply, secondProj_apply, embedding_uniformizer hs, hq] using h1

theorem duU_sum_cor (a : Fin (r + 1)) (X : F) (f : Fin (r + 1) → F) :
    ∑ b, cor r a b X * f b = if a = Fin.last r then X * f (Fin.last r) else 0 := by
  unfold cor
  split_ifs with ha
  · simp [ha, ite_mul]
  · simp [ha]

theorem firstProj_zzPlus_conj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      ph2 g (Zh a b) / (g.q : F) - cor r a b (-T / (g.q : F)) := by
  unfold cor
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem secondProj_zzPlus_conj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      -(ph1 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := by
  unfold cor
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [firstProj_apply, secondProj_apply, g.e_cj]

end DuU

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
