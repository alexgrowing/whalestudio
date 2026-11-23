import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.EmbeddingSecondComponent

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def ind (r : ℕ) (a b : Fin (r + 1)) : F := if a = Fin.last r ∧ b = Fin.last r then 1 else 0

theorem e_cor (x : E) (a b : Fin (r + 1)) :
    g.e (cor r a b x) = (ind r a b * (g.e x).1, ind r a b * (g.e x).2) := by
  unfold cor ind; split_ifs <;> simp <;> rfl

theorem e_cjR (x : E) : g.e ((M.L.cj : E →+* E) x) = ((g.e x).2, (g.e x).1) := g.e_cj x

theorem e_cjA (x : E) : g.e (M.L.cj x) = ((g.e x).2, (g.e x).1) := g.e_cj x

theorem e_gram (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (i j : Ix r) :
    g.e (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T') i j) =
      match i, j with
      | Sum.inl a, Sum.inl b => (ind r a b * (-T), ind r a b * (-T))
      | Sum.inl a, Sum.inr b => ((g.q : F)⁻¹ * ((g.e (Zh a b)).2 + ind r a b * T),
          (g.q : F)⁻¹ * ((g.e (Zh a b)).1 + ind r a b * T))
      | Sum.inr a, Sum.inl b => ((g.q : F)⁻¹ * ((g.e (Zh b a)).1 + ind r a b * T),
          (g.q : F)⁻¹ * ((g.e (Zh b a)).2 + ind r a b * T))
      | Sum.inr a, Sum.inr b => ((g.q : F)⁻¹ * (g.q : F)⁻¹ *
            (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2 - ind r a b * (T + T')),
          (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1 - ind r a b * (T + T'))) := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [gramG, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, map_mul, map_add, map_sub, map_neg, e_cor,
      Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg, e_cjR, e_cjA] <;>
    refine Prod.ext ?_ ?_ <;> simp [e_cjR, e_cjA] <;> ring

theorem sum_ind_l (x : Fin (r + 1) → F) (b : Fin (r + 1)) :
    ∑ a, x a * ind r a b = if b = Fin.last r then x (Fin.last r) else 0 := by
  unfold ind
  by_cases hb : b = Fin.last r
  · subst hb; simp
  · simp [hb]

variable (hs : M.split = some g)

def mOf1 (c : Ix r → M.L.O) : Fin (r + 1) → M.R :=
  fun a => rOf hs (c1 g (c (Sum.inr a))) (-(c1 g (c (Sum.inl a))))

def mOf2 (c : Ix r → M.L.O) : Fin (r + 1) → M.R :=
  fun a => rOf hs (c2 g (c (Sum.inr a))) (-(c2 g (c (Sum.inl a))))

theorem e_llMap (Z : M.Mat (r + 1)) (TT : M.R) (m : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    g.e ((llMap hs Z TT m b : M.R) : E) =
      (∑ a, (g.e (Z.Z b a : E)).1 * (g.e (m a : E)).1 -
          (if b = Fin.last r then (g.e (TT : E)).1 *
            (((g.e (m (Fin.last r) : E)).1 - (g.e (m (Fin.last r) : E)).2) / (g.q : F)) else 0),
        ∑ a, (g.e (Z.Z b a : E)).2 * (g.e (m a : E)).2 -
          (if b = Fin.last r then (g.e (TT : E)).2 *
            (((g.e (m (Fin.last r) : E)).1 - (g.e (m (Fin.last r) : E)).2) / (g.q : F)) else 0)) := by
  by_cases hb : b = Fin.last r
  · subst hb
    refine Prod.ext ?_ ?_ <;>
      simp [llMap, Matrix.mulVec, dotProduct, map_sum, Prod.fst_sum, Prod.snd_sum, e_dgR, trO_coe]
  · refine Prod.ext ?_ ?_ <;>
      simp [hb, llMap, Matrix.mulVec, dotProduct, map_sum, Prod.fst_sum, Prod.snd_sum, e_dgR, trO_coe]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
