import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKUConjOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppFinTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def atH (a b : ℕ) (w : Pl E) : Gf E a b →* GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w)).prodMap (GeneralLinearGroup.map (pLoc E w))

abbrev thW (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w := (thL a w).prodMap (thL b w)

abbrev dW (w : Pl E) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : GLw a w × GLw b w := (locEl a w δ₁, locEl b w δ₂)

abbrev dG (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : Gf E a b := (ratF E a δ₁, ratF E b δ₂)

abbrev KK (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Subgroup (Gf E a b) := (Kf E a).prod (Kf E b)

omit [IsCMField E] in
theorem atH_apply (w : Pl E) (y : Gf E a b) : atH a b w y = atW w y := rfl

theorem mem_KK_iff (g : Gf E a b) : g ∈ KK E a b ↔ ∀ u : Pl E, atH a b u g ∈ K2 a b u := by
  simp only [KK, Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact ⟨fun h u => ⟨h.1 u, h.2 u⟩, fun h => ⟨fun u => (h u).1, fun u => (h u).2⟩⟩

theorem ext_atH {g h : Gf E a b} (H : ∀ u : Pl E, atH a b u g = atH a b u h) : g = h :=
  Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun u => congrArg Prod.fst (H u))
    (GlobalTheory.EulerTwRestr.gl_ext fun u => congrArg Prod.snd (H u))

theorem ae_mem_GL {n : ℕ} (x : GL (Fin n) (Af E)) :
    ∀ᶠ w in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w n := by
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (x.1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (x.1 i j).2
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w ((x⁻¹).1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((x⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem ae_mem (g : Gf E a b) : ∀ᶠ u in cofinite, atH a b u g ∈ K2 a b u := by
  filter_upwards [ae_mem_GL g.1, ae_mem_GL g.2] with u h1 h2
  exact ⟨h1, h2⟩

theorem exists_GL_of_family {n : ℕ} (z : ∀ u : Pl E, GLw n u) (hz : ∀ᶠ u in cofinite, z u ∈ GlobalTheory.LFun.KGL u n) :
    ∃ g : GL (Fin n) (Af E), ∀ u, GeneralLinearGroup.map (pLoc E u) g = z u := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (z w).1 i j, hz.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((z w)⁻¹).1 i j, hz.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E),
      (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q := fun P Q h =>
    Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (z w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (z w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun u => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem exists_of_family (z : ∀ u : Pl E, GLw a u × GLw b u) (hz : ∀ᶠ u in cofinite, z u ∈ K2 a b u) :
    ∃ g : Gf E a b, ∀ u, atH a b u g = z u := by
  obtain ⟨g₁, h₁⟩ := exists_GL_of_family (fun u => (z u).1) (hz.mono fun u h => h.1)
  obtain ⟨g₂, h₂⟩ := exists_GL_of_family (fun u => (z u).2) (hz.mono fun u h => h.2)
  exact ⟨(g₁, g₂), fun u => Prod.ext (h₁ u) (h₂ u)⟩

theorem thP_thP (y : Gf E a b) : thP E a b (thP E a b y) = y :=
  Prod.ext (GlobalTheory.EulerTw.Comm.thF_thF y.1) (GlobalTheory.EulerTw.Comm.thF_thF y.2)

theorem atH_thP_congr {u v : Pl E} (huv : GlobalTheory.EulerTw.cPl E u = v) {g h : Gf E a b}
    (H : atH a b v g = atH a b v h) : atH a b u (thP E a b g) = atH a b u (thP E a b h) := by
  subst huv
  refine Prod.ext ?_ ?_
  · change GeneralLinearGroup.map (pLoc E u) (thF E a g.1) = GeneralLinearGroup.map (pLoc E u) (thF E a h.1)
    rw [GlobalTheory.EulerTw.IntRead.map_thF, GlobalTheory.EulerTw.IntRead.map_thF]
    exact congrArg _ (congrArg Prod.fst H)
  · change GeneralLinearGroup.map (pLoc E u) (thF E b g.2) = GeneralLinearGroup.map (pLoc E u) (thF E b h.2)
    rw [GlobalTheory.EulerTw.IntRead.map_thF, GlobalTheory.EulerTw.IntRead.map_thF]
    exact congrArg _ (congrArg Prod.snd H)

theorem integral_of_twist_conjugate_place (u : Pl E) {g : Gf E a b} (H : atH a b u (thP E a b g) ∈ K2 a b u) :
    atH a b (GlobalTheory.EulerTw.cPl E u) g ∈ K2 a b (GlobalTheory.EulerTw.cPl E u) := by
  refine ⟨GlobalTheory.EulerTw.IntRead.mem_KGL_of_thAt u _ ?_, GlobalTheory.EulerTw.IntRead.mem_KGL_of_thAt u _ ?_⟩
  · have := H.1
    change GeneralLinearGroup.map (pLoc E u) (thF E a g.1) ∈ _ at this
    rwa [GlobalTheory.EulerTw.IntRead.map_thF] at this
  · have := H.2
    change GeneralLinearGroup.map (pLoc E u) (thF E b g.2) ∈ _ at this
    rwa [GlobalTheory.EulerTw.IntRead.map_thF] at this

theorem map_thF_of_not_split {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (g : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) (thF E n g) = thL n w (GeneralLinearGroup.map (pLoc E w) g) := by
  rw [GlobalTheory.EulerTw.IntRead.map_thF]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h2 := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (cj w) (GeneralLinearGroup.map (pLoc E w) g) i j
  have e : thL n w = thetaGL n (cj w) := if_neg hw
  rw [e, h2, GlobalTheory.EulerTw.IntRead.thAt_apply, GlobalTheory.EulerTwRestr.loc_inv_val, GlobalTheory.EulerTwRestr.loc_inv_val]
  congr 1
  exact GlobLev.conjLoc_eq_cj hw _

theorem usage₇ {w : Pl E} (hw : ¬ IsSplitAt w) (g : Gf E a b) :
    atH a b w (thP E a b g) = thW a b w (atH a b w g) :=
  Prod.ext (map_thF_of_not_split hw g.1) (map_thF_of_not_split hw g.2)

theorem thW_of_split {w : Pl E} (hw : IsSplitAt w) (y : GLw a w × GLw b w) : thW a b w y = y := by
  simp [thL, hw]

theorem atH_dG_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    atH a b w (dG δ₁ δ₂) = dW w δ₁ δ₂ := by
  refine Prod.ext ?_ ?_
  · simp only [locEl, if_neg hw]; rfl
  · simp only [locEl, if_neg hw]; rfl

theorem atH_norm_of_split {w : Pl E} (hw : IsSplitAt w) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    atH a b w (dG δ₁ δ₂ * thP E a b (dG δ₁ δ₂)) = dW w δ₁ δ₂ := by
  refine Prod.ext ?_ ?_
  · simp only [locEl, if_pos hw]
    change GeneralLinearGroup.map (pLoc E w) (ratF E a δ₁ * thF E a (ratF E a δ₁)) = _
    rw [← GlobalTheory.EulerTw.Comm.thF_ratF, ← map_mul]; rfl
  · simp only [locEl, if_pos hw]
    change GeneralLinearGroup.map (pLoc E w) (ratF E b δ₂ * thF E b (ratF E b δ₂)) = _
    rw [← GlobalTheory.EulerTw.Comm.thF_ratF, ← map_mul]; rfl

theorem mem_or_conj {S : Set (Pl E)} (hS : IsSection S) (u : Pl E) : u ∈ S ∨ ∃ v ∈ S, u = GlobalTheory.EulerTw.cPl E v := by
  obtain ⟨v, ⟨hv, hvu⟩, -⟩ := hS u
  rcases GlobLev.eq_or_eq_conjSrc hvu.symm with h | h
  · exact Or.inl (h ▸ hv)
  · exact Or.inr ⟨v, hv, h⟩

theorem split_of_conj_ne {v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ v) : IsSplitAt v := by
  by_contra hv
  exact h (GlobLev.conjSrc_eq_of_not_split hv)

theorem cPl_cPl (v : Pl E) : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v) = v := GlobalTheory.ThetaPull.conjSrc_conjSrc _

theorem conj_not_mem {S : Set (Pl E)} (hS : IsSection S) {v : Pl E} (hv : v ∈ S) (h : IsSplitAt v) :
    GlobalTheory.EulerTw.cPl E v ∉ S := by
  intro hc
  obtain ⟨u, hne, hu⟩ := h
  have h1 : (GlobalTheory.EulerTw.cPl E v).under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) :=
    (GlobalTheory.EulerTwRestr.mem_orb_iff v _).1 (by simp [GlobalTheory.EulerTw.orb])
  have h2 : GlobalTheory.EulerTw.cPl E v = v := (hS v).unique ⟨hc, h1⟩ ⟨hv, rfl⟩
  rcases GlobLev.eq_or_eq_conjSrc hu with h3 | h3
  · exact hne h3
  · exact hne (h3.trans h2)

end GlobalTheory.CompanionTheory.SuppFinTw

end
