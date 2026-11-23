import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.Imports

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem line_deriv (hR : N.RightRule) {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : Formalism.REAL.inG ε A)
    (hexp : ∀ t, ReciprocityTheory.ChartRestriction.DS.inUJ ε (aT A t)) (i : D × List (Fin n)) (u : (path ⟨D, E, hK.gl⟩ χ ss).V)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : ReciprocityTheory.ChartRestriction.DS.inUJ ε g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => famP σ D E hK.gl χ ss i u (g * aT A s))
      (famP σ D E hK.gl χ ss i (actM (path ⟨D, E, hK.gl⟩ χ ss) A u) (g * aT A t)) t := by
  have hgt : ReciprocityTheory.ChartRestriction.DS.inUJ ε (g * aT A t) := by
    have h2 := hexp t
    unfold ReciprocityTheory.ChartRestriction.DS.inUJ at hg h2 ⊢
    rw [Matrix.conjTranspose_mul]
    calc (aT A t)ᴴ * gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * (g * aT A t)
        = (aT A t)ᴴ * (gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * g) * aT A t := by simp only [Matrix.mul_assoc]
      _ = ReciprocityTheory.ChartRestriction.DS.Jm ε := by rw [hg, h2]
  have h0 := hR n ε H σ D E hK χ ss hU i u A hA (g * aT A t) hgt
  have h1 := HasDerivAt.comp_sub_const (f := fun s : ℝ => (famP σ D E hK.gl χ ss i u)
    (g * aT A t * NormedSpace.exp ((s : ℂ) • A))) t t (by rw [sub_self]; exact h0)
  have hfun : (fun s : ℝ => (famP σ D E hK.gl χ ss i u) (g * aT A t * NormedSpace.exp (((s - t : ℝ) : ℂ) • A))) =
      fun s : ℝ => famP σ D E hK.gl χ ss i u (g * aT A s) := by
    funext s
    unfold aT
    rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute]
    · rw [← add_smul]
      push_cast
      ring
    · exact ((Commute.refl A).smul_left _).smul_right _
  have hval : (∑ a, ∑ b, A a b • (path ⟨D, E, hK.gl⟩ χ ss).E a b u) = actM (path ⟨D, E, hK.gl⟩ χ ss) A u := by
    simp [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hval] at h1
  simpa only [hfun] using h1

def wv {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) (k : ℕ) : X.V :=
  ((zs.drop k).map (fun z => actM X A - z • (1 : Module.End ℂ X.V))).prod u

theorem wv_succ {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) (k : ℕ)
    (hk : k < zs.length) :
    actM X A (wv X A zs u (k + 1)) = zs[k] • wv X A zs u (k + 1) + wv X A zs u k := by
  have h : wv X A zs u k = actM X A (wv X A zs u (k + 1)) - zs[k] • wv X A zs u (k + 1) := by
    simp only [wv]
    rw [List.drop_eq_getElem_cons hk, List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
  rw [h]
  abel

theorem wv_length {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) :
    wv X A zs u zs.length = u := by
  simp [wv]

theorem wv_zero {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ) (hp : p.Monic) (u : X.V) :
    wv X A p.roots.toList u 0 = Polynomial.aeval (actM X A) p u := by
  have hsplit := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
  have hl : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod =
      ((p.roots.toList).map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    conv_lhs => rw [← Multiset.coe_toList p.roots]
    rw [Multiset.map_coe, Multiset.prod_coe]
  have key : (p.roots.toList.map (fun z => actM X A - z • (1 : Module.End ℂ X.V))).prod =
      Polynomial.aeval (actM X A) p := by
    conv_rhs => rw [hsplit, hl, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    simp [Algebra.algebraMap_eq_smul_one]
  unfold wv
  rw [List.drop_zero, key]

end CompanionTheory.RgExh.Dec.L.SA
