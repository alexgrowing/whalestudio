import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Generic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ a, Fintype (ι a)] {k : Type} [Field k]

omit [Fintype K] [DecidableEq K] [∀ a, Fintype (ι a)] in

theorem X_mem_mIdealOver_iff {Ω : Type} [Field Ω] [Algebra k Ω] (y : (Σ a, ι a) → Ω) (p : Σ a, ι a) :
    (X p : NumbersDVR.MRing ι k) ∈ mIdealOver k y ↔ y p = 0 := by
  change mConeMapOver k y (X p) = 0 ↔ _
  simp [mConeMapOver, X_ne_zero]

def genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] :
    (Σ a, ι a) → FractionRing (NumbersDVR.MRing ι k ⧸ W) :=
  fun p => algebraMap _ _ (Ideal.Quotient.mk W (X p))

omit [Fintype K] [DecidableEq K] [∀ a, Fintype (ι a)] in

theorem aeval_genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] (g : NumbersDVR.MRing ι k) :
    aeval (genPtOf W) g = algebraMap _ (FractionRing (NumbersDVR.MRing ι k ⧸ W)) (Ideal.Quotient.mk W g) := by
  have h : (aeval (genPtOf W) : NumbersDVR.MRing ι k →ₐ[k] FractionRing (NumbersDVR.MRing ι k ⧸ W)) =
      (IsScalarTower.toAlgHom k (NumbersDVR.MRing ι k ⧸ W) (FractionRing (NumbersDVR.MRing ι k ⧸ W))).comp
        (Ideal.Quotient.mkₐ k W) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPtOf]
  exact congrArg (fun φ : NumbersDVR.MRing ι k →ₐ[k] FractionRing (NumbersDVR.MRing ι k ⧸ W) => φ g) h

theorem mIdealOver_genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] (hh : NumbersDVR.IsMultiHomogIdeal W) :
    mIdealOver k (genPtOf W) = W := by
  have hz : ∀ g, aeval (genPtOf W) g = 0 ↔ g ∈ W := fun g => by
    rw [aeval_genPtOf, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective (NumbersDVR.MRing ι k ⧸ W) (FractionRing (NumbersDVR.MRing ι k ⧸ W))).eq_iff'
      (map_zero _)
  ext f
  change mConeMapOver k (genPtOf W) f = 0 ↔ f ∈ W
  constructor
  · intro h
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => (hz _).mp ?_
    rw [← coeff_mConeMapOver, h, coeff_zero]
  · intro hf
    ext e
    rw [coeff_zero, ← Finsupp.equivFunOnFinite_symm_coe e, coeff_mConeMapOver]
    exact (hz _).mpr (hh f hf _)

end Generic

theorem DegEq.proof (hGR : GraphRestrict.Statement) (hIR : Kleiman.InterNumRestrict.Statement.{0, 0})
    (hNM : NumModel.Statement) : DegEq.Statement := by
  intro k _ N Ω _ _ x Q n m s _ hgen pp W hsub hW hle hcomap
  classical
  have := hW.isPrime
  have hWy : mIdealOver k (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  let x' : Fin (N + 1) → FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) := fun a => genPtOf W ⟨Sum.inl (), a⟩
  let s' : Fin m → FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) := fun b => genPtOf W ⟨Sum.inr (), b⟩
  have hy : graphVec x' s' = genPtOf W := by
    funext p
    rcases p with ⟨⟨⟩ | ⟨⟩, a⟩ <;> rfl
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing (graphIdx N m) k) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := k), hWy]
  have hxy : ∀ i, x' i ≠ 0 → x i ≠ 0 := fun i h h0 =>
    h ((hzero _).mpr (hle ((X_mem_mIdealOver_iff (graphVec x s) ⟨Sum.inl (), i⟩).mpr h0)))
  have hx' : ∃ i, x' i ≠ 0 := by
    obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hs' : ∃ j, s' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
    exact ⟨j, fun h => hj ((hzero _).mp h)⟩
  have hyW : mIdealOver k (graphVec x' s') = W := by rw [hy]; exact hWy
  have hleW : mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') := hyW.symm ▸ hle
  have hpp : Kleiman.primeOf (S := k) x' = pp := by
    rw [← comap_mIdealOver_graph (S := k) x' s', hyW, hcomap]
  obtain ⟨Q', r, hR, hgen'⟩ := hGR k N Ω x Q n m s _ x' s' hxy hgen hleW hx' hs'
  have hsub' : Kleiman.IsSubvar x' pp 1 := ⟨hsub.isPrime, hsub.homog, le_of_eq hpp, hsub.relevant, hsub.dim⟩
  have h1 := hIR k Ω N x _ x' hxy (hsub.le.trans hpp.ge) pp 1 hsub' ![Q] ![Q'] (fun _ => r)
    (fun i => by fin_cases i; exact hR)
  have h2 := hNM k (Unit ⊕ Unit) (graphIdx N m) _ (graphVec x' s') baseBlock N (Equiv.refl _) x' rfl
    (GraphModel.full k N _ x' Q' n m s' hx' hgen') 1 ![Q'] ![graphDeg n]
    (fun i => by fin_cases i; exact realises_graph Q' n s' hgen') (by rw [hpp]; exact hsub')
  rw [hyW, hpp] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
