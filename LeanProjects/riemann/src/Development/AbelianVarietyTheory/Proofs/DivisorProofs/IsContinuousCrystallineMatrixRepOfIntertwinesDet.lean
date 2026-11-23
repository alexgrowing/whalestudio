import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

theorem matGood_of_tw {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (f n : ℕ)
    (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r r' : ↥(GK K) →* GL (Fin n) ↥(OL LL))
    (U : ZMod f → Multiset ℤ) (a : Mx ↥(OL LL) n n) :
    MatGood P emb r U → Tw r' r a → a.det ≠ 0 → MatGood P emb r' U := by
  rintro ⟨hc, hcr, hj⟩ ht hdet
  set φ := algebraMap ↥(OL LL) ↥LL.1 with hφ
  have hinj : Function.Injective φ := fun x y h => Subtype.ext h
  set aL : Mx ↥LL.1 n n := a.map φ with haL
  have hdL : IsUnit aL.det := by
    have hd : aL.det = φ a.det := (RingHom.map_det φ a).symm
    rw [hd]
    exact isUnit_iff_ne_zero.mpr (fun h => hdet (hinj (by rw [h, map_zero])))
  have htL : ∀ g, aL * (r' g : Mx ↥(OL LL) n n).map φ = (r g : Mx ↥(OL LL) n n).map φ * aL := fun g => by
    rw [haL, ← Matrix.map_mul, ← Matrix.map_mul, ht g]
  have hconj : ∀ g, (r' g : Mx ↥(OL LL) n n).map φ = aL⁻¹ * ((r g : Mx ↥(OL LL) n n).map φ * aL) := fun g => by
    rw [← htL g, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdL, Matrix.one_mul]
  let e : (Fin n → ↥LL.1) ≃ₗ[↥LL.1] (Fin n → ↥LL.1) :=
    LinearEquiv.ofLinear (Matrix.toLin' aL) (Matrix.toLin' aL⁻¹)
      (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hdL, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hdL, Matrix.toLin'_one])
  have he : ∀ g v, e (repOf r' g v) = repOf r g (e v) := fun g v => by
    show aL.mulVec (repOf r' g v) = repOf r g (aL.mulVec v)
    rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htL g]
  refine ⟨fun i j => ?_, GlobalTheory.HTW.Rec.isCrys_of_equiv _ e he hcr, fun i τ hτ u => ?_⟩
  · have hform : (fun g => (((r' g : Mx ↥(OL LL) n n) i j : ↥(OL LL)) : ↥LL.1)) =
        fun g => ∑ k, aL⁻¹ i k * ∑ m, (((r g : Mx ↥(OL LL) n n) k m : ↥(OL LL)) : ↥LL.1) * aL m j := by
      funext g
      have := congrFun (congrFun (hconj g) i) j
      simp only [Matrix.map_apply, Matrix.mul_apply] at this
      exact this
    rw [hform]
    refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
    exact continuous_finset_sum _ fun m _ => (hc k m).mul continuous_const
  · rw [GlobalTheory.HTW.Rec.multV_eq_of_equiv _ e he]
    exact hj i τ hτ u

end GlobalTheory.WachPlace

end
