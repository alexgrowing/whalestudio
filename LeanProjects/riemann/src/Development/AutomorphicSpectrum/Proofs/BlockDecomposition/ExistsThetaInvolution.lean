import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EopWMemStabAlg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc GlobalTheory.CompanionTheory.TwY GlobalTheory.CompanionTheory.TrPassage
open PositivityTheory.RgBcC (KMod lefE lefT phiOf infOf IsMult Inf GLs IsEig MultAlg)
open PositivityTheory.RgBcC.Real (IsLefK)
open PositivityTheory.RgBcC.RealD (invA flipA trOn hwSp harmSet kF gelA barF IsPair IsDerivK)
open PositivityTheory.RgTw (G Mat)
open scoped ContDiff InnerProductSpace
attribute [local instance] borelH Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TwY.ThInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def adjH : Lie E n →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᴴ
      map_add' := fun X Y => by
        rw [show Matrix.of (X + Y) = Matrix.of X + Matrix.of Y from rfl, Matrix.conjTranspose_add]; rfl
      map_smul' := fun t X => by
        rw [show Matrix.of (t • X) = t • Matrix.of X from rfl, Matrix.conjTranspose_smul, star_trivial]; rfl }

theorem adjH_apply (X : Lie E n) (i j : Fin n) : adjH X i j = star (X j i) := rfl

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map p g) := by
  ext i j
  change p (c ((g⁻¹ : GL (Fin n) R).val j i)) = c' (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S).val j i)
  rw [h, ← map_inv]
  rfl

theorem thetaA_infGL (y : GL (Fin n) (Cinf E)) :
    thetaA E n (infGL E n y) = infGL E n (thetaR (starRingEnd (Cinf E)) n y) :=
  ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_infGL, pInf_infGL])
    (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

theorem thetaA_finGL (k : GL (Fin n) (Af E)) : thetaA E n (finGL E n k) = finGL E n (thetaF E n k) :=
  ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
    (by rw [pFin_finGL]; rfl)

theorem thetaA_kAt (w : InfinitePlace E) (c : UU n) : thetaA E n (kAt w c) = kAt w c := by
  classical
  have e : kAt w c = infGL E n (locInf w (Unitary.toUnits c)) := rfl
  rw [e, thetaA_infGL]
  congr 1
  refine Units.ext ?_
  ext i j v
  rw [thetaR_val, ← map_inv, ← map_inv]
  change star ((locInf w (Unitary.toUnits c)⁻¹ : GL (Fin n) (Cinf E)).val j i v) = _
  rw [locInf_apply, locInf_apply]
  by_cases hv : v = w
  · simp only [hv, if_true]
    change star ((star c.1 : Matrix (Fin n) (Fin n) ℂ) j i) = c.1 i j
    simp [Matrix.star_apply]
  · simp only [hv, if_false]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem toL_thetaR (y : GL (Fin n) (Cinf E)) :
    toL (thetaR (starRingEnd (Cinf E)) n y).val = adjH (GlobalTheory.ThetaPull.invL (toL y.val)) := by
  rw [thetaR_val]
  ext i j : 2
  change starRingEnd (Cinf E) ((y⁻¹ : GL (Fin n) (Cinf E)).val j i) = star ((y.val)⁻¹ j i)
  rw [Matrix.coe_units_inv]
  rfl

theorem chart_theta (φ : GA E n → ℂ) (g : GA E n) {x : Lie E n} (hx : x ∈ invSet E n) :
    chart (fun g => φ (thetaA E n g)) g x = chart φ (thetaA E n g) (adjH (GlobalTheory.ThetaPull.invL x)) := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_thetaR, chart_val, chart_val, map_mul, thetaA_infGL]

theorem lieD_theta (X : Lie E n) {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g : GA E n) :
    lieD X (fun g => φ (thetaA E n g)) g = -lieD (adjH X) φ (thetaA E n g) := by
  have e : chart (fun g => φ (thetaA E n g)) g =ᶠ[nhds (oneL E n)]
      chart φ (thetaA E n g) ∘ adjH ∘ GlobalTheory.ThetaPull.invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_theta φ g hx
  have h1 : (adjH ∘ GlobalTheory.ThetaPull.invL) (oneL E n) = oneL E n :=
    (toL_thetaR 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E n) (f := adjH ∘ GlobalTheory.ThetaPull.invL)
    (by rw [h1]; exact (differentiableAt_chart hφ (thetaA E n g)).hasFDerivAt)
    ((adjH (E := E) (n := n)).hasFDerivAt.comp (oneL E n) GlobalTheory.ThetaPull.invL_smooth.2)
  unfold lieD
  rw [e.fderiv_eq, h2.fderiv]
  simp

open ComplexConjugate in

theorem atEmb_conjugate (w : InfinitePlace E) (z : ℂ) :
    atEmb (ComplexEmbedding.conjugate w.embedding) z = atEmb w.embedding (conj z) := by
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)
  unfold atEmb
  rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne, if_pos rfl]

open ComplexConjugate in

theorem star_atEmb (w : InfinitePlace E) (z : ℂ) : star (atEmb w.embedding z) = atEmb w.embedding (conj z) := by
  funext v
  simp only [atEmb, InfinitePlace.mk_embedding, if_true, Pi.star_apply]
  by_cases hv : v = w
  · subst hv; simp
  · classical
    rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, star_zero]

def sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : Lie E n := toL (Matrix.single a b (atEmb w.embedding z))

open ComplexConjugate in
theorem adjH_sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : adjH (sg w a b z) = sg w b a (conj z) := by
  funext i j
  rw [adjH_apply]
  change star (Matrix.single a b (atEmb w.embedding z) j i) = Matrix.single b a (atEmb w.embedding (conj z)) i j
  rw [Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos h.symm, star_atEmb]
  · rw [if_neg h, if_neg fun h' => h h'.symm, star_zero]

theorem Eop_apply (τ : E →+* ℂ) (a b : Fin n) (φ : Sm E n) (g : GA E n) :
    (Eop τ a b φ).1 g = (1 / 2 : ℂ) * (lieD (toL (Matrix.single a b (atEmb τ 1))) φ.1 g -
      Complex.I * lieD (toL (Matrix.single a b (atEmb τ Complex.I))) φ.1 g) := rfl

def thV (π : CuspSub E n) (h : ThetaFix π) : Module.End ℂ π.V where
  toFun ψ := ⟨(h.2 ψ.1 ψ.2).choose, (h.2 ψ.1 ψ.2).choose_spec.1⟩
  map_add' a b := Subtype.ext <| Subtype.ext <| funext fun x => by
    change (h.2 (a + b).1 (a + b).2).choose.1 x =
      (h.2 a.1 a.2).choose.1 x + (h.2 b.1 b.2).choose.1 x
    rw [(h.2 (a + b).1 (a + b).2).choose_spec.2, (h.2 a.1 a.2).choose_spec.2, (h.2 b.1 b.2).choose_spec.2]
    rfl
  map_smul' c a := Subtype.ext <| Subtype.ext <| funext fun x => by
    change (h.2 (c • a).1 (c • a).2).choose.1 x = c * (h.2 a.1 a.2).choose.1 x
    rw [(h.2 (c • a).1 (c • a).2).choose_spec.2, (h.2 a.1 a.2).choose_spec.2]
    rfl

theorem thV_apply (π : CuspSub E n) (h : ThetaFix π) (ψ : π.V) (x : GA E n) :
    ((thV π h ψ : π.V) : Sm E n).1 x = (ψ : Sm E n).1 (thetaA E n x) :=
  (h.2 ψ.1 ψ.2).choose_spec.2 x

end GlobalTheory.CompanionTheory.TwY.ThInv
end
