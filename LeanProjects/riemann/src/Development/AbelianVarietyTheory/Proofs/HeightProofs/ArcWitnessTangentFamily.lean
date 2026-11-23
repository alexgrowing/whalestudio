import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange

noncomputable section

namespace GlobalTheory.ConstEig

open Matrix

theorem eig_toPowerSeries {A : Type} [CommRing A] {I : Type} {g m : ℕ}
    (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (h : ∀ z : Fin g → A, (∀ i, z ᵥ* M i = ρ i • z) → ∃! cf : Fin m → A, z = ∑ k, cf k • U k)
    (w : Fin g → PowerSeries A)
    (hw : ∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) :
    ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j) := by
  have key : ∀ cf : Fin m → PowerSeries A, (w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j)) ↔
      ∀ n, (fun j => PowerSeries.coeff n (w j)) = ∑ k, PowerSeries.coeff n (cf k) • U k := fun cf => by
    simp only [funext_iff, PowerSeries.ext_iff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum,
      PowerSeries.coeff_mul_C]
    exact forall_comm
  choose c hc hu using fun n => h (fun j => PowerSeries.coeff n (w j)) fun i => by
    funext j
    have := congrArg (PowerSeries.coeff n) (congrFun (hw i) j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine ⟨fun k => PowerSeries.mk fun n => c n k, (key _).2 fun n => ?_, fun cf hcf => ?_⟩
  · simpa only [PowerSeries.coeff_mk] using hc n
  · funext k
    ext n
    rw [PowerSeries.coeff_mk, ← hu n _ ((key _).1 hcf n)]

end GlobalTheory.ConstEig

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

open Matrix GlobalTheory.BasisUniv GlobalTheory.ConstLie in

theorem GlobalTheory.ConstEig.basis_iff_const : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (m : ℕ) (e : Fin m → Out.GtPt a.D₀ (epsR A)) (v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)) (eig : (epsR (PowerSeries A) ⟶ W.t.G) → Prop), (∀ w, eig w ↔ ∀ x : 𝓞 E, (w ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ w.left) → (∀ k, LieImg W (e k) (v k)) → (∀ k, IsTangent (v k) ∧ eig (v k)) → ((∀ w, IsTangent w → eig w → ∃! cf : Fin m → PowerSeries A, IsLieComb cf v w) ↔ ∀ ν w, LieImg W ν w → IsTangent w → eig w → ∃! cf : Fin m → A, GtComb cf e ν) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W t m e v eig heig hev hv
  have ex := GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W
  have lin := GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W

  have back : ∀ {n : ℕ} {e₀ : Fin n → Out.GtPt a.D₀ (epsR A)} {v₀ : Fin n → (epsR (PowerSeries A) ⟶ W.t.G)},
      (∀ k, LieImg W (e₀ k) (v₀ k)) → ∀ {ν w} {cf : Fin n → PowerSeries A}, LieImg W ν w → IsLieComb cf v₀ w →
      GtComb (fun i => PowerSeries.constantCoeff (cf i)) e₀ ν := fun {n e₀ v₀} h₀ ν w cf hw hc => by
    obtain ⟨ν', hν'⟩ := exists_gtComb (fun i => PowerSeries.constantCoeff (cf i)) e₀
    obtain ⟨t', ht', -⟩ := (ex ν').1
    obtain rfl : ν = ν' := eq_of_red W hG hw ht'
      (red_eq_of_comb _ hc ((lin n _ e₀ ν' v₀ t' h₀ hν').1 ht') (fun i => by simp) fun _ => rfl)
    exact hν'
  constructor
  · intro h ν w hw ht he
    obtain ⟨cf, hc, hu⟩ := h w ht he
    refine ⟨_, back hev hw hc, fun cf' h' => funext fun i => ?_⟩
    rw [← hu _ ((lin m _ e ν v w hev h').1 hw)]
    simp
  · intro h w ht he
    obtain ⟨g, e₁, v₁, M, hev₁, hv₁, hcomb, hM⟩ := exists_const_basis hG E H Dw l Xo c O β Y A b a χ W
    have hsm : Smooth W.t.G.hom := W.t.semi.smooth
    have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
    obtain ⟨n, y, hy⟩ := Chart.univChartLoc W.t.G
    have hU : ∀ k, ∃ U : Fin g → A, IsLieComb (fun j => PowerSeries.C (R := A) (U j)) v₁ (v k) := fun k => by
      obtain ⟨U, hU, -⟩ := hcomb _ (((ex (e k)).2 _ (hev k)).2 (hv k).1)
      exact ⟨U, (lin g U e₁ (e k) v₁ _ (fun i => (hev₁ i).2) hU).1 (hev k)⟩
    choose U hU using hU
    have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v₁ (v₁ i ≫ W.t.act.act x) := hM
    obtain ⟨z, hz, -⟩ := hv₁.2 w ht
    simp only [comb_iff hy hv₁ hU hz]
    refine GlobalTheory.ConstEig.eig_toPowerSeries M (fun x => t x) U (fun s hs => ?_) z
      (fun x => (eig_iff hy hv₁ _ (hMR x) hz _).1 ((heig w).1 he x))
    obtain ⟨ν, hν⟩ := exists_gtComb s e₁
    obtain ⟨w', hw', -⟩ := (ex ν).1
    have hc := (lin g s e₁ ν v₁ w' (fun i => (hev₁ i).2) hν).1 hw'
    have key : ∀ cf : Fin m → A, GtComb cf e ν ↔ s = ∑ k, cf k • U k := fun cf => by
      have e₂ : IsLieComb (fun k => PowerSeries.C (R := A) (cf k)) v w' ↔ s = ∑ k, cf k • U k := by
        rw [comb_iff hy hv₁ hU hc]
        constructor
        · intro q
          funext j
          have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun q j)
          simpa [Finset.sum_apply] using this
        · intro q
          funext j
          have := congrArg (PowerSeries.C (R := A)) (congrFun q j)
          simpa [Finset.sum_apply] using this
      rw [← e₂]
      exact ⟨fun q => (lin m cf e ν v w' hev q).1 hw', fun q => by simpa using back hev hw' q⟩
    have := h ν w' hw' (isTangent_of_comb hy hv₁.1 hc) ((heig w').2 fun x =>
      (eig_iff hy hv₁ _ (hMR x) hc _).2 (by
        funext j
        have := congrArg (PowerSeries.C (R := A)) (congrFun (hs x) j)
        simpa [Matrix.vecMul, dotProduct] using this))
    simpa only [key] using this
