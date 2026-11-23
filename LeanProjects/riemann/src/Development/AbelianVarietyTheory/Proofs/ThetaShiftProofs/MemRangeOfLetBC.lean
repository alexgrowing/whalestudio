import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.IntLetterCoord

open Matrix GlobalTheory.BasisUniv

theorem mem_range_of_comb {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] {I : Type} {g m : ℕ} (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (hU : ∀ k i, U k ᵥ* M i = ρ i • U k)
    (h : ∀ w : Fin g → PowerSeries A, (∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) →
      ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j))
    (z : Fin g → A) (y : Fin m → K) (hz : (fun j => algebraMap A K (z j)) = ∑ k, y k • fun j => algebraMap A K (U k j))
    (k : Fin m) : y k ∈ Set.range (algebraMap A K) := by
  have hK : ∀ i, (fun j => algebraMap A K (z j)) ᵥ* (M i).map (algebraMap A K) =
      algebraMap A K (ρ i) • fun j => algebraMap A K (z j) := fun i => by
    have e : ∀ k, (fun j => algebraMap A K (U k j)) ᵥ* (M i).map (algebraMap A K) =
        algebraMap A K (ρ i) • fun j => algebraMap A K (U k j) := fun k => by
      funext j
      have := congrArg (algebraMap A K) (congrFun (hU k i) j)
      simpa [Matrix.vecMul, dotProduct] using this
    rw [hz, Matrix.sum_vecMul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_vecMul, e, smul_comm]
  have hA : ∀ i, z ᵥ* (M i).map (RingHom.id A) = RingHom.id A (ρ i) • z := fun i => by
    funext j
    apply IsFractionRing.injective A K
    have := congrFun (hK i) j
    simpa [Matrix.vecMul, dotProduct] using this
  have hfl : (algebraMap A K).Flat :=
    RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors A))
  obtain ⟨cf, hcf, -⟩ := eig_powerSeries M ρ U hU h (RingHom.id A) (RingHom.Flat.id A) z hA
  have := (eig_powerSeries M ρ U hU h (algebraMap A K) hfl _ hK).unique (y₂ := fun k => algebraMap A K (cf k)) hz (by
    funext j
    have := congrArg (algebraMap A K) (congrFun hcf j)
    simpa [Finset.sum_apply, Algebra.smul_def] using this)
  exact ⟨cf k, (congrFun this k).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem mem_range_of_letBC (hL : Out.Laws) (hL₂ : Out.Laws2) (hU : Out.UnifBaseChangeSt) (hL₅ : Out.Laws5)
    {A K : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {b : O →+* A} {b' : O →+* K}
    {a : ArcIn Dw l β A b} {a' : ArcIn Dw l β K b'}
    {p : Out.IsPullDeg (algebraMap A K) a.D₀ a'.D₀} (hp : InBC (algebraMap A K) a a' p)
    {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (hB : ArcBasis W ρ e) (τ : E →+* ℂ) {e₁ : Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR K)}
    (he : ∀ k, LetBC p (e τ k) (e₁ k)) {ν : Out.GtPt a.D₀ (epsR A)} {ν₁ e₂ : Out.GtPt a'.D₀ (epsR K)}
    (hν : GtTanR ν) (hν₁ : LetBC p ν ν₁) {y : Fin (Dw.mult τ) → K} (h₂ : GtComb y e₁ e₂) {x : K}
    (hx : GtComb ![x] ![e₂] ν₁) (k : Fin (Dw.mult τ)) : x * y k ∈ Set.range (algebraMap A K) := by
  have hG := hL.globalFns
  have hf : Function.Injective (algebraMap A K) := IsFractionRing.injective _ _
  obtain ⟨hW, -⟩ := (GlobalTheory.ArcQBC.baseChanges hL hL₂ hU hL₅ E H Dw l Xo c O β Y A K b a _ hf b' hp.1).2 a' p hp
  obtain ⟨W', hW'⟩ := hW χ W
  obtain ⟨m, -, hm, -⟩ := GlobalTheory.ArcBaseChange.main hL hL₂ E H Dw l Xo c O β Y A b a χ W K b' a' _ p W' hp hW'
  obtain ⟨v₀, hv₀, hB⟩ := hB
  obtain ⟨g, s, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c O β Y A b a χ W
  have ex := GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y A b a χ W
  have ex' := GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y K b' a' _ W'
  have lin := GlobalTheory.ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y A b a χ W
  have lin' := GlobalTheory.ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y K b' a' _ W'
  have hsm : Smooth W.t.G.hom := W.t.semi.smooth
  have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
  obtain ⟨n, j, hy⟩ := Chart.univChartLoc W.t.G
  obtain ⟨n', j', hy'⟩ := exists_chart_of_pullback _ m.cart
  choose v' hv' using fun j => exists_lift _ m.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange _ m.cart hv hv'
  have coord : ∀ ξ ξ' w, GtTanR ξ → LieImg W ξ w → LetBC p ξ ξ' → ∃ (z : Fin g → A) (w' : epsR (PowerSeries K) ⟶ W'.t.G),
      IsLieComb (fun j => PowerSeries.C (R := A) (z j)) v w ∧ LieImg W' ξ' w' ∧
      IsLieComb (fun j => PowerSeries.C (R := K) (algebraMap A K (z j))) v' w' := fun ξ ξ' w ht hw hξ => by
    obtain ⟨z, hz, -⟩ := hcomb _ ht
    have h1 := (lin g z s ξ v w (fun i => (hev i).2) hz).1 hw
    obtain ⟨w', hw'⟩ := exists_lift _ m.cart w
    refine ⟨z, w', h1, hm _ _ w w' hξ hw hw', ?_⟩
    simpa only [PowerSeries.map_C] using Chart.comb_baseChange _ m.cart h1 hv' hw'
  choose U u hU₀ hu hU' using fun k => coord _ _ _ (((ex (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1) (hv₀ τ k) (he k)
  obtain ⟨w, hw⟩ := (ex ν).1.exists
  obtain ⟨z, w', -, hw', hz'⟩ := coord _ _ _ hν hw hν₁
  obtain ⟨w₂, hw₂⟩ := (ex' e₂).1.exists
  have c₂ := (lin' _ y e₁ e₂ u w₂ hu h₂).1 hw₂
  have c₁ := (lin' _ ![x] ![e₂] ν₁ (fun _ => w₂) w' (fun i => by fin_cases i; exact hw₂) hx).1 hw'
  have d₂ : IsLieComb (∑ k, PowerSeries.C (R := K) (y k) • fun j => PowerSeries.C (R := K) (algebraMap A K (U k j)))
      v' w₂ := by
    have hc := (Chart.isLieComb_iff (∑ k, PowerSeries.C (R := K) (y k) •
      fun j => PowerSeries.C (R := K) (algebraMap A K (U k j))) v' _).2 rfl
    have := (comb_iff hy' hb' hU' hc _).2 rfl
    rwa [((Chart.isLieComb_iff _ _ _).1 this).trans ((Chart.isLieComb_iff _ _ _).1 c₂).symm] at hc
  have d₁ := (comb_iff hy' hb' (u := fun _ : Fin 1 => w₂) (fun _ => d₂) hz' _).1 c₁
  have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
  have hUe : ∀ k x, U k ᵥ* M x = ρ τ x • U k := fun k x => by
    have := (eig_iff hy hv _ (hMR x) (hU₀ k) _).1 (((hB τ).1 k).2 x)
    funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine mem_range_of_comb M (fun x => ρ τ x) U hUe (fun s hs => ?_) z (fun k => x * y k) ?_ k
  · have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv hU₀ hc] using this
  · funext i
    have := congrArg (PowerSeries.constantCoeff (R := K)) (congrFun d₁ i)
    simpa [Finset.sum_apply, Finset.mul_sum, _root_.mul_assoc] using this

theorem main : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (Yw : Model Xo c (c.V Wl).subtype), Yw.N4 → (∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew) → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (x : Tv.Fr), (∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![x] ![e₂] ν₁) → ∀ m, x * M.g τ k m ∈ Set.range (algebraMap Tv.V Tv.Fr) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d Tv io Wl M Yw hN hB τ k x ⟨ν, ν₁, e₂, hν, hν₁, he₂, hx⟩ m
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨χ₀, hχ₀, -⟩ := hN Tv.V M.b ϖ M.aw (Or.inr ⟨inferInstance, hϖ, by
    rw [← hϖ.maximalIdeal_eq]; infer_instance⟩)
  obtain ⟨W₀⟩ := (Yw.hasArcData_iff _ _ _ _ _).1 ((hχ₀ χ₀).1 rfl).2.2.2
  obtain ⟨e₁, e₂', l₁, l₂, -, hg⟩ := M.e_tie
  have hK' : InBC io (d.a.restrict (c.V d.Wp).subtype) (M.aK.restrict (c.V d.Wp).subtype) M.pK := ⟨rfl, M.bcK.2⟩
  obtain ⟨-, x₂, -⟩ :=
    (GlobalTheory.ArcQBC.baseChanges hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c _ _ d.Y K₁ Tv.Fr _
      (d.a.restrict (c.V d.Wp).subtype) io io.injective _ hK'.1).2 (M.aK.restrict (c.V d.Wp).subtype) M.pK hK'
  obtain rfl : e₂ = e₂' τ k := (x₂ (d.e τ k)).unique he₂ (l₂ τ k)
  exact mem_range_of_letBC hK.laws hK.laws2 hK.ubc hK.laws5 M.bcw W₀ (hB χ₀ W₀) τ (l₁ τ) hν hν₁ (hg τ k) hx m

end GlobalTheory.IntLetterCoord
