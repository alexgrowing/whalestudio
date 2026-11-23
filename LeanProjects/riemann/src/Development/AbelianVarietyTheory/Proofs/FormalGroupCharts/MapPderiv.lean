import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NonemptyTensorQuotientEquiv
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAdicCompleteOfFgOfNatCastMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AlgHomDualNumberExt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapMaximalIdealEqKerMapResidue
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.DetJacobianFormalMulNEqPowMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesMemMapCOfCoeffMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MulFConstAndMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsReducedGenericFibreOfIsReduced
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLawChartFiniteHeightSpecialFibreStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinEtaleFormallyUnramified

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalTorsion

theorem map_pderiv {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : MvPowerSeries σ R) (s : σ) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv R s f) = MvPowerSeries.pderiv S s (MvPowerSeries.map φ f) := by
  ext n
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv]

theorem map_bound {R S σ κ : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : κ → MvPowerSeries σ R)
    (I : Ideal R) (M : ℕ)
    (h : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤
      Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) I) :
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ S)) ^ M ≤
      Ideal.span (Set.range fun j => MvPowerSeries.map φ (f j)) ⊔
        Ideal.map (MvPowerSeries.C : S →+* MvPowerSeries σ S) (Ideal.map φ I) := by
  have h2 := Ideal.map_mono (f := MvPowerSeries.map φ) h
  rw [Ideal.map_pow, Ideal.map_span, Ideal.map_sup, Ideal.map_span, Ideal.map_map] at h2
  have e1 : (MvPowerSeries.map φ) '' Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R) =
      Set.range (MvPowerSeries.X : σ → MvPowerSeries σ S) := by
    rw [← Set.range_comp]
    congr 1
    funext s
    simp [MvPowerSeries.map_X]
  have e2 : (MvPowerSeries.map φ) '' Set.range f = Set.range fun j => MvPowerSeries.map φ (f j) := by
    rw [← Set.range_comp]
    rfl
  have e3 : (MvPowerSeries.map φ).comp (MvPowerSeries.C : R →+* MvPowerSeries σ R) =
      (MvPowerSeries.C : S →+* MvPowerSeries σ S).comp φ := by
    ext a
    simp [MvPowerSeries.map_C]
  rw [e1, e2, e3] at h2
  rw [Ideal.map_map]
  exact h2

theorem fhSt : ∀ (p : ℕ) [Fact p.Prime], FHSt p := by
  intro p _
  unfold FHSt
  intro T _ _ _ _ _ _ hp G _ _ D A hU d F x hx C _ _ _ v O _ _ hv _ _ iota hiota m
  unfold QF
  have hp0 : p ≠ 0 := Nat.Prime.ne_zero Fact.out
  have hN1 : 1 ≤ p ^ m := Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)
  have hNd : (p ^ m) ^ d ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp0)

  let e : Fin d ≃ Fin 1 × Fin d :=
    { toFun := fun j => (0, j), invFun := fun q => q.2, left_inv := fun _ => rfl,
      right_inv := fun q => Prod.ext (Subsingleton.elim _ _) rfl }
  let _ : Algebra T O := iota.toAlgebra
  have : IsDomain O := hv.hom_inj.isDomain
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : IsFractionRing O C := hv.isFractionRing

  have hc : ∀ j, MvPowerSeries.constantCoeff (mulF F.F (p ^ m) j) = 0 := fun j =>
    (GlobalTheory.FormalMul.mulF_const_and_map T O iota d F (p ^ m) j).1
  have hmap : ∀ j, mulF (F.mapF iota) (p ^ m) j = MvPowerSeries.map iota (mulF F.F (p ^ m) j) :=
    fun j => (GlobalTheory.FormalMul.mulF_const_and_map T O iota d F (p ^ m) j).2

  obtain ⟨M, hM⟩ := GlobalTheory.T.formalGroupLaw_chart_finiteHeight_specialFibre T G D A hU d F x hx (p ^ m) hN1
  obtain ⟨hFree, hFin⟩ := GlobalTheory.FiniteColength.free_finite_quotient T inferInstance (Fin 1 × Fin d) d e
    (mulF F.F (p ^ m)) hc ⟨M, hM⟩
  have hMT := GlobalTheory.span_X_pow_le_sup_of_residue T (Fin 1 × Fin d) (Fin d) (mulF F.F (p ^ m)) M hM

  have hFGT : (maximalIdeal T).FG := IsNoetherian.noetherian _
  have hJfg : ((maximalIdeal T).map iota).FG := hFGT.map iota
  have hJle : (maximalIdeal T).map iota ≤ maximalIdeal O :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit iota a ha
  have hJne : (maximalIdeal T).map iota ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 (h ▸ hJle))
  have hpT : (p : T) ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal _).2 hp
  have hpJ : (p : O) ∈ (maximalIdeal T).map iota := by
    simpa using Ideal.mem_map_of_mem iota hpT
  have hJc : IsAdicComplete ((maximalIdeal T).map iota) O :=
    GlobalTheory.isAdicComplete_of_fg_of_natCast_mem C v O hv p hp0 inferInstance _ hJfg hJne hpJ

  obtain ⟨eqv⟩ := GlobalTheory.QuotientBaseChange.nonempty_tensor_quotient_equiv T O (maximalIdeal T) hFGT hJc
    (Fin 1 × Fin d) (Fin d) (mulF F.F (p ^ m)) M hMT hFree hFin
  have hspan : (Set.range fun j => MvPowerSeries.map (algebraMap T O) (mulF F.F (p ^ m) j)) =
      Set.range (mulF (F.mapF iota) (p ^ m)) := by
    congr 1
    funext j
    exact (hmap j).symm
  rw [hspan] at eqv
  have hFO : Module.Free O (MvPowerSeries (Fin 1 × Fin d) O ⧸
      Ideal.span (Set.range (mulF (F.mapF iota) (p ^ m)))) :=
    Module.Free.of_equiv eqv.toLinearEquiv
  have hFinO : Module.Finite O (MvPowerSeries (Fin 1 × Fin d) O ⧸
      Ideal.span (Set.range (mulF (F.mapF iota) (p ^ m)))) :=
    Module.Finite.equiv eqv.toLinearEquiv

  have hMO := map_bound iota (mulF F.F (p ^ m)) (maximalIdeal T) M hMT
  have hfun : (fun j => MvPowerSeries.map iota (mulF F.F (p ^ m) j)) = mulF (F.mapF iota) (p ^ m) :=
    funext fun j => (hmap j).symm
  rw [hfun] at hMO
  obtain ⟨U, hU8⟩ := GlobalTheory.T.det_jacobian_formalMulN_eq_pow_mul_unit T d F (p ^ m)
  have h2 : Matrix.of (fun i j : Fin d => MvPowerSeries.pderiv O (e j) (mulF (F.mapF iota) (p ^ m) i)) =
      (MvPowerSeries.map iota).mapMatrix
        (Matrix.of fun i j : Fin d => MvPowerSeries.pderiv T ((0 : Fin 1), j) (mulF F.F (p ^ m) i)) := by
    ext i j
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [map_pderiv, hmap]
    rfl
  have hdet : Matrix.det (Matrix.of fun i j : Fin d =>
      MvPowerSeries.pderiv O (e j) (mulF (F.mapF iota) (p ^ m) i)) =
      (((p ^ m) ^ d : ℕ) : MvPowerSeries (Fin 1 × Fin d) O) *
        (Units.map (MvPowerSeries.map iota).toMonoidHom U : (MvPowerSeries (Fin 1 × Fin d) O)ˣ) := by
    rw [h2, ← RingHom.map_det, hU8, map_mul, map_pow, map_natCast]
    simp only [Nat.cast_pow]
    rfl
  have hdn := GlobalTheory.NoTangent.algHom_dualNumber_ext C v O hv p hp0 inferInstance _ hJfg hJne hpJ
    (Fin 1 × Fin d) d e (mulF (F.mapF iota) (p ^ m)) M ((p ^ m) ^ d) _ hNd hMO hdet

  obtain ⟨-, hsep, -⟩ := GlobalTheory.finEtale_main C O (MvPowerSeries (Fin 1 × Fin d) O ⧸
      Ideal.span (Set.range (mulF (F.mapF iota) (p ^ m)))) v hv hdn
  have hred : IsReduced (MvPowerSeries (Fin 1 × Fin d) O ⧸
      Ideal.span (Set.range (mulF (F.mapF iota) (p ^ m)))) :=
    ⟨fun q hq => hsep q fun φ => (hq.map φ).eq_zero⟩
  exact ⟨hFO, hFinO, GlobalTheory.isReduced_genericFibre_of_isReduced O C _ hred, hsep⟩

end GlobalTheory.FormalTorsion
