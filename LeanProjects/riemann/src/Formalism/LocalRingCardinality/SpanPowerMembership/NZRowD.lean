import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowB
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowC

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

variable (D : D7)

def divXStd (n : ℕ → ℕ) (bM : ∀ j, OrthonormalBasis (Fin (n j)) ℂ (D.what₂.Mj j))
    (hg : ∀ j, (D.what₂.MjLat j).gen = genB (bM j)) (kap : ℝ) (hk : 0 < kap) : DivX D where
  geo := geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}
  plpFin := fun p _ => PlOver.plFin D p
  plpNe := fun p _ => PlOver.plNe D p
  wtP := fun p _ la => PlOver.wt D p la.1
  divisorWeight_nonneg := fun p _ la => PlOver.wt_nonneg D p la.1
  divisorWeight_sum := fun p _ => PlOver.wt_sum D p
  plP := fun _ _ => Equiv.refl _
  divisorWeight_def := fun _ _ _ => rfl
  jC := fun p _ _ => (teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := fun j => stdH D.what₂.LL (n j)
  MjH_good := fun j => stdH_good _ _
  jM := fun j => jB D.what₂.embLL (bM j)
  jM_basis := fun j => jB_basis _ _
  jM_lat := fun j _ _ x => by rw [hg]; exact jB_lat _ _ x
  jM_metric := fun j _ _ x => jB_norm _ _ x
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  logLam_base := fun _ _ => rfl
  kapR := fun _ => kap
  kapR_pos := fun _ => hk
  kapR_conj := fun _ => rfl
  MjLat_sub := fun j _ _ => by rw [hg]; exact jB_gen _ _
  phiFr_unram := fun _ κ => κ.elim
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

theorem ijIdx_zero {D : D7} (X : DivX D) (μ j w) (h : (X.MjH j).L = Idx.thTj X μ j) : Idx.IjIdx X μ j w = 0 := by
  unfold Idx.IjIdx Formalism.HermitianLatticesTheory.lidx
  rw [h]; exact sub_self _

theorem jwIdx_zero (μ j w) (h : Idx.TjL D μ j = Idx.TjDual D μ j) : Idx.jwIdx D μ j w = 0 := by
  unfold Idx.jwIdx Formalism.HermitianLatticesTheory.lidx
  rw [← h]; exact sub_self _

theorem lamDef_of (h : ∀ μ j π, ∀ x ∈ D.what₂.isot j π,
    D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = ((D.what₂.lamP μ j π : ℝ) : ℂ) • x) : DV.LamDef D :=
  fun μ j _ _ π h0 => (DV.lamTr_of_scalar D μ j π _ h0 (h μ j π)).symm

section Kap

variable {D} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

theorem iiStar_id (he : S.eOp D.what₂.mu0 = LinearMap.id)
    (hiso : ∀ x y, inner ℂ (S.iota D.what₂.mu0 x) (S.iota D.what₂.mu0 y) = inner ℂ x y)
    (hs : Function.Surjective (S.iota D.what₂.mu0)) : S.iiStar = LinearMap.id := by
  have hi : Function.Injective (S.iota D.what₂.mu0) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have := hiso x x
    rw [LinearMap.mem_ker.mp hx, inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  ext x
  refine ext_inner_right ℂ fun y => ?_
  obtain ⟨z, rfl⟩ := hs y
  have hz : z ∈ S.Qsp D.what₂.mu0 := by rw [Qsp_top S he hi]; trivial
  show inner ℂ (S.iota D.what₂.mu0 (LinearMap.adjoint (S.iotaQ D.what₂.mu0) x : S.Amb D.what₂.mu0))
    (S.iota D.what₂.mu0 z) = inner ℂ x (S.iota D.what₂.mu0 z)
  rw [hiso]
  have h1 : inner ℂ (LinearMap.adjoint (S.iotaQ D.what₂.mu0) x) (⟨z, hz⟩ : S.Qsp D.what₂.mu0) =
      inner ℂ x (S.iotaQ D.what₂.mu0 ⟨z, hz⟩) := LinearMap.adjoint_inner_left _ _ _
  exact h1

theorem kapOf_one {n : ℕ} (ty : Fin n → D.what₂.FT) (hii : S.iiStar = LinearMap.id)
    (hl : ∀ j π, D.what₂.lamP D.what₂.mu0 j π = 1) : S.kapOf ty = 1 := by
  have hr : S.kapRatio ty = 1 := by
    unfold RowSide.kapRatio DV.lamProd
    rw [hii, LinearMap.det_id]
    simp [hl]
  unfold RowSide.kapOf
  rw [hr, if_pos one_pos, Real.one_rpow]

end Kap

end Formalism.BasicNotions.Examples₂.NZ
