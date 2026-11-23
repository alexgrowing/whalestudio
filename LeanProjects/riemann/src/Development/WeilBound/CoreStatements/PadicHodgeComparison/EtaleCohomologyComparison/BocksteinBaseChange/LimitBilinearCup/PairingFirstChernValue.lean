import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.FirstChernClassUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PeriodMapZEqCast
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.Imports

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {G : Model l K → Prop}
  {D : Dat R} {C : PerC R} {I : Iso l K C.K₀} {β : BMap G D} {β₁ : BPhi β}

variable (hF : R.Facts) (hC : C.Facts) (Fm : FMap G C I D β₁.pull) (hL : D.Laws G) (E : EMap G D)
  {X : XEnd I} {Y : XMid D X}

include hL in
theorem plus_cup (HX : XLaws Y E β β₁ Fm) {M : Model l K} (hM : G M) (a : D.Ch M) {i j : ℕ} (x : M.T i) (y : M.T j)
    (z : M.T (i + j)) (hz : M.CupT x y z) {m m' : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M i))
    (b' : Module.Basis (Fin m') C.K₀ (I.D M j)) (f : Module.Dual C.K₀ (I.D M (i + j))) :
    delta hF hC Fm a (i + j) (E.e a (i + j) z) f = ∑ s, ∑ s', delta hF hC Fm a i (E.e a i x) (b.coord s) *
      delta hF hC Fm a j (E.e a j y) (b'.coord s') * C.k (f (X.cupD M i j (b s) (b' s'))) := by
  obtain ⟨zh, hzh⟩ := HX.cup_ex a hM (dX β a hM i (E.e a i x)) (dX β a hM j (E.e a j y))
  have h1 := HX.β_cup a hM _ _ _ hzh
  rw [dX_spec, dX_spec] at h1
  have h2 := hL.cup_smul a (R.t ^ dN β a hM i) (R.t ^ dN β a hM j) _ _ _ (E.cup a hM x y z hz)
  have h3 := hL.cup_uniq a _ _ _ _ h1 h2
  have h4 := HX.ψ_cup a hM _ _ _ hzh b b' f
  rw [delta_key hF hC Fm hM h3 f] at h4
  simp only [delta_key' hF hC Fm hM] at h4
  have hu : IsUnit (iP C Fm.k (R.t ^ dN β a hM i * R.t ^ dN β a hM j)) := by
    rw [map_mul]; exact (iP_unit hF hC _ _).mul (iP_unit hF hC _ _)
  apply hu.mul_left_cancel
  rw [h4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [map_mul]
  ring

include hL in
theorem plus_one (HX : XLaws Y E β β₁ Fm) {M : Model l K} (hM : G M) (a : D.Ch M) (v : M.T 0) (y : I.D M 0)
    (hv : X.oneT M v) (hy : X.oneD M y) (f : Module.Dual C.K₀ (I.D M 0)) :
    delta hF hC Fm a 0 (E.e a 0 v) f = C.k (f y) := by
  obtain ⟨x, hx⟩ := HX.one_ex a hM
  have h1 := hL.one_uniq a _ _ (HX.β_one a hM x hx) (HX.e_one a hM v hv)
  have h2 := delta_key hF hC Fm hM (c := 1) (by rw [h1, one_smul]) f
  rw [map_one, one_mul] at h2
  rw [← h2, HX.ψ_one a hM x y hx hy f]

theorem pairing_first_chern_value (HX : XLaws Y E β β₁ Fm) {M : Model l K} (hM : G M) (a : D.Ch M) (L : X.Ln M) (v : M.T 2)
    (y : I.D M 2) (hv : X.c1T L v) (hy : X.c1D L y) (f : Module.Dual C.K₀ (I.D M 2)) :
    (l : C.C) ^ Fm.k * C.c R.t * delta hF hC Fm a 2 (E.e a 2 v) f = C.k (f y) := by
  obtain ⟨x, hx⟩ := HX.first_chern_class_exists a hM L
  have h1 := HX.first_chern_class_unique a hM L _ _ (HX.beta_firstChern a hM L x hx) (HX.etale_firstChern a hM L v hv)
  have h2 := delta_key hF hC Fm hM h1 f
  rw [HX.psi_firstChern a hM L x y hx hy f, iP_apply] at h2
  have e : R.φ^[Fm.k] R.t = (l : R.A) ^ Fm.k * R.t := by
    simpa using phiA_iterate_tA_of_prime hF Fm.k 1
  rw [h2, e, map_mul, map_pow, map_natCast]

theorem phiPlus : ProductClassComparison := by
  intro l _ K R G C I D X Y hF hC hE hL E β β₁ κ Fm HX
  obtain ⟨P, -, hP⟩ := pre' l K R G D hF hE hL E β κ
  refine ⟨crys hF hC Fm hL E hE (fun M n hM => cC_inj hF hC Fm hL E hE κ inj P hP M n hM), ?_⟩
  refine ⟨fun M hM i j x y z hz m m' b b' f => ?_, fun M hM v y hv hy f => ?_,
    fun M hM L v y hv hy f => ?_⟩
  · show cC hF hC Fm hL E M (i + j) (M.toV _ z) f = ∑ s, ∑ s', cC hF hC Fm hL E M i (M.toV _ x) (b.coord s) *
      cC hF hC Fm hL E M j (M.toV _ y) (b'.coord s') * C.k (f (X.cupD M i j (b s) (b' s')))
    simp only [cC_toV hF hC Fm hL E hM (a0 hL M hM)]
    exact plus_cup hF hC Fm hL E HX hM _ x y z hz b b' f
  · show cC hF hC Fm hL E M 0 (M.toV 0 v) f = C.k (f y)
    rw [cC_toV hF hC Fm hL E hM (a0 hL M hM)]
    exact plus_one hF hC Fm hL E HX hM _ v y hv hy f
  · show (l : C.C) ^ Fm.k * C.c R.t * cC hF hC Fm hL E M 2 (M.toV 2 v) f = C.k (f y)
    rw [cC_toV hF hC Fm hL E hM (a0 hL M hM)]
    exact pairing_first_chern_value hF hC Fm E HX hM _ L v y hv hy f

end CrystallineSemistableComparison
