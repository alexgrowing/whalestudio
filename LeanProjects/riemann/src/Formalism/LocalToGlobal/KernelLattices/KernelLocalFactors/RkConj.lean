import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThIndEqAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.CharacterFactorUnitaryAction
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.GMConjTranspose

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd.CarC

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section SeamU

variable {D : Car} {X : Fields} (s : Cd.Seam D X)

def matU {n : ℕ} (γ : UF X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E).map s.iE

theorem vec_gmap {n : ℕ} (γ : UF X.E n) (x : Sp X.E n) : s.vec (γ.1 x) = (matU s γ).mulVec (s.vec x) := by
  have h := toGLm_mulVec γ.1 x
  rw [← h]
  funext i
  simp only [Cd.Seam.vec, Matrix.mulVec, dotProduct, map_sum, map_mul, matU]
  rfl

theorem lat_gmap {n : ℕ} (γ : UF X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat (gmap γ.1 N) = SDLat.smulLat (matU s γ) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  simp only [SDLat.smulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := hx
    exact ⟨s.vec x0, (s.mem_lat N _).2 ⟨x0, hx0, rfl⟩, (vec_gmap s γ x0).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    exact ⟨γ.1 x0, ⟨x0, hx0, rfl⟩, vec_gmap s γ x0⟩

theorem matU_mem (hok : s.Ok) {n : ℕ} (γ : UF X.E n) :
    (letI := D.host.cmStar; matU s γ ∈ Matrix.unitaryGroup (Fin n) D.host.E) := by
  let _ := D.host.cmStar
  have h : Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) * 1 *
      ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) = 1 := toGLm_mem_UJ γ
  rw [Matrix.mul_one] at h
  have key : star (matU s γ) = (Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)).map s.iE := by
    ext i j
    rw [Matrix.star_apply, Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.star_conj]
    simp only [matU, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    rw [hok.2]
  rw [Matrix.mem_unitaryGroup_iff', key, matU, ← Matrix.map_mul, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem det_matU {n : ℕ} (γ : UF X.E n) : (matU s γ).det = s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) := by
  rw [← TE.det_ufGL]
  exact (RingHom.map_det s.iE.toRingHom _).symm

theorem prod_emb (hok : s.Ok) (z : X.E) : ∏ τ : X.Tau, X.embC s.σ₀ τ z = ∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (s.iE z) :=
  Fintype.prod_equiv s.iT _ _ fun τ => hok.1 τ z

end SeamU

section Laws

variable {D : Car} {X : Fields} (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem ambOf_conj (hok : s.Ok) (τ : X.Tau) (x : X.E) :
    X.embC (Cd.ambOf s B χ cD).σ₀ τ (star x) = star (X.embC (Cd.ambOf s B χ cD).σ₀ τ x) := by
  let _ := D.host.cmStar
  show s.σ₀ (X.emb τ (star x)) = star (s.σ₀ (X.emb τ x))
  rw [hok.1, hok.1, hok.2, ← Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.star_conj, Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.embT_star']

theorem chiLaw_ambOf_of (hok : s.Ok) (hχ : Cd.TaylorLogMetric.IsChi D χ) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (Cd.ambOf s B χ cD : Amb X).ChiLaw a b := by
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN'
  show Cd.Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) = _ * _ * Cd.Base.chiFac χ a b (s.lat N) (s.lat N')
  rw [lat_gmap, lat_gmap]
  have h := Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.character_factor_unitary_action χ hχ (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.detSmul D) (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.norm_one_unit_ideal D) ha hb (s.lat N) (s.lat N')
    ⟨matU s γ, matU_mem s hok γ⟩ ⟨matU s γ', matU_mem s hok γ'⟩ (s.sd_lat hok hN) (s.sd_lat hok hN')
  simp only at h
  rw [h]
  have u1 := Matrix.det_of_mem_unitary (matU_mem s hok γ)
  have p1 : ∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (star (matU s γ).det) = (∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ := by
    rw [prod_emb s hok, ← Finset.prod_inv_distrib, ← det_matU]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.emb_star_unit τ _ (Unitary.mul_star_self_of_mem u1)
  have p2 : ∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (matU s γ').det = ∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) := by
    rw [prod_emb s hok, ← det_matU]
  show Cd.Base.chiFac χ a b (s.lat N) (s.lat N') * ((∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (star (matU s γ).det)) ^ (b / 2) *
      (∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (matU s γ').det) ^ (a / 2)) = _
  rw [p1, p2, inv_pow, zpow_neg, zpow_natCast, zpow_natCast, mul_comm]
  rfl

theorem chiLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : Cd.NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (Cd.ambOf s B χ cD : Amb X).ChiLaw a b :=
  chiLaw_ambOf_of s B χ cD hN.2.2.2.2.2.1 hN.2.2.2.1 ha hb

theorem eNat_analytic (hθ : AnalyticOnNhd ℂ B.thMM Set.univ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AnalyticOnNhd ℂ (B.eNat χ N N' L L') Set.univ := by
  have hT := entireStatements_holds
  have h0 : AnalyticOnNhd ℂ (B.thZero N N') Set.univ := hT.2 _ B.thMM N N' hθ
  have h1 : AnalyticOnNhd ℂ (B.thHalf N N' L) Set.univ := hT.1 _ _ _ _ _ _ _ _ h0
  have h2 : AnalyticOnNhd ℂ (B.thMoved N N' L L') Set.univ := hT.1 _ _ _ _ _ _ _ _ h1
  intro z _
  exact analyticAt_const.mul (h2 z (Set.mem_univ _))

theorem eOmega_ambOf_of (hS : B.StdOK) (a b : ℕ) : (Cd.ambOf s B χ cD : Amb X).EOmega a b := by
  intro N N' _ _
  have hA := eNat_analytic B χ (B.thMM_spec hS).1.1 a b (s.lat N) (s.lat N')
  have hc : ContDiff ℂ ⊤ (B.eNat χ a b (s.lat N) (s.lat N')) := hA.contDiff
  exact hc.comp (contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT.symm τ))

theorem eOmega_ambOf {σ₀ : X.K →+* ℂ} (hN : Cd.NatOk s cc δ χ cD σ₀) (a b : ℕ) : (Cd.ambOf s B χ cD : Amb X).EOmega a b :=
  eOmega_ambOf_of s B χ cD (B.stdOK hN.1 hN.2.1) a b

theorem eqLaw_ambOf_of (hok : s.Ok) (hE : B.EqP χ) {a b : ℕ} (ha : Even a) (hb : Even b) : (Cd.ambOf s B χ cD : Amb X).EqLaw a b := by
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN' z
  have hE1 := hE.1 a b ⟨s.lat N, s.sd_lat hok hN⟩ ⟨s.lat N', s.sd_lat hok hN'⟩ ha hb ⟨matU s γ, matU_mem s hok γ⟩ ⟨matU s γ', matU_mem s hok γ'⟩
  show B.eNat χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) (fun τ => z (s.iT.symm τ)) =
    B.eNat χ a b (s.lat N) (s.lat N') (fun τ => (Cd.ambOf s B χ cD : Amb X).pullV a b γ.1 γ'.1 z (s.iT.symm τ))
  rw [lat_gmap, lat_gmap]
  have hE' := congrFun hE1 (fun τ => z (s.iT.symm τ))
  rw [← hE']
  unfold Cd.TaylorLogMetric.pull
  congr 1
  funext τ i j
  obtain ⟨τ', rfl⟩ := s.iT.surjective τ
  simp only [Equiv.symm_apply_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold Amb.pullV
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have e1 : ∀ y : X.E, Cd.TaylorLogMetric.embT D (s.iT τ') (s.iE y) = X.embC s.σ₀ τ' y := fun y => (hok.1 τ' y).symm
  have f1 : star ((B.tor).emb (s.iT τ') (matU s γ' k i)) = X.embC s.σ₀ τ' (γ'.1.symm (Pi.single k 1) i) := by
    rw [TE.ufInv_apply, matU, Matrix.map_apply, TE.ufGL_apply']
    show star (Cd.TaylorLogMetric.embT D (s.iT τ') (s.iE _)) = _
    rw [← Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.embT_star', Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.star_conj, ← hok.2, e1]
  have f2 : (B.tor).emb (s.iT τ') (matU s γ l j) = X.embC s.σ₀ τ' (γ.1 (Pi.single j 1) l) := by
    rw [matU, Matrix.map_apply, TE.ufGL_apply']
    exact e1 _
  rw [f1, f2]
  rfl

theorem eqLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : Cd.NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (Cd.ambOf s B χ cD : Amb X).EqLaw a b :=
  eqLaw_ambOf_of s B χ cD hN.2.2.2.2.2.1 (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG.eqP_car B hN.1 hN.2.1 χ hN.2.2.2.1) ha hb

end Laws

end Formalism.L2.Ker.Cd.CarC
