import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.CharacterFactorUnitaryAction
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section SeamU

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.matU {n : ℕ} (γ : UF X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E).map s.iE

theorem Seam.vec_gmap {n : ℕ} (γ : UF X.E n) (x : Sp X.E n) : s.vec (γ.1 x) = (s.matU γ).mulVec (s.vec x) := by
  have h := toGLm_mulVec γ.1 x
  rw [← h]
  funext i
  simp only [Seam.vec, Matrix.mulVec, dotProduct, map_sum, map_mul, Seam.matU]
  rfl

theorem Seam.lat_gmap {n : ℕ} (γ : UF X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat (gmap γ.1 N) = SDLat.smulLat (s.matU γ) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  simp only [SDLat.smulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := hx
    exact ⟨s.vec x0, (s.mem_lat N _).2 ⟨x0, hx0, rfl⟩, (s.vec_gmap γ x0).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    exact ⟨γ.1 x0, ⟨x0, hx0, rfl⟩, s.vec_gmap γ x0⟩

theorem Seam.matU_mem (hok : s.Ok) {n : ℕ} (γ : UF X.E n) :
    (letI := D.host.cmStar; s.matU γ ∈ Matrix.unitaryGroup (Fin n) D.host.E) := by
  let _ := D.host.cmStar
  have h : Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) * 1 *
      ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) = 1 := toGLm_mem_UJ γ
  rw [Matrix.mul_one] at h
  have key : star (s.matU γ) = (Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)).map s.iE := by
    ext i j
    rw [Matrix.star_apply, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj]
    simp only [Seam.matU, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    rw [hok.2]
  rw [Matrix.mem_unitaryGroup_iff', key, Seam.matU, ← Matrix.map_mul, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem Seam.det_matU {n : ℕ} (γ : UF X.E n) : (s.matU γ).det = s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) := by
  rw [← TE.det_ufGL]
  exact (RingHom.map_det s.iE.toRingHom _).symm

theorem Seam.prod_emb (hok : s.Ok) (z : X.E) : ∏ τ : X.Tau, X.embC s.σ₀ τ z = ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.iE z) :=
  Fintype.prod_equiv s.iT _ _ fun τ => hok.1 τ z

end SeamU

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem chiLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (ambOf s B χ cD : Amb X).ChiLaw a b := by
  obtain ⟨-, -, -, hχ, -, hok, -⟩ := hN
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN'
  show Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) = _ * _ * Base.chiFac χ a b (s.lat N) (s.lat N')
  rw [s.lat_gmap, s.lat_gmap]
  have h := Formalism.L2.PairingIndexBounds.Eq.character_factor_unitary_action χ hχ (Formalism.L2.PairingIndexBounds.Eq.detSmul D) (Formalism.L2.PairingIndexBounds.Eq.norm_one_unit_ideal D) ha hb (s.lat N) (s.lat N')
    ⟨s.matU γ, s.matU_mem hok γ⟩ ⟨s.matU γ', s.matU_mem hok γ'⟩ (s.sd_lat hok hN) (s.sd_lat hok hN')
  simp only at h
  rw [h]
  have u1 := Matrix.det_of_mem_unitary (s.matU_mem hok γ)
  have p1 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (s.matU γ).det) = (∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ := by
    rw [s.prod_emb hok, ← Finset.prod_inv_distrib, ← s.det_matU]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.PairingIndexBounds.Eq.emb_star_unit τ _ (Unitary.mul_star_self_of_mem u1)
  have p2 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.matU γ').det = ∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) := by
    rw [s.prod_emb hok, ← s.det_matU]
  show Base.chiFac χ a b (s.lat N) (s.lat N') * ((∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (s.matU γ).det)) ^ (b / 2) *
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.matU γ').det) ^ (a / 2)) = _
  rw [p1, p2, inv_pow, zpow_neg, zpow_natCast, zpow_natCast, mul_comm]
  rfl

end Chi

end Formalism.L2.Ker
