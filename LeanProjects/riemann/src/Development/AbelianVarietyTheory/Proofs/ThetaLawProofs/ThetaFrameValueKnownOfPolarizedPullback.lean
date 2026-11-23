import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBOn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KnownScale

theorem val_scale {P : Out.PolAV (Sp ℂ)} {hg rig hr th hth v hv th' hth' v' hv'} {a : ℂ} (ha : a ≠ 0)
    {N : Matrix (Fin P.g) (Fin P.g) ℂ} (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i)
    (h₂ : ∀ i, IsLieComb (N i) v (v' i)) {t : ℂ} (h : Val ⟨P, hg, rig, hr, th, hth, v, hv⟩ t) :
    Val ⟨P, hg, rig, hr, th', hth', v', hv'⟩ (N.det ^ 4 / a ^ 8 * t) := by
  obtain ⟨τ, M, p, q, c, hpq, hc, ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩, rfl⟩ := h
  have := P.isAb.comm
  refine ⟨τ, N * M, p, q, a * c, hpq, mul_ne_zero ha hc, ⟨u, k₁, k₂, k₃, k₄, fun i z hz => ?_, fun i => ?_⟩, ?_⟩
  · refine ((congrArg (valAt' _ _) (h₁ i)).trans (valAt'_mul _ _ _ _)).trans ?_
    rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
    refine (congrArg (a * ·) (k₅ i z hz)).trans ?_
    simp only [_root_.mul_assoc]
  · have k := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 k₆ (h₂ i)
    have e : ∑ j, N i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (N * M) i := by
      simp only [smul_comm (N i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
      rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
      rfl
    rwa [e] at k
  · rw [Matrix.det_mul, mul_pow, mul_pow, div_mul_div_comm]

theorem det_map_cast {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') {m n : ℕ} (e : m = n)
    (M : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin m => f (M (i.cast e) (j.cast e))).det = f M.det := by
  subst e
  exact (f.map_det M).symm

theorem known_change {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'} (a : Kˣ)
    (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (h : Known K ⟨P, hg, rig, hr, th, hth, v, hv⟩) : Known K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ := by
  obtain ⟨t₀, ht₀⟩ := h
  have := P.isAb.comm
  choose N hN using fun i => (hv'.2 (v i) (hv.1 i)).exists
  have hdet : IsUnit (Matrix.of N).det :=
    ((GlobalTheory.LieComb.lieComb_algebra K P.A P.g v' hv'.1).2.2.2.2 (Matrix.of N) v hv' hN).1 hv
  have h₁' : ∀ i, LB.Sec.f th i = constFn P.A.hom _ ((a⁻¹ : Kˣ) : K) * LB.Sec.f th' i := fun i => by
    rw [h₁, ← _root_.mul_assoc, ← KeyPow.constFn_mul, Units.inv_mul, KeyPow.constFn_one, _root_.one_mul]
  refine ⟨((Matrix.of N).det)⁻¹ ^ 4 / (a : K) ^ 8 * t₀, fun e x hx => ?_⟩
  obtain ⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ := x
  obtain ⟨eg⟩ : Nonempty (Q.g = P.g) := by
    obtain ⟨_, _, _, hg, _⟩ := hx
    exact ⟨hg⟩
  have := Q.isAb.comm
  obtain ⟨ex, -, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ Q.A Q.g u hu.1
  let N' : Matrix (Fin Q.g) (Fin Q.g) ℂ := Matrix.of fun i j => e (Matrix.of N (i.cast eg) (j.cast eg))
  have hd : N'.det = e (Matrix.of N).det := det_map_cast e eg (Matrix.of N)
  choose u₀ hu₀ using fun i => (ex (N' i)).exists
  have hb₀ : IsLieBasis u₀ := (bas N' u₀ hu hu₀).2 (hd ▸ hdet.map e)
  choose M hM using fun i => (hb₀.2 (u i) (hu.1 i)).exists
  have hMN : Matrix.of M * N' = 1 := by
    funext i
    have k := (hu.2 (u i) (hu.1 i)).unique (comp _ (fun j => N' j) u₀ (M i) (u i) hu₀ (hM i)) (sgl i)
    rw [← Matrix.vecMul_eq_sum] at k
    refine k.trans ?_
    simpa using (smul_one_row (1 : ℂ) i).symm
  have hMd : (Matrix.of M).det = (e (Matrix.of N).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hd, ← Matrix.det_mul, hMN, Matrix.det_one]
  obtain ⟨s₀, e₀, e₁, hle⟩ := exists_sec_div Q.A.hom (a := e a) (b := e ((a⁻¹ : Kˣ) : K))
    (by rw [← map_mul, Units.mul_inv, map_one]) s
  have hs₀ : ∀ p : Sp ℂ, ∃ z : Q.A.left, Q.A.hom z = p ∧ z ∈ Out.nonzeroLocus s₀ :=
    fun p => (hs p).imp fun z hz => ⟨hz.1, hle hz.2⟩
  have hx₀ := KeyPBScale.keyPB_scale K ℂ e P hg rig hr th' hth' v' hv' th hth v hv _ (Matrix.of N) Q eg hgQ rigQ hrQ
    s hs u hu s₀ hs₀ u₀ hb₀ h₁' hN e₀ hu₀ hx
  have k := val_scale (hth' := hs) (hv' := hu) (N := Matrix.of M) ((map_ne_zero e).2 a.ne_zero) e₁ hM (ht₀ e _ hx₀)
  rw [hMd] at k
  rwa [map_mul, map_div₀, map_pow, map_pow, map_inv₀]

theorem known_of_keyPB {K : Type} [Field K] {y y' : KeyIn K} (h : KeyPB y' y (RingHom.id K)) (hy : Known K y) :
    Known K y' :=
  hy.imp fun _ ht e x hx => ht e x (keyPB_trans _ _ _ y y' x (RingHom.id K) e h hx)

theorem known_of_polPB : Out.Laws → ∀ (K : Type) [Field K] (y y' : KeyIn K) (φ : y'.P.A.left ⟶ y.P.A.left), PolPB y'.P y.P (𝟙 _) φ → Known K y → Known K y' := by
  intro hL K _ y y' φ ⟨h₁, h₂, h₃⟩ hy
  have e : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  obtain ⟨rig, hr, th, hth, v, hv, hz⟩ := KeyTf.exists_keyPB_on K K (RingHom.id K) y y'.P φ y'.g_pos h₂ (e ▸ h₁) h₃
  obtain ⟨a, t, ht, hta, hid⟩ := (KeyOnPol.main hL K).2 ⟨y'.P, y'.g_pos, rig, hr, th, hth, v, hv⟩
    y'.rig y'.rig_gen y'.th y'.th_ne y'.v y'.basis
  exact known_of_keyPB hid (known_change a hta (known_of_keyPB hz hy))

end GlobalTheory.KnownScale
end
