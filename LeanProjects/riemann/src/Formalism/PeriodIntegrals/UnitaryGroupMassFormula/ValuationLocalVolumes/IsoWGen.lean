import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Root

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem isoW_gen {a : ℕ} (Y : TupV (E := E) v n a) (z : Fin a) (γ : Fv F v)
    (hγ : γ ∈ v.adicCompletionIntegers F) (hγm : Valued.v γ < 1)
    (hz : ∀ i, gramR (Fv F v) σ J Y i z = if i = z then sc (E := E) v γ else 0)
    (hPD : PrimDual σ J ψ v Λ a)
    (hTS : ∃ S : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E), (∀ i j, S i j ∈ OEv (E := E) v) ∧
      bordM v (gramR (Fv F v) σ J Y) z * S = 1) :
    IsoW σ J ψ v Λ a Y := by
  classical
  intro hG
  obtain ⟨hS, hL, hSD, hUn, -, hYp⟩ := hG
  have hcm := hS.1
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  have hconj : ∀ x y, sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x :=
    fun x y => PI.OmLocU.Orb.hR_conj σ J v hcm hJ x y
  have hsc : ∀ r : Fv F v, sigR (Fv F v) σ (sc (E := E) v r) = sc (E := E) v r :=
    fun r => PI.OmLocU.NormOneUnitFixedPoints.sigR_sc' σ v r
  set G := gramR (Fv F v) σ J Y with hGdef

  obtain ⟨S, hSi, hTS1⟩ := hTS
  have hGi : ∀ i j, G i j ∈ OEv (E := E) v := fun i j =>
    PI.OmLocU.hR_mem_oEv σ J v Λ hSD (hYp.1 i) (hYp.1 j)
  have hBi : ∀ i j, bordM v G z i j ∈ OEv (E := E) v := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [bordM, Fin.snoc_last]; exact oEv_zero v
      | cast j =>
        simp only [bordM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [bordM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
      | cast j => simp only [bordM, Fin.snoc_castSucc]; exact hGi i j
  refine ⟨bordM v G z, ⟨S.det, det_int v _ hSi, det_int v _ hBi, ?_⟩, ?_⟩
  · rw [← Matrix.det_mul, hTS1, Matrix.det_one]
  intro X hX hXY
  obtain ⟨W, hW, hWd⟩ := hPD hS hSD hUn hL X hX
  set g := sc (E := E) v γ with hg
  have hgO : g ∈ OEv (E := E) v := PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hγ
  have hXz : ∀ i, hR (Fv F v) σ J (X i) (X z) = if i = z then g else 0 := by
    intro i
    have := congrFun (congrFun hXY i) z
    simp only [gramR] at this
    rw [this]; exact hz i
  set w0 := W z with hw0
  have hw0L : w0 ∈ latLoc (E := E) v Λ := hW z
  have hXw0 : ∀ i, hR (Fv F v) σ J (X i) w0 = if i = z then 1 else 0 := fun i => (hWd i z).1
  have hw0X : ∀ i, hR (Fv F v) σ J w0 (X i) = if i = z then 1 else 0 := fun i => (hWd i z).2
  set y := X z + (-g) • w0 with hy
  have hyL : y ∈ latLoc (E := E) v Λ :=
    Submodule.add_mem _ (hX.1 z) (PI.OmLocU.Orb.oSmul v Λ hL _ (oEv_neg v hgO) _ hw0L)
  have hXy : ∀ i, hR (Fv F v) σ J (X i) y = 0 := by
    intro i
    rw [hy, hAddR, hSmulR, hXz, hXw0]
    split_ifs <;> ring
  have hyX : ∀ i, hR (Fv F v) σ J y (X i) = 0 := by
    intro i; rw [← hconj, hXy, map_zero]
  set b := hR (Fv F v) σ J w0 w0 with hb
  have hbO : b ∈ OEv (E := E) v := PI.OmLocU.hR_mem_oEv σ J v Λ hSD hw0L hw0L
  obtain ⟨β, hβ, hbβ⟩ := PI.OmLocU.NormOneUnitFixedPoints.fix_int_sc σ v hcm hbO (hconj w0 w0)
  have h1 : hR (Fv F v) σ J w0 y = 1 + (-g) * b := by
    rw [hy, hAddR, hSmulR, hw0X, if_pos rfl]
  have h2 : hR (Fv F v) σ J y w0 = 1 + (-g) * b := by
    rw [← hconj, h1, map_add, map_one, map_mul, map_neg, hg, hsc, hconj]
  have h3 : hR (Fv F v) σ J y y = (-g) * (1 + (-g) * b) := by
    rw [hy, hAddR, hSmulR, ← hy, hyX, h2, zero_add]

  obtain ⟨θ, hθO, hθ⟩ := PI.OmLocU.Red.trOnto_holds σ J ψ v hS hUn 1 (oEv_one v) (map_one _)
  have hinv : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := PI.OmLocU.Orb.sigR_invol σ v hcm
  have hNO : sigR (Fv F v) σ θ * θ ∈ OEv (E := E) v := by
    refine oEv_mul v ?_ hθO
    have := hθ ▸ (oEv_one (E := E) v)
    have e : sigR (Fv F v) σ θ = (θ + sigR (Fv F v) σ θ) - θ := by ring
    rw [e]
    exact oEv_add v this (oEv_neg v hθO)
  have hNf : sigR (Fv F v) σ (sigR (Fv F v) σ θ * θ) = sigR (Fv F v) σ θ * θ := by
    rw [map_mul, hinv, mul_comm]
  obtain ⟨ν, hν, hNν⟩ := PI.OmLocU.NormOneUnitFixedPoints.fix_int_sc σ v hcm hNO hNf
  obtain ⟨s, hsO, hs⟩ := exists_integral_root_of_quadratic v β γ ν hβ hγ hγm hν
  set t := sc (E := E) v s * θ with ht
  have htO : t ∈ OEv (E := E) v := oEv_mul v (PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hsO) hθO
  have hσt : sigR (Fv F v) σ t = sc (E := E) v s * sigR (Fv F v) σ θ := by
    rw [ht, map_mul, hsc]
  set w := w0 + t • y with hw
  have hwL : w ∈ latLoc (E := E) v Λ :=
    Submodule.add_mem _ hw0L (PI.OmLocU.Orb.oSmul v Λ hL _ htO _ hyL)
  have hXw : ∀ i, hR (Fv F v) σ J (X i) w = if i = z then 1 else 0 := by
    intro i; rw [hw, hAddR, hSmulR, hXy, hXw0, mul_zero, add_zero]
  have hwX : ∀ i, hR (Fv F v) σ J w (X i) = if i = z then 1 else 0 := by
    intro i; rw [hw, hAddL, hSmulL, hyX, hw0X, mul_zero, add_zero]
  have E0 : hR (Fv F v) σ J w w = b + t * hR (Fv F v) σ J w0 y +
      (sigR (Fv F v) σ t * hR (Fv F v) σ J y w0 + sigR (Fv F v) σ t * (t * hR (Fv F v) σ J y y)) := by
    rw [hw, hAddL, hAddR, hAddR, hSmulR, hSmulL, hSmulL, hSmulR]
  have key : sc (E := E) v (β + (1 - γ * β) * s - γ * (1 - γ * β) * ν * s ^ 2) = 0 := by
    rw [hs]; simp [sc]
  have keyE : sc (E := E) v β + (1 - g * sc (E := E) v β) * sc (E := E) v s -
      g * (1 - g * sc (E := E) v β) * sc (E := E) v ν * sc (E := E) v s ^ 2 = 0 := by
    rw [← key, hg]
    simp only [PI.OmLocU.NormOneUnitFixedPoints.sc_eq, map_add, map_sub, map_mul, map_one, map_pow]
  have hww : hR (Fv F v) σ J w w = 0 := by
    rw [E0, h1, h2, h3, hσt, hbβ, ht]
    linear_combination keyE + ((1 - g * sc (E := E) v β) * sc (E := E) v s) * hθ -
      (g * (1 - g * sc (E := E) v β) * sc (E := E) v s ^ 2) * hNν
  refine ⟨w, hwL, ?_⟩
  rw [gram_augT σ J v X w z hXw hwX hww, hXY]

end PI.OmVf
