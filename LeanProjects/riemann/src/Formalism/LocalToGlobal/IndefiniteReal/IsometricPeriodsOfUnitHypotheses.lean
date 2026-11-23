import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfHypotheses

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def MIUnit2 (d : X.MIDat fc) : Prop :=
  (∀ e ∈ X.EEl true, d.V e ∈ X.EEl true ∧ ‖d.V e‖ = ‖e‖) ∧
    (∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((d.U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x) ∧
    ((∀ u t, d.ζC u t ≠ 0) ∧ ∀ u w (k : K), Bs.v0.embedding k = d.ζC u (X.μ w) → vw w k = 0) ∧
    ∀ u, d.ζC u Bs.μ0 = 1

def MIstar2 (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) : Prop :=
  ∃ d : X.MIDat fc, X.MIUnit2 d ∧ X.MIid eV sEE d ∧ X.AuNZ d

theorem vw_eq_zero_of_pow {k : K} {n : ℕ} (hn : 0 < n) (hk : k ^ n = 1) (w : HeightOneSpectrum (𝓞 K)) : vw w k = 0 := by
  have h1 : (n : ℤ) * vw w k = 0 := by
    unfold vw
    rw [← FractionalIdeal.count_pow]
    first
    | rw [FractionalIdeal.spanSingleton_pow]
    | rw [← FractionalIdeal.spanSingleton_pow]
    rw [hk, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h (by exact_mod_cast hn.ne')
  · exact h

theorem zetaOK_of_miUnit2 {d : X.MIDat fc} (hU : X.MIUnit2 d) : X.ZetaOK (X.zetaOf d) := by
  refine ⟨fun u => ?_, fun u t => ?_, fun u w => ?_⟩
  · have h : ∃ k : K, Bs.v0.embedding k = d.ζC u Bs.μ0 := ⟨1, by rw [map_one, hU.2.2.2 u]⟩
    apply Bs.v0.embedding.injective
    rw [X.zetaOf_spec u Bs.μ0 h, hU.2.2.2 u, map_one]
  · by_cases h : ∃ k : K, Bs.v0.embedding k = d.ζC u t
    · intro h0
      have h' := X.zetaOf_spec u t h
      rw [h0, map_zero] at h'
      exact hU.2.2.1.1 u t h'.symm
    · rw [X.zetaOf_not u t h]
      exact one_ne_zero
  · by_cases h : ∃ k : K, Bs.v0.embedding k = d.ζC u (X.μ w)
    · exact hU.2.2.1.2 u w _ (X.zetaOf_spec u (X.μ w) h)
    · rw [X.zetaOf_not u (X.μ w) h]
      exact vw_eq_zero_of_pow one_pos (one_pow 1) w

section Ident2

variable {eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH} {d : X.MIDat fc}

theorem embedding_pairing_eq_mul_inner (hW : (fc X.zs).Df1.WF) (hJ : X.JIsoR cv) (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true)
    (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true) (hE : X.EVTie cr cv eV) (hU : X.MIUnit2 d)
    (hI : X.MIid eV sEE d) (u : (fc X.zs).Dc.Mem) (φ : Fin ((fc X.zs).Dc.a u) → K)
    (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → K) :
    Bs.v0.embedding (X.Bdef u φ y) =
      d.a u * ⟪sEE (d.V (X.iC cr true Bs.μ0 (cpt Bs.v0.embedding y))),
        (fc X.zs).Sp.Pu u ((d.U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ := by
  have h1 := hI u Bs.μ0 φ ((rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec y)
  rw [hU.2.2.2 u, one_mul, X.theta_eV cr cv eV hJ hRL hDn hUp hC hE] at h1
  have h3 : ((fc X.zs).Df1.Pq Bs.μ0).mulVec ((rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec y) = y :=
    mulVec_rinv _ (hW.Pq_surj Bs.μ0) y
  rw [h3] at h1
  rw [X.iC_cpt' cr true Bs.μ0 y]
  exact h1

theorem zetaC_mul_embedding_Pt (hW : (fc X.zs).Df1.WF) (h2 : X.H2 cr true) (hr : X.RATmu cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hU : X.MIUnit2 d) (hI : X.MIid eV sEE d) (u : (fc X.zs).Dc.Mem) (t : Bs.Tup)
    (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K) :
    d.ζC u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) =
      Bs.v0.embedding (X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))) := by
  rw [X.embedding_pairing_eq_mul_inner cr cv hW hJ hRL hDn hUp hC hE hU hI, hI u t φ F, X.theta_eV cr cv eV hJ hRL hDn hUp hC hE]
  have hx : X.iC cr true Bs.μ0 (cpt Bs.v0.embedding ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))) =
      X.Θ t (X.jR t (cr.toR X.zs true t (((fc X.zs).Df1.Pq t).mulVec F))) :=
    (X.key_row cr true h2 hr t _).trans (X.iC_cpt' cr true t _)
  rw [hx]

theorem base_tuple_vanishing_of_hypotheses (hJ : X.JIsoR cv) (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true)
    (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true) (hE : X.EVTie cr cv eV) (hU : X.MIUnit2 d)
    (hI : X.MIid eV sEE d) : X.BtVanish (fc := fc) := by
  intro u φ F hF
  have hP : ((fc X.zs).Df1.Pq Bs.μ0).mulVec F = 0 := LinearMap.mem_ker.1 hF
  have h1 := hI u Bs.μ0 φ F
  have h0 : cr.toR X.zs true Bs.μ0 (((fc X.zs).Df1.Pq Bs.μ0).mulVec F) = 0 := by
    rw [hP]; exact map_zero _
  rw [hU.2.2.2 u, one_mul, X.theta_eV cr cv eV hJ hRL hDn hUp hC hE, h0] at h1
  simp only [map_zero, inner_zero_left, mul_zero] at h1
  exact (map_eq_zero Bs.v0.embedding).1 h1

theorem matrix_identity_of_unit_hypotheses (hW : (fc X.zs).Df1.WF) (h2 : X.H2 cr true) (hr : X.RATmu cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hU : X.MIUnit2 d) (hI : X.MIid eV sEE d) : X.MatrixIdentityOffBase cr (X.zetaOf d) := by
  intro u t _ φ F
  have hk := X.zetaC_mul_embedding_Pt cr cv hW h2 hr hJ hRL hDn hUp hC hE hU hI u t φ F
  by_cases h : ∃ k : K, Bs.v0.embedding k = d.ζC u t
  · apply Bs.v0.embedding.injective
    rw [map_mul, X.zetaOf_spec u t h, hk]
  · have hP : (fc X.zs).Dc.Pt u t φ F = 0 := by
      by_contra hP
      apply h
      refine ⟨X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F)) /
        (fc X.zs).Dc.Pt u t φ F, ?_⟩
      rw [map_div₀, ← hk, mul_div_assoc, div_self ((map_ne_zero _).2 hP), mul_one]
    rw [hP, map_zero, mul_zero] at hk
    rw [hP, mul_zero]
    exact ((map_eq_zero _).1 hk.symm).symm

theorem isometric_periods_of_unit_hypotheses (hW : (fc X.zs).Df1.WF) (hpos : X.H4pos) (h2 : X.H2 cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hS : X.SEEIso sEE) (hU : X.MIUnit2 d) (hI : X.MIid eV sEE d) (hA : X.AuNZ d)
    (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) : (X.colOf cr (X.colDef ζ sEE)).L1e := by
  have hn : 0 < X.nP true := hpos.2.2 true
  have hli : LinearIndependent ℂ (fun i => X.iC cr true Bs.μ0 (Pi.single i 1)) :=
    li_of_lin_injective (by rw [lin_basis]; exact h2.1)
  have hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true) :=
    (rowXE_spec (Df := lv (fc X.zs) true) hW _ (X.gramE_unit cr true h2 hn) X.κ hpos.1
      (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hpos.2.1 j Bs.μ0 p v)).2.1
  have hfn : ∀ y, fnorm (X.XE cr true Bs.v0) y = Real.sqrt (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 y‖ := by
    intro y
    rw [hXE, gramE, fnorm_gram_smul _ hli _ (inv_pos.mpr hn), lin_basis]
  have hmem : ∀ y, X.iC cr true Bs.μ0 y ∈ X.EEl true := fun y => h2.2.2 ▸ LinearMap.mem_range_self _ y
  have hsn : ∀ e ∈ X.EEl true, ‖sEE e‖ = Real.sqrt (X.nP true)⁻¹ * ‖e‖ := by
    intro e he
    have h3 : ‖sEE e‖ ^ 2 = (X.nP true)⁻¹ * ‖e‖ ^ 2 := by
      rw [← hS.1 e he, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
    rw [← Real.sqrt_sq (norm_nonneg (sEE e)), h3, Real.sqrt_mul (inv_pos.mpr hn).le, Real.sqrt_sq (norm_nonneg e)]
  have hex : ∀ y, ∃ y', X.iC cr true Bs.μ0 y' = d.V (X.iC cr true Bs.μ0 y) := by
    intro y
    have h4 := (hU.1 _ (hmem y)).1
    rw [← h2.2.2] at h4
    exact LinearMap.mem_range.1 h4
  choose w hw using hex
  let W : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) →ₗ[ℂ] (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) :=
    { toFun := w
      map_add' := fun x y => h2.1 (by simp only [hw, map_add])
      map_smul' := fun c y => h2.1 (by simp only [hw, map_smul, RingHom.id_apply]) }
  have hWy : ∀ y, (LinearMap.toMatrix' W).mulVec y = w y := fun y => LinearMap.toMatrix'_mulVec W y
  refine ⟨fun (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) => ?_, fun y => ?_, ?_, LinearMap.toMatrix' W,
    fun (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) => ?_,
    fun u => ⟨d.a u, hA u, d.U u, hU.2.1 u, fun x (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) => ?_⟩⟩
  · exact (hsn _ (hmem y)).trans (hfn y).symm
  · exact hS.2.1 _ (hmem y)
  · show Module.finrank ℂ (fc X.zs).Sp.Rw = (lv (fc X.zs) true).dQ Bs.μ0
    rw [hS.2.2, ← h2.2.2, LinearMap.finrank_range_of_inj h2.1, Module.finrank_fin_fun]
  · have e1 : fnorm (X.XE cr true Bs.v0) ((LinearMap.toMatrix' W).mulVec y) = fnorm (X.XE cr true Bs.v0) (w y) :=
      congrArg _ (hWy y)
    refine e1.trans ((hfn _).trans ?_)
    rw [hw, (hU.1 _ (hmem y)).2]
    exact (hfn y).symm
  · show pairC Bs.v0 (X.Bdef u) x y =
      d.a u * ⟪sEE (X.iC cr true Bs.μ0 ((LinearMap.toMatrix' W).mulVec y)), (fc X.zs).Sp.Pu u ((d.U u).mulVec x)⟫_ℂ
    rw [hWy, hw]
    let Φ : (Fin ((fc X.zs).Dc.a u) → ℂ) →ₗ[ℂ] (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ
        (fun x y => d.a u * ⟪sEE (d.V (X.iC cr true Bs.μ0 y)), (fc X.zs).Sp.Pu u ((d.U u).mulVec x)⟫_ℂ)
        (fun x x' y => by simp only [Matrix.mulVec_add, map_add, inner_add_right, mul_add])
        (fun c x y => by simp only [Matrix.mulVec_smul, map_smul, inner_smul_right, smul_eq_mul]; ring)
        (fun x y y' => by simp only [map_add, inner_add_left, mul_add])
        (fun c x y => by
          simp only [map_smul, LinearMap.map_smulₛₗ, inner_smul_left, smul_eq_mul, starRingEnd_self_apply]; ring)
    have hΦ : d.a u * ⟪sEE (d.V (X.iC cr true Bs.μ0 y)), (fc X.zs).Sp.Pu u ((d.U u).mulVec x)⟫_ℂ = Φ x y := rfl
    rw [hΦ, bil_expand Φ x y, pairC]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have hik : Φ (Pi.single i 1) (Pi.single k 1) = Bs.v0.embedding (X.Bdef u (Pi.single i 1) (Pi.single k 1)) := by
      rw [X.embedding_pairing_eq_mul_inner cr cv hW hJ hRL hDn hUp hC hE hU hI, cpt_single, cpt_single]
      rfl
    rw [hik]

end Ident2

theorem btVanish_of_miStar2 (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (hW : (fc X.zs).Df1.WF) (hpos : X.H4pos) (h2 : X.H2 cr true) (hr : X.RATmu cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hS : X.SEEIso sEE) (hM : X.MIstar2 eV sEE) :
    X.BtVanish (fc := fc) ∧ ∃ ζ : (fc X.zs).Dc.Mem → Bs.Tup → K, X.MatrixIdentityOffBase cr ζ ∧ X.ZetaOK ζ ∧
      (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e := by
  obtain ⟨d, hU, hI, hA⟩ := hM
  exact ⟨X.base_tuple_vanishing_of_hypotheses cr cv hJ hRL hDn hUp hC hE hU hI, X.zetaOf d,
    X.matrix_identity_of_unit_hypotheses cr cv hW h2 hr hJ hRL hDn hUp hC hE hU hI, X.zetaOK_of_miUnit2 hU,
    X.isometric_periods_of_unit_hypotheses cr cv hW hpos h2 hJ hRL hDn hUp hC hE hS hU hI hA _⟩

theorem exists_zeta_pairing_factors_through_periods (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (hW : (fc X.zs).Df1.WF) (hpos : X.H4pos) (h2 : X.H2 cr true) (hr : X.RATmu cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hS : X.SEEIso sEE) (hM : X.MIstar2 eV sEE) :
    ∃ ζ : (fc X.zs).Dc.Mem → Bs.Tup → K, (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).PairingFactorsThroughPeriods ∧
      (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e := by
  obtain ⟨hBt, ζ, hMI, hZ, hL⟩ := X.btVanish_of_miStar2 cr cv eV sEE hW hpos h2 hr hJ hRL hDn hUp hC hE hS hM
  exact ⟨ζ, X.cutPairing cr ζ sEE hW h2 hBt hMI hZ, hL⟩

end CxData

end Formalism.IndefR.Cx
