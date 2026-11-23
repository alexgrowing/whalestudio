import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairTermEqPointSumAnyTrivialisationStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.RelMove

section Generic

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

theorem triv_move (σ : S →+* Sᵐᵒᵖ) (b : S) (x Y : Sˣ) (t s : A)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t) :
    ((x * Y⁻¹ : Sˣ) : S) * (algebraMap A S s * ((Y : S) * b * (σ Y).unop)) * (σ ((x * Y⁻¹ : Sˣ) : S)).unop =
      algebraMap A S (s * t) := by
  have h1 : (σ Y).unop * (σ ((Y⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * Y⁻¹ : Sˣ) : S) * (algebraMap A S s * ((Y : S) * b * (σ Y).unop)) * (σ ((x * Y⁻¹ : Sˣ) : S)).unop
      = s • ((x : S) * ((((Y⁻¹ : Sˣ) : S) * Y) * b * ((σ Y).unop * (σ ((Y⁻¹ : Sˣ) : S)).unop)) * (σ x).unop) := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, ← Algebra.smul_def, mul_smul_comm,
          smul_mul_assoc, mul_assoc]
    _ = algebraMap A S (s * t) := by
        rw [Units.inv_mul, h1, one_mul, mul_one, hx, map_mul, Algebra.smul_def]

end Generic

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_units (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul, Units.inv_mul]; simp [sh]

theorem key (y v : G.Cˣ) (β : G.C) (s : ℚ) :
    ((y * v * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * v * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C s * (y * ((v : G.C) * β * sh G v) * sh G y) := by
  calc ((y * v * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * v * y⁻¹ : G.Cˣ) : G.C)
      = s • ((y : G.C) * v * (((y⁻¹ : G.Cˣ) : G.C) * y) * β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) *
          sh G v * sh G y) := by
        simp only [Units.val_mul, sh_mul, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, sh_units, mul_one, mul_one, Algebra.smul_def]; simp only [mul_assoc]

theorem scal (y : G.Cˣ) (β : G.C) (s u : ℚ) :
    algebraMap ℚ G.C u * (algebraMap ℚ G.C s * (y * β * sh G y)) =
      algebraMap ℚ G.C s * (y * (algebraMap ℚ G.C u * β) * sh G y) := by
  simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm u s]

theorem cancel (y : G.Cˣ) (X Z : G.C) (s : ℚ) (hs : s ≠ 0)
    (h : algebraMap ℚ G.C s * (y * X * sh G y) = algebraMap ℚ G.C s * (y * Z * sh G y)) : X = Z := by
  have h' : (y : G.C) * X * sh G y = y * Z * sh G y := by
    have := congrArg (fun w => algebraMap ℚ G.C s⁻¹ * w) h
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul] using this
  have e : ∀ W : G.C, W = ((y⁻¹ : G.Cˣ) : G.C) * (y * W * sh G y) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
    intro W
    rw [mul_assoc, mul_assoc, sh_units, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
  rw [e X, e Z, h']

def cj (y : G.Cˣ) : G.Cˣ × ℚˣ ≃* G.Cˣ × ℚˣ := (MulAut.conj y).prodCongr (MulEquiv.refl ℚˣ)

theorem cj_apply (y : G.Cˣ) (v : G.Cˣ × ℚˣ) : cj y v = (y * v.1 * y⁻¹, v.2) := rfl

theorem mem_of (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) (v : G.Cˣ × ℚˣ) (hv : v ∈ P.cent) : cj y v ∈ Q.cent := by
  obtain ⟨h1, h2⟩ := hv
  change v.1 * P.γ = P.γ * v.1 at h1
  change (v.1 : G.C) * P.β * sh G v.1 = algebraMap ℚ G.C v.2 * P.β at h2
  refine ⟨?_, ?_⟩
  · change y * v.1 * y⁻¹ * Q.γ = Q.γ * (y * v.1 * y⁻¹)
    rw [hγ]
    calc y * v.1 * y⁻¹ * (y * P.γ * y⁻¹) = y * (v.1 * P.γ) * y⁻¹ := by group
      _ = y * (P.γ * v.1) * y⁻¹ := by rw [h1]
      _ = _ := by group
  · change ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) * Q.β * sh G ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C v.2 * Q.β
    rw [hβ, key, h2, scal]

theorem mem_back (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) (w : G.Cˣ × ℚˣ) (hw : w ∈ Q.cent) : (cj y).symm w ∈ P.cent := by
  obtain ⟨h1, h2⟩ := hw
  set v := (cj y).symm w with hv
  have hw' : w = cj y v := by rw [hv, MulEquiv.apply_symm_apply]
  rw [hw', cj_apply] at h1 h2
  change y * v.1 * y⁻¹ * Q.γ = Q.γ * (y * v.1 * y⁻¹) at h1
  change ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) * Q.β * sh G ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C v.2 * Q.β at h2
  refine ⟨?_, ?_⟩
  · change v.1 * P.γ = P.γ * v.1
    rw [hγ] at h1
    have : y * (v.1 * P.γ) * y⁻¹ = y * (P.γ * v.1) * y⁻¹ := by
      calc y * (v.1 * P.γ) * y⁻¹ = y * v.1 * y⁻¹ * (y * P.γ * y⁻¹) := by group
        _ = (y * P.γ * y⁻¹) * (y * v.1 * y⁻¹) := h1
        _ = _ := by group
    simpa using this
  · change (v.1 : G.C) * P.β * sh G v.1 = algebraMap ℚ G.C v.2 * P.β
    rw [hβ, key, scal] at h2
    exact cancel y _ _ s hs h2

theorem cent_map (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) : P.cent.map (cj y).toMonoidHom = Q.cent := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mem_of P Q y s hβ hγ v hv
  · intro hw
    exact ⟨(cj y).symm w, mem_back P Q y s hs hβ hγ w hw, by simp⟩

theorem toAf_val (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (v : P.cent) :
    ((P.toAf x t hx v : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      (x * Units.map (inC G (AfP p)).toMonoidHom v.1.1 * x⁻¹, Units.map (algebraMap ℚ (AfP p)).toMonoidHom v.1.2) :=
  rfl

theorem toQr_val (P : Pair G) (r : ℕ) (z : Gr G r) (v : P.cent) :
    P.toQr r z v = z⁻¹ * inclG G r (locC G v.1) * z := by
  simp [Pair.toQr, carry, MulAut.conj_apply]

theorem locC_conj (y : G.Cˣ) (v : G.Cˣ × ℚˣ) :
    locC G (y * v.1 * y⁻¹, v.2) = locC G (y, 1) * locC G v * (locC G (y, 1))⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem triv_rel (P Q : Pair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) :
    Triv G (AfP p) Q.β (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 s hs) * t) := by
  have e1 : inC G (AfP p) (sh G y) = (starT G.star (AfP p) (inC G (AfP p) y)).unop :=
    (starT_tmul G.star (AfP p) 1 _).symm
  have e2 : inC G (AfP p) (algebraMap ℚ G.C s) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) s) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
  unfold Triv
  rw [hβ, map_mul, map_mul, map_mul, e1, e2]
  have := triv_move (starT G.star (AfP p)) (inC G (AfP p) P.β) x (Units.map (inC G (AfP p)).toMonoidHom y)
    (t : AfP p) (algebraMap ℚ (AfP p) s) hx
  simpa [mul_assoc] using this

end GlobalTheory.LKMid.RelMove

namespace GlobalTheory.LKMid.Pair

open GlobalTheory.LKMid.RelMove in

theorem term_eq_of_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
    (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
    P.Rel Q → Q.term Kf f r K φ = P.term Kf f r K φ := by
  intro p _ G P Q Kf f r K φ hr hf hφ hPQ
  obtain ⟨y, s, hs, hβ, hγ⟩ := hPQ
  have hc : Q.c = P.c := (GlobalTheory.T.related_pairs_same_polarization p G P Q ⟨y, s, hs, hβ, hγ⟩).2
  have hat : Q.atP = locC G (y, 1) * P.atP * (locC G (y, 1))⁻¹ := by
    have := locC_conj y (P.γ, P.c)
    simp only [Pair.atP, hγ, hc]
    exact this
  have hnrm : ∀ δ z, IsNrm G r P.atP δ z → IsNrm G r Q.atP δ (inclG G r (locC G (y, 1)) * z) := by
    intro δ z h
    unfold IsNrm at h ⊢
    rw [h, hat, map_mul, map_mul, map_inv]
    group
  by_cases hP : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2
  · obtain ⟨⟨δ, z⟩, hδ⟩ := hP
    obtain ⟨x, t, hx⟩ := P.trivAf
    have hx' := triv_rel P Q y s hs.ne' hβ x t hx
    rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f r K φ hr hf hφ x t hx δ z hδ,
      GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G Q Kf f r K φ hr hf hφ _ _ hx' δ _ (hnrm δ z hδ)]
    let e : P.cent ≃* Q.cent := ((cj y).subgroupMap P.cent).trans
      (MulEquiv.subgroupCongr (cent_map P Q y s hs.ne' hβ hγ))
    have he : ∀ v : P.cent, ((e v : Q.cent) : G.Cˣ × ℚˣ) = cj y v := fun v => rfl
    have hA : (Q.toAf _ _ hx').comp e.toMonoidHom = P.toAf x t hx := by
      ext v : 1
      apply Subtype.ext
      rw [MonoidHom.comp_apply, toAf_val, toAf_val]
      simp only [MulEquiv.coe_toMonoidHom, he, cj_apply]
      refine Prod.ext ?_ rfl
      simp only [map_mul, map_inv]
      group
    have hQr : (Q.toQr r (inclG G r (locC G (y, 1)) * z)).comp e.toMonoidHom = P.toQr r z := by
      ext v : 1
      rw [MonoidHom.comp_apply, toQr_val, toQr_val]
      simp only [MulEquiv.coe_toMonoidHom, he, cj_apply]
      rw [locC_conj, map_mul, map_mul, map_inv]
      group
    have hS : Q.self = e P.self := by
      apply Subtype.ext
      rw [he, cj_apply]
      exact Prod.ext hγ hc
    unfold termAt
    have hS' : Q.toAf _ _ hx' (e P.self) = P.toAf x t hx P.self := by rw [← hA]; rfl
    rw [hS, ← GlobalTheory.T.kottwitzIsogenyClassPointSum_comp_mulEquiv e, hS', hA, hQr]
  · have hQ : ¬ ∃ dz : Gr G r × Gr G r, IsNrm G r Q.atP dz.1 dz.2 := by
      rintro ⟨⟨δ, z⟩, h⟩
      apply hP
      refine ⟨(δ, (inclG G r (locC G (y, 1)))⁻¹ * z), ?_⟩
      unfold IsNrm at h ⊢
      rw [h, hat, map_mul, map_mul, map_inv]
      group
    unfold term
    rw [dif_neg hP, dif_neg hQ]

end GlobalTheory.LKMid.Pair
