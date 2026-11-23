import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairTermEqPointSumAnyTrivialisationStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDefTerm

theorem pointSum_equiv {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ ≃* Γ')
    (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (ι₁' : Γ' →* G₁) (ι₂' : Γ' →* G₂) (h₁ : ∀ y, ι₁' (e y) = ι₁ y)
    (h₂ : ∀ y, ι₂' (e y) = ι₂ y) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f : G₁ → ℂ) (φ : G₂ → ℂ) :
    pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ = pointSum ι₁' ι₂' θ K₁ K₂ γ δ f φ := by
  have e₁ : ι₁ = ι₁'.comp e.toMonoidHom := MonoidHom.ext fun y => (h₁ y).symm
  have e₂ : ι₂ = ι₂'.comp e.toMonoidHom := MonoidHom.ext fun y => (h₂ y).symm
  subst e₁ e₂
  have hr : ((ι₁'.comp e.toMonoidHom).prod (ι₂'.comp e.toMonoidHom)).range = (ι₁'.prod ι₂').range := by
    ext g
    simp only [MonoidHom.mem_range, MonoidHom.prod_apply, MonoidHom.comp_apply]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨e y, hy⟩
    · rintro ⟨y, hy⟩; exact ⟨e.symm y, by simpa using hy⟩
  have hc : ∀ x : G₁ × G₂, Nat.card (stab (ι₁'.comp e.toMonoidHom) (ι₂'.comp e.toMonoidHom) K₁ K₂ x) =
      Nat.card (stab ι₁' ι₂' K₁ K₂ x) := by
    intro x
    have : stab (ι₁'.comp e.toMonoidHom) (ι₂'.comp e.toMonoidHom) K₁ K₂ x =
        (stab ι₁' ι₂' K₁ K₂ x).comap e.toMonoidHom := by
      simp only [stab, Subgroup.comap_inf, Subgroup.comap_comap]
    rw [this]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv fun a => Iff.rfl)
  unfold pointSum
  simp only [hc]
  rw [hr]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem quot_commute (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) :
    ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (P.γ : G.C) = (P.γ : G.C) * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) := by
  have hP := P.sim
  have hQ := Q.sim
  rw [hγ, hc] at hP
  rw [hγ]
  set γ := Q.γ
  set c := Q.c
  set b₁ := P.β
  set b₂ := Q.β
  set C := algebraMap ℚ G.C (c : ℚ)
  have hs : sh G (γ : G.C) = ((b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (C * b₂) := by
    rw [← hQ]; simp only [← mul_assoc, Units.inv_mul_cancel_left]
    rw [mul_assoc ((b₂⁻¹ : G.Cˣ) : G.C), Units.inv_mul, mul_one, Units.inv_mul, one_mul]
  have hCu : IsUnit C := c.isUnit.map (algebraMap ℚ G.C)
  have h := congrArg (· * ((b₂⁻¹ : G.Cˣ) : G.C)) hP
  rw [hs] at h
  have key : C * ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) =
      C * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) := by
    calc C * ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C))
        = ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * C := Algebra.commutes _ _
      _ = (γ : G.C) * b₁ * (((b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (C * b₂)) *
            ((b₂⁻¹ : G.Cˣ) : G.C) := by
          simp only [Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = C * b₁ * ((b₂⁻¹ : G.Cˣ) : G.C) := h
      _ = _ := by simp only [Units.val_mul, mul_assoc]
  have k2 := hCu.mul_left_cancel key
  calc ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * (γ : G.C)
      = ((γ : G.C) * ((b₁ * b₂⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * γ := by rw [k2]
    _ = _ := by simp only [mul_assoc, Units.inv_mul, mul_one]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem commute_quot (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) (y : G.C)
    (hy : y * (P.γ : G.C) = (P.γ : G.C) * y) :
    y * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * y := by
  obtain ⟨w, hw⟩ := (GlobalTheory.LKCentAf.cent_iff_mem P _).1 (quot_commute P Q hγ hc)
  have hb : ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) ∈ Algebra.adjoin G.F ({(P.γ : G.C)} : Set G.C) := by
    rw [← hw]; exact w.2
  exact Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun z hz => by
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hy

theorem cent_eq (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) : P.cent = Q.cent := by
  ext ⟨y, s⟩
  change (y * P.γ = P.γ * y ∧ (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β) ↔
    (y * Q.γ = Q.γ * y ∧ (y : G.C) * Q.β * sh G y = algebraMap ℚ G.C s * Q.β)
  rw [← hγ]
  refine and_congr_right fun h1 => ?_
  have hy : (y : G.C) * (P.γ : G.C) = (P.γ : G.C) * y := by rw [← Units.val_mul, h1, Units.val_mul]
  have hcomm := commute_quot P Q hγ hc y hy
  set b : G.Cˣ := P.β * Q.β⁻¹
  have hβ : (P.β : G.C) = (b : G.C) * Q.β := by simp [b, mul_assoc]
  rw [hβ]
  have e1 : (y : G.C) * (b * Q.β) * sh G y = b * ((y : G.C) * Q.β * sh G y) := by
    rw [← mul_assoc (y : G.C), hcomm]; simp only [mul_assoc]
  have e2 : algebraMap ℚ G.C s * ((b : G.C) * Q.β) = b * (algebraMap ℚ G.C s * Q.β) := by
    rw [← mul_assoc, Algebra.commutes, mul_assoc]
  rw [e1, e2]
  constructor
  · intro h
    have := congrArg (((b⁻¹ : G.Cˣ) : G.C) * ·) h
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
  · intro h; rw [h]

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem triv_mul_inv (bP bQ : G.C) (x u : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) bQ x t)
    (hu : (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) bQ * (starT G.star (AfP p) u).unop = inC G (AfP p) bP) :
    Triv G (AfP p) bP (x * u⁻¹) t := by
  unfold Triv at *
  have hs : (starT G.star (AfP p) (((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop =
      (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop *
        (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop := by
    rw [Units.val_mul, map_mul, MulOpposite.unop_mul]
  have h1 : (starT G.star (AfP p) (u : AfP p ⊗[ℚ] G.C)).unop *
      (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  rw [hs, ← hu, ← hx]
  calc ((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        ((u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) bQ * (starT G.star (AfP p) u).unop) *
        ((starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop *
          (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop)
      = (x : AfP p ⊗[ℚ] G.C) * (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * u) * inC G (AfP p) bQ *
          ((starT G.star (AfP p) (u : AfP p ⊗[ℚ] G.C)).unop *
            (starT G.star (AfP p) (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C)).unop) *
          (starT G.star (AfP p) (x : AfP p ⊗[ℚ] G.C)).unop := by
        simp only [Units.val_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h1, mul_one, mul_one]

theorem termAt_eq (P : Pair G) (Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) (x u : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) Q.β x t) (hx' : Triv G (AfP p) P.β (x * u⁻¹) t)
    (hu : (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u)
    (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (δ z : Gr G r) :
    P.termAt Kf f r K φ (x * u⁻¹) t hx' δ z = Q.termAt Kf f r K φ x t hx δ z := by
  set e : P.cent ≃* Q.cent := MulEquiv.subgroupCongr (cent_eq P Q hγ hc)
  have h₁ : ∀ y, Q.toAf x t hx (e y) = P.toAf (x * u⁻¹) t hx' y := by
    intro y
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    apply Units.ext
    have hyc : ((y : G.Cˣ × ℚˣ).1 : G.C) * (P.γ : G.C) = (P.γ : G.C) * (y : G.Cˣ × ℚˣ).1 := by
      rw [← Units.val_mul, y.2.1, Units.val_mul]
    have hc1 : ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, hyc]
    have hc2 : (u : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) * u := by rw [hγ]; exact hu
    have hcomm := GlobalTheory.LKCentAf.commute_of_centralizer ℚ (AfP p) G.C _ (P.γ : G.C) _
      (GlobalTheory.LKCentAf.cent_iff_mem P) _ _ hc2 hc1
    show (x : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) =
      ((x * u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) *
        (((x * u⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
    have hY : ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        (((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * u) = (1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C) := by
      rw [← hcomm, ← mul_assoc, Units.inv_mul, one_mul]
    calc (x : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) *
          ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
        = (x : AfP p ⊗[ℚ] G.C) * (((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
            (((1 : AfP p) ⊗ₜ[ℚ] ((y : G.Cˣ × ℚˣ).1 : G.C)) * u)) *
            ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by rw [hY]
      _ = _ := by simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]
  have hself : e P.self = Q.self := Subtype.ext (by
    show ((P.γ, P.c) : G.Cˣ × ℚˣ) = (Q.γ, Q.c)
    rw [hγ, hc])
  have hs : P.toAf (x * u⁻¹) t hx' P.self = Q.toAf x t hx Q.self := by rw [← h₁, hself]
  unfold Pair.termAt DPair.termAt
  rw [hs]
  exact pointSum_equiv e _ _ _ _ h₁ (fun y => rfl) _ _ _ _ _ _ _

end GlobalTheory.LKDefTerm

namespace GlobalTheory.LKDefTerm

theorem term_eq_of_local_isom : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Q : DPair G), P.γ = Q.γ → P.c = Q.c → (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C)) → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.term Kf f r K φ = Q.term Kf f r K φ := by
  intro p _ G P Q hγ hc hu Kf f r K φ hr hf hφ
  obtain ⟨u, huγ, huβ⟩ := hu
  have hat : P.atP = Q.atP := by
    unfold Pair.atP DPair.atP
    rw [hγ, hc]
  unfold DPair.term
  split_ifs with h
  · have hQ := Q.trivAf.choose_spec.choose_spec
    have hx' := triv_mul_inv (P.β : G.C) (Q.β : G.C) _ u _ hQ huβ
    rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f r K φ hr hf hφ _ _ hx' h.choose.1 h.choose.2 (by rw [hat]; exact h.choose_spec)]
    exact termAt_eq P Q hγ hc _ u _ hQ hx' huγ Kf f r K φ _ _
  · unfold Pair.term
    rw [dif_neg]
    rwa [hat]

end GlobalTheory.LKDefTerm
