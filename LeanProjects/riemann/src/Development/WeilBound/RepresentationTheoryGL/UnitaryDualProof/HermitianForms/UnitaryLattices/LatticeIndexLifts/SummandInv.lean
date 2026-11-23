import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.SumCharEqZero

noncomputable section

set_option linter.unusedSectionVars false

open Matrix
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def stab (col : (Fin n → k) → V →ₗ[ℂ] V) (hc0 : ∀ v, col 0 v = v)
    (hca : ∀ x y v, col (x + y) v = col x (col y v)) (v : V) : AddSubgroup (Fin n → k) where
  carrier := {x | col x v = v}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [hca, hy, hx]
  zero_mem' := hc0 v
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    calc col (-x) v = col (-x) (col x v) := by rw [hx]
      _ = col (-x + x) v := (hca _ _ _).symm
      _ = v := by rw [neg_add_cancel, hc0]

def kers (φ : AddChar k Circle) (s : Finset (Fin n → k)) : AddSubgroup (Fin n → k) where
  carrier := {x | ∀ ξ ∈ s, φ (ξ ⬝ᵥ x) = 1}
  add_mem' := by
    intro x y hx hy ξ hξ
    rw [dotProduct_add, AddChar.map_add_eq_mul, hx ξ hξ, hy ξ hξ, one_mul]
  zero_mem' := by
    intro ξ _
    simp
  neg_mem' := by
    intro x hx ξ hξ
    rw [dotProduct_neg, AddChar.map_neg_eq_inv, hx ξ hξ, inv_one]

theorem isOpen_kers (φ : AddChar k Circle) (hφ : Continuous φ) (s : Finset (Fin n → k)) :
    IsOpen (kers φ s : Set (Fin n → k)) := by
  have : (kers φ s : Set (Fin n → k)) = ⋂ ξ ∈ s, {x | φ (ξ ⬝ᵥ x) = 1} := by
    ext x
    simp [kers]
  rw [this]
  refine isOpen_biInter_finset fun ξ _ => ?_
  exact (isOpen_ker φ hφ).preimage (by fun_prop)

theorem exists_AD (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (hsm : ∀ v, IsOpen {x | col x v = v})
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k)) (v : V) :
    ∃ p : AddSubgroup (Fin n → k) × Finset (Fin n → k), ∀ ξ ∈ s, AD φ col ξ A v p := by
  let H := A ⊓ stab col hc0 hca v ⊓ kers φ s
  have hHo : IsOpen (H : Set (Fin n → k)) := by
    simp only [H, AddSubgroup.coe_inf]
    exact (hA.2.inter (hsm v)).inter (isOpen_kers φ hφ s)
  have hHA : H ≤ A := fun x hx => hx.1.1
  obtain ⟨T, hT, hu⟩ := exists_tr A H hA.1 hHo hHA
  exact ⟨(H, T), fun ξ hξ => ⟨hHA, hHo, fun a ha => ha.1.2, fun a ha => ha.2 ξ hξ, hT, hu⟩⟩

theorem summand_inv (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hca : ∀ x y v, col (x + y) v = col x (col y v)) (ξ : Fin n → k) (v : V) (H : AddSubgroup (Fin n → k))
    (h3 : ∀ a ∈ H, col a v = v) (h4 : ∀ a ∈ H, φ (ξ ⬝ᵥ a) = 1) :
    ∀ x, ∀ h ∈ H, (fun t => (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) (x + h) =
      (fun t => (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) x := by
  intro x h hh
  simp only [dotProduct_add, AddChar.map_add_eq_mul, h4 h hh, mul_one, hca, h3 h hh]

theorem av_eq' (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (A : AddSubgroup (Fin n → k)) (ξ : Fin n → k) (v : V) (p : AddSubgroup (Fin n → k) × Finset (Fin n → k))
    (hp : AD φ col ξ A v p) :
    av φ col ξ A v = ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v := by
  have hd : ∃ p, AD φ col ξ A v p := ⟨p, hp⟩
  unfold av
  rw [dif_pos hd]
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hd.choose_spec
  obtain ⟨g1, -, g3, g4, g5, g6⟩ := hp
  exact avg_indep A _ _ h1 g1 _ _ h5 h6 g5 g6 _ (summand_inv φ col hca ξ v _ h3 h4)
    (summand_inv φ col hca ξ v _ g3 g4)

theorem circ_char (φ ψ : AddChar k Circle) (ξ η : Fin n → k) (x y : Fin n → k) :
    (φ (ξ ⬝ᵥ (x + y)))⁻¹ * ψ (η ⬝ᵥ (x + y)) = ((φ (ξ ⬝ᵥ x))⁻¹ * ψ (η ⬝ᵥ x)) * ((φ (ξ ⬝ᵥ y))⁻¹ * ψ (η ⬝ᵥ y)) := by
  rw [dotProduct_add, dotProduct_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

open Classical in
theorem av_eigen' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (ψ : AddChar k Circle) (η : Fin n → k)
    (hE : ∀ x u w, E (col x u) w = ((ψ (η ⬝ᵥ x) : Circle) : ℂ) * E u w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v w : V) :
    E (av φ col ξ A v) w = if ∀ a ∈ A, ψ (η ⬝ᵥ a) = φ (ξ ⬝ᵥ a) then E v w else 0 := by
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA {ξ} v
  have hp' := hp ξ (Finset.mem_singleton_self ξ)
  rw [av_eq' φ col hca A ξ v p hp']
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hp'
  let χ : (Fin n → k) → Circle := fun t => (φ (ξ ⬝ᵥ t))⁻¹ * ψ (η ⬝ᵥ t)
  have hexp : E (((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) w
      = ((p.2.card : ℂ)⁻¹ * ∑ t ∈ p.2, ((χ t : Circle) : ℂ)) * E v w := by
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, hE]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [χ, Circle.coe_mul, Circle.coe_inv_eq_conj]
    ring
  rw [hexp]
  by_cases hEv : E v w = 0
  · rw [hEv, mul_zero]
    split_ifs <;> rfl
  have hψ : ∀ a ∈ p.1, ψ (η ⬝ᵥ a) = 1 := by
    intro a ha
    have h := hE a v w
    rw [h3 a ha] at h
    have h' : (((ψ (η ⬝ᵥ a) : Circle) : ℂ) - 1) * E v w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact Circle.coe_eq_one.1 (sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hEv))
  have hχH : ∀ a ∈ p.1, χ a = 1 := by
    intro a ha
    simp only [χ, h4 a ha, hψ a ha, inv_one, mul_one]
  have hN := card_ne_zero A p.1 p.2 h6
  split_ifs with hc
  · have : ∑ t ∈ p.2, ((χ t : Circle) : ℂ) = p.2.card := by
      rw [Finset.sum_congr rfl (fun t ht => by
        simp only [χ, hc t (h5 t ht), inv_mul_cancel, Circle.coe_one] : ∀ t ∈ p.2, ((χ t : Circle) : ℂ) = 1)]
      simp
    rw [this, inv_mul_cancel₀ hN, one_mul]
  · simp only [not_forall] at hc
    obtain ⟨a, ha, hne⟩ := hc
    have hχa : χ a ≠ 1 := by
      intro h
      apply hne
      have := congrArg (fun z => φ (ξ ⬝ᵥ a) * z) h
      simpa [χ] using this
    rw [sum_circ_eq_zero A p.1 h1 p.2 h5 h6 χ (circ_char φ ψ ξ η) hχH a ha hχa, mul_zero, zero_mul]

theorem mulVec_ginv (g : GL (Fin n) k) (x : Fin n → k) :
    ((g : Matrix (Fin n) (Fin n) k)) *ᵥ (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem ginv_mulVec (g : GL (Fin n) k) (x : Fin n → k) :
    (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem mem_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (x : Fin n → k) :
    x ∈ gmap g A ↔ (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x ∈ A := by
  simp only [gmap, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [ginv_mulVec]
  · intro h
    exact ⟨_, h, mulVec_ginv g x⟩

theorem isOpen_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : IsOpen (A : Set (Fin n → k))) :
    IsOpen (gmap g A : Set (Fin n → k)) := by
  have : (gmap g A : Set (Fin n → k)) =
      (fun x => (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x) ⁻¹' (A : Set (Fin n → k)) := by
    ext x
    exact mem_gmap g A x
  rw [this]
  exact hA.preimage (continuous_const.matrix_mulVec continuous_id)

theorem lat_gmap' (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) : Lat (gmap g A) := by
  refine ⟨?_, isOpen_gmap g A hA.2⟩
  have : (gmap g A : Set (Fin n → k)) = (fun x => (g : Matrix (Fin n) (Fin n) k) *ᵥ x) '' (A : Set (Fin n → k)) := by
    simp only [gmap, AddSubgroup.coe_map]
    rfl
  rw [this]
  exact hA.1.image (continuous_const.matrix_mulVec continuous_id)

theorem dot_g (g : GL (Fin n) k) (ξ x : Fin n → k) :
    (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ⬝ᵥ x =
      ξ ⬝ᵥ ((((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x) := by
  rw [dotProduct_mulVec]

theorem av_conj' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (gl : GL (Fin n) k →* (V →ₗ[ℂ] V))
    (hconj : ∀ g x v, gl g (col x v) = col ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) (gl g v))
    (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v : V) :
    gl g (av φ col ξ A v) = av φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) := by
  classical
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA {ξ} v
  have hp' := hp ξ (Finset.mem_singleton_self ξ)
  rw [av_eq' φ col hca A ξ v p hp']
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp'
  have hinj : Function.Injective (fun t : Fin n → k => (g : Matrix (Fin n) (Fin n) k) *ᵥ t) := by
    intro x y hxy
    have := congrArg (fun z => (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ z) hxy
    simpa only [ginv_mulVec] using this
  let q : AddSubgroup (Fin n → k) × Finset (Fin n → k) :=
    (gmap g p.1, p.2.image (fun t => (g : Matrix (Fin n) (Fin n) k) *ᵥ t))
  have hsub : ∀ a t, (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ (a - (g : Matrix (Fin n) (Fin n) k) *ᵥ t)
      = (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ a - t := by
    intro a t
    rw [Matrix.mulVec_sub, ginv_mulVec]
  have hq : AD φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) q := by
    refine ⟨AddSubgroup.map_mono h1, isOpen_gmap g p.1 h2, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [mem_gmap] at ha
      rw [← mulVec_ginv g a, ← hconj, h3 _ ha]
    · intro a ha
      rw [mem_gmap] at ha
      rw [dot_g]
      exact h4 _ ha
    · intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 ht
      rw [mem_gmap, ginv_mulVec]
      exact h5 t₀ ht₀
    · intro a ha
      rw [mem_gmap] at ha
      obtain ⟨t₀, ⟨ht₀, hb⟩, huq⟩ := h6 _ ha
      refine ⟨(g : Matrix (Fin n) (Fin n) k) *ᵥ t₀, ⟨Finset.mem_image.2 ⟨t₀, ht₀, rfl⟩, ?_⟩, ?_⟩
      · rw [mem_gmap, hsub]
        exact hb
      · rintro t ⟨ht, hat⟩
        obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.1 ht
        rw [mem_gmap, hsub] at hat
        rw [huq t₁ ⟨ht₁, hat⟩]
  rw [av_eq' φ col hca (gmap g A) _ (gl g v) q hq]
  simp only [q]
  rw [Finset.card_image_of_injective _ hinj, Finset.sum_image (fun x _ y _ h => hinj h)]
  simp only [map_smul, map_sum, hconj, dot_g, ginv_mulVec]

end PositivityTheory.RgUd.Form.U.Lift2.AvA
