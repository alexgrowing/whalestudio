import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open Formalism.UG

namespace GlobalTheory.UnitarySplit

variable {A : Type} [CommRing A] {n : ℕ}

noncomputable def adj (c : A →+* A) (J M : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  J⁻¹ * cT c M * J

theorem cT_add' (c : A →+* A) (M N : Matrix (Fin n) (Fin n) A) :
    cT c (M + N) = cT c M + cT c N := by
  ext i j; simp [cT]

theorem cT_smul' (c : A →+* A) (a : A) (M : Matrix (Fin n) (Fin n) A) :
    cT c (a • M) = c a • cT c M := by
  ext i j; simp [cT]

theorem cT_cT' (c : A →+* A) (hc : ∀ x, c (c x) = x) (M : Matrix (Fin n) (Fin n) A) :
    cT c (cT c M) = M := by
  ext i j; simp [cT, hc]

theorem adj_add (c : A →+* A) (J M N : Matrix (Fin n) (Fin n) A) :
    adj c J (M + N) = adj c J M + adj c J N := by
  simp only [adj, cT_add', Matrix.mul_add, Matrix.add_mul]

theorem adj_smul (c : A →+* A) (a : A) (J M : Matrix (Fin n) (Fin n) A) :
    adj c J (a • M) = c a • adj c J M := by
  simp only [adj, cT_smul', Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) :
    adj c J 1 = 1 := by
  rw [adj, cT_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hJ]

theorem adj_mul (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (M N : Matrix (Fin n) (Fin n) A) : adj c J (M * N) = adj c J N * adj c J M := by
  simp only [adj, cT_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

theorem adj_adj (c : A →+* A) (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) A}
    (hJ : IsUnit J.det) (hh : cT c J = J) (M : Matrix (Fin n) (Fin n) A) :
    adj c J (adj c J M) = M := by
  have h1 : J * cT c J⁻¹ = 1 := by
    have := cT_mul c J⁻¹ J
    rw [Matrix.nonsing_inv_mul _ hJ, cT_one, hh] at this
    exact this.symm
  have h2 : cT c J⁻¹ * J = 1 := mul_eq_one_comm.mp h1
  simp only [adj, cT_mul, hh, cT_cT' c hc, Matrix.mul_assoc, h2, Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ hJ]

theorem mem_iff_adj (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (G : GL (Fin n) A) :
    G ∈ UJ c J ↔ adj c J (G : Matrix (Fin n) (Fin n) A) * (G : Matrix (Fin n) (Fin n) A) = 1 := by
  change cT c (G : Matrix (Fin n) (Fin n) A) * J * (G : Matrix (Fin n) (Fin n) A) = J ↔ _
  constructor
  · intro h
    rw [adj, Matrix.mul_assoc J⁻¹, Matrix.mul_assoc J⁻¹, h, Matrix.nonsing_inv_mul _ hJ]
  · intro h
    have := congrArg (fun M => J * M) h
    simpa only [adj, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ,
      Matrix.mul_one] using this

theorem unitary_supported_equiv (A L : Type) [CommRing A] [CommRing L] (n : ℕ) (c : A →+* A)
    (e : A) (J : Matrix (Fin n) (Fin n) A) (π : A →+* L) (s : L → A)
    (hc : ∀ x, c (c x) = x) (he : e * e = e) (hec : e * c e = 0) (hJ : IsUnit J.det)
    (hh : cT c J = J) (hs : ∀ x, s (π x) = e * x) (hπ : ∀ a, π (s a) = a) :
    (∀ g : GL (Fin n) L, ∃ G ∈ UJ c J,
      (∀ i j, (e + c e) * ((G : Matrix (Fin n) (Fin n) A) - 1) i j
        = ((G : Matrix (Fin n) (Fin n) A) - 1) i j) ∧ bc π G = g) ∧
    ∀ G ∈ UJ c J, ∀ G' ∈ UJ c J,
      (∀ i j, (e + c e) * ((G : Matrix (Fin n) (Fin n) A) - 1) i j
        = ((G : Matrix (Fin n) (Fin n) A) - 1) i j) →
      (∀ i j, (e + c e) * ((G' : Matrix (Fin n) (Fin n) A) - 1) i j
        = ((G' : Matrix (Fin n) (Fin n) A) - 1) i j) → bc π G = bc π G' → G = G' := by
  have hπe : π e = 1 := by
    have := hπ (π 1)
    rwa [hs, mul_one, map_one] at this
  have hπc : π (c e) = 0 := by
    have := congrArg π hec
    rwa [map_mul, hπe, one_mul, map_zero] at this
  have hcc : c e * c e = c e := by rw [← map_mul, he]
  have hce : c e * e = 0 := by rw [mul_comm, hec]
  have key : ∀ M N : Matrix (Fin n) (Fin n) A, π.mapMatrix M = π.mapMatrix N → e • M = e • N := by
    intro M N h
    ext i j
    have h1 : π (M i j) = π (N i j) := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul, ← hs, h1]
  constructor
  · intro g
    have lift : ∀ M : Matrix (Fin n) (Fin n) L, π.mapMatrix (M.map s) = M := by
      intro M; ext i j; simp [hπ]
    set X : Matrix (Fin n) (Fin n) A := (g : Matrix (Fin n) (Fin n) L).map s with hX
    set Y : Matrix (Fin n) (Fin n) A := ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map s
      with hY
    have hYX : e • (Y * X) = e • (1 : Matrix (Fin n) (Fin n) A) := by
      apply key
      rw [map_mul, lift, lift, map_one, Units.inv_mul]
    have hXY : c e • (adj c J X * adj c J Y) = c e • (1 : Matrix (Fin n) (Fin n) A) := by
      rw [← adj_mul c hJ, ← adj_smul, hYX, adj_smul, adj_one c hJ]
    obtain ⟨f, hf⟩ : ∃ f, f = 1 - e - c e := ⟨_, rfl⟩
    have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
    have hef : e * f = 0 := by rw [hf, mul_sub, mul_sub, he, hec]; ring
    have hfe : f * e = 0 := by rw [mul_comm, hef]
    have hcef : c e * f = 0 := by rw [hf, mul_sub, mul_sub, hce, hcc]; ring
    have hfce : f * c e = 0 := by rw [mul_comm, hcef]
    have hff : f * f = f := by
      have : f * f = f - f * e - f * c e := by
        conv_lhs => rw [show f * f = f * (1 - e - c e) by rw [← hf]]
        ring
      rw [this, hfe, hfce]; ring
    have hπf : π f = 0 := by rw [hf, map_sub, map_sub, map_one, hπe, hπc]; ring
    set M : Matrix (Fin n) (Fin n) A := e • X + c e • adj c J Y + f • 1 with hM
    have hadj : adj c J M = c e • adj c J X + e • Y + f • 1 := by
      rw [hM, adj_add, adj_add, adj_smul, adj_smul, adj_smul, adj_adj c hc hJ hh, hc, hcf,
        adj_one c hJ]
    have hMM : adj c J M * M = 1 := by
      rw [hadj, hM]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
        smul_smul, he, hec, hce, hcc, hef, hfe, hcef, hfce, hff, zero_smul, zero_add, add_zero,
        hYX, hXY, Matrix.mul_one]
      rw [← add_smul, ← add_smul, hf]
      simp
    refine ⟨⟨M, adj c J M, mul_eq_one_comm.mp hMM, hMM⟩, (mem_iff_adj c hJ _).mpr hMM, ?_, ?_⟩
    · intro i j
      change (e + c e) * (M - 1) i j = (M - 1) i j
      have : f * (M - 1) i j = 0 := by
        simp only [hM, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          mul_sub, mul_add, ← mul_assoc, hfe, hfce, hff]
        ring
      rw [hf] at this
      linear_combination -this
    · ext i j
      change π (M i j) = (g : Matrix (Fin n) (Fin n) L) i j
      simp only [hM, hX, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, hπe,
        hπc, hπf, Matrix.map_apply, hπ]
      ring
  · intro G hG G' hG' h1 h2 h
    have h3 : e • (G : Matrix (Fin n) (Fin n) A) = e • (G' : Matrix (Fin n) (Fin n) A) :=
      key _ _ (congrArg Units.val h)
    have hinv : bc π G⁻¹ = bc π G'⁻¹ := by rw [map_inv, map_inv, h]
    have h4 : e • ((G⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
        = e • ((G'⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) :=
      key _ _ (congrArg Units.val hinv)
    have hi : ∀ K ∈ UJ c J, ((K⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
        = adj c J (K : Matrix (Fin n) (Fin n) A) := fun K hK =>
      Units.inv_eq_of_mul_eq_one_left ((mem_iff_adj c hJ K).mp hK)
    rw [hi G hG, hi G' hG'] at h4
    have h5 := congrArg (adj c J) h4
    rw [adj_smul, adj_smul, adj_adj c hc hJ hh, adj_adj c hc hJ hh] at h5
    ext i j
    have a1 := h1 i j
    have a2 := h2 i j
    have a3 := congrFun (congrFun h3 i) j
    have a5 := congrFun (congrFun h5 i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at a1 a2 a3 a5
    linear_combination a2 - a1 + a3 + a5

end GlobalTheory.UnitarySplit
