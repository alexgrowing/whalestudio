import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Central
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DSigma
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {F G : Type} [Field F] [Group G] {n : ℕ}

private theorem evP_iff {a : ℕ} (N : Matrix (Fin n) (Fin n) F) :
    N ∈ Ev F F n a ↔ ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → N i j = 0 :=
  ⟨fun h i j e => (Submodule.mem_bot F).1 ((h i j).2 e),
    fun h i j => ⟨fun _ => Submodule.mem_top, fun e => (Submodule.mem_bot F).2 (h i j e)⟩⟩

private theorem evP_mul {a : ℕ} {N N' : Matrix (Fin n) (Fin n) F} (h : N ∈ Ev F F n a)
    (h' : N' ∈ Ev F F n a) : N * N' ∈ Ev F F n a := by
  rw [evP_iff] at *
  intro i j e
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases c : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [h' k j (by tauto), mul_zero]
  · rw [h i k c, zero_mul]

private theorem evP_tr {a : ℕ} {N : Matrix (Fin n) (Fin n) F} (h : N ∈ Ev F F n a) :
    Nᵀ ∈ Ev F F n a := by
  rw [evP_iff] at *
  intro i j e
  exact h j i (by tauto)

private theorem evP_inv (D : DetFr F G n) (g : G) : D.r g⁻¹ * D.r g = 1 := by
  rw [← map_mul]; simp

private theorem evP_inv' (D : DetFr F G n) (g : G) : D.r g * D.r g⁻¹ = 1 := by
  rw [← map_mul]; simp

private theorem evP_kills (D : DetFr F G n) (z : G → Matrix (Fin n) (Fin n) F)
    (hz : TwCoc (fun _ => 1) D.r D.G' z) (hev : ∀ g, z g ∈ Ev F F n D.a)
    (htr : ∀ g ∈ D.G', (z g * D.r g).trace = 0) (i j : Fin n) : D.KillsRel z i j := by
  classical
  intro c hc h0
  set M := c.sum fun g x => x • (z g * D.r g) with hM
  have hME : M ∈ Ev F F n D.a :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (evP_mul (hev g) (D.ev g))
  have key : ∀ X ∈ Ev F F n D.a, (M * X).trace = 0 := by
    intro X hX
    rw [← D.span] at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      have e : ∀ g ∈ c.support, (c g • (z g * D.r g) * D.r h).trace
          = -((c g • D.r g) * (z h * D.r h)).trace := by
        intro g hg
        have h1 := htr _ (D.G'.mul_mem (hc g hg) hh)
        rw [hz g (hc g hg) h hh, map_mul, one_smul, add_mul] at h1
        have h2 : D.r g * z h * D.r g⁻¹ * (D.r g * D.r h)
            = D.r g * z h * (D.r g⁻¹ * D.r g) * D.r h := by
          simp only [mul_assoc]
        rw [h2, evP_inv, mul_one, trace_add] at h1
        rw [smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul, ← smul_neg]
        congr 1
        simp only [mul_assoc] at h1 ⊢
        exact eq_neg_of_add_eq_zero_left h1
      rw [hM, Finsupp.sum, Finset.sum_mul, trace_sum, Finset.sum_congr rfl e,
        Finset.sum_neg_distrib, ← trace_sum, ← Finset.sum_mul]
      rw [Finsupp.sum] at h0
      rw [h0]; simp
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mul_smul_comm, trace_smul, hx, smul_zero]
  by_cases hij : ((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)
  · have hE : Matrix.single j i (1 : F) ∈ Ev F F n D.a := by
      rw [evP_iff]
      intro p q h
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h hij.symm
    have := key _ hE
    rw [Matrix.trace_mul_single] at this
    simpa using this
  · exact (evP_iff M).1 hME i j hij

private theorem evP_even (D : DetFr F G n) (Y : Matrix (Fin n) (Fin n) F) :
    ∃ Y' ∈ Ev F F n D.a, ∀ (χ : G → F) (g : G), dTw χ D.r Y g ∈ Ev F F n D.a →
      dTw χ D.r Y g = dTw χ D.r Y' g := by
  classical
  set S : Matrix (Fin n) (Fin n) F := diagonal fun i => if (i : ℕ) < D.a then 1 else -1 with hS
  have hc : ∀ X ∈ Ev F F n D.a, S * X = X * S := by
    intro X hX
    ext i j
    rw [hS, diagonal_mul, mul_diagonal]
    by_cases hij : ((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)
    · simp only [hij, mul_comm]
    · rw [(evP_iff X).1 hX i j hij]; simp
  have hSS : S * S = 1 := by
    rw [hS, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp
  refine ⟨(2 : F)⁻¹ • (Y + S * Y * S), ?_, fun χ g hg => ?_⟩
  · refine Submodule.smul_mem _ _ ?_
    rw [evP_iff]
    intro i j hij
    rw [Matrix.add_apply, hS, mul_diagonal, diagonal_mul]
    by_cases hi : (i : ℕ) < D.a <;> by_cases hj : (j : ℕ) < D.a
    · exact absurd (iff_of_true hi hj) hij
    · rw [if_pos hi, if_neg hj]; ring
    · rw [if_neg hi, if_pos hj]; ring
    · exact absurd (iff_of_false hi hj) hij
  · have h1 : dTw χ D.r (S * Y * S) g = dTw χ D.r Y g := by
      have h2 : S * dTw χ D.r Y g * S = dTw χ D.r Y g := by
        rw [hc _ hg, mul_assoc, hSS, mul_one]
      rw [← h2]
      unfold dTw
      rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      congr 2
      calc D.r g * (S * Y * S) * D.r g⁻¹ = (D.r g * S) * Y * (S * D.r g⁻¹) := by
            simp only [mul_assoc]
        _ = _ := by
            rw [← hc _ (D.ev g), hc _ (D.ev g⁻¹)]
            simp only [mul_assoc]
    have h3 : dTw χ D.r ((2 : F)⁻¹ • (Y + S * Y * S)) g
        = (2 : F)⁻¹ • (dTw χ D.r Y g + dTw χ D.r (S * Y * S) g) := by
      unfold dTw
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
      module
    rw [h3, h1, ← two_smul F, smul_smul, inv_mul_cancel₀ D.two, one_smul]

private theorem evP_sah (D : DetFr F G n) (z : G → Matrix (Fin n) (Fin n) F)
    (hz : TwCoc D.χF D.r Set.univ z) (hev : ∀ g, z g ∈ Ev F F n D.a)
    (h0 : ∀ g ∈ D.G', z g = 0) : ∃ Z ∈ Ev F F n D.a, ∀ g, z g = dTw D.χF D.r Z g := by
  have hχ : ∀ g ∈ D.G', D.χF g = 1 := fun g hg => by simp [DetFr.χF, D.χ_triv g hg]
  have hcomm : ∀ k g, D.r g * z k = z k * D.r g := by
    intro k
    refine (UpperTheory.V.Pa.Det.central D (z k) fun h hh => ?_).2 (hev k)
    have hm : k⁻¹ * h * k ∈ D.G' := by
      have := D.G'.mul_mem (D.comm k⁻¹ h) hh
      simpa using this
    have e1 := hz h trivial k trivial
    have e2 := hz k trivial _ (Set.mem_univ (k⁻¹ * h * k))
    rw [h0 _ hm, show k * (k⁻¹ * h * k) = h * k by group, e1, h0 h hh, hχ h hh] at e2
    simp only [zero_add, one_smul, mul_zero, zero_mul, smul_zero, add_zero] at e2
    conv_rhs => rw [← e2]
    rw [mul_assoc, evP_inv, mul_one]
  have hconj : ∀ k g, D.r g * z k * D.r g⁻¹ = z k := fun k g => by
    rw [hcomm, mul_assoc, evP_inv', mul_one]
  have hmul : ∀ g k, z (g * k) = z g + D.χF g • z k := fun g k => by
    rw [hz g trivial k trivial, hconj]
  have hne : D.χF D.g₀ - 1 ≠ 0 := by
    intro h
    exact D.χ_ne (Units.ext (sub_eq_zero.1 h))
  refine ⟨(D.χF D.g₀ - 1)⁻¹ • z D.g₀, Submodule.smul_mem _ _ (hev _), fun g => ?_⟩
  have e1 : z (D.g₀ * g) = z (g * D.g₀) := by
    have hm := D.comm D.g₀ g
    rw [show D.g₀ * g = (D.g₀ * g * D.g₀⁻¹ * g⁻¹) * (g * D.g₀) by group, hmul _ (g * D.g₀),
      h0 _ hm, hχ _ hm, zero_add, one_smul]
  rw [hmul, hmul] at e1
  have e2 : (D.χF D.g₀ - 1) • z g = (D.χF g - 1) • z D.g₀ := by
    rw [sub_smul, sub_smul, one_smul, one_smul]
    rw [sub_eq_sub_iff_add_eq_add, add_comm, e1, add_comm]
  unfold dTw
  rw [mul_smul_comm, smul_mul_assoc, hconj, smul_comm, ← smul_sub,
    show D.χF g • z D.g₀ - z D.g₀ = (D.χF g - 1) • z D.g₀ by rw [sub_smul, one_smul], ← e2,
    smul_smul, inv_mul_cancel₀ hne, one_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Det.evenPart :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), s * s = 1 → TwCoc D.χF D.r Set.univ ph → (∀ g, ph g ∈ Ev F F n D.a) → (∀ g, ph (D.σ g) = s • (ph g)ᵀ) → (∀ g ∈ D.G', (ph g * D.r g).trace = 0) → ∃ Y ∈ Ev F F n D.a, s • Yᵀ = Y ∧ ∀ g, ph g = dTw D.χF D.r Y g := by
  intro F G _ _ n D s ph hs hz hev hpol htr
  have hχ : ∀ g ∈ D.G', D.χF g = 1 := fun g hg => by simp [DetFr.χF, D.χ_triv g hg]
  have hz1 : TwCoc (fun _ => 1) D.r D.G' ph := fun g hg h _ => by
    rw [hz g trivial h trivial, hχ g hg]
  obtain ⟨Y₀, hY₀⟩ := UpperTheory.V.Pa.Det.der D ph hz1 (evP_kills D ph hz1 hev htr)
  obtain ⟨Y₁, hY₁, hY₁'⟩ := evP_even D Y₀
  have hd : ∀ g, dTw D.χF D.r Y₁ g ∈ Ev F F n D.a := fun g =>
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (evP_mul (evP_mul (D.ev g) hY₁) (D.ev g⁻¹))) hY₁
  obtain ⟨Z, hZ, hZ'⟩ := evP_sah D (fun g => ph g - dTw D.χF D.r Y₁ g) (by
    intro g _ h _
    have hm : D.χF (g * h) = D.χF g * D.χF h := by simp [DetFr.χF]
    simp only [hz g trivial h trivial, dTw, hm, _root_.mul_inv_rev, map_mul, mul_sub, sub_mul,
      mul_smul_comm, smul_mul_assoc, mul_assoc]
    module) (fun g => Submodule.sub_mem _ (hev g) (hd g)) (by
    intro g hg
    have h1 := hY₁' (fun _ => 1) g (hY₀ g hg ▸ hev g)
    rw [hY₀ g hg, h1]
    simp only [dTw, hχ g hg, sub_self])
  have hY : ∀ g, ph g = dTw D.χF D.r (Y₁ + Z) g := by
    intro g
    have h1 := hZ' g
    rw [sub_eq_iff_eq_add] at h1
    rw [h1]
    simp only [dTw, mul_add, add_mul]
    module
  have hE : Y₁ + Z ∈ Ev F F n D.a := Submodule.add_mem _ hY₁ hZ
  generalize Y₁ + Z = Y at hY hE
  refine ⟨(2 : F)⁻¹ • (Y + s • Yᵀ),
    Submodule.smul_mem _ _ (Submodule.add_mem _ hE (Submodule.smul_mem _ _ (evP_tr hE))), ?_,
    fun g => ?_⟩
  · rw [transpose_smul, transpose_add, transpose_smul, transpose_transpose, smul_comm, smul_add s,
      smul_smul, hs, one_smul, add_comm]
  · have h1 := UpperTheory.V.Pa.Det.dSigma D D.χF Y g (fun g => by simp [DetFr.χF, D.χσ])
    rw [← hY, hpol] at h1
    have h2 : dTw D.χF D.r Yᵀ g = s • ph g := by
      have := congrArg transpose h1
      simpa using this.symm
    have h3 : dTw D.χF D.r ((2 : F)⁻¹ • (Y + s • Yᵀ)) g
        = (2 : F)⁻¹ • (dTw D.χF D.r Y g + s • dTw D.χF D.r Yᵀ g) := by
      unfold dTw
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
      module
    rw [h3, h2, ← hY, smul_smul s, hs, one_smul, ← two_smul F, smul_smul, inv_mul_cancel₀ D.two,
      one_smul]
