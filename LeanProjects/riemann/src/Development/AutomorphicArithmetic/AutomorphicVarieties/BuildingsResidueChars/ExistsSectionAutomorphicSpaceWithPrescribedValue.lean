import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearSectionAutomorphicFunctionsOfFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIwahoriTorusProjection

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_section_automorphicSpace_with_prescribed_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ U : Subgroup X.Ub, X.Free τ θ U → ∀ (c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∃ s : (Fin N × Fin m → A) →ₗ[A] X.Fn A m, ∀ v, s v ∈ X.Sp τ θ U ∧ (∀ i j, s v (x i) j = v (i, j)) ∧ ∀ k : ℕ, (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) → ∀ y ∈ X.I.Nm c, X.rp A m y (s v) - s v ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ U hF c N x hcov huniq
  unfold Iwa.ContChar at hθ
  obtain ⟨tt, htt1, htt⟩ := UpperTheory.exists_iwahori_torus_projection Gp X.I
  obtain ⟨s, hs⟩ := UpperTheory.exists_linear_section_automorphicFunctions_of_free Γ Ga Gp X A m τ θ U hF c N x hcov huniq tt
    (fun b hb t => ((htt b hb).1 t).1)
  have hN_le : X.I.N ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_left.trans le_sup_left
  have hT_le : X.I.T ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_right.trans le_sup_left
  have hNm_le : X.I.Nm c ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_right
  have hIw0 : X.I.Iw c ≤ X.I.Iw 0 := by
    unfold Iwa.Iw
    exact sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  have key : ∀ (k : ℕ) (a e w : A), e - 1 ∈ maximalIdeal A ^ k → a * (e * w) - a * w ∈ maximalIdeal A ^ k := by
    intro k a e w h
    rw [show a * (e * w) - a * w = (a * w) * (e - 1) by ring]
    exact Ideal.mul_mem_left _ _ h
  have hright : ∀ (γ : Γ) (i : Fin N) (u : X.Ub) (b y : Gp),
      X.glob γ * x i * ((u : Ga), b) * (1, y) = X.glob γ * x i * ((u : Ga), b * y) := by
    intro γ i u b y
    rw [mul_assoc]
    exact congrArg _ (Prod.ext (mul_one _) rfl)
  have hdiff : ∀ v (k c' : ℕ), c ≤ c' → (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c' → (θ t : A) - 1 ∈ maximalIdeal A ^ k) →
      ∀ y ∈ X.I.Nm c', ∀ g j, s v (g * (1, y)) j - s v g j ∈ maximalIdeal A ^ k := by
    intro v k c' hcc' hk y hy g j
    obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
    have hb0 : b ∈ X.I.Iw 0 := hIw0 hb
    have hyc : y ∈ X.I.Nm c := X.I.Nm_anti hcc' hy
    obtain ⟨s0, hs0, hts⟩ := (htt b hb0).2.2 c' y hy
    have hby : b * y ∈ X.I.Iw c := mul_mem hb (hNm_le hyc)
    rw [hright, hs v γ i u hu (b * y) hby, hs v γ i u hu b hb, hts, map_mul, mul_inv, Units.val_mul, mul_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    apply key
    have h := hk s0 hs0
    have hinv := Units.inv_mul (θ s0)
    have : (((θ s0)⁻¹ : Aˣ) : A) - 1 = -(((θ s0)⁻¹ : Aˣ) : A) * ((θ s0 : A) - 1) := by
      linear_combination hinv
    rw [this]
    exact Ideal.mul_mem_left _ _ h
  refine ⟨s, fun v => ⟨?_, ?_, ?_⟩⟩
  · unfold Frame.Sp Frame.Amb
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show (_ ∧ _ ∧ _ ∧ _)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro γ' g
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [show X.glob γ' * (X.glob γ * x i * ((u : Ga), b)) = X.glob (γ' * γ) * x i * ((u : Ga), b) by
          rw [map_mul]; simp only [mul_assoc], hs v _ i u hu b hb, hs v γ i u hu b hb]
      · unfold fixd
        show ∀ n ∈ X.I.N, _
        intro n hn
        funext g
        show s v (g * (1, n)) = s v g
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [hright, hs v γ i u hu (b * n) (mul_mem hb (hN_le hn)), hs v γ i u hu b hb,
          (htt b (hIw0 hb)).2.1 n hn]
      · intro t
        funext g
        show s v (g * (1, (t : Gp))) = _
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [hright, hs v γ i u hu (b * t) (mul_mem hb (hT_le t.2)), Pi.smul_apply, hs v γ i u hu b hb,
          ((htt b (hIw0 hb)).1 t).2, map_mul, mul_inv, Units.val_mul,
          mul_comm (((θ (tt b))⁻¹ : Aˣ) : A), mul_smul]
      · intro k
        obtain ⟨c0, hc0⟩ := hθ k
        exact ⟨max c c0, fun y hy g j => hdiff v k (max c c0) (le_max_left _ _)
          (fun t ht => hc0 t (X.I.Tc_anti (le_max_right _ _) ht)) y hy g j⟩
    · unfold fixd
      show ∀ u' ∈ U, _
      intro u' hu'
      funext g
      rw [Frame.ra_apply]
      obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
      rw [show X.glob γ * x i * ((u : Ga), b) * ((u' : Ga), 1) =
            X.glob γ * x i * (((u * u' : X.Ub) : Ga), b) by
          rw [mul_assoc]; exact congrArg _ (Prod.ext rfl (mul_one _)),
        hs v γ i (u * u') (mul_mem hu hu') b hb, hs v γ i u hu b hb, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, show u' * (u * u')⁻¹ = u⁻¹ by group]
  · intro i j
    have e : x i = X.glob 1 * x i * (((1 : X.Ub) : Ga), (1 : Gp)) := by simp
    rw [e, hs v 1 i 1 U.one_mem 1 (X.I.Iw c).one_mem, htt1]
    simp
  · intro k hk y hy
    unfold Frame.valIn
    rw [Submodule.mem_pi]
    intro g _
    rw [Submodule.mem_pi]
    intro j _
    exact hdiff v k c le_rfl hk y hy g j
