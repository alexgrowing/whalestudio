import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem lower_one {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) (c d : ℕ) (hcd : c ≤ d) (v : M) (hN : v ∈ fixd π I.N) (hT : v ∈ fixd π (I.Tc c))
    (hm : v ∈ fixd π (I.Nm (d + 1))) :
    I.uOp π I.z v ∈ fixd π I.N ∧ I.uOp π I.z v ∈ fixd π (I.Tc c) ∧ I.uOp π I.z v ∈ fixd π (I.Nm d) := by
  obtain ⟨h1, -, -, h2, -⟩ := uOpMul G I A M π I.z I.z I.z_mem I.z_mem v hN
  refine ⟨h1, fun t ht => by rw [h2 t (I.Tc_le c ht), hT t ht], fun y hy => ?_⟩
  exact (uOpLevel G I A M π d).2.1 v hN (fun t ht => hT t (I.Tc_anti hcd ht)) hm y (Subgroup.mem_sup_right hy)

private theorem lower_many {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) (c n : ℕ) : ∀ v : M, v ∈ fixd π I.N → v ∈ fixd π (I.Tc c) →
      v ∈ fixd π (I.Nm (c + n)) → (I.uOp π I.z ^ n) v ∈ fixd π (I.Nm c) := by
  induction n with
  | zero => exact fun v _ _ hm => by simpa using hm
  | succ n ih =>
    intro v hN hT hm
    obtain ⟨h1, h2, h3⟩ := lower_one I π c (c + n) (Nat.le_add_right c n) v hN hT hm
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ h1 h2 h3

theorem UpperTheory.uOperator_pow_eventually_invariant_mod_pow :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ f ∈ X.Amb m θ, ∀ k c : ℕ, (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ y ∈ X.I.Nm c, X.rp A m y ((X.U A m X.I.z ^ n) f) - (X.U A m X.I.z ^ n) f ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m θ _ f hf k c hc
  obtain ⟨-, h2, h3, h4⟩ := hf
  obtain ⟨c1, hc1⟩ := h4 k
  refine ⟨c1, fun n hn y hy => ?_⟩
  let φ : X.Fn A m →ₗ[A] X.Fn (A ⧸ maximalIdeal A ^ k) m := X.mapFn
  have hφ : ∀ f g i, φ f g i = Ideal.Quotient.mk _ (f g i) := fun _ _ _ => rfl
  have hnat : ∀ b f, φ (X.rp A m b f) = X.rp _ m b (φ f) := fun _ _ => rfl
  have hN : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) X.I.N := fun x hx => by rw [← hnat, h2 x hx]
  have hT : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.Tc c) := fun t ht => by
    have ht' := X.I.Tc_le _ ht
    have := hc ⟨t, ht'⟩⁻¹ (inv_mem ht)
    rw [← hnat, h3 ⟨t, ht'⟩]
    funext g i
    rw [hφ, hφ, Ideal.Quotient.eq]
    have h6 := Ideal.mul_mem_right (f g i) _ this
    rw [map_inv] at h6
    convert h6 using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hm : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.Nm (c + n)) := fun w hw => by
    rw [← hnat]
    funext g i
    rw [hφ, hφ, Ideal.Quotient.eq]
    exact hc1 w (X.I.Nm_anti (by omega) hw) g i
  have hpow : ∀ j : ℕ, φ ((X.U A m X.I.z ^ j) f) =
      (X.I.uOp (X.rp (A ⧸ maximalIdeal A ^ k) m) X.I.z ^ j) (φ f) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact uOpNat Gp X.I A _ (X.rp A m) _ _ (X.rp (A ⧸ maximalIdeal A ^ k) m) φ.toAddMonoidHom X.I.z X.I.z_mem _
        (fun _ _ => rfl)
  have h7 := lower_many X.I (X.rp (A ⧸ maximalIdeal A ^ k) m) c n _ hN hT hm y hy
  rw [← hpow, ← hnat] at h7
  simp only [Frame.valIn, Submodule.mem_pi]
  intro g _ i _
  have h9 := congrFun (congrFun h7 g) i
  rw [hφ, hφ, Ideal.Quotient.eq] at h9
  exact h9
