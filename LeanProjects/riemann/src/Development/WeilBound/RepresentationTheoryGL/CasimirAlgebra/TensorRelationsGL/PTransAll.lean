import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllC

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TA

def TAk (N : ℕ) : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (E : ι → Fin n → Fin n → Module.End ℂ M), (∀ τ, GlRel (E τ)) →
  (∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) →
  ∀ (l : ι → Fin n → ℤ), (∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → (∀ τ, IsWh (E τ) ℓ) →
  ∀ (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = N →
  ∀ (lab : P → ι) (C : Type) [DecidableEq C] (col : P → C) (b co : P → Fin n),
    (∀ p q, col p = col q → lab p = lab q) → IsTab col b → (∀ p q, col p = col q → co p = co q → p = q) →
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)

theorem main (hT : Trans) (N : ℕ) : TAk N := by
  refine Nat.strong_induction_on N ?_
  intro N ih
  intro n M _ _ ι _ _ E hG hC l hl ℓ hℓ hW P _ _ hN lab C _ col b co hcl htab hinj
  rcases isEmpty_or_nonempty P with hP | ⟨⟨p0⟩⟩
  · exact base lab E l hl ℓ hℓ col b co
  obtain ⟨τ0, hp0⟩ : ∃ τ0, lab p0 = τ0 := ⟨_, rfl⟩
  have hcard : Fintype.card {p : P // ¬ lab p = τ0} < N := by
    rw [← hN]
    exact Fintype.card_subtype_lt (p := fun p => ¬ lab p = τ0) (x := p0) (fun h => h hp0)
  obtain ⟨S1, hS1, hne1, hev1⟩ := ih _ hcard n M {τ : ι // τ ≠ τ0} (fun τ => E τ) (fun τ => hG τ)
    (fun τ τ' h => hC τ τ' (fun e => h (Subtype.ext e))) (fun τ => l τ) (fun τ => hl τ) ℓ hℓ
    (fun τ => hW τ) {p : P // ¬ lab p = τ0} rfl (labR lab τ0) C (fun p => col p) (fun p => b p)
    (fun p => co p) (fun p q h => Subtype.ext (hcl p q h))
    ⟨fun p q h1 h2 => Subtype.ext (htab.1 _ _ h1 h2), fun p i hi => by
      obtain ⟨r, hr1, hr2⟩ := htab.2 p i hi
      exact ⟨⟨r, by rw [hcl r p hr1]; exact p.2⟩, hr1, hr2⟩⟩
    (fun p q h1 h2 => Subtype.ext (hinj _ _ h1 h2))
  unfold envAlg at hS1
  have hWh1 : IsWh (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c))
      (ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) := by
    obtain ⟨ψ, h1, h2, h3⟩ := hW τ0
    refine ⟨ψ, h1, h2, fun a c hac => ?_⟩
    have hcomm : Commute S1 (lift (E τ0 a c)) := comm_of_mem_adjoin hS1 (by
      rintro T ⟨τ, c', d', rfl⟩
      exact tE_comm_lift _ _ _ (fun x y => hC τ τ0 τ.2 x y a c) c' d')
    have e2 := cA_lift (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) (E τ0 a c)
    apply LinearMap.ext
    intro F
    have := LinearMap.congr_fun hcomm.eq F
    have h3' := LinearMap.congr_fun (h3 a c hac)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply] at this h3' ⊢
    rw [this, ← LinearMap.comp_apply (cA _ _) (lift _), e2, LinearMap.comp_apply, h3']
  have hWh1' := hWh1
  obtain ⟨S0, hS0, hne0, hev0⟩ := hT n (TV n M {p : P // ¬ lab p = τ0})
    (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c))
    (by have := glRel_map (liftA n M {p : P // ¬ lab p = τ0}) (E τ0) (hG τ0); simpa only [liftA_apply] using this)
    (l τ0) (qdet_lift _ _ (hl τ0)) _ hne1 hWh1 {p : P // lab p = τ0} C (fun p => col p) (fun p => b p) (fun p => co p)
    ⟨fun p q h1 h2 => Subtype.ext (htab.1 _ _ h1 h2), fun p i hi => by
      obtain ⟨r, hr1, hr2⟩ := htab.2 p i hi
      exact ⟨⟨r, by rw [hcl r p hr1]; exact p.2⟩, hr1, hr2⟩⟩
    (fun p q h1 h2 => Subtype.ext (hinj _ _ h1 h2))
  unfold envAlg at hS0
  have hcAl : ∀ (B : Module.End ℂ (TV n M {p : P // ¬ lab p = τ0})) (z : TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}),
      cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) (lift B z) = B (cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) z) := fun B z => LinearMap.congr_fun (cA_lift _ _ B) z
  have hkey : ∀ Y : Module.End ℂ (TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}),
      (ℓ ∘ₗ cA col b ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0)) ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) Y =
        (((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ Y) ∘ₗ (spl (n := n) (M := M) (fun p : P => lab p = τ0)).toLinearMap := by
    intro Y
    apply LinearMap.ext
    intro F
    simp only [LinearMap.comp_apply, cj_apply, LinearEquiv.apply_symm_apply, Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [cA_split (fun p => lab p = τ0) col (fun p p' h => by rw [hcl p p' h]) b]
    simp only [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
    rw [hcAl]
  have hkey0 : ℓ ∘ₗ cA col b ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0) =
        ((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ (spl (n := n) (M := M) (fun p : P => lab p = τ0)).toLinearMap := by
    apply LinearMap.ext
    intro F
    simp only [LinearMap.comp_apply, cj_apply, LinearEquiv.apply_symm_apply, Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [cA_split (fun p => lab p = τ0) col (fun p p' h => by rw [hcl p p' h]) b]
    simp only [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
    rw [hcAl]
  refine ⟨cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0), ?_, ?_, ?_⟩
  · unfold envAlg
    rw [map_mul]
    apply Subalgebra.mul_mem
    · have hsub : Algebra.adjoin ℂ {T : Module.End ℂ (TV n M {p : P // ¬ lab p = τ0}) | ∃ (τ : {τ : ι // τ ≠ τ0}) (a c : Fin n),
          T = tE (fib (labR lab τ0) τ) (E τ) a c} ≤
          (Algebra.adjoin ℂ {T : Module.End ℂ (TV n M P) | ∃ (τ : ι) (a c : Fin n), T = tE (fib lab τ) (E τ) a c}).comap
            ((cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))).comp (liftA n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0})) := by
        apply Algebra.adjoin_le
        rintro T ⟨τ, c, d, rfl⟩
        simp only [SetLike.mem_coe, Subalgebra.mem_comap, AlgHom.comp_apply, liftA_apply]
        rw [conj_tensor_entry_fibre]
        exact Algebra.subset_adjoin ⟨τ, c, d, rfl⟩
      have := hsub hS1
      simpa only [Subalgebra.mem_comap, AlgHom.comp_apply, liftA_apply] using this
    · have hsub : Algebra.adjoin ℂ {T : Module.End ℂ (TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}) | ∃ (_ : Unit) (a c : Fin n),
          T = tE Finset.univ (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c)) a c} ≤
          (Algebra.adjoin ℂ {T : Module.End ℂ (TV n M P) | ∃ (τ : ι) (a c : Fin n), T = tE (fib lab τ) (E τ) a c}).comap
            (cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))) := by
        apply Algebra.adjoin_le
        rintro T ⟨_, c, d, rfl⟩
        simp only [SetLike.mem_coe, Subalgebra.mem_comap]
        rw [conj_tensor_entry_base]
        exact Algebra.subset_adjoin ⟨τ0, c, d, rfl⟩
      exact hsub hS0
  · rw [hkey0]
    intro h
    apply hne0
    apply LinearMap.ext
    intro G
    have := LinearMap.congr_fun h ((spl (n := n) (M := M) (fun p : P => lab p = τ0)).symm G)
    simpa using this
  · intro τ u
    by_cases hτ : τ = τ0
    · subst hτ
      have hq : qdet (tE (fib lab τ) (E τ)) u =
          cj (spl (n := n) (M := M) (fun p : P => lab p = τ)) (qdet (tE Finset.univ (fun a c => lift (P := {p : P // ¬ lab p = τ}) (E τ a c))) u) := by
        rw [qdet_map']
        simp only [conj_tensor_entry_base]
      rw [hq, hkey, hev0 u, LinearMap.smul_comp, ← hkey0]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      congr 2
      exact card_sub (fun p : P => lab p = τ) (fun p => co p = k)
    · have hq : qdet (tE (fib lab τ) (E τ)) u =
          cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) := by
        have := qdet_map' ((cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))).comp (liftA n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0})) (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u
        simp only [AlgHom.comp_apply, liftA_apply, conj_tensor_entry_fibre] at this
        exact this.symm
      have hcQ : Commute S0 (lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) :=
        comm_of_mem_adjoin hS0 (by
          rintro T ⟨_, c, d, rfl⟩
          exact tE_comm_lift _ _ _ (fun x y => (qdet_commute _ u _ (fun a' c' =>
            tE_comm_lift _ _ _ (fun x' y' => hC τ τ0 hτ x' y' x y) a' c')).symm) c d)
      have hmid : (((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) =
          ((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0 := by
        apply LinearMap.ext
        intro F
        have := LinearMap.congr_fun hcQ.eq F
        simp only [LinearMap.comp_apply, Module.End.mul_apply] at this ⊢
        rw [this, hcAl]
      rw [hq, hkey, hmid, hev1 ⟨τ, hτ⟩ u, LinearMap.smul_comp, LinearMap.smul_comp, ← hkey0]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      rw [card_R]

end TA

theorem transAll_of (_h1 : TensorGl) (h2 : Trans) : TransAll := by
  intro n M _ _ ι _ _ E hE hC l hl ℓ hℓ hW P _ _ lab C _ col b co h1' h2' h3'
  exact TA.main h2 (Fintype.card P) n M ι E hE hC l hl ℓ hℓ hW P rfl lab C col b co h1' h2' h3'

end PositivityTheory.Rg.Cz

end
