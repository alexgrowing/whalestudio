import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GrMIff

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_gco :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (B : Box F 3 C) (π : F.V → Fin 3 → ZMod 2) (D : SetLift p B), D.Gr σ' π → ∀ j, ∀ u ∈ formp σ' (RingHom.ker p) j, (∀ x, (D.co u).1 x ∈ adp (ResidueField O) j) ∧ ∀ v s, (D.co u).2 v s ∈ adp (ResidueField O) j := by
  intro l _ k _ F O _ _ C' _ _ _ C _ _ p σ' B π D hD j u hu
  have hu' : ∀ i, i ≠ j → ∀ y : RingHom.ker p, (y : C') ∈ evp σ' i → u y = 0 := hu
  have key : ∀ M : Matrix (Fin 3) (Fin 3) C', GrM σ' pq pq M →
      M.map (evK (RingHom.ker p) u) ∈ adp (ResidueField O) j := by
    intro M hM
    change ∀ a b, pw a b ≠ j → M.map (evK (RingHom.ker p) u) a b = 0
    intro a b hab
    rw [Matrix.map_apply]
    have hmem := hM a b
    rw [← pw_eq] at hmem
    unfold evK
    split_ifs with hk
    · exact hu' (pw a b) hab ⟨M a b, hk⟩ hmem
    · rfl
  obtain ⟨h1, hsub, hmul, hinv, hsgn⟩ := ep_grm σ'
  refine ⟨fun x => ?_, fun v s => ?_⟩
  · refine key (D.om x) ?_
    unfold SetLift.om
    rw [Units.val_mul, Units.val_mul]
    exact hsub _ _ _ _ (hmul _ _ _ _ _ (hmul _ _ _ _ _ (hD.r x.1) (hsgn _ _ (hD.r x.2)))
      (hinv _ _ _ (hD.r (x.1 * x.2)))) (h1 pq)
  · have hX : GrM σ' pq pq ↑((D.g v)⁻¹ * D.t v s * D.g v) := by
      rw [Units.val_mul, Units.val_mul]
      exact hmul _ _ _ _ _ (hmul _ _ _ _ _ (hinv _ _ _ (hD.g v)) (hD.t v s)) (hD.g v)
    refine key (D.a v s) ?_
    unfold SetLift.a
    rw [Units.val_mul]
    exact hsub _ _ _ _ (hmul _ _ _ _ _ (hD.r _) (hinv _ _ _ hX)) (h1 pq)
