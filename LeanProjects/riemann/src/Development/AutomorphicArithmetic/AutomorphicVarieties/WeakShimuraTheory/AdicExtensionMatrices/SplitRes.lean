import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem split_r {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (b : O →+* R) (g : Γ) :
    (Φ.split b).r g = Matrix.diagonal fun i => b (Φ.χ i g) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Fr.split, mapRep, diagRep]
  · simp [Fr.split, mapRep, diagRep, Matrix.diagonal_apply_ne _ h]

private theorem split_conj {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (b : O →+* R) (v : Φ.ι)
    (g : Γ) : adj ((Φ.split b).n v) * (Φ.split b).r g * (Φ.split b).n v = Matrix.diagonal fun i => b (Φ.χ i g) := by
  show adj 1 * _ * 1 = _
  rw [(grp R).2.2.2.2.1, one_mul, mul_one, split_r]

private theorem adj_diag {R : Type} [CommRing R] (d : Fin 4 → R) :
    adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
  ext i j
  rw [adj_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    fin_cases i <;> simp [sgn]
  · rw [Matrix.diagonal_apply_ne _ h,
      Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), smul_zero]

private theorem res_self {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsCO Λ (ResidueField Λ)] (x : ResidueField Λ) :
    res Λ (ResidueField Λ) x = x := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  have := (res Λ (ResidueField Λ)).commutes a
  rwa [IsLocalRing.ResidueField.algebraMap_eq] at this

theorem UpperTheory.V.Ws.sxSplitRes :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Φ : Fr O Γ} {l : ℕ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} [IsCO Λ (ResidueField Λ)], Φ.Std l a → Φ.IsRes ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) ∧ Φ.Lifts a (Φ.split ((residue Λ).comp a)) (Φ.split ((residue Λ).comp a)) := by
  intro O Γ _ _ _ _ Φ l Λ _ _ a _ hs
  have ok := hs.ok
  have hψ : ∀ v i s, (Φ.split ((residue Λ).comp a)).ψ v i s = (residue Λ).comp a (Φ.χ i s) := by
    intro v i s
    unfold PD.ψ
    rw [split_conj, Matrix.diagonal_apply_eq]
  have hpair : Φ.IsPair ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) := by
    refine ⟨fun g => ?_, fun g hg => ?_, ?_, fun v => ?_, fun v s _ => ?_, fun v s hs' i => ?_⟩
    · show adj _ * _ = _
      rw [split_r, adj_diag, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        rw [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
          ← map_mul, ← Units.val_mul, mul_comm, ok.mul]
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    · rw [split_r, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact ok.kill g hg i
    · rw [split_r]
      exact Matrix.isDiag_diagonal _
    · show IsLow (1 : M4 (ResidueField Λ))
      refine ⟨?_, fun i => Matrix.one_apply_eq i, fun i j hij => Matrix.one_apply_ne hij.ne⟩
      show adj 1 * 1 = (1 : ResidueField Λ) • 1
      rw [(grp _).2.2.2.2.1, mul_one, one_smul]
    · rw [split_conj]
      intro i j hji
      exact Matrix.diagonal_apply_ne _ hji.ne'
    · rw [hψ]
      exact (hs.mu v s hs').2 i
  have hres : Φ.Res ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) :=
    ⟨fun g i => by rw [split_r, Matrix.diagonal_apply_eq], fun v s _ i => hψ v i s,
      Or.inr fun g i j hij _ => by rw [split_r, Matrix.diagonal_apply_ne _ hij]⟩
  have hcont : ∀ I, (Φ.split ((residue Λ).comp a)).Cont I := by
    intro I i j N
    by_cases h : i = j
    · subst h
      simp only [split_r, Matrix.diagonal_apply_eq]
      exact (ok.lc i).comp _
    · simp only [split_r, Matrix.diagonal_apply_ne _ h, map_zero]
      exact IsLocallyConstant.const _
  refine ⟨⟨hpair, hres, hcont ⊥⟩, ⟨?_, hcont _, ?_⟩⟩
  · rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact hpair
  · apply PD.ext
    · exact MonoidHom.ext fun g => Matrix.ext fun i j => res_self _
    · funext v
      exact Matrix.ext fun i j => res_self _
