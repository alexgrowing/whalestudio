import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {k : Type} [Field k] {n : ℕ}

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}

theorem Frame.card_index {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k} (F : Frame Z M L R o N v) :
    Fintype.card (Σ m, L m × (Σ a : F.ι m, Fin (F.l m a))) = n := by
  rw [← Module.finrank_eq_card_basis F.β, Module.finrank_fin_fun]

theorem Frame.l_le [∀ m, Nonempty (L m)] {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k}
    (F : Frame Z M L R o N v) (m : M) (a : F.ι m) : F.l m a ≤ n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (L m))
  have hinj : Function.Injective (fun i : Fin (F.l m a) =>
      (⟨m, (p, ⟨a, i⟩)⟩ : Σ m, L m × (Σ a : F.ι m, Fin (F.l m a)))) := by
    intro i j h
    have h1 := sigma_mk_injective h
    have h2 := sigma_mk_injective (Prod.ext_iff.mp h1).2
    exact h2
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, F.card_index] at this
  exact this

theorem Frame.card_le [∀ m, Nonempty (L m)] {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k}
    (F : Frame Z M L R o N v) (m : M) : Nat.card (F.ι m) ≤ n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (L m))
  have hinj : Function.Injective (fun a : F.ι m =>
      (⟨m, (p, ⟨a, ⟨0, F.hl m a⟩⟩)⟩ : Σ m, L m × (Σ a : F.ι m, Fin (F.l m a)))) := by
    intro a b h
    have h1 := sigma_mk_injective h
    have h2 := (Prod.ext_iff.mp h1).2
    exact congrArg Sigma.fst h2
  have := Fintype.card_le_of_injective _ hinj
  rw [F.card_index] at this
  rw [Nat.card_eq_fintype_card]
  exact this

theorem exists_equiv_ls [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) (m : M) :
    ∃ e : F₁.ι m ≃ F₂.ι m, ∀ a, F₂.l m (e a) = F₁.l m a ∧ F₂.s m (e a) = F₁.s m a := by
  have hf : ∀ c : ℕ × ℕ, Nonempty ({a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} ≃
      {b : F₂.ι m // (F₂.l m b, F₂.s m b) = c}) := by
    intro c
    rw [← Finite.card_eq]
    by_cases hc : c.1 ≤ n ∧ c.2 ≤ n
    · have e1 : {a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} ≃ {a : F₁.ι m // F₁.l m a = c.1 ∧ F₁.s m a = c.2} :=
        Equiv.subtypeEquivRight (fun a => Prod.ext_iff)
      have e2 : {a : F₂.ι m // (F₂.l m a, F₂.s m a) = c} ≃ {a : F₂.ι m // F₂.l m a = c.1 ∧ F₂.s m a = c.2} :=
        Equiv.subtypeEquivRight (fun a => Prod.ext_iff)
      rw [Nat.card_congr e1, Nat.card_congr e2]
      exact h m c.1 c.2 hc.1 hc.2
    · have hE1 : IsEmpty {a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} := by
        refine ⟨fun ⟨a, ha⟩ => hc ?_⟩
        rw [← ha]
        exact ⟨F₁.l_le m a, (F₁.hs m a).trans (F₁.l_le m a)⟩
      have hE2 : IsEmpty {a : F₂.ι m // (F₂.l m a, F₂.s m a) = c} := by
        refine ⟨fun ⟨a, ha⟩ => hc ?_⟩
        rw [← ha]
        exact ⟨F₂.l_le m a, (F₂.hs m a).trans (F₂.l_le m a)⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]
  let e := fun c => (hf c).some
  refine ⟨Equiv.ofFiberEquiv (fun c => e c), fun a => ?_⟩
  have := Equiv.ofFiberEquiv_map (f := fun a => (F₁.l m a, F₁.s m a)) (g := fun b => (F₂.l m b, F₂.s m b))
    (fun c => e c) a
  exact Prod.ext_iff.mp this

theorem conj_of_frames [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) :
    ∃ g : GL (Fin n) k, (∀ a ∈ Z, a * g.val = g.val * a) ∧ g.val * N₁ = N₂ * g.val ∧ g.val *ᵥ v₁ = v₂ := by
  choose σ hσ using exists_equiv_ls F₁ F₂ h
  let ψ : ∀ m, (Σ a : F₁.ι m, Fin (F₁.l m a)) ≃ (Σ b : F₂.ι m, Fin (F₂.l m b)) := fun m =>
    Equiv.sigmaCongr (σ m) (fun a => finCongr (hσ m a).1.symm)
  have hψ : ∀ m (a : F₁.ι m) (i : Fin (F₁.l m a)), ψ m ⟨a, i⟩ = ⟨σ m a, Fin.cast (hσ m a).1.symm i⟩ := by
    intro m a i
    rfl
  let Φ : (Σ m, L m × (Σ a : F₁.ι m, Fin (F₁.l m a))) ≃ (Σ m, L m × (Σ b : F₂.ι m, Fin (F₂.l m b))) :=
    Equiv.sigmaCongrRight (fun m => Equiv.prodCongr (Equiv.refl _) (ψ m))
  have hΦ : ∀ m (p : L m) j, Φ ⟨m, (p, j)⟩ = ⟨m, (p, ψ m j)⟩ := fun m p j => rfl
  let g : (Fin n → k) ≃ₗ[k] (Fin n → k) := F₁.β.equiv F₂.β Φ
  have hg : ∀ j, g (F₁.β j) = F₂.β (Φ j) := fun j => Module.Basis.equiv_apply _ _ _ _
  let G : GL (Fin n) k := ⟨LinearMap.toMatrix' (g : (Fin n → k) →ₗ[k] (Fin n → k)),
    LinearMap.toMatrix' (g.symm : (Fin n → k) →ₗ[k] (Fin n → k)),
    by rw [← LinearMap.toMatrix'_comp]; convert LinearMap.toMatrix'_id; ext x; simp,
    by rw [← LinearMap.toMatrix'_comp]; convert LinearMap.toMatrix'_id; ext x; simp⟩
  have hGv : ∀ x, G.val *ᵥ x = g x := fun x => LinearMap.toMatrix'_mulVec _ x

  have hext : ∀ X Y : Matrix (Fin n) (Fin n) k, (∀ j, X *ᵥ F₁.β j = Y *ᵥ F₁.β j) → X = Y := by
    intro X Y hXY
    apply Matrix.toLin'.injective
    apply F₁.β.ext
    intro j
    simp only [Matrix.toLin'_apply]
    exact hXY j
  refine ⟨G, ?_, ?_, ?_⟩
  · intro a ha
    apply hext
    rintro ⟨m, p, j⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGv, hg, hΦ]
    have h1 := F₂.hZ ⟨a, ha⟩ m p (ψ m j)
    have h2 := F₁.hZ ⟨a, ha⟩ m p j
    simp only at h1 h2
    rw [h1, h2, hGv, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, hg, hΦ]
  · apply hext
    rintro ⟨m, p, a, i⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F₁.hN]
    simp only [hGv]
    rw [hg, hΦ, hψ, F₂.hN]
    simp only [Fin.val_cast]
    by_cases hi : (i : ℕ) + 1 < F₁.l m a
    · have hi2 : (i : ℕ) + 1 < F₂.l m (σ m a) := by rw [(hσ m a).1]; exact hi
      rw [dif_pos hi, dif_pos hi2, hg, hΦ, hψ]
      rfl
    · have hi2 : ¬ (i : ℕ) + 1 < F₂.l m (σ m a) := by rw [(hσ m a).1]; exact hi
      rw [dif_neg hi, dif_neg hi2, map_zero]
  · rw [hGv, F₁.hv, F₂.hv, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum, ← Equiv.sum_comp (σ m)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : F₁.s m a < F₁.l m a
    · have ha2 : F₂.s m (σ m a) < F₂.l m (σ m a) := by rw [(hσ m a).1, (hσ m a).2]; exact ha
      rw [dif_pos ha, dif_pos ha2, map_smul, hg, hΦ, hψ]
      have hc : (Fin.cast (hσ m a).1.symm ⟨F₁.s m a, ha⟩ : Fin (F₂.l m (σ m a))) = ⟨F₂.s m (σ m a), ha2⟩ :=
        Fin.ext (by simp [(hσ m a).2])
      rw [hc]
    · have ha2 : ¬ F₂.s m (σ m a) < F₂.l m (σ m a) := by rw [(hσ m a).1, (hσ m a).2]; exact ha
      rw [dif_neg ha, dif_neg ha2, map_zero]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
