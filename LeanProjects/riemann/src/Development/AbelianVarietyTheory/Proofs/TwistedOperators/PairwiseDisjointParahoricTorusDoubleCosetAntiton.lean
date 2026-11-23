import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.CellDisjoint

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def reix {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m) :
    GL n k →* GL m k :=
  Units.map (Matrix.reindexAlgEquiv k k e).toAlgHom.toMonoidHom

theorem reix_val {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : GL n k) : (reix e g).1 = g.1.submatrix e.symm e.symm := rfl

theorem reix_mem_KO {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    {g : GL n k} (hg : g ∈ KO k n) : reix e g ∈ KO k m := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨Units.map (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] e).toAlgHom.toMonoidHom h, Units.ext ?_⟩
  ext i j
  rfl

theorem reix_torusElt {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (ϖ : kˣ) (f : n → ℤ) : reix e (torusElt k n ϖ f) = torusElt k m ϖ (f ∘ e.symm) := by
  ext1
  rw [reix_val, val_torusElt, val_torusElt, submatrix_diagonal_equiv]
  rfl

theorem perm_of_eq {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (a b : Fin N → ℤ)
    (x y : GL (Fin N) k) (hx : x ∈ KO k (Fin N)) (hy : y ∈ KO k (Fin N))
    (h : x * torusElt k (Fin N) ϖ a * y = torusElt k (Fin N) ϖ b) :
    List.Perm (List.ofFn a) (List.ofFn b) := by
  let σ := Tuple.sort (fun i => -a i)
  let τ := Tuple.sort (fun i => -b i)
  have ha : Antitone (a ∘ σ) := fun i j hij => by
    have := Tuple.monotone_sort (fun i => -a i) hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  have hb : Antitone (b ∘ τ) := fun i j hij => by
    have := Tuple.monotone_sort (fun i => -b i) hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  obtain ⟨S₁, h₁, e₁⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] σ.symm
  obtain ⟨S₂, h₂, e₂⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] σ
  obtain ⟨T₁, h₃, e₃⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] τ.symm
  obtain ⟨T₂, h₄, e₄⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] τ
  have hA : torusElt k (Fin N) ϖ a = S₁ * torusElt k (Fin N) ϖ (a ∘ σ) * S₂ := by
    ext1
    simp only [Units.val_mul, val_torusElt, e₁, e₂]
    exact Formalism.UG.P.cartan_diag_perm (fun i => (ϖ : k) ^ a i) σ
  have hB : torusElt k (Fin N) ϖ b = T₁ * torusElt k (Fin N) ϖ (b ∘ τ) * T₂ := by
    ext1
    simp only [Units.val_mul, val_torusElt, e₃, e₄]
    exact Formalism.UG.P.cartan_diag_perm (fun i => (ϖ : k) ^ b i) τ
  have E : (T₁⁻¹ * x * S₁) * torusElt k (Fin N) ϖ (a ∘ σ) * (S₂ * y * T₂⁻¹) =
      torusElt k (Fin N) ϖ (b ∘ τ) := by
    have h' : torusElt k (Fin N) ϖ (b ∘ τ) = T₁⁻¹ * torusElt k (Fin N) ϖ b * T₂⁻¹ := by
      rw [hB]; group
    rw [h', ← h, hA]; group
  have hab : a ∘ σ = b ∘ τ := by
    refine Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
      (hϖ ▸ uniformizer_lt_one) (a ∘ σ) (b ∘ τ) ha hb (T₁⁻¹ * x * S₁)
      (mul_mem (mul_mem (inv_mem h₃) hx) h₁) (S₂ * y * T₂⁻¹) (mul_mem (mul_mem h₂ hy) (inv_mem h₄)) ?_
    have := congrArg Units.val E
    simp only [Units.val_mul, val_torusElt] at this
    simpa only [Units.val_mul, Matrix.mul_assoc] using this
  exact (Equiv.Perm.ofFn_comp_perm σ a).symm.trans (hab ▸ Equiv.Perm.ofFn_comp_perm τ b)

end GlobalTheory.CellDisjoint

namespace GlobalTheory.CellDisjoint

theorem dcell_pairwise_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (r l t : ℕ),
    Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t a b hab
  refine Set.disjoint_left.2 fun g ha hb => hab (Subtype.ext ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 ha
  obtain ⟨x', hx', y', hy', e⟩ := DoubleCoset.mem_doubleCoset.1 hb
  have hK : ∀ z : GL (Fin r ⊕ Blocks l t) k, z ∈ (parahoric k (Fin r) (Blocks l t) : Set _) →
      z ∈ KO k (Fin r ⊕ Blocks l t) := fun z hz => (mem_parahoric.1 hz).1
  have e' : (x'⁻¹ * x) * mtor ϖ (a.1 ∘ (blkEquiv l t).symm) * (y * y'⁻¹) =
      mtor ϖ (b.1 ∘ (blkEquiv l t).symm) := by
    calc _ = x'⁻¹ * (x * mtor ϖ (a.1 ∘ (blkEquiv l t).symm) * y) * y'⁻¹ := by group
      _ = _ := by rw [e]; group
  let ρ : Fin (r + l * t) ≃ Fin r ⊕ Blocks l t :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin r)) (blkEquiv l t))
  have hρ : ∀ f : Fin (l * t) → ℤ,
      (Sum.elim (0 : Fin r → ℤ) (f ∘ (blkEquiv l t).symm)) ∘ ρ.symm.symm = Fin.append (0 : Fin r → ℤ) f := by
    intro f
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [ρ]
    · simp [ρ]
  have e'' := congrArg (reix (k := k) ρ.symm) e'
  simp only [map_mul, mtor, reix_torusElt, hρ] at e''
  have hp := perm_of_eq hϖ _ _ _ _ (mul_mem (reix_mem_KO _ (inv_mem (hK _ hx'))) (reix_mem_KO _ (hK _ hx)))
    (mul_mem (reix_mem_KO _ (hK _ hy)) (reix_mem_KO _ (inv_mem (hK _ hy')))) e''
  rw [List.ofFn_fin_append, List.ofFn_fin_append, List.perm_append_left_iff] at hp
  exact List.ofFn_injective (List.Perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.2 a.2)
    (List.sortedGE_ofFn_iff.2 b.2) hp)

end GlobalTheory.CellDisjoint
