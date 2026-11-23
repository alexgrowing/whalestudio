import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem finrank_quotient_le_of_forall_dependent_mod {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]
    (g : ℕ) (U : Submodule F V)
    (h : ∀ z : Fin (g + 1) → V, ∃ c : Fin (g + 1) → F, c ≠ 0 ∧ ∑ i, c i • z i ∈ U) :
    Module.finrank F (V ⧸ U) ≤ g := by
  by_contra hlt
  push_neg at hlt
  let b := Module.finBasis F (V ⧸ U)
  let y : Fin (g + 1) → V ⧸ U := fun i => b (Fin.castLE hlt i)
  have hli : LinearIndependent F y := b.linearIndependent.comp _ (Fin.castLE_injective hlt)
  choose z hz using fun i => U.mkQ_surjective (y i)
  obtain ⟨c, hc0, hc⟩ := h z
  have hsum : ∑ i, c i • y i = 0 := by
    have : U.mkQ (∑ i, c i • z i) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hc
    simpa [map_sum, map_smul, hz] using this
  exact hc0 (funext fun i => Fintype.linearIndependent_iff.1 hli c hsum i)

private theorem exists_spanning_family_of_finrank_le {F V : Type} [Field F] [AddCommGroup V] [Module F V] (N : ℕ)
    (C : Submodule F V) [Module.Finite F C] (h : Module.finrank F C ≤ N) :
    ∃ ψ : Fin N → V, (∀ i, ψ i ∈ C) ∧ C ≤ Submodule.span F (Set.range ψ) := by
  classical
  let b := Module.finBasis F C
  refine ⟨fun i => if hi : (i : ℕ) < Module.finrank F C then (b ⟨i, hi⟩ : V) else 0, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact (b _).2
    · exact C.zero_mem
  · intro f hf
    have hf' : f = ∑ k, b.repr ⟨f, hf⟩ k • (b k : V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨f, hf⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hf']
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨k, lt_of_lt_of_le k.2 h⟩, ?_⟩)
    simp [k.2]

theorem UpperTheory.V.Pa.linAlg :
    ∀ (F T : Type) [Field F] [AddCommGroup T] [Module F T] [Module.Finite F T] (g D0 : ℕ) (U : Submodule F (Fin g → T)), (∀ z : Fin (g + 1) → Fin g → T, ∃ c : Fin (g + 1) → F, c ≠ 0 ∧ ∑ i, c i • z i ∈ U) → (∀ (e : ℕ) (α : Fin e → T), LinearIndependent F α → (∀ i j, Pi.single j (α i) ∈ U) → e + g * g ≤ D0) → ∃ (X : Fin D0 → Module.Dual F T) (c : Fin g × Fin g → Fin D0 → F), Submodule.span F (Set.range X) = ⊤ ∧ LinearIndependent F c ∧ ∀ a ∈ U, ∀ i, ∑ j, ∑ k, c (i, j) k * X k (a j) = 0 := by
  intro F T _ _ _ _ g D0 U h1 h2
  classical
  have hAdim : Module.finrank F U.dualAnnihilator ≤ g := by
    have e1 := finrank_quotient_le_of_forall_dependent_mod g U h1
    have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq U
    have e3 := Submodule.finrank_quotient_add_finrank U
    omega
  obtain ⟨Φ, hΦA, hΦspan⟩ := exists_spanning_family_of_finrank_le g U.dualAnnihilator hAdim
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin g → Fin g → Module.Dual F T, ∀ i j t, φ i j t = Φ i (Pi.single j t) :=
    ⟨fun i j => (Φ i).comp (LinearMap.single F (fun _ : Fin g => T) j), fun i j t => rfl⟩
  have hrow : ∀ a ∈ U, ∀ i, ∑ j, φ i j (a j) = 0 := by
    intro a ha i
    simp only [hφ]
    rw [← map_sum, Finset.univ_sum_single]
    exact (Submodule.mem_dualAnnihilator _).1 (hΦA i) a ha
  set W : Submodule F T := ⨅ j : Fin g, U.comap (LinearMap.single F (fun _ : Fin g => T) j) with hWdef
  have hW : Module.finrank F W + g * g ≤ D0 := by
    let bW := Module.finBasis F W
    refine h2 _ (fun k => (bW k : T)) ?_ ?_
    · exact bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    · intro k j
      have hmem : (bW k : T) ∈ ⨅ j : Fin g, U.comap (LinearMap.single F (fun _ : Fin g => T) j) :=
        (bW k).2
      rw [Submodule.mem_iInf] at hmem
      exact hmem j
  set S : Submodule F (Module.Dual F T) :=
    Submodule.span F (Set.range fun p : Fin g × Fin g => φ p.1 p.2) with hSdef
  have hSco : S.dualCoannihilator ≤ W := by
    intro t ht
    rw [Submodule.mem_dualCoannihilator] at ht
    rw [hWdef, Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_comap, ← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U),
      Submodule.mem_dualCoannihilator]
    intro f hf
    have hle : Submodule.span F (Set.range Φ) ≤ LinearMap.ker
        (Module.Dual.eval F (Fin g → T) (LinearMap.single F (fun _ : Fin g => T) j t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      have := ht _ (Submodule.subset_span ⟨(i, j), rfl⟩)
      simpa [hφ] using this
    have := hle (hΦspan hf)
    simpa using this
  have hSrank : Module.finrank F T ≤ Module.finrank F S + Module.finrank F W := by
    have e1 := Subspace.finrank_add_finrank_dualCoannihilator_eq S
    have e2 := Submodule.finrank_mono hSco
    omega
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  have hCdim : Module.finrank F C ≤ D0 - g * g := by
    have e1 := Submodule.finrank_add_eq_of_isCompl hC
    have e2 : Module.finrank F (Module.Dual F T) = Module.finrank F T := Subspace.dual_finrank_eq
    omega
  obtain ⟨ψ, -, hψspan⟩ := exists_spanning_family_of_finrank_le (D0 - g * g) C hCdim
  have hgD : g * g ≤ D0 := le_trans (Nat.le_add_left _ _) hW
  let e : Fin D0 ≃ Fin (g * g) ⊕ Fin (D0 - g * g) := (finCongr (by omega)).trans finSumFinEquiv.symm
  let κ : Fin g × Fin g → Fin D0 := fun p => e.symm (Sum.inl (finProdFinEquiv p))
  have hκ : Function.Injective κ := fun p q hpq =>
    finProdFinEquiv.injective (Sum.inl_injective (e.symm.injective hpq))
  let X : Fin D0 → Module.Dual F T := fun k =>
    Sum.elim (fun m => φ (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) ψ (e k)
  have hXκ : ∀ p, X (κ p) = φ p.1 p.2 := by
    intro p
    simp only [X, κ, Equiv.apply_symm_apply, Sum.elim_inl, Equiv.symm_apply_apply]
  refine ⟨X, fun p => Pi.basisFun F (Fin D0) (κ p), ?_,
    (Pi.basisFun F (Fin D0)).linearIndependent.comp κ hκ, ?_⟩
  · rw [eq_top_iff, ← hC.sup_eq_top, sup_le_iff]
    constructor
    · rw [hSdef, Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨κ p, by simp only [hXκ]⟩
    · refine le_trans hψspan (Submodule.span_mono ?_)
      rintro _ ⟨m, rfl⟩
      refine ⟨e.symm (Sum.inr m), ?_⟩
      simp only [X, Equiv.apply_symm_apply, Sum.elim_inr]
  · intro a ha i
    rw [← hrow a ha i]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.basisFun_apply, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hXκ]
