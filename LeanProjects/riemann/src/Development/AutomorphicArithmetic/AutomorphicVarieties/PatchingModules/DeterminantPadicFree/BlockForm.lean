import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IrredIffSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DensityProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IntertwinerIso

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem finSumFinEquiv_inl_lt_and_inr_not_lt {n a b : ℕ} (hn : n = a + b) (i : Fin n) :
    (∀ p, ((finCongr hn).trans finSumFinEquiv.symm) i = Sum.inl p → (i : ℕ) < a) ∧
    (∀ p, ((finCongr hn).trans finSumFinEquiv.symm) i = Sum.inr p → ¬ (i : ℕ) < a) := by
  constructor
  · intro p hp
    have h := congrArg (fun s => ((finCongr hn).trans finSumFinEquiv.symm).symm s) hp
    simp only [Equiv.symm_apply_apply] at h
    subst h
    simp
  · intro p hp
    have h := congrArg (fun s => ((finCongr hn).trans finSumFinEquiv.symm).symm s) hp
    simp only [Equiv.symm_apply_apply] at h
    subst h
    simp

private theorem submatrix_mem_ev_of_offDiag_blocks_zero {R : Type} [CommRing R] {n a b : ℕ} (hn : n = a + b)
    (Z : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R)
    (h12 : ∀ i j, Z (Sum.inl i) (Sum.inr j) = 0) (h21 : ∀ i j, Z (Sum.inr i) (Sum.inl j) = 0) :
    Z.submatrix ((finCongr hn).trans finSumFinEquiv.symm) ((finCongr hn).trans finSumFinEquiv.symm)
      ∈ Ev R R n a := by
  simp only [Ev, blkMat, Submodule.mem_top, implies_true, Submodule.mem_bot, true_and, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  intro i j hij
  simp only [Matrix.submatrix_apply]
  rcases hi : ((finCongr hn).trans finSumFinEquiv.symm) i with p | p <;>
    rcases hj : ((finCongr hn).trans finSumFinEquiv.symm) j with q | q
  · exact absurd (iff_of_true ((finSumFinEquiv_inl_lt_and_inr_not_lt hn i).1 p hi) ((finSumFinEquiv_inl_lt_and_inr_not_lt hn j).1 q hj)) hij
  · exact h12 p q
  · exact h21 p q
  · exact absurd (iff_of_false ((finSumFinEquiv_inl_lt_and_inr_not_lt hn i).2 p hi) ((finSumFinEquiv_inl_lt_and_inr_not_lt hn j).2 q hj)) hij

private theorem intertwiner_eq_zero_of_span_eq_univ_of_reverse_zero {K Γ : Type} [Field K] {a b : ℕ} (ha : 1 ≤ a)
    (ρ₁ : Γ → Matrix (Fin a) (Fin a) K) (ρ₂ : Γ → Matrix (Fin b) (Fin b) K)
    (s₁ : Submodule.span K (Set.range ρ₁) = ⊤) (s₂ : Submodule.span K (Set.range ρ₂) = ⊤)
    (i₂₁ : ∀ M : Matrix (Fin b) (Fin a) K, (∀ g, M * ρ₁ g = ρ₂ g * M) → M = 0)
    (V : Matrix (Fin a) (Fin b) K) (hV : ∀ g, ρ₁ g * V = V * ρ₂ g) : V = 0 := by
  by_contra hne
  obtain ⟨W, hVW, hWV⟩ := (UpperTheory.V.AlgebraTools.intertwiner_iso ρ₁ ρ₂ s₁ s₂).1 V hV hne
  have hW : W = 0 := by
    apply i₂₁
    intro g
    calc W * ρ₁ g = W * ρ₁ g * (V * W) := by rw [hVW, Matrix.mul_one]
      _ = W * (ρ₁ g * V) * W := by simp only [Matrix.mul_assoc]
      _ = W * (V * ρ₂ g) * W := by rw [hV g]
      _ = (W * V) * ρ₂ g * W := by simp only [Matrix.mul_assoc]
      _ = ρ₂ g * W := by rw [hWV, Matrix.one_mul]
  rw [hW, Matrix.mul_zero] at hVW
  have := congrFun (congrFun hVW ⟨0, ha⟩) ⟨0, ha⟩
  simp at this

private theorem span_range_fromBlocks_submatrix_eq_ev {K Γ : Type} [Field K] [Monoid Γ] {n a b : ℕ} (hn : n = a + b)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ρ₁ : Γ →* Matrix (Fin a) (Fin a) K) (ρ₂ : Γ →* Matrix (Fin b) (Fin b) K)
    (s₁ : Submodule.span K (Set.range ρ₁) = ⊤) (s₂ : Submodule.span K (Set.range ρ₂) = ⊤)
    (i₁₂ : ∀ V : Matrix (Fin a) (Fin b) K, (∀ g, ρ₁ g * V = V * ρ₂ g) → V = 0)
    (i₂₁ : ∀ V : Matrix (Fin b) (Fin a) K, (∀ g, ρ₂ g * V = V * ρ₁ g) → V = 0) :
    Submodule.span K (Set.range fun g => (Matrix.fromBlocks (ρ₁ g) 0 0 (ρ₂ g)).submatrix
      ((finCongr hn).trans finSumFinEquiv.symm) ((finCongr hn).trans finSumFinEquiv.symm)) = Ev K K n a := by
  set τ := (finCongr hn).trans finSumFinEquiv.symm with hτ
  haveI i3 : ∀ s : Bool, Nonempty (Fin (cond s a b)) := fun s => by
    cases s
    · exact ⟨⟨0, hb⟩⟩
    · exact ⟨⟨0, ha⟩⟩
  let ρ : (s : Bool) → Γ →* Matrix (Fin (cond s a b)) (Fin (cond s a b)) K := fun s => match s with
    | false => ρ₂
    | true => ρ₁
  have hspan : ∀ s, Submodule.span K (Set.range (ρ s)) = ⊤ := by
    intro s
    cases s
    · exact s₂
    · exact s₁
  have hint : ∀ s t, s ≠ t → ∀ V : Matrix (Fin (cond s a b)) (Fin (cond t a b)) K, (∀ g, ρ s g * V = V * ρ t g) → V = 0 := by
    intro s t hst
    cases s <;> cases t
    · exact absurd rfl hst
    · exact i₂₁
    · exact i₁₂
    · exact absurd rfl hst
  have hD := UpperTheory.V.AlgebraTools.density_prod (fun s : Bool => Fin (cond s a b)) ρ hspan hint
  let L : ((s : Bool) → Matrix (Fin (cond s a b)) (Fin (cond s a b)) K) →ₗ[K] Matrix (Fin n) (Fin n) K :=
    { toFun := fun f => (Matrix.fromBlocks (f true) 0 0 (f false)).submatrix τ τ
      map_add' := by
        intro f h
        ext i j
        simp only [Matrix.submatrix_apply, Pi.add_apply, Matrix.add_apply]
        rcases τ i with p | p <;> rcases τ j with q | q <;> simp [Matrix.fromBlocks]
      map_smul' := by
        intro c f
        ext i j
        simp only [Matrix.submatrix_apply, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
        rcases τ i with p | p <;> rcases τ j with q | q <;> simp [Matrix.fromBlocks] }
  have hrange : (Set.range fun g => (Matrix.fromBlocks (ρ₁ g) 0 0 (ρ₂ g)).submatrix τ τ) =
      L '' Set.range (fun g s => ρ s g) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, Submodule.span_image, hD, Submodule.map_top]
  ext M
  constructor
  · rintro ⟨f, rfl⟩
    apply submatrix_mem_ev_of_offDiag_blocks_zero hn
    · intro i j
      simp [Matrix.fromBlocks]
    · intro i j
      simp [Matrix.fromBlocks]
  · intro hM
    have hM' := hM
    simp only [Ev, blkMat, Submodule.mem_top, implies_true, Submodule.mem_bot, true_and, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hM'
    let Z := M.submatrix τ.symm τ.symm
    let f : (s : Bool) → Matrix (Fin (cond s a b)) (Fin (cond s a b)) K := fun s => match s with
      | false => Z.toBlocks₂₂
      | true => Z.toBlocks₁₁
    refine ⟨f, ?_⟩
    ext i j
    show (Matrix.fromBlocks Z.toBlocks₁₁ 0 0 Z.toBlocks₂₂) (τ i) (τ j) = M i j
    rcases hi : τ i with p | p <;> rcases hj : τ j with q | q
    · rw [Matrix.fromBlocks_apply₁₁]
      simp only [Z, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply]
      rw [← hi, ← hj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    · have := hM' i j (fun h => ((finSumFinEquiv_inl_lt_and_inr_not_lt hn j).2 q hj) (h.1 ((finSumFinEquiv_inl_lt_and_inr_not_lt hn i).1 p hi)))
      simp [this]
    · have := hM' i j (fun h => ((finSumFinEquiv_inl_lt_and_inr_not_lt hn i).2 p hi) (h.2 ((finSumFinEquiv_inl_lt_and_inr_not_lt hn j).1 q hj)))
      simp [this]
    · rw [Matrix.fromBlocks_apply₂₂]
      simp only [Z, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply]
      rw [← hi, ← hj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private theorem exists_perm_matrix_conj_and_transpose_eq_submatrix {R : Type} [CommRing R] {n : ℕ} (π : Fin n ≃ Fin n) :
    ∃ T : GL (Fin n) R, ∀ M : Matrix (Fin n) (Fin n) R,
      (T : Matrix (Fin n) (Fin n) R) * M * ((T⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = M.submatrix π π ∧
      ((T⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * M * ((T⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
        = M.submatrix π π := by
  have hAM : ∀ M : Matrix (Fin n) (Fin n) R, (1 : Matrix (Fin n) (Fin n) R).submatrix π id * M = M.submatrix π id := by
    intro M
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hMB : ∀ M : Matrix (Fin n) (Fin n) R, M * (1 : Matrix (Fin n) (Fin n) R).submatrix id π = M.submatrix id π := by
    intro M
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hAB : (1 : Matrix (Fin n) (Fin n) R).submatrix π id * (1 : Matrix (Fin n) (Fin n) R).submatrix id π = 1 := by
    rw [hAM]
    ext i j
    simp [Matrix.one_apply]
  have hBA : (1 : Matrix (Fin n) (Fin n) R).submatrix id π * (1 : Matrix (Fin n) (Fin n) R).submatrix π id = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    rw [Equiv.sum_comp π (fun k => (if i = k then (1 : R) else 0) * (if k = j then 1 else 0))]
    simp
  refine ⟨⟨(1 : Matrix (Fin n) (Fin n) R).submatrix π id, (1 : Matrix (Fin n) (Fin n) R).submatrix id π, hAB, hBA⟩, ?_⟩
  intro M
  have hinv : (((⟨(1 : Matrix (Fin n) (Fin n) R).submatrix π id, (1 : Matrix (Fin n) (Fin n) R).submatrix id π, hAB, hBA⟩ :
      GL (Fin n) R)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = (1 : Matrix (Fin n) (Fin n) R).submatrix id π := rfl
  have htr : ((1 : Matrix (Fin n) (Fin n) R).submatrix id π)ᵀ = (1 : Matrix (Fin n) (Fin n) R).submatrix π id := by
    rw [Matrix.transpose_submatrix, Matrix.transpose_one]
  rw [hinv, htr]
  refine ⟨?_, ?_⟩
  · show (1 : Matrix (Fin n) (Fin n) R).submatrix π id * M * (1 : Matrix (Fin n) (Fin n) R).submatrix id π = _
    rw [hAM, hMB]
    rfl
  · rw [hAM, hMB]
    rfl

private theorem intertwiner_eq_zero_of_map_intertwiner_eq_zero {K L Γ : Type} [Field K] [Field L] (f : K →+* L) {m k : Type} [Fintype m]
    [Fintype k] [DecidableEq m] [DecidableEq k] (ρ₁ : Γ → Matrix m m K) (ρ₂ : Γ → Matrix k k K)
    (hL : ∀ V : Matrix m k L, (∀ g, (ρ₁ g).map f * V = V * (ρ₂ g).map f) → V = 0)
    (V : Matrix m k K) (hV : ∀ g, ρ₁ g * V = V * ρ₂ g) : V = 0 := by
  have h0 := hL (V.map f) (by
    intro g
    rw [← Matrix.map_mul, ← Matrix.map_mul, hV g])
  ext i j
  have := congrFun (congrFun h0 i) j
  simpa using this

private theorem reindex_transpose_mul_mul {R : Type} [CommRing R] {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (X Y W : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex e e (Xᵀ * Y * W) = (Matrix.reindex e e X)ᵀ * Matrix.reindex e e Y * Matrix.reindex e e W := by
  simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

private theorem rh_mul_pi_mul_z_eq_pi_mul_z_mul_s {K : Type} [CommRing K] {a b : ℕ} (A Ai P Pi Rh : Matrix (Fin a) (Fin a) K)
    (S : Matrix (Fin b) (Fin b) K) (Z : Matrix (Fin a) (Fin b) K) (hAAi : A * Ai = 1) (hPiP : Pi * P = 1)
    (hPPi : P * Pi = 1) (hf : Aᵀ * P * Rh = P) (hz : Aᵀ * Z * S = Z) : Rh * (Pi * Z) = (Pi * Z) * S := by
  have hT : Aiᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hAAi, Matrix.transpose_one]
  have h1 : P * Rh = Aiᵀ * P := by
    calc P * Rh = (Aiᵀ * Aᵀ) * P * Rh := by rw [hT, Matrix.one_mul]
      _ = Aiᵀ * (Aᵀ * P * Rh) := by simp only [Matrix.mul_assoc]
      _ = Aiᵀ * P := by rw [hf]
  have h2 : Rh = Pi * (Aiᵀ * P) := by
    calc Rh = (Pi * P) * Rh := by rw [hPiP, Matrix.one_mul]
      _ = Pi * (P * Rh) := by rw [Matrix.mul_assoc]
      _ = Pi * (Aiᵀ * P) := by rw [h1]
  calc Rh * (Pi * Z) = Pi * Aiᵀ * (P * Pi) * Z := by rw [h2]; simp only [Matrix.mul_assoc]
    _ = Pi * Aiᵀ * Z := by rw [hPPi, Matrix.mul_one]
    _ = Pi * Aiᵀ * (Aᵀ * Z * S) := by rw [hz]
    _ = Pi * (Aiᵀ * Aᵀ) * Z * S := by simp only [Matrix.mul_assoc]
    _ = (Pi * Z) * S := by rw [hT, Matrix.mul_one]

private theorem eps_eq_one_of_mem_G' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) (hg : g ∈ F.G') : F.eps O R g = 1 := by
  have h : F.ε (g : _) = 1 := by
    simpa only [GFrame.G', MonoidHom.mem_ker, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] using hg
  ext
  simp only [GFrame.eps, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, Units.coe_map,
    MonoidHom.coe_coe, RingHom.coe_comp]
  rw [h]
  simp

private theorem conj_mem_G'_and_conj_conj_eq_of_mem_G' {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) (hg : g ∈ F.G') :
    F.conj g ∈ F.G' ∧ F.conj (F.conj g) = g := by
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_left F.c_sq
  constructor
  · simp only [GFrame.G', MonoidHom.mem_ker, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at hg ⊢
    simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [map_mul, map_mul, hg, mul_one, map_inv, mul_inv_cancel]
  · apply Subtype.ext
    simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hc]
    have h2 : F.c * (F.c * (g : _) * F.c) * F.c = (F.c * F.c) * (g : _) * (F.c * F.c) := by group
    rw [h2, F.c_sq, one_mul, mul_one]

private theorem mem_ev_self_self {R : Type} [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) : M ∈ Ev R R n n := by
  simp only [Ev, blkMat, Submodule.mem_top, implies_true, Submodule.mem_bot, true_and, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  intro i j h
  exact absurd (iff_of_true i.2 j.2) h

theorem UpperTheory.V.Pa.Det.blockForm :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (x : Point r), 0 < n → x.TypeI ∨ x.TypeE → ∃ (a : ℕ) (Q : GL (Fin n) x.Fr), 1 ≤ a ∧ a ≤ n ∧ (x.TypeI → a = n) ∧ (∀ g, ((Q * x.ρF g * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) ∈ Ev x.Fr x.Fr n a) ∧ Submodule.span x.Fr ((fun g => ((Q * x.ρF g * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)) '' (F.G' : Set F.G₀)) = Ev x.Fr x.Fr n a ∧ ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) ∈ Ev x.Fr x.Fr n a := by
  intro l _ F O _ _ _ n r x hn hx
  have hρF : ∀ g, ((x.ρF g : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) =
      ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) := by
    intro g
    simp only [Point.ρF, MonoidHom.coe_comp, Function.comp_apply, GeneralLinearGroup.val_map_apply]
  have hpush : ∀ {k : ℕ} (ρ : F.G₀ →* GL (Fin k) x.Fr) (g : F.G₀),
      mat (pushRep (algebraMap x.Fr x.Fb) ρ) g = (mat ρ g).map (algebraMap x.Fr x.Fb) := by
    intro k ρ g
    simp only [mat, pushRep, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
      GeneralLinearGroup.val_map_apply]
  have hspanFb : ∀ {k : ℕ} (ρ : F.G₀ →* GL (Fin k) x.Fr),
      UpperTheory.V.U3.MatIrr F.G' ⇑(mat (pushRep (algebraMap x.Fr x.Fb) ρ)) →
      Submodule.span x.Fb (Set.range ((mat (pushRep (algebraMap x.Fr x.Fb) ρ)).comp F.G'.subtype)) = ⊤ := by
    intro k ρ hirr
    refine ((UpperTheory.V.AlgebraTools.irred_iff_span (RingHom.id x.Fb) ((mat (pushRep (algebraMap x.Fr x.Fb) ρ)).comp F.G'.subtype)).1.1) ?_
    intro N hN
    apply hirr N
    intro g hg v hv
    exact hN ⟨g, hg⟩ v hv
  by_cases hI : x.TypeI
  · refine ⟨n, 1, hn, le_refl n, fun _ => rfl, fun g => mem_ev_self_self n _, ?_, mem_ev_self_self n _⟩
    simp only [one_mul, inv_one, mul_one]
    rw [Set.image_eq_range]
    have hmem : ∀ i : (F.G' : Set F.G₀), ((x.ρF i : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) ∈ Ev x.Fr x.Fr n n :=
      fun i => mem_ev_self_self n _
    rw [Det.spanDesc (algebraMap x.Fr x.Fb) _ hmem]
    have h1 := hspanFb x.ρF hI
    have h2 : (Set.range fun i : (F.G' : Set F.G₀) =>
        ((x.ρF i : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr).map (algebraMap x.Fr x.Fb)) =
        Set.range ((mat (pushRep (algebraMap x.Fr x.Fb) x.ρF)).comp F.G'.subtype) := by
      ext M
      simp only [Set.mem_range, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hpush]
      rfl
    rw [h2, h1]
    exact (eq_top_iff.2 (fun M _ => mem_ev_self_self n M)).symm

  · have hE : x.TypeE := hx.resolve_left hI
    unfold Point.TypeE at hE
    obtain ⟨a, b, ha, hb, e, Q, r₁, r₂, hQ, ⟨P₁, hP₁⟩, ⟨P₂, hP₂⟩, i₁, i₂, hint⟩ := hE
    have hnab : n = a + b := by simpa using Fintype.card_congr e
    obtain ⟨T, hT⟩ := exists_perm_matrix_conj_and_transpose_eq_submatrix (R := x.Fr) (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm)
    have hsub : ∀ X : Matrix (Fin n) (Fin n) x.Fr,
        X.submatrix (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm)
          (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm)
          = (Matrix.reindex e e X).submatrix ((finCongr hnab).trans finSumFinEquiv.symm)
            ((finCongr hnab).trans finSumFinEquiv.symm) := by
      intro X
      rw [Matrix.reindex_apply, Matrix.submatrix_submatrix]
      rfl
    have hN : ∀ g, (((T * Q) * x.ρF g * (T * Q)⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) =
        (Matrix.fromBlocks (mat r₁ g) 0 0 (mat r₂ g)).submatrix ((finCongr hnab).trans finSumFinEquiv.symm)
          ((finCongr hnab).trans finSumFinEquiv.symm) := by
      intro g
      have h1 : (T * Q) * x.ρF g * (T * Q)⁻¹ = T * (Q * x.ρF g * Q⁻¹) * T⁻¹ := by group
      rw [h1, Units.val_mul, Units.val_mul, (hT _).1, hsub, hQ g]
    have hmemAll : ∀ g, (((T * Q) * x.ρF g * (T * Q)⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)
        ∈ Ev x.Fr x.Fr n a := by
      intro g
      rw [hN]
      apply submatrix_mem_ev_of_offDiag_blocks_zero hnab
      · intro i j
        simp
      · intro i j
        simp
    let ρ₁' := (mat (pushRep (algebraMap x.Fr x.Fb) r₁)).comp F.G'.subtype
    let ρ₂' := (mat (pushRep (algebraMap x.Fr x.Fb) r₂)).comp F.G'.subtype
    have s₁ := hspanFb r₁ i₁
    have s₂ := hspanFb r₂ i₂
    have i₂₁' : ∀ V : Matrix (Fin b) (Fin a) x.Fb, (∀ g, ρ₂' g * V = V * ρ₁' g) → V = 0 :=
      fun V hV => hint V (fun g hg => (hV ⟨g, hg⟩).symm)
    have i₁₂' : ∀ V : Matrix (Fin a) (Fin b) x.Fb, (∀ g, ρ₁' g * V = V * ρ₂' g) → V = 0 :=
      fun V hV => intertwiner_eq_zero_of_span_eq_univ_of_reverse_zero ha ⇑ρ₁' ⇑ρ₂' s₁ s₂ (fun M hM => hint M (fun g hg => hM ⟨g, hg⟩)) V hV
    refine ⟨a, T * Q, ha, by omega, fun h => absurd h hI, hmemAll, ?_, ?_⟩
    · rw [Set.image_eq_range]
      have hmem : ∀ i : (F.G' : Set F.G₀), (((T * Q) * x.ρF i * (T * Q)⁻¹ : GL (Fin n) x.Fr) :
          Matrix (Fin n) (Fin n) x.Fr) ∈ Ev x.Fr x.Fr n a := fun i => hmemAll i
      rw [Det.spanDesc (algebraMap x.Fr x.Fb) _ hmem]
      have h2 : (Set.range fun i : (F.G' : Set F.G₀) => ((((T * Q) * x.ρF i * (T * Q)⁻¹ : GL (Fin n) x.Fr) :
          Matrix (Fin n) (Fin n) x.Fr)).map (algebraMap x.Fr x.Fb)) =
          Set.range fun g : F.G' => (Matrix.fromBlocks (ρ₁' g) 0 0 (ρ₂' g)).submatrix
            ((finCongr hnab).trans finSumFinEquiv.symm) ((finCongr hnab).trans finSumFinEquiv.symm) := by
        congr 1
        funext g
        rw [hN, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
        simp only [ρ₁', ρ₂', MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hpush,
          Matrix.map_zero _ (map_zero (algebraMap x.Fr x.Fb))]
      rw [h2]
      exact span_range_fromBlocks_submatrix_eq_ev hnab ha hb ρ₁' ρ₂' s₁ s₂ i₁₂' i₂₁'
    · have hρcoe : ∀ g, mat x.ρF g = ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) :=
        fun g => hρF g
      have hform : ∀ g ∈ F.G', (mat x.ρF g)ᵀ * (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) *
          mat x.ρF (F.conj g) = (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) := by
        intro g hg
        have hf := x.form
        unfold GFrame.IsForm at hf
        have h0 := hf g
        rw [eps_eq_one_of_mem_G' F O _ g hg, _root_.one_zpow, Units.val_one, one_smul] at h0
        rw [hρcoe, hρcoe, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
        exact congrArg (fun M => M.map (algebraMap x.A x.Fr)) h0
      set Pm := (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) with hPm
      set W := ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * Pm *
        ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) with hW
      have hqq : ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) * (Q : Matrix (Fin n) (Fin n) x.Fr) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hqqT : (Q : Matrix (Fin n) (Fin n) x.Fr)ᵀ * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hqq, Matrix.transpose_one]
      have hWeq : ∀ g ∈ F.G', ((Q * x.ρF g * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * W *
          ((Q * x.ρF (F.conj g) * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) = W := by
        intro g hg
        have hf := hform g hg
        simp only [Units.val_mul]
        calc ((Q : Matrix (Fin n) (Fin n) x.Fr) * (x.ρF g : Matrix (Fin n) (Fin n) x.Fr) *
              ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr))ᵀ * W *
              ((Q : Matrix (Fin n) (Fin n) x.Fr) * (x.ρF (F.conj g) : Matrix (Fin n) (Fin n) x.Fr) *
              ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr))
            = ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * (x.ρF g : Matrix (Fin n) (Fin n) x.Fr)ᵀ *
              ((Q : Matrix (Fin n) (Fin n) x.Fr)ᵀ * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ) * Pm *
              (((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) * (Q : Matrix (Fin n) (Fin n) x.Fr)) *
              (x.ρF (F.conj g) : Matrix (Fin n) (Fin n) x.Fr) * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) := by
              simp only [hW, Matrix.transpose_mul, Matrix.mul_assoc]
          _ = ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ *
              ((mat x.ρF g)ᵀ * Pm * mat x.ρF (F.conj g)) * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) := by
              rw [hqqT, hqq]
              simp only [Matrix.mul_one, Matrix.mul_assoc]
              rfl
          _ = W := by rw [hf]
      set Z := Matrix.reindex e e W with hZ
      have hZeq : ∀ g ∈ F.G', (mat r₁ g)ᵀ * Z.toBlocks₁₂ * mat r₂ (F.conj g) = Z.toBlocks₁₂ ∧
          (mat r₂ g)ᵀ * Z.toBlocks₂₁ * mat r₁ (F.conj g) = Z.toBlocks₂₁ := by
        intro g hg
        have h0 := congrArg (Matrix.reindex e e) (hWeq g hg)
        rw [reindex_transpose_mul_mul, hQ g, hQ (F.conj g)] at h0
        rw [← hZ] at h0
        rw [← Matrix.fromBlocks_toBlocks Z] at h0
        simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj,
          Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h0
        exact ⟨h0.2.1, h0.2.2.1⟩
      have hmatinv : ∀ {k : ℕ} (ρ : F.G₀ →* GL (Fin k) x.Fr) (g : F.G₀), mat ρ g * mat ρ g⁻¹ = 1 := by
        intro k ρ g
        rw [← map_mul, mul_inv_cancel, map_one]
      have hfm : ∀ {k : ℕ} (ρ : F.G₀ →* GL (Fin k) x.Fr) (Pk : GL (Fin k) x.Fr), F.IsForm O n ρ Pk → ∀ g ∈ F.G',
          (mat ρ g)ᵀ * (Pk : Matrix (Fin k) (Fin k) x.Fr) * mat ρ (F.conj g) = Pk := by
        intro k ρ Pk h g hg
        unfold GFrame.IsForm at h
        have h0 := h g
        rw [eps_eq_one_of_mem_G' F O _ g hg, _root_.one_zpow, Units.val_one, one_smul] at h0
        exact h0
      have hPP : ∀ {k : ℕ} (Pk : GL (Fin k) x.Fr),
          ((Pk⁻¹ : GL (Fin k) x.Fr) : Matrix (Fin k) (Fin k) x.Fr) * Pk = 1 ∧
          (Pk : Matrix (Fin k) (Fin k) x.Fr) * ((Pk⁻¹ : GL (Fin k) x.Fr) : Matrix (Fin k) (Fin k) x.Fr) = 1 := by
        intro k Pk
        constructor
        · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have h12 : Z.toBlocks₁₂ = 0 := by
        have hV : ∀ h : F.G', mat r₁ h * (((P₁⁻¹ : GL (Fin a) x.Fr) : Matrix (Fin a) (Fin a) x.Fr) * Z.toBlocks₁₂) =
            (((P₁⁻¹ : GL (Fin a) x.Fr) : Matrix (Fin a) (Fin a) x.Fr) * Z.toBlocks₁₂) * mat r₂ h := by
          intro h
          obtain ⟨hc, hcc⟩ := conj_mem_G'_and_conj_conj_eq_of_mem_G' F h h.2
          have h3 := rh_mul_pi_mul_z_eq_pi_mul_z_mul_s (mat r₁ (F.conj h)) (mat r₁ (F.conj h)⁻¹) (P₁ : Matrix (Fin a) (Fin a) x.Fr) _
            (mat r₁ (F.conj (F.conj h))) (mat r₂ (F.conj (F.conj h))) Z.toBlocks₁₂ (hmatinv r₁ _) (hPP P₁).1
            (hPP P₁).2 (hfm r₁ P₁ hP₁ _ hc) (hZeq _ hc).1
          rw [hcc] at h3
          exact h3
        have h0 := intertwiner_eq_zero_of_map_intertwiner_eq_zero (algebraMap x.Fr x.Fb) (fun h : F.G' => mat r₁ h) (fun h : F.G' => mat r₂ h)
          (fun V hV' => i₁₂' V (fun g => by simpa [ρ₁', ρ₂', hpush] using hV' g)) _ hV
        calc Z.toBlocks₁₂ = (P₁ : Matrix (Fin a) (Fin a) x.Fr) *
              (((P₁⁻¹ : GL (Fin a) x.Fr) : Matrix (Fin a) (Fin a) x.Fr) * Z.toBlocks₁₂) := by
              rw [← Matrix.mul_assoc, (hPP P₁).2, Matrix.one_mul]
          _ = 0 := by rw [h0, Matrix.mul_zero]
      have h21 : Z.toBlocks₂₁ = 0 := by
        have hV : ∀ h : F.G', mat r₂ h * (((P₂⁻¹ : GL (Fin b) x.Fr) : Matrix (Fin b) (Fin b) x.Fr) * Z.toBlocks₂₁) =
            (((P₂⁻¹ : GL (Fin b) x.Fr) : Matrix (Fin b) (Fin b) x.Fr) * Z.toBlocks₂₁) * mat r₁ h := by
          intro h
          obtain ⟨hc, hcc⟩ := conj_mem_G'_and_conj_conj_eq_of_mem_G' F h h.2
          have h3 := rh_mul_pi_mul_z_eq_pi_mul_z_mul_s (mat r₂ (F.conj h)) (mat r₂ (F.conj h)⁻¹) (P₂ : Matrix (Fin b) (Fin b) x.Fr) _
            (mat r₂ (F.conj (F.conj h))) (mat r₁ (F.conj (F.conj h))) Z.toBlocks₂₁ (hmatinv r₂ _) (hPP P₂).1
            (hPP P₂).2 (hfm r₂ P₂ hP₂ _ hc) (hZeq _ hc).2
          rw [hcc] at h3
          exact h3
        have h0 := intertwiner_eq_zero_of_map_intertwiner_eq_zero (algebraMap x.Fr x.Fb) (fun h : F.G' => mat r₂ h) (fun h : F.G' => mat r₁ h)
          (fun V hV' => i₂₁' V (fun g => by simpa [ρ₁', ρ₂', hpush] using hV' g)) _ hV
        calc Z.toBlocks₂₁ = (P₂ : Matrix (Fin b) (Fin b) x.Fr) *
              (((P₂⁻¹ : GL (Fin b) x.Fr) : Matrix (Fin b) (Fin b) x.Fr) * Z.toBlocks₂₁) := by
              rw [← Matrix.mul_assoc, (hPP P₂).2, Matrix.one_mul]
          _ = 0 := by rw [h0, Matrix.mul_zero]
      have hgoal : (((T * Q)⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * Pm *
          (((T * Q)⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) =
          W.submatrix (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm)
            (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm) := by
        rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, ← (hT W).2, hW]
        simp only [Matrix.mul_assoc]
      rw [hgoal, hsub]
      apply submatrix_mem_ev_of_offDiag_blocks_zero hnab
      · intro i j
        have := congrFun (congrFun h12 i) j
        exact this
      · intro i j
        have := congrFun (congrFun h21 i) j
        exact this
