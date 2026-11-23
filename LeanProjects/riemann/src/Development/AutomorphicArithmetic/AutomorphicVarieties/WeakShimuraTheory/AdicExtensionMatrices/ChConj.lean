import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section
variable {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

private theorem ch_adj (g : R →+* R') (X : M4 R) : adj (X.map g) = (adj X).map g := by
  ext i j
  simp [adj]

private theorem ch_map (D : RD Φ R) (f : R →+* R') (g : R' →+* R'') : (D.map f).map g = D.map (g.comp f) := by
  apply RD.ext
  · ext s i j
    rfl
  · funext v i
    ext s
    rfl

private theorem ch_conj (D : RD Φ R) (g : R →+* R') (X : M4 R) (s : Γ) (i j : Fin 4) :
    (adj (X.map g) * (D.map g).r s * X.map g) i j = g ((adj X * D.r s * X) i j) := by
  rw [ch_adj]
  show ((adj X).map g * (D.r s).map g * X.map g) i j = _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  rfl

private theorem ch_gsp (g : R →+* R') (X : M4 R) (i j : Fin 4) :
    (adj (X.map g) * X.map g - 1) i j = g ((adj X * X - 1) i j) := by
  rw [ch_adj, ← Matrix.map_mul, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private def chEq (D : RD Φ R) (n : Φ.ι → M4 R) : Set R :=
  {x | (∃ v i j, x = (adj (n v) * n v - 1) i j) ∨ (∃ v i, x = n v i i - 1) ∨ (∃ v i j, i < j ∧ x = n v i j) ∨
    (∃ v, ∃ s ∈ Φ.Gv v, ∃ i j, j < i ∧ x = (adj (n v) * D.r s * n v) i j) ∨
    (∃ v i, ∃ s : Φ.Gv v, x = (adj (n v) * D.r s * n v) i i - D.ψ v i s) ∨
    ∃ v i, ∃ s : Φ.Gv v, (s : Γ) ∈ Φ.Mu v ∧ x = D.ψ v i s - 1}

private theorem ch_iff (D : RD Φ R) (n : Φ.ι → M4 R) (g : R →+* R') :
    (D.map g).Flags (fun v => (n v).map g) ↔ ∀ x ∈ chEq D n, g x = 0 := by
  constructor
  · rintro ⟨hlow, hflag, hchar, hmu⟩ x hx
    rcases hx with ⟨v, i, j, rfl⟩ | ⟨v, i, rfl⟩ | ⟨v, i, j, hij, rfl⟩ | ⟨v, s, hs, i, j, hij, rfl⟩ |
      ⟨v, i, s, rfl⟩ | ⟨v, i, s, hs, rfl⟩
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow IsGSp at hl
      rw [← ch_gsp, hl.1]
      simp
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow at hl
      rw [map_sub, map_one, sub_eq_zero]
      exact hl.2.1 i
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow at hl
      exact hl.2.2 i j hij
    · rw [← ch_conj]
      exact hflag v s hs i j hij
    · rw [map_sub, sub_eq_zero, ← ch_conj]
      exact hchar v i s
    · rw [map_sub, map_one, sub_eq_zero]
      exact hmu v i s hs
  · intro h
    refine ⟨fun v => ?_, fun v s hs i j hij => ?_, fun v i s => ?_, fun v i s hs => ?_⟩
    · unfold IsLow IsGSp
      refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
      · ext i j
        have hx := h _ (Or.inl ⟨v, i, j, rfl⟩)
        rw [← ch_gsp, Matrix.sub_apply, sub_eq_zero] at hx
        rw [one_smul]
        exact hx
      · have hx := h _ (Or.inr (Or.inl ⟨v, i, rfl⟩))
        rw [map_sub, map_one, sub_eq_zero] at hx
        exact hx
      · exact h _ (Or.inr (Or.inr (Or.inl ⟨v, i, j, hij, rfl⟩)))
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, s, hs, i, j, hij, rfl⟩))))
      rw [← ch_conj] at hx
      exact hx
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, i, s, rfl⟩)))))
      rw [map_sub, sub_eq_zero, ← ch_conj] at hx
      exact hx
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, i, s, hs, rfl⟩)))))
      rw [map_sub, map_one, sub_eq_zero] at hx
      exact hx

end

theorem UpperTheory.V.Ws.sxChart :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {A₀ : Type} [CommRing A₀] (D : RD Φ A₀), ∃ (A : Type) (_ : CommRing A) (_ : Algebra A₀ A) (n : Φ.ι → M4 A), Algebra.FiniteType A₀ A ∧ Algebra.adjoin A₀ (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) = ⊤ ∧ (D.map (algebraMap A₀ A)).Flags n ∧ ∀ (R : Type) [CommRing R] (f : A₀ →+* R) (n' : Φ.ι → M4 R), (D.map f).Flags n' → ∃ F : A →+* R, F.comp (algebraMap A₀ A) = f ∧ ∀ v, (n v).map F = n' v := by
  intro O Γ _ _ Φ A₀ _ D
  classical
  let σ := Φ.ι × Fin 4 × Fin 4
  let N : Φ.ι → M4 (MvPolynomial σ A₀) := fun v => Matrix.of fun i j => MvPolynomial.X (v, i, j)
  let I : Ideal (MvPolynomial σ A₀) := Ideal.span (chEq (D.map MvPolynomial.C) N)
  let n : Φ.ι → M4 (MvPolynomial σ A₀ ⧸ I) := fun v => (N v).map (Ideal.Quotient.mk I)
  have hfac : algebraMap A₀ (MvPolynomial σ A₀ ⧸ I) = (Ideal.Quotient.mk I).comp MvPolynomial.C :=
    RingHom.ext fun _ => rfl
  refine ⟨MvPolynomial σ A₀ ⧸ I, inferInstance, inferInstance, n, ?_, ?_, ?_, ?_⟩
  · exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A₀ I) (Ideal.Quotient.mkₐ_surjective A₀ I)
  · have hset : (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) =
        (Ideal.Quotient.mkₐ A₀ I) '' Set.range (MvPolynomial.X : σ → MvPolynomial σ A₀) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨MvPolynomial.X x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [hset, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective A₀ I
  · rw [hfac, ← ch_map]
    exact (ch_iff _ _ _).2 fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
  · intro R _ f n' hn'
    let φ : MvPolynomial σ A₀ →+* R := MvPolynomial.eval₂Hom f fun x => n' x.1 x.2.1 x.2.2
    have hφC : φ.comp MvPolynomial.C = f := MvPolynomial.eval₂Hom_comp_C f _
    have hN : ∀ v, (N v).map φ = n' v := by
      intro v
      ext i j
      simp [φ, N]
    have hfl : ((D.map MvPolynomial.C).map φ).Flags (fun v => (N v).map φ) := by
      have hfun : (fun v => (N v).map φ) = n' := funext hN
      rw [ch_map, hφC, hfun]
      exact hn'
    have hker : I ≤ RingHom.ker φ :=
      Ideal.span_le.2 fun x hx => RingHom.mem_ker.2 ((ch_iff _ _ _).1 hfl x hx)
    refine ⟨Ideal.Quotient.lift I φ fun a ha => RingHom.mem_ker.1 (hker ha), ?_, ?_⟩
    · rw [hfac, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hφC]
    · intro v
      rw [← hN v]
      ext i j
      simp [n]
