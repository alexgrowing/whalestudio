import Development.EtaleCohomology.KummerTheory.InjSlice

open CategoryTheory Limits

namespace LateralTheory.KummerTheory.GhostPf

variable {A : Type*} [Category A] [Abelian A]

theorem cyc (C : CochainComplex A ℤ) (N : ℕ) {j k l : ℤ} (hjk : j + 1 = k) (hkl : k + 1 = l)
    (hH : N • 𝟙 (C.homology k) = 0) {I : A} (φ : C.X k ⟶ I) (hφ : C.d j k ≫ φ = 0)
    {P : A} (f : P ⟶ C.X k) (hf : f ≫ C.d k l = 0) : f ≫ (N • φ) = 0 := by
  rw [← C.liftCycles_i f l ((ComplexShape.up ℤ).next_eq' hkl) hf,
    ← C.p_descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ]
  have e : C.iCycles k ≫ (N • (C.pOpcycles k ≫ C.descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ)) =
      C.homologyπ k ≫ (N • 𝟙 (C.homology k)) ≫ C.homologyι k ≫
        C.descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp]
    rw [← Category.assoc (C.iCycles k), ← C.homology_π_ι, Category.assoc]
  rw [Category.assoc, e, hH]
  simp

theorem extd (C : CochainComplex A ℤ) (N : ℕ) {j k l : ℤ} (hjk : j + 1 = k) (hkl : k + 1 = l)
    (hH : N • 𝟙 (C.homology k) = 0) {I : A} [Injective I] (φ : C.X k ⟶ I) (hφ : C.d j k ≫ φ = 0) :
    ∃ c : C.X l ⟶ I, C.d k l ≫ c = N • φ := by
  have hk : kernel.ι (factorThruImage (C.d k l)) ≫ (N • φ) = 0 := by
    apply cyc C N hjk hkl hH φ hφ
    calc kernel.ι (factorThruImage (C.d k l)) ≫ C.d k l
        = (kernel.ι (factorThruImage (C.d k l)) ≫ factorThruImage (C.d k l)) ≫ image.ι (C.d k l) := by
          rw [Category.assoc, image.fac]
      _ = 0 := by rw [kernel.condition, zero_comp]
  refine ⟨Injective.factorThru (Abelian.epiDesc _ _ hk) (image.ι (C.d k l)), ?_⟩
  calc C.d k l ≫ _ = factorThruImage (C.d k l) ≫ image.ι (C.d k l) ≫
        Injective.factorThru (Abelian.epiDesc _ _ hk) (image.ι (C.d k l)) := by
          rw [← Category.assoc, image.fac]
    _ = N • φ := by rw [Injective.comp_factorThru, Abelian.comp_epiDesc]

theorem step (C : CochainComplex A ℤ) (N M : ℕ) {i j k l : ℤ} (_hij : i + 1 = j) (hjk : j + 1 = k)
    (hkl : k + 1 = l) (hH : N • 𝟙 (C.homology k) = 0) [Injective (C.X k)]
    (a : C.X j ⟶ C.X i) (b : C.X k ⟶ C.X j) (hab : a ≫ C.d i j + C.d j k ≫ b = M • 𝟙 (C.X j)) :
    ∃ c : C.X l ⟶ C.X k, (N • b) ≫ C.d j k + C.d k l ≫ c = (N * M) • 𝟙 (C.X k) := by
  have hdb : C.d j k ≫ b = M • 𝟙 (C.X j) - a ≫ C.d i j := by rw [← hab]; abel
  have hφ : C.d j k ≫ (M • 𝟙 (C.X k) - b ≫ C.d j k) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hdb, Preadditive.sub_comp, Category.assoc,
      HomologicalComplex.d_comp_d]
    simp
  obtain ⟨c, hc⟩ := extd C N hjk hkl hH _ hφ
  refine ⟨c, ?_⟩
  rw [hc, Preadditive.nsmul_comp, smul_sub, mul_smul]
  abel

theorem homot (C : CochainComplex A ℤ) [C.IsStrictlyGE (-1)] (hI : ∀ j, Injective (C.X j)) (N m : ℕ)
    (hH : ∀ j : ℤ, j < m → N • 𝟙 (C.homology j) = 0) :
    ∀ n : ℕ, ∀ i j k : ℤ, i + 1 = j → j + 1 = k → j = (n : ℤ) - 1 → j < m →
      ∃ a : C.X j ⟶ C.X i, ∃ b : C.X k ⟶ C.X j, a ≫ C.d i j + C.d j k ≫ b = N ^ (n + 1) • 𝟙 (C.X j) := by
  intro n
  induction n with
  | zero =>
    intro i j k hij hjk hj hjm
    have hj' : j = -1 := by simpa using hj
    subst hj'
    have := hI (-1)
    have hz : C.d i (-1) ≫ 𝟙 (C.X (-1)) = 0 :=
      (C.isZero_of_isStrictlyGE (-1) i (by omega)).eq_of_src _ _
    obtain ⟨c, hc⟩ := extd C N hij hjk (hH _ hjm) (𝟙 _) hz
    exact ⟨0, c, by simp [hc]⟩
  | succ n ih =>
    intro i j k hij hjk hj hjm
    subst hij
    obtain ⟨a, b, hab⟩ := ih (i - 1) i (i + 1) (by ring) rfl (by push_cast at hj; omega) (by omega)
    have := hI (i + 1)
    obtain ⟨c, hc⟩ := step C N (N ^ (n + 1)) (by ring : i - 1 + 1 = i) rfl hjk (hH _ hjm) a b hab
    exact ⟨N • b, c, by rw [hc, ← pow_succ']⟩

theorem Ghost_of : LateralTheory.KummerTheory.Ghost := by
  intro A _ _ _ C _ hI N m hH j hj P f hf
  by_cases hlow : j < -1
  · refine ⟨0, ?_⟩
    exact (C.isZero_of_isStrictlyGE (-1) j hlow).eq_of_tgt _ _
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = (n : ℤ) - 1 := ⟨(j + 1).toNat, by omega⟩
    obtain ⟨a, b, hab⟩ := homot C hI N m hH n (j - 1) j (j + 1) (by ring) rfl hn hj
    have hnm : n + 1 ≤ m + 1 := by omega
    refine ⟨N ^ (m + 1 - (n + 1)) • (f ≫ a), ?_⟩
    have e : f ≫ a ≫ C.d (j - 1) j = N ^ (n + 1) • f := by
      have := congrArg (f ≫ ·) hab
      simp only [Preadditive.comp_add, Preadditive.comp_nsmul, Category.comp_id] at this
      rw [← Category.assoc f (C.d j (j + 1)) b, hf, zero_comp, add_zero] at this
      exact this
    rw [Preadditive.nsmul_comp, Category.assoc, e, smul_smul, ← pow_add, Nat.sub_add_cancel hnm]

end LateralTheory.KummerTheory.GhostPf
