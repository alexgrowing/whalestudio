import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem star_single' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) :
    F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp]

private theorem star_sub' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (x y : MonoidAlgebra R F.G₀) :
    F.star O R n (x - y) = F.star O R n x - F.star O R n y := by
  simp [GFrame.star]

end UpperTheory.V.Pa

private theorem chib_conj_eq_one_of_chib_eq_one_of_eps_eq_one {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (x : F.G₀) (hχ : ∀ i, r.chib i x = 1)
    (he : F.eps O (ResidueField O) x = 1) (j : Fin n) :
    r.chib j (F.conj x) = 1 := by
  have hD : ∀ (y : F.G₀) (t : ResidueField O),
      (GDet.ofRep (diagRep r.chib)).D (ResidueField O) (MonoidAlgebra.single y t - 1) =
        ∏ i, (((r.chib i y : (ResidueField O)ˣ) : ResidueField O) * t - 1) := by
    intro y t
    simp only [GDet.ofRep, GDet.repAlg, diagRep]
    simp
    have e : (t • Matrix.diagonal fun i ↦ ((r.chib i y : (ResidueField O)ˣ) : ResidueField O)) - 1 =
        Matrix.diagonal fun i ↦ ((r.chib i y : (ResidueField O)ˣ) : ResidueField O) * t - 1 := by
      ext i k
      by_cases h : i = k
      · subst h; simp [mul_comm]
      · simp [Matrix.diagonal, Matrix.one_apply, h]
    rw [e, Matrix.det_diagonal]
  set t : ResidueField O := ((r.chib j (F.conj x) : (ResidueField O)ˣ) : ResidueField O) with ht
  have hs : F.star O (ResidueField O) n (MonoidAlgebra.single x t - 1) =
      MonoidAlgebra.single (F.conj x)⁻¹ t - 1 := by
    rw [star_sub', star_single', he]
    congr 1
    · simp
    · rw [MonoidAlgebra.one_def, star_single']
      simp
  have hp := r.polar (ResidueField O) (MonoidAlgebra.single x t - 1)
  rw [hs, hD, hD] at hp
  simp only [hχ, Units.val_one, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  have h0 : ∏ i, (((r.chib i (F.conj x)⁻¹ : (ResidueField O)ˣ) : ResidueField O) * t - 1) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [ht, map_inv, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _), sub_self]
  rw [h0] at hp
  have h1 : t - 1 = 0 := (pow_eq_zero_iff (Fin.pos j).ne').mp hp.symm
  ext
  simpa [ht, sub_eq_zero] using h1

private theorem eps_residueField_eq_one_of_toZMod_eq_one {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] [CharP (ResidueField O) l] (x : F.G₀)
    (hx : PadicInt.toZMod ((F.ε x : ℤ_[l]ˣ) : ℤ_[l]) = 1) :
    F.eps O (ResidueField O) x = 1 := by
  have hm : ((F.ε x : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hx, map_one, sub_self]
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  ext
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, Units.val_one]
  have key := congrArg (algebraMap ℤ_[l] (ResidueField O)) hw
  simp only [map_sub, map_one, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_eq_zero] at key
  simpa [IsScalarTower.algebraMap_apply ℤ_[l] O (ResidueField O)] using key

theorem UpperTheory.V.Pa.hEx :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) [CharP (ResidueField O) l] (r : Resid F O n), ∃ H : OpenNormalSubgroup F.Γ, ∀ g : F.Γ, g ∈ H ↔ ∃ h : F.η g = 1, (∀ i, r.chib i ⟨g, h⟩ = 1) ∧ PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  intro l _ F O _ _ _ n _ r
  let P : F.Γ → Prop := fun g => ∃ h : F.η g = 1, (∀ i, r.chib i ⟨g, h⟩ = 1) ∧
    PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1
  let S : Subgroup F.Γ :=
    { carrier := {g | P g}
      mul_mem' := by
        rintro a b ⟨ha, hχa, hεa⟩ ⟨hb, hχb, hεb⟩
        refine ⟨by simp [ha, hb], fun i => ?_, ?_⟩
        · show r.chib i (⟨a, ha⟩ * ⟨b, hb⟩) = 1
          rw [map_mul, hχa, hχb, one_mul]
        · rw [map_mul, Units.val_mul, map_mul, hεa, hεb, one_mul]
      one_mem' := by
        refine ⟨by simp, fun i => ?_, ?_⟩
        · show r.chib i 1 = 1
          exact map_one _
        · simp
      inv_mem' := by
        rintro a ⟨ha, hχa, hεa⟩
        refine ⟨by simp [ha], fun i => ?_, ?_⟩
        · show r.chib i (⟨a, ha⟩)⁻¹ = 1
          rw [map_inv, hχa, inv_one]
        · have hu : ((F.ε a⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * ((F.ε a : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
            rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
          have := congrArg PadicInt.toZMod hu
          rw [map_mul, hεa, mul_one, map_one] at this
          exact this }
  have hmem : ∀ g, g ∈ S ↔ P g := fun g => Iff.rfl
  have hopen : IsOpen (S : Set F.Γ) := by
    have h1 : IsOpen {x : F.G₀ | ∀ i, r.chib i x = 1} := by
      have e : {x : F.G₀ | ∀ i, r.chib i x = 1} = ⋂ i, ((r.chib i).ker : Set F.G₀) := by
        ext x
        simp [MonoidHom.mem_ker]
      rw [e]
      exact isOpen_iInter_of_finite fun i => r.chib_open i
    have h2 : IsOpen {x : F.G₀ | PadicInt.toZMod ((F.ε x : ℤ_[l]ˣ) : ℤ_[l]) = 1} := by
      have e : ∀ z : ℤ_[l], PadicInt.toZMod z = 1 ↔ ‖z - 1‖ < 1 := by
        intro z
        rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod,
          RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      simp_rw [e]
      exact isOpen_lt (continuous_norm.comp ((Units.continuous_val.comp
        (F.ε_cont.comp continuous_subtype_val)).sub continuous_const)) continuous_const
    have e : (S : Set F.Γ) = Subtype.val ''
        ({x : F.G₀ | ∀ i, r.chib i x = 1} ∩ {x : F.G₀ | PadicInt.toZMod ((F.ε x : ℤ_[l]ˣ) : ℤ_[l]) = 1}) := by
      ext g
      constructor
      · rintro ⟨h, hχ, hε⟩
        exact ⟨⟨g, h⟩, ⟨hχ, hε⟩, rfl⟩
      · rintro ⟨x, ⟨hχ, hε⟩, rfl⟩
        exact ⟨x.2, hχ, hε⟩
    rw [e]
    exact F.η_open.isOpenMap_subtype_val _ (h1.inter h2)
  have case1 : ∀ g, P g → ∀ a, F.η a = 1 → P (a * g * a⁻¹) := by
    rintro g ⟨h, hχ, hε⟩ a ha
    refine ⟨by simp [h, ha], fun i => ?_, ?_⟩
    · show r.chib i (⟨a, ha⟩ * ⟨g, h⟩ * (⟨a, ha⟩)⁻¹) = 1
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
      exact hχ i
    · rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
      exact hε
  have hnorm : S.Normal := by
    refine ⟨fun g hg a => ?_⟩
    rw [hmem] at hg ⊢
    rcases Int.units_eq_one_or (F.η a) with ha | ha
    · exact case1 g hg a ha
    · have hb : F.η (F.c⁻¹ * a) = 1 := by
        rw [map_mul, map_inv, F.η_c, ha]
        rfl
      obtain ⟨h', hχ', hε'⟩ := case1 g hg (F.c⁻¹ * a) hb
      obtain ⟨h, -, hε⟩ := hg
      have hη : F.η (a * g * a⁻¹) = 1 := by simp [h]
      have hx : (⟨a * g * a⁻¹, hη⟩ : F.G₀) = F.conj ⟨F.c⁻¹ * a * g * (F.c⁻¹ * a)⁻¹, h'⟩ := by
        apply Subtype.ext
        simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk]
        group
      refine ⟨hη, fun i => ?_, ?_⟩
      · rw [hx]
        exact chib_conj_eq_one_of_chib_eq_one_of_eps_eq_one F O n r _ hχ' (eps_residueField_eq_one_of_toZMod_eq_one F O _ hε') i
      · rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
        exact hε
  exact ⟨⟨⟨S, hopen⟩, hnorm⟩, fun g => Iff.rfl⟩
