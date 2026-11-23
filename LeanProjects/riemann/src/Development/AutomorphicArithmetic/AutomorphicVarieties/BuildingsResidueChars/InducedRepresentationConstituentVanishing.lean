import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Pointwise

private theorem cyc_ine (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have h1 : Chr.cls ℚ Ω (l ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ
  have h2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hspec.symm.trans h2)
  rw [ZMod.val_injective _ h3]
  simp

private theorem ine_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F]
    (A : ValuationSubring Ω) (g : G F Ω) : g ∈ Ine (F := F) A ↔ resQ F g ∈ Ine (F := ℚ) A := Iff.rfl

private theorem mix_one {k : Type} [Field k] (h : (2 : k) ≠ 0) (γ : kˣ) : mix γ 1 1 = (1 : M4 k) := by
  have e : (2 : k)⁻¹ * (1 + 1) = 1 := by rw [one_add_one_eq_two, inv_mul_cancel₀ h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mix, e]

private theorem diag_one {Γ k : Type} [Group Γ] [Field k] {r : Γ →* GL (Fin 2) k} {H : Subgroup Γ} {x : Γ →* kˣ}
    (h : IsDiagOn r H ![1, x]) {s : Γ} (hs : s ∈ H) (hx : x s = 1) : r s = 1 := by
  obtain ⟨g, hg⟩ := h
  have h1 : g * r s * g⁻¹ = 1 := by
    apply Units.ext
    rw [hg s hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hx]
  simpa [mul_inv_eq_one] using h1

private theorem sqrt_one {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : (Qbar l)ˣ} (h : d ^ 2 = 1) (hc : Cong d 1) : d = 1 := by
  have h1 : (d : Qbar l) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  rcases sq_eq_one_iff.1 h1 with h2 | h2
  · exact Units.ext h2
  · exfalso
    have h3 : ‖(2 : Qbar l)‖ < 1 := by
      have h4 : ‖(d : Qbar l) - 1‖ < 1 := hc
      rw [h2, show (-1 - 1 : Qbar l) = -2 by ring, norm_neg] at h4
      exact h4
    have h5 : ‖((2 : ℕ) : ℚ_[l])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hl
    have h6 : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by rw [map_natCast, Nat.cast_ofNat]
    rw [h6, norm_algebraMap', h5] at h3
    exact lt_irrefl _ h3

theorem UpperTheory.induced_representation_constituent_vanishing :
    UpperTheory.V.Sd.S2.IndKill := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H g hg
  obtain ⟨A, hA, hgI, hrb⟩ := hg
  have hAl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
  have hsI : resQ T.F g ∈ Ine (F := ℚ) A := (ine_iff _ _ _).1 hgI
  have hψ : D.ψ (resQ T.F g) = 1 :=
    H.hyp.ok.kb A (fun p hp => by rw [Finset.mem_singleton.1 hp]; exact hAl) g hgI hrb
  have hk : resQ T.F g ∈ k₀.fixingSubgroup := (H.hyp.ps g).1 (H.hyp.two.unr A g hgI)
  have hδ2 := H.δ_sq g
  have hδ1 := H.δ_one g
  show (tw (R.comp (resQ T.F)) δ g).val = 1
  rw [tw_val, MonoidHom.comp_apply]
  generalize resQ T.F g = s at *
  have hz : cycZ ℚ Ω l s = 1 := cyc_ine Ω l A hAl hsI
  have hbar : cycBar ℚ Ω l s = 1 := by simp [cycBar, hz]
  have hchi : chiO ℚ Ω l c.O s = 1 := by simp [chiO, hz]
  have hom : D.om s = 1 := (H.chars.om s).2 (by rw [hbar]; simp [Cong])
  have hal : D.al s = D.ξ s := by simp [Raw.al, hchi, hom]
  have hξ : D.ξ s = 1 := by
    refine H.chars.xi s ?_
    have h1 : residue c.O (D.ξ s : c.O) = 1 := by
      have h2 := congrFun (congrFun hrb 2) 2
      rw [← hal]
      simpa [Raw.rbar, Raw.r0, mapRep, GradeZeroInterpolatingElement.diagRep, Raw.ps] using h2
    have h3 : (D.ξ s : c.O) - 1 ∈ maximalIdeal c.O := by
      rw [← residue_eq_zero_iff, map_sub, h1, map_one, sub_self]
    have h4 := (UpperTheory.V.Fr.sc_norm l c _).2.1 h3
    rw [Subalgebra.coe_sub, Subalgebra.coe_one] at h4
    unfold Cong
    rw [Units.val_one]
    exact h4
  have hth : D.th s = 1 := by simp [Raw.th, Raw.Psi, Chr.Psi, hal, hξ, hchi, hψ]
  have hup : up D.ξ s = 1 := by simp [up, hξ]
  have hδ : δ g = 1 := by
    refine sqrt_one H.hyp.good.l_odd ?_ hδ1
    simpa [hbar, hup, H.hyp.φ_in s hk, up, hth, hξ] using hδ2
  obtain ⟨h, rfl⟩ : s ∈ (resQ k₀).range := ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => hk ⟨x.1, x.2⟩, rfl⟩
  have hN : (resQ k₀).range.Normal := Subgroup.normal_of_index_eq_two H.mix.index
  set t₀ := resQ T.F T.g0 with ht₀
  obtain ⟨h', hh'⟩ : t₀⁻¹ * resQ k₀ h * t₀ ∈ (resQ k₀).range := hN.conj_mem' _ ⟨h, rfl⟩ t₀
  have r1 : r h = 1 := diag_one (H.dat.away A hAl) ((ine_iff _ _ _).2 hsI) hup
  obtain ⟨c1, c2, -⟩ := UpperTheory.V.Two.ineConj ℚ Ω t₀
  have hAA : t₀ • (t₀⁻¹ • A) = A := smul_inv_smul _ _
  have r2 : r h' = 1 := by
    refine diag_one (H.dat.away (t₀⁻¹ • A) fun h0 => hAl ?_) ((ine_iff _ _ _).2 ?_) ?_
    · rw [← hAA]; exact (c2 _ l).2 h0
    · rw [hh']; exact c1 _ _ (hAA.symm ▸ hsI)
    · rw [MonoidHom.comp_apply, hh', map_mul, map_mul, hup, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [H.mix.on h h' hh', r1, r2, hδ, Units.val_one, Units.val_one, one_smul]
  exact mix_one H.mix.two _
