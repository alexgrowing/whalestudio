import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CocT
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UpSupUp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.ResEntry
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UMFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem ac_mul {S A : Type} [TopologicalSpace S] [CommRing A] {I : Ideal A}
    {M N : S → M4 A} (hM : ∀ a b, AdicCont I fun s => M s a b) (hN : ∀ a b, AdicCont I fun s => N s a b) :
    ∀ a b, AdicCont I fun s => (M s * N s) a b := by
  intro a b n
  simp only [Matrix.mul_apply, map_sum, map_mul, Fin.sum_univ_four, map_add]
  exact ((((hM a 0 n).mul (hN 0 b n)).add ((hM a 1 n).mul (hN 1 b n))).add ((hM a 2 n).mul (hN 2 b n))).add
    ((hM a 3 n).mul (hN 3 b n))

private theorem twist_mul {R Γ : Type} [CommRing R] [Group Γ] {r : Γ →* M4 R} (hb : ∀ g, IsBlock (r g)) {z : Γ → M4 R}
    (hz : ∀ g, z g ∈ hAB R) (coc : ∀ g h, z (g * h) = z g + r g * z h * r g⁻¹) (g h : Γ) :
    (1 + z (g * h)) * r (g * h) = (1 + z g) * r g * ((1 + z h) * r h) := by
  have e : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e0 : z g * (r g * z h * r h) = 0 := hAB_mul_hAB (hz g) (hAB_mul_mul (hb g) (hz h) (hb h))
  have e1 : r g * z h * r g⁻¹ * (r g * r h) = r g * z h * r h := by
    rw [mul_assoc, ← mul_assoc (r g⁻¹), e, one_mul]
  rw [coc, map_mul, ← add_assoc, add_mul, e1]
  calc _ = (1 + z g) * (r g * r h) + r g * z h * r h + z g * (r g * z h * r h) := by rw [e0, add_zero]
    _ = _ := by noncomm_ring

theorem UpperTheory.V.Ws.Bl.cocA :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (r : G ℚ Ω →* M4 A) (u : M4 A), IsAdicComplete (maximalIdeal A) A → (l : A) ∈ maximalIdeal A → BlockDiagonalOrdinaryGSpRep S c s B r u →
          ∃ (r' : G ℚ Ω →* M4 A) (z : G ℚ Ω → M4 A) (y : M4 A), (∀ g, r' g = (1 + z g) * r g) ∧ (∀ i j, AdicCont (maximalIdeal A) fun g => r' g i j) ∧ (∀ g, z g ∈ uM A) ∧ y ∈ uM A ∧
            (∀ g i j, z g i j ∈ maximalIdeal A) ∧ z c = 0 ∧ (∀ g ∈ neSet l r.ker, z g = 0) ∧ (∀ h ∈ Dec (F := ℚ) B, IsSUp (adj u * (z h - (r h * y * r h⁻¹ - y)) * u)) ∧ z ≠ 0 := by
  intro hP Ω _ _ _ l _ S c s B hpos A _ _ _ _ r u hc hl hb
  obtain ⟨hfin, hfree, hI⟩ := uMFacts A
  obtain ⟨hlat, hcc, hker⟩ := latU S c s B hpos A r u hb
  obtain ⟨z, y, hz, hne⟩ := cocT hP S c s B hpos A (uM A) (adU hb.bg) (uPlus u) r.ker hc hl hlat
    (adBij A _ r hb.bg s hb.sep) hcc hker hb.unr
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have htm : t ∈ maximalIdeal A := ht.not_isUnit
  have coc : ∀ g h, (t • z (g * h)).1 = (t • z g).1 + r g * (t • z h).1 * r g⁻¹ := fun g h => by
    rw [hz.coc, smul_add, ← map_smul, Submodule.coe_add, adU_val]
  have z1 : z 1 = 0 := by
    have := hz.coc 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    exact left_eq_add.mp this
  have zc : ∀ i j, AdicCont (maximalIdeal A) fun g => (1 + (t • z g).1) i j := fun i j n => by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hz.cont n) g] with g' e
    have e1 : z g' - z g ∈ lev A (uM A) n := (Submodule.Quotient.eq _).1 e
    have e2 := (hI _ _).1 (Submodule.smul_mem _ t e1) i j
    rw [Ideal.Quotient.eq]
    convert e2 using 1
    simp [smul_sub, mul_sub]
  refine ⟨MonoidHom.mk ⟨fun g => (1 + (t • z g).1) * r g, by simp [z1]⟩
      (twist_mul hb.bg.blk (fun g => (t • z g).2.1) coc), fun g => (t • z g).1, (t • y).1, fun _ => rfl,
    ac_mul zc hb.cont, fun g => (t • z g).2, (t • y).2, fun g i j => ?_, by simp [hz.cz], fun g hg => by simp [hz.kill g hg],
    fun h hh => ?_, fun e => hne (funext fun g => ?_)⟩
  · exact Ideal.mul_mem_right _ _ htm
  · have := (uPlus u).smul_mem t (hz.loc h hh)
    rw [smul_sub, smul_sub, ← map_smul] at this
    exact this
  · have e1 : t • (z g).1 = 0 := congrFun e g
    exact Subtype.ext ((smul_eq_zero.1 e1).resolve_left ht.ne_zero)
