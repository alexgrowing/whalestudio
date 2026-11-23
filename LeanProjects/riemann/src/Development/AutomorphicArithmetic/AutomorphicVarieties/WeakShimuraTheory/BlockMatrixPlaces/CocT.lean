import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GwCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GammaOneGammaZeroHomogeneousCocyclesFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CardP
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PrimEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Compat
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.IsPrecompleteFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.cocT :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (ρ : Representation A (G ℚ Ω) T) (P : Submodule A T) (K : Subgroup (G ℚ Ω)),
          IsAdicComplete (maximalIdeal A) A → (l : A) ∈ maximalIdeal A → Lat ρ (Dec (F := ℚ) B) P → (Function.Bijective fun x => ρ s x - x) → (∀ x, ρ c x = -x) → K ≤ ρ.ker → (∀ A', Raw.Away S A' → Ine (F := ℚ) A' ≤ K) →
          ∃ (z : G ℚ Ω → T) (y : T), IsZT ρ c (neSet l K) (Dec (F := ℚ) B) P z y ∧ z ≠ 0 := by
  intro hC Ω _ _ _ l _ S c s B hP A _ _ _ _ T _ _ _ _ ρ P K hA hl hL hs hc hK hU
  have hcard := cardP A T P hL.sat hL.ne
  have hfin : ∀ n, Finite (T ⧸ lev A T n) := fun n => (hcard n).1
  have htor : ∀ n, ∀ m : T ⧸ lev A T n, (l ^ n) • m = 0 := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul A, Nat.cast_pow]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl n) Submodule.mem_top
  have hlc : ∀ n, ∀ m : T ⧸ lev A T n, IsLocallyConstant fun g => modRep ρ n g m := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    exact hL.cont n x
  have hker : ∀ n, K ≤ (modRep ρ n).ker := by
    intro n g hg
    have h1 : ρ g = 1 := hK hg
    refine LinearMap.ext fun m => ?_
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [modRep_mk, h1]
    rfl
  have hneg : ∀ n, ∀ m : T ⧸ lev A T n, modRep ρ n c m = -m := by
    intro n m
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    rw [modRep_mk, hc, map_neg]
  have hbij : ∀ n, Function.Bijective fun m : T ⧸ lev A T n => modRep ρ n s m - m := by
    intro n
    haveI := hfin n
    refine Finite.surjective_iff_bijective.1 fun m => ?_
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective m
    obtain ⟨y, rfl⟩ := hs.2 x
    exact ⟨(lev A T n).mkQ y, by simp only [modRep_mk, map_sub]⟩
  have hstab : ∀ n, ∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P.map (lev A T n).mkQ, modRep ρ n h x ∈ P.map (lev A T n).mkQ := by
    rintro n h hh _ ⟨x, hx, rfl⟩
    exact ⟨ρ h x, hL.stab h hh x hx, rfl⟩
  have hZ : ∀ n, (Zn ρ c (neSet l K) (Dec (F := ℚ) B) P n).Finite := fun n => by
    haveI := hfin n
    exact zcFin hC.gf S c s B hP A _ (modRep ρ n) n (htor n) (hlc n) K (hker n) hU _
  have hge : ∀ n, n ≤ Nat.card (Zn ρ c (neSet l K) (Dec (F := ℚ) B) P n) := fun n => by
    haveI := hfin n
    exact (hcard n).2.trans
      (gwCount hC S c s B hP A _ (modRep ρ n) n (htor n) (hlc n) K (hker n) hU (hneg n) (hbij n) _ (hstab n))
  obtain ⟨z, y, h1, h2, h3, h4⟩ := compat A T _ ρ c _ _ P hfin hZ (primEx A T _ ρ c _ _ P hL hZ hge)
  exact limit A T _ ρ c _ _ P hA z y h1 h2 h3 h4
