import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CcAt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.ge_real (hE : GlobalEulerChar) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Set (HeightOneSpectrum (𝓞 F)))
    (hf : S.Finite) (hS : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (c : InfinitePlace F → G F Ω) (hc : ∀ w, IsCCAt w (c w))
    (A : Type) [CommRing A] (M : FRep A (GS Ω S)) (hM : ∀ m : M.X, l • m = 0) :
    Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ Module.finrank ℚ F =
      Nat.card (H1 M.ρ) * ∏ w, Nat.card {m : M.X // M.ρ (toGS Ω S (c w)) m = m} := by
  classical
  obtain ⟨S, rfl⟩ := hf.exists_finset_coe
  letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (by simpa using hM)
  obtain ⟨hρ, -, ⟨e1, -⟩, e2, -⟩ := UpperTheory.V.Pa.B2.scal A _ M (l ^ 1)
  have h := hE F Ω l 1 M.X S (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) one_pos (fun v hv => hS v hv) hρ c fun w _ => hc w
  rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
    Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w] at h
  have c0 : Nat.card (H0 M.ρ) = Nat.card (H0 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [c0, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]
  exact h

theorem UpperTheory.V.Pa.B2.arGE :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∃ c : Fin (Module.finrank ℚ (Lp L)) → (globOf r V).Γ, (∀ i, (globOf r V).η (c i) = -1 ∧ c i * c i = 1) ∧ ∀ (A : Type) [CommRing A] (M : FRep A (globOf r V).Γ), (∀ m : M.X, l • m = 0) → Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ Module.finrank ℚ (Lp L) = Nat.card (H1 M.ρ) * ∏ i, Nat.card {m : M.X // M.ρ (c i) m = m} := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r
  obtain ⟨h1, h2⟩ := UpperTheory.V.Pa.ccEx l L Ω
  choose c hc using h1
  have hcard : Fintype.card (InfinitePlace (Lp L)) = Module.finrank ℚ (Lp L) := by
    rw [IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  let e : Fin (Module.finrank ℚ (Lp L)) ≃ InfinitePlace (Lp L) := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => toGS Ω V.S' (c (e i)), fun i => ?_, fun A _ M hM => ?_⟩
  · obtain ⟨j, hj, -⟩ := hc (e i)
    obtain ⟨a1, a2, -⟩ := h2 _ ⟨j, hj⟩
    refine ⟨(Int.units_eq_one_or (V.η (toGS Ω V.S' (c (e i))))).resolve_left fun h => a2 ((V.hη _).1 h), ?_⟩
    exact (map_mul (toGS Ω V.S') _ _).symm.trans (by rw [a1, map_one]; rfl)
  · have h := UpperTheory.V.Pa.B2.ge_real hP.ge (Lp L) Ω l V.S' V.fin (fun v hv => V.sub (Or.inl hv)) c hc A M hM
    rw [← Equiv.prod_comp e] at h
    exact h
