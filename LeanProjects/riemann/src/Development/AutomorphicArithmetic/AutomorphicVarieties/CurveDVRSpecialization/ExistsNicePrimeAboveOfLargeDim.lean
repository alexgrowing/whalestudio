import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NicePrimeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyCoeffsInSubalgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimLtOfNotLeTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

theorem UpperTheory.V.Pr.exists_nice_prime_above_of_large_dim :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (C₀ n : ℕ), F.Ok C₀ → F.Big C₀ → (n = 2 ∨ n = 3) → ∀ (S : UpperTheory.V.Fr.Space O F n) (x : Ideal S.A) (L : S.Loc x), ¬ S.u.triP ≤ x → ∀ I : Ideal S.B, S.FinLam I → ∀ P : Ideal L.R, I ≤ L.π P → ((n * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ UpperTheory.V.Pr.qdim P → ∃ p, UpperTheory.V.Pr.Nice L.ρ p ∧ P ≤ p := by
  intro l _ O _ _ _ _ F C₀ n hOk hBig hn S x L hx I hI P hIP hdim
  haveI := L.co
  haveI : IsLocalHom (algebraMap L.O' L.R) := L.co.isLocalHom
  haveI : CharP (IsLocalRing.ResidueField O) l := UpperTheory.V.Fr.IsCoef.char (O := O)
  obtain ⟨_, hP⟩ := UpperTheory.V.Fr.l51 hOk hn S x L hx
  obtain ⟨hM, hC⟩ := UpperTheory.V.Fr.krull_dim_lt_of_not_le_triangular hOk hn S x L hBig hx
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {w} := hw.maximalIdeal_eq
  have hwO' : algebraMap O L.O' w ∈ IsLocalRing.maximalIdeal L.O' := by
    rw [← L.unr]
    exact Ideal.mem_map_of_mem _ (hmax ▸ Ideal.subset_span rfl)
  have hwR : algebraMap O L.R w ∈ IsLocalRing.maximalIdeal L.R := by
    rw [IsScalarTower.algebraMap_apply O L.O' L.R]
    exact map_nonunit (algebraMap L.O' L.R) _ hwO'
  let a : Option (F.V × Fin n × Fin n) → Ideal L.R := fun o =>
    match o with
    | none => L.ρ.triM
    | some (v, i, j) =>
      if i = j then ⊤ else
        Ideal.map L.b I ⊔ Ideal.map (algebraMap O L.R) (IsLocalRing.maximalIdeal O) ⊔
          Ideal.span {y | ∃ g ∈ F.Nv v, y = ↑((L.ρ.ψ v i) g) - ↑((L.ρ.ψ v j) g)}
  have hN : 1 ≤ n * F.d := by
    have h1 : 1 ≤ n := by rcases hn with h | h <;> omega
    have h2 : 1 ≤ F.d := by have := hBig.1; omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have ha : ∀ o, UpperTheory.V.Pr.qdim (a o) < ↑(n * F.d) := by
    intro o
    rcases o with _ | ⟨v, i, j⟩
    · exact hM
    · by_cases hij : i = j
      · simp only [a, hij, if_true]
        show ringKrullDim (L.R ⧸ (⊤ : Ideal L.R)) < _
        rw [ringKrullDim_eq_bot_of_subsingleton]
        exact WithBot.bot_lt_coe _
      · simp only [a, hij, if_false]
        exact hC I hI v i j hij
  obtain ⟨p, hp, hPp, hp1, hwp, hnot⟩ :=
    UpperTheory.V.Pr.nicePrimeEx L.R (algebraMap O L.R w) hwR (n * F.d) hN _ a ha P hdim
  have hmap : Ideal.map (algebraMap O L.R) (IsLocalRing.maximalIdeal O) ≤ p := by
    rw [hmax, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hwp
  refine ⟨p, ⟨hp, hp1, ?_, ⟨?_, ?_⟩, ?_⟩, hPp⟩
  · have hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ l
    have := hmap (Ideal.mem_map_of_mem (algebraMap O L.R) hl)
    simpa using this
  · intro h
    rw [hP, top_le_iff] at h
    exact hp.ne_top h
  · exact hnot none
  · intro v i j hij hco
    apply hnot (some (v, i, j))
    simp only [a, hij, if_false]
    refine sup_le (sup_le ?_ hmap) ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact hPp (hIP hy)
    · rw [Ideal.span_le]
      rintro y ⟨g, hg, rfl⟩
      exact hco g hg
