import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.local_deformation_trace_mod_maximal :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (maximalIdeal O).map (algebraMap O L.R) ≤ maximalIdeal L.R ∧ (∀ (g : F.G0) (i : Fin n), F.Ψ g = 1 → L.ρ.r g i i - 1 ∈ maximalIdeal L.R) ∧ ∀ (P : Ideal L.R) [IsLocalRing (L.R ⧸ P)], (maximalIdeal O).map (algebraMap O L.R) ≤ P → Finite (ResidueField (L.R ⧸ P)) ∧ (∀ y ∈ maximalIdeal L.R, Ideal.Quotient.mk P y ∈ maximalIdeal (L.R ⧸ P)) ∧ (L.ρ.map (Ideal.Quotient.mk P)).Cont (maximalIdeal (L.R ⧸ P)) ∧ ∃ f : ResidueField O →+* L.R ⧸ P, (∀ a : O, Ideal.Quotient.mk P (algebraMap O L.R a) = f (residue O a)) ∧ ((L.ρ.map (Ideal.Quotient.mk P)).map (residue (L.R ⧸ P))).IsBar ((residue (L.R ⧸ P)).comp f) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  obtain ⟨hc, hb, -⟩ := UpperTheory.V.Fr.loc_rho hF hn S x L
  have hm : ∀ a ∈ maximalIdeal O, algebraMap O L.R a ∈ maximalIdeal L.R := fun a ha => by
    have h1 : algebraMap O L.O' a ∈ maximalIdeal L.O' := L.unr ▸ Ideal.mem_map_of_mem _ ha
    rw [IsScalarTower.algebraMap_apply O L.O' L.R]
    exact map_nonunit (algebraMap L.O' L.R) _ h1
  haveI hloc : IsLocalHom (algebraMap O L.R) := ⟨fun a ha => by
    by_contra hna
    exact hm a hna ha⟩
  have hb0 := hb (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _
  refine ⟨Ideal.map_le_iff_le_comap.2 hm, fun g i hg => ?_, fun P _ hP => ?_⟩
  · have h := hb0.1 g i
    rw [hg, NRep.map_r] at h
    rw [← residue_eq_zero_iff, map_sub, h]
    simp
  haveI hlocP : IsLocalHom (Ideal.Quotient.mk P) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmP : ∀ y ∈ maximalIdeal L.R, Ideal.Quotient.mk P y ∈ maximalIdeal (L.R ⧸ P) :=
    fun y hy => map_nonunit (Ideal.Quotient.mk P) y hy
  have hle : ∀ N : ℕ, maximalIdeal L.R ^ N ≤ (maximalIdeal (L.R ⧸ P) ^ N).comap (Ideal.Quotient.mk P) := fun N =>
    le_trans (Ideal.pow_right_mono (fun y hy => hmP y hy) N) (Ideal.le_comap_pow _ N)
  refine ⟨?_, hmP, ⟨fun i j N => ?_, fun v i N => ?_⟩, ?_⟩
  · haveI : Finite (ResidueField L.R) := Finite.of_surjective _ (resMap_bijective L.O' L.R).2
    refine Finite.of_surjective (ResidueField.map (Ideal.Quotient.mk P)) fun y => ?_
    obtain ⟨y, rfl⟩ := residue_surjective y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨residue _ y, ResidueField.map_residue _ _⟩
  · exact (hc.1 i j N).comp (Ideal.quotientMap _ (Ideal.Quotient.mk P) (hle N))
  · exact (hc.2 v i N).comp (Ideal.quotientMap _ (Ideal.Quotient.mk P) (hle N))
  · let f : ResidueField O →+* L.R ⧸ P :=
      Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk P).comp (algebraMap O L.R))
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hP (Ideal.mem_map_of_mem _ ha))
    have hf : ∀ a : O, Ideal.Quotient.mk P (algebraMap O L.R a) = f (residue O a) := fun a => rfl
    have key : ∀ (y : L.R) (t : ResidueField O), residue L.R y = ResidueField.map (algebraMap O L.R) t →
        residue (L.R ⧸ P) (Ideal.Quotient.mk P y) = residue (L.R ⧸ P) (f t) := fun y t h => by
      obtain ⟨a, rfl⟩ := residue_surjective t
      rw [← hf, ← ResidueField.map_residue (Ideal.Quotient.mk P), h, ResidueField.map_residue,
        ResidueField.map_residue]
    exact ⟨f, hf, fun g i => key _ _ (hb0.1 g i), fun v i g => key _ _ (hb0.2 v i g)⟩
