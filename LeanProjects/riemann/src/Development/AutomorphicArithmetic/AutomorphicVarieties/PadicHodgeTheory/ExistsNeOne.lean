import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CocycleTransportH1fSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem sandwich {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B S Z : Submodule E M)
    (hBS : B ≤ S) (hSZ : S ≤ Z) [Module.Finite E B]
    [hQ : Module.Finite E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ)] :
    Module.Finite E S ∧
      finrank E S = finrank E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ) + finrank E B := by
  let f : S →ₗ[E] (Z ⧸ B.comap Z.subtype) := (B.comap Z.subtype).mkQ ∘ₗ Submodule.inclusion hSZ
  have hr : LinearMap.range f = (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
  have hk : LinearMap.ker f = B.comap S.subtype := by
    ext x
    simp [f]
  have eB := Submodule.comapSubtypeEquivOfLe hBS
  have hkf : Module.Finite E ↥(LinearMap.ker f) := by
    rw [hk]; exact Module.Finite.equiv eB.symm
  have hrf : Module.Finite E ↥(LinearMap.range f) := by rw [hr]; exact hQ
  have hS : Module.Finite E S := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
    · rw [Submodule.map_top]; exact Module.Finite.iff_fg.1 hrf
    · rw [top_inf_eq]; exact Module.Finite.iff_fg.1 hkf
  refine ⟨hS, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hr, hk, eB.finrank_eq]

private theorem exists_ne_one {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] ℚ_[l] E] (κ : G →* Eˣ) (w : ℤ) (hw : w ≠ 0) (h : HasWeight φ κ w) :
    ∃ g, κ g ≠ 1 := by
  obtain ⟨U, hU, h⟩ := h
  obtain ⟨-, s, ⟨⟨g, hg, rfl⟩, hs⟩, hfin⟩ := (cycInertia l).2 (U.map φ) (hφ.isOpenMap _ hU)
  refine ⟨g, fun h1 => hfin ?_⟩
  have hinj : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective
  have h2 := h g hg hs
  rw [h1] at h2
  have h3 : cyc l l (φ g) ^ w = 1 := by
    apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinj
    rw [map_zpow, map_one]
    exact h2.symm
  exact isOfFinOrder_iff_zpow_eq_one.2 ⟨w, hw, h3⟩

private theorem finrank_ddr {l : ℕ} [Fact l.Prime] {G : Type} [Group G]
    (φ : G →* GQ l) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (ρ : Representation E G E) (h : IsDr φ ρ) : finrank E ↥(Ddr φ ρ) = φ.range.index := by
  have he : Ddr φ (resCoef ℚ_[l] ρ) = (Ddr φ ρ).restrictScalars ℚ_[l] := by
    ext x
    simp only [Ddr, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have h1 : finrank ℚ_[l] ↥(Ddr φ ρ) = φ.range.index * finrank ℚ_[l] E := by
    unfold IsDr at h
    rw [he] at h
    exact h
  rw [← Module.finrank_mul_finrank ℚ_[l] E, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

theorem UpperTheory.V.Loc.z1fChar :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (κ : G →* Eˣ), Continuous (fun g => (κ g : E)) → ∀ w : ℤ, HasWeight φ κ w → (w < 0 → UpperTheory.V.Loc.finiteCocycles φ (chRep κ) = ReciprocityTheory.Gal.B1 (chRep κ) ∧ finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1) ∧ (0 < w → Module.Finite E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) ∧ finrank E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) = φ.range.index + 1) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ w hw
  have hc : ReciprocityTheory.Gal.ContAction (chRep κ) := by
    have : (fun p : G × E => chRep κ p.1 p.2) = fun p => (κ p.1 : E) * p.2 := by
      funext p; simp [chRep]
    unfold ReciprocityTheory.Gal.ContAction
    rw [this]
    exact (hκ.comp continuous_fst).mul continuous_snd
  obtain ⟨hdr, hfil⟩ := charFil φ hφ κ hκ w hw
  obtain ⟨hfin, hdim⟩ := bkDim hP φ hφ (chRep κ) hc hdr
  have hBS := (z1fMap φ (chRep κ) (chRep κ)).1 hc
  have hSZ : UpperTheory.V.Loc.finiteCocycles φ (chRep κ) ≤ ReciprocityTheory.Gal.Z1 (chRep κ) := fun c h => h.1
  have hBf : Module.Finite E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := by
    unfold ReciprocityTheory.Gal.B1; infer_instance
  obtain ⟨hS, hSd⟩ := sandwich _ _ _ hBS hSZ (hQ := hfin)
  replace hSd : finrank E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) =
    finrank E ↥(finiteCohomology φ (chRep κ)) + finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := hSd
  have key : w ≠ 0 → ReciprocityTheory.Gal.H0 (chRep κ) = ⊥ ∧ finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1 := by
    intro h0
    obtain ⟨g, hg⟩ := exists_ne_one φ hφ κ w h0 hw
    have hz : ∀ m : E, chRep κ g m - m = 0 → m = 0 := by
      intro m hm
      have h1 : ((κ g : E) - 1) * m = 0 := by
        rw [sub_mul, one_mul]; simpa [chRep] using hm
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h)) hg
      · exact h
    refine ⟨?_, ?_⟩
    · rw [eq_bot_iff]
      intro m hm
      exact hz m (sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm g))
    · unfold ReciprocityTheory.Gal.B1
      rw [LinearMap.finrank_range_of_inj, finrank_self]
      rw [injective_iff_map_eq_zero]
      intro m hm
      exact hz m (congrFun hm g)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨h0, hB⟩ := key h.ne
    rw [h0, (hfil 0).1 (by omega), finrank_ddr φ _ hdr, finrank_bot, finrank_self] at hdim
    refine ⟨(Submodule.eq_of_le_of_finrank_eq hBS (by omega)).symm, hB⟩
  · obtain ⟨h0, hB⟩ := key h.ne'
    rw [h0, (hfil 0).2 (by omega), finrank_bot, finrank_bot, finrank_self] at hdim
    exact ⟨hS, by omega⟩
