import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairInnerLatticeIndicesAndGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefinitePartLatticeDiscriminantEqQuotienStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.FixIdx

section

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem idx_inf_le (A B C W : Submodule R V) (hAB : A ≤ B) (hAW : A ≤ W) (h : idx B C ≠ 0) :
    idx A (C ⊓ W) ≠ 0 ∧ idx A (C ⊓ W) ≤ idx B C := by
  have e : idx A (C ⊓ W) = idx A C := by
    unfold idx
    rw [← AddSubgroup.inf_relIndex_right (C ⊓ W).toAddSubgroup, ← AddSubgroup.inf_relIndex_right C.toAddSubgroup]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hAW hx.2⟩, hx.2⟩⟩
  rw [e]
  have hle : A.toAddSubgroup ≤ B.toAddSubgroup := hAB
  exact ⟨fun h0 => h (AddSubgroup.relIndex_eq_zero_of_le_right hle h0),
    AddSubgroup.relIndex_le_of_le_right hle h⟩

theorem gens_of_sup (A C D : Submodule R V) (hD : A ⊓ C ≤ D) (hDA : D ≤ A) (e : ℕ) (t : Finset V)
    (ht : t.card ≤ e) (h : A ⊔ C = C ⊔ Submodule.span R (t : Set V)) :
    ∃ t' : Finset V, t'.card ≤ e ∧ A = D ⊔ Submodule.span R (t' : Set V) := by
  have h1 : ∀ x : V, ∃ a : V, x ∈ t → a ∈ A ∧ x - a ∈ C := by
    intro x
    by_cases hx : x ∈ t
    · have : x ∈ A ⊔ C := by rw [h]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 this
      exact ⟨a, fun _ => ⟨ha, by simpa using hc⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h1
  have hsA : Submodule.span R ((t.image f : Finset V) : Set V) ≤ A := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact (hf x hx).1
  refine ⟨t.image f, Finset.card_image_le.trans ht, le_antisymm ?_ (sup_le hDA hsA)⟩
  have h2 : A ≤ C ⊔ Submodule.span R ((t.image f : Finset V) : Set V) := by
    refine le_trans (le_sup_left (b := C)) ?_
    rw [h]
    refine sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)
    have : x = (x - f x) + f x := by abel
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem_sup (hf x hx).2
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)))
  intro x hx
  obtain ⟨c, hc, s, hs, rfl⟩ := Submodule.mem_sup.1 (h2 hx)
  refine Submodule.add_mem_sup (hD ⟨?_, hc⟩) hs
  simpa using A.sub_mem hx (hsA hs)

end

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in

theorem isLatMod_of_idx (A B : Submodule (𝓞 K) V) (S I : Submodule K V) (hA : IsLatMod A S I) (hBA : B ≤ A)
    (hI : rs (𝓞 K) I ≤ B) (h : idx A B ≠ 0) : IsLatMod B S I := by
  obtain ⟨⟨M, hM, hL⟩, hsp⟩ := hA
  refine ⟨⟨B ⊓ M, ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · haveI : IsNoetherian (𝓞 K) M := isNoetherian_of_fg_of_noetherian _ hM
    exact isNoetherian_submodule.1 this _ inf_le_right
  · rw [inf_sup_assoc_of_le _ hI, ← hL]
    exact (inf_eq_left.2 hBA).symm
  · rw [← hsp]; exact Submodule.span_mono hBA
  · rw [← hsp, Submodule.span_le]
    intro x hx
    have h1 : (idx A B) • x ∈ B := AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup (K := A.toAddSubgroup) hx
    have h2 : ((idx A B : K))⁻¹ • ((idx A B) • x) ∈ Submodule.span K (B : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 h), one_smul] at h2

variable [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}

theorem radical (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) :
    II N.F N.F' ≤ wSp N.F N.F' ∧
      ∀ x ∈ wSp N.F N.F', (∀ y ∈ wSp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
  obtain ⟨-, -, -, -, -, -, hw, -, hPD, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have h2 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B y x = 0 := by
    intro x hx y hy
    rw [← hw] at hx
    rw [← H.herm, (mem_perp_iff H _ x).1 hx y (Submodule.mem_sup_left (Submodule.mem_sup_left hy.1)),
      star_zero]
  rw [hw]
  refine ⟨le_sup_right, fun x hx => ⟨fun hx0 => ?_, fun hxI y hy => h2 y hy x hxI⟩⟩
  obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
  have haa := hx0 a (Submodule.mem_sup_left ha)
  rw [map_add, LinearMap.add_apply, h2 a (Submodule.mem_sup_left ha) i hi, add_zero] at haa
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have ha0 : a = 0 := by
    by_contra hne
    have := hPD τ ⟨a, ha⟩ (fun h => hne (congrArg Subtype.val h))
    have e : GlobalTheory.Mass.hRes H.B.flip N.Wt ⟨a, ha⟩ ⟨a, ha⟩ = H.B a a := rfl
    rw [e, haa] at this
    simp at this
  rw [ha0, zero_add]; exact hi

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) ∧ 0 < N.gI g Λ ∧ 0 < N.iI g Λ ∧ (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del ∧ ((N.gI g Λ : ℝ) * N.iI g Λ ≤ N.Del) ∧ GenBy (flagPairDefinitePartLattice N.F N.F' Λ) (latLa N.F N.F' Λ (g : 𝓞 K)) N.j ∧ del H (latTh N.F N.F' Λ) = (N.gI g Λ : ℝ) * N.iI g Λ * N.NT ∧ IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨hb0, -, hDel, hbar⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hΛ
  obtain ⟨hnB, -, h1L, hB, t, ht, hgen⟩ := GlobalTheory.T.flagPairInnerLattice_indices_and_generators K V H hK r N g Λ hg hΛ
  obtain ⟨hd0, -, -, hlat0, -⟩ := GlobalTheory.T.flagPairDefinitePartLattice_discriminant_eq_quotient K V H hK r N g Λ hg hΛ
  obtain ⟨hIW, hrad⟩ := radical hK N
  have hww : wSp N.F' N.F = wSp N.F N.F' := by
    unfold wSp V0
    rw [sup_comm N.F'.X, Set.pair_comm]
  have hn0 : idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) ≠ 0 := by
    intro h0
    rw [h0] at hnB
    simp only [Nat.cast_zero, zero_mul] at hnB
    linarith
  have hB0 : cardB N.F N.F' Λ ≠ 0 := by
    intro h0
    rw [h0] at hnB
    simp only [Nat.cast_zero, mul_zero] at hnB
    linarith
  have hThLa : latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) := by
    intro x hx
    refine ⟨⟨⟨(h1L hx.1).2, by rw [hww]; exact hx.2⟩, ⟨(h1L hx.1).1, hx.2⟩⟩, ?_⟩
    obtain ⟨l, hl, i, hi, rfl⟩ := Submodule.mem_sup.1 hx.1.1
    refine Submodule.mem_sup.2 ⟨(l, l), ⟨⟨hl.1, hl.1⟩, ?_⟩, (i, i), ⟨hi.2, hi.1⟩, rfl⟩
    simp
  have hLa0 : latLa N.F N.F' Λ (g : 𝓞 K) ≤ flagPairDefinitePartLattice N.F N.F' Λ := fun x hx => hx.1.2
  have hLaL : latLa N.F N.F' Λ (g : 𝓞 K) ≤ latL N.F N.F' Λ ⊓ latL N.F' N.F Λ :=
    fun x hx => ⟨hx.1.2.1, hx.1.1.1⟩
  have hmul : N.iI g Λ * N.gI g Λ = idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) :=
    AddSubgroup.relIndex_mul_relIndex _ _ _ hThLa hLa0
  obtain ⟨hp0, hpn⟩ : idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) ≠ 0 ∧
      idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) ≤ idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) :=
    idx_inf_le _ _ _ _ inf_le_left inf_le_right hn0
  have hq0 : idx (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ) (lamOne N.F N.F' Λ) ≠ 0 := fun h0 =>
    hn0 (AddSubgroup.relIndex_eq_zero_of_le_right
      (show (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ).toAddSubgroup ≤ (latL N.F N.F' Λ).toAddSubgroup from
        fun x hx => hx.1) h0)
  have hiB : N.iI g Λ ≤ cardB N.F N.F' Λ :=
    (idx_inf_le _ _ _ (rs (𝓞 K) (wSp N.F N.F')) hLaL (hLa0.trans inf_le_right) hq0).2.trans hB
  have hi0 : N.iI g Λ ≠ 0 := fun h0 => hp0 (by rw [← hmul, h0, zero_mul])
  have hg0 : N.gI g Λ ≠ 0 := fun h0 => hp0 (by rw [← hmul, h0, mul_zero])
  have hmulR : (N.gI g Λ : ℝ) * N.iI g Λ = idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) := by
    rw [← hmul]; push_cast; ring
  have hmain : (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del := by
    rw [← hDel, ← hnB, sq (N.iI g Λ : ℝ), ← mul_assoc, hmulR]
    have e1 : (idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) : ℝ) ≤ idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) := by
      exact_mod_cast hpn
    have e2 : (N.iI g Λ : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast hiB
    gcongr
  have hITh : rs (𝓞 K) (II N.F N.F') ≤ latTh N.F N.F' Λ := by
    intro x hx
    refine ⟨⟨Submodule.mem_sup_right hx, ?_⟩, hIW hx⟩
    exact (mem_perp_iff H _ x).2 fun y hy => (mem_perp_iff H _ x).1 (hIW hx) y (Submodule.mem_sup_left hy)
  have hlat : IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') :=
    isLatMod_of_idx _ _ _ _ hlat0 (hThLa.trans hLa0) hITh hp0
  refine ⟨hThLa, Nat.pos_of_ne_zero hg0, Nat.pos_of_ne_zero hi0, hmain, le_trans ?_ hmain, ?_, ?_, hlat⟩
  · have e1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi0
    have e2 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    calc (N.gI g Λ : ℝ) * N.iI g Λ = (N.gI g Λ : ℝ) * (N.iI g Λ * 1) * 1 ^ 2 := by ring
      _ ≤ (N.gI g Λ : ℝ) * (N.iI g Λ * N.iI g Λ) * (N.bI Λ : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  · have h1 : lamOne N.F N.F' Λ ≤ latL N.F N.F' Λ := h1L.trans inf_le_left
    obtain ⟨t', ht', h'⟩ := ((GlobalTheory.Mass.LatticeGens.gens_and_count K V _ _ h1 hn0).2 N.j t ht hgen).2
      (flagPairDefinitePartLattice N.F N.F' Λ ⊔ lamOne N.F N.F' Λ) le_sup_right (sup_le inf_le_left h1)
    exact gens_of_sup _ _ _
      (le_trans (show flagPairDefinitePartLattice N.F N.F' Λ ⊓ lamOne N.F N.F' Λ ≤ latTh N.F N.F' Λ from
        fun x hx => ⟨hx.2, hx.1.2⟩) hThLa) hLa0 N.j t' ht' h'
  · rw [(DelScale.main K V H hK _ _ _ _ hIW hrad hlat0 hlat).2.2.1, hd0, hmulR]
    have : idx (latTh N.F N.F' Λ) (flagPairDefinitePartLattice N.F N.F' Λ) = 1 :=
      AddSubgroup.relIndex_eq_one.2 (hThLa.trans hLa0)
    rw [gidx, this]
    simp

end GlobalTheory.DegCnt.FixIdx
