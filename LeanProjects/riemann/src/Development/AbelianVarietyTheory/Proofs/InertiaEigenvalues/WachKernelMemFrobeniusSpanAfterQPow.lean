import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLetterRingFrobeniusDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFrobeniusFlatCrystallineStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.PhiSpanKer

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA' (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have h := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at h
  exact h

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

variable {m : ℕ} (u : Fin m → LetA O n)

theorem mem_sum_form (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T))
    (hdec : ∀ a : LetA O n, ∃ c : Fin m → LetA O n, a = ∑ j, u j * W.φA (c j))
    {w : W.DD T} (hw : w ∈ φspan W T S) :
    ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w = ∑ j, u j • W.φD T (z j) := by
  have hadd : ∀ w w' : W.DD T,
      (∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w = ∑ j, u j • W.φD T (z j)) →
      (∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w' = ∑ j, u j • W.φD T (z j)) →
      ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w + w' = ∑ j, u j • W.φD T (z j) := by
    rintro w w' ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    refine ⟨z + z', fun j => S.add_mem (hz j) (hz' j), ?_⟩
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  have key : ∀ w ∈ φspan W T S, ∀ a : LetA O n,
      ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ a • w = ∑ j, u j • W.φD T (z j) := by
    intro w hw
    unfold φspan at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      intro a
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hdec a
      refine ⟨fun j => c j • y, fun j => S.smul_mem _ hy, ?_⟩
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [φD_smulA', mul_smul]
    | zero => intro a; exact ⟨0, fun j => S.zero_mem, by simp⟩
    | add x y _ _ hx hy => intro a; rw [smul_add]; exact hadd _ _ (hx a) (hy a)
    | smul b x _ hx => intro a; rw [smul_smul]; exact hx (a * b)
  simpa using key w hw 1

theorem phispan_of (hdec : ∀ a : LetA O n, ∃ c : Fin m → LetA O n, a = ∑ j, u j * W.φA (c j))
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (hinj : Function.Injective (W.map ι)) (hex : Function.Exact (W.map ι) (W.map π))
    (hπN : ∀ x ∈ W.N T₁, W.map π x ∈ W.N T₂)
    (hind : ∀ z : Fin m → W.DD T₂, (∀ j, z j ∈ W.N T₂) →
      ∑ j, u j • W.φD T₂ (z j) = 0 → ∀ j, z j = 0) :
    ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (LetA O n)),
      ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (LetA O n))) := by
  intro y hy
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy
  obtain ⟨k, hk⟩ := W.N_φinv T₁ _ hy
  refine ⟨k, ?_⟩
  have hk' : W.Q ^ k • W.map ι y ∈ φspan W T₁ (W.N T₁) := hk
  obtain ⟨w, hw, he⟩ := mem_sum_form W u T₁ (W.N T₁) hdec hk'
  have hπ0 : ∀ j, W.map π (w j) = 0 := by
    refine hind _ (fun j => hπN _ (hw j)) ?_
    have h1 := congrArg (W.map π) he
    rw [map_smulA, (hex _).2 ⟨y, rfl⟩, smul_zero, map_sum] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulA, W.map_φ]
  choose w' hw' using fun j => (hex (w j)).1 (hπ0 j)
  have hmem : ∀ j, w' j ∈ (W.N T₁).comap ((W.map ι).restrictScalars (LetA O n)) := by
    intro j
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hw']
    exact hw j
  have heq : W.Q ^ k • y = ∑ j, u j • W.φD T₀ (w' j) := by
    apply hinj
    rw [map_smulA, he, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulA, W.map_φ, hw']
  rw [heq]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w' j, hmem j, rfl⟩)

end Generic

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π c0 c1 c2 hses
  have hex := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T₀ T₁ T₂ ι π hses
  exact phispan_of W (fun j : Fin l => (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL))
    (GlobalTheory.T.wachLetterRing_frobenius_decomposition D HW l K s LL h) ι π hex.1 hex.2.1 (fun x hx => W.map_N π c1 c2 x hx)
    (GlobalTheory.T.wachFrobenius_flat_crystalline D HW F l K s LL h T₂ c2)

end GlobalTheory.NL.PhiSpanKer
