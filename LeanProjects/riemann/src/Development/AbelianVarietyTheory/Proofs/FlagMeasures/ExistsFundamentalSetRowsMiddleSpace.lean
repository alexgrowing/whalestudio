import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolumeStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

noncomputable section

namespace GlobalTheory.DegVol.RefCov

theorem hermPk_eq_Hb {k r : ℕ} (u w : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hw : inWb k r w) :
    herm (Hpk k r) u w = herm (Hb k) (fun l => u (wI k r l)) (fun l => w (wI k r l)) := by
  have ue : ∀ a : Fin r, u (eI k r a) = 0 := fun a => hu _ (Or.inl (by simp [eI]))
  have us : ∀ b : Fin r, u (esI k r b) = 0 := fun b => hu _ (Or.inr (by have := b.2; simp [esI]; omega))
  have we : ∀ a : Fin r, w (eI k r a) = 0 := fun a => hw _ (Or.inl (by simp [eI]))
  have ws : ∀ b : Fin r, w (esI k r b) = 0 := fun b => hw _ (Or.inr (by have := b.2; simp [esI]; omega))
  have inner : ∀ l, (Hpk k r *ᵥ u) (wI k r l) = Rad.sg k l * u (wI k r l) := by
    intro l
    rw [Matrix.mulVec, dotProduct, Rad.sum3 (fun j => Hpk k r (wI k r l) j * u j)]
    simp only [ue, us, mul_zero, Finset.sum_const_zero, add_zero, zero_add, Rad.H_ww]
    rw [Finset.sum_eq_single l] <;> simp +contextual [eq_comm]
  rw [Rad.herm_Hb, herm, dotProduct, Rad.sum3 (fun i => star w i * (Hpk k r *ᵥ u) i)]
  simp only [Pi.star_apply, we, ws, star_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, inner]

theorem mem_smul_inf_rs {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (S : Submodule K V) (A : Submodule (𝓞 K) K)
    (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ A • (L ⊓ rs (𝓞 K) S) ↔ ∃ y : S, y ∈ A • L.comap (S.subtype.restrictScalars (𝓞 K)) ∧ (y : V) = x := by
  set f : S →ₗ[𝓞 K] V := S.subtype.restrictScalars (𝓞 K)
  have h1 : L ⊓ rs (𝓞 K) S = (L.comap f).map f := by
    ext z
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨hz, hs⟩; exact ⟨⟨z, hs⟩, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
  have h2 : A • (L.comap f).map f = (A • L.comap f).map f := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      rintro c hc _ ⟨y, hy, rfl⟩
      exact ⟨c • y, Submodule.smul_mem_smul hc hy, rfl⟩
    · rw [Submodule.map_le_iff_le_comap, Submodule.smul_le]
      intro c hc y hy
      rw [Submodule.mem_comap]
      change ((c • y : S) : V) ∈ A • Submodule.map f (Submodule.comap f L)
      rw [Submodule.coe_smul_of_tower]
      exact Submodule.smul_mem_smul hc ⟨y, hy, rfl⟩
  rw [h1, h2, Submodule.mem_map]
  rfl

end GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.DegVol.RefCov.rowsFund : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (S : Submodule K V) (HW : HermSpace K S) (k r : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ), (∀ x y : S, HW.B x y = H.B x y) → IsPlaces σ → Module.finrank K S = k + 1 → (∀ v, IsReal H k r (σ v) (Φ v)) → (∀ v, ∀ w ∈ S, inWb k r (Φ v w)) → ∀ (L : Submodule (𝓞 K) V) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), GlobalTheory.HermLat.IsUnimod HW (L.comap (S.subtype.restrictScalars (𝓞 K))) → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : V, x ∈ ipow 𝔡 n • (L ⊓ rs (𝓞 K) S) ∧ ((fun v => (ρ : ℂ) • fun l => Φ v x (wI k r l)) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  intro K V _ _ _ _ _ _ _ _ H hK S HW k r ι _ σ Φ hHW hσ hk hΦ hWb L 𝔡 n ρ hL h𝔡 hρ
  obtain ⟨F, hF, hU, hvol⟩ := GlobalTheory.T.unimodular_lattice_fundamentalSet_volume K S HW hK k ι σ (fun v x l => Φ v (x : V) (wI k r l)) hσ hk
    (fun v x y => by funext l; simp [(hΦ v).1 (x : V) y])
    (fun v c x => by funext l; simp [(hΦ v).2.1 c (x : V)])
    (fun v x y => by
      rw [← GlobalTheory.DegVol.RefCov.hermPk_eq_Hb _ _ (hWb v x x.2) (hWb v y y.2), (hΦ v).2.2.1, hHW])
    (L.comap (S.subtype.restrictScalars (𝓞 K))) 𝔡 n ρ hL h𝔡 hρ
  refine ⟨F, hF, fun a => ?_, hvol⟩
  obtain ⟨y, ⟨hy, hyF⟩, hyu⟩ := hU a
  refine ⟨(y : V), ⟨(GlobalTheory.DegVol.RefCov.mem_smul_inf_rs S _ L _).2 ⟨y, hy, rfl⟩, hyF⟩, ?_⟩
  rintro x ⟨hx, hxF⟩
  obtain ⟨y', hy', rfl⟩ := (GlobalTheory.DegVol.RefCov.mem_smul_inf_rs S _ L _).1 hx
  rw [hyu y' ⟨hy', hxF⟩]

end
