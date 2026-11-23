import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FV
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapMPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.TermAff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm.AssemblyHe1

theorem capO_isAffineOpen {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q)
    {n : ℕ} (i : Fin (n + 1) → U.ι) : IsAffineOpen (capO U.U i) := by
  classical
  have h := U.inter (Finset.image i Finset.univ) ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  have e : (⨅ α ∈ Finset.image i Finset.univ, U.U α) = capO U.U i := by
    refine le_antisymm ?_ ?_
    · exact le_iInf fun k => iInf₂_le (i k) (Finset.mem_image_of_mem i (Finset.mem_univ k))
    · refine le_iInf₂ fun α hα => ?_
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
      exact capO_le U.U i k
  rwa [e] at h

def capEquiv {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) : HU (Fk q U a) (capT (Vk q U a) i) a ≃ₗ[K] CH.H (FV q (capO U.U i) a) a :=
  LinearEquiv.ofBijective ((capM q U a n i).pull a) (capM_bij q U a n i a)

theorem capEquiv_apply {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (x : HU (Fk q U a) (capT (Vk q U a) i) a) :
    capEquiv q U a n i x = (capM q U a n i).pull a x := rfl

theorem term : ∀ (K : Type) [Field K] [CharZero K],
    ∃ t : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι),
      HU (Fk q U a) (capT (Vk q U a) i) a ≃ₗ[K] OmU q (capO U.U i) a,
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a m n : ℕ) (i : Fin (n + 1) → U.ι)
      (θ : Fin (m + 1) → Fin (n + 1)) (x : HU (Fk q U a) (capT (Vk q U a) (i ∘ θ)) a),
      t q U a n i ((resU (Fk q U a) (U := capT (Vk q U a) (i ∘ θ)) (V := capT (Vk q U a) i) fun T hT k => hT (θ k)).pull a x) =
        formRes q (capO_comp U.U i θ) a (t q U a m (i ∘ θ) x)) ∧
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
      (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ)
      (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T)) (n : ℕ) (i : Fin (n + 1) → U.ι)
      (hG' : ∀ T, capT (Vk q U a) i T →
        capT (Vk p W a) (τ ∘ i) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
      (x : HU (Fk p W a) (capT (Vk p W a) (τ ∘ i)) a),
      t q U a n i ((morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
        (U' := capT (Vk q U a) i) hG').pull a x) =
        formRes q (hτ n i) a (formPull hu (capO W.U (τ ∘ i)) a (t p W a n (τ ∘ i) x)) := by
  intro K _ _
  obtain ⟨t0, h0⟩ := CrystallineSemistableComparison.Om.Nt2.TermAff.term_aff K
  refine ⟨fun {X} q _ U a n i => (capEquiv q U a n i).trans (t0 q (capO U.U i) (capO_isAffineOpen q U i) a), ?_, ?_⟩
  · intro X q _ U a m n i θ x
    have hle : KS q (a + 1) {capO U.U i} ≤ KS q (a + 1) {capO U.U (i ∘ θ)} := by
      rintro T ⟨h1, V', rfl, h2⟩
      exact ⟨h1, _, rfl, inU_mono q (capO_comp U.U i θ) T h2⟩
    have hG : ∀ T, KS q (a + 1) {capO U.U i} T → KS q (a + 1) {capO U.U (i ∘ θ)} ((pullM (𝟙 X) (Category.id_comp q) a).G.obj T) :=
      fun T hT => ks_pull (𝟙 X) (Category.id_comp q) (capO_comp U.U i θ) (a + 1) a T hT
    have e1 := capM_res U a m n i θ x
    have e2 := morU_id (Category.id_comp q) a _ _ hG hle a ((capM q U a m (i ∘ θ)).pull a x)
    have e3 := h0 q q (𝟙 X) (Category.id_comp q) (capO U.U i) (capO U.U (i ∘ θ)) (capO_isAffineOpen q U i)
      (capO_isAffineOpen q U (i ∘ θ)) (capO_comp U.U i θ) a hG ((capM q U a m (i ∘ θ)).pull a x)
    have e4 := formPull_id q a (capO U.U (i ∘ θ)) (t0 q (capO U.U (i ∘ θ)) (capO_isAffineOpen q U (i ∘ θ)) a ((capM q U a m (i ∘ θ)).pull a x))
    change t0 q (capO U.U i) _ a ((capM q U a n i).pull a _) = formRes q _ a (t0 q (capO U.U (i ∘ θ)) _ a ((capM q U a m (i ∘ θ)).pull a x))
    rw [e1, ← e2, e3]
    exact congrArg (formRes q (capO_comp U.U i θ) a) e4
  · intro X Y q p _ _ u hu U W τ hτ a hG n i hG' x
    have h : ∀ T, KS q (a + 1) {capO U.U i} T → KS p (a + 1) {capO W.U (τ ∘ i)} ((pullM u hu a).G.obj T) :=
      fun T hT => ks_pull u hu (hτ n i) (a + 1) a T hT
    have e1 := capM_pull u hu U W τ a hG n i hG' h x
    have e3 := h0 q p u hu (capO U.U i) (capO W.U (τ ∘ i)) (capO_isAffineOpen q U i)
      (capO_isAffineOpen p W (τ ∘ i)) (hτ n i) a h ((capM p W a n (τ ∘ i)).pull a x)
    change t0 q (capO U.U i) _ a ((capM q U a n i).pull a _) = formRes q _ a (formPull hu _ a (t0 p (capO W.U (τ ∘ i)) _ a ((capM p W a n (τ ∘ i)).pull a x)))
    rw [e1, e3]

end GlobalTheory.CompanionTheory.OmGlobTerm.AssemblyHe1
