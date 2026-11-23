import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExistsStatement
open NumberField

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.TrueCx Topology Filter

noncomputable section

namespace GlobalTheory.LocInj

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domI : IsOpen (DomI ι p q) := by
  have hc : Continuous (flat : (ι → Matrix (Fin p) (Fin q) ℂ) → ι × Fin p × Fin q → ℂ) :=
    continuous_pi fun x => (continuous_apply x.1).matrix_elem x.2.1 x.2.2
  exact GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage hc

theorem continuousAt_moeb (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (hu : IsUnit (M.toBlocks₂₁ * z + M.toBlocks₂₂).det) :
    ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => moeb M w) z := by
  unfold moeb
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  have h1 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => A * w + B) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have h2 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => C * w + D) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have hi : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℂ → Matrix (Fin q) (Fin q) ℂ) (C * z + D) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hu.ne_zero
  have h3 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (C * w + D)⁻¹) z :=
    ContinuousAt.comp (g := Inv.inv) hi h2.continuousAt
  have hm : Continuous (fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact ContinuousAt.comp (g := fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2)
    (f := fun w => (A * w + B, (C * w + D)⁻¹)) hm.continuousAt (h1.continuousAt.prodMk h3)

theorem continuousAt_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : ι → Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ DomI ι p q) : ContinuousAt (moebI g) z := by
  refine continuousAt_pi.2 fun t => ?_
  have hu := GlobalTheory.HodgeDomain.kapQ_isUnit (hg t trivial) (hz t)
  exact ContinuousAt.comp (g := fun w => moeb ((g t : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) w)
    (continuousAt_moeb _ _ hu) (continuous_apply t).continuousAt

theorem moebI_one (z : ι → Matrix (Fin p) (Fin q) ℂ) : moebI (1 : ι → GL (Fin p ⊕ Fin q) ℂ) z = z := by
  funext t
  simp [moebI, GlobalTheory.TrueCx.PointWell.moeb_one]

end GlobalTheory.LocInj

namespace GlobalTheory.LocInj

open GlobalTheory.ShFam.SecFrame

theorem continuous_frameAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) {Tau : Type} (κ : Tau ≃ X.Ψ) : Continuous (frameAt X hj κ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun z : Tau → Matrix (Fin j) (Fin (r - j)) ℂ =>
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1)
  refine continuous_const.matrix_mul ?_
  simp only [reindex_symm, reindex_apply, Equiv.symm_symm]
  exact (continuous_const.matrix_fromBlocks (continuous_apply _) continuous_const continuous_const).matrix_submatrix _ _

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  intro E _ _ _ r j X hj Tau _ κ hp z₀ hz₀
  haveI : LocallyCompactSpace (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Tau → Fin j → Fin (r - j) → ℂ))

  obtain ⟨C, hCn, hCD, hCc⟩ := local_compact_nhds (isOpen_domI.mem_nhds hz₀)
  set K := frameAt X hj κ '' C with hK
  have hKc : IsCompact K := hCc.image (continuous_frameAt X hj κ)
  have hKd : K ⊆ X.dom := by
    rintro _ ⟨z, hz, rfl⟩
    exact frameAt_mem X hj κ hp (hCD hz)
  have hS := GlobalTheory.T.finite_setOf_lact_eq_rmul_blockTriangular E r X K hKc hKd
  set S := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
    (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
    (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
    ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b} with hSdef

  have hev : ∀ γ ∈ S, ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, γ ≠ 1 → moebI (toUpq X hj κ γ) w.1 ≠ w.2 := by
    intro γ hγS
    by_cases h1 : γ = 1
    · exact Filter.Eventually.of_forall fun _ h => absurd h1 h
    have hne : moebI (toUpq X hj κ γ) z₀ ≠ z₀ := by
      intro h
      have hx := frameAt_mem X hj κ hp hz₀
      refine h1 (GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq E r j X hj Tau κ hp γ hγS.1 _ hx ?_)
      rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, h]
    have hc : ContinuousAt (fun w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) =>
        moebI (toUpq X hj κ γ) w.1) (z₀, z₀) :=
      ContinuousAt.comp (g := moebI (toUpq X hj κ γ))
        (continuousAt_moebI (gammaU_le X hj κ hp ⟨γ, hγS.1, rfl⟩) hz₀) continuous_fst.continuousAt
    have hO : IsOpen {w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) |
        w.1 ≠ w.2} := isOpen_ne_fun continuous_fst continuous_snd
    have := (hc.prodMk continuous_snd.continuousAt).preimage_mem_nhds (hO.mem_nhds hne)
    rw [nhds_prod_eq] at this
    exact Filter.mem_of_superset this fun w hw _ => hw
  have hCC : C ×ˢ C ∈ 𝓝 z₀ ×ˢ 𝓝 z₀ := Filter.prod_mem_prod hCn hCn
  have hall : ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, (fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b) w.1 w.2 :=
    (Filter.Eventually.and hCC ((Filter.eventually_all_finite hS).2 hev)).mono fun w h => ⟨h.1.1, h.1.2, h.2⟩
  obtain ⟨t, ht, htP⟩ := (Filter.eventually_prod_self_iff (la := 𝓝 z₀)
    (r := fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b)).1 hall
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, ?_⟩
  rintro z ⟨hzt, hzD⟩ z' ⟨hzt', hzD'⟩ γ hγ e
  obtain ⟨hzC, hzC', hmove⟩ := htP z (interior_subset hzt) z' (interior_subset hzt')
  have hx := frameAt_mem X hj κ hp hzD
  have hy := frameAt_mem X hj κ hp hzD'
  have hgx := KU.lact_dom X hγ hx
  set x := frameAt X hj κ z
  set y := frameAt X hj κ z'
  have hpt : domPt X hj κ (lact γ x) = domPt X hj κ y := by
    rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, domPt_frameAt, e]
  have hblk : ∀ τ (a c : Fin r), X.p0 ≤ a → (c : ℕ) < X.p0 → ((mat y τ)⁻¹ * mat (lact γ x) τ) a c = 0 := by
    intro τ
    refine GlobalTheory.TrueCx.PointWell.block_of_moeb_eq X hj hp hy hgx τ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    exact (congrFun hpt s).symm
  have hγS : γ ∈ S := by
    refine ⟨hγ, x, ⟨z, hzC, rfl⟩, y, ⟨z', hzC', rfl⟩, fun τ => (mat y τ)⁻¹ * mat (lact γ x) τ, fun τ => ?_,
      fun τ a c hc ha => hblk τ a c (not_lt.1 ha) hc, ?_⟩
    · show ((mat y τ)⁻¹ * mat (lact γ x) τ).det ≠ 0
      rw [det_mul, det_nonsing_inv]
      exact mul_ne_zero (by rw [Ring.inverse_eq_inv']; exact inv_ne_zero (hy τ).1) (hgx τ).1
    · funext τ
      show mat (lact γ x) τ = mat y τ * ((mat y τ)⁻¹ * mat (lact γ x) τ)
      rw [mul_nonsing_inv_cancel_left _ _ (hy τ).1.isUnit]
  by_contra hne
  by_cases h1 : γ = 1
  · subst h1
    apply hne
    rw [e, map_one, moebI_one]
  · exact hmove γ hγS h1 e.symm

end GlobalTheory.LocInj
