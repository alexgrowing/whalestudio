import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairBDual
import Formalism.LocalToGlobal.Columns.CoefModAt

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisDual

open Formalism.HermitianLatticesTheory Formalism.UG Formalism.L2.Forms
open scoped Matrix

theorem natCast_notMem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {l s : ℕ}
    (hl : l.Prime) (hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) (hs : ¬ l ∣ s) : (s : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hcop : Nat.Coprime l s := (hl.coprime_iff_not_dvd).2 hs
  obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hlw
  · simpa using h

theorem isBasisAt_tauLat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}
    (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) {l : ℕ} (hl : l.Prime)
    (hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) (M : Submodule (𝓞 E) (Fin n → E)) (B : GL (Fin n) E)
    (hB : IsLocBasis l (M : Set (Fin n → E)) B) : IsBasisAt w (tauLat emb τ M) (bc (emb τ) B) := by
  have h1 : ¬ l ∣ 1 := fun h => hl.one_lt.ne' (Nat.dvd_one.1 h)
  unfold IsBasisAt
  apply le_antisymm
  · rw [← localized_localized w (colLat _)]
    refine localization_mono _ ?_
    unfold tauLat
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s', hs', hint⟩ := (hB x).1 ⟨1, h1, by simpa using hx⟩
    refine ⟨(s' : 𝓞 K), natCast_notMem w hl hlw hs', ?_⟩
    rw [lc_mem_colLat]
    intro a
    have e : ((s' : 𝓞 K) • fun b => emb τ (x b)) = fun b => emb τ (((s' : E) • x) b) := by
      funext b
      simp [Algebra.smul_def]
    rw [e, Formalism.L2.Col.vl_bc_inv_mulVec, Matrix.mulVec_smul]
    obtain ⟨r, hr⟩ := hint a
    exact du_map_mem_one (emb τ) (Submodule.mem_one.2 ⟨r, by rw [hr]; rfl⟩)
  · rw [← localized_localized w (tauLat emb τ M)]
    refine localization_mono _ ?_
    unfold colLat
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s', hs', hmem⟩ := (hB (fun a => (B : Matrix (Fin n) (Fin n) E) a j)).2 ⟨1, h1, fun a => by
      have e : (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ fun a => (B : Matrix (Fin n) (Fin n) E) a j) a =
          (1 : Matrix (Fin n) (Fin n) E) a j := by
        have h2 : ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (B : Matrix (Fin n) (Fin n) E) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [← h2]
        rfl
      rw [e, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩⟩
    refine ⟨(s' : 𝓞 K), natCast_notMem w hl hlw hs', ?_⟩
    refine Submodule.subset_span ⟨_, hmem, ?_⟩
    funext b
    simp [Algebra.smul_def, bc_coe]

end GlobalTheory.LocBasisDual

namespace GlobalTheory.LocBasisDual

theorem basisAt_dualFr_tauLat : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → (∃ B, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B) ∧ Submodule.IsLattice K (dualFr (tauLat emb τ M)) ∧ ∀ B : GL (Fin n) E, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B → IsBasisAt w (dualFr (tauLat emb τ M)) (inside₂ K n (Matrix.GeneralLinearGroup.map (emb τ) B)) := by
  intro E K _ _ _ _ ι _ n emb τ w l hl hlw M hM
  have : Fact l.Prime := ⟨hl⟩
  refine ⟨Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis l E M hM.fg hM.span_eq_top,
    Formalism.L2.DIV.dualFr_tauLat_isLattice emb τ M hM, fun B hB => ?_⟩
  exact pb_isBasisAt_dualFr w _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
    (isBasisAt_tauLat emb τ w hl hlw M B hB)

end GlobalTheory.LocBasisDual
