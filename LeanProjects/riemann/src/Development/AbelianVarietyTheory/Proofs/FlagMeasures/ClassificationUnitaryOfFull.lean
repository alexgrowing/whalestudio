import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraPermuteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignKeyTrueLtFalse
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariant
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.DSSU

theorem classU_of_classF : ∀ n : ℕ, (∀ ε : Fin n → Bool, ClassF ε) → ClassU n := by
  intro n hF
  unfold ClassF at hF
  choose F hP hC hE using hF
  obtain ⟨std, t, ht, hst, hren⟩ := GlobalTheory.SignRenumber.block_renumbering n
  have e1a : ∀ (ε : Fin n → Bool) (x : Fin n), std ε (t ε x) = ε x := fun ε x => congrFun (ht ε).1 x
  have hmono : ∀ (ε : Fin n → Bool) (a b : Fin n), a < b → std ε (t ε a) = std ε (t ε b) → t ε a < t ε b := by
    intro ε a b hab h
    rw [e1a, e1a] at h
    exact (ht ε).2 a b hab h
  refine ⟨fun ε lam => (F (std ε)).H (lam ∘ (t ε).symm), fun ε lam => inferInstance, fun ε lam => inferInstance,
    fun ε lam g => (F (std ε)).π (lam ∘ (t ε).symm) (g.submatrix (t ε).symm (t ε).symm), ?_, ?_⟩
  · intro ε lam hlam
    have hpar : IsParU (lam ∘ (t ε).symm) :=
      ⟨hlam.1.injective.comp (t ε).symm.injective, fun a => hlam.2 _⟩
    have e2 : (lam ∘ (t ε).symm) ∘ (t ε) = lam := by funext a; simp
    have h1 := GlobalTheory.T.harish_chandra_permute n (std ε) _ ((F (std ε)).π (lam ∘ (t ε).symm)) (lam ∘ (t ε).symm) (t ε)
      (hmono ε) (by rw [e2]; exact hlam.1) (hP _ _ hpar)
    rw [(ht ε).1, e2] at h1
    exact h1
  · intro ε H' _ _ σ' hσ
    let σ₀ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H') := fun g => σ' (g.submatrix (t ε) (t ε))
    have hσ₀ : IsSqIntIrr (std ε) σ₀ := by
      rw [(GlobalTheory.DSId.PermK.permKType n (std ε) (t ε) H' σ₀ (hmono ε)).2.2.2.1]
      have e3 : (fun g : Matrix (Fin n) (Fin n) ℂ => σ₀ (g.submatrix (t ε).symm (t ε).symm)) = σ' := by
        funext g
        simp only [σ₀, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
      rw [(ht ε).1, e3]
      exact hσ
    obtain ⟨lam₀, hpar₀, T, hT⟩ := hE (std ε) H' σ₀ hσ₀
    obtain ⟨w, s, hw, hanti, hs⟩ := hren ε (lam₀ ∘ t ε) (hpar₀.1.comp (t ε).injective)
    refine ⟨s, ((lam₀ ∘ t ε) ∘ w) ∘ s, ⟨hanti, fun a => hpar₀.2 _⟩, hs, ?_⟩
    have hstd : std (ε ∘ s) = std ε := (hst ε s).1
    have htt : t (ε ∘ s) = s.trans (t ε) := Equiv.ext ((hst ε s).2 hs)
    show UEquiv (ε ∘ s) (fun g => σ' (g.submatrix s.symm s.symm))
      (fun g => (F (std (ε ∘ s))).π ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (t (ε ∘ s)).symm)
        (g.submatrix (t (ε ∘ s)).symm (t (ε ∘ s)).symm))
    rw [htt, hstd]
    have hconj : ConjK (std ε) lam₀ ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (s.trans (t ε)).symm) := by
      refine ⟨(t ε).symm.trans (w.trans (t ε)), ?_, ?_⟩
      · intro a
        simp only [Equiv.trans_apply]
        rw [e1a, hw, ← e1a ε ((t ε).symm a), Equiv.apply_symm_apply]
      · funext a
        simp [Equiv.symm_trans_apply]
    obtain ⟨T2, hT2⟩ := hC (std ε) lam₀ _ hpar₀ hconj
    refine ⟨T.trans T2, ?_⟩
    intro g hg v
    have hcomp : std ε ∘ (s.trans (t ε)) = ε ∘ s := by
      funext a; simp [Equiv.trans_apply, e1a]
    have hh : g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm ∈ UJset (std ε) :=
      (((GlobalTheory.Dec.PermGroup.permGroup n (std ε) (s.trans (t ε))).1 g).1).mp (by rw [hcomp]; exact hg)
    have hσh : σ₀ (g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm) = σ' (g.submatrix s.symm s.symm) := by
      show σ' ((g.submatrix _ _).submatrix (t ε) (t ε)) = _
      rw [Matrix.submatrix_submatrix]
      congr 2 <;> funext a <;> simp [Equiv.symm_trans_apply]
    simp only [LinearIsometryEquiv.trans_apply]
    rw [← hσh, hT _ hh, hT2 _ hh]

end GlobalTheory.DSSU
