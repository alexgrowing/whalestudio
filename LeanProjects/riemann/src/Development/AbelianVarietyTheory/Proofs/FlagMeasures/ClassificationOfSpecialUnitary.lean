import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmulOneMem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraParameterDescentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtensionPreservesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestTypeParameterAscentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtensionStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SUtoU

variable {n : ℕ}

theorem equivOn_of_ext (hn : 1 ≤ n) (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (m : ℤ)
    {σ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (h : Ext ε m σ π) (h' : Ext ε m σ' π') (hT : EquivOn (SUset ε) σ σ') : EquivOn (UJset ε) π π' := by
  obtain ⟨T, hT⟩ := hT
  refine ⟨T, fun g hg v => ?_⟩
  obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := (GlobalTheory.T.unitary_to_special_unitary_local n hn ε).1 g hg
  rw [h z hz g₀ hg₀, h' z hz g₀ hg₀, _root_.smul_apply, _root_.smul_apply,
    LinearIsometryEquiv.map_smul, hT g₀ hg₀ v]

def meanFree (lam : Fin n → ℝ) : Fin n → ℝ := fun a => lam a - (∑ b, lam b) / n

def ExtProp (ε : Fin n → Bool) (F : Fam n) (lam : Fin n → ℝ)
    (π : Matrix (Fin n) (Fin n) ℂ → (F.H (meanFree lam) →L[ℂ] F.H (meanFree lam))) : Prop :=
  ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ Ext ε m (F.π (meanFree lam)) π ∧ IsHCU ε lam π

def famU (ε : Fin n → Bool) (F : Fam n) : Fam n where
  H lam := F.H (meanFree lam)
  nacg _ := inferInstance
  ips _ := inferInstance
  π lam := Classical.epsilon (ExtProp ε F lam)

theorem parS_meanFree (hn : 1 ≤ n) {lam : Fin n → ℝ} (hlam : IsParU lam) : IsParS (meanFree lam) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [meanFree, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hn0, sub_self]
  · intro a b h
    exact hlam.1 (by simpa [meanFree] using h)
  · intro a b
    obtain ⟨p, hp⟩ := hlam.2 a
    obtain ⟨q, hq⟩ := hlam.2 b
    exact ⟨p - q, by simp only [meanFree]; push_cast; linarith⟩

theorem exists_ext (hn : 1 ≤ n) (ε : Fin n → Bool) (F : Fam n) (hF : ParamS ε F) (lam : Fin n → ℝ)
    (hlam : IsParU lam) : ∃ π, ExtProp ε F lam π := by
  obtain ⟨m, hsum, -, hext⟩ := GlobalTheory.T.harish_chandra_parameter_descent n hn ε (F.H (meanFree lam)) (F.π (meanFree lam)) lam hlam
  have hμ : meanFree lam = fun a => lam a - (m : ℝ) / n := by funext a; simp [meanFree, hsum]
  have key : ∀ ν, ν = meanFree lam → IsHCS ε ν (F.π (meanFree lam)) := by
    rintro ν rfl; exact hF.1 _ (parS_meanFree hn hlam)
  obtain ⟨π, hπ1, hπ2⟩ := hext (key _ hμ.symm)
  exact ⟨π, m, hsum, hπ1, hπ2⟩

theorem famU_spec (hn : 1 ≤ n) (ε : Fin n → Bool) (F : Fam n) (hF : ParamS ε F) (lam : Fin n → ℝ)
    (hlam : IsParU lam) : ExtProp ε F lam ((famU ε F).π lam) :=
  Classical.epsilon_spec (exists_ext hn ε F hF lam hlam)

theorem classF_of_classS : ∀ (n : ℕ), 1 ≤ n → ∀ ε : Fin n → Bool, ClassS ε → ClassF ε := by
  intro n hn ε hS
  obtain ⟨F, hP, hE⟩ := hS
  refine ⟨famU ε F, fun lam hlam => ?_, ?_, ?_⟩
  · obtain ⟨-, -, -, h⟩ := famU_spec hn ε F hP lam hlam
    exact h
  · rintro lam lam' hlam ⟨w, hw, rfl⟩
    have hlam' : IsParU (lam ∘ w) := ⟨hlam.1.comp w.injective, fun a => hlam.2 (w a)⟩
    obtain ⟨m, hs, he, -⟩ := famU_spec hn ε F hP lam hlam
    obtain ⟨m', hs', he', -⟩ := famU_spec hn ε F hP _ hlam'
    have hsum : ∑ a, lam (w a) = ∑ a, lam a := Equiv.sum_comp w lam
    have hmm : m' = m := by exact_mod_cast (hs'.symm.trans ((show ∑ a, (lam ∘ w) a = ∑ a, lam a from hsum).trans hs))
    subst hmm
    refine equivOn_of_ext hn ε _ he he' ?_
    have hc : ConjK ε (meanFree lam) (meanFree (lam ∘ w)) := ⟨w, hw, by funext a; simp [meanFree, Function.comp_apply, hsum]⟩
    exact (hP.2 _ _ (parS_meanFree hn hlam) (parS_meanFree hn hlam')).2 hc
  · intro H' _ _ σ hσ
    obtain ⟨hc, hnt, hu, hirr, hsq⟩ := hσ
    obtain ⟨m, hm⟩ := GlobalTheory.CentralChar.central_char n hn ε H' σ hc hnt hu hirr
    obtain ⟨huS, hirrS, -, -⟩ := GlobalTheory.T.extension_preserves_properties n hn ε H' m σ σ hm
    have hsqS := (GlobalTheory.T.square_integrable_iff_extension n hn ε H' m σ σ hm hu).1 hsq
    obtain ⟨lam', hpar', T, hT⟩ := hE H' σ ⟨hc, hnt, huS hu, hirrS.1 hirr, hsqS⟩
    let ρ : Matrix (Fin n) (Fin n) ℂ → (F.H lam' →L[ℂ] F.H lam') := fun g =>
      (T.toContinuousLinearEquiv : H' →L[ℂ] F.H lam').comp
        ((σ g).comp (T.symm.toContinuousLinearEquiv : F.H lam' →L[ℂ] H'))
    have hρ : Ext ε m (F.π lam') ρ := by
      intro z hz g hg
      ext v
      have h1 : ρ (z • g) v = T (σ (z • g) (T.symm v)) := rfl
      rw [h1, hm z hz g hg, _root_.smul_apply, _root_.smul_apply,
        LinearIsometryEquiv.map_smul, hT g hg, LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨S, hS, -⟩ := (hP.1 lam' hpar').2.2.1
    obtain ⟨hparU, hsumU⟩ := GlobalTheory.T.lowest_type_parameter_ascent n hn ε (F.H lam') m (F.π lam') ρ hρ lam' hpar' ⟨S, hS⟩
    refine ⟨fun a => lam' a + (m : ℝ) / n, hparU, ?_⟩
    obtain ⟨m₁, hs₁, he₁, -⟩ := famU_spec hn ε F hP _ hparU
    have hm₁ : m₁ = m := by exact_mod_cast hs₁.symm.trans hsumU
    subst hm₁
    have hμ : meanFree (fun a => lam' a + (m₁ : ℝ) / n) = lam' := by
      funext a; simp only [meanFree]; rw [hsumU]; ring
    have key : ∀ ν, ν = lam' → EquivOn (SUset ε) σ (F.π ν) := by rintro ν rfl; exact ⟨T, hT⟩
    exact equivOn_of_ext hn ε _ hm he₁ (key _ hμ)

end GlobalTheory.SUtoU
end
