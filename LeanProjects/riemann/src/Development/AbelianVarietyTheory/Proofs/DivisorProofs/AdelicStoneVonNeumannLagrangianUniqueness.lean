import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalFStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dot_smul_rat {κ : Type} [Fintype κ] (s t : AF F) (u v : (κ → F) × (κ → F)) :
    (s • ((fun i => algebraMap F (AF F) (u.1 i)), (fun i => algebraMap F (AF F) (u.2 i)))).1 ⬝ᵥ
      (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))).2 =
      s * t * algebraMap F (AF F) (u.1 ⬝ᵥ v.2) := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [show (fun i => algebraMap F (AF F) (u.1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (v.2 i)) =
    algebraMap F (AF F) (u.1 ⬝ᵥ v.2) from (RingHom.map_dotProduct (algebraMap F (AF F)) u.1 v.2).symm]
  ring

theorem inv_sum (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))) (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ)
    {ι : Type} (s : Finset ι) (t : ι → AF F) (w : ι → (κ → F) × (κ → F)) (hw : ∀ j, w j ∈ L) :
    ∀ φ ∈ schA F κ, l (schr ψ (∑ j ∈ s, t j • ((fun i => algebraMap F (AF F) ((w j).1 i)),
      (fun i => algebraMap F (AF F) ((w j).2 i)))) φ) = l φ := by
  classical
  induction s using Finset.induction_on with
  | empty => intro φ _; simp only [Finset.sum_empty]; congr 1; funext x; simp [schr]
  | insert j s hj ih =>
    intro φ hφ
    set a := t j • ((fun i => algebraMap F (AF F) ((w j).1 i)), (fun i => algebraMap F (AF F) ((w j).2 i)))
    set b := ∑ k ∈ s, t k • ((fun i => algebraMap F (AF F) ((w k).1 i)), (fun i => algebraMap F (AF F) ((w k).2 i)))
    have hab : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0 := by
      simp only [a, b, Prod.fst_sum, Prod.snd_sum, dotProduct_sum, sum_dotProduct, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [dot_smul_rat, dot_smul_rat, hL _ (hw j) _ (hw k)]
      ring
    have e := GlobalTheory.ThetaQuasiRat.schr_schr ψ a b φ
    rw [hab, mul_zero, AddChar.map_zero_eq_one, one_smul] at e
    rw [Finset.sum_insert hj, ← e, hl _ _ (hw j) _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ b φ hφ), ih φ hφ]

end GlobalTheory.AdelicSvN

namespace GlobalTheory.AdelicSvN
variable {F : Type} [Field F] [NumberField F]

theorem realised_of_mem_closure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ Submonoid.closure (gens F κ)) : Realised ψ g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | rfl
    · exact GlobalTheory.T.isRealisedOnAdelicSchwartz_levi_inverseTranspose F ψ κ A hA
    · exact GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz F ψ hψ κ C hC
    · exact GlobalTheory.T.isRealisedOnAdelicSchwartz_weyl_fourier F ψ hψ κ
  | one => exact realised_one ψ
  | mul g h _ _ hg hh => exact hg.mul hh

theorem act_zero_eq_sum {κ : Type} [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (y : κ → AF F) :
    act g (0, y) = ∑ j, y j • ((fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inl) i)),
      (fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inr) i))) := by
  have key : ∀ k, (g.map (algebraMap F (AF F)) *ᵥ Sum.elim 0 y) k =
      ∑ j, y j * algebraMap F (AF F) ((g *ᵥ Sum.elim 0 (Pi.single j 1)) k) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun m _ hm => by simp [Pi.single_apply, hm]) (by simp)]
    simp [mul_comm]
  ext i
  · simp only [act, Function.comp_apply, key, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  · simp only [act, Function.comp_apply, key, Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ →
    ∀ l₁ ∈ (adeleClass F).adm κ, ∀ l₂ ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  intro F _ _ ψ hψ κ _ L hL hdim l₁ hl₁ l₂ hl₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩
  classical
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := realised_of_mem_closure ψ hψ hg
  have key : ∀ l ∈ (adeleClass F).adm κ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    intro l hl hi
    obtain ⟨l', hl', e⟩ := hSa l hl
    obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ l' hl' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]
      exact inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  obtain ⟨c₁, h₁⟩ := key l₁ hl₁ hi₁
  obtain ⟨c₂, h₂⟩ := key l₂ hl₂ hi₂
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hSs φ₀ hφ₀
  have hc₂ : c₂ ≠ 0 := fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  rw [h₁ φ' hφ', h₂ φ' hφ']
  field_simp
end GlobalTheory.AdelicSvN
