import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetCharEqOneOfHasWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.Published.HeckeFEModel

section
variable {E : Type} [Field E] [NumberField E]

theorem exists_exponents (χ : HChar E) : ∃ a : HeightOneSpectrum (𝓞 E) →₀ ℕ, ∀ v, ExpAt χ v (a v) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ
  have hE : ∀ v, ExpAt χ v (Nat.find (h2 v)) := fun v m => by
    refine ⟨fun h => Nat.find_min' _ h, fun h x hx hx' => Nat.find_spec (h2 v) x hx (hx'.trans ?_)⟩
    rw [WithZero.exp_le_exp]
    omega
  refine ⟨Finsupp.ofSupportFinite (fun v => Nat.find (h2 v)) (h1.subset fun v hv hu => hv ?_), fun v => hE v⟩
  exact (hE v).unique ((expAt_zero_iff χ v).2 hu)

theorem hasInf_inv {I : Type} [Fintype I] {φ : I → E →+* ℂ} {χ : HChar E} {n : I → ℤ}
    (h : Formalism.L2.Host.HChar.HasInf χ φ n) : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -n i) := fun k => by
  rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp only [zpow_neg]

theorem isUnitary_inv {χ : HChar E} (h : IsUnitary χ) : IsUnitary χ⁻¹ := fun x => by
  show ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]

theorem isCMType_embedding : IsCMType (fun w : InfinitePlace E => w.embedding) := fun σ => by
  refine ⟨InfinitePlace.mk σ, ?_, ?_⟩
  · rcases InfinitePlace.embedding_mk_eq σ with h | h
    · exact Or.inl h.symm
    · right
      show σ = ComplexEmbedding.conjugate (InfinitePlace.mk σ).embedding
      rw [h]; ext x; simp
  · rintro w (h | h)
    · rw [h]; exact (InfinitePlace.mk_embedding w).symm
    · rw [h, InfinitePlace.mk_conjugate_eq]; exact (InfinitePlace.mk_embedding w).symm

theorem zero_iff (h : HeckeFunctionalEquationAbs) [IsTotallyComplex E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} {Λ Λ' : ℂ → ℂ} (hu : IsUnitary χ)
    (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0) (h1 : IsCompletedL χ n Λ)
    (h2 : IsCompletedL χ⁻¹ (fun i => -n i) Λ') (s : ℂ) : Λ s = 0 ↔ Λ' (1 - s) = 0 := by
  obtain ⟨a, ha⟩ := exists_exponents χ
  obtain ⟨ε, hε, hs⟩ := h E I φ hφ χ n a Λ Λ' hu hi hn ha h1 h2
  have h0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hA : ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ)) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    refine mul_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero E)) ?_
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  rw [hs s, mul_eq_zero, mul_eq_zero, Complex.cpow_eq_zero_iff]
  tauto

end

section
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.DefU.NonTriv

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem exists_unitary : ∃ χ : HChar E, χ.IsUnitary ∧
    χ.HasInf (fun w : InfinitePlace E => w.embedding) (fun _ => expT E) := by
  classical
  have hbij : Function.Bijective fun w : InfinitePlace E => InfinitePlace.mk w.embedding := by
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨ψ, hψ, hψu, hψi, -, -, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar E (InfinitePlace E) (fun w => w.embedding)
    hbij (fun _ => expT E) ∅ (fun _ => 1) (by simp)
  have hinf := (GlobalTheory.InfTypeLocal.infType_iff_local E (InfinitePlace E) (fun w => w.embedding) hbij ψ hψ _).2 hψi
  have hmem : ∀ k : Eˣ, infDiag k ∈ unitIdl E := fun k => by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply]
    exact Subgroup.prod_mem _ fun w _ => GlobalTheory.Mem.Chr.AntiExist.inf_mem w _
  obtain ⟨χ, hχ, hχ1, hχU, hχd⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles E) Eˣ (unitIdl E)
    GlobalTheory.Mem.UnitOpen.isOpen_unitIdl (diagUnits E) 1 ψ hψ hψu (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu⟩ := exists_unit k hk
      show (1 : ℂˣ) = ψ (diagUnits E k)
      rw [hψd, Finset.prod_empty, mul_one]
      refine (Units.ext ?_).symm
      rw [hinf k, Units.val_one]
      refine Finset.prod_eq_one fun w _ => ?_
      rw [← hu]
      exact phase_pow_eq_one u w.embedding)
  refine ⟨⟨χ, hχ, fun k => by rw [hχd]; rfl⟩, hχ1, fun k => ?_⟩
  show ((χ (infDiag k) : ℂˣ) : ℂ) = _
  rw [hχU _ (hmem k)]
  exact hinf k

end

theorem hypotheses_inhabited (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ (χ : HChar E) (n : InfinitePlace E → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ),
      IsCMType (fun w : InfinitePlace E => w.embedding) ∧ IsUnitary χ ∧
      Formalism.L2.Host.HChar.HasInf χ (fun w : InfinitePlace E => w.embedding) n ∧ (∃ i, n i ≠ 0) ∧ (∀ v, ExpAt χ v (a v)) ∧
      (CompletedLBoundedInStrips → ∃ Λ Λ' : ℂ → ℂ, IsCompletedL χ n Λ ∧ IsCompletedL χ⁻¹ (fun i => -n i) Λ') := by
  obtain ⟨χ, hu, hi⟩ := exists_unitary E
  obtain ⟨a, ha⟩ := exists_exponents χ
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  refine ⟨χ, _, a, isCMType_embedding, hu, hi, ⟨w, GlobalTheory.DefU.NonTriv.expT_ne_zero⟩, ha, fun h => ?_⟩
  obtain ⟨Λ, h1, -⟩ := h E _ _ isCMType_embedding χ _ hu hi ⟨w, GlobalTheory.DefU.NonTriv.expT_ne_zero⟩
  obtain ⟨Λ', h2, -⟩ := h E _ _ isCMType_embedding χ⁻¹ _ (isUnitary_inv hu) (hasInf_inv hi)
    ⟨w, neg_ne_zero.2 GlobalTheory.DefU.NonTriv.expT_ne_zero⟩
  exact ⟨Λ, Λ', h1, h2⟩

example : IsCMField (CyclotomicField 4 ℚ) :=
  IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) (S := {4}) ⟨4, rfl, by norm_num⟩

example (E : Type) [Field E] [NumberField E] (φ : Empty → E →+* ℂ) : ¬ IsCMType φ := fun h => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  obtain ⟨i, -⟩ := h w.embedding
  exact i.elim

end GlobalTheory.Published.HeckeFEModel

end
