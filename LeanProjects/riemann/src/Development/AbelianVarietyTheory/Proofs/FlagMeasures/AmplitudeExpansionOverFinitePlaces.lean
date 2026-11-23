import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodOfHpEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodEqProdMulFinprodIte
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DefectPhase

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ} (G : GFrames A r k)

theorem amp_eq_finsum (d : G.Dat) (hT : {o : Quot G.LRel | G.IsTerm d o.out}.Finite) (Q : G.Lt → Prop) :
    G.amp d Q = ∑ o ∈ hT.toFinset, if Q o.out then (G.mu o.out : ℂ) * G.om d o.out else 0 := by
  unfold GFrames.amp
  rw [tsum_eq_sum (s := hT.toFinset)]
  · refine Finset.sum_congr rfl fun o ho => ?_
    have : G.IsTerm d o.out := hT.mem_toFinset.1 ho
    simp only [this, true_and]
  · intro o ho
    have : ¬ G.IsTerm d o.out := fun h => ho (hT.mem_toFinset.2 h)
    simp only [this, false_and, if_false]

theorem finprod_split' {ι : Type} (S1 : Finset ι) (f g : ι → ℂ) (hf : (Function.mulSupport f).Finite)
    (hfg : ∀ p ∉ S1, f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S1, f p) * ∏ᶠ p, (if p ∈ S1 then 1 else g p) := by
  first
  | exact @_root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite
  | exact _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite
  | (apply _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite ..)

theorem norm_finprod_eq_one {ι : Type} (g : ι → ℂ) (hg : (Function.mulSupport g).Finite)
    (h1 : ∀ p, ‖g p‖ = 1) : ‖∏ᶠ p, g p‖ = 1 := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hg.toFinset) g (fun p hp => hg.mem_toFinset.2 hp), norm_prod]
  exact Finset.prod_eq_one fun p _ => h1 p

def cond (d : G.Dat) (B : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F)) :
    Submodule (A.L p).O (G.S p).V → Prop :=
  if p ∈ B then fun Λ => ¬ (G.S p).BBzero (d p) Λ else (G.S p).BBzero (d p)

theorem amp_cond (d : G.Dat) (B : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F)) :
    (G.S p).amp (d p) (cond G d B p) = if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ)
      else (G.S p).amp (d p) ((G.S p).BBzero (d p)) := by
  unfold cond
  split_ifs <;> rfl

theorem cond_pos (d : G.Dat) {B : Finset (HeightOneSpectrum (𝓞 F))} {p : HeightOneSpectrum (𝓞 F)} (h : p ∈ B)
    (Λ : Submodule (A.L p).O (G.S p).V) : cond G d B p Λ ↔ ¬ (G.S p).BBzero (d p) Λ := by
  unfold cond
  rw [if_pos h]

theorem cond_neg (d : G.Dat) {B : Finset (HeightOneSpectrum (𝓞 F))} {p : HeightOneSpectrum (𝓞 F)} (h : p ∉ B)
    (Λ : Submodule (A.L p).O (G.S p).V) : cond G d B p Λ ↔ (G.S p).BBzero (d p) Λ := by
  unfold cond
  rw [if_neg h]

end GlobalTheory.HL.DefectPhase

namespace GlobalTheory.HL.DefectPhase

theorem amp_sum_defect_sets : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  intro F E _ _ _ _ _ sig A r k G hk d hex S1 hS1
  obtain ⟨Λ₀, hΛ₀⟩ := hex
  obtain ⟨-, -, -, -, hgood⟩ := GlobalTheory.HL.BadPlaces.bad_places A r k G hk d Λ₀ hΛ₀
  have hinv : ∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ →
      ((G.S p).BBzero (d p) (h • Λ) ↔ (G.S p).BBzero (d p) Λ) := by
    intro p h hh Λ hΛ
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms _ r k (G.S p) (d p) Λ hΛ h hh).2.2.2.2.2.2.2.1
  have hBB : ∀ p ∉ (S1 : Set _), ∀ Λ, (G.S p).IsTerm (d p) Λ → (G.S p).BBzero (d p) Λ :=
    fun p hp Λ hΛ => (hgood p fun h => hp (hS1 h)).1 _ _ hΛ
  have hprod : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) = ∏ᶠ p, (G.S p).amp (d p) (cond G d B p) ∧
      {p | (G.S p).amp (d p) (cond G d B p) ≠ 1 ∨ (G.S p).mass (d p) (cond G d B p) ≠ 1}.Finite ∧
      {o : Quot G.LRel | G.IsTerm d o.out}.Finite := by
    intro B hB
    have hI : ∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ → cond G d B p Λ →
        cond G d B p (h • Λ) := by
      intro p h hh Λ hΛ hP
      by_cases hp : p ∈ B
      · rw [cond_pos G d hp] at hP ⊢
        rwa [hinv p h hh Λ hΛ]
      · rw [cond_neg G d hp] at hP ⊢
        rwa [hinv p h hh Λ hΛ]
    have hF : {p | ∃ Λ, (G.S p).IsTerm (d p) Λ ∧ ¬ cond G d B p Λ}.Finite := by
      refine S1.finite_toSet.subset fun p ⟨Λ, hΛ, hP⟩ => ?_
      by_contra hp
      have hpB : p ∉ B := fun h => hp (hB h)
      rw [cond_neg G d hpB] at hP
      exact hP (hBB p hp Λ hΛ)
    obtain ⟨a1, -, a3, a4⟩ := GlobalTheory.T.hermitian_amplitude_mass_product_structure A r k G hk d ⟨Λ₀, hΛ₀⟩ (cond G d B) hI hF
    exact ⟨a1, a3, a4⟩
  have hT := (hprod ∅ (Finset.empty_subset _)).2.2
  set g : HeightOneSpectrum (𝓞 F) → ℂ := fun p => (G.S p).amp (d p) ((G.S p).BBzero (d p)) with hg
  set c : ℂ := ∏ᶠ p, (if p ∈ S1 then 1 else g p) with hc
  have hsupp : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      (Function.mulSupport fun p => (G.S p).amp (d p) (cond G d B p)).Finite := fun B hB =>
    (hprod B hB).2.1.subset fun p hp => Or.inl hp
  have hsplit : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) =
        c * ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ)
          else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
    intro B hB
    rw [(hprod B hB).1, finprod_split' S1 _ g (hsupp B hB), mul_comm]
    · rw [Finset.prod_congr rfl fun p _ => amp_cond G d B p]
    · intro p hp
      have hpB : p ∉ B := fun h => hp (hB h)
      rw [amp_cond, if_neg hpB]
  have hc1 : ‖c‖ = 1 := by
    refine norm_finprod_eq_one _ ?_ fun p => ?_
    · refine (hsupp ∅ (Finset.empty_subset _)).subset fun p hp => ?_
      by_cases h : p ∈ S1
      · exact absurd (if_pos h) hp
      · change (G.S p).amp (d p) (cond G d ∅ p) ≠ 1
        rw [amp_cond, if_neg (Finset.notMem_empty p)]
        simpa [h] using hp
    · by_cases h : p ∈ S1
      · simp [h]
      · simp only [h, if_false, hg]
        exact ((hgood p fun hp => h (hS1 hp)).2 (d p) ⟨A.lat p Λ₀, hΛ₀.2 p⟩).1
  refine ⟨c, hc1, fun Q => ?_⟩
  have hsum : G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty),
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) := by
    rw [amp_eq_finsum G d hT]
    simp only [amp_eq_finsum G d hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o ho => ?_
    have hto : ∀ p, (G.S p).IsTerm (d p) (A.lat p o.out) := (hT.mem_toFinset.1 ho).2
    have hS : ∀ p, ¬ (G.S p).BBzero (d p) (A.lat p o.out) → p ∈ S1 := fun p hn => by
      by_contra hp
      exact hn (hBB p hp _ (hto p))
    set B₀ := S1.filter fun p => ¬ (G.S p).BBzero (d p) (A.lat p o.out) with hB₀
    have hgen : (¬ G.Gen d o.out) = B₀.Nonempty := by
      apply propext
      constructor
      · intro h
        obtain ⟨p, hp⟩ := not_forall.1 h
        exact ⟨p, Finset.mem_filter.2 ⟨hS p hp, hp⟩⟩
      · rintro ⟨p, hp⟩ h
        exact (Finset.mem_filter.1 hp).2 (h p)
    have heq : ∀ B ∈ S1.powerset.filter (fun B => Q B.Nonempty),
        (if ∀ p, cond G d B p (A.lat p o.out) then (G.mu o.out : ℂ) * G.om d o.out else 0) =
          if B₀ = B then (G.mu o.out : ℂ) * G.om d o.out else 0 := by
      intro B hB
      have hBS : B ⊆ S1 := Finset.mem_powerset.1 (Finset.mem_filter.1 hB).1
      have hiff : (∀ p, cond G d B p (A.lat p o.out)) ↔ B₀ = B := by
        constructor
        · intro hQ
          ext p
          constructor
          · intro hp
            by_contra hpB
            exact (Finset.mem_filter.1 hp).2 ((cond_neg G d hpB _).1 (hQ p))
          · intro hp
            exact Finset.mem_filter.2 ⟨hBS hp, (cond_pos G d hp _).1 (hQ p)⟩
        · rintro rfl p
          by_cases hp : p ∈ B₀
          · exact (cond_pos G d hp _).2 (Finset.mem_filter.1 hp).2
          · refine (cond_neg G d hp _).2 ?_
            by_contra hn
            exact hp (Finset.mem_filter.2 ⟨hS p hn, hn⟩)
      simp only [hiff]
    rw [Finset.sum_congr rfl heq, Finset.sum_ite_eq, hgen]
    have hmem : B₀ ∈ S1.powerset.filter (fun B => Q B.Nonempty) ↔ Q B₀.Nonempty := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨Finset.filter_subset _ _, h⟩⟩
    by_cases hq : Q B₀.Nonempty
    · rw [if_pos hq, if_pos (hmem.2 hq)]
    · rw [if_neg hq, if_neg (fun h => hq (hmem.1 h))]
  rw [hsum, Finset.sum_congr rfl fun B hB => hsplit B (Finset.mem_powerset.1 (Finset.mem_filter.1 hB).1),
    ← Finset.mul_sum]

end GlobalTheory.HL.DefectPhase
