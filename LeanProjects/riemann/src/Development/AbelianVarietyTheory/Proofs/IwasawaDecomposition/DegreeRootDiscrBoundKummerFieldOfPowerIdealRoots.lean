import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzAdjoinRootOfUnity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzFieldRangeEmbedding
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardFilterLeLogClassNumber
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.KummerSize

open GlobalTheory.FieldSize.Capit

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (J : Ideal (𝓞 E)) (γ : 𝓞 E) (hγ : γ ≠ 0) (hJ : J ^ k = Ideal.span {γ}) (z : ℂ) (hz : z ^ k = φ (γ : E)) :
    Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  have hyF : (intMap φ F h γ : F) ≠ 0 := by
    intro h0
    have h1 : φ (γ : E) = 0 := by rw [← coe_intMap φ F h, h0]; rfl
    exact hγ (RingOfIntegers.ext ((map_eq_zero φ).1 h1))
  exact GlobalTheory.FieldSize.sz_sup_adjoin_root F a b k (intMap φ F h γ : F)
    (IsLocalization.coeSubmodule F (J.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hJ, Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]) hz

theorem sz_adjoin_roots (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) {ι : Type}
    (k : ι → ℕ) (hk : ∀ i, 0 < k i) (J : ι → Ideal (𝓞 E)) (γ : ι → 𝓞 E) (hγ : ∀ i, γ i ≠ 0)
    (hJ : ∀ i, J i ^ k i = Ideal.span {γ i}) (z : ι → ℂ) (hz : ∀ i, z i ^ k i = φ (γ i : E)) (s : Finset ι) :
    Sz (F ⊔ IntermediateField.adjoin ℚ (z '' s)) (a + ∑ i ∈ s, Real.log (k i)) (b + ∑ i ∈ s, Real.log (k i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hF
  | insert i s hi ih =>
    have h' : ∀ x, φ x ∈ F ⊔ IntermediateField.adjoin ℚ (z '' s) := fun x => (le_sup_left : F ≤ F ⊔ _) (h x)
    have hS := step φ _ _ _ ih h' (k i) (hk i) (J i) (γ i) (hγ i) (hJ i) (z i) (hz i)
    have he : F ⊔ IntermediateField.adjoin ℚ (z '' ↑(insert i s)) =
        F ⊔ IntermediateField.adjoin ℚ (z '' s) ⊔ ℚ⟮z i⟯ := by
      rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, IntermediateField.adjoin_union, sup_comm
        (IntermediateField.adjoin ℚ {z i}), sup_assoc]
    rw [he, Finset.sum_insert hi]
    refine sz_mono' hS (by linarith) (by linarith)

end GlobalTheory.FieldSize.KummerSize

namespace GlobalTheory.FieldSize.KummerSize

variable {E : Type} [Field E] [NumberField E]

open GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis in

theorem exists_decomp (b : ClassBasis E) (J : Fin b.k → (Ideal (𝓞 E))⁰)
    (hJc : ∀ i, ClassGroup.mk0 (J i) = ClassGroup.mk E (b.c i)) (γ : Fin b.k → 𝓞 E) (hγ0 : ∀ i, γ i ≠ 0)
    (hγ : ∀ i, (J i : Ideal (𝓞 E)) ^ b.h i = Ideal.span {γ i}) {h : ℕ} (hh : 0 < h) {y : E}
    (hy : y ∈ powIdealElts E h) :
    ∃ (u : (𝓞 E)ˣ) (t : Eˣ) (a m : Fin b.k → ℤ), (∀ i, (h : ℤ) * a i = b.h i * m i) ∧
      y = (u : E) * (t : E) ^ h * ∏ i, (γ i : E) ^ m i := by
  obtain ⟨hy0, 𝔞, h𝔞⟩ := hy
  have h𝔞0 : 𝔞 ≠ 0 := by
    rintro rfl
    rw [zero_pow hh.ne'] at h𝔞
    exact hy0 (FractionalIdeal.spanSingleton_eq_zero_iff.1 h𝔞)
  set U := Units.mk0 𝔞 h𝔞0 with hU
  set Y := Units.mk0 y hy0 with hY
  have hUY : U ^ h = toPrincipalIdeal (𝓞 E) E Y := by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val, hU, Units.val_mk0, hY, Units.val_mk0, h𝔞]
  have hγE : ∀ i, (γ i : E) ≠ 0 := fun i h0 => hγ0 i (RingOfIntegers.ext h0)
  let G : Fin b.k → Eˣ := fun i => Units.mk0 (γ i : E) (hγE i)
  let P : Fin b.k → (FractionalIdeal (𝓞 E)⁰ E)ˣ := fun i => FractionalIdeal.mk0 E (J i)
  have hP : ∀ i, ClassGroup.mk E (P i) = ClassGroup.mk E (b.c i) := fun i => by
    rw [ClassGroup.mk_mk0, hJc]
  have hPG : ∀ i, P i ^ b.h i = toPrincipalIdeal (𝓞 E) E (G i) := fun i => by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val, FractionalIdeal.coe_mk0, ← FractionalIdeal.coeIdeal_pow,
      hγ i, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  obtain ⟨a, ha⟩ := b.span (ClassGroup.mk E U)
  have hx1 : ClassGroup.mk E U ^ h = 1 := by
    rw [← map_pow, hUY, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  have hm : ∀ i, ∃ m : ℤ, (h : ℤ) * a i = b.h i * m := by
    have h1 := b.indep (fun i => (h : ℤ) * a i) (by
      simp only [zpow_mul', zpow_natCast]
      rw [Finset.prod_pow, ← ha, hx1])
    intro i
    exact orderOf_dvd_iff_zpow_eq_one.2 (h1 i)
  choose m hm using hm
  have h2 : ClassGroup.mk E (U * (∏ i, P i ^ a i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_prod, ha]
    simp only [map_zpow, hP, mul_inv_cancel]
  obtain ⟨t, ht⟩ := exists_gen h2
  have hU' : U = toPrincipalIdeal (𝓞 E) E t * ∏ i, P i ^ a i := by
    rw [← ht, inv_mul_cancel_right]
  have h3 : toPrincipalIdeal (𝓞 E) E (t ^ h * ∏ i, G i ^ m i) = toPrincipalIdeal (𝓞 E) E Y := by
    rw [← hUY, hU', mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, ← hPG, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← hm i, mul_comm]
  rw [toPrincipalIdeal_eq_iff, coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_eq_spanSingleton] at h3
  obtain ⟨u, hu⟩ := h3
  refine ⟨u, t, a, m, hm, ?_⟩
  show (Y : E) = _
  rw [← hu, Units.smul_def, Algebra.smul_def]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, G, Units.val_mk0]
  ring

end GlobalTheory.FieldSize.KummerSize

namespace GlobalTheory.FieldSize

open GlobalTheory.FieldSize.KummerSize GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis

theorem sz_kummerField : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), 0 < h →
    Sz (kummerField φ h) (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h +
      Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E +
      ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) := by
  intro E _ _ φ h hh
  classical

  let b : ClassBasis E := Classical.arbitrary _
  choose J hJ using fun i => ClassGroup.mk0_surjective (ClassGroup.mk E (b.c i))
  have hprin : ∀ i, ((J i : Ideal (𝓞 E)) ^ b.h i).IsPrincipal := fun i => by
    have hmem : (J i : Ideal (𝓞 E)) ^ b.h i ∈ (Ideal (𝓞 E))⁰ := pow_mem (J i).2 _
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have : (⟨_, hmem⟩ : (Ideal (𝓞 E))⁰) = J i ^ b.h i := rfl
    rw [this, map_pow, hJ]
    exact pow_orderOf_eq_one _
  choose γ hγ using fun i => (hprin i).principal
  have hγ' : ∀ i, (J i : Ideal (𝓞 E)) ^ b.h i = Ideal.span {γ i} := fun i => by
    rw [hγ i, Ideal.submodule_span_eq]
  have hγ0 : ∀ i, γ i ≠ 0 := fun i h0 => by
    have h1 := hγ' i
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at h1
    exact nonZeroDivisors.coe_ne_zero (J i ^ b.h i) h1

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion E)
  let uγ : Option (Fin (NumberField.Units.rank E)) → (𝓞 E)ˣ :=
    fun o => o.elim (g : (𝓞 E)ˣ) (NumberField.Units.fundSystem E)
  have huJ : ∀ o, (⊤ : Ideal (𝓞 E)) ^ h = Ideal.span {((uγ o : (𝓞 E)ˣ) : 𝓞 E)} := fun o => by
    rw [Ideal.top_pow, eq_comm, Ideal.span_singleton_eq_top]
    exact (uγ o).isUnit
  have hu0 : ∀ o, ((uγ o : (𝓞 E)ˣ) : 𝓞 E) ≠ 0 := fun o => (uγ o).ne_zero

  choose ρ hρ using fun o => IsAlgClosed.exists_pow_nat_eq (φ (((uγ o : (𝓞 E)ˣ) : 𝓞 E) : E)) hh
  choose β hβ using fun i => IsAlgClosed.exists_pow_nat_eq (φ ((γ i : 𝓞 E) : E)) (b.h_pos i)

  have hF1 : Sz (imField φ ⊔ cycField h) (Real.log (Module.finrank ℚ E) + Real.log h)
      (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log h) :=
    sz_sup _ _ _ _ _ _ (sz_fieldRange_embedding E φ) (sz_adjoin_rootOfUnity h hh)
  have hφ1 : ∀ x, φ x ∈ imField φ ⊔ cycField h := fun x => (le_sup_left : imField φ ≤ _) ⟨x, rfl⟩
  have hF2 := sz_adjoin_roots φ _ _ _ hF1 hφ1 (fun _ => h) (fun _ => hh) (fun _ => ⊤)
    (fun o => ((uγ o : (𝓞 E)ˣ) : 𝓞 E)) hu0 huJ ρ hρ Finset.univ
  set F2 := imField φ ⊔ cycField h ⊔ IntermediateField.adjoin ℚ (ρ '' ↑(Finset.univ : Finset (Option (Fin (NumberField.Units.rank E))))) with hF2def
  have hφ2 : ∀ x, φ x ∈ F2 := fun x => (le_sup_left : _ ≤ F2) (hφ1 x)
  have hF3 := sz_adjoin_roots φ _ _ _ hF2 hφ2 b.h b.h_pos (fun i => (J i : Ideal (𝓞 E))) γ hγ0 hγ' β hβ Finset.univ
  set F3 := F2 ⊔ IntermediateField.adjoin ℚ (β '' ↑(Finset.univ : Finset (Fin b.k))) with hF3def
  have hsum1 : ∑ _o ∈ (Finset.univ : Finset (Option (Fin (NumberField.Units.rank E)))), Real.log (h : ℕ) =
      (NumberField.Units.rank E + 1) * Real.log h := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_option]
  have hsum2 : ∑ i ∈ (Finset.univ : Finset (Fin b.k)), Real.log (b.h i) ≤ Real.log (classNumber E) := by
    have h1 : ∏ i, b.h i ≤ classNumber E := prod_orderOf_le_card_of_indep _ b.indep
    rw [← Real.log_prod (fun i _ => by exact_mod_cast (b.h_pos i).ne')]
    refine Real.log_le_log (Finset.prod_pos fun i _ => by exact_mod_cast b.h_pos i) ?_
    exact_mod_cast h1
  have hF3' := (sz_mono_and_of_le.1 F3 _ _ _ _ hF3 (by rw [hsum1] at *; linarith) (by rw [hsum1] at *; linarith) :
    Sz F3 (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h +
      Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E +
      ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))))
  refine sz_mono_and_of_le.2 _ _ _ _ ?_ hF3'

  have h23 : F2 ≤ F3 := le_sup_left
  have h13 : imField φ ⊔ cycField h ≤ F3 := le_sup_left.trans h23
  have hρF : ∀ o, ρ o ∈ F3 := fun o => h23 ((le_sup_right : _ ≤ F2)
    (IntermediateField.subset_adjoin ℚ _ ⟨o, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩))
  have hβF : ∀ i, β i ∈ F3 := fun i => (le_sup_right : _ ≤ F3)
    (IntermediateField.subset_adjoin ℚ _ ⟨i, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
  refine (kummerField_le_iff φ).2 ⟨fun x => h13 (hφ1 x), h13 ((le_sup_right : cycField h ≤ _)
    (IntermediateField.mem_adjoin_simple_self ℚ _)), fun y hy z hz => ?_⟩
  have hy0 : y ≠ 0 := hy.1
  obtain ⟨u, t, a, m, hm, rfl⟩ := exists_decomp b J hJ γ hγ0 hγ' hh hy
  obtain ⟨⟨ζ, e⟩, hζe, -⟩ := NumberField.Units.exist_unique_eq_mul_prod E u
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 (hg ζ)
  let Φ : (𝓞 E)ˣ →* ℂˣ := Units.map ((φ.comp (algebraMap (𝓞 E) E)) : 𝓞 E →* ℂ)
  have hΦ : ∀ v : (𝓞 E)ˣ, ((Φ v : ℂˣ) : ℂ) = φ ((v : 𝓞 E) : E) := fun v => rfl
  set w : ℂ := ρ none ^ c * (∏ j, ρ (some j) ^ e j) * φ (t : E) * ∏ i, β i ^ a i with hw
  have hwF : w ∈ F3 := mul_mem (mul_mem (mul_mem (zpow_mem (hρF none) _)
    (prod_mem fun j _ => zpow_mem (hρF (some j)) _)) (h13 (hφ1 _))) (prod_mem fun i _ => zpow_mem (hβF i) _)
  have hA : ∀ o (k : ℤ), (ρ o ^ k) ^ h = ((Φ (uγ o) ^ k : ℂˣ) : ℂ) := fun o k => by
    rw [Units.val_zpow_eq_zpow_val, hΦ, ← hρ o, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hB : ∀ i, (β i ^ a i) ^ h = φ ((γ i : 𝓞 E) : E) ^ m i := fun i => by
    rw [← hβ i, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (a i), hm i]
  have hu : φ ((u : 𝓞 E) : E) = ((Φ (uγ none) ^ c : ℂˣ) : ℂ) * ∏ j, ((Φ (uγ (some j)) ^ e j : ℂˣ) : ℂ) := by
    rw [← hΦ, hζe, ← hc, map_mul, Units.val_mul, map_prod, Units.coe_prod]
    congr 1
    · rw [Subgroup.coe_zpow, map_zpow]; rfl
    · exact Finset.prod_congr rfl fun j _ => by rw [map_zpow]; rfl
  have hwh : w ^ h = φ ((u : E) * (t : E) ^ h * ∏ i, ((γ i : 𝓞 E) : E) ^ m i) := by
    rw [hw, mul_pow, mul_pow, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, hA]
    simp only [hA, hB]
    rw [map_mul, map_mul, map_pow, map_prod, hu]
    simp only [map_zpow₀]
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne', eq_comm, map_eq_zero] at hwh
    exact hy0 hwh
  have hzw : z / w ∈ cycField h := mem_cycField hh.ne' (by rw [div_pow, hz, ← hwh, div_self (pow_ne_zero _ hw0)])
  have := mul_mem (h13 ((le_sup_right : cycField h ≤ _) hzw)) hwF
  rwa [div_mul_cancel₀ _ hw0] at this

end GlobalTheory.FieldSize

end
