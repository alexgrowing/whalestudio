import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.TwOrbUnimod

open GlobalTheory.TwOrbLat

section Mat

variable {L : Type} [Field L] {a : ℕ}

theorem mem_GLint_iff' {S : Subring L} {x : GL (Fin a) L} :
    x ∈ GLint (Fin a) S ↔ (∀ i j, x.1 i j ∈ S) ∧ ∀ i j, (x⁻¹).1 i j ∈ S := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective S.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective S.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem mulVec_mem {S : Subring L} {M : Matrix (Fin a) (Fin a) L} {v : Fin a → L}
    (hM : ∀ i j, M i j ∈ S) (hv : ∀ j, v j ∈ S) (i : Fin a) : (M *ᵥ v) i ∈ S := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => S.mul_mem (hM i j) (hv j)

theorem single_mem (S : Subring L) (j k : Fin a) : (Pi.single j (1 : L) : Fin a → L) k ∈ S := by
  by_cases hk : k = j
  · subst hk; simp [S.one_mem]
  · simp [Pi.single_eq_of_ne hk, S.zero_mem]

theorem mem_GLint_iff_dual {S : Subring L} (c : L →+* L) (hc : ∀ x, c (c x) = x) (hS : ∀ x, c x ∈ S ↔ x ∈ S)
    (Y : GL (Fin a) L) :
    Y ∈ GLint (Fin a) S ↔ ∀ u : Fin a → L, (∀ j, u j ∈ S) ↔ ∀ i, (Y.1 *ᵥ (c ∘ u)) i ∈ S := by
  rw [mem_GLint_iff']
  constructor
  · rintro ⟨h1, h2⟩ u
    constructor
    · intro hu i
      exact mulVec_mem h1 (fun j => (hS _).2 (hu j)) i
    · intro hY j
      have e1 : (c ∘ u) = (Y⁻¹).1 *ᵥ (Y.1 *ᵥ (c ∘ u)) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have h := mulVec_mem h2 hY j
      rw [← e1] at h
      exact (hS _).1 h
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have hcu : c ∘ (Pi.single j (1 : L) : Fin a → L) = Pi.single j 1 := by
        funext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
      have h3 := (h _).1 (single_mem S j) i
      rw [hcu, Matrix.mulVec_single_one] at h3
      simpa [Matrix.col] using h3
    · have hY : Y.1 *ᵥ ((Y⁻¹).1 *ᵥ Pi.single j 1) = Pi.single j 1 := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hcc : c ∘ (c ∘ ((Y⁻¹).1 *ᵥ Pi.single j 1)) = (Y⁻¹).1 *ᵥ Pi.single j 1 := funext fun k => hc _
      have h2 := (h (c ∘ ((Y⁻¹).1 *ᵥ Pi.single j 1))).2 (by rw [hcc, hY]; exact single_mem S j) i
      have h4 := (hS _).1 h2
      rw [Matrix.mulVec_single_one] at h4
      simpa [Matrix.col] using h4

theorem invT_mem_iff {S : Subring L} (x : GL (Fin a) L) :
    invT a L x ∈ GLint (Fin a) S ↔ x ∈ GLint (Fin a) S := by
  rw [mem_GLint_iff', mem_GLint_iff']
  have h1 : (invT a L x).1 = (x⁻¹).1ᵀ := rfl
  have h2 : ((invT a L x)⁻¹).1 = x.1ᵀ := rfl
  rw [h1, h2]
  simp only [Matrix.transpose_apply]
  exact ⟨fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩, fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩⟩

theorem PhiU_mem (S : Subring L) : PhiU a L ∈ GLint (Fin a) S := by
  rw [mem_GLint_iff']
  have h2 : ((PhiU a L)⁻¹).1 = (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  have h1 : (PhiU a L).1 = GlobalTheory.Tw.Phi a L := rfl
  rw [h1, h2]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
  · simp only [Matrix.transpose_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
    split_ifs
    · exact S.pow_mem (S.neg_mem S.one_mem) _
    · exact S.zero_mem

end Mat

end GlobalTheory.TwOrbUnimod

noncomputable section
namespace GlobalTheory.TwOrbUnimod
open GlobalTheory.TwOrbLat

section Herm

variable {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (β : B.A) {a : ℕ}

theorem herm_add_left (y y' z : B.A) : B.herm β (y + y') z = B.herm β y z + B.herm β y' z := by
  simp [GlobalTheory.UnitLemma.InvAlg.herm, mul_add, add_mul, map_add]

theorem herm_zero_left (z : B.A) : B.herm β 0 z = 0 := by
  simp [GlobalTheory.UnitLemma.InvAlg.herm]

theorem herm_smul_left (t : K.E) (y z : B.A) : B.herm β (t • y) z = t * B.herm β y z := by
  simp only [GlobalTheory.UnitLemma.InvAlg.herm]
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]

theorem herm_smul_right (t : K.E) (y z : B.A) : B.herm β y (t • z) = K.c t * B.herm β y z := by
  simp only [GlobalTheory.UnitLemma.InvAlg.herm]
  rw [Algebra.smul_def, (B.σ).map_mul, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem herm_sum_left (f : Fin a → B.A) (z : B.A) : B.herm β (∑ i, f i) z = ∑ i, B.herm β (f i) z := by
  simp [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (y : B.A) (f : Fin a → B.A) : B.herm β y (∑ i, f i) = ∑ i, B.herm β y (f i) := by
  simp [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum]

end Herm

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem herm_crd (c : w.adicCompletion E →+* w.adicCompletion E) (hc : ∀ x, e (K.c x) = c (e x)) (β : B.A)
    (y z : B.A) :
    e (B.herm β y z) = crd e b y ⬝ᵥ (GlobalTheory.TwLat.gram e b β *ᵥ (c ∘ crd e b z)) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  simp_rw [herm_smul_left, herm_sum_right, herm_smul_right]
  simp only [map_sum, map_mul, hc, crd, GlobalTheory.TwLat.gram, dotProduct, Matrix.mulVec, Function.comp_apply,
    Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.TwOrbUnimod

namespace GlobalTheory.TwOrbUnimod
open GlobalTheory.TwOrbLat

theorem twist_integral_iff_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (β : B.Aˣ) (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → ∀ q : GLw a w, (q⁻¹ * δ * thL a w q ∈ GlobalTheory.LFun.KGL w a ↔ ∀ z, z ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b q, B.herm β y z ∈ (algebraMap K.O K.E).range) := by
  intro E _ _ _ w hw K e he hO a B β b δ hG q
  set F := w.adicCompletion E
  set c := cj w
  have hS : ∀ x : F, x ∈ Ov E w ↔ Valued.v x ≤ 1 := fun x => by
    simp only [Ov]
    first
    | exact Iff.rfl
    | exact IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers E w
    | exact Valued.mem_integer_iff _ _
  have hR : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ e x ∈ Ov E w := fun x => by rw [hO, hS]
  have hc2 : ∀ x, c (c x) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← he, ← he, K.c_c]
  have hcR : ∀ x, K.c x ∈ (algebraMap K.O K.E).range ↔ x ∈ (algebraMap K.O K.E).range := by
    have h1 : ∀ x, x ∈ (algebraMap K.O K.E).range → K.c x ∈ (algebraMap K.O K.E).range := by
      rintro _ ⟨o, rfl⟩
      obtain ⟨o', ho'⟩ := K.c_int o
      exact ⟨o', ho'.symm⟩
    exact fun x => ⟨fun h => K.c_c x ▸ h1 _ h, h1 x⟩
  have hcS : ∀ x, c x ∈ Ov E w ↔ x ∈ Ov E w := fun x => by
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← he, ← hR, ← hR, hcR]
  have hGram : GlobalTheory.TwLat.gram e b (β : B.A) = ((δ.val * GlobalTheory.Tw.Phi a F)⁻¹)ᵀ := by
    exact Matrix.ext fun i j => (hG i j).symm
  set Yg : GLw a w := invT a F (q⁻¹ * (δ * PhiU a F) * invT a F (GeneralLinearGroup.map c q)) with hYg
  have hY : Yg.val = q.valᵀ * GlobalTheory.TwLat.gram e b (β : B.A) * q.val.map c := by
    rw [hGram]
    show ((q⁻¹ * (δ * PhiU a F) * invT a F (GeneralLinearGroup.map c q))⁻¹).valᵀ = _
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← map_inv (invT a F)]
    simp only [Units.val_mul, Matrix.transpose_mul]
    have h2 : (invT a F (GeneralLinearGroup.map c q)⁻¹).val = (GeneralLinearGroup.map c q).valᵀ := by
      show ((GeneralLinearGroup.map c q)⁻¹⁻¹).valᵀ = _
      rw [inv_inv]
    rw [h2, Matrix.transpose_transpose, Matrix.coe_units_inv, Units.val_mul]
    rfl
  have step1 : q⁻¹ * δ * thL a w q ∈ GlobalTheory.LFun.KGL w a ↔ Yg ∈ GlobalTheory.LFun.KGL w a := by
    have hth : thL a w q = PhiU a F * invT a F (GeneralLinearGroup.map c q) * (PhiU a F)⁻¹ := by
      simp only [GlobalTheory.BCT.thL, if_neg hw]
      rfl
    have hP : PhiU a F ∈ GlobalTheory.LFun.KGL w a := PhiU_mem _
    rw [hth, show q⁻¹ * δ * (PhiU a F * invT a F (GeneralLinearGroup.map c q) * (PhiU a F)⁻¹) =
      (q⁻¹ * (δ * PhiU a F) * invT a F (GeneralLinearGroup.map c q)) * (PhiU a F)⁻¹ by group,
      Subgroup.mul_mem_cancel_right _ (inv_mem hP), hYg, invT_mem_iff]
  have step2 : (∀ z, z ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b q, B.herm β y z ∈ (algebraMap K.O K.E).range) ↔
      ∀ u : Fin a → F, (∀ j, u j ∈ Ov E w) ↔ ∀ i, (Yg.1 *ᵥ (c ∘ u)) i ∈ Ov E w := by
    set y : Fin a → B.A := fun j => ofCrd e b fun i => q.val i j with hy
    have hcrdy : ∀ j, crd e b (y j) = fun i => q.val i j := fun j => crd_ofCrd e b _
    have hL : GlobalTheory.TwLat.lat e b q = Submodule.span K.O (Set.range y) := latOf_eq e b q
    have hcomb : ∀ t : Fin a → K.E, crd e b (∑ j, t j • y j) = q.val *ᵥ fun j => e (t j) := by
      intro t
      rw [crd_sum]
      funext i
      simp [crd_smul, hcrdy, Finset.sum_apply, Matrix.mulVec, dotProduct, mul_comm]
    have hinv : ∀ u v : Fin a → F, q.val *ᵥ u = q.val *ᵥ v → u = v := by
      intro u v h
      have := congrArg (fun x => (q⁻¹).val *ᵥ x) h
      simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] using this
    let zOf : (Fin a → F) → B.A := fun u => ofCrd e b (q.val *ᵥ u)
    have hz : ∀ u, crd e b (zOf u) = q.val *ᵥ u := fun u => crd_ofCrd e b _
    have hsurj : ∀ z, ∃ u, z = zOf u := fun z => ⟨(q⁻¹).val *ᵥ crd e b z, by
      apply crd_injective e b
      rw [hz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    have hmem : ∀ u, zOf u ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ j, u j ∈ Ov E w := by
      intro u
      rw [hL, Submodule.mem_span_range_iff_exists_fun]
      constructor
      · rintro ⟨f, hf⟩
        have h1 : (∑ j, f j • y j) = ∑ j, (algebraMap K.O K.E (f j)) • y j :=
          Finset.sum_congr rfl fun j _ => (algebraMap_smul K.E (f j) (y j)).symm
        have h2 := congrArg (crd e b) (h1.symm.trans hf)
        rw [hcomb, hz] at h2
        have h3 := hinv _ _ h2
        intro j
        rw [← h3]
        exact (hR _).1 ⟨f j, rfl⟩
      · intro hu
        choose o ho using fun j => (hR (e.symm (u j))).2 (by rw [RingEquiv.apply_symm_apply]; exact hu j)
        refine ⟨o, ?_⟩
        apply crd_injective e b
        rw [show (∑ j, o j • y j) = ∑ j, (algebraMap K.O K.E (o j)) • y j from
          Finset.sum_congr rfl fun j _ => (algebraMap_smul K.E (o j) (y j)).symm, hcomb, hz]
        congr 1
        funext j
        rw [ho, RingEquiv.apply_symm_apply]
    have hdual : ∀ z, (∀ x ∈ GlobalTheory.TwLat.lat e b q, B.herm β x z ∈ (algebraMap K.O K.E).range) ↔
        ∀ i, B.herm β (y i) z ∈ (algebraMap K.O K.E).range := by
      intro z
      rw [hL]
      constructor
      · intro h i; exact h _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro h x hx
        induction hx using Submodule.span_induction with
        | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
        | zero => rw [herm_zero_left]; exact zero_mem _
        | add x x' _ _ hx hx' => rw [herm_add_left]; exact add_mem hx hx'
        | smul o x _ hx => rw [← algebraMap_smul K.E o x, herm_smul_left]; exact mul_mem ⟨o, rfl⟩ hx
    have hform : ∀ u i, e (B.herm β (y i) (zOf u)) = (Yg.1 *ᵥ (c ∘ u)) i := by
      intro u i
      rw [herm_crd e b c he, hcrdy, hz, hY]
      have hcu : c ∘ (q.val *ᵥ u) = q.val.map c *ᵥ (c ∘ u) := funext fun k => RingHom.map_mulVec c _ _ k
      rw [hcu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rfl
    constructor
    · intro h u
      rw [← hmem, h, hdual]
      exact forall_congr' fun i => by rw [hR, hform]
    · intro h z
      obtain ⟨u, rfl⟩ := hsurj z
      rw [hmem, hdual, h u]
      exact forall_congr' fun i => by rw [hR, hform]
  rw [step1, step2]
  exact mem_GLint_iff_dual c hc2 hcS Yg

end GlobalTheory.TwOrbUnimod
