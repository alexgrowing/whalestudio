import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotientStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GelfParts

open GlobalTheory.SmoothForms MulOpposite

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem map_gelfA {B : Type} [Ring B] (f : A →+* B) (E : Fin n → Fin n → A) (k : ℕ) :
    f (gelfA E k) = gelfA (fun a b => f (E a b)) k := by
  simp only [gelfA, map_sum, map_list_prod, List.map_ofFn, Function.comp_def]

theorem gelfA_mem {S : Type} [SetLike S A] [SubsemiringClass S A] (s : S) {E : Fin n → Fin n → A}
    (h : ∀ a b, E a b ∈ s) (k : ℕ) : gelfA E k ∈ s := by
  simp only [gelfA]
  refine sum_mem fun idx _ => list_prod_mem fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨a, rfl⟩ := hx
  exact h _ _

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem glRel_op {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) : Formalism.REAL.GlRel fun a b => op (-E a b) := by
  intro a b c d
  apply MulOpposite.unop_injective
  have key : E c d * E a b - E a b * E c d =
      -((if b = c then E a d else 0) - (if d = a then E c b else 0)) := by
    rw [← hE a b c d, neg_sub]
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op, neg_mul_neg, key]
  split_ifs <;> (simp; try abel)

private theorem prod_ofFn_mem_filt_succ (E : Fin n → Fin n → A) (m : ℕ) (I K : Fin m → Fin n) :
    (List.ofFn fun a => E (I a) (K a)).prod ∈ filt E (m + 1) := by
  refine range_le_filt (Nat.lt_succ_self m) ⟨Matrix.single I K 1, ?_⟩
  simp [wordMap, Matrix.single_apply]
  rw [Fintype.sum_eq_single I fun x hx => by simp [Ne.symm hx]]
  simp

private theorem list_ofFn_reverse_eq_ofFn_rev' {X : Type} (m : ℕ) (f : Fin m → X) :
    (List.ofFn f).reverse = List.ofFn fun a => f a.rev := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  congr 1
  ext
  simp only [Fin.val_rev]
  simp at h1
  omega

theorem unop_gelfA_mem {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (k : ℕ) :
    unop (gelfA (fun a b => op (-E a b)) k) ∈ Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  set G : Fin n → Fin n → Aᵐᵒᵖ := fun a b => op (-E a b) with hGdef
  have hG : Formalism.REAL.GlRel G := glRel_op hE
  have hc : ∀ a b, E a b * unop (gelfA G k) = unop (gelfA G k) * E a b := by
    intro a b
    have h0 := congrArg MulOpposite.unop (gelf_adjoin_comm hG (Algebra.subset_adjoin ⟨k, rfl⟩) a b)
    simp only [hGdef, MulOpposite.unop_mul, MulOpposite.unop_op, mul_neg, neg_mul, neg_inj] at h0
    exact h0.symm
  have hf : unop (gelfA G k) ∈ filt E (k + 2) := by
    simp only [hGdef, gelfA, Finset.unop_sum, MulOpposite.unop_list_prod, List.map_ofFn, Function.comp_def,
      MulOpposite.unop_op]
    refine sum_mem fun idx _ => ?_
    have hmap : (List.ofFn fun a : Fin (k + 1) => -E (idx a.rev) (idx (a.rev + 1))) =
        (List.ofFn fun a : Fin (k + 1) => E (idx a.rev) (idx (a.rev + 1))).map Neg.neg := by
      rw [List.map_ofFn]
      rfl
    simp only [list_ofFn_reverse_eq_ofFn_rev']
    rw [hmap, List.prod_map_neg, List.length_ofFn]
    have hw := prod_ofFn_mem_filt_succ E (k + 1) (fun a => idx a.rev) (fun a => idx (a.rev + 1))
    rcases neg_one_pow_eq_or A (k + 1) with h | h
    · rw [h, one_mul]; exact hw
    · rw [h, neg_one_mul]; exact neg_mem hw
  exact central_of_filt hE (k + 2) _ hf hc

end Alg

section Pair

variable {M : Type} [AddCommGroup M] [Module ℂ M] (P Q : Submodule ℂ M) (B : M → M → ℂ)
  (h1 : ∀ x ∈ P, ∀ x' ∈ P, ∀ y ∈ Q, B (x + x') y = B x y + B x' y)
  (h2 : ∀ x ∈ P, ∀ y ∈ Q, ∀ y' ∈ Q, B x (y + y') = B x y + B x y')

def adjPairs : Subsemiring (Module.End ℂ M × (Module.End ℂ M)ᵐᵒᵖ) where
  carrier := {p | (∀ x ∈ P, p.1 x ∈ P) ∧ (∀ y ∈ Q, p.2.unop y ∈ Q) ∧ ∀ x ∈ P, ∀ y ∈ Q, B (p.1 x) y = B x (p.2.unop y)}
  mul_mem' := by
    rintro p q ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    exact ⟨fun x hx => a1 _ (b1 x hx), fun y hy => b2 _ (a2 y hy), fun x hx y hy =>
      (a3 _ (b1 x hx) y hy).trans (b3 x hx _ (a2 y hy))⟩
  one_mem' := ⟨fun _ h => h, fun _ h => h, fun _ _ _ _ => rfl⟩
  add_mem' := by
    rintro p q ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun x hx => add_mem (a1 x hx) (b1 x hx), fun y hy => add_mem (a2 y hy) (b2 y hy), fun x hx y hy => ?_⟩
    change B (p.1 x + q.1 x) y = B x (p.2.unop y + q.2.unop y)
    rw [h1 _ (a1 x hx) _ (b1 x hx) y hy, h2 x hx _ (a2 y hy) _ (b2 y hy), a3 x hx y hy, b3 x hx y hy]
  zero_mem' := by
    refine ⟨fun _ _ => zero_mem _, fun _ _ => zero_mem _, fun x hx y hy => ?_⟩
    have e1 := h1 0 (zero_mem _) 0 (zero_mem _) y hy
    have e2 := h2 x hx 0 (zero_mem _) 0 (zero_mem _)
    rw [add_zero, left_eq_add] at e1 e2
    exact e1.trans e2.symm

include h1 h2 in
theorem exists_adj {n : ℕ} {E : Fin n → Fin n → Module.End ℂ M} (hE : Formalism.REAL.GlRel E)
    (hP : ∀ a b, ∀ x ∈ P, E a b x ∈ P) (hQ : ∀ a b, ∀ y ∈ Q, E a b y ∈ Q)
    (h : ∀ a b, ∀ x ∈ P, ∀ y ∈ Q, B (E a b x) y = B x (-E a b y)) (k : ℕ) :
    ∃ z ∈ Algebra.adjoin ℂ (Set.range (gelfA E)), (∀ y ∈ Q, z y ∈ Q) ∧
      ∀ x ∈ P, ∀ y ∈ Q, B (gelfA E k x) y = B x (z y) := by
  have hgen : ∀ a b, ((E a b, op (-E a b)) : Module.End ℂ M × (Module.End ℂ M)ᵐᵒᵖ) ∈ adjPairs P Q B h1 h2 :=
    fun a b => ⟨hP a b, fun y hy => by simpa using neg_mem (hQ a b y hy), fun x hx y hy => by simpa using h a b x hx y hy⟩
  have hmem := gelfA_mem (adjPairs P Q B h1 h2) hgen k
  have e1 := map_gelfA (RingHom.fst (Module.End ℂ M) (Module.End ℂ M)ᵐᵒᵖ)
    (fun a b => ((E a b, op (-E a b)) : Module.End ℂ M × (Module.End ℂ M)ᵐᵒᵖ)) k
  have e2 := map_gelfA (RingHom.snd (Module.End ℂ M) (Module.End ℂ M)ᵐᵒᵖ)
    (fun a b => ((E a b, op (-E a b)) : Module.End ℂ M × (Module.End ℂ M)ᵐᵒᵖ)) k
  simp only [RingHom.coe_fst, RingHom.coe_snd] at e1 e2
  obtain ⟨-, m2, m3⟩ := hmem
  refine ⟨(gelfA (fun a b => op (-E a b)) k).unop, unop_gelfA_mem hE k, fun y hy => ?_, fun x hx y hy => ?_⟩
  · have := m2 y hy
    rwa [e2] at this
  · have := m3 x hx y hy
    rwa [e1, e2] at this

end Pair

variable {D : D7}

def ModS (θ : InfF D) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | IsMod θ V φ}
  add_mem' := by
    rintro φ ψ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨add_mem a1 b1, fun γ hγ g => by simp only [Pi.add_apply, a2 γ hγ, b2 γ hγ], fun l hl => ?_⟩
    rw [word_add hl a1 b1]
    refine ⟨(a3 l hl).1.add (b3 l hl).1, ?_⟩
    obtain ⟨N, C, hC⟩ := (a3 l hl).2
    obtain ⟨N', C', hC'⟩ := (b3 l hl).2
    refine ⟨max N N', |C| + |C'|, fun g => ?_⟩
    have g1 : (1 : ℝ) ≤ (height θ V g : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ V g
    rw [Pi.add_apply, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hC g).trans ?_) ((hC' g).trans ?_))
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ g1 (le_max_left _ _)) (by positivity) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ g1 (le_max_right _ _)) (by positivity) (abs_nonneg _)
  zero_mem' := isMod_const θ V 0
  smul_mem' := by
    rintro c φ ⟨a1, a2, a3⟩
    refine ⟨Submodule.smul_mem _ c a1, fun γ hγ g => by simp only [Pi.smul_apply, a2 γ hγ], fun l hl => ?_⟩
    rw [word_smul hl]
    refine ⟨(a3 l hl).1.const_smul c, ?_⟩
    obtain ⟨N, C, hC⟩ := (a3 l hl).2
    refine ⟨N, ‖c‖ * C, fun g => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c)

theorem gelf_by_parts : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ (Z : Submodule ℂ (GA D V → ℂ)), (∀ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ k, ∀ F ∈ Decay θ V ⊓ Z, ∃ F' ∈ Decay θ V ⊓ Z, ∀ φ, IsMod θ V φ → ∫ g in 𝓕, gelf θ V τ k φ g * F g ∂μ = ∫ g in 𝓕, φ g * F' g ∂μ := by
  intro D θ hθ V μ 𝓕 hq τ Z hZ k F hF
  have h0 : (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ lieAt V τ := by simp [lieAt]
  have hint : ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ :=
    fun φ F hφ hF => (GlobalTheory.T.integration_by_parts_rightDerivative_adelicQuotient D θ hθ V μ 𝓕 hq τ 0 h0 φ F hφ hF).1
  have hRC : ∀ (W : Submodule ℂ (GA D V → ℂ)) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ),
      (∀ X ∈ lieAt V τ, Rder θ V τ X φ ∈ W) → RderC θ V τ Y φ ∈ W := by
    intro W Y φ hW
    obtain ⟨m1, m2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Y
    exact W.add_mem (hW _ m1) (W.smul_mem _ (hW _ m2))
  let S := SmFun θ V
  let P : Submodule ℂ S := (ModS θ V).comap S.subtype
  let Q : Submodule ℂ S := (Decay θ V).comap S.subtype
  let B : S → S → ℂ := fun x y => ∫ g in 𝓕, x.1 g * y.1 g ∂μ
  have h1 : ∀ x ∈ P, ∀ x' ∈ P, ∀ y ∈ Q, B (x + x') y = B x y + B x' y := by
    intro x hx x' hx' y hy
    simp only [B, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (hint _ _ hx hy) (hint _ _ hx' hy)
  have h2 : ∀ x ∈ P, ∀ y ∈ Q, ∀ y' ∈ Q, B x (y + y') = B x y + B x y' := by
    intro x hx y hy y' hy'
    simp only [B, Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add (hint _ _ hx hy) (hint _ _ hx hy')
  let E : Fin V.rank → Fin V.rank → Module.End ℂ S :=
    fun a b => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single a b 1)
  have hE : Formalism.REAL.GlRel E := glRel_derEnd hθ V τ
  have hEv : ∀ a b (x : S), (E a b x).1 = RderC θ V τ (Matrix.single a b 1) x.1 := fun _ _ _ => rfl
  have hP : ∀ a b, ∀ x ∈ P, E a b x ∈ P := by
    intro a b x hx
    have hx' : IsMod θ V x.1 := hx
    show (E a b x).1 ∈ ModS θ V
    rw [hEv]
    exact hRC (ModS θ V) _ _ fun X hX => hx'.rder hX
  have hQ : ∀ a b, ∀ y ∈ Q, E a b y ∈ Q := by
    intro a b y hy
    have hy' : y.1 ∈ Decay θ V := hy
    show (E a b y).1 ∈ Decay θ V
    rw [hEv]
    exact hRC (Decay θ V) _ _ fun X hX => Rder_mem_Decay hy' hX
  have hadj : ∀ a b, ∀ x ∈ P, ∀ y ∈ Q, B (E a b x) y = B x (-E a b y) := by
    intro a b x hx y hy
    have hx' : IsMod θ V x.1 := hx
    have hy' : y.1 ∈ Decay θ V := hy
    obtain ⟨m1, m2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ (Matrix.single a b 1)
    have r1 := (GlobalTheory.T.integration_by_parts_rightDerivative_adelicQuotient D θ hθ V μ 𝓕 hq τ _ m1 x.1 y.1 hx' hy').2
    have r2 := (GlobalTheory.T.integration_by_parts_rightDerivative_adelicQuotient D θ hθ V μ 𝓕 hq τ _ m2 x.1 y.1 hx' hy').2
    have i1 := hint _ _ (hx'.rder m1) hy'
    have i2 := hint _ _ (hx'.rder m2) hy'
    have j1 := hint _ _ hx' (Rder_mem_Decay hy' m1)
    have j2 := hint _ _ hx' (Rder_mem_Decay hy' m2)
    simp only [B, Submodule.coe_neg, hEv, Pi.neg_apply, RderC, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (fun g => (Rder θ V τ ((1 / 2 : ℂ) • (Matrix.single a b 1 + conjAt V τ (Matrix.single a b 1))) x.1 g +
        Complex.I * Rder θ V τ ((1 / (2 * Complex.I)) • (Matrix.single a b 1 - conjAt V τ (Matrix.single a b 1))) x.1 g) *
          y.1 g) = fun g => Rder θ V τ ((1 / 2 : ℂ) • (Matrix.single a b 1 + conjAt V τ (Matrix.single a b 1))) x.1 g *
          y.1 g + Complex.I * (Rder θ V τ ((1 / (2 * Complex.I)) • (Matrix.single a b 1 -
            conjAt V τ (Matrix.single a b 1))) x.1 g * y.1 g) from funext fun g => by ring,
      show (fun g => x.1 g * -(Rder θ V τ ((1 / 2 : ℂ) • (Matrix.single a b 1 + conjAt V τ (Matrix.single a b 1))) y.1 g +
        Complex.I * Rder θ V τ ((1 / (2 * Complex.I)) • (Matrix.single a b 1 - conjAt V τ (Matrix.single a b 1))) y.1 g)) =
          fun g => -(x.1 g * Rder θ V τ ((1 / 2 : ℂ) • (Matrix.single a b 1 + conjAt V τ (Matrix.single a b 1))) y.1 g +
          Complex.I * (x.1 g * Rder θ V τ ((1 / (2 * Complex.I)) • (Matrix.single a b 1 -
            conjAt V τ (Matrix.single a b 1))) y.1 g)) from funext fun g => by ring,
      integral_add i1 (i2.const_mul _), integral_neg, integral_add j1 (j2.const_mul _), integral_const_mul,
      integral_const_mul, r1, r2]
    ring
  obtain ⟨z, hz, hzQ, hzB⟩ := exists_adj P Q B h1 h2 hE hP hQ hadj k
  have hF' := Submodule.mem_inf.1 hF
  let Fs : S := ⟨F, hF'.1.1⟩
  have hFQ : Fs ∈ Q := hF'.1
  have hzZ : ∀ x : S, x.1 ∈ Z → (z x).1 ∈ Z := by
    refine Algebra.adjoin_induction (p := fun z _ => ∀ x : S, x.1 ∈ Z → (z x).1 ∈ Z) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨j, rfl⟩ x hx
      rw [← GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ j x]
      exact hZ j _ hx
    · intro c x hx
      rw [Module.algebraMap_end_apply]
      exact Z.smul_mem c hx
    · intro u v _ _ hu hv x hx
      exact Z.add_mem (hu x hx) (hv x hx)
    · intro u v _ _ hu hv x hx
      exact hu _ (hv x hx)
  refine ⟨(z Fs).1, Submodule.mem_inf.2 ⟨hzQ Fs hFQ, hzZ Fs hF'.2⟩, fun φ hφ => ?_⟩
  have e : gelf θ V τ k φ = (gelfA E k ⟨φ, hφ.1⟩).1 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k ⟨φ, hφ.1⟩
  rw [e]
  exact hzB ⟨φ, hφ.1⟩ hφ Fs hFQ

end GlobalTheory.Mem.GelfParts

end
