import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section SyLemmas

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  (w : O) (Fr : Frames n' r) (Q : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n'))

local notation "PP" => MvPolynomial (TV n' k) (KK O)

theorem hom_iff {R : Type*} [CommRing R] (P : MvPolynomial (TV n' k) R) (o : ℕ) :
    (∀ m ∈ P.support, normDeg r m = o) ↔ IsWeightedHomogeneous (normalVariableWeight n' k r) P o := by
  constructor
  · intro h m hm; rw [weight_eq_normal_degree]; exact h m (mem_support_iff.2 hm)
  · intro h m hm; rw [← weight_eq_normal_degree]; exact h (mem_support_iff.1 hm)

variable {w Fr Q g}

theorem Sy_mul {o1 o2 : ℕ} {P1 P2 : PP} (h1 : Sy w Fr Q g o1 P1) (h2 : Sy w Fr Q g o2 P2) :
    Sy w Fr Q g (o1 + o2) (P1 * P2) := by
  refine ⟨(hom_iff _ _).2 (((hom_iff _ _).1 h1.1).mul ((hom_iff _ _).1 h2.1)), ?_⟩
  have := bc_gr_mul (bc_agen_mul w Fr Q g) h1.2 h2.2
  have e : C (algebraMap O (KK O) (w ^ (o1 + o2))) * (P1 * P2) =
      (C (algebraMap O (KK O) (w ^ o1)) * P1) * (C (algebraMap O (KK O) (w ^ o2)) * P2) := by
    rw [pow_add, map_mul, C_mul]; ring
  rw [e]; simpa using this

theorem IT_hom {H : PP} (h : bc_IT Fr H) : IsWeightedHomogeneous (normalVariableWeight n' k r) H 0 := by
  obtain ⟨h0, h1, _, rfl⟩ := h
  rw [← hom_iff]
  intro m hm
  have hm' : m ∈ h0.support := support_map_subset _ _ hm
  unfold normDeg
  refine Finset.sum_eq_zero fun v hv => ?_
  rw [if_neg (h1 v ((mem_vars v).2 ⟨m, hm', hv⟩))]

theorem Sy_IT {H : PP} (h : bc_IT Fr H) : Sy w Fr Q g 0 H :=
  ⟨(hom_iff _ _).2 (IT_hom h), AddSubmonoid.subset_closure ⟨1, H, isKeyProduct_one w Fr Q g, h, by simp⟩⟩

theorem SyS_of_Sy {o : ℕ} {P : PP} (h : Sy w Fr Q g o P) : P ∈ SyS w Fr Q g := AddSubmonoid.subset_closure ⟨o, h⟩

theorem SyS_mul {a b : PP} (ha : a ∈ SyS w Fr Q g) (hb : b ∈ SyS w Fr Q g) : a * b ∈ SyS w Fr Q g := by
  have h := AddSubmonoid.mul_mem_mul ha hb
  unfold SyS at h
  rw [AddSubmonoid.closure_mul_closure] at h
  refine AddSubmonoid.closure_mono ?_ h
  rintro _ ⟨x, ⟨o1, h1⟩, y, ⟨o2, h2⟩, rfl⟩
  exact ⟨o1 + o2, Sy_mul h1 h2⟩

theorem SyS_prod {κ : Type*} (s : Finset κ) (f : κ → PP) (h : ∀ t ∈ s, f t ∈ SyS w Fr Q g) :
    ∏ t ∈ s, f t ∈ SyS w Fr Q g := by
  induction s using Finset.induction_on with
  | empty => simpa using SyS_of_Sy (Sy_IT (w := w) (Q := Q) (g := g) (bc_IT_one (Fr := Fr)))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact SyS_mul (h a (Finset.mem_insert_self a s)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

theorem IT_C (c : O) : bc_IT Fr (C (algebraMap O (KK O) c) : PP) :=
  ⟨C c, fun v hv => by simp at hv, fun v hv => by simp at hv, by simp⟩

theorem SyS_comp {H0 : PP} (hH0 : IsWeightedHomogeneous (normalVariableWeight n' k r) H0 0) {Z : PP} (hZ : Z ∈ SyS w Fr Q g) (o : ℕ) :
    ∃ W ∈ AddSubmonoid.closure (bc_agen w Fr Q g o 0),
      C (algebraMap O (KK O) (w ^ o)) * weightedHomogeneousComponent (normalVariableWeight n' k r) o (Z * H0) = W * H0 := by
  unfold SyS at hZ
  induction hZ using AddSubmonoid.closure_induction with
  | mem P hP =>
    obtain ⟨o', h1, h2⟩ := hP
    have hh : IsWeightedHomogeneous (normalVariableWeight n' k r) (P * H0) o' := by
      have := ((hom_iff _ _).1 h1).mul hH0
      simpa using this
    by_cases e : o = o'
    · subst e
      exact ⟨_, h2, by rw [hh.weightedHomogeneousComponent_same]; ring⟩
    · exact ⟨0, zero_mem _, by rw [hh.weightedHomogeneousComponent_ne o e]; simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨W1, a1, b1⟩ := hx
    obtain ⟨W2, a2, b2⟩ := hy
    exact ⟨W1 + W2, add_mem a1 a2, by rw [add_mul, map_add, mul_add, b1, b2, add_mul]⟩

theorem inWj_compN {w : O} (o : ℕ) {P : PP} {j : ℕ} (hP : InWj w P j) :
    InWj w (weightedHomogeneousComponent (normalVariableWeight n' k r) o P) j := fun m => by
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact hP m
  · exact ⟨0, by simp⟩

end SyLemmas

section Core

variable {p n' r K : ℕ} [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)

local notation "PP" => MvPolynomial (TV n' (r + K)) (KK O)

theorem fixed_symbol_factor_integral (c' : ℕ) : bc_IT X.Fr (X.fixedSymbolFactor c') := by
  have hn := X.hH.2.2.2.2
  have hr : 1 ≤ r := by have := X.hH.2.1; omega
  unfold Ctx.fixedSymbolFactor Ctx.sb
  refine bc_IT_mul (bc_IT_mul (bc_IT_pow ?_ _) (bc_IT_prod _ _ fun j _ =>
    bc_IT_pow (bc_IT_Del X.S.w X.Fr X.hV hn X.hH.2.2.1 X.hg j) _)) ?_
  · unfold R0
    rw [map_prod]
    refine bc_IT_prod _ _ fun j _ => ?_
    rw [map_pow]
    exact bc_IT_pow (bc_IT_Del X.S.w X.Fr X.hV hn X.hH.2.2.1 X.hg j) _
  · unfold DtopProd
    rw [map_prod]
    refine bc_IT_prod _ _ fun s _ => ?_
    rw [map_pow]
    exact bc_IT_pow (bc_IT_Dtop X.S.w X.Fr X.hV hn hr X.hH.2.2.1 X.hg _) _

theorem terms_of_agen (c' o : ℕ) {W : PP} (hW : W ∈ AddSubmonoid.closure (bc_agen X.S.w X.Fr X.Q X.g o 0)) :
    ∃ l : List (Term n' (r + K) O), (∀ τ ∈ l, τ.Valid p n' X.S.w n' r X.Q X.g ∧ τ.InTops X.Fr ∧ o ≤ τ.level) ∧
      W * X.fixedSymbolFactor c' = (l.map fun τ => τ.sym p n' X.S.w X.Fr X.hH.2.2.1 X.g c' ((2 * X.Q + 3) * c') c').sum := by
  induction hW using AddSubmonoid.closure_induction with
  | mem P hP =>
    obtain ⟨A1, H, h1, h2, rfl⟩ := hP
    obtain ⟨τ, t1, t2, t3, t4⟩ := bc_sym_of_KP X.S.w X.Fr X.Q X.g X.hH.2.2.1 c' ((2 * X.Q + 3) * c') c' 0 h1 h2
    refine ⟨[τ], ?_, ?_⟩
    · intro τ' hτ'
      rw [List.mem_singleton] at hτ'
      subst hτ'
      exact ⟨t1, t2, by omega⟩
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [t4]
      unfold Ctx.fixedSymbolFactor Ctx.sb
      simp only [pow_zero, map_one, one_mul]
      ring
  | zero => exact ⟨[], by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l1, a1, b1⟩ := hx
    obtain ⟨l2, a2, b2⟩ := hy
    refine ⟨l1 ++ l2, ?_, by rw [add_mul, b1, b2, List.map_append, List.sum_append]⟩
    intro τ hτ
    rcases List.mem_append.1 hτ with h | h
    · exact a1 τ h
    · exact a2 τ h

theorem core (D : Formalism.BasicNotions.D7) (c' o : ℕ) (T Z Y' : PP) (hZ : Z ∈ X.SyS) (hY : InWj X.S.w Y' 0)
    (hT : T = Z * X.fixedSymbolFactor c' + C (algebraMap O (KK O) ((p : O) ^ c')) * Y')
    (ho : ∀ m ∈ T.support, normDeg r m = o) : Realisable p n' X.S.w n' r X.g c' o T := by
  obtain ⟨W, hW, hWe⟩ := SyS_comp (IT_hom (fixed_symbol_factor_integral X c')) hZ o
  obtain ⟨l, hl, hle⟩ := terms_of_agen X c' o hW
  have hTo := ((hom_iff _ _).1 ho).weightedHomogeneousComponent_same

  have hdiff : InWj X.S.w (C (algebraMap O (KK O) (X.S.w ^ o)) * T - W * X.fixedSymbolFactor c') (o + c') := by
    have e1 : T = weightedHomogeneousComponent (normalVariableWeight n' (r + K) r) o (Z * X.fixedSymbolFactor c') +
        C (algebraMap O (KK O) ((p : O) ^ c')) * weightedHomogeneousComponent (normalVariableWeight n' (r + K) r) o Y' := by
      conv_lhs => rw [← hTo, hT]
      rw [map_add, C_mul', C_mul', map_smul]
    have e2 : C (algebraMap O (KK O) (X.S.w ^ o)) * T - W * X.fixedSymbolFactor c' =
        C (algebraMap O (KK O) (X.S.w ^ (o + c') * X.S.w ^ c')) *
          weightedHomogeneousComponent (normalVariableWeight n' (r + K) r) o Y' := by
      rw [← hWe]
      conv_lhs => rw [e1]
      have hp : (p : O) ^ c' = X.S.w ^ c' * X.S.w ^ c' := by
        rw [← X.hO.1, ← pow_mul, ← pow_add]; congr 1; omega
      rw [hp, pow_add]
      simp only [map_mul, C_mul]
      ring
    rw [e2]
    have := inWj_mul (inWj_C (σ := TV n' (r + K)) (w := X.S.w) (o + c') (X.S.w ^ c')) (inWj_compN (r := r) o hY)
    simpa using this
  obtain ⟨F0, hA, _, hW0, hG⟩ := clean_symbol_order D (symbol_order_ge_level D) (raw_term_order_ge_off_plane D (localiser_vanishing_off_plane D) (bs_restRawTops D))
    (order_claim_of_residue_form D (bc_claim' D)) p n' r (r + K) O X.S X.hO X.hH X.Fr X.L₁ X.N₁ X.hV X.Q X.hT X.g X.hg c' o
    l.length (fun i => l[i.1]) (fun i => hl _ (List.getElem_mem i.2))
  rw [Fin.sum_univ_fun_getElem l (fun τ => τ.sym p n' X.S.w X.Fr X.hH.2.2.1 X.g c' ((2 * X.Q + 3) * c') c'),
    ← hle] at hW0
  have hF0 : InWj X.S.w (subst p n' O X.S.w n' r X.g F0 - C (algebraMap O (KK O) (X.S.w ^ o)) * T) (o + c') := by
    have := inWj_sub hW0 hdiff
    have e : subst p n' O X.S.w n' r X.g F0 - C (algebraMap O (KK O) (X.S.w ^ o)) * T =
        (subst p n' O X.S.w n' r X.g F0 - W * X.fixedSymbolFactor c') -
          (C (algebraMap O (KK O) (X.S.w ^ o)) * T - W * X.fixedSymbolFactor c') := by ring
    rw [e]; exact this
  by_cases h0 : T = 0
  · refine ⟨0, (inA_iff_inWj0 (w := X.S.w) _).2 (inWj_zero 0), fun d' _ => Submodule.zero_mem _, ?_, ?_⟩
    · rw [h0, map_zero, mul_zero, sub_zero]; exact inWj_zero _
    · intro g' _ _
      show InWj X.S.w (subst p n' O X.S.w n' r g' 0) (o + c')
      rw [map_zero]; exact inWj_zero _
  by_cases hd : ∃ d, HasMultideg T d
  · obtain ⟨d, hd⟩ := hd
    refine ⟨weightedHomogeneousComponent (coordinatePositionWeight n' (r + K)) d F0,
      (integral_iff_order_zero X.S.w _).2 (inWPow_weighted_component d ((integral_iff_order_zero X.S.w _).1 hA)), ?_, ?_, ?_⟩
    · intro d' hd'
      rw [multideg_unique h0 hd hd']
      exact (hasMultideg_iff_weighted_homog _ _).2 (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · have hs : IsWeightedHomogeneous (coordinatePositionWeight n' (r + K)) (C (algebraMap O (KK O) (X.S.w ^ o)) * T) d :=
        ((hasMultideg_iff_weighted_homog _ _).1 hd).C_mul _
      have := inWPow_weighted_component d hF0
      rw [map_sub, weighted_component_substitute_comm, hs.weightedHomogeneousComponent_same] at this
      exact this
    · intro g' hg' hne
      have := inWPow_weighted_component d (hG g' hg' hne)
      show InWj X.S.w (subst p n' O X.S.w n' r g' _) _
      rw [← weighted_component_substitute_comm]
      exact this
  · exact ⟨F0, hA, fun d h => absurd ⟨d, h⟩ hd, hF0, hG⟩

end Core

end Formalism.MainNotions.G.symbolGeneratorData
