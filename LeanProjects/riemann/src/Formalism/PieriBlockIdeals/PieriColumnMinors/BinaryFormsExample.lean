import Formalism.PieriBlockIdeals.LemmaDSkeletonUnit
import Formalism.PieriBlockIdeals.PieriColumnMinors.Symmetrization
import Formalism.PieriBlockIdeals.PieriColumnMinors.DividedPowerZeroZeroVector

open Polynomial

namespace Formalism.CohomologicalDescent.BinaryFormsExample

open Formalism.CohomologicalDescent.Symmetrization

theorem good_part_abstract_holds : GoodPartAbstract := by
  intro K M I _ _ _ n c Mt χ hχ htop w
  set A : Module.End K M := w ^ n • (1 : Module.End K M) + ∑ a : Fin n, w ^ a.val • c a with hA
  have hAm : ∀ τ, ∀ m ∈ Mt τ, A m = (w ^ n + ∑ a : Fin n, χ τ a * w ^ a.val) • m := by
    intro τ m hm
    simp only [hA, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply, add_smul,
      Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hχ τ a m hm, smul_smul, mul_comm]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ τ, Mt τ := by rw [htop]; trivial
    refine Submodule.iSup_induction Mt (motive := fun x => A x ∈
      ⨆ τ ∈ {τ : I | w ^ n + ∑ a : Fin n, χ τ a * w ^ a.val ≠ 0}, Mt τ) hx ?_ ?_ ?_
    · intro τ m hm
      rw [hAm τ m hm]
      by_cases hs : w ^ n + ∑ a : Fin n, χ τ a * w ^ a.val = 0
      · rw [hs, zero_smul]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem τ (Submodule.mem_iSup_of_mem hs hm))
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · refine iSup₂_le fun τ hτ m hm => ?_
    refine ⟨(w ^ n + ∑ a : Fin n, χ τ a * w ^ a.val)⁻¹ • m, ?_⟩
    rw [map_smul, hAm τ m hm, smul_smul, inv_mul_cancel₀ hτ, one_smul]

theorem eval_monic_sum_C_mul_X_pow {K : Type} [CommRing K] (n : ℕ) (χ : Fin n → K) (w : K) :
    (X ^ n + ∑ a : Fin n, C (χ a) * X ^ a.val : K[X]).eval w = w ^ n + ∑ a : Fin n, χ a * w ^ a.val := by
  simp [eval_finsetSum]

theorem good_part_holds : GoodPart := by
  intro K R P M I _ _ _ _ _ _ _ _ EM hEM n Mt χ h3a htop w good hbad
  obtain ⟨c, hc1, -, hc3, -⟩ := coefficient_operators_hold K K R P M EM hEM n
  have hχ : ∀ τ a, ∀ y ∈ Mt τ, c a y = χ τ a • y := by
    intro τ a y hy
    obtain ⟨z', rfl⟩ := toSym_surjective (k := K) y
    rw [hc1, h3a τ a z' hy]
  have hr := good_part_abstract_holds K _ I n c Mt χ hχ htop w
  constructor
  · intro z
    have h1 : toSym K (AA K EM n w z) ∈ LinearMap.range
        (w ^ n • (1 : Module.End K (Sym (R × P) n → M)) + ∑ a : Fin n, w ^ a.val • c a) := by
      rw [hc3]; exact LinearMap.mem_range_self _ _
    rw [hr] at h1
    refine (iSup₂_le fun τ hτ => ?_ : _ ≤ ⨆ τ ∈ good, Mt τ) h1
    have hg : τ ∈ good := by
      by_contra hg
      exact hτ (by rw [← eval_monic_sum_C_mul_X_pow]; exact hbad τ hg)
    exact le_iSup₂_of_le τ hg le_rfl
  · intro hgood y hy
    have h1 : y ∈ LinearMap.range
        (w ^ n • (1 : Module.End K (Sym (R × P) n → M)) + ∑ a : Fin n, w ^ a.val • c a) := by
      rw [hr]
      refine (iSup₂_le fun τ hτ => ?_ : (⨆ τ ∈ good, Mt τ) ≤ _) hy
      exact le_iSup₂_of_le (f := fun τ (_ : τ ∈ {τ : I | w ^ n + ∑ a : Fin n, χ τ a * w ^ a.val ≠ 0}) => Mt τ) τ
        (by have := hgood τ hτ; rwa [eval_monic_sum_C_mul_X_pow] at this) le_rfl
    obtain ⟨y', rfl⟩ := h1
    obtain ⟨z, rfl⟩ := toSym_surjective (k := K) y'
    exact ⟨z, (hc3 w z).symm⟩

section Form

variable {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]

theorem contravariant_flip (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V) (h : Contra S B) :
    Contra S (LinearMap.flip B) := by
  intro a b x y
  rw [LinearMap.flip_apply, LinearMap.flip_apply]
  exact (h b a y x).symm

theorem pairing_list_reverse_adjoint (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V) (h : Contra S B) :
    ∀ (L : List (R × P)) (x y : V), B ((L.map S.f).prod x) y = B x ((L.reverse.map S.e).prod y)
  | [], x, y => by simp
  | v :: L, x, y => by
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.reverse_cons, List.map_append, List.prod_append,
      Module.End.mul_apply]
    have h1 : B (S.f v ((L.map S.f).prod x)) y = B ((L.map S.f).prod x) (S.e v y) := h _ _ _ _
    rw [h1, pairing_list_reverse_adjoint S B h L]
    simp

theorem pairing_list_adjoint (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V) (h : Contra S B) (L : List (R × P)) (x y : V) :
    B ((L.map S.f).prod x) y = B x ((L.map S.e).prod y) := by
  rw [pairing_list_reverse_adjoint S B h, list_prod_map_eq_of_perm_pairwise_commute S.e (fun a b => raising_operators_commute S a b) (List.reverse_perm L)]

theorem wordProducts_eq_list_prod (S : HidaSetting k V P R) {n : ℕ} (g : Fin n → R × P) :
    S.Fw g = ((List.ofFn g).map S.f).prod ∧ S.Ew g = ((List.ofFn g).map S.e).prod := by
  constructor <;> · rw [List.map_ofFn]; rfl

theorem pairing_word_adjoint (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V) (h : Contra S B) {n : ℕ} (g : Fin n → R × P)
    (x y : V) : B (S.Fw g x) y = B x (S.Ew g y) := by
  rw [(wordProducts_eq_list_prod S g).1, (wordProducts_eq_list_prod S g).2]; exact pairing_list_adjoint S B h _ x y

end Form

theorem contravariant_word_holds : ContraWord := by
  intro k V P R _ _ _ _ _ S B h n x y
  refine ⟨fun g => ⟨pairing_word_adjoint S B h g x y, ?_⟩, fun m => ⟨pairing_list_adjoint S B h _ x y, ?_⟩⟩
  · have := pairing_word_adjoint S _ (contravariant_flip S B h) g y x
    rwa [LinearMap.flip_apply, LinearMap.flip_apply] at this
  · have := pairing_list_adjoint S _ (contravariant_flip S B h) m.1.toList y x
    rwa [LinearMap.flip_apply, LinearMap.flip_apply] at this

theorem contravariant_iota_holds : ContraIota := by
  intro k V P R _ _ _ _ _ _ _ S B h n m u v
  obtain ⟨h1, h2⟩ := (contravariant_word_holds k V P R S B h n u v).2 m
  obtain ⟨-, h4⟩ := (contravariant_word_holds k V P R S B h n v u).2 m
  unfold HidaSetting.iota
  constructor
  · rw [map_smul, LinearMap.smul_apply, map_smul, h1]
  · rw [map_smul, map_smul, LinearMap.smul_apply, h4]

theorem sum_diagFirst_eq_smul {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P]
    [Fintype P] (w : k) (n : ℕ) (z : Tens R P M n) :
    ∑ α : P, diagX k w α α z = ((Fintype.card P : k) * w - (n : k)) • z := by
  funext g
  have h1 : ∀ j : Fin n, ∑ α : P, (unitX k j α α z) g = z g := by
    intro j
    simp only [unitFirst_apply_formula]
    rw [Finset.sum_ite_eq]
    simp
  simp only [diagX, if_true, Finset.sum_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.sum_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => h1 j]
  simp [sub_smul, mul_smul, Nat.cast_smul_eq_nsmul]

theorem depth_eigen_holds : DepthEigen := by
  intro k V P R _ _ _ _ _ _ _ S n z
  rw [LinearMap.sum_apply, Finset.sum_congr rfl fun α _ => ((symMap_equivariant_holds k V P R S n z).2.1 α α), ← map_sum,
    sum_diagFirst_eq_smul, map_smul]

theorem depth_orthogonal_holds : DepthOrthogonal := by
  intro k V P R _ _ _ _ _ _ _ _ S B h n n' hne z z'
  have h1 : B ((∑ α : P, S.E (Sum.inl α) (Sum.inl α)) (S.mu n z)) (S.mu n' z') =
      B (S.mu n z) ((∑ α : P, S.E (Sum.inl α) (Sum.inl α)) (S.mu n' z')) := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun α _ => h _ _ _ _
  rw [depth_eigen_holds, depth_eigen_holds, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h1
  have h2 : ((n' : k) - (n : k)) * B (S.mu n z) (S.mu n' z') = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast (sub_eq_zero.1 h3).symm) hne
  · exact h3

theorem lowering_symMap_eq_symMap_succ {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (n : ℕ) (v : R × P) (z : Tens R P S.W n) :
    S.f v (S.mu n z) = S.mu (n + 1) (fun g => if g 0 = v then z (Fin.tail g) else 0) := by
  rw [symMap_succ_eq_sum_contract S n 0]
  have h1 : ∀ v' : R × P, contr k 0 v' (fun g : Fin (n + 1) → R × P => if g 0 = v then z (Fin.tail g) else 0) =
      if v' = v then z else 0 := by
    intro v'
    funext g
    rw [contract_apply_insertNth]
    by_cases hv : v' = v <;> simp [hv]
  rw [Finset.sum_congr rfl fun v' _ => by rw [h1 v']]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb; simp [hb]
  · intro hv; exact absurd (Finset.mem_univ _) hv

theorem depth_span_holds : DepthSpan := by
  intro k V P R _ _ _ _ _ _ _ S
  have h1 : LinearMap.range (S.mu 0) = S.W := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      rw [symMap_zero_eq_default]; exact (z default).2
    · intro u hu
      exact ⟨fun _ => ⟨u, hu⟩, by rw [symMap_zero_eq_default]⟩
  have h2 : ∀ (n : ℕ) (v : R × P) (z : Tens R P S.W n), S.f v (S.mu n z) ∈ LinearMap.range (S.mu (n + 1)) :=
    fun n v z => ⟨_, (lowering_symMap_eq_symMap_succ S n v z).symm⟩
  have h3 : ∀ (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)), S.e v (S.mu (n + 1) z) ∈ LinearMap.range (S.mu n) :=
    fun n v z => ⟨_, (raising_symMap_eq_one_level_down S n v z).symm⟩
  have h4 : ∀ (v : R × P) (z : Tens R P S.W 0), S.e v (S.mu 0 z) = 0 := by
    intro v z
    rw [symMap_zero_eq_default]; exact S.kill _ _ _ (z default).2
  have h5 : ∀ (n : ℕ) (z : Tens R P S.W n),
      (∀ c d : R, S.E (Sum.inr c) (Sum.inr d) (S.mu n z) ∈ LinearMap.range (S.mu n)) ∧
      ∀ α β : P, S.E (Sum.inl α) (Sum.inl β) (S.mu n z) ∈ LinearMap.range (S.mu n) := by
    intro n z
    obtain ⟨ha, hb, -⟩ := symMap_equivariant_holds k V P R S n z
    exact ⟨fun c d => ⟨_, (ha c d).symm⟩, fun α β => ⟨_, (hb α β).symm⟩⟩
  have h6 : ∀ a b, ∀ x ∈ ⨆ n, LinearMap.range (S.mu n), S.E a b x ∈ ⨆ n, LinearMap.range (S.mu n) := by
    intro a b x hx
    refine Submodule.iSup_induction (fun n => LinearMap.range (S.mu n))
      (motive := fun x => S.E a b x ∈ ⨆ n, LinearMap.range (S.mu n)) hx ?_ ?_ ?_
    · rintro n _ ⟨z, rfl⟩
      rcases a with α | c <;> rcases b with β | d
      · exact Submodule.mem_iSup_of_mem n ((h5 n z).2 α β)
      · rcases n with _ | n
        · have := h4 (d, α) z
          rw [show S.E (Sum.inl α) (Sum.inr d) = S.e (d, α) from rfl, this]; exact Submodule.zero_mem _
        · exact Submodule.mem_iSup_of_mem n (h3 n (d, α) z)
      · exact Submodule.mem_iSup_of_mem (n + 1) (h2 n (c, β) z)
      · exact Submodule.mem_iSup_of_mem n ((h5 n z).1 c d)
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  refine ⟨h1, h2, h3, h4, h5, h6, fun hgen => hgen _ ?_ h6⟩
  exact h1.symm.le.trans (le_iSup (fun n => LinearMap.range (S.mu n)) 0)

theorem mfact_cast_ne_zero {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι] {n : ℕ} (m : Sym ι n) :
    (mfact m : k) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun v _ => Nat.factorial_ne_zero _

theorem iota_kernel_holds : IotaKernel := by
  intro k V P R _ _ _ _ _ _ _ _ S B h n v hv z
  rw [symMap_apply_sum_words, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [pairing_word_adjoint S B h, ← (word_products_of_content S g).2]
  have h1 := hv (cont g)
  unfold HidaSetting.iota at h1
  rw [(smul_eq_zero_iff_right (inv_ne_zero (mfact_cast_ne_zero _))).1 h1, map_zero]

theorem iota_injective_holds : IotaInjective := by
  intro k V P R _ _ _ _ _ _ _ _ S B h hgen hnd n z hz
  apply hnd
  intro x
  have hx : x ∈ ⨆ n, LinearMap.range (S.mu n) := by
    rw [(depth_span_holds k V P R S).2.2.2.2.2.2 hgen]; trivial
  refine Submodule.iSup_induction (fun n => LinearMap.range (S.mu n))
    (motive := fun x => B x (S.mu n z) = 0) hx ?_ ?_ ?_
  · rintro n' _ ⟨z', rfl⟩
    by_cases hn : n' = n
    · subst hn; exact iota_kernel_holds k V P R S B h _ _ hz z'
    · exact depth_orthogonal_holds k V P R S B h n' n hn z' z
  · simp
  · intro x y hx hy; rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

theorem nabla_criterion_holds : NablaCriterion := by
  intro O K V P R _ _ _ _ _ _ _ _ _ _ _ _ S B DelL h n z
  constructor
  · intro hv m
    refine ⟨toSym K (AA K S.EW n S.w z) m, ?_, iota_symMap_holds K V P R S n z m⟩
    unfold NablaL
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro x hx
    change B ((toSym K (AA K S.EW n S.w z) m : S.W) : V) (x : V) ∈ (1 : Submodule O K)
    rw [← iota_symMap_holds K V P R S n z m, ← (contravariant_iota_holds K V P R S B h n m x (S.mu n z)).2]
    refine hv _ (Submodule.mem_iSup_of_mem n (Submodule.subset_span ⟨m, x, hx, rfl⟩))
  · intro hv
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    have hle : DeltaAll S DelL ≤ (1 : Submodule O K).comap ((B (S.mu n z)).restrictScalars O) := by
      refine iSup_le fun n' => Submodule.span_le.2 ?_
      rintro _ ⟨m, u, hu, rfl⟩
      change B (S.mu n z) (((mfact m : K)⁻¹) • S.Fs m (u : V)) ∈ (1 : Submodule O K)
      by_cases hn : n' = n
      · subst hn
        rw [(contravariant_iota_holds K V P R S B h _ m u (S.mu _ z)).2]
        obtain ⟨u', hu', he⟩ := hv m
        rw [he]
        exact hu' u hu
      · obtain ⟨g, rfl⟩ := content_surjective m
        rw [(word_products_of_content S g).1, ← symMap_single_eq_wordProduct, map_smul,
          depth_orthogonal_holds K V P R S B h n n' (Ne.symm hn), smul_zero]
        exact Submodule.zero_mem _
    exact fun y hy => hle hy

theorem dual_stable_holds : DualStable := by
  intro O K V P R _ _ _ _ _ _ _ _ _ S B DelL h hst b b' u hu
  unfold NablaL at hu ⊢
  rw [LinearMap.BilinForm.mem_dualSubmodule] at hu ⊢
  intro x hx
  have h1 := hu _ (hst b' b x hx)
  change B (S.E (Sum.inr b) (Sum.inr b') (u : V)) (x : V) ∈ (1 : Submodule O K)
  rw [h]
  exact h1

theorem mem_shapes_holds : MemShapes := by
  intro p w i q lam2 tau
  unfold LD.shapes shapesAll
  simp only [Finset.mem_filter]
  tauto

theorem shape_eval_zero_holds : ShapeEvalZero := by
  intro q lam2 tau c
  unfold shapePoly LD.boxesOfContent
  rw [eval_prod, Finset.prod_eq_zero_iff, Finset.card_ne_zero]
  constructor
  · rintro ⟨a, -, ha⟩
    rw [eval_prod, Finset.prod_eq_zero_iff] at ha
    obtain ⟨j, hj, hj0⟩ := ha
    rw [Finset.mem_Ico] at hj
    simp only [eval_sub, eval_X, eval_C] at hj0
    exact ⟨a, by rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_, ?_⟩ <;> omega⟩
  · rintro ⟨a, ha⟩
    rw [Finset.mem_filter] at ha
    refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [eval_prod, Finset.prod_eq_zero_iff]
    refine ⟨(c + a.val).toNat, ?_, ?_⟩
    · rw [Finset.mem_Ico]; omega
    · simp only [eval_sub, eval_X, eval_C]; omega

theorem shapePoly_monic {q : ℕ} (lam2 tau : Fin q → ℕ) : (shapePoly lam2 tau).Monic := by
  unfold shapePoly
  exact monic_prod_of_monic _ _ fun a _ => monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _

theorem natDegree_shapePoly_eq {p i q : ℕ} {lam2 tau : Fin q → ℕ} (h : tau ∈ shapesAll p i lam2) :
    (shapePoly lam2 tau).natDegree = i := by
  unfold shapesAll at h
  rw [Finset.mem_filter, Fintype.mem_piFinset] at h
  have hb : ∀ a, lam2 a ≤ tau a := fun a => (Finset.mem_Icc.1 (h.1 a)).1
  have hsum := h.2.2.1
  unfold shapePoly
  rw [natDegree_prod_of_monic _ _ fun a _ => monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
  have : ∀ a : Fin q, (∏ j ∈ Finset.Ico (lam2 a) (tau a), (X - C ((j : ℤ) - (a.val : ℤ)) : ℤ[X])).natDegree =
      tau a - lam2 a := by
    intro a
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _,
      Finset.sum_congr rfl fun j _ => natDegree_X_sub_C _]
    simp
  rw [Finset.sum_congr rfl fun a _ => this a]
  have h2 : ∑ a, (tau a - lam2 a) + ∑ a, lam2 a = ∑ a, tau a := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Nat.sub_add_cancel (hb a)
  omega

theorem shape_coefficient_holds : ShapeCoeff := by
  intro A _ p i q lam2 tau htau
  have hm := shapePoly_monic lam2 tau
  have hd := natDegree_shapePoly_eq htau
  conv_rhs => rw [hm.as_sum, hd]
  rw [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
    Fin.sum_univ_eq_sum_range (fun a => (C (((shapePoly lam2 tau).coeff a : ℤ) : A) * X ^ a : A[X])) i]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C]
  rfl

theorem eval_map_intCast {A : Type} [CommRing A] (f : ℤ[X]) (c : ℤ) :
    (f.map (Int.castRingHom A)).eval (c : A) = ((f.eval c : ℤ) : A) := by
  rw [eval_map, show (c : A) = Int.castRingHom A c from rfl, eval₂_at_apply]
  rfl

theorem shape_divisibility_field_holds : ShapeDvdField := by
  intro O K _ _ _ p w i q lam2 hw
  refine ⟨fun tau htau => ?_, ?_, fun tau htau hn => ?_⟩
  · rw [shape_coefficient_holds K p i q lam2 tau ((mem_shapes_holds p w i q lam2 tau).1 htau).1, Polynomial.map_map,
      Subsingleton.elim ((algebraMap O K).comp (Int.castRingHom O)) (Int.castRingHom K)]
    exact Polynomial.map_dvd _ (shape_divisibility_holds p w i q lam2 hw tau htau).2.2
  · have := eval_map_intCast (A := O) (DnPoly p w i lam2) (w : ℤ)
    rw [polynomial_evaluation_holds] at this
    rw [← this]; simp
  · rw [shape_coefficient_holds K p i q lam2 tau htau]
    have h1 : LD.boxesOfContent lam2 tau (w : ℤ) ≠ 0 := fun h0 => hn ((mem_shapes_holds p w i q lam2 tau).2 ⟨htau, h0⟩)
    have h2 := eval_map_intCast (A := K) (shapePoly lam2 tau) (w : ℤ)
    rw [(shape_eval_zero_holds q lam2 tau w).2 h1] at h2
    simpa using h2

theorem unit_clause_holds : UnitClause := by
  intro O V _ _ _ Del l D η e a v hη hD h
  obtain ⟨u, rfl⟩ := hη
  have h1 : l ^ (e + a) • v = (↑u⁻¹ : O) • ((l ^ e * D) • v) := by
    rw [smul_smul, hD]
    congr 1
    calc l ^ (e + a) = (↑u⁻¹ * ↑u) * (l ^ e * l ^ a) := by rw [Units.inv_mul, one_mul, pow_add]
      _ = _ := by ring
  rw [h1]; exact Del.smul_mem _ h

theorem valuation_unit_holds : ValuationUnit := by
  intro O _ l hl hO D hD
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨m, hm⟩ := (padicValInt_dvd (p := l) D)
  have hnd : ¬ (l : ℤ) ∣ m := by
    rintro ⟨m', rfl⟩
    have h1 : (l : ℤ) ^ (padicValInt l D + 1) ∣ D := ⟨m', by rw [pow_succ, mul_assoc]; exact hm⟩
    rcases (padicValInt_dvd_iff (p := l) _ D).1 h1 with h2 | h2
    · exact hD h2
    · omega
  refine ⟨(m : O), hO m hnd, ?_⟩
  conv_lhs => rw [hm]
  push_cast
  ring

theorem depth_skeleton_second_form_holds : LemmaDSkeleton2 := by
  intro O K V P q _ _ _ _ _ _ _ _ _ _ S B n w lam2 DelL Mt xi lam l e i' H ν hν v hv hvr hvν
  obtain ⟨z, rfl⟩ := hvr
  obtain ⟨hd1, hd2, hd3⟩ := shape_divisibility_field_holds O K (Fintype.card P) w n q lam2 H.le_w
  have h3b : ∀ z : Tens (Fin q) P S.W n, toSym K (AA K S.EW n S.w z) ∈
      ⨆ τ : {τ // τ ∈ LD.shapes (Fintype.card P) w n lam2}, Mt τ.1 := by
    intro z
    have hg := (good_part_holds K (Fin q) P S.W {τ // τ ∈ shapesAll (Fintype.card P) n lam2} S.EW (generators_satisfy_gl_relations S) n
      (fun τ => Mt τ.1) (fun τ a => (((shapePoly lam2 τ.1).coeff a.val : ℤ) : K))
      (fun τ a z hz => H.eigen τ.1 τ.2 a z hz) (by rw [iSup_subtype]; exact H.decomp) S.w
      {τ | τ.1 ∈ LD.shapes (Fintype.card P) w n lam2}
      (fun τ hτ => by rw [H.scalar]; exact hd3 τ.1 τ.2 hτ)).1 z
    refine (iSup₂_le fun τ hτ => ?_ :
      _ ≤ ⨆ τ : {τ // τ ∈ LD.shapes (Fintype.card P) w n lam2}, Mt τ.1) hg
    exact le_iSup (fun τ : {τ // τ ∈ LD.shapes (Fintype.card P) w n lam2} => Mt τ.1) ⟨τ.1, hτ⟩
  have hmain : (l ^ e * ((LD.Dn (Fintype.card P) w n lam2 : ℤ) : O)) • S.mu n z ∈ S.DeltaN n DelL := by
    have := lemma_d_skeleton_holds O K V P (Fin q) {τ // τ ∈ LD.shapes (Fintype.card P) w n lam2} S n (w : O)
      (NablaL S B DelL) DelL (fun τ => Mt τ.1) (fun τ a => (((shapePoly lam2 τ.1).coeff a.val : ℤ) : K))
      ((DnPoly (Fintype.card P) w n lam2).map (Int.castRingHom O)) xi lam l e i'
      (by rw [H.scalar, map_natCast])
      (dual_stable_holds O K V P (Fin q) S B DelL H.contra H.stable)
      (iota_injective_holds K V P (Fin q) S B H.contra H.generated H.nondeg n)
      (fun τ a z hz => H.eigen τ.1 ((mem_shapes_holds (Fintype.card P) w n q lam2 τ.1).1 τ.2).1 a z hz)
      (fun τ => hd1 τ.1 τ.2) h3b H.dominant H.expL ν hν z hvν
      ((nabla_criterion_holds O K V P (Fin q) S B DelL H.contra n z).1 hv)
    rwa [hd2] at this
  exact ⟨hmain, fun a η hη hD => unit_clause_holds O V _ l _ η e a _ hη hD hmain⟩

theorem depth_skeleton_valuation_holds : LemmaDSkeleton2Val := by
  intro O K V P q _ _ _ _ _ _ _ _ _ _ S B n w lam2 DelL Mt xi lam l e i' hl hO H ν hν v hv hvr hvν
  obtain ⟨η, hη, hD⟩ := valuation_unit_holds O l hl hO _ (LD.d_n_ne_zero (Fintype.card P) w n q lam2)
  exact (depth_skeleton_second_form_holds O K V P q S B n w lam2 DelL Mt xi lam (l : O) e i' H ν hν v hv hvr hvν).2 _ η hη hD

theorem mem_eigen_piece_of_mem_iSup {O K V : Type*} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (f : Module.End K V) (μ : ℕ → K) (hμ : Function.Injective μ) (N : ℕ → Submodule O V)
    (hN : ∀ n', ∀ x ∈ N n', x ∈ f.eigenspace (μ n')) (n : ℕ) (x : V) (hx : x ∈ ⨆ n', N n')
    (hxe : x ∈ f.eigenspace (μ n)) : x ∈ N n := by
  have key : ∃ a ∈ N n, x - a ∈ ⨆ j ≠ μ n, f.eigenspace j := by
    refine Submodule.iSup_induction N (motive := fun x => ∃ a ∈ N n, x - a ∈ ⨆ j ≠ μ n, f.eigenspace j) hx ?_ ?_ ?_
    · intro n' x hx'
      by_cases h : n' = n
      · subst h; exact ⟨x, hx', by rw [sub_self]; exact Submodule.zero_mem _⟩
      · refine ⟨0, Submodule.zero_mem _, ?_⟩
        rw [sub_zero]
        exact Submodule.mem_iSup_of_mem (μ n') (Submodule.mem_iSup_of_mem (fun he => h (hμ he)) (hN n' x hx'))
    · exact ⟨0, Submodule.zero_mem _, by rw [sub_zero]; exact Submodule.zero_mem _⟩
    · rintro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
      exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [add_sub_add_comm]; exact Submodule.add_mem _ hxa hyb⟩
  obtain ⟨a, ha, hxa⟩ := key
  have h0 : x - a = 0 :=
    (Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep f (μ n))) _ (Submodule.sub_mem _ hxe (hN n a ha)) hxa
  rw [sub_eq_zero.1 h0]; exact ha

theorem natCast_sub_injective {k : Type*} [Field k] [CharZero k] (c : k) : Function.Injective (fun n : ℕ => c - (n : k)) := by
  intro a b h
  have : (a : k) = b := by linear_combination -h
  exact_mod_cast this

theorem range_symMap_le_eigenspace {k V P R : Type} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (n : ℕ) (x : V) (hx : x ∈ LinearMap.range (S.mu n)) :
    x ∈ (∑ α : P, S.E (Sum.inl α) (Sum.inl α)).eigenspace ((Fintype.card P : k) * S.w - (n : k)) := by
  obtain ⟨z, rfl⟩ := hx
  rw [Module.End.mem_eigenspace_iff]
  exact depth_eigen_holds k V P R S n z

theorem depth_of_weight_holds : DepthOfWeight := by
  intro k V P R _ _ _ _ _ _ _ _ S w n hw hgen ν v hv hsum
  have htop := (depth_span_holds k V P R S).2.2.2.2.2.2 hgen
  refine mem_eigen_piece_of_mem_iSup (O := k) (∑ α : P, S.E (Sum.inl α) (Sum.inl α)) (fun n' : ℕ => (Fintype.card P : k) * S.w - (n' : k))
    (natCast_sub_injective _) (fun n' => LinearMap.range (S.mu n')) (fun n' x hx => range_symMap_le_eigenspace S n' x hx) n v
    (by rw [htop]; trivial) ?_
  rw [Module.End.mem_eigenspace_iff, LinearMap.sum_apply,
    Finset.sum_congr rfl fun α _ => (mem_weightSpace_iff_alt S ν v).1 hv (Sum.inl α), ← Finset.sum_smul]
  congr 1
  rw [hw]
  have := congrArg (Int.cast : ℤ → k) hsum
  push_cast at this
  linear_combination this

theorem depth_skeleton_literal_holds : LemmaDSkeleton2Lit := by
  intro O K V P q _ _ _ _ _ _ _ _ _ _ S B n w lam2 DelL Mt xi lam l e i' hl hO H ν hsum hν v hv hvν
  have hr := depth_of_weight_holds K V P (Fin q) S w n H.scalar H.generated ν v hvν hsum
  have h := depth_skeleton_valuation_holds O K V P q S B n w lam2 DelL Mt xi lam l e i' hl hO H ν hν v hv hr hvν
  exact ⟨Submodule.mem_iSup_of_mem n h, by rw [← algebraMap_smul K]; exact (S.wt ν).smul_mem _ hvν⟩

theorem depthPart_eq_sum_positionGenerators {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P]
    (EM : R → R → Module.End k M) (n j : ℕ) (hj : j ≤ n) (b b' : R) :
    (Dpart k EM j b b' : Module.End k (Tens R P M n)) = ∑ i ∈ Finset.range (j + 1), factorGenerator k EM n i b b' := by
  rw [Finset.sum_range_succ', Dpart, add_comm]
  refine congrArg₂ (· + ·) ?_ rfl
  refine Finset.sum_nbij (fun s => s.val) ?_ ?_ ?_ ?_
  · intro a ha; exact Finset.mem_range.2 (Finset.mem_filter.1 ha).2
  · intro a _ b _ hab; exact Fin.ext hab
  · intro a ha
    have ha' : a < j := by simpa using ha
    exact ⟨⟨a, by omega⟩, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha'⟩), rfl⟩
  · intro a _; simp only [factorGenerator, dif_pos a.2, Fin.eta]

theorem casimir_jucys_murphy_holds : CasimirJM := by
  intro k R P M _ _ _ _ _ _ EM n j
  have h := casimir_recursion_holds (Module.End k (Tens R P M n)) R (factorGenerator k EM n)
    (fun i j hij a b c d => factorGenerator_commute_of_ne k EM i j hij a b c d) (j.val + 1)
  unfold Cas
  simp only [depthPart_eq_sum_positionGenerators EM n (j.val + 1) j.2, depthPart_eq_sum_positionGenerators EM n j.val j.2.le]
  rw [h, ← jucysMurphy_eq_sum_position_products]
  congr 1
  simp only [factorGenerator, dif_pos j.2, Fin.eta]
  exact casimir_on_tensor_holds k R P M n j

theorem coeff_list_prod_X_sub_C_apply_eigen {K Y : Type*} [CommRing K] [AddCommGroup Y] [Module K Y] (z : Y) :
    ∀ (n : ℕ) (x : Fin n → Module.End K Y) (c : Fin n → ℤ), (∀ j, x j z = (c j : K) • z) → ∀ a,
    (List.ofFn fun j => (X - C (x j) : (Module.End K Y)[X])).prod.coeff a z =
      (((List.ofFn fun j => (X - C (c j) : ℤ[X])).prod.coeff a : ℤ) : K) • z := by
  intro n
  induction n with
  | zero =>
    intro x c _ a
    rw [List.ofFn_zero, List.ofFn_zero, List.prod_nil, List.prod_nil, coeff_one, coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    intro x c h a
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    have ih' := ih (fun j => x j.succ) (fun j => c j.succ) (fun j => h j.succ)
    rcases a with _ | a
    · rw [coeff_zero_X_sub_C_mul_alt, coeff_zero_X_sub_C_mul_alt, LinearMap.neg_apply, Module.End.mul_apply, ih' 0, map_smul, h 0, smul_smul]
      push_cast
      rw [neg_smul, mul_comm]
    · rw [coeff_succ_X_sub_C_mul_alt, coeff_succ_X_sub_C_mul_alt, LinearMap.sub_apply, Module.End.mul_apply, ih' a, ih' (a + 1), map_smul, h 0,
        smul_smul]
      push_cast
      rw [sub_smul, mul_comm]

theorem path_eigen_holds : PathEigen := by
  intro K P M q _ _ _ _ _ EM n κ ρ hstep z hz
  have hx : ∀ j : Fin n, xJM K EM j z = (((κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ) : ℤ) : K) • z := by
    intro j
    have h1 := congrArg (fun T : Module.End K (Tens (Fin q) P M n) => T z) (casimir_jucys_murphy_holds K (Fin q) P M EM n j)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Fintype.card_fin] at h1
    rw [hz (j.val + 1) j.2, hz j.val j.2.le, hstep j, ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h1
    have h2 := casimir_content_holds q (fun b => (κ j.val b : ℤ)) (ρ j)
    have h3 : casVal (κ j.val + Pi.single (ρ j) 1) - casVal (κ j.val) - (q : ℤ) =
        2 * ((κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ)) := by
      unfold casVal
      simp only [Pi.add_apply, Pi.single_apply, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact h2
    have e2 : ((casVal (κ j.val + Pi.single (ρ j) 1) : ℤ) : K) - ((casVal (κ j.val) : ℤ) : K) - (q : K) =
        2 * (((κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ) : ℤ) : K) := by
      have := congrArg (Int.cast : ℤ → K) h3
      push_cast at this ⊢
      exact this
    have e1 : ((2 : ℕ) : K) • xJM K EM j z = (((casVal (κ j.val + Pi.single (ρ j) 1) : ℤ) : K) -
        ((casVal (κ j.val) : ℤ) : K) - (q : K)) • z := by
      rw [sub_smul, sub_smul, h1, add_sub_cancel_right]
    rw [e2, mul_smul, Nat.cast_two] at e1
    exact smul_right_injective _ (two_ne_zero (α := K)) e1
  refine ⟨hx, fun a => ?_⟩
  have := coeff_list_prod_X_sub_C_apply_eigen z n (fun j => xJM K EM j) (fun j => (κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ)) hx a
  rw [List.prod_ofFn] at this
  exact this

theorem shapePoly_add_single {q : ℕ} (l t : Fin q → ℕ) (r : Fin q) (h : l r ≤ t r) :
    shapePoly l (t + Pi.single r 1) = (X - C ((t r : ℤ) - (r.val : ℤ))) * shapePoly l t := by
  have L : shapePoly l (t + Pi.single r 1) =
      (∏ j ∈ Finset.Ico (l r) ((t + Pi.single r 1 : Fin q → ℕ) r), (X - C ((j : ℤ) - (r.val : ℤ)) : ℤ[X])) *
        ∏ a ∈ Finset.univ.erase r, ∏ j ∈ Finset.Ico (l a) ((t + Pi.single r 1 : Fin q → ℕ) a), (X - C ((j : ℤ) - (a.val : ℤ))) :=
    (Finset.mul_prod_erase Finset.univ (fun a => ∏ j ∈ Finset.Ico (l a) ((t + Pi.single r 1 : Fin q → ℕ) a),
      (X - C ((j : ℤ) - (a.val : ℤ)) : ℤ[X])) (Finset.mem_univ r)).symm
  have Rr : shapePoly l t =
      (∏ j ∈ Finset.Ico (l r) (t r), (X - C ((j : ℤ) - (r.val : ℤ)) : ℤ[X])) *
        ∏ a ∈ Finset.univ.erase r, ∏ j ∈ Finset.Ico (l a) (t a), (X - C ((j : ℤ) - (a.val : ℤ))) :=
    (Finset.mul_prod_erase Finset.univ (fun a => ∏ j ∈ Finset.Ico (l a) (t a),
      (X - C ((j : ℤ) - (a.val : ℤ)) : ℤ[X])) (Finset.mem_univ r)).symm
  have e1 : ∏ j ∈ Finset.Ico (l r) ((t + Pi.single r 1 : Fin q → ℕ) r), (X - C ((j : ℤ) - (r.val : ℤ)) : ℤ[X]) =
      (∏ j ∈ Finset.Ico (l r) (t r), (X - C ((j : ℤ) - (r.val : ℤ)))) * (X - C ((t r : ℤ) - (r.val : ℤ))) := by
    rw [Pi.add_apply, Pi.single_eq_same, Finset.prod_Ico_succ_top h]
  have e2 : ∏ a ∈ Finset.univ.erase r, ∏ j ∈ Finset.Ico (l a) ((t + Pi.single r 1 : Fin q → ℕ) a),
        (X - C ((j : ℤ) - (a.val : ℤ)) : ℤ[X]) =
      ∏ a ∈ Finset.univ.erase r, ∏ j ∈ Finset.Ico (l a) (t a), (X - C ((j : ℤ) - (a.val : ℤ))) := by
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase ha), add_zero]
  rw [L, Rr, e1, e2]; ring

theorem path_bounds_and_shapePoly {q n : ℕ} (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q)
    (hstep : ∀ j : Fin n, κ (j.val + 1) = κ j.val + Pi.single (ρ j) 1) :
    ∀ m ≤ n, (∀ b, κ 0 b ≤ κ m b ∧ κ m b ≤ κ 0 b + m) ∧ ∑ b, κ m b = ∑ b, κ 0 b + m ∧
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < m), (X - C ((κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ)) : ℤ[X]) =
        shapePoly (κ 0) (κ m) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun b => ⟨le_rfl, le_rfl⟩, rfl, ?_⟩
    simp [shapePoly]
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hs : κ (m + 1) = κ m + Pi.single (ρ ⟨m, hm⟩) 1 := hstep ⟨m, hm⟩
    have hb : ∀ b, κ (m + 1) b = κ m b + if b = ρ ⟨m, hm⟩ then 1 else 0 := by
      intro b; rw [hs, Pi.add_apply, Pi.single_apply]
    refine ⟨fun b => ?_, ?_, ?_⟩
    · have := h1 b
      rw [hb b]
      split_ifs <;> omega
    · simp only [hb, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      omega
    · have hf : Finset.univ.filter (fun j : Fin n => j.val < m + 1) =
          insert (⟨m, hm⟩ : Fin n) (Finset.univ.filter (fun j : Fin n => j.val < m)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hf, Finset.prod_insert (by simp), h3, hs, shapePoly_add_single _ _ _ (h1 _).1]

theorem path_shape_holds : PathShape := by
  intro q n lam2 tau κ ρ H
  obtain ⟨h0, hstep, hn, -⟩ := H
  subst h0
  subst hn
  obtain ⟨h1, h2, h3⟩ := path_bounds_and_shapePoly κ ρ hstep n le_rfl
  refine ⟨?_, h1, h2⟩
  rw [← h3, Finset.filter_true_of_mem fun j _ => j.2]
  rfl

theorem path_space_eigen_holds : PathSpaceEigen := by
  intro K P M q _ _ _ _ _ _ EM hEM n lam2 tau a z hz
  obtain ⟨z', hz', he⟩ := hz
  obtain ⟨c, hc1, -, -, -⟩ := coefficient_operators_hold K K (Fin q) P M EM hEM n
  have hle : PathSpace K EM n lam2 tau ≤ LinearMap.ker ((AApoly K EM n).coeff a.val -
      (((shapePoly lam2 tau).coeff a.val : ℤ) : K) • (1 : Module.End K (Tens (Fin q) P M n))) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨κ, ρ, hp, hx⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero,
      (path_eigen_holds K P M q EM n κ ρ hp.step x hx).2 a.val, (path_shape_holds q n lam2 tau κ ρ hp).1]
  have h1 := hle hz'
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h1
  rw [← hc1, ← he, hc1, h1, map_smul]

theorem path_decomposition_holds : PathDecomp := by
  intro K P M q _ _ _ _ _ EM n p lam2 htop hcol
  rw [eq_top_iff]
  have h1 : (⊤ : Submodule K (Sym (Fin q × P) n → M)) =
      ⨆ tau, (PathSpace K (P := P) EM n lam2 tau).map (toSym K) := by
    rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top.2 (toSym_surjective (k := K))]
  rw [h1]
  refine iSup_le fun tau => ?_
  by_cases hc : ∃ b : Fin q, ∃ j < tau b, p < LD.colLen lam2 tau j
  · rintro _ ⟨z, hz, rfl⟩
    rw [hcol tau hc z hz]; exact Submodule.zero_mem _
  · by_cases hp : ∃ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ
    · obtain ⟨κ, ρ, hp⟩ := hp
      have hmem : tau ∈ shapesAll p n lam2 := by
        obtain ⟨-, hb, hs⟩ := path_shape_holds q n lam2 tau κ ρ hp
        unfold shapesAll
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun a => Finset.mem_Icc.2 (hb a), fun a b hab => ?_, hs, fun b j hj => ?_⟩
        · have := hp.dom n le_rfl
          rw [hp.stop] at this
          exact this hab
        · by_contra hlt
          exact hc ⟨b, j, hj, not_le.1 hlt⟩
      exact le_iSup₂_of_le (f := fun tau (_ : tau ∈ shapesAll p n lam2) =>
        (PathSpace K (P := P) EM n lam2 tau).map (toSym K)) tau hmem le_rfl
    · have h0 : PathSpace K (P := P) EM n lam2 tau = ⊥ := by
        unfold PathSpace
        rw [Submodule.span_eq_bot]
        rintro x ⟨κ, ρ, h, -⟩
        exact absurd ⟨κ, ρ, h⟩ hp
      rw [h0, Submodule.map_bot]; exact bot_le

theorem inputs_from_pieri_holds : InputsFromPieri := by
  intro O K V P q _ _ _ _ _ _ _ _ _ _ S B n w lam2 DelL xi lam l e i' H
  exact ⟨H.scalar, H.le_w, H.contra, H.generated, H.nondeg, H.stable,
    fun τ _ a z hz => path_space_eigen_holds K P S.W q S.EW (generators_satisfy_gl_relations S) n lam2 τ a z hz,
    path_decomposition_holds K P S.W q S.EW n _ lam2 H.pieri H.columns, H.dominant, H.expL⟩

theorem depth_skeleton_third_form_holds : LemmaDSkeleton3 := by
  intro O K V P q _ _ _ _ _ _ _ _ _ _ S B n w lam2 DelL xi lam l e i' hl hO H
  exact depth_skeleton_literal_holds O K V P q S B n w lam2 DelL _ xi lam l e i' hl hO
    (inputs_from_pieri_holds O K V P q S B n w lam2 DelL xi lam (l : O) e i' H)

def glOperatorOnSequences (K : Type) [Field K] (y d : ℕ) : Unit ⊕ Fin 1 → Unit ⊕ Fin 1 → Module.End K (ℕ → K)
  | Sum.inl _, Sum.inl _ => LinearMap.pi fun j => (((y + d : ℕ) : K) - j) • LinearMap.proj j
  | Sum.inl _, Sum.inr _ => LinearMap.pi fun j => ((j : K) + 1) • LinearMap.proj (j + 1)
  | Sum.inr _, Sum.inl _ => LinearMap.pi fun j =>
      match j with
      | 0 => 0
      | i + 1 => ((d : K) - i) • LinearMap.proj i
  | Sum.inr _, Sum.inr _ => LinearMap.pi fun j => ((y : K) + j) • LinearMap.proj j

section Inst

variable (K : Type) [Field K] (y d : ℕ)

theorem glOperator_diag_first_apply (a b : Unit) (x : ℕ → K) (j : ℕ) :
    glOperatorOnSequences K y d (Sum.inl a) (Sum.inl b) x j = (((y + d : ℕ) : K) - j) * x j := rfl

theorem glOperator_raising_apply (a : Unit) (b : Fin 1) (x : ℕ → K) (j : ℕ) :
    glOperatorOnSequences K y d (Sum.inl a) (Sum.inr b) x j = ((j : K) + 1) * x (j + 1) := rfl

theorem glOperator_lowering_zero (a : Fin 1) (b : Unit) (x : ℕ → K) : glOperatorOnSequences K y d (Sum.inr a) (Sum.inl b) x 0 = 0 := rfl

theorem glOperator_lowering_apply (a : Fin 1) (b : Unit) (x : ℕ → K) (j : ℕ) :
    glOperatorOnSequences K y d (Sum.inr a) (Sum.inl b) x (j + 1) = ((d : K) - j) * x j := rfl

theorem glOperator_diag_second_apply (a b : Fin 1) (x : ℕ → K) (j : ℕ) :
    glOperatorOnSequences K y d (Sum.inr a) (Sum.inr b) x j = ((y : K) + j) * x j := rfl

theorem glOperator_commutator (a b c e : Unit ⊕ Fin 1) :
    glOperatorOnSequences K y d a b * glOperatorOnSequences K y d c e - glOperatorOnSequences K y d c e * glOperatorOnSequences K y d a b =
      (if b = c then glOperatorOnSequences K y d a e else 0) - (if e = a then glOperatorOnSequences K y d c b else 0) := by
  refine LinearMap.ext fun x => funext fun j => ?_
  have key : ∀ a : Unit ⊕ Fin 1, a = Sum.inl () ∨ a = Sum.inr 0 := by
    rintro (a | a)
    · exact Or.inl rfl
    · exact Or.inr (congrArg Sum.inr (Subsingleton.elim _ _))
  rcases key a with rfl | rfl <;> rcases key b with rfl | rfl <;> rcases key c with rfl | rfl <;>
    rcases key e with rfl | rfl <;> rcases j with _ | j <;>
    simp [glOperator_diag_first_apply, glOperator_raising_apply, glOperator_lowering_zero, glOperator_lowering_apply, glOperator_diag_second_apply] <;> ring

def binaryFormCoords : Submodule K (ℕ → K) where
  carrier := {x | ∀ j, d < j → x j = 0}
  add_mem' := by
    intro a b ha hb j hj
    rw [Pi.add_apply, ha j hj, hb j hj, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c a ha j hj
    rw [Pi.smul_apply, ha j hj, smul_zero]

theorem glOperator_preserves_binaryFormCoords (a b : Unit ⊕ Fin 1) : ∀ x ∈ binaryFormCoords K d, glOperatorOnSequences K y d a b x ∈ binaryFormCoords K d := by
  intro x hx j hj
  rcases a with a | a <;> rcases b with b | b
  · rw [glOperator_diag_first_apply, hx j hj, mul_zero]
  · rw [glOperator_raising_apply, hx (j + 1) (by omega), mul_zero]
  · rcases j with _ | j
    · rfl
    · rw [glOperator_lowering_apply]
      rcases Nat.lt_or_ge d j with h | h
      · rw [hx j h, mul_zero]
      · rw [show j = d by omega, sub_self, zero_mul]
  · rw [glOperator_diag_second_apply, hx j hj, mul_zero]

def binaryFormsSetting : HidaSetting K (binaryFormCoords K d) Unit (Fin 1) where
  E a b := (glOperatorOnSequences K y d a b).restrict (glOperator_preserves_binaryFormCoords K y d a b)
  comm a b c e := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have h := congrArg (fun T : Module.End K (ℕ → K) => T x.1) (glOperator_commutator K y d a b c e)
    by_cases h1 : b = c <;> by_cases h2 : e = a <;> simpa [h1, h2] using h
  W := (binaryFormCoords K 0).comap (binaryFormCoords K d).subtype
  w := ((y + d : ℕ) : K)
  kill α a u hu := by
    refine Subtype.ext (funext fun j => ?_)
    change glOperatorOnSequences K y d (Sum.inl α) (Sum.inr a) u.1 j = 0
    rw [glOperator_raising_apply, show u.1 (j + 1) = 0 from hu (j + 1) (by omega), mul_zero]
  scal α β u hu := by
    rw [if_pos (Subsingleton.elim α β)]
    refine Subtype.ext (funext fun j => ?_)
    change glOperatorOnSequences K y d (Sum.inl α) (Sum.inl β) u.1 j = ((y + d : ℕ) : K) * u.1 j
    rw [glOperator_diag_first_apply]
    rcases j with _ | j
    · simp
    · rw [show u.1 (j + 1) = 0 from hu (j + 1) (by omega), mul_zero, mul_zero]
  stab b b' u hu := by
    intro j hj
    change glOperatorOnSequences K y d (Sum.inr b) (Sum.inr b') u.1 j = 0
    rw [glOperator_diag_second_apply, show u.1 j = 0 from hu j hj, mul_zero]

end Inst

section Inst2

variable (K : Type) [Field K] [CharZero K] (y d : ℕ)

def binaryFormMonomial (j : ℕ) : binaryFormCoords K d :=
  ⟨fun i => if i = j ∧ j ≤ d then 1 else 0, by
    intro i hi
    change (if i = j ∧ j ≤ d then (1 : K) else 0) = 0
    rw [if_neg]; omega⟩

theorem binaryFormMonomial_apply (j i : ℕ) : (binaryFormMonomial K d j).1 i = if i = j ∧ j ≤ d then 1 else 0 := rfl

def inverseBinomialCoeff (j : ℕ) : K := ∏ i ∈ Finset.range j, ((i : K) + 1) / ((d : K) - i)

def binaryFormPairing : LinearMap.BilinForm K (binaryFormCoords K d) :=
  ∑ j ∈ Finset.range (d + 1), inverseBinomialCoeff K d j • LinearMap.BilinForm.linMulLin
    (LinearMap.proj j ∘ₗ (binaryFormCoords K d).subtype) (LinearMap.proj j ∘ₗ (binaryFormCoords K d).subtype)

theorem monomial_zero_mem_highestWeight_space : binaryFormMonomial K d 0 ∈ (binaryFormsSetting K y d).W := by
  intro i hi
  change (binaryFormMonomial K d 0).1 i = 0
  rw [binaryFormMonomial_apply, if_neg (by omega)]

end Inst2

section Inst3

variable (K : Type) [Field K] [CharZero K] (y d : ℕ)

def highestWeightVector : (binaryFormsSetting K y d).W := ⟨binaryFormMonomial K d 0, monomial_zero_mem_highestWeight_space K y d⟩

def singletonWord : Fin 1 → Fin 1 × Unit := fun _ => (0, ())

end Inst3

section Inst4

variable (K : Type) [Field K] [CharZero K] (y d : ℕ)

def binaryForms_grading : (Unit ⊕ Fin 1 → ℤ) →+ ℤ := Pi.evalAddMonoidHom (fun _ => ℤ) (Sum.inl ())

def binaryForms_highestWeight : Unit ⊕ Fin 1 → ℤ := Sum.elim (fun _ => (y : ℤ) + d) (fun _ => (y : ℤ))

def binaryForms_firstDepthWeight : Unit ⊕ Fin 1 → ℤ := Sum.elim (fun _ => (y : ℤ) + d - 1) (fun _ => (y : ℤ) + 1)

variable (O : Type) [CommRing O] [Algebra O K]

end Inst4

end Formalism.CohomologicalDescent.BinaryFormsExample
