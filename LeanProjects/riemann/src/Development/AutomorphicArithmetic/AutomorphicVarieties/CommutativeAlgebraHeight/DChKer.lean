import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

private theorem chk_div (x : E) (p : A[X]) : ∃ Q : A[X] ⊗[A] E,
    p ⊗ₜ[A] (1 : E) - 1 ⊗ₜ aeval x p = Q * (X ⊗ₜ 1 - 1 ⊗ₜ x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Q, hQ⟩ := hp
    obtain ⟨R, hR⟩ := hq
    refine ⟨Q + R, ?_⟩
    rw [add_mul, ← hQ, ← hR, map_add, add_tmul, tmul_add]
    abel
  | monomial k a =>
    have hc : Commute ((X : A[X]) ⊗ₜ[A] (1 : E)) (1 ⊗ₜ x) := by
      simp [Commute, SemiconjBy]
    obtain ⟨G, h⟩ : ∃ G, G * _ = _ := ⟨_, hc.geom_sum₂_mul k⟩
    refine ⟨a • G, ?_⟩
    · rw [smul_mul_assoc, h, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow, one_pow,
        smul_sub, aeval_monomial, ← Algebra.smul_def, tmul_smul, ← smul_X_eq_monomial, ← smul_tmul']

private theorem chk_chi (x y : E) : D.chi (x - y * aeval x (D.chi x)) = D.chi x := by
  nontriviality A
  obtain ⟨h0, -, -, -, hm, -, -⟩ := d_chi D x
  obtain ⟨-, -, -, -, hm', hd', -⟩ := d_chi D (x - y * aeval x (D.chi x))
  have hn : n ≤ (D.chi x).natDegree := by
    apply le_natDegree_of_ne_zero
    have : (D.chi x).coeff n = 1 := by simpa [Det.lam] using h0
    rw [this]; exact one_ne_zero
  refine eq_of_monic_of_dvd_of_natDegree_le hm hm' ?_ (hd'.trans hn)
  obtain ⟨Q, hQ⟩ := chk_div x (D.chi x)
  let π := Ideal.Quotient.mkₐ A (Ideal.span {D.chi x})
  have hπ : π (D.chi x) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have e : ((X : A[X]) ⊗ₜ[A] (1 : E) - 1 ⊗ₜ (x - y * aeval x (D.chi x))) =
      (1 - (1 ⊗ₜ y) * Q) * (X ⊗ₜ 1 - 1 ⊗ₜ x) + D.chi x ⊗ₜ y := by
    rw [sub_mul, mul_assoc, ← hQ, one_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, mul_one, tmul_sub]
    abel
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change π (D.D A[X] _) = 0
  rw [e, ← D.nat, map_add, Algebra.TensorProduct.map_tmul, hπ, zero_tmul, add_zero, D.nat, map_mul, map_mul]
  change _ * π (D.chi x) = 0
  rw [hπ, mul_zero]

private theorem chk_eval (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E) :
    (D.chiS S y).eval s = D.D S (s ⊗ₜ 1 - y) := by
  let ev : S[X] →ₐ[A] S := (Polynomial.aeval (R := S) s).restrictScalars A
  have h := D.nat S[X] S ev (X ⊗ₜ 1 -
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) y)
  have hev : Algebra.TensorProduct.map ev (AlgHom.id A E)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) y) = y := by
    clear h
    induction y with
    | zero => simp
    | tmul b z => simp [ev]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [map_sub, hev] at h
  simpa [ev, Det.chiS, coe_aeval_eq_eval] using h.symm

private theorem chk_val (x h : E) : D.val (1 + h * aeval x (D.chi x)) = 1 := by
  obtain ⟨-, -, h3, h4⟩ := d_bc D A[X]
  have h1 := chk_chi (D.baseChange A[X]) (1 ⊗ₜ x) ((X ⊗ₜ 1 - 1 ⊗ₜ x) * (1 ⊗ₜ h))
  have h2 : aeval ((1 : A[X]) ⊗ₜ[A] x) ((D.baseChange A[X]).chi (1 ⊗ₜ x)) = 1 ⊗ₜ aeval x (D.chi x) := by
    rw [(h4 x).1, aeval_map_algebraMap]
    exact aeval_algHom_apply (Algebra.TensorProduct.includeRight : E →ₐ[A] A[X] ⊗[A] E) x _
  rw [h2, h3, h3] at h1
  have h5 := congrArg (eval X) h1
  rw [chk_eval, chk_eval] at h5
  have e : ((X : A[X]) ⊗ₜ[A] (1 : E) - (1 ⊗ₜ x - (X ⊗ₜ 1 - 1 ⊗ₜ x) * (1 ⊗ₜ h) * 1 ⊗ₜ aeval x (D.chi x))) =
      (X ⊗ₜ 1 - 1 ⊗ₜ x) * (1 ⊗ₜ (1 + h * aeval x (D.chi x))) := by
    rw [tmul_add, ← Algebra.TensorProduct.one_def, mul_add, mul_one, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
    abel
  rw [e, map_mul] at h5
  have hm : (D.chi x).Monic := (d_chi D x).2.2.2.2.1
  have h6 : D.D A[X] (1 ⊗ₜ (1 + h * aeval x (D.chi x))) = 1 :=
    hm.isRegular.left (h5.trans (mul_one _).symm)
  have h7 := D.nat A[X] A (aeval (0 : A)) (1 ⊗ₜ (1 + h * aeval x (D.chi x)))
  rw [h6, map_one, Algebra.TensorProduct.map_tmul, map_one] at h7
  exact h7

private theorem chk_chiS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y) = (D.chiS S y).map (f : S →+* T) := by
  have h := D.nat (Polynomial S) (Polynomial T) (Polynomial.mapAlgHom f) (Polynomial.X ⊗ₜ 1 -
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y)
  refine Eq.trans ?_ h
  unfold Det.chiS
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y with
    | zero => simp
    | tmul s x => simp
    | add a b ha hb => simp only [map_add, ha, hb]

private theorem chk_F_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    Polynomial.aeval (Algebra.TensorProduct.map f (AlgHom.id A E) y)
      (D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y)) =
      Algebra.TensorProduct.map f (AlgHom.id A E) (Polynomial.aeval y (D.chiS S y)) := by
  rw [chk_chiS_map]
  generalize D.chiS S y = p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial k a =>
    simp [Polynomial.aeval_monomial, Algebra.TensorProduct.algebraMap_apply]

private def chkK (B : Type) [CommRing B] [Algebra A B] (w : B ⊗[A] E) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra A S] (f : B →ₐ[A] S) (h : S ⊗[A] E),
    D.D S (1 + h * Algebra.TensorProduct.map f (AlgHom.id A E) w) = 1

private theorem chk_comp {B S T : Type} [CommRing B] [Algebra A B] [CommRing S] [Algebra A S] [CommRing T]
    [Algebra A T] (f : B →ₐ[A] S) (g : S →ₐ[A] T) (w : B ⊗[A] E) :
    Algebra.TensorProduct.map g (AlgHom.id A E) (Algebra.TensorProduct.map f (AlgHom.id A E) w) =
      Algebra.TensorProduct.map (g.comp f) (AlgHom.id A E) w := by
  induction w with
  | zero => simp
  | tmul s x => simp
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem chkK_ch (B : Type) [CommRing B] [Algebra A B] (y : B ⊗[A] E) :
    chkK D B (aeval y (D.chiS B y)) := by
  intro S _ _ f h
  obtain ⟨-, h2, h3, -⟩ := d_bc D S
  rw [← chk_F_map, ← h2, ← h3]
  exact chk_val _ _ _

private theorem chkK_map {B T : Type} [CommRing B] [Algebra A B] [CommRing T] [Algebra A T] (g : B →ₐ[A] T)
    {w : B ⊗[A] E} (hw : chkK D B w) : chkK D T (Algebra.TensorProduct.map g (AlgHom.id A E) w) := by
  intro S _ _ f h
  rw [chk_comp]
  exact hw S _ h

private theorem chkK_sat {w : A[X] ⊗[A] E} (hw : chkK D A[X] (((X : A[X]) ⊗ₜ[A] (1 : E)) * w)) :
    chkK D A[X] w := by
  intro S _ _ f h
  let L := Localization.Away (X : S[X])
  let i : S[X] →ₐ[A] L := IsScalarTower.toAlgHom A S[X] L
  have hi : Function.Injective i :=
    IsLocalization.injective L ((Submonoid.powers_le (P := nonZeroDivisors S[X])).2 X_mem_nonzeroDivisors)
  let g : A[X] →ₐ[A] S[X] := mapAlgHom (Algebra.ofId A S)
  let c : S →ₐ[A] S[X] := IsScalarTower.toAlgHom A S S[X]
  let ev : S[X] →ₐ[A] S := (aeval (R := S) (f X)).restrictScalars A
  have h1 : ev.comp g = f := by
    apply Polynomial.algHom_ext
    simp [ev, g]
  have h2 : ev.comp c = AlgHom.id A S := by
    ext s
    simp [ev, c]
  have h3 := hw L (i.comp g) (Algebra.TensorProduct.map (i.comp c) (AlgHom.id A E) h *
    (IsLocalization.Away.invSelf (X : S[X]) ⊗ₜ 1))
  have h4 : IsLocalization.Away.invSelf (X : S[X]) * (i.comp g) X = 1 := by
    rw [mul_comm]
    simpa [i, g] using IsLocalization.Away.mul_invSelf (S := L) (X : S[X])
  rw [map_mul, Algebra.TensorProduct.map_tmul, mul_assoc, ← mul_assoc (_ ⊗ₜ _),
    Algebra.TensorProduct.tmul_mul_tmul, h4, map_one, mul_one, ← Algebra.TensorProduct.one_def, one_mul,
    ← chk_comp, ← chk_comp, ← map_mul, ← map_one (Algebra.TensorProduct.map i (AlgHom.id A E)), ← map_add,
    D.nat, ← map_one i] at h3
  have h5 := congrArg ev (hi h3)
  rw [← D.nat, map_add, map_one, map_mul, chk_comp, chk_comp, h1, h2, map_one] at h5
  simpa using h5

private theorem chkK_coef (M : ℕ) : ∀ z : ℕ → E,
    chkK D A[X] (∑ k ∈ Finset.range M, ((X : A[X]) ^ k) ⊗ₜ[A] z k) → ∀ k < M, z k ∈ D.ker := by
  induction M with
  | zero => intro z _ k hk; omega
  | succ M ih =>
    intro z hz
    rw [Finset.sum_range_succ'] at hz
    have h0 : z 0 ∈ D.ker := by
      refine (d_ker D _).1.2 fun S _ _ h => ?_
      have := hz S (aeval 0) h
      simpa [map_sum] using this
    have h1 : chkK D A[X] (∑ k ∈ Finset.range M, ((X : A[X]) ^ k) ⊗ₜ[A] z (k + 1)) := by
      apply chkK_sat
      intro S _ _ f h
      have := hz S f h
      rw [map_add (Algebra.TensorProduct.map f _), mul_add, ← add_assoc, pow_zero, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply,
        ← mul_one (h * 1 ⊗ₜ _), D.mem_ker.1 h0] at this
      rw [← this, Finset.mul_sum]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pow_succ']
    rintro (_ | k) hk
    · exact h0
    · exact ih _ h1 k (by omega)

private theorem chk_expand {ι : Type} (w : MvPolynomial ι A ⊗[A] E) :
    ∃ s : Finset (ι →₀ ℕ), ∀ t, s ⊆ t → w = ∑ α ∈ t, (MvPolynomial.monomial α (1 : A)) ⊗ₜ[A]
      TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) := by
  classical
  induction w with
  | zero => exact ⟨∅, by simp⟩
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨s', hs'⟩ := hb
    refine ⟨s ∪ s', fun t ht => ?_⟩
    simp only [map_add, tmul_add, Finset.sum_add_distrib]
    rw [← hs t (Finset.subset_union_left.trans ht), ← hs' t (Finset.subset_union_right.trans ht)]
  | tmul p z =>
    refine ⟨p.support, fun t ht => ?_⟩
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, MvPolynomial.lcoeff_apply, ← smul_tmul,
      ← sum_tmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    congr 1
    conv_lhs => rw [p.as_sum]
    refine Finset.sum_subset ht fun α _ hα => ?_
    rw [MvPolynomial.notMem_support_iff.1 hα, map_zero]

private theorem chk_kron {k : ℕ} (t : Finset (Fin k →₀ ℕ)) :
    ∃ N : ℕ, ∀ α ∈ t, ∀ β ∈ t, ∑ i, α i * N ^ (i : ℕ) = ∑ i, β i * N ^ (i : ℕ) → α = β := by
  have hb : ∀ α ∈ t, ∀ i, α i < t.sup (fun γ => ∑ j, γ j) + 1 := fun α hα i =>
    Nat.lt_succ_of_le ((Finset.single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans (Finset.le_sup (f := fun γ : Fin k →₀ ℕ => ∑ j, γ j) hα))
  refine ⟨t.sup (fun γ => ∑ j, γ j) + 1, fun α hα β hβ h => ?_⟩
  have : finFunctionFinEquiv (fun i => (⟨α i, hb α hα i⟩ : Fin _)) =
      finFunctionFinEquiv (fun i => (⟨β i, hb β hβ i⟩ : Fin _)) := by
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    exact h
  ext i
  exact congrArg Fin.val (congrFun (finFunctionFinEquiv.injective this) i)

private theorem chkK_mv {k : ℕ} (w : MvPolynomial (Fin k) A ⊗[A] E) (hw : chkK D _ w) (α : Fin k →₀ ℕ) :
    TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) ∈ D.ker := by
  classical
  obtain ⟨s, hs⟩ := chk_expand w
  have h1 := hs (insert α s) (Finset.subset_insert _ _)
  have hα : α ∈ insert α s := Finset.mem_insert_self _ _
  generalize insert α s = t at h1 hα
  obtain ⟨c, hc⟩ : ∃ c : (Fin k →₀ ℕ) → E,
      ∀ β, TensorProduct.lid A E ((MvPolynomial.lcoeff A β).rTensor E w) = c β := ⟨_, fun _ => rfl⟩
  simp only [hc] at h1 ⊢
  obtain ⟨N, hN⟩ := chk_kron t
  let φ : (Fin k →₀ ℕ) → ℕ := fun β => ∑ i, β i * N ^ (i : ℕ)
  have h2 := chkK_map D (MvPolynomial.aeval fun i : Fin k => (X : A[X]) ^ N ^ (i : ℕ)) hw
  have hlt : ∀ β ∈ t, φ β ∈ Finset.range (t.sup φ + 1) := fun β hβ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup hβ))
  have h3 : Algebra.TensorProduct.map (MvPolynomial.aeval fun i : Fin k => (X : A[X]) ^ N ^ (i : ℕ))
      (AlgHom.id A E) w = ∑ j ∈ Finset.range (t.sup φ + 1),
        ((X : A[X]) ^ j) ⊗ₜ[A] ∑ β ∈ t with φ β = j, c β := by
    rw [h1, map_sum, ← Finset.sum_fiberwise_of_maps_to hlt]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tmul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [← (Finset.mem_filter.1 hβ).2, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (by simp), ← Finset.prod_pow_eq_pow_sum]
    simp only [← pow_mul, mul_comm, AlgHom.id_apply]
  rw [h3] at h2
  have h4 := chkK_coef D _ _ h2 (φ α) (Finset.mem_range.1 (hlt α hα))
  have h5 : ∑ β ∈ t with φ β = φ α, c β = c α :=
    Finset.sum_eq_single_of_mem α (Finset.mem_filter.2 ⟨hα, rfl⟩) fun β hβ hne =>
      absurd (hN β (Finset.mem_filter.1 hβ).1 α hα (Finset.mem_filter.1 hβ).2) hne
  rwa [h5] at h4

end

theorem UpperTheory.V.CA.d_ch_ker :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), D.CH ≤ D.ker := by
  intro n A E _ _ _ D
  refine TwoSidedIdeal.span_le.2 ?_
  rintro _ ⟨k, x, α, rfl⟩
  exact chkK_mv D _ (chkK_ch D _ _) α
