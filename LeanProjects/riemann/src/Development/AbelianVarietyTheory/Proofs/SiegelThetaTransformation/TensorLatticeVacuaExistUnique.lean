import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExOfPow
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndexStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TensVac

section Product

variable {κ ι : Type} [Fintype κ] [Fintype ι] {φ φ' ψ : Matrix κ ι ℚ → ℂ}

theorem sb_mul_conj (h : IsSB φ) (h' : IsSB ψ) : IsSB (fun x => φ x * conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ (fun x => conj (ψ x)) h (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι ψ ψ h' h').2.2.2.1).2.2.1

theorem sb_smul (c : ℂ) (h : IsSB φ) : IsSB (c • φ) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ φ h h).2.1 c

theorem ip_smul_left (c : ℂ) (h : IsSB φ) (h' : IsSB ψ) : SW.ip (c • φ) ψ = c * SW.ip φ ψ := by
  have hm := sb_mul_conj h h'
  have e : (fun x => (c • φ) x * conj (ψ x)) = c • fun x => φ x * conj (ψ x) := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  unfold SW.ip; rw [e]; exact (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ hm hm).2.2.2.2.2.1 c

theorem ip_add_left (h : IsSB φ) (h₂ : IsSB φ') (h' : IsSB ψ) :
    SW.ip (φ + φ') ψ = SW.ip φ ψ + SW.ip φ' ψ := by
  have hm := sb_mul_conj h h'
  have hm' := sb_mul_conj h₂ h'
  have e : (fun x => (φ + φ') x * conj (ψ x)) =
      (fun x => φ x * conj (ψ x)) + fun x => φ' x * conj (ψ x) := by
    funext x; simp only [Pi.add_apply, add_mul]
  unfold SW.ip; rw [e]; exact (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ hm hm').2.2.2.2.1

theorem ip_conj (h : IsSB φ) (h' : IsSB ψ) : SW.ip ψ φ = conj (SW.ip φ ψ) := by
  have hm := sb_mul_conj h h'
  have e : (fun x => ψ x * conj (φ x)) = fun x => conj (φ x * conj (ψ x)) := by
    funext x; simp only [map_mul, RCLike.conj_conj, mul_comm]
  unfold SW.ip; rw [e]; exact (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ hm hm).2.2.2.2.2.2.1

theorem ip_smul_right (c : ℂ) (h : IsSB φ) (h' : IsSB ψ) :
    SW.ip φ (c • ψ) = conj c * SW.ip φ ψ := by
  have hm := sb_mul_conj h h'
  have e : (fun x => φ x * conj ((c • ψ) x)) = conj c • fun x => φ x * conj (ψ x) := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  unfold SW.ip; rw [e]; exact (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ hm hm).2.2.2.2.2.1 (conj c)

theorem sum_sb_ip (s : Finset (Matrix κ ι ℚ → ℂ)) (hs : ∀ φ ∈ s, IsSB φ) (h' : IsSB ψ) :
    IsSB (∑ φ ∈ s, φ) ∧ SW.ip (∑ φ ∈ s, φ) ψ = ∑ φ ∈ s, SW.ip φ ψ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨isSB_zero, ?_⟩
    have := ip_smul_left (0 : ℂ) (isSB_zero (κ := κ) (ι := ι) (K := ℚ)) h'
    simpa using this
  | insert a s ha ih =>
    have ha' := hs a (Finset.mem_insert_self a s)
    obtain ⟨h1, h2⟩ := ih fun φ hφ => hs φ (Finset.mem_insert_of_mem hφ)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ ha' h1).1, by rw [ip_add_left ha' h1 h', h2]⟩

theorem heisS_fix [DecidableEq ι] {R : ℕ} (h : HasLevel R φ) {a b : Matrix κ ι ℚ} (ha : IntM a)
    (hb : IntM b) : heisS (((2 * R : ℕ) : ℚ) • a) (((2 * R : ℕ) : ℚ) • b) φ = φ := by
  funext x
  have hint : ∀ {q : ℚ}, IsIntegral ℤ q → ∃ z : ℤ, q = z := fun hq => by
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
    exact ⟨z, by rw [← hz]; simp⟩
  have hcast : ∀ z : ℤ, IsIntegral ℤ (z : ℚ) := fun z => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := z))
  have hper : φ (x - ((2 * R : ℕ) : ℚ) • b) = φ x := by
    have hy : IntM ((-2 : ℚ) • b) := fun k i => by
      obtain ⟨z, hz⟩ := hint (hb k i)
      simp only [Matrix.smul_apply, smul_eq_mul, hz]
      simpa using hcast (-2 * z)
    rw [← h.2 x _ hy]
    congr 1
    rw [smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 2
    push_cast; ring
  simp only [heisS]
  rw [hper]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul]
  have hRx := h.1 x hx
  choose Xz hXz using fun k i => hint (hRx k i)
  choose Az hAz using fun k i => hint (ha k i)
  choose Bz hBz using fun k i => hint (hb k i)
  obtain ⟨M, key⟩ : ∃ M : ℤ, (∑ k, (2 * (x k ⬝ᵥ (((2 * R : ℕ) : ℚ) • a) k) -
      (((2 * R : ℕ) : ℚ) • a) k ⬝ᵥ (((2 * R : ℕ) : ℚ) • b) k) : ℚ) = 2 * (M : ℚ) := by
    refine ⟨∑ k, ∑ i, (2 * Xz k i * Az k i - 2 * (R : ℤ) ^ 2 * Az k i * Bz k i), ?_⟩
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := hXz k i
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    rw [hAz, hBz]
    linear_combination 4 * (Az k i : ℚ) * e
  rw [key]
  have : cexp (↑π * I * (((2 * (M : ℚ) : ℚ)) : ℂ)) = 1 := by
    rw [show (↑π * I * (((2 * (M : ℚ) : ℚ)) : ℂ)) = (M : ℂ) * (2 * π * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I M
  rw [this, mul_one]

end Product

section Groups

variable {G α : Type} [AddCommGroup G]

theorem finite_image_of_fg {A : AddSubgroup G} (hA : A.FG) (f : G → α) {N : ℕ} (hN : 0 < N)
    (hf : ∀ a ∈ A, ∀ b ∈ A, f (a + N • b) = f a) : (f '' A).Finite := by
  classical
  obtain ⟨S, hS⟩ := hA
  have hspan : ∀ x, x ∈ A ↔ x ∈ Submodule.span ℤ (S : Set G) := fun x => by
    rw [← hS, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]
  have hmemS : ∀ d : S → ℤ, (∑ s : S, d s • (s : G)) ∈ A := fun d =>
    (hspan _).2 (Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span s.2))
  let rep : (S → Fin N) → G := fun d => ∑ s : S, (((d s : ℕ) : ℤ)) • (s : G)
  refine (Set.finite_range (f ∘ rep)).subset ?_
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.1 ((hspan a).1 ha)
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hnn : ∀ s, 0 ≤ c s % (N : ℤ) := fun s => Int.emod_nonneg _ hN'.ne'
  refine ⟨fun s => ⟨(c s % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (c s) hN'
    have h0 := hnn s
    omega
  · have hdec : a = (∑ s : S, (c s % (N : ℤ)) • (s : G)) + N • ∑ s : S, (c s / (N : ℤ)) • (s : G) := by
      rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← natCast_zsmul, smul_smul, ← add_smul]
      congr 1
      rw [Int.emod_add_mul_ediv]
    have e : rep (fun s => ⟨(c s % (N : ℤ)).toNat, by
        have h1 := Int.emod_lt_of_pos (c s) hN'
        have h0 := hnn s
        omega⟩) = ∑ s : S, (c s % (N : ℤ)) • (s : G) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Int.toNat_of_nonneg (hnn s)]
    show f (rep _) = f a
    rw [e, hdec]
    exact (hf _ (hmemS _) _ (hmemS _)).symm

theorem ncard_image_eq {A A' : AddSubgroup G} (f : G → α)
    (hf : ∀ a ∈ A, ∀ b ∈ A, f a = f b ↔ -a + b ∈ A') : (f '' A).ncard = A'.relIndex A := by
  rw [← Nat.card_coe_set_eq, AddSubgroup.relIndex, AddSubgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (fun a : A => (⟨f a, a, a.2, rfl⟩ : f '' A)) ?_) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : -(a : G) + b ∈ A' := by
      have := QuotientAddGroup.leftRel_apply.1 hab
      simpa [AddSubgroup.mem_addSubgroupOf] using this
    exact Subtype.ext ((hf a a.2 b b.2).2 h1)
  · intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
    have h1 := congrArg Subtype.val hxy
    have h2 : f a = f b := h1
    refine QuotientAddGroup.eq.2 ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa using (hf a a.2 b b.2).1 h2
  · rintro ⟨_, a, ha, rfl⟩
    exact ⟨QuotientAddGroup.mk ⟨a, ha⟩, rfl⟩

end Groups

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

noncomputable def crdHom (hs : IsSympl X bas) :
    Matrix (Fin n) (Fin r) E →+ Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ :=
  AddMonoidHom.mk' (fun y => (Matrix.of fun k i => crd X bas (y k) (Sum.inl i),
    Matrix.of fun k i => crd X bas (y k) (Sum.inr i))) fun y y' => by
      refine Prod.ext ?_ ?_ <;> ext k i <;> exact congrFun (crd_add hs (y k) (y' k)) _

theorem heisG_eq (hs : IsSympl X bas) (y : Matrix (Fin n) (Fin r) E) (φ : TF n g) :
    heisG X bas y φ = heisS (crdHom hs y).1 (crdHom hs y).2 φ := rfl

theorem crdHom_bijective (hs : IsSympl X bas) : Function.Bijective (crdHom (n := n) hs) := by
  constructor
  · intro y y' h
    funext k
    have e1 := congrArg Prod.fst h
    have e2 := congrArg Prod.snd h
    have : crd X bas (y k) = crd X bas (y' k) := by
      funext j
      cases j with
      | inl i => exact congrFun (congrFun e1 k) i
      | inr i => exact congrFun (congrFun e2 k) i
    rw [← vecQ_crd X bas (y k), this, vecQ_crd]
  · rintro ⟨P, Q⟩
    refine ⟨fun k => vecQ X bas (Sum.elim (P k) (Q k)), ?_⟩
    refine Prod.ext ?_ ?_ <;> ext k i <;> simp [crdHom, crd_vecQ hs]

theorem om_crdHom (hs : IsSympl X bas) (y y' : Matrix (Fin n) (Fin r) E) :
    (∑ k, ((crdHom hs y).1 k ⬝ᵥ (crdHom hs y').2 k - (crdHom hs y').1 k ⬝ᵥ (crdHom hs y).2 k) : ℚ) =
      -∑ k, EF X (y k) (y' k) := by
  simp only [EF_crd hs, crdHom, AddMonoidHom.mk'_apply, dotProduct, Matrix.of_apply,
    Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sumEF_swap (hs : IsSympl X bas) (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, EF X (y' k) (y k) = -∑ k, EF X (y k) (y' k) := by
  simp only [EF_crd hs]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem heisG_smul (y : Matrix (Fin n) (Fin r) E) (c : ℂ) (φ : TF n g) :
    heisG X bas y (c • φ) = c • heisG X bas y φ := by
  funext x; simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem heisG_sum (y : Matrix (Fin n) (Fin r) E) (s : Finset (TF n g)) :
    heisG X bas y (∑ φ ∈ s, φ) = ∑ φ ∈ s, heisG X bas y φ := by
  funext x; simp only [heisG, heisS, Finset.sum_apply, Finset.sum_mul]

theorem epsW_zero (w : E) : epsW X w (0 : Matrix (Fin n) (Fin r) E) = 1 := by
  have h0 : ∀ v : Fin r → E, EF X 0 v = 0 := fun v => (EFBil X).map_zero₂ v
  have h1 : ∀ i, EF X ((0 : Matrix (Fin n) (Fin r) E) i) (w • (0 : Matrix (Fin n) (Fin r) E) i) = 0 :=
    fun i => by rw [show (0 : Matrix (Fin n) (Fin r) E) i = 0 from rfl, smul_zero]; exact h0 0
  simp only [epsW, h1, Finset.sum_const_zero, Rat.cast_zero, mul_zero, Complex.exp_zero]

theorem epsW_mul_conj (w : E) (y : Matrix (Fin n) (Fin r) E) :
    epsW X w y * conj (epsW X w y) = 1 := by
  unfold epsW
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : conj (↑π * I * (((∑ k, EF X (y k) (w • y k) : ℚ)) : ℂ)) =
      -(↑π * I * (((∑ k, EF X (y k) (w • y k) : ℚ)) : ℂ)) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ratCast]; ring
  rw [this, add_neg_cancel, Complex.exp_zero]

variable (X) in

def Good (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) : Prop :=
  A.FG ∧ (∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ k : ℤ, ∑ i, EF X (y i) (y' i) = k) ∧
    ∀ y ∈ A, epsW X w y ^ 2 = 1 ∧ ∀ y' ∈ A, epsW X w (y + y') =
      epsW X w y * epsW X w y' * cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ)))

variable {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem Good.eps_two (hs : IsSympl X bas) (hA : Good X w A) {y} (hy : y ∈ A) :
    epsW X w (2 • y) = 1 := by
  have hsw := sumEF_swap hs y y
  have h0 : (∑ k, EF X (y k) (y k)) = 0 := by linarith
  rw [two_nsmul, (hA.2.2 y hy).2 y hy, h0]
  simp only [Rat.cast_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
  rw [← sq]; exact (hA.2.2 y hy).1

theorem Good.vac (hs : IsSympl X bas) (hA : Good X w A) : ∃ v : TF n g, IsVac X bas w A v ∧
    ∀ v', IsSB v' → (∀ y ∈ A, epsW X w y • heisG X bas y v' = v') → ∃ c : ℂ, v' = c • v := by
  set e := AddEquiv.ofBijective (crdHom (n := n) hs) (crdHom_bijective hs) with he
  have hee : ∀ y, e.symm (crdHom hs y) = y := fun y => e.symm_apply_apply y
  have hce : ∀ p, crdHom hs (e.symm p) = p := fun p => e.apply_symm_apply p
  have hmem : ∀ y, crdHom hs y ∈ A.map (crdHom hs) ↔ y ∈ A := fun y =>
    AddSubgroup.mem_map_iff_mem (crdHom_bijective hs).1
  have hsd : ∀ p, p ∈ A.map (crdHom hs) ↔ ∀ p' ∈ A.map (crdHom hs),
      ∃ m : ℤ, (∑ k, (p.1 k ⬝ᵥ p'.2 k - p'.1 k ⬝ᵥ p.2 k) : ℚ) = m := by
    intro p
    constructor
    · intro hp p' hp'
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hp
      obtain ⟨y', hy', rfl⟩ := AddSubgroup.mem_map.1 hp'
      obtain ⟨m, hm⟩ := (hA.2.1 y).1 hy y' hy'
      exact ⟨-m, by rw [om_crdHom hs, hm]; push_cast; ring⟩
    · intro H
      rw [← hce p]
      refine AddSubgroup.mem_map_of_mem _ ((hA.2.1 _).2 fun y' hy' => ?_)
      obtain ⟨m, hm⟩ := H _ (AddSubgroup.mem_map_of_mem _ hy')
      refine ⟨-m, ?_⟩
      rw [← hce p, om_crdHom hs] at hm
      push_cast; linarith
  have hnorm : ∀ p ∈ A.map (crdHom hs), ‖epsW X w (e.symm p)‖ = 1 := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hp
    rw [hee]
    have h2 := congrArg norm (hA.2.2 y hy).1
    rw [norm_pow, norm_one] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  have hsemi : ∀ p ∈ A.map (crdHom hs), ∀ p' ∈ A.map (crdHom hs),
      epsW X w (e.symm (p + p')) = epsW X w (e.symm p) * epsW X w (e.symm p') *
        cexp (π * I * ((∑ k, (p.1 k ⬝ᵥ p'.2 k - p'.1 k ⬝ᵥ p.2 k) : ℚ) : ℂ)) := by
    intro p hp p' hp'
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hp
    obtain ⟨y', hy', rfl⟩ := AddSubgroup.mem_map.1 hp'
    rw [← map_add, hee, hee, hee, (hA.2.2 y hy).2 y' hy', om_crdHom hs]
    congr 2
    push_cast; ring
  have hord : ∃ m : ℕ, 0 < m ∧ ∀ p ∈ A.map (crdHom hs), epsW X w (e.symm (m • p)) = 1 := by
    refine ⟨2, two_pos, fun p hp => ?_⟩
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hp
    rw [← map_nsmul, hee]
    exact Good.eps_two hs hA hy
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := Vac.vacuum (Fin n) (Fin g) (A.map (crdHom hs))
    (fun p => epsW X w (e.symm p)) (Vac.fg_map hA.1 _) hsd hnorm hsemi hord
  refine ⟨v, ⟨hv1, hv2, fun y hy => ?_⟩, fun v' hv' hfix => hv4 v' hv' fun p hp => ?_⟩
  · have := hv3 _ ((hmem y).2 hy)
    rwa [hee] at this
  · obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hp
    rw [hee]; exact hfix y hy

theorem Good.uniq (hs : IsSympl X bas) (hA : Good X w A) {v v' : TF n g} (hv : IsVac X bas w A v)
    (hv' : IsSB v') (h : ∀ y ∈ A, epsW X w y • heisG X bas y v' = v') :
    v' = SW.ip v' v • v := by
  obtain ⟨v₀, hv₀, huniq⟩ := Good.vac hs hA
  obtain ⟨c, rfl⟩ := huniq v hv.1 hv.2.2
  obtain ⟨c', rfl⟩ := huniq v' hv' h
  have h1 := hv.2.1
  rw [ip_smul_left c hv₀.1 (sb_smul c hv₀.1), ip_smul_right c hv₀.1 hv₀.1, hv₀.2.1] at h1
  rw [ip_smul_left c' hv₀.1 (sb_smul c hv₀.1), ip_smul_right c hv₀.1 hv₀.1, hv₀.2.1, smul_smul]
  congr 1
  linear_combination -c' * h1

variable (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
include idx hs hn

theorem laws (y : Matrix (Fin n) (Fin r) E) {φ : TF n g} (hφ : IsSB φ) :
    IsSB (heisG X bas y φ) ∧ heisG X bas 0 φ = φ ∧ (∀ y', heisG X bas y (heisG X bas y' φ) =
      cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ))) • heisG X bas (y + y') φ) ∧
      (∀ ψ, IsSB ψ → SW.ip (heisG X bas y φ) (heisG X bas y ψ) = SW.ip φ ψ) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := (heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ
  exact ⟨h1, h2, h3, h4⟩

theorem rho_sb (y : Matrix (Fin n) (Fin r) E) {φ : TF n g} (hφ : IsSB φ) :
    IsSB (epsW X w y • heisG X bas y φ) := sb_smul _ (laws idx hs hn y hφ).1

theorem rho_zero {φ : TF n g} (hφ : IsSB φ) : epsW X w (0 : Matrix (Fin n) (Fin r) E) • heisG X bas 0 φ = φ := by
  rw [epsW_zero, one_smul]; exact (laws idx hs hn 0 hφ).2.1

theorem rho_ip (y : Matrix (Fin n) (Fin r) E) {φ ψ : TF n g} (hφ : IsSB φ) (hψ : IsSB ψ) :
    SW.ip (epsW X w y • heisG X bas y φ) (epsW X w y • heisG X bas y ψ) = SW.ip φ ψ := by
  obtain ⟨h1, -, -, h4⟩ := laws idx hs hn y hφ
  have h1' := (laws idx hs hn y hψ).1
  rw [ip_smul_left _ h1 (sb_smul _ h1'), ip_smul_right _ h1 h1', ← mul_assoc, epsW_mul_conj, one_mul,
    h4 ψ hψ]

theorem Good.rho_rho (hA : Good X w A) {y y'} (hy : y ∈ A) (hy' : y' ∈ A) {φ : TF n g}
    (hφ : IsSB φ) : epsW X w y • heisG X bas y (epsW X w y' • heisG X bas y' φ) =
      epsW X w (y + y') • heisG X bas (y + y') φ := by
  rw [heisG_smul, (laws idx hs hn y hφ).2.2.1 y', smul_smul, smul_smul, (hA.2.2 y hy).2 y' hy']

theorem Good.finite (hA : Good X w A) {φ : TF n g} (hφ : IsSB φ) :
    ((fun y => epsW X w y • heisG X bas y φ) '' A).Finite := by
  obtain ⟨R, hR, hlev⟩ := hφ
  obtain ⟨D1, hD1, hD1'⟩ := Vac.exists_den_fg
    (A.map ((AddMonoidHom.fst _ _).comp (crdHom (n := n) hs))) (Vac.fg_map hA.1 _)
  obtain ⟨D2, hD2, hD2'⟩ := Vac.exists_den_fg
    (A.map ((AddMonoidHom.snd _ _).comp (crdHom (n := n) hs))) (Vac.fg_map hA.1 _)
  have hint : ∀ b ∈ A, IntM (((D1 * D2 : ℕ) : ℚ) • (crdHom hs b).1) ∧
      IntM (((D1 * D2 : ℕ) : ℚ) • (crdHom hs b).2) := by
    intro b hb
    have h1 := hD1' _ (AddSubgroup.mem_map_of_mem _ hb)
    have h2 := hD2' _ (AddSubgroup.mem_map_of_mem _ hb)
    constructor
    · have := Vac.intM_smul D2 h1
      rwa [smul_smul, ← Nat.cast_mul, mul_comm D2 D1] at this
    · have := Vac.intM_smul D1 h2
      rwa [smul_smul, ← Nat.cast_mul] at this
  have hc : ∀ x : Matrix (Fin n) (Fin g) ℚ,
      (2 * (R * (D1 * D2))) • x = ((2 * R : ℕ) : ℚ) • (((D1 * D2 : ℕ) : ℚ) • x) := fun x => by
    rw [smul_smul, ← Nat.cast_smul_eq_nsmul ℚ]
    congr 1
    push_cast; ring
  refine finite_image_of_fg hA.1 _ (N := 2 * (R * (D1 * D2))) (by positivity) fun a ha b hb => ?_
  have hNb : (2 * (R * (D1 * D2))) • b ∈ A := AddSubgroup.nsmul_mem _ hb _
  have hfix : epsW X w ((2 * (R * (D1 * D2))) • b) • heisG X bas ((2 * (R * (D1 * D2))) • b) φ = φ := by
    have he : epsW X w ((2 * (R * (D1 * D2))) • b) = 1 := by
      rw [← smul_smul]; exact Good.eps_two hs hA (AddSubgroup.nsmul_mem _ hb _)
    rw [he, one_smul, heisG_eq hs, map_nsmul]
    show heisS ((2 * (R * (D1 * D2))) • (crdHom hs b).1) ((2 * (R * (D1 * D2))) • (crdHom hs b).2) φ = φ
    rw [hc, hc]
    exact heisS_fix hlev (hint b hb).1 (hint b hb).2
  show epsW X w (a + _) • heisG X bas (a + _) φ = epsW X w a • heisG X bas a φ
  rw [← Good.rho_rho idx hs hn hA ha hNb ⟨R, hR, hlev⟩, hfix]

theorem Good.proj (hA : Good X w A) {φ v : TF n g} (hφ : IsSB φ) (hv : IsVac X bas w A v) :
    IsSB (projA X bas w A φ) ∧ projA X bas w A φ = SW.ip φ v • v := by
  set O := (fun y => epsW X w y • heisG X bas y φ) '' (A : Set (Matrix (Fin n) (Fin r) E)) with hO
  have hfin : O.Finite := Good.finite idx hs hn hA hφ
  have hmemO : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    rw [Set.Finite.mem_toFinset] at hψ
    obtain ⟨y, -, rfl⟩ := hψ
    exact rho_sb idx hs hn y hφ
  obtain ⟨hsum, hip⟩ := sum_sb_ip hfin.toFinset hmemO hv.1
  have hipφ : ∀ ψ ∈ hfin.toFinset, SW.ip ψ v = SW.ip φ v := by
    intro ψ hψ
    rw [Set.Finite.mem_toFinset] at hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    conv_lhs => rw [← hv.2.2 y hy]
    exact rho_ip idx hs hn y hφ hv.1
  rw [Finset.sum_congr rfl hipφ, Finset.sum_const, nsmul_eq_mul] at hip
  have hfix : ∀ z ∈ A, epsW X w z • heisG X bas z (∑ ψ ∈ hfin.toFinset, ψ) = ∑ ψ ∈ hfin.toFinset, ψ := by
    intro z hz
    rw [heisG_sum, Finset.smul_sum]
    refine Finset.sum_nbij' (fun ψ => epsW X w z • heisG X bas z ψ)
      (fun ψ => epsW X w (-z) • heisG X bas (-z) ψ) ?_ ?_ ?_ ?_ ?_
    · intro ψ hψ
      simp only [Set.Finite.mem_toFinset] at hψ ⊢
      obtain ⟨y, hy, rfl⟩ := hψ
      exact ⟨z + y, add_mem hz hy, (Good.rho_rho idx hs hn hA hz hy hφ).symm⟩
    · intro ψ hψ
      simp only [Set.Finite.mem_toFinset] at hψ ⊢
      obtain ⟨y, hy, rfl⟩ := hψ
      exact ⟨-z + y, add_mem (neg_mem hz) hy, (Good.rho_rho idx hs hn hA (neg_mem hz) hy hφ).symm⟩
    · intro ψ hψ
      have h1 := hmemO ψ hψ
      rw [Good.rho_rho idx hs hn hA (neg_mem hz) hz h1, neg_add_cancel, rho_zero idx hs hn h1]
    · intro ψ hψ
      have h1 := hmemO ψ hψ
      rw [Good.rho_rho idx hs hn hA hz (neg_mem hz) h1, add_neg_cancel, rho_zero idx hs hn h1]
    · intro ψ hψ; rfl
  have hU := Good.uniq hs hA hv hsum hfix
  have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
    have h0 : φ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨0, zero_mem A, rho_zero idx hs hn hφ⟩
    exact_mod_cast (Finset.card_pos.2 ⟨φ, h0⟩).ne'
  have hproj : projA X bas w A φ = ((hfin.toFinset.card : ℂ))⁻¹ • ∑ ψ ∈ hfin.toFinset, ψ := by
    rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card O hfin]
  refine ⟨hproj ▸ sb_smul _ hsum, ?_⟩
  rw [hproj, hU, hip, smul_smul, inv_mul_cancel_left₀ hcard]

theorem Good.ip_eq_zero (hA : Good X w A) {v : TF n g} (hv : IsVac X bas w A v) {y}
    (hy : y ∉ A) : SW.ip (epsW X w y • heisG X bas y v) v = 0 := by
  have hnot : ¬ ∀ y' ∈ A, ∃ k : ℤ, ∑ i, EF X (y i) (y' i) = k := fun H => hy ((hA.2.1 y).2 H)
  push Not at hnot
  obtain ⟨y', hy', hk⟩ := hnot
  have hvs := hv.1
  have hfix := hv.2.2 y' hy'
  obtain ⟨hHv, -, hc1, -⟩ := laws idx hs hn y hvs
  obtain ⟨-, -, hc2, -⟩ := laws idx hs hn y' hvs
  have hsu : IsSB (epsW X w y • heisG X bas y v) := sb_smul _ hHv
  have hsw := sumEF_swap hs y y'
  set t : ℚ := ∑ i, EF X (y i) (y' i) with ht
  have key : epsW X w y' • heisG X bas y' (epsW X w y • heisG X bas y v) =
      cexp (2 * π * I * t) • (epsW X w y • heisG X bas y v) := by
    have e1 : epsW X w y' • heisG X bas y' (epsW X w y • heisG X bas y v) =
        (epsW X w y' * epsW X w y * cexp (-(π * I * ((∑ k, EF X (y' k) (y k) : ℚ) : ℂ)))) •
          heisG X bas (y' + y) v := by
      rw [heisG_smul, hc2 y, smul_smul, smul_smul]
    have e2 : epsW X w y • heisG X bas y v =
        (epsW X w y * epsW X w y' * cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ)))) •
          heisG X bas (y + y') v := by
      conv_lhs => rw [← hfix]
      rw [heisG_smul, hc1 y', smul_smul, smul_smul]
    rw [e1, e2, smul_smul, add_comm y' y, hsw]
    congr 1
    have : cexp (-(↑π * I * ((-t : ℚ) : ℂ))) = cexp (2 * π * I * t) * cexp (-(↑π * I * (t : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  have hl : cexp (2 * π * I * t) ≠ 1 := by
    intro h1
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h1
    apply hk m
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((t : ℚ) : ℂ) = (m : ℂ) := by
      apply mul_left_cancel₀ h2; rw [hm]; ring
    exact_mod_cast this
  have hip := rho_ip idx hs hn (w := w) y' hsu hvs
  rw [key, hfix, ip_smul_left _ hsu hvs] at hip
  have : (cexp (2 * π * I * t) - 1) * SW.ip (epsW X w y • heisG X bas y v) v = 0 := by
    rw [sub_mul, hip, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hl
  · exact h

theorem Good.overlap (hA : Good X w A) (hA' : Good X w A') {v v' : TF n g}
    (hv : IsVac X bas w A v) (hv' : IsVac X bas w A' v') :
    (A'.relIndex A : ℝ) * ‖SW.ip v v'‖ ^ 2 = 1 := by
  have hv's := hv'.1
  have hfin : ((fun y => epsW X w y • heisG X bas y v') '' (A : Set (Matrix (Fin n) (Fin r) E))).Finite :=
    Good.finite idx hs hn hA hv's
  have hinv : ∀ z ∈ A, ∀ ψ, IsSB ψ →
      epsW X w (-z) • heisG X bas (-z) (epsW X w z • heisG X bas z ψ) = ψ := fun z hz ψ hψ => by
    rw [Good.rho_rho idx hs hn hA (neg_mem hz) hz hψ, neg_add_cancel, rho_zero idx hs hn hψ]
  have hstab : ∀ z ∈ A, epsW X w z • heisG X bas z v' = v' ↔ z ∈ A' := by
    intro z hz
    constructor
    · intro h
      by_contra hz'
      have h0 := Good.ip_eq_zero idx hs hn hA' hv' hz'
      rw [h, hv'.2.1] at h0
      exact one_ne_zero h0
    · intro h; exact hv'.2.2 z h
  have hfeq : ∀ a ∈ A, ∀ b ∈ A, (fun y => epsW X w y • heisG X bas y v') a =
      (fun y => epsW X w y • heisG X bas y v') b ↔ -a + b ∈ A' := by
    intro a ha b hb
    simp only
    have hc : -a + b ∈ A := add_mem (neg_mem ha) hb
    constructor
    · intro h
      rw [← hstab _ hc, ← Good.rho_rho idx hs hn hA (neg_mem ha) hb hv's, ← h, hinv a ha v' hv's]
    · intro h
      conv_rhs => rw [show b = a + (-a + b) by abel]
      rw [← Good.rho_rho idx hs hn hA ha hc hv's, hv'.2.2 _ h]
  set T := hfin.toFinset with hT
  have hmemT : ∀ ψ ∈ T, IsSB ψ := by
    intro ψ hψ
    rw [hT, Set.Finite.mem_toFinset] at hψ
    obtain ⟨y, -, rfl⟩ := hψ
    exact rho_sb idx hs hn y hv's
  have horth : ∀ χ ∈ T, ∀ ψ ∈ T, SW.ip χ ψ = if χ = ψ then 1 else 0 := by
    intro χ hχ ψ hψ
    rw [hT, Set.Finite.mem_toFinset] at hχ hψ
    obtain ⟨b, hb, rfl⟩ := hχ
    obtain ⟨a, ha, rfl⟩ := hψ
    have hb' := rho_sb idx hs hn b hv's (w := w)
    have ha' := rho_sb idx hs hn a hv's (w := w)
    rw [← rho_ip idx hs hn (-a) hb' ha', hinv a ha v' hv's,
      Good.rho_rho idx hs hn hA (neg_mem ha) hb hv's]
    have hc : -a + b ∈ A := add_mem (neg_mem ha) hb
    by_cases h : -a + b ∈ A'
    · rw [hv'.2.2 _ h, hv'.2.1, if_pos (((hfeq a ha b hb).2 h).symm)]
    · rw [Good.ip_eq_zero idx hs hn hA' hv' h, if_neg]
      intro he
      exact h ((hfeq a ha b hb).1 he.symm)
  obtain ⟨hS, -⟩ := sum_sb_ip T hmemT hv's
  have hSψ : ∀ ψ ∈ T, SW.ip (∑ χ ∈ T, χ) ψ = 1 := by
    intro ψ hψ
    rw [(sum_sb_ip T hmemT (hmemT ψ hψ)).2, Finset.sum_congr rfl fun χ hχ => horth χ hχ ψ hψ,
      Finset.sum_ite_eq', if_pos hψ]
  have hSS : SW.ip (∑ χ ∈ T, χ) (∑ χ ∈ T, χ) = T.card := by
    rw [(sum_sb_ip T hmemT hS).2, Finset.sum_congr rfl fun ψ hψ => by
      rw [ip_conj hS (hmemT ψ hψ), hSψ ψ hψ, map_one], Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (T.card : ℂ) ≠ 0 := by
    have h0 : v' ∈ T := by
      rw [hT, Set.Finite.mem_toFinset]; exact ⟨0, zero_mem A, rho_zero idx hs hn hv's⟩
    exact_mod_cast (Finset.card_pos.2 ⟨v', h0⟩).ne'
  have hproj : projA X bas w A v' = ((T.card : ℂ))⁻¹ • ∑ ψ ∈ T, ψ := by
    rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin]
  have hP := (Good.proj idx hs hn hA hv's hv).2
  have e1 := congrArg (fun ψ => SW.ip ψ ψ) hP
  rw [hproj, ip_smul_left _ hS (sb_smul _ hS), ip_smul_right _ hS hS, hSS,
    ip_smul_left _ hv.1 (sb_smul _ hv.1), ip_smul_right _ hv.1 hv.1, hv.2.1] at e1
  have e2 : SW.ip v' v * conj (SW.ip v' v) = ((T.card : ℂ))⁻¹ := by
    have : conj ((T.card : ℂ)⁻¹) = (T.card : ℂ)⁻¹ := by simp
    rw [this, inv_mul_cancel₀ hcard, mul_one, mul_one] at e1
    exact e1.symm
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at e2
  have e3 : ‖SW.ip v' v‖ ^ 2 = ((T.card : ℝ))⁻¹ := Complex.ofReal_injective (by rw [e2]; simp)
  have hcr : (T.card : ℝ) ≠ 0 := by exact_mod_cast hcard
  rw [← ncard_image_eq _ hfeq, Set.ncard_eq_toFinset_card _ hfin, ← hT, ip_conj hv's hv.1,
    Complex.norm_conj, e3, mul_inv_cancel₀ hcr]

end Main

theorem vacua : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (∃ v, IsVac X bas w (tens Λ L) v) ∧ (∀ v v', IsVac X bas w (tens Λ L) v → IsSB v' → (∀ y ∈ tens Λ L, epsW X w y • heisG X bas y v' = v') → v' = ip v' v • v) ∧ (∀ φ : TF n g, IsSB φ → ∀ v, IsVac X bas w (tens Λ L) v → projA X bas w (tens Λ L) φ = ip φ v • v) ∧ ∀ L', SelfD X L' → ∀ Λ' ∈ Vset E n M, ∀ v v', IsVac X bas w (tens Λ L) v → IsVac X bas w (tens Λ' L') v' → ((tens Λ' L').relIndex (tens Λ L) : ℝ) * ‖ip v v'‖ ^ 2 = 1 := by
  intro E _ _ _ r X g bas idx n hs hn w hw htr L hL M Λ hΛ
  have good : ∀ L, SelfD X L → ∀ Λ ∈ Vset E n M, Good X w (tens Λ L) := fun L hL Λ hΛ => by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw htr L hL M Λ hΛ
    exact ⟨h1, h2, h3⟩
  have hG := good L hL Λ hΛ
  exact ⟨(Good.vac hs hG).imp fun v hv => hv.1, fun v v' hv hv' h => Good.uniq hs hG hv hv' h,
    fun φ hφ v hv => (Good.proj idx hs hn hG hφ hv).2, fun L' hL' Λ' hΛ' v v' hv hv' =>
      Good.overlap idx hs hn hG (good L' hL' Λ' hΛ') hv hv'⟩

end GlobalTheory.SW.TensVac
