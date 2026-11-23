import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier
import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.LagrangeIdealSgProof

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Lagrange

variable {LL O : Type} [Field LL] [CommRing O] [Algebra O LL] (v : AddValuation LL (WithTop ℚ))

theorem natCast_le_withTop {a b : ℕ} (h : ((a : ℕ) : WithTop ℚ) ≤ ((b : ℕ) : WithTop ℚ)) : a ≤ b := by
  have h1 : (((a : ℚ)) : WithTop ℚ) ≤ (((b : ℚ)) : WithTop ℚ) := by simpa using h
  exact_mod_cast WithTop.coe_le_coe.1 h1

theorem v_pow_nat {p : ℕ} (hvp : v (p : LL) = 1) (k : ℕ) : v ((p : LL) ^ k) = ((k : ℕ) : WithTop ℚ) := by
  rw [AddValuation.map_pow, hvp]; simp

theorem assoc_of_v {p : ℕ} (hinj : Function.Injective (algebraMap O LL)) (hvp : v (p : LL) = 1)
    (hO : ∀ x : LL, 0 ≤ v x → ∃ a : O, algebraMap O LL a = x) (x : O) (k : ℕ)
    (hx : v (algebraMap O LL x) = ((k : ℕ) : WithTop ℚ)) : Associated x ((p : O) ^ k) := by
  have hk : ((k : ℕ) : WithTop ℚ) ≠ ⊤ := by
    have : ((k : ℕ) : WithTop ℚ) = (((k : ℚ)) : WithTop ℚ) := by simp
    rw [this]; exact WithTop.coe_ne_top
  have hp0 : ((p : LL) ^ k) ≠ 0 := by
    intro h0
    have := v_pow_nat v hvp k
    rw [h0, AddValuation.map_zero] at this
    exact hk this.symm
  set y : LL := algebraMap O LL x / (p : LL) ^ k with hy
  have hyx : y * (p : LL) ^ k = algebraMap O LL x := by rw [hy]; field_simp
  have hvy : v y = 0 := by
    have h1 : v y + ((k : ℕ) : WithTop ℚ) = 0 + ((k : ℕ) : WithTop ℚ) := by
      rw [← v_pow_nat v hvp k, ← AddValuation.map_mul, hyx, hx, v_pow_nat v hvp k, zero_add]
    exact (WithTop.add_right_inj hk).1 h1
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hvy
    exact WithTop.top_ne_zero hvy
  have hvyi : v y⁻¹ = 0 := by
    have h1 : v y⁻¹ + v y = 0 := by
      rw [← AddValuation.map_mul, inv_mul_cancel₀ hy0, AddValuation.map_one]
    rwa [hvy, add_zero] at h1
  obtain ⟨u, hu⟩ := hO y hvy.ge
  obtain ⟨w, hw⟩ := hO y⁻¹ hvyi.ge
  have huw : u * w = 1 := hinj (by rw [map_mul, hu, hw, map_one, mul_inv_cancel₀ hy0])
  have hxu : x = (p : O) ^ k * u := hinj (by
    rw [map_mul, map_pow, map_natCast, hu, ← hyx, mul_comm])
  have hunit : IsUnit u := IsUnit.of_mul_eq_one w huw
  obtain ⟨uu, rfl⟩ := hunit
  exact (Associated.symm ⟨uu, hxu.symm⟩)

theorem v_prod (S : Finset ℤ) (f : ℤ → O) (k : ℤ → ℕ)
    (h : ∀ b ∈ S, v (algebraMap O LL (f b)) = ((k b : ℕ) : WithTop ℚ)) :
    v (algebraMap O LL (∏ b ∈ S, f b)) = ((∑ b ∈ S, k b : ℕ) : WithTop ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, AddValuation.map_mul,
      h a (Finset.mem_insert_self a s), ih (fun b hb => h b (Finset.mem_insert_of_mem hb))]
    push_cast; rfl

theorem lagrange_of_val (p : ℕ) [Fact p.Prime] [IsDomain O]
    (hinj : Function.Injective (algebraMap O LL)) (hvp : v (p : LL) = 1)
    (hO : ∀ x : LL, 0 ≤ v x → ∃ a : O, algebraMap O LL a = x)
    (S₁ S₂ : Finset ℤ) (sg : ℕ) (c : ℤ → O) (hd : Disjoint S₁ S₂)
    (hc : ∀ a ∈ S₁ ∪ S₂, ∀ b ∈ S₁ ∪ S₂, a ≠ b →
      v (algebraMap O LL (c a - c b)) = ((sg + padicValInt p (a - b) : ℕ) : WithTop ℚ))
    (E : ℕ) (hE : ∀ a ∈ S₁,
      v (algebraMap O LL ((∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))).eval (c a))) +
        v (algebraMap O LL ((Polynomial.derivative
          (∏ b ∈ S₁, (Polynomial.X - Polynomial.C (c b)))).eval (c a))) ≤ (E : WithTop ℚ)) :
    Polynomial.C (((p : ℕ) : O) ^ E) ∈
        Ideal.span ({∏ b ∈ S₁, (Polynomial.X - Polynomial.C (c b)),
          ∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))} : Set (Polynomial O)) := by
  classical
  have hL := Formalism.ZetaNonvanishing.LIFTV.lagrangeIdealSg_proof p O sg S₁ S₂ c hd (fun a ha b hb hab =>
    assoc_of_v v hinj hvp hO _ _ (hc a (Finset.mem_union_left _ ha) b hb hab))
  set Em : ℕ := S₁.sup fun a =>
        (∑ b ∈ S₂, (sg + padicValInt p (a - b))) + ∑ a' ∈ S₁.erase a, (sg + padicValInt p (a - a'))
    with hEm
  have hle : Em ≤ E := by
    refine Finset.sup_le fun a ha => ?_
    have h1 : (∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))).eval (c a) =
        ∏ b ∈ S₂, (c a - c b) := by
      rw [Polynomial.eval_prod]; simp
    have h2 : (Polynomial.derivative (∏ b ∈ S₁, (Polynomial.X - Polynomial.C (c b)))).eval (c a) =
        ∏ b ∈ S₁.erase a, (c a - c b) := by
      have := Lagrange.eval_nodal_derivative_eval_node_eq (s := S₁) (v := c) ha
      rw [Lagrange.nodal, Lagrange.nodal] at this
      rw [this, Polynomial.eval_prod]; simp
    have h3 := hE a ha
    rw [h1, h2, v_prod v S₂ (fun b => c a - c b) (fun b => sg + padicValInt p (a - b))
      (fun b hb => hc a (Finset.mem_union_left _ ha) b (Finset.mem_union_right _ hb)
        (fun hab => (Finset.disjoint_left.1 hd ha) (hab ▸ hb))),
      v_prod v (S₁.erase a) (fun b => c a - c b) (fun b => sg + padicValInt p (a - b))
      (fun b hb => hc a (Finset.mem_union_left _ ha) b
        (Finset.mem_union_left _ (Finset.mem_of_mem_erase hb)) (Finset.ne_of_mem_erase hb).symm),
      ← Nat.cast_add] at h3
    exact natCast_le_withTop h3
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [pow_add, mul_comm, Polynomial.C_mul]
  exact Ideal.mul_mem_left _ _ hL

end Lagrange

theorem exists_pos_const_Lagrange_condition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : adm5 D HW F := by
  intro l _ K s LL h S₁ S₂ sg c hd hc E hE
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have : Fact ((D.loc l).PD K).p.Prime := ⟨((D.loc l).PD K).hp⟩
  refine lagrange_of_val ((D.loc l).v LL) ((D.loc l).PD K).p Subtype.val_injective
    (by rw [hp]; exact (D.loc l).v_l LL)
    (fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩) S₁ S₂ sg c hd hc E hE

theorem lam_eq (l H : ℕ) : lam l H = Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam l H := rfl

theorem aR_eq (l H : ℕ) : aR l H = Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR l H := rfl

theorem one_le_lam (l H : ℕ) (hl : 2 ≤ l) : 1 ≤ lam l H := by
  unfold lam
  have : 0 ≤ Real.logb (l : ℝ) (2 * (H : ℝ)) := by
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · simp
    · refine Real.logb_nonneg (by exact_mod_cast hl) ?_
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
  linarith

theorem aR_nonneg (l H : ℕ) (hl : 2 ≤ l) : 0 ≤ aR l H := by
  unfold aR
  have h1 := one_le_lam l H hl
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h2 : 0 ≤ (H : ℝ) * (2 * (l : ℝ) - 1) / ((l : ℝ) - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (Nat.cast_nonneg H) (by linarith)
  linarith

theorem floor_a_le (l H η bi : ℕ) (hl : 2 ≤ l) (h : 2 * aR l H + (η : ℝ) + 1 ≤ (bi : ℝ)) :
    2 * ⌊aR l H⌋₊ + η + 1 ≤ bi := by
  have h1 : ((⌊aR l H⌋₊ : ℕ) : ℝ) ≤ aR l H := Nat.floor_le (aR_nonneg l H hl)
  have h2 : ((2 * ⌊aR l H⌋₊ + η + 1 : ℕ) : ℝ) ≤ (bi : ℝ) := by push_cast; linarith
  exact_mod_cast h2

theorem add_le_hpar (n : ℕ) [NeZero n] (b : ZMod n → ℕ) (S : ℕ) (i : ZMod n) :
    b i + S ≤ hpar n b S :=
  Nat.add_le_add_right (Finset.le_sup (f := b) (Finset.mem_univ i)) S

theorem eBd_parts (l : ℕ) (hl : 11 ≤ l) (h η S b a : ℕ) (s₁ E e₂ t : ℝ) (ht : 0 ≤ t) (hb : b ≤ h)
    (ha : (a : ℝ) ≤ aR l (h + η) + 1)
    (hs₁ : s₁ ≤ (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + 2 * lam l (h + η))
    (hE : E ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((l : ℝ) - 1) + 3 * lam l (h + η))
    (he₂ : e₂ ≤ (b : ℝ) / ((l : ℝ) * ((l : ℝ) - 1)) + E + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η)
      + 2 * (S : ℝ) + 5 + lam l (h + η)) :
    s₁ + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + e₂ + (S : ℝ) + E + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η) + t ≤
      eBd 32 4 10 (24 + t) l (h + η) S η := by
  have h1 := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_coefficient_chain_bounds.2.1 l hl h η S b a s₁ E e₂ hb ha hs₁ hE he₂
  have h2 := one_le_lam l (h + η) (by omega)
  have h3 : t ≤ t * lam l (h + η) := le_mul_of_one_le_right ht h2
  unfold eBd
  rw [← lam_eq] at h1
  linarith

theorem exists_e (l : ℕ) (hl : 11 ≤ l) (h η S b a : ℕ) (s₁ E e₂ : ℝ) (hb : b ≤ h)
    (ha : (a : ℝ) ≤ aR l (h + η) + 1)
    (hs₁ : s₁ ≤ (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + 2 * lam l (h + η))
    (hE : E ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((l : ℝ) - 1) + 3 * lam l (h + η))
    (he₂ : e₂ ≤ (b : ℝ) / ((l : ℝ) * ((l : ℝ) - 1)) + E + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η)
      + 2 * (S : ℝ) + 5 + lam l (h + η)) :
    ∃ e : ℕ, s₁ + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + e₂ + (S : ℝ) + E + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η) ≤ e ∧
      (e : ℝ) ≤ eBd 32 4 10 25 l (h + η) S η := by
  have h1 := eBd_parts l hl h η S b a s₁ E e₂ 1 zero_le_one hb ha hs₁ hE he₂
  norm_num at h1
  set x := s₁ + 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + e₂ + (S : ℝ) + E + Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l (h + η) with hx
  refine ⟨⌈x⌉₊, Nat.le_ceil x, ?_⟩
  rcases le_or_gt 0 x with h0 | h0
  · exact (Nat.ceil_lt_add_one h0).le.trans h1
  · rw [Nat.ceil_eq_zero.2 h0.le]
    have h2 := one_le_lam l (h + η) (by omega)
    have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
    unfold eBd
    have t1 : 0 ≤ 32 * (((h + η : ℕ) : ℝ)) / (l : ℝ) ^ 2 := by positivity
    have t2 : 0 ≤ 10 * (η : ℝ) / ((l : ℝ) - 1) :=
      div_nonneg (by positivity) (by linarith)
    have t3 : 0 ≤ 4 * (S : ℝ) := by positivity
    push_cast at t1 ⊢
    linarith

section MassData

variable {O : Type} [CommRing O] [IsDomain O]

theorem len_quot_nat [IsDiscreteValuationRing O] (a : O) (ha : a ≠ 0) :
    ∃ k : ℕ, Module.length O (O ⧸ Ideal.span {a}) = k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have h1 : Ideal.span {a} = Ideal.span {ϖ ^ e} := Ideal.span_singleton_eq_span_singleton.2 he
  have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le ϖ e
  have h3 : IsSimpleModule O (O ⧸ Ideal.span {ϖ}) := by
    rw [isSimpleModule_iff_isCoatom, ← hϖ.maximalIdeal_eq]
    exact (IsLocalRing.maximalIdeal.isMaximal O).out
  rw [Module.length_eq_one (R := O) (M := O ⧸ Ideal.span {ϖ}), mul_one, ← h1] at h2
  have h4 : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top e) h2
  exact ⟨_, (ENat.natCast_toNat h4).symm⟩

variable [IsPrincipalIdealRing O] {M : Type} [AddCommGroup M] [Module O M] [Module.Free O M]
  [Module.Finite O M]

theorem length_le_of_filtration (a : O) (P : Submodule O M) (k : ℕ) (Fl : ℕ → Submodule O M) (gen : Finset ℕ)
    (m e e' L kO : ℕ) (hk : Module.length O (O ⧸ Ideal.span {a}) = kO)
    (hF0 : Fl 0 = ⊤) (hF : ∀ i < k, Fl (i + 1) ≤ Fl i) (hgen : gen ⊆ Finset.range k)
    (hgs : ∀ i ∈ gen, ∃ s : Finset M, s.card ≤ m ∧ (↑s : Set M) ⊆ Fl i ∧
        Fl i ≤ Submodule.span O (↑s : Set M) ⊔ Fl (i + 1))
    (hkill : ∀ x : M, a ^ e' • x ∈ P)
    (hlen : ∀ i < k, i ∉ gen →
      Module.length O (↥(Fl i) ⧸ (Fl (i + 1) ⊔ P).comap (Fl i).subtype) ≤ (L : ℕ∞))
    (hlast : ∀ x ∈ Fl k, a ^ e • x ∈ P) :
    Module.length O (M ⧸ P) ≤
      ((Module.finrank O M * e * kO + gen.card * (m * e' * kO) + (k - gen.card) * L : ℕ) : ℕ∞) := by
  have h1 := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_coefficient_chain_bounds.2.2.2.2.2.2.2.2.1 O M P k Fl hF0 hF
  have h2 := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_coefficient_chain_bounds.2.2.2.2.2.2.2.2.2.1 O M a e (Fl k) P hlast
  rw [hk] at h2
  have hA : ∑ i ∈ gen, Module.length O (↥(Fl i) ⧸ (Fl (i + 1) ⊔ P).comap (Fl i).subtype) ≤
      gen.card • ((m * e' * kO : ℕ) : ℕ∞) := by
    refine Finset.sum_le_card_nsmul _ _ _ fun i hi => ?_
    obtain ⟨s, hc, hsF, hle⟩ := hgs i hi
    have hZ : Submodule.span O (↑s : Set M) ⊔ Fl (i + 1) = Fl i :=
      le_antisymm (sup_le (Submodule.span_le.2 hsF) (hF i (Finset.mem_range.1 (hgen hi)))) hle
    have := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ColAsm.len_bound a m e' (Fl i) (Fl (i + 1)) (Fl (i + 1) ⊔ P) s hc hZ
      le_sup_left (fun p _ => Submodule.mem_sup_right (hkill p))
    rw [hk] at this
    exact_mod_cast this
  have hB : ∑ i ∈ Finset.range k \ gen,
      Module.length O (↥(Fl i) ⧸ (Fl (i + 1) ⊔ P).comap (Fl i).subtype) ≤
      (Finset.range k \ gen).card • (L : ℕ∞) := by
    refine Finset.sum_le_card_nsmul _ _ _ fun i hi => ?_
    obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.1 hi
    exact hlen i (Finset.mem_range.1 hi1) hi2
  rw [Finset.card_sdiff_of_subset hgen, Finset.card_range] at hB
  rw [← Finset.sum_sdiff hgen] at h1
  calc Module.length O (M ⧸ P) ≤ _ := h1
    _ ≤ ((k - gen.card) • (L : ℕ∞) + gen.card • ((m * e' * kO : ℕ) : ℕ∞)) +
        ((Module.finrank O M * e : ℕ) : ℕ∞) * (kO : ℕ∞) := by gcongr
    _ = _ := by
      simp only [nsmul_eq_mul]
      push_cast
      ring

end MassData

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def preIm (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {FF : Type} [AddCommGroup FF] [Module O FF] (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) : Submodule O FF :=
  ((F.ImF PD).comap (latticeFiniteCocycles PD T₂.L).subtype).comap g

def MassData (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (n r m : ℕ) (c : ℝ) (e : ℕ) : Prop :=
  ∃ (FF : Type) (_ : AddCommGroup FF) (_ : Module O FF) (_ : Module.Free O FF)
    (_ : Module.Finite O FF) (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (k : ℕ) (Fl : ℕ → Submodule O FF)
    (gen : Finset ℕ),
    (∀ z : ↥(latticeFiniteCocycles PD T₂.L), ∃ x : FF, (z : G → T₂.V) - (g x : G → T₂.V) ∈ latticeCoboundaries T₂.L) ∧
    Module.finrank O FF ≤ (n + 1) * r ∧ gen.card ≤ 4 * n ∧ k - gen.card ≤ 3 * n / 2 ∧
    Fl 0 = ⊤ ∧ (∀ i < k, Fl (i + 1) ≤ Fl i) ∧ gen ⊆ Finset.range k ∧
    (∀ i ∈ gen, ∃ s : Finset FF, s.card ≤ m ∧ (↑s : Set FF) ⊆ Fl i ∧
      Fl i ≤ Submodule.span O (↑s : Set FF) ⊔ Fl (i + 1)) ∧
    (∀ i < k, i ∉ gen → ∃ L kO : ℕ,
      Module.length O (↥(Fl i) ⧸ (Fl (i + 1) ⊔ preIm PD F g).comap (Fl i).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧ (L : ℝ) ≤ c * kO) ∧
    ∀ x ∈ Fl k, ((PD.p : O) ^ e) • (g x : G → T₂.V) ∈ F.ImF PD

theorem colLeR_of_lengthCount [IsDomain O] [IsDiscreteValuationRing O] (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (n r m S H e e' : ℕ) (hl : 2 ≤ PD.p)
    (hLift : F.LiftF PD e')
    (hB : MassData PD F n r m ((r : ℝ) * (S : ℝ) + 2 * (m : ℝ) * cD PD.p H) e) :
    ColLeR PD F (colBd 4 (3 / 2) PD.p n r m S H e e') := by
  obtain ⟨FF, _, _, _, _, g, k, Fl, gen, hg, hr, hg4, hk3, hF0, hF, hgen, hgs, hlen, hlast⟩ := hB
  obtain ⟨kO, hkO⟩ := len_quot_nat ((PD.p : ℕ) : O) hp0
  set c : ℝ := (r : ℝ) * (S : ℝ) + 2 * (m : ℝ) * cD PD.p H with hc
  have hc0 : 0 ≤ c := by
    have hl' : (2 : ℝ) ≤ PD.p := by exact_mod_cast hl
    have : 0 ≤ cD PD.p H := by
      unfold cD
      have : 0 ≤ ((H : ℝ) + 1) / ((PD.p : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
      linarith
    rw [hc]; positivity
  have hcol : F.col PD ≤ Module.length O (FF ⧸ preIm PD F g) := by
    let I' : Submodule O ↥(latticeFiniteCocycles PD T₂.L) := (F.ImF PD).comap (latticeFiniteCocycles PD T₂.L).subtype
    let ψ : FF →ₗ[O] (↥(latticeFiniteCocycles PD T₂.L) ⧸ I') := I'.mkQ.comp g
    have hker : preIm PD F g ≤ LinearMap.ker ψ := by
      intro x hx
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero I').2 hx
    have hs : Function.Surjective ((preIm PD F g).liftQ ψ hker) := by
      intro y
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
      obtain ⟨x, hx⟩ := hg z
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      rw [Submodule.liftQ_apply]
      refine ((Submodule.Quotient.eq I').2 ?_).symm
      exact Submodule.mem_sup_right hx
    exact Module.length_le_of_surjective _ hs
  have hb := length_le_of_filtration ((PD.p : ℕ) : O) (preIm PD F g) k Fl gen m e e' ⌊c * kO⌋₊ kO hkO hF0 hF hgen hgs
    (fun x => by
      change ((g (((PD.p : ℕ) : O) ^ e' • x) : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V) ∈ F.ImF PD
      rw [map_smul]
      exact hLift _ (g x).2)
    (fun i hi hig => by
      obtain ⟨L, kO', h1, h2, h3⟩ := hlen i hi hig
      have hkk : kO' = kO := by
        have : (kO' : ℕ∞) = kO := by rw [← h2, ← hkO]; rfl
        exact_mod_cast this
      subst hkk
      refine h1.trans ?_
      exact_mod_cast Nat.le_floor h3)
    (fun x hx => by
      change ((g (((PD.p : ℕ) : O) ^ e • x) : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V) ∈ F.ImF PD
      rw [map_smul]
      exact hlast x hx)
  have htot := hcol.trans hb
  have hne : F.col PD ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) htot
  refine ⟨(F.col PD).toNat, kO, (ENat.natCast_toNat hne).symm, hkO, ?_⟩
  have hnat : (F.col PD).toNat ≤
      Module.finrank O FF * e * kO + gen.card * (m * e' * kO) + (k - gen.card) * ⌊c * kO⌋₊ := by
    have := htot
    rw [← ENat.natCast_toNat hne] at this
    exact_mod_cast this
  have hreal : (((F.col PD).toNat : ℕ) : ℝ) ≤
      (Module.finrank O FF : ℝ) * e * kO + (gen.card : ℝ) * (m * e' * kO) +
        ((k - gen.card : ℕ) : ℝ) * (⌊c * kO⌋₊ : ℝ) := by exact_mod_cast hnat
  have hfl : ((⌊c * kO⌋₊ : ℕ) : ℝ) ≤ c * kO := Nat.floor_le (by positivity)
  have h1 : (Module.finrank O FF : ℝ) ≤ ((n : ℝ) + 1) * r := by exact_mod_cast hr
  have h2 : (gen.card : ℝ) ≤ 4 * n := by exact_mod_cast hg4
  have h3 : ((k - gen.card : ℕ) : ℝ) ≤ 3 / 2 * n := by
    have : ((k - gen.card : ℕ) : ℝ) ≤ ((3 * n / 2 : ℕ) : ℝ) := by exact_mod_cast hk3
    have h' : ((3 * n / 2 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) / 2 := by exact_mod_cast Nat.cast_div_le
    push_cast at h'
    linarith
  have t1 : (Module.finrank O FF : ℝ) * e * kO ≤ ((n : ℝ) + 1) * r * e * kO := by gcongr
  have t2 : (gen.card : ℝ) * (m * e' * kO) ≤ 4 * n * (m * e' * kO) := by gcongr
  have t3 : ((k - gen.card : ℕ) : ℝ) * (⌊c * kO⌋₊ : ℝ) ≤ 3 / 2 * n * (c * kO) := by gcongr
  unfold colBd
  rw [← hc]
  nlinarith [t1, t2, t3, hreal]

def OpenC [NeZero n] (W : LocWach PD LL O v n) (R : ℕ → Prop) (C : ℝ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → R m →
      ∃ e : ℕ, (e : ℝ) ≤ eBd 32 4 10 C PD.p (hpar n b S + η) S η ∧
        MassData PD F n (Module.finrank LL T₂.V) m
          ((Module.finrank LL T₂.V : ℝ) * (S : ℝ) + 2 * (m : ℝ) * cD PD.p (hpar n b S + η)) e ∧
        (m = 0 → F.LiftF PD (e + 3 * S))

theorem thmCKR_of_open [NeZero n] (W : LocWach PD LL O v n) (R : ℕ → Prop) (C : ℝ)
    (hA : Formalism.MainNotions.LiftingTheory.coreLiftA W) (h : OpenC W R C) : ThmCKR W R 32 4 10 4 (3 / 2) C := by
  intro d T₁ T₂ F b S η m hS hR
  obtain ⟨e, he, hB, h0⟩ := h d T₁ T₂ F b S η m hS hR
  have hJ := jumpsLet_win W hS
  obtain ⟨hCA, h11, -, ⟨hdom, hdvr, -⟩, -, hSur, -⟩ := hS
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0'
    have h1 : ((PD.p : ℕ) : LL) = 0 := by
      have := congrArg (algebraMap O LL) h0'
      simpa using this
    have h2 := W.v_l
    rw [h1, AddValuation.map_zero] at h2
    exact WithTop.top_ne_one h2
  exact ⟨e, he, colLeR_of_lengthCount hp0 F n _ m S _ e _ (by omega) (hA hCA T₁ T₂ F (MiW d b S η) (hiW d b S η) hSur hJ) hB, h0⟩

end Core

def openKR (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (R : ℕ → Prop) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], OpenC ((HW l).W K 1 LL hg) R C

theorem Theorem_C_range_of_open (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (R : ℕ → Prop) (C CA CB CK : ℝ) (h10 : adm10 D HW F CA CB CK)
    (h : openKR D HW F R C) : TheoremCConstantsRange D HW F R 32 4 10 4 (3 / 2) C := by
  intro l _ K LL hg _
  exact thmCKR_of_open _ R C (h10.1 l K 1 LL hg) (h l K LL hg)

theorem Theorem_C_of_open (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h10 : adm10 D HW F CA CB CK)
    (h : openKR D HW F (fun _ => True) C) : aux₃ D HW F C :=
  Theorem_C_range_of_open D HW F _ C CA CB CK h10 h

end Formalism.MainNotions.RamifiedCoefficientChains
