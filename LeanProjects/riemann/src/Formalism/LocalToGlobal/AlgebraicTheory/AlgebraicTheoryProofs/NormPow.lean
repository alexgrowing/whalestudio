import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH Sesq altE IsSelfDual IsHerm IsReps IsSemiChar imgLat Th alphaQ qOf opU
  relIdx inter fixedBy stdH stdLat blk4 pow4 slice tens4 kernel4 sumU IsIsom F0 StdData prodFn)
open Formalism.L2.Th1.GD (LocNorm)

namespace RepresentativeBijection

section Reps

variable {V : Type} [AddCommGroup V]

private theorem bijective_mk_of_isReps {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    Function.Bijective (fun x : {x // x ∈ S} =>
      (QuotientAddGroup.mk (⟨x.1, hS.1 x.1 x.2⟩ : Λ₂) : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)) := by
  have h2 := hS.2.1
  have h3 := hS.2.2
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg] at hxy
    have h' := Λ₁.neg_mem hxy
    rw [neg_add, neg_neg, ← sub_eq_add_neg] at h'
    exact Subtype.ext (h2 x hx y hy h')
  · intro q
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x, hx, hzx⟩ := h3 z hz
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg]
    rwa [neg_add_eq_sub]

theorem relIdx_eq_card {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    relIdx Λ₁ Λ₂ = S.card := by
  classical
  calc relIdx Λ₁ Λ₂ = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := rfl
    _ = Nat.card {x // x ∈ S} := (Nat.card_congr (Equiv.ofBijective _ (bijective_mk_of_isReps hS))).symm
    _ = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem mem_imgLat' [Module ℂ V] (g : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) (y : V) :
    y ∈ imgLat (g : V →ₗ[ℂ] V) Λ ↔ g.symm y ∈ Λ := by
  simp only [imgLat, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

end Reps

private theorem exists_isReps_of_relIdx_ne_zero {V : Type} [AddCommGroup V] {A B : AddSubgroup V}
    (hAB : relIdx A B ≠ 0) : ∃ S : Finset V, IsReps A B S := by
  classical
  have hfin : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero hAB
  have := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
  choose r hr using (QuotientAddGroup.mk_surjective :
    Function.Surjective (QuotientAddGroup.mk : B → B ⧸ A.addSubgroupOf B))
  refine ⟨Finset.univ.image fun q => ((r q : B) : V), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact (r q).2
  · intro x hx y hy hxy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy
    have hqq : q = q' := by
      rw [← hr q, ← hr q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
        AddSubgroup.coe_neg]
      have h' := A.neg_mem hxy
      rwa [neg_sub, sub_eq_neg_add] at h'
    rw [hqq]
  · intro y hy
    refine ⟨(r (QuotientAddGroup.mk ⟨y, hy⟩) : V), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    have h' := hr (QuotientAddGroup.mk ⟨y, hy⟩)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg] at h'
    rwa [neg_add_eq_sub] at h'

private theorem mul_opU_add_eq_of_mem_fixedBy {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
    {A B : AddSubgroup V} {α : V → ℂ} {F : V → ℂ} (hH : IsHerm H) (hα : IsSemiChar H B α)
    (hF : F ∈ fixedBy H α A) {x a : V} (hx : x ∈ B) (ha : a ∈ A) (haB : a ∈ B) (z : V) :
    α (x + a) * opU H (x + a) F z = α x * opU H x F z := by
  have hF' : ∀ y ∈ A, ∀ w, α y * opU H y F w = F w := hF
  have h1 := hα.1
  have hxa := hα.2 x hx a haB
  have hax := hα.2 a haB x hx
  rw [add_comm a x] at hax
  have hx0 : α x ≠ 0 := by rcases h1 x hx with h | h <;> rw [h] <;> norm_num
  have ha0 : α a ≠ 0 := by rcases h1 a haB with h | h <;> rw [h] <;> norm_num
  have hE : altE H a x = -altE H x a := by
    simp only [altE]
    rw [hH x a, Complex.conj_im]
  have h4 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))
      = Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H a x : ℝ) : ℂ)) := by
    have h3 : α x * α a * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))
        = α x * α a * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H a x : ℝ) : ℂ)) := by
      rw [← hxa, hax]; ring
    exact mul_left_cancel₀ (mul_ne_zero hx0 ha0) h3
  have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))
      * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)) = 1 := by
    conv_lhs => arg 2; rw [h4]
    rw [← Complex.exp_add, hE, Complex.ofReal_neg]
    convert Complex.exp_zero using 2
    ring
  have hFa := hF' a ha (z + x)
  simp only [opU] at hFa ⊢
  have hPQ : ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2)
      + (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2)
      = (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)
        + (Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ) := by
    have hc : H x a - conj (H x a) = 2 * Complex.I * (((H x a).im : ℝ) : ℂ) := by
      rw [Complex.sub_conj]; push_cast; ring
    simp only [map_add, LinearMap.add_apply, altE]
    rw [hH x a]
    linear_combination ((Real.pi : ℂ) / 2) * hc
  have hinv : Complex.exp (-(Real.pi : ℂ) * H (z + x) a - (Real.pi : ℂ) * H a a / 2)
      * Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  have key : Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2)
      * Complex.exp (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2)
      = Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)
        * Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hPQ]
  rw [← add_assoc]
  set E1 := Complex.exp (-(Real.pi : ℂ) * H (z + x) a - (Real.pi : ℂ) * H a a / 2)
  set E2 := Complex.exp ((Real.pi : ℂ) * H (z + x) a + (Real.pi : ℂ) * H a a / 2)
  set EQ := Complex.exp (-(Real.pi : ℂ) * H z (x + a) - (Real.pi : ℂ) * H (x + a) (x + a) / 2)
  set eR := Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)
  set eE := Complex.exp ((Real.pi : ℂ) * Complex.I * ((altE H x a : ℝ) : ℂ))
  linear_combination (F (z + x + a) * EQ) * hxa + (α x * eR) * hFa
    + (-(α x * α a * F (z + x + a) * eE * EQ)) * hinv + (α x * α a * F (z + x + a) * eE * E1) * key
    + (α x * α a * F (z + x + a) * eR * E1) * hexp

private theorem finsum_quotient_eq_sum_reps {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
    {A B : AddSubgroup V} {α : V → ℂ} {F : V → ℂ} (hH : IsHerm H) (hα : IsSemiChar H B α)
    (hF : F ∈ fixedBy H α A) {S : Finset V} (hS : IsReps A B S) (z : V) :
    (∑ᶠ c : B ⧸ A.addSubgroupOf B, α ((Quotient.out c : B) : V) * opU H ((Quotient.out c : B) : V) F z)
      = ∑ x ∈ S, α x * opU H x F z := by
  classical
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_mk_of_isReps hS)), finsum_eq_sum_of_fintype,
    ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun x _ => ?_
  set q := (Equiv.ofBijective _ (bijective_mk_of_isReps hS)) x with hqdef
  have hq : (QuotientAddGroup.mk (Quotient.out q) : B ⧸ A.addSubgroupOf B)
      = QuotientAddGroup.mk (⟨x.1, hS.1 x.1 x.2⟩ : B) := QuotientAddGroup.out_eq' q
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
    AddSubgroup.coe_neg] at hq
  have hoB : ((Quotient.out q : B) : V) ∈ B := (Quotient.out q).2
  have haB : -((Quotient.out q : B) : V) + x.1 ∈ B := B.add_mem (B.neg_mem hoB) (hS.1 x.1 x.2)
  have hxo : (x.1 : V) = ((Quotient.out q : B) : V) + (-((Quotient.out q : B) : V) + x.1) := by abel
  rw [hxo]
  exact (mul_opU_add_eq_of_mem_fixedBy hH hα hF hoB hq haB z).symm

private theorem stdH_apply_algebraic (L : PeriodPair) (N : Type) [Fintype N] [DecidableEq N] (u v : N → ℂ) :
    stdH L N u v = ∑ m, u m * ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ * conj (v m) := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem sum_ite_eq_snd {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (b : β)
    (f : α × β → ℂ) : ∑ w : α × β, (if b = w.2 then f w else 0) = ∑ k, f (k, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

private theorem sum_ite_eq_fst {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] (a : α)
    (f : α × β → ℂ) : ∑ w : α × β, (if a = w.1 then f w else 0) = ∑ k, f (a, k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

private theorem matH_blk4 {N : Type} [Fintype N] (g : Matrix N N ℂ) (u v : Fin 4 × N → ℂ) :
    matH (blk4 g) u v = ∑ a, matH g (slice a u) (slice a v) := by
  simp only [matH, LinearMap.mk₂'ₛₗ_apply, blk4, mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq_fst]
  rw [Fintype.sum_prod_type]
  rfl

theorem sqrt_pow_inv (r k : ℕ) :
    ((Real.sqrt ((r ^ k : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ = (((Real.sqrt r : ℝ) : ℂ)⁻¹) ^ k := by
  have h : Real.sqrt ((r ^ k : ℕ) : ℝ) = Real.sqrt r ^ k := by
    conv_lhs => rw [Nat.cast_pow, ← Real.sq_sqrt (Nat.cast_nonneg r)]
    rw [← pow_mul, mul_comm 2 k, pow_mul, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]
  rw [h, Complex.ofReal_pow, inv_pow]

section Slices

variable {M M' I : Type} [Fintype M] [Fintype M'] [Fintype I] (e : M' ≃ M × I)

def sl (i : I) (w : M' → ℂ) : M → ℂ := fun m => w (e.symm (m, i))

def asm (f : I → M → ℂ) : M' → ℂ := fun m' => f (e m').2 (e m').1

theorem sl_asm (f : I → M → ℂ) (i : I) : sl e i (asm e f) = f i := by
  funext m
  simp [sl, asm]

theorem asm_sl (w : M' → ℂ) : asm e (fun i => sl e i w) = w := by
  funext m'
  simp [sl, asm]

theorem sl_add (i : I) (x y : M' → ℂ) : sl e i (x + y) = sl e i x + sl e i y := rfl
theorem sl_sub (i : I) (x y : M' → ℂ) : sl e i (x - y) = sl e i x - sl e i y := rfl
theorem sl_smul (i : I) (c : ℂ) (x : M' → ℂ) : sl e i (c • x) = c • sl e i x := rfl

theorem asm_injective : Function.Injective (asm e) := by
  intro f g h
  funext i
  have := congrArg (sl e i) h
  rwa [sl_asm, sl_asm] at this

theorem sum_e (G : M' → ℂ) : ∑ m', G m' = ∑ i, ∑ m, G (e.symm (m, i)) := by
  rw [← Equiv.sum_comp e.symm G, Fintype.sum_prod_type, Finset.sum_comm]

theorem prod_e (G : M' → ℂ) : ∏ m', G m' = ∏ i, ∏ m, G (e.symm (m, i)) := by
  rw [← Equiv.prod_comp e.symm G, Fintype.prod_prod_type, Finset.prod_comm]

def prodSub (A : AddSubgroup (M → ℂ)) : AddSubgroup (M' → ℂ) where
  carrier := {w | ∀ i, sl e i w ∈ A}
  zero_mem' := fun _ => A.zero_mem
  add_mem' := fun hx hy i => A.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => A.neg_mem (hx i)

theorem mem_prodSub (A : AddSubgroup (M → ℂ)) (w : M' → ℂ) : w ∈ prodSub e A ↔ ∀ i, sl e i w ∈ A := Iff.rfl

variable [DecidableEq I]

theorem reps_prod {A B : AddSubgroup (M → ℂ)} {S : Finset (M → ℂ)} (hS : IsReps A B S) :
    ∃ S' : Finset (M' → ℂ), IsReps (prodSub e A) (prodSub e B) S' ∧ S'.card = S.card ^ Fintype.card I ∧
      ∀ G : (M' → ℂ) → ℂ, ∑ x ∈ S', G x = ∑ f ∈ Fintype.piFinset (fun _ : I => S), G (asm e f) := by
  classical
  have h1 := hS.1
  have h2 := hS.2.1
  have h3 := hS.2.2
  refine ⟨(Fintype.piFinset fun _ : I => S).image (asm e), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    rw [Fintype.mem_piFinset] at hf
    refine (mem_prodSub e B _).2 fun i => ?_
    rw [sl_asm]
    exact h1 _ (hf i)
  · intro x hx y hy hxy
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hy
    rw [Fintype.mem_piFinset] at hf hg
    have hfg : f = g := by
      funext i
      have := (mem_prodSub e A _).1 hxy i
      rw [sl_sub, sl_asm, sl_asm] at this
      exact h2 _ (hf i) _ (hg i) this
    rw [hfg]
  · intro y hy
    have : ∀ i, ∃ x ∈ S, sl e i y - x ∈ A := fun i => h3 _ ((mem_prodSub e B y).1 hy i)
    choose f hfS hfA using this
    refine ⟨asm e f, Finset.mem_image.2 ⟨f, Fintype.mem_piFinset.2 hfS, rfl⟩, ?_⟩
    refine (mem_prodSub e A _).2 fun i => ?_
    rw [sl_sub, sl_asm]
    exact hfA i
  · rw [Finset.card_image_of_injective _ (asm_injective e), Fintype.card_piFinset,
      Finset.prod_const, Finset.card_univ]
  · intro G
    rw [Finset.sum_image fun x _ y _ h => asm_injective e h]

theorem relIdx_prod {A B : AddSubgroup (M → ℂ)} (hAB : relIdx A B ≠ 0) :
    relIdx (prodSub e A) (prodSub e B) = relIdx A B ^ Fintype.card I := by
  obtain ⟨S, hS⟩ := exists_isReps_of_relIdx_ne_zero hAB
  obtain ⟨S', hS', hcard, -⟩ := reps_prod e hS
  rw [relIdx_eq_card hS', relIdx_eq_card hS, hcard]

variable (H : Sesq (M → ℂ)) (H' : Sesq (M' → ℂ)) (hHd : ∀ x y, H' x y = ∑ i, H (sl e i x) (sl e i y))
include hHd

theorem herm_prod (hH : IsHerm H) : IsHerm H' := by
  intro x y
  rw [hHd, hHd, map_sum]
  exact Finset.sum_congr rfl fun i _ => hH _ _

theorem altE_prod (x y : M' → ℂ) : altE H' x y = ∑ i, altE H (sl e i x) (sl e i y) := by
  simp only [altE, hHd, Complex.im_sum]

theorem alphaQ_prod (c : ℝ) (x : M' → ℂ) : alphaQ c H' x = ∏ i, alphaQ c H (sl e i x) := by
  simp only [alphaQ, qOf, hHd, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Complex.exp_sum]

theorem opU_prod (x : M' → ℂ) (F : (M → ℂ) → ℂ) (z : M' → ℂ) :
    opU H' x (fun w => ∏ i, F (sl e i w)) z = ∏ i, opU H (sl e i x) F (sl e i z) := by
  simp only [opU, hHd, sl_add, Finset.prod_mul_distrib]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]

theorem semiChar_prod {B : AddSubgroup (M → ℂ)} {α : (M → ℂ) → ℂ} (hα : IsSemiChar H B α) :
    IsSemiChar H' (prodSub e B) (fun x => ∏ i, α (sl e i x)) := by
  obtain ⟨h1, h2⟩ := hα
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [mem_prodSub] at hx
    refine Finset.prod_induction _ (fun z => z = 1 ∨ z = -1) ?_ (Or.inl rfl) fun i _ => h1 _ (hx i)
    rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · rw [mem_prodSub] at hx hy
    simp only [sl_add]
    rw [Finset.prod_congr rfl fun i _ => h2 _ (hx i) _ (hy i), Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, altE_prod (hHd := hHd), Complex.ofReal_sum, Finset.mul_sum,
      Complex.exp_sum]

theorem fixed_prod {A : AddSubgroup (M → ℂ)} {α : (M → ℂ) → ℂ} {F : (M → ℂ) → ℂ} (hF : F ∈ fixedBy H α A) :
    (fun w => ∏ i, F (sl e i w)) ∈ fixedBy H' (fun x => ∏ i, α (sl e i x)) (prodSub e A) := by
  have hF' : ∀ x ∈ A, ∀ z, α x * opU H x F z = F z := hF
  show ∀ x ∈ prodSub e A, ∀ z, (∏ i, α (sl e i x)) * opU H' x (fun w => ∏ i, F (sl e i w)) z
    = ∏ i, F (sl e i z)
  intro x hx z
  rw [mem_prodSub] at hx
  rw [opU_prod (hHd := hHd), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => hF' _ (hx i) _

theorem inter_prod (hH : IsHerm H) (A B : AddSubgroup (M → ℂ)) (α : (M → ℂ) → ℂ) (hα : IsSemiChar H B α)
    (F : (M → ℂ) → ℂ) (hF : F ∈ fixedBy H α A) (hAB : relIdx A B ≠ 0) (z : M' → ℂ) :
    inter H' (fun x => ∏ i, α (sl e i x)) (prodSub e A) (prodSub e B) (fun w => ∏ i, F (sl e i w)) z
      = ∏ i, inter H α A B F (sl e i z) := by
  classical
  obtain ⟨S, hS⟩ := exists_isReps_of_relIdx_ne_zero hAB
  obtain ⟨S', hS', hcard, hsum⟩ := reps_prod e hS
  have hR : ∀ i, inter H α A B F (sl e i z)
      = ((Real.sqrt (relIdx A B) : ℝ) : ℂ)⁻¹ * ∑ x ∈ S, α x * opU H x F (sl e i z) := fun i => by
    simp only [inter]
    rw [finsum_quotient_eq_sum_reps hH hα hF hS]
  rw [Finset.prod_congr rfl fun i _ => hR i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  simp only [inter]
  rw [finsum_quotient_eq_sum_reps (herm_prod e H H' hHd hH) (semiChar_prod e H H' hHd hα)
    (fixed_prod e H H' hHd hF) hS' z, hsum, relIdx_prod e hAB, sqrt_pow_inv]
  congr 1
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [opU_prod (hHd := hHd), ← Finset.prod_mul_distrib]
  simp only [sl_asm]

end Slices

section Std

variable {M M' I : Type} [Fintype M] [Fintype M'] [Fintype I] [DecidableEq M] [DecidableEq M'] (e : M' ≃ M × I)

theorem stdH_prod (L : PeriodPair) (x y : M' → ℂ) :
    stdH L M' x y = ∑ i, stdH L M (sl e i x) (sl e i y) := by
  simp only [stdH_apply_algebraic]
  rw [sum_e e]
  rfl

theorem stdLat_prod (L : PeriodPair) : stdLat L M' = prodSub e (stdLat L M) := by
  ext w
  rw [mem_prodSub]
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, sl]
  constructor
  · intro h i m
    exact h _
  · intro h m'
    have := h (e m').2 (e m').1
    simpa using this

theorem gaussianVacuum_prod_blocks (L : PeriodPair) (ω₀ : ℂ) : F0 L ω₀ M' = fun w => ∏ i, F0 L ω₀ M (sl e i w) := by
  funext w
  simp only [F0, prodFn]
  exact prod_e e _

end Std

section Pow

variable {n : Type} [Fintype n] [DecidableEq n] {I : Type} [Fintype I] [DecidableEq I]

def eP (n I : Type) : Fin 4 × (n × I) ≃ (Fin 4 × n) × I := (Equiv.prodAssoc (Fin 4) n I).symm

def powEquiv {M M' : Type} [Fintype M] [Fintype M'] (e : M' ≃ M × I) (g : (M → ℂ) ≃ₗ[ℂ] (M → ℂ)) : (M' → ℂ) ≃ₗ[ℂ] (M' → ℂ) where
  toFun z := asm e fun i => g (sl e i z)
  invFun z := asm e fun i => g.symm (sl e i z)
  map_add' x y := by
    funext m'
    show g (sl e (e m').2 (x + y)) (e m').1 = g (sl e (e m').2 x) (e m').1 + g (sl e (e m').2 y) (e m').1
    rw [sl_add, map_add]; rfl
  map_smul' c x := by
    funext m'
    show g (sl e (e m').2 (c • x)) (e m').1 = c * g (sl e (e m').2 x) (e m').1
    rw [sl_smul, map_smul]; rfl
  left_inv z := by
    show asm e (fun i => g.symm (sl e i (asm e fun i => g (sl e i z)))) = z
    simp only [sl_asm, LinearEquiv.symm_apply_apply, asm_sl]
  right_inv z := by
    show asm e (fun i => g (sl e i (asm e fun i => g.symm (sl e i z)))) = z
    simp only [sl_asm, LinearEquiv.apply_symm_apply, asm_sl]

theorem sl_powEquiv {M M' : Type} [Fintype M] [Fintype M'] (e : M' ≃ M × I) (g : (M → ℂ) ≃ₗ[ℂ] (M → ℂ)) (i : I) (z : M' → ℂ) :
    sl e i (powEquiv e g z) = g (sl e i z) := by
  show sl e i (asm e fun i => g (sl e i z)) = g (sl e i z)
  rw [sl_asm]

theorem matH_hPow (h : Matrix n n ℂ) (u v : n × I → ℂ) :
    matH (hPow I h) u v = ∑ i, matH h (fun k => u (k, i)) (fun k => v (k, i)) := by
  simp only [matH, LinearMap.mk₂'ₛₗ_apply, hPow, mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq_snd]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem hermitian_block_power_sum (h : Matrix n n ℂ) (x y : Fin 4 × (n × I) → ℂ) :
    matH (blk4 (hPow I h)) x y = ∑ i, matH (blk4 h) (sl (eP n I) i x) (sl (eP n I) i y) := by
  rw [matH_blk4]
  simp only [matH_hPow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matH_blk4]
  rfl

theorem img_prod (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (Λ : AddSubgroup (n → ℂ)) :
    imgLat ((powEquiv (eP n I) g : (Fin 4 × (n × I) → ℂ) ≃ₗ[ℂ] (Fin 4 × (n × I) → ℂ)) :
        (Fin 4 × (n × I) → ℂ) →ₗ[ℂ] (Fin 4 × (n × I) → ℂ)) (pow4 (latPow I Λ)) =
      prodSub (eP n I) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) := by
  ext y
  rw [mem_imgLat', mem_prodSub]
  simp only [mem_imgLat']
  constructor
  · intro h i
    show ∀ a, _
    intro a
    exact h a i
  · intro h a
    show ∀ i, _
    intro i
    exact h i a

end Pow

end RepresentativeBijection

open RepresentativeBijection

theorem local_norm_scaling : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hL
  obtain ⟨g₁, ε, h1, h2, h3, h4, h5⟩ := hL
  refine ⟨g₁, c ^ 4 * ε, h1, h2, h3, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 ^ 4 * 1 := by gcongr
      _ = 1 := by norm_num
  · funext z
    have hz := congrFun h5 z
    simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hz ⊢
    rw [hz]
    ring

theorem local_norm_power : LocNormPow := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hOK n _ _ h Λ hΛ hΛθ θ hθ p _ ι hN I _ _
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, hT⟩ := hN
  have hidx1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 := by
    intro h0; rw [h0] at hp; exact hp (dvd_zero p)
  have hSD := Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hOK.1 hOK.2.1 hOK.2.2.1 n h Λ g₁ hiso hΛ hΛθ
    hidx1 hidx
  have hH : IsHerm (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) :=
    (Formalism.L2.Th1.H.stdHBasic (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)).2.1
  have hF := (Formalism.L2.Th1.H.product_theta_mem' (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) hSD.per hSD.half _
    hSD.betaStd).1.2
  have hHd := stdH_prod (eP n I) (cmL a₀ b₀ dK ha hdK lam hlam)
  refine ⟨powEquiv (eP n I) g₁, ε ^ Fintype.card I, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [LinearEquiv.coe_coe]
    rw [hHd, hermitian_block_power_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sl_powEquiv, sl_powEquiv]
    exact hiso _ _
  · rw [stdLat_prod (eP n I), img_prod, relIdx_prod _ hidx1]
    intro hd
    exact hp ((Fact.out : p.Prime).dvd_of_dvd_pow hd)
  · rw [stdLat_prod (eP n I), img_prod, relIdx_prod _ hidx]
    exact pow_ne_zero _ hidx
  · rw [map_pow, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hε
  · funext z
    have hL : tens4 (fnPow I θ) z = ∏ i, tens4 θ (sl (eP n I) i z) := by
      simp only [tens4, fnPow]
      rw [Finset.prod_comm]
      rfl
    rw [hL, Pi.smul_apply, smul_eq_mul]
    simp only [hT, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    congr 1
    simp only [kernel4]
    have hα : alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × (n × I))) =
        fun x => ∏ i, alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (sl (eP n I) i x) :=
      funext fun x => alphaQ_prod (eP n I) _ _ hHd _ x
    rw [stdLat_prod (eP n I), img_prod, hα, gaussianVacuum_prod_blocks (eP n I),
      inter_prod (eP n I) _ _ hHd hH _ _ _ hSD.betaSemi _ hF hidx1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sl_powEquiv]

end Formalism.L2.AlgTh
