import Mathlib

namespace GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)

def stab (x : V) : Subgroup L where
  carrier := {l | π (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_stab {x : V} {l : L} : l ∈ stab π L x ↔ π (l : G) x = x := Iff.rfl

noncomputable def cv (H : Subgroup L) (x : V) (q : L ⧸ H) : V := π ((q.out : L) : G) x

theorem cv_mk {H : Subgroup L} {x : V} (hH : H ≤ stab π L x) (a : L) :
    cv π L H x (QuotientGroup.mk a) = π (a : G) x := by
  unfold cv
  set b : L := (QuotientGroup.mk a : L ⧸ H).out with hb
  have h1 : (QuotientGroup.mk b : L ⧸ H) = QuotientGroup.mk a := QuotientGroup.out_eq' _
  have h2 : b⁻¹ * a ∈ H := QuotientGroup.eq.mp h1
  have h3 := (mem_stab π L).mp (hH h2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply] at h3
  calc π (b : G) x = π (b : G) (π (b : G)⁻¹ (π (a : G) x)) := by rw [h3]
    _ = π (a : G) x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

noncomputable def avgH (H : Subgroup L) (x : V) : V :=
  ((H.index : ℂ))⁻¹ • ∑ᶠ q : L ⧸ H, cv π L H x q

theorem avgH_refine {H H' : Subgroup L} {x : V} (hle : H' ≤ H) (hH : H ≤ stab π L x)
    [H'.FiniteIndex] : avgH π L H' x = avgH π L H x := by
  classical
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hrel := Subgroup.relIndex_mul_index hle
  haveI : (H'.subgroupOf H).FiniteIndex := by
    refine ⟨?_⟩
    intro h0
    have h4 : H'.index = 0 := by rw [← hrel]; simp [Subgroup.relIndex, h0]
    exact Subgroup.FiniteIndex.index_ne_zero h4
  haveI := Fintype.ofFinite (L ⧸ H)
  haveI := Fintype.ofFinite (L ⧸ H')
  haveI := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  unfold avgH
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let e := Subgroup.quotientEquivProdOfLE hle
  have hcv : ∀ q : L ⧸ H', cv π L H' x q = cv π L H x (e q).1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L (le_trans hle hH), show (e (QuotientGroup.mk a)).1 = QuotientGroup.mk a from rfl,
        cv_mk π L hH]
  have hsum : ∑ q : L ⧸ H', cv π L H' x q =
      (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) • ∑ q : L ⧸ H, cv π L H x q := by
    simp_rw [hcv]
    rw [Equiv.sum_comp e (fun p => cv π L H x p.1), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [Finset.smul_sum]
    simp [Nat.cast_smul_eq_nsmul]
  have hc : Fintype.card (H ⧸ H'.subgroupOf H) = H'.relIndex H := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hsum, hc, ← hrel, smul_smul]
  congr 1
  have h5 : (H'.relIndex H : ℂ) ≠ 0 := by
    have := Subgroup.FiniteIndex.index_ne_zero (H := H'.subgroupOf H)
    exact_mod_cast this
  push_cast
  field_simp

theorem stab_finiteIndex {x : V} (hx : (Set.range fun l : L => π (l : G) x).Finite) :
    (stab π L x).FiniteIndex := by
  haveI : Finite (Set.range fun l : L => π (l : G) x) := hx.to_subtype
  let F : L ⧸ stab π L x → Set.range fun l : L => π (l : G) x :=
    fun q => ⟨cv π L (stab π L x) x q, ⟨_, rfl⟩⟩
  have hF : Function.Injective F := by
    intro q1 q2 h
    induction q1 using QuotientGroup.induction_on with
    | H a =>
    induction q2 using QuotientGroup.induction_on with
    | H b =>
    have h' : π (a : G) x = π (b : G) x := by
      have := congrArg Subtype.val h
      simpa only [F, cv_mk π L le_rfl] using this
    apply QuotientGroup.eq.mpr
    rw [mem_stab]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply, ← h']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  haveI : Finite (L ⧸ stab π L x) := Finite.of_injective F hF
  exact Subgroup.finiteIndex_of_finite_quotient

theorem stab_le_add (x y : V) : stab π L x ⊓ stab π L y ≤ stab π L (x + y) := by
  intro l hl
  rw [mem_stab, map_add, (mem_stab π L).mp hl.1, (mem_stab π L).mp hl.2]

theorem stab_le_smul (c : ℂ) (x : V) : stab π L x ≤ stab π L (c • x) := by
  intro l hl
  rw [mem_stab, map_smul, (mem_stab π L).mp hl]

theorem avgH_add (H : Subgroup L) [H.FiniteIndex] (x y : V) :
    avgH π L H (x + y) = avgH π L H x + avgH π L H y := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_add, Finset.sum_add_distrib, smul_add]

theorem avgH_smul (H : Subgroup L) [H.FiniteIndex] (c : ℂ) (x : V) :
    avgH π L H (c • x) = c • avgH π L H x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum, smul_comm c]

noncomputable def avg (x : V) : V := avgH π L (stab π L x) x

theorem avg_eq {H : Subgroup L} {x : V} [H.FiniteIndex] (hH : H ≤ stab π L x) :
    avg π L x = avgH π L H x := (avgH_refine π L hH le_rfl).symm

theorem avgH_mem (D : Submodule ℂ V) (hD : ∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) (H : Subgroup L)
    [H.FiniteIndex] {x : V} (hx : x ∈ D) : avgH π L H x ∈ D := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH
  rw [finsum_eq_sum_of_fintype]
  exact D.smul_mem _ (D.sum_mem fun q _ => hD _ (q.out).2 x hx)

theorem avg_fixed {x : V} (hx : (stab π L x).FiniteIndex) (hfix : ∀ l ∈ L, π l x = x) :
    avg π L x = x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH
  have : ∀ q : L ⧸ stab π L x, cv π L (stab π L x) x q = x := fun q => hfix _ (q.out).2
  simp only [finsum_eq_sum_of_fintype, this, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h0 : ((stab π L x).index : ℂ) ≠ 0 := by exact_mod_cast hx.index_ne_zero
  rw [show Nat.card (L ⧸ stab π L x) = (stab π L x).index from rfl, inv_mul_cancel₀ h0, one_smul]

theorem avg_invariant {x : V} (hx : (stab π L x).FiniteIndex) (l : L) :
    π (l : G) (avg π L x) = avg π L x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH
  rw [finsum_eq_sum_of_fintype, map_smul, map_sum]
  congr 1
  have h : ∀ q : L ⧸ stab π L x, π (l : G) (cv π L (stab π L x) x q) =
      cv π L (stab π L x) x (l • q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L le_rfl, MulAction.Quotient.smul_mk, cv_mk π L le_rfl, smul_eq_mul, Subgroup.coe_mul, map_mul,
        Module.End.mul_apply]
  simp_rw [h]
  exact Equiv.sum_comp (MulAction.toPerm l) (cv π L (stab π L x) x)

theorem avg_add {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    avg π L (x + y) = avg π L x + avg π L y := by
  haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance
  rw [avg_eq π L (stab_le_add π L x y), avg_eq π L (inf_le_left : stab π L x ⊓ stab π L y ≤ stab π L x),
    avg_eq π L (inf_le_right : stab π L x ⊓ stab π L y ≤ stab π L y), avgH_add]

theorem avg_smul {x : V} (hx : (stab π L x).FiniteIndex) (c : ℂ) :
    avg π L (c • x) = c • avg π L x := by
  rw [avg_eq π L (stab_le_smul π L c x), avgH_smul]
  rfl

theorem avg_pair {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧
      avg π L x = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g x ∧
      avg π L y = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g y ∧
      Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ y = π (f g) y := by
  classical
  set N := (stab π L x ⊓ stab π L y).normalCore with hN
  have hNx : N ≤ stab π L x := le_trans (Subgroup.normalCore_le _) inf_le_left
  have hNy : N ≤ stab π L y := le_trans (Subgroup.normalCore_le _) inf_le_right
  haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance
  haveI : N.FiniteIndex := Subgroup.finiteIndex_normalCore _
  haveI := Fintype.ofFinite (L ⧸ N)
  let r : L ⧸ N → G := fun q => ((q.out : L) : G)
  have hr : Function.Injective r := by
    intro q1 q2 h
    have h1 : q1.out = q2.out := Subtype.ext h
    rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, h1]
  let s : Finset G := Finset.univ.image r
  have hcard : s.card = N.index := by
    rw [Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_eq_nat_card]; rfl
  have hsum : ∀ z : V, N ≤ stab π L z → avg π L z = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g z := by
    intro z hz
    have hzf : (stab π L z).FiniteIndex := Subgroup.finiteIndex_of_le hz
    rw [avg_eq π L hz, hcard, Finset.sum_image (fun a _ b _ h => hr h)]
    unfold avgH
    rw [finsum_eq_sum_of_fintype]
    rfl
  let f : G → G := fun g => if h : g ∈ L then
    (((((QuotientGroup.mk (⟨g, h⟩ : L) : L ⧸ N))⁻¹).out : L) : G) else g
  have hf : ∀ q : L ⧸ N, f (r q) = r q⁻¹ := by
    intro q
    simp only [f, r, Subtype.coe_eta, QuotientGroup.out_eq']
    rw [dif_pos (q.out).2]
  have hmem : ∀ g, g ∈ s ↔ ∃ q, r q = g := by
    intro g; simp [s]
  refine ⟨s, f, ?_, ?_, hsum x hNx, hsum y hNy, ?_, ?_⟩
  · exact ⟨r 1, (hmem _).mpr ⟨1, rfl⟩⟩
  · intro g hg
    obtain ⟨q, rfl⟩ := (hmem g).mp hg
    exact (q.out).2
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨q, rfl⟩ := (hmem g).mp hg
      rw [Finset.mem_coe, hf]
      exact (hmem _).mpr ⟨_, rfl⟩
    · intro g1 hg1 g2 hg2 h
      obtain ⟨q1, rfl⟩ := (hmem g1).mp hg1
      obtain ⟨q2, rfl⟩ := (hmem g2).mp hg2
      rw [hf, hf] at h
      rw [inv_injective (hr h)]
    · intro g hg
      obtain ⟨q, rfl⟩ := (hmem g).mp hg
      refine ⟨r q⁻¹, (hmem _).mpr ⟨_, rfl⟩, ?_⟩
      rw [hf, inv_inv]
  · intro g hg
    obtain ⟨q, rfl⟩ := (hmem g).mp hg
    rw [hf]
    have e1 : π (r q⁻¹) y = cv π L N y q⁻¹ := rfl
    have e2 : π (r q)⁻¹ y = cv π L N y (QuotientGroup.mk (q.out)⁻¹) := by
      rw [cv_mk π L hNy]; rfl
    rw [e1, e2, QuotientGroup.mk_inv, QuotientGroup.out_eq']

end GlobalTheory.OrbitAvg

open GlobalTheory.OrbitAvg in

theorem GlobalTheory.orbitAverage_exists : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (π : G →* Module.End ℂ V) (L : Subgroup G) (D : Submodule ℂ V),
    (∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) → (∀ x ∈ D, (Set.range fun l : L => π (l : G) x).Finite) →
    ∃ P : D →ₗ[ℂ] D, (∀ x : D, (∀ l ∈ L, π l (x : V) = x) → P x = x) ∧
      (∀ x : D, ∀ l ∈ L, π l (P x : V) = P x) ∧
      ∀ x y : D, ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧
        (P x : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (x : V) ∧
        (P y : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (y : V) ∧
        Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ (y : V) = π (f g) (y : V) := by
  intro G V _ _ _ π L D hD hfin
  have hfi : ∀ x : D, (stab π L (x : V)).FiniteIndex := fun x => stab_finiteIndex π L (hfin x x.2)
  let P : D →ₗ[ℂ] D :=
    { toFun := fun x => ⟨avg π L (x : V), by
        haveI := hfi x
        exact avgH_mem π L D hD _ x.2⟩
      map_add' := fun x y => Subtype.ext (avg_add π L (hfi x) (hfi y))
      map_smul' := fun c x => Subtype.ext (avg_smul π L (hfi x) c) }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x hx
    exact Subtype.ext (avg_fixed π L (hfi x) fun l hl => hx l hl)
  · intro x l hl
    exact avg_invariant π L (hfi x) ⟨l, hl⟩
  · intro x y
    exact avg_pair π L (hfi x) (hfi y)
