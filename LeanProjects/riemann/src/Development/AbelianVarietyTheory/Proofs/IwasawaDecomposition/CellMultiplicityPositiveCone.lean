import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section
namespace GlobalTheory.PolFan
namespace ConsMult

variable {M : Type} [AddCommGroup M]

def sat (P : Submodule ℤ M) : Submodule ℤ M := (Submodule.torsion ℤ (M ⧸ P)).comap P.mkQ

theorem mem_sat {P : Submodule ℤ M} {x : M} : x ∈ sat P ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ P := by
  simp only [sat, Submodule.mem_comap, Submodule.mkQ_apply, Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨n, hn⟩, h⟩
    refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
    rw [Submonoid.smul_def] at h
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact h
  · rintro ⟨n, hn, h⟩
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    rw [Submonoid.smul_def]
    show n • Submodule.Quotient.mk x = (0 : M ⧸ P)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact h

theorem le_sat (P : Submodule ℤ M) : P ≤ sat P := fun x hx => mem_sat.2 ⟨1, one_ne_zero, by simpa using hx⟩

theorem sat_eq {E P : Submodule ℤ M} (hEP : E ≤ P) (hP : P ≤ sat E) : sat P = sat E := by
  ext x
  rw [mem_sat, mem_sat]
  constructor
  · rintro ⟨n, hn, h⟩
    obtain ⟨k, hk, h'⟩ := mem_sat.1 (hP h)
    exact ⟨k * n, mul_ne_zero hk hn, by rw [mul_smul]; exact h'⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, hEP h⟩

theorem card_torsion_eq_relIndex (P : Submodule ℤ M) :
    Nat.card (Submodule.torsion ℤ (M ⧸ P)) = P.toAddSubgroup.relIndex (sat P).toAddSubgroup := by
  let f : (sat P).toAddSubgroup →+ Submodule.torsion ℤ (M ⧸ P) :=
    { toFun := fun x => ⟨P.mkQ x.1, x.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : f.ker = P.toAddSubgroup.addSubgroupOf (sat P).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    change (⟨P.mkQ x.1, x.2⟩ : Submodule.torsion ℤ (M ⧸ P)) = 0 ↔ x.1 ∈ P
    rw [← Subtype.coe_inj]
    exact Submodule.Quotient.mk_eq_zero P
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv).symm

theorem relIndex_cons_smul {p : ℕ} (v : M) (w : Fin p → M) (n : ℤ)
    (hli : LinearIndependent ℤ (Fin.cons v w : Fin (p + 1) → M)) :
    (Submodule.span ℤ (Set.range (Fin.cons (n • v) w : Fin (p + 1) → M))).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range (Fin.cons v w : Fin (p + 1) → M))).toAddSubgroup = n.natAbs := by
  set u : Fin (p + 1) → M := Fin.cons v w with hu
  set K := Submodule.span ℤ (Set.range u)
  set K' := Submodule.span ℤ (Set.range (Fin.cons (n • v) w : Fin (p + 1) → M))
  let b := Module.Basis.span hli
  have hb : ∀ i, (b i : M) = u i := fun i => by simp [b, Module.Basis.span_apply]
  let f : K →ₗ[ℤ] ℤ := b.coord 0
  have hf0 : f (b 0) = 1 := by simp [f]
  have hfs : ∀ i : Fin p, f (b i.succ) = 0 := fun i => by
    simp [f, Finsupp.single_apply, Fin.succ_ne_zero]
  have hmem : ∀ x : K, (x : M) ∈ K' ↔ n ∣ f x := by
    intro x
    constructor
    · intro hx
      let S' : Submodule ℤ K := Submodule.comap f (Ideal.span ({n} : Set ℤ))
      have hle : K' ≤ S'.map K.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases ?_ (fun i => ?_) i
        · refine ⟨n • b 0, ?_, ?_⟩
          · simp [S', Ideal.mem_span_singleton, hf0]
          · simp [hb, u]
        · refine ⟨b i.succ, ?_, ?_⟩
          · simp [S', hfs]
          · simp [hb, u]
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = x := Subtype.ext hyx
      subst this
      simpa [S', Ideal.mem_span_singleton] using hy
    · rintro ⟨q, hq⟩
      have hx : (x : M) = ∑ i, b.repr x i • u i := by
        have e0 := congrArg Subtype.val (b.sum_repr x)
        rw [← e0, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, hb]
      rw [hx, Fin.sum_univ_succ]
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => ?_)
      · have h0 : b.repr x 0 = f x := rfl
        rw [h0, hq, mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp [u]⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.succ, by simp [u]⟩)
  have hsurj : Function.Surjective f.toAddMonoidHom := fun t => ⟨t • b 0, by simp [hf0]⟩
  have heq : K'.toAddSubgroup.addSubgroupOf K.toAddSubgroup =
      (AddSubgroup.zmultiples n).comap f.toAddMonoidHom := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, Int.mem_zmultiples_iff]
    exact hmem x
  rw [AddSubgroup.relIndex, heq, AddSubgroup.index_comap_of_surjective _ hsurj, Int.index_zmultiples]

theorem card_torsion_cons_mul {p : ℕ} (v β : M) (w : Fin p → M) (k a : ℤ) (b : Fin p → ℤ) (hk : k ≠ 0) (ha : a ≠ 0)
    (hli : LinearIndependent ℤ (Fin.cons v w : Fin (p + 1) → M)) (hrel : k • β = a • v + ∑ i, b i • w i) :
    k.natAbs * Nat.card (Submodule.torsion ℤ (M ⧸ Submodule.span ℤ (Set.range (Fin.cons β w : Fin (p + 1) → M)))) =
      a.natAbs * Nat.card (Submodule.torsion ℤ (M ⧸ Submodule.span ℤ (Set.range (Fin.cons v w : Fin (p + 1) → M)))) := by
  have hli' : LinearIndependent ℤ (Fin.cons β w : Fin (p + 1) → M) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Fin.cons_zero, Fin.cons_succ] at hg
    have h2 : (g 0 * a) • v + ∑ i, (g 0 * b i + k * g i.succ) • w i = 0 := by
      have e1 := congrArg (k • ·) hg
      simp only [smul_add, smul_zero, Finset.smul_sum, smul_smul] at e1
      rw [mul_comm k (g 0), mul_smul, hrel] at e1
      rw [← e1]
      simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
      abel
    have h3 := hli (Fin.cons (g 0 * a) fun i => g 0 * b i + k * g i.succ) (by
      rw [Fin.sum_univ_succ]; simpa using h2)
    have hg0 : g 0 = 0 := by
      have := h3 0
      simp only [Fin.cons_zero, mul_eq_zero] at this
      tauto
    intro i
    refine Fin.cases hg0 (fun i => ?_) i
    have := h3 i.succ
    simp only [Fin.cons_succ, hg0, zero_mul, zero_add, mul_eq_zero] at this
    tauto
  set D := Submodule.span ℤ (Set.range (Fin.cons v w : Fin (p + 1) → M)) with hD
  set N := Submodule.span ℤ (Set.range (Fin.cons β w : Fin (p + 1) → M)) with hN
  set E := Submodule.span ℤ (Set.range (Fin.cons (k • β) w : Fin (p + 1) → M)) with hE
  have hw : ∀ P : Submodule ℤ M, (∀ i, w i ∈ P) → ∑ i, b i • w i ∈ P := fun P h =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)
  have hwE : ∀ i, w i ∈ E := fun i => Submodule.subset_span ⟨i.succ, by simp⟩
  have hkE : k • β ∈ E := Submodule.subset_span ⟨0, by simp⟩
  have haE : a • v ∈ E := by
    have : a • v = k • β - ∑ i, b i • w i := by rw [hrel]; abel
    rw [this]; exact sub_mem hkE (hw _ hwE)
  have hE' : E = Submodule.span ℤ (Set.range (Fin.cons (a • v) w : Fin (p + 1) → M)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero, SetLike.mem_coe]
        rw [hrel]
        exact add_mem (Submodule.subset_span ⟨0, by simp⟩) (hw _ fun i => Submodule.subset_span ⟨i.succ, by simp⟩)
      · exact Submodule.subset_span ⟨i.succ, by simp⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using haE
      · simpa using hwE i
  have hED : E ≤ D := by
    rw [hE', Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using Submodule.smul_mem D a (Submodule.subset_span ⟨0, by simp⟩)
    · exact Submodule.subset_span ⟨i.succ, by simp⟩
  have hEN : E ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using Submodule.smul_mem N k (Submodule.subset_span ⟨0, by simp⟩)
    · exact Submodule.subset_span ⟨i.succ, by simp⟩
  have hDs : D ≤ sat E := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact mem_sat.2 ⟨a, ha, by simpa using haE⟩
    · exact le_sat E (by simpa using hwE i)
  have hNs : N ≤ sat E := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact mem_sat.2 ⟨k, hk, by simpa using hkE⟩
    · exact le_sat E (by simpa using hwE i)
  have h1 := card_torsion_eq_relIndex D
  rw [sat_eq hED hDs] at h1
  have h2 := card_torsion_eq_relIndex N
  rw [sat_eq hEN hNs] at h2
  rw [h1, h2, ← relIndex_cons_smul β w k hli', ← relIndex_cons_smul v w a hli, ← hE']
  change E.toAddSubgroup.relIndex N.toAddSubgroup * _ = E.toAddSubgroup.relIndex D.toAddSubgroup * _
  rw [AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hEN) ((Submodule.toAddSubgroup_le _ _).2 hNs),
    AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hED) ((Submodule.toAddSubgroup_le _ _).2 hDs)]

theorem exists_int_rel {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (hli : LinearIndependent ℤ δ)
    (hc : toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X)) :
    ∃ (k : ℤ) (a : Fin m → ℤ), k ≠ 0 ∧ k • β = ∑ i, a i • δ i ∧ ∀ i, (k : ℝ) * c i = a i := by
  have hind : ∀ (d : Fin 0 → ℤ) (g : Fin m → ℤ),
      ∑ i, g i • (δ i : LinearMap.BilinForm ℤ X) = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) → g = 0 :=
    fun d g hg => by
      refine funext (Fintype.linearIndependent_iff.1 hli g (Subtype.ext ?_))
      simpa using hg
  have hdep : ¬ LinearIndependent ℤ (Fin.cons β δ : Fin (m + 1) → balForms bar X) := by
    intro h
    have hind' : ∀ (d : Fin 0 → ℤ) (g : Fin (m + 1) → ℤ),
        ∑ i, g i • (((Fin.cons β δ : Fin (m + 1) → balForms bar X) i : balForms bar X) : LinearMap.BilinForm ℤ X) =
          ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) → g = 0 :=
      fun d g hg => by
        refine funext (Fintype.linearIndependent_iff.1 h g (Subtype.ext ?_))
        simpa using hg
    have := eq_zero_of_toReal_rel hind' (r := Fin.cons 1 (-c)) (s := 0) (by
      rw [Fin.sum_univ_succ]
      simp [hc])
    simpa using congrFun this 0
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hdep
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have hg0 : g 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hg
    have := Fintype.linearIndependent_iff.1 hli _ hg
    exact hi0 (Fin.cases h0 (fun i => this i) i0)
  have hb : g 0 • β = -∑ i, g i.succ • δ i := eq_neg_of_add_eq_zero_left hg
  refine ⟨g 0 * g 0, fun i => -(g 0 * g i.succ), mul_ne_zero hg0 hg0, ?_, ?_⟩
  · rw [mul_smul, hb, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, neg_smul]
  · have hr := eq_zero_of_toReal_rel hind (r := fun i => (g 0 : ℝ) * c i + g i.succ) (s := 0) (by
      ext x y
      have h1 := LinearMap.congr_fun₂ hc x y
      have h2 := LinearMap.congr_fun₂ (congrArg Subtype.val hg) x y
      simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
        Submodule.coe_sum, LinearMap.add_apply, smul_eq_mul, ZeroMemClass.coe_zero, LinearMap.zero_apply] at h1 h2 ⊢
      simp only [Fin.sum_univ_zero]
      have h3 : ((g 0 * (β : LinearMap.BilinForm ℤ X) x y + ∑ i, g i.succ * (δ i : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) = 0 := by
        exact_mod_cast h2
      push_cast at h3
      rw [h1] at h3
      rw [Finset.mul_sum, ← Finset.sum_add_distrib] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
    intro i
    have := congrFun hr i
    simp only [Pi.zero_apply] at this
    push_cast
    linear_combination (g 0 : ℝ) * this

theorem cellMult_cons_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    0 < c j → (∀ i, i ∈ Set.range e ↔ i ≠ j) → 0 < cellMult bar δ →
    (cellMult bar (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) : ℝ) = c j * cellMult bar δ := by
  intro O _ bar X _ _ m p δ β c j e hli hc hcj he _
  obtain ⟨k, a, hk, hrel, hca⟩ := exists_int_rel δ β c hli hc

  have hinj : Function.Injective (Fin.cons j e : Fin (p + 1) → Fin m) := by
    rw [Fin.cons_injective_iff]
    exact ⟨fun h => (he j).1 h rfl, e.injective⟩
  have hsurj : Function.Surjective (Fin.cons j e : Fin (p + 1) → Fin m) := by
    intro i
    by_cases hij : i = j
    · exact ⟨0, by simp [hij]⟩
    · obtain ⟨l, hl⟩ := (he i).2 hij
      exact ⟨l.succ, by simp [hl]⟩
  let σ : Fin (p + 1) ≃ Fin m := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  have hσ0 : σ 0 = j := by
    show (Fin.cons j e : Fin (p + 1) → Fin m) 0 = j
    exact Fin.cons_zero _ _
  have hσs : ∀ l, σ l.succ = e l := fun l => by
    show (Fin.cons j e : Fin (p + 1) → Fin m) l.succ = e l
    exact Fin.cons_succ _ _ _
  have hσ : (Fin.cons (δ j) (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) = δ ∘ σ := by
    funext r
    refine Fin.cases ?_ (fun l => ?_) r
    · simp [hσ0]
    · simp [hσs]
  have hli' : LinearIndependent ℤ (Fin.cons (δ j) (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) := by
    rw [hσ]; exact hli.comp σ σ.injective
  have hrange : Set.range (Fin.cons (δ j) (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) = Set.range δ := by
    rw [hσ]; exact EquivLike.range_comp δ σ
  have hsum : ∀ f : Fin m → balForms bar X, ∑ i, f i = f j + ∑ l, f (e l) := fun f => by
    rw [← σ.sum_comp, Fin.sum_univ_succ, hσ0]
    simp only [hσs]
  have hrel' : k • β = a j • δ j + ∑ l, a (e l) • δ (e l) := by rw [hrel, hsum (fun i => a i • δ i)]
  have haj : (a j : ℝ) = k * c j := (hca j).symm
  have haj0 : a j ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at haj
    exact (mul_ne_zero (by exact_mod_cast hk) hcj.ne') haj.symm
  have key := card_torsion_cons_mul (δ j) β (fun l => δ (e l)) k (a j) (fun l => a (e l)) hk haj0 hli' hrel'
  rw [hrange] at key
  have key' : (k.natAbs : ℝ) * (cellMult bar (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) : ℝ) =
      ((a j).natAbs : ℝ) * (cellMult bar δ : ℝ) := by
    unfold cellMult; exact_mod_cast key
  have hkabs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have haabs : (((a j).natAbs : ℕ) : ℝ) = |(k : ℝ)| * c j := by
    rw [Nat.cast_natAbs, Int.cast_abs, haj, abs_mul, abs_of_pos hcj]
  rw [hkabs, haabs, mul_assoc] at key'
  exact mul_left_cancel₀ (abs_ne_zero.2 (by exact_mod_cast hk)) key'

end ConsMult
end GlobalTheory.PolFan
