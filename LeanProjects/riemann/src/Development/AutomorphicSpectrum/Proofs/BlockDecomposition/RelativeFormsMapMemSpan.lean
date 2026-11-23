import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonLNegMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExceptionalIdealLeSpanPosDegree

set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub

theorem span_multi {K M N ι : Type} [Semiring K] [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    [Fintype ι] [DecidableEq ι] (F : (ι → M) → N) (T : Submodule K N)
    (hadd : ∀ (x : ι → M) (i : ι) (y z : M), F (Function.update x i (y + z)) =
      F (Function.update x i y) + F (Function.update x i z))
    (hsmul : ∀ (x : ι → M) (i : ι) (c : K) (y : M), F (Function.update x i (c • y)) =
      c • F (Function.update x i y))
    (V : ι → Set M) (h : ∀ x : ι → M, (∀ i, x i ∈ V i) → F x ∈ T)
    (x : ι → M) (hx : ∀ i, x i ∈ Submodule.span K (V i)) : F x ∈ T := by
  have key : ∀ s : Finset ι, ∀ x : ι → M, (∀ i ∈ s, x i ∈ Submodule.span K (V i)) →
      (∀ i, i ∉ s → x i ∈ V i) → F x ∈ T := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ h2; exact h x fun i => h2 i (by simp)
    | insert i s hi ih =>
      intro x h1 h2
      have claim : ∀ y ∈ Submodule.span K (V i), F (Function.update x i y) ∈ T := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          refine ih _ (fun j hj => ?_) (fun j hj => ?_)
          · have hne : j ≠ i := fun e => hi (e ▸ hj)
            rw [Function.update_of_ne hne]
            exact h1 j (Finset.mem_insert_of_mem hj)
          · by_cases e : j = i
            · subst e
              simpa using hy
            · rw [Function.update_of_ne e]
              exact h2 j (by simp [e, hj])
        | zero =>
          have h0 := hsmul x i 0 0
          rw [zero_smul, zero_smul] at h0
          rw [h0]
          exact T.zero_mem
        | add y z _ _ hy hz => rw [hadd]; exact T.add_mem hy hz
        | smul c y _ hy => rw [hsmul]; exact T.smul_mem c hy
      have h3 := claim (x i) (h1 i (Finset.mem_insert_self _ _))
      rwa [Function.update_eq_self] at h3
  exact key Finset.univ x (fun i _ => hx i) fun i hi => absurd (Finset.mem_univ i) hi

variable {K : Type} [Field K] {n d : ℕ}

def goodSpan (K : Type) [Field K] (n d : ℕ) (S : Finset (Fin d)) (a : ℕ) : Submodule K (Om K (Lr K n d) a) :=
  Submodule.span K {w : Om K (Lr K n d) a | ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}),
    good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D}

theorem enumD_surj {a : ℕ} (D : {D : Finset (E n d) // D.card = a}) (e : E n d) (he : e ∈ D.1) :
    ∃ i, enumD D i = e := by
  have h1 : finSumFinEquiv e ∈ D.1.map finSumFinEquiv.toEmbedding := Finset.mem_map_of_mem _ he
  have h2 := Finset.range_orderEmbOfFin (D.1.map finSumFinEquiv.toEmbedding) (k := a) (by simpa using D.2)
  have h3 : finSumFinEquiv e ∈ Set.range ((D.1.map finSumFinEquiv.toEmbedding).orderEmbOfFin (k := a)
      (by simpa using D.2)) := by
    rw [h2]; exact h1
  obtain ⟨i, hi⟩ := h3
  exact ⟨i, by simp [enumD, hi]⟩

theorem wedge_eq_or {a : ℕ} (f : Fin a → E n d) (D : {D : Finset (E n d) // D.card = a})
    (hf : Function.Injective f) (hD : ∀ i, f i ∈ D.1) :
    wedge (K := K) f = wedge (enumD D) ∨ wedge (K := K) f = -wedge (enumD D) := by
  have hex : ∀ i, ∃ j, enumD D j = f i := fun i => enumD_surj D _ (hD i)
  choose τ hτ using hex
  have hinj : Function.Injective τ := fun i j h => hf (by rw [← hτ, ← hτ, h])
  let σ : Equiv.Perm (Fin a) := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hinj)
  have h1 : wedge (K := K) f = Equiv.Perm.sign σ • wedge (K := K) (enumD D) := by
    have h2 : (fun i => dl (K := K) (f i)) = (fun i => dl (K := K) (enumD D i)) ∘ σ := by
      funext i
      simp only [Function.comp_apply]
      rw [← hτ i]
      rfl
    unfold wedge
    rw [h2]
    exact AlternatingMap.map_perm _ _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · left; rw [h1, h, one_smul]
  · right; rw [h1, h, Units.neg_smul, one_smul]

theorem term_mem (S : Finset (Fin d)) {a : ℕ} (g : Gam n d) (f : Fin a → E n d) (hf : Function.Injective f)
    (hx : ∀ l, 0 ≤ g (Sum.inl l)) (hxf : ∀ i l, f i = Sum.inl l → 0 < g (Sum.inl l))
    (ht : ∀ j, j ∉ S → 0 ≤ g (Sum.inr j)) (htf : ∀ i j, j ∉ S → f i = Sum.inr j → 0 < g (Sum.inr j))
    (hdeg : 1 ≤ tdeg g) : monL K g • wedge (K := K) f ∈ goodSpan K n d S a := by
  classical
  let D : {D : Finset (E n d) // D.card = a} :=
    ⟨Finset.univ.image f, by rw [Finset.card_image_of_injective _ hf]; simp⟩
  have hD : ∀ i, f i ∈ D.1 := fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)
  have hDf : ∀ e ∈ D.1, ∃ i, f i = e := fun e he => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 he
    exact ⟨i, hi⟩
  have hm : monW K g D ∈ goodSpan K n d S a := by
    refine Submodule.subset_span ⟨g, D, ⟨fun l => ⟨hx l, fun h0 hl => ?_⟩, hdeg⟩, ?_, rfl⟩
    · obtain ⟨i, hi⟩ := hDf _ hl
      have := hxf i l hi
      omega
    · intro j hj
      by_contra hS
      have h1 := ht j hS
      rcases (Finset.mem_filter.1 hj).2 with h2 | ⟨h2, h3⟩
      · omega
      · obtain ⟨i, hi⟩ := hDf _ h3
        have := htf i j hS hi
        omega
  rcases wedge_eq_or (K := K) f D hf hD with h | h
  · rw [h]; exact hm
  · rw [h, smul_neg]; exact Submodule.neg_mem _ hm

theorem prod_monL {ι : Type} (s : Finset ι) (c : ι → Gam n d) : ∏ i ∈ s, monL K (c i) = monL K (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LaurentD.monL_zero']
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, LaurentD.monL_add', ih]

theorem tdeg_sum {ι : Type} (s : Finset ι) (c : ι → Gam n d) : tdeg (∑ i ∈ s, c i) = ∑ i ∈ s, tdeg (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tdeg]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tdeg_add, ih]

theorem coord_pos {a : ℕ} (c₀ : Gam n d) (c : Fin a → Gam n d) (e : E n d) (h₀ : 0 ≤ c₀ e) (h : ∀ i, 0 ≤ c i e) :
    0 ≤ (c₀ + ∑ i, c i) e ∧ ∀ i, c i e ≠ 0 → 0 < (c₀ + ∑ i, c i) e := by
  have h1 : (c₀ + ∑ i, c i) e = c₀ e + ∑ i, c i e := by simp [Finset.sum_apply]
  rw [h1]
  refine ⟨add_nonneg h₀ (Finset.sum_nonneg fun i _ => h i), fun i hi => ?_⟩
  have h2 : c i e ≤ ∑ i, c i e := Finset.single_le_sum (f := fun i => c i e) (fun i _ => h i) (Finset.mem_univ i)
  have h3 : 0 < c i e := lt_of_le_of_ne (h i) (Ne.symm hi)
  omega

theorem form_expand {a : ℕ} (c₀ : Gam n d) (c : Fin a → Gam n d) :
    form K (monL K c₀) (fun k => monL K (c k)) =
      ∑ f : Fin a → E n d, (∏ k, c k (f k) : ℤ) • (monL K (c₀ + ∑ i, c i) • wedge (K := K) f) := by
  let W := (exteriorPower.ιMulti (Lr K n d) a (M := Ω[Lr K n d⁄K])).toMultilinearMap
  have s1 : exteriorPower.ιMulti (Lr K n d) a
      (fun k => monL K (c k) • ∑ e, (c k e) • (dl e : Ω[Lr K n d⁄K])) =
      (∏ k, monL K (c k)) • W (fun k => ∑ e, (c k e) • (dl e : Ω[Lr K n d⁄K])) :=
    W.map_smul_univ _ _
  have s2 : W (fun k => ∑ e, (c k e) • (dl e : Ω[Lr K n d⁄K])) =
      ∑ f : Fin a → E n d, W (fun k => (c k (f k)) • (dl (f k) : Ω[Lr K n d⁄K])) :=
    W.map_sum fun k e => (c k e) • (dl e : Ω[Lr K n d⁄K])
  have s3 : ∀ f : Fin a → E n d, W (fun k => (c k (f k)) • (dl (f k) : Ω[Lr K n d⁄K])) =
      (∏ k, c k (f k) : ℤ) • wedge (K := K) f := by
    intro f
    have h1 : (fun k => (c k (f k)) • (dl (f k) : Ω[Lr K n d⁄K])) =
        fun k => ((c k (f k) : ℤ) : Lr K n d) • (dl (f k) : Ω[Lr K n d⁄K]) :=
      funext fun k => (Int.cast_smul_eq_zsmul _ _ _).symm
    rw [h1, W.map_smul_univ, ← Int.cast_prod, Int.cast_smul_eq_zsmul]
    rfl
  unfold form
  simp only [LaurentD.D_monL]
  rw [s1, s2, prod_monL, smul_smul, ← LaurentD.monL_add', Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [s3, smul_comm]

theorem form_mon_mem (S : Finset (Fin d)) {a : ℕ} (c₀ : Gam n d) (c : Fin a → Gam n d)
    (h₀ : c₀ ∈ (cone S : AddSubmonoid (Gam n d))) (hc : ∀ i, c i ∈ (cone S : AddSubmonoid (Gam n d)))
    (ht : 1 ≤ tdeg c₀ ∨ ∃ k, 1 ≤ tdeg (c k)) :
    form K (monL K c₀) (fun k => monL K (c k)) ∈ goodSpan K n d S a := by
  rw [form_expand]
  refine Submodule.sum_mem _ fun f _ => ?_
  by_cases hf : Function.Injective f
  · by_cases hz : ∀ k, c k (f k) ≠ 0
    · refine zsmul_mem (term_mem S _ f hf ?_ ?_ ?_ ?_ ?_) _
      · exact fun l => (coord_pos c₀ c _ (h₀.1 l) fun i => (hc i).1 l).1
      · intro i l hl
        refine (coord_pos c₀ c _ (h₀.1 l) fun i => (hc i).1 l).2 i ?_
        rw [← hl]; exact hz i
      · exact fun j hj => (coord_pos c₀ c _ (h₀.2.1 j hj) fun i => (hc i).2.1 j hj).1
      · intro i j hj hl
        refine (coord_pos c₀ c _ (h₀.2.1 j hj) fun i => (hc i).2.1 j hj).2 i ?_
        rw [← hl]; exact hz i
      · rw [tdeg_add, tdeg_sum]
        have hnn : ∀ i, 0 ≤ tdeg (c i) := fun i => (hc i).2.2
        have h0 : 0 ≤ tdeg c₀ := h₀.2.2
        rcases ht with h | ⟨k, h⟩
        · have := Finset.sum_nonneg (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hnn i
          omega
        · have := Finset.single_le_sum (f := fun i => tdeg (c i)) (fun i _ => hnn i) (Finset.mem_univ k)
          omega
    · push_neg at hz
      obtain ⟨k, hk⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ k) hk, zero_smul]
      exact Submodule.zero_mem _
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hf
    have h0 : wedge (K := K) f = 0 :=
      (exteriorPower.ιMulti (Lr K n d) a (M := Ω[Lr K n d⁄K])).map_eq_zero_of_eq _ (congrArg dl hij) hne
    rw [h0, smul_zero, smul_zero]
    exact Submodule.zero_mem _

def MonS (K : Type) [Field K] (n : ℕ) {d : ℕ} (S : Finset (Fin d)) (q : Prop) : Set (R0 K n d S) :=
  {y | ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), (q → 1 ≤ tdeg g) ∧ y = mon K g hg}

theorem span_all (S : Finset (Fin d)) {q : Prop} (hq : ¬q) (x : R0 K n d S) :
    x ∈ Submodule.span K (MonS K n S q) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | single m c =>
    have h1 : (AddMonoidAlgebra.single m c : R0 K n d S) = c • mon K m.1 m.2 := by
      simp [mon, AddMonoidAlgebra.smul_single]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m.1, m.2, fun h => absurd h hq, rfl⟩)

theorem span_I (S : Finset (Fin d)) (q : Prop) {x : R0 K n d S} (hx : x ∈ I0 n K S) :
    x ∈ Submodule.span K (MonS K n S q) :=
  Submodule.span_mono (by rintro _ ⟨g, hg, h1, e⟩; exact ⟨g, hg, fun _ => h1, e⟩) (exceptional_ideal_le_span_pos_degree S x hx)

theorem mem_of_mons (S : Finset (Fin d)) {a : ℕ} (q₀ : Prop) (q : Fin a → Prop) (hq : q₀ ∨ ∃ k, q k)
    (y₀ : R0 K n d S) (h₀ : y₀ ∈ MonS K n S q₀) (y : Fin a → R0 K n d S) (hy : ∀ i, y i ∈ MonS K n S (q i)) :
    omMap (incl le_top) a (form K y₀ y) ∈ goodSpan K n d S a := by
  obtain ⟨c₀, hc₀, hq₀, rfl⟩ := h₀
  choose c hc hqc hy' using hy
  obtain rfl : y = fun i => mon K (c i) (hc i) := funext hy'
  rw [omMap_form]
  simp only [incl_mon]
  refine form_mon_mem S c₀ c hc₀ hc ?_
  rcases hq with h | ⟨k, h⟩
  · exact Or.inl (hq₀ h)
  · exact Or.inr ⟨k, hqc k h⟩

section Generic
variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem D_update {a : ℕ} (x : Fin a → A) (i : Fin a) (v : A) :
    (fun k => KaehlerDifferential.D K A (Function.update x i v k)) =
      Function.update (fun k => KaehlerDifferential.D K A (x k)) i (KaehlerDifferential.D K A v) := by
  funext k
  by_cases e : k = i
  · subst e; simp
  · simp [Function.update_of_ne e]

theorem form_update_add {a : ℕ} (y₀ : A) (x : Fin a → A) (i : Fin a) (u v : A) :
    form K y₀ (Function.update x i (u + v)) =
      form K y₀ (Function.update x i u) + form K y₀ (Function.update x i v) := by
  unfold form
  rw [D_update, D_update, D_update, map_add, AlternatingMap.map_update_add, smul_add]

theorem form_update_smul {a : ℕ} (y₀ : A) (x : Fin a → A) (i : Fin a) (c : K) (u : A) :
    form K y₀ (Function.update x i (c • u)) = c • form K y₀ (Function.update x i u) := by
  unfold form
  rw [D_update, D_update, Derivation.map_smul, ← algebraMap_smul A c (KaehlerDifferential.D K A u),
    AlternatingMap.map_update_smul, smul_comm, algebraMap_smul]

theorem form_multi {N : Type} [AddCommMonoid N] [Module K N] {a : ℕ} (Φ : Om K A a →ₗ[K] N) (T : Submodule K N)
    (y₀ : A) (V : Fin a → Set A) (h : ∀ x : Fin a → A, (∀ i, x i ∈ V i) → Φ (form K y₀ x) ∈ T)
    (y : Fin a → A) (hy : ∀ i, y i ∈ Submodule.span K (V i)) : Φ (form K y₀ y) ∈ T :=
  span_multi (fun x => Φ (form K y₀ x)) T
    (fun x i u v => by
      show Φ _ = Φ _ + Φ _
      rw [form_update_add, map_add])
    (fun x i c u => by
      show Φ _ = c • Φ _
      rw [form_update_smul, map_smul])
    V h y hy

end Generic

theorem mem_of_mon_spans (S : Finset (Fin d)) {a : ℕ} (q₀ : Prop) (q : Fin a → Prop) (hq : q₀ ∨ ∃ k, q k)
    (y₀ : R0 K n d S) (h₀ : y₀ ∈ MonS K n S q₀) (y : Fin a → R0 K n d S)
    (hy : ∀ i, y i ∈ Submodule.span K (MonS K n S (q i))) :
    omMap (incl le_top) a (form K y₀ y) ∈ goodSpan K n d S a := by
  have hle : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤ := le_top
  have h := form_multi (K := K) (A := R0 K n d S) (N := Om K (Lr K n d) a) (omMap (incl hle) a)
    (goodSpan K n d S a) y₀ (fun i => MonS K n S (q i)) (fun x hx => mem_of_mons S q₀ q hq y₀ h₀ x hx) y
  exact h hy

theorem mem_of_spans (S : Finset (Fin d)) {a : ℕ} (q₀ : Prop) (q : Fin a → Prop) (hq : q₀ ∨ ∃ k, q k)
    (y₀ : R0 K n d S) (h₀ : y₀ ∈ Submodule.span K (MonS K n S q₀)) (y : Fin a → R0 K n d S)
    (hy : ∀ i, y i ∈ Submodule.span K (MonS K n S (q i))) :
    omMap (incl le_top) a (form K y₀ y) ∈ goodSpan K n d S a := by
  induction h₀ using Submodule.span_induction with
  | mem y₀ h₀ =>
    exact mem_of_mon_spans S q₀ q hq y₀ h₀ y hy
  | zero =>
    have h1 : form K (0 : R0 K n d S) y = 0 := by unfold form; rw [zero_smul]
    rw [h1, map_zero]
    exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
    have h1 : form K (u + v) y = form K u y + form K v y := by unfold form; rw [add_smul]
    rw [h1, map_add]
    exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
    have h1 : form K (c • u) y = c • form K u y := by unfold form; rw [smul_assoc]
    rw [h1, map_smul]
    exact Submodule.smul_mem _ _ hu

theorem gen_mem (S : Finset (Fin d)) {a : ℕ} (g₀ : R0 K n d S) (g : Fin a → R0 K n d S)
    (hg : g₀ ∈ I0 n K S ∨ ∃ k, g k ∈ I0 n K S) :
    omMap (incl le_top) a (form K g₀ g) ∈ goodSpan K n d S a := by
  rcases hg with h | ⟨k, hk⟩
  · exact mem_of_spans S True (fun _ => False) (Or.inl trivial) g₀ (span_I S _ h) g
      fun i => span_all S (by simp) _
  · refine mem_of_spans S False (fun i => i = k) (Or.inr ⟨k, rfl⟩) g₀ (span_all S (by simp) _) g fun i => ?_
    by_cases e : i = k
    · subst e
      exact span_I S _ hk
    · exact span_all S e _

theorem relOm_image_mem_span : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ) (ω : Om K (R0 K n d S) a),
    ω ∈ relOm K (I0 n K S) a → omMap (incl le_top) a ω ∈ Submodule.span K {w : Om K (Lr K n d) a |
      ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D} := by
  intro K _ n d S a ω hω
  have key : ∀ r : R0 K n d S, omMap (incl le_top) a (r • ω) ∈ goodSpan K n d S a := by
    unfold relOm at hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, g, hg, rfl⟩ := hx
      intro r
      have h1 : r • form K g₀ g = form K (r * g₀) g := by unfold form; rw [smul_smul]
      rw [h1]
      refine gen_mem S _ g ?_
      rcases hg with h | h
      · exact Or.inl (Ideal.mul_mem_left _ r h)
      · exact Or.inr h
    | zero => intro r; rw [smul_zero, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro r; rw [smul_add, map_add]; exact Submodule.add_mem _ (hx r) (hy r)
    | smul c x _ hx => intro r; rw [smul_smul]; exact hx (r * c)
  have h1 := key 1
  rw [one_smul] at h1
  exact h1

end GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub
