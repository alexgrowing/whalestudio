import Mathlib

noncomputable section

namespace PositivityTheory.ThKG.Fub

open MeasureTheory Topology Filter
open scoped NNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

structure Split (S A B : Subgroup G) (p q : G →* G) : Prop where
  cp : Continuous p
  cq : Continuous q
  cA : IsClosed (A : Set G)
  cB : IsClosed (B : Set G)
  cS : IsClosed (S : Set G)
  mA : ∀ g ∈ S, p g ∈ A
  mB : ∀ g ∈ S, q g ∈ B
  mul : ∀ g ∈ S, p g * q g = g
  hA : ∀ a ∈ A, a ∈ S ∧ p a = a ∧ q a = 1
  hB : ∀ b ∈ B, b ∈ S ∧ q b = b ∧ p b = 1

instance scSub (S : Subgroup G) : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _

variable {S A B : Subgroup G} {p q : G →* G}

def Split.e (h : Split S A B p q) : S ≃ₜ* A × B where
  toFun g := (⟨p g, h.mA _ g.2⟩, ⟨q g, h.mB _ g.2⟩)
  invFun x := ⟨x.1 * x.2, S.mul_mem (h.hA _ x.1.2).1 (h.hB _ x.2.2).1⟩
  left_inv g := Subtype.ext (h.mul _ g.2)
  right_inv x := Prod.ext (Subtype.ext (by simp [(h.hA _ x.1.2).2.1, (h.hB _ x.2.2).2.2]))
    (Subtype.ext (by simp [(h.hA _ x.1.2).2.2, (h.hB _ x.2.2).2.1]))
  map_mul' a b := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
  continuous_toFun := ((h.cp.comp continuous_subtype_val).subtype_mk _).prodMk ((h.cq.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem Split.fub (h : Split S A B p q) (μ : Measure S) (α : Measure A) (β : Measure B) [μ.IsHaarMeasure] [α.IsHaarMeasure]
    [β.IsHaarMeasure] : ∃ c : ℝ≥0, c ≠ 0 ∧
      (∀ f g : G → ℂ, Integrable (fun a : A => f a) α → Integrable (fun b : B => g b) β →
        Integrable (fun x : S => f (p x) * g (q x)) μ ∧
          ∫ x : S, f (p x) * g (q x) ∂μ = c * ((∫ a : A, f a ∂α) * ∫ b : B, g b ∂β)) ∧
      ∀ U : Set G, MeasurableSet U → (∀ g ∈ S, g ∈ U ↔ p g ∈ U ∧ q g ∈ U) →
        μ {x | x.1 ∈ U} = c * (α {x | x.1 ∈ U} * β {x | x.1 ∈ U}) := by
  haveI : LocallyCompactSpace A := h.cA.locallyCompactSpace
  haveI : LocallyCompactSpace B := h.cB.locallyCompactSpace
  haveI : LocallyCompactSpace S := h.cS.locallyCompactSpace
  have hm : (μ.map h.e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ h.e
  set c := Measure.haarScalarFactor (μ.map h.e) (α.prod β) with hc
  have he : μ.map h.e = c • α.prod β := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have hme : MeasurableEmbedding h.e := h.e.toHomeomorph.measurableEmbedding
  refine ⟨c, hc0, fun f g hf hg => ?_, fun U hU hh => ?_⟩
  · have h1 : Integrable (fun x : A × B => f x.1 * g x.2) (μ.map h.e) := by
      rw [he]; exact (hf.mul_prod hg).smul_measure_nnreal
    refine ⟨(hme.integrable_map_iff.1 h1 :), ?_⟩
    have h2 := hme.integral_map (μ := μ) (fun x : A × B => f x.1 * g x.2)
    rw [he, integral_smul_nnreal_measure, integral_prod_mul (fun a : A => f a) (fun b : B => g b)] at h2
    refine Eq.trans ?_ (h2.symm.trans ?_)
    · rfl
    · simp [NNReal.smul_def]
  · have h2 : {x : S | x.1 ∈ U} = h.e ⁻¹' ({x : A | x.1 ∈ U} ×ˢ {x : B | x.1 ∈ U}) := Set.ext fun x => hh _ x.2
    rw [h2, ← hme.map_apply, he, Measure.smul_apply, Measure.prod_prod]
    rfl

theorem exists_haar (S : Subgroup G) (hS : IsClosed (S : Set G)) (U : Set G) (h1 : (1 : G) ∈ U)
    (hc : IsCompact {x : S | x.1 ∈ U}) (ho : IsOpen {x : S | x.1 ∈ U}) :
    ∃ μ : Measure S, μ.IsHaarMeasure ∧ μ {x | x.1 ∈ U} = 1 := by
  haveI : LocallyCompactSpace S := hS.locallyCompactSpace
  let K : TopologicalSpace.PositiveCompacts S := ⟨⟨_, hc⟩, ⟨1, by simpa [ho.interior_eq] using h1⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

variable {R : Type} [CommRing R]

structure Sys (P : R → G →* G) (K : Subgroup G) (U : Set G) (good : R → Prop) : Prop where
  cont : ∀ a, good a → Continuous (P a)
  comp : ∀ a b, good a → good b → ∀ g, P a (P b g) = P (a * b) g
  zero : ∀ g, P 0 g = 1
  add : ∀ a b, good a → good b → a * b = 0 → good (a + b) ∧ ∀ g, P (a + b) g = P a g * P b g
  idem : ∀ a, good a → a * a = a
  cK : IsClosed (K : Set G)
  mK : ∀ a, good a → ∀ g ∈ K, P a g ∈ K
  mU : MeasurableSet U
  one : (1 : G) ∈ U
  mul : ∀ g ∈ U, ∀ g' ∈ U, g * g' ∈ U
  pU : ∀ a, good a → ∀ g ∈ U, P a g ∈ U

def part (P : R → G →* G) (K : Subgroup G) (a : R) : Subgroup G := K ⊓ (P a).eqLocus (MonoidHom.id G)

theorem mem_part {P : R → G →* G} {K : Subgroup G} {a : R} {g : G} : g ∈ part P K a ↔ g ∈ K ∧ P a g = g := Iff.rfl

variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}

theorem Sys.closed (s : Sys P K U good) {a : R} (ha : good a) : IsClosed (part P K a : Set G) :=
  s.cK.inter (isClosed_eq (s.cont a ha) continuous_id)

theorem Sys.split (s : Sys P K U good) {a b : R} (ha : good a) (hb : good b) (hab : a * b = 0) :
    Split (part P K (a + b)) (part P K a) (part P K b) (P a) (P b) where
  cp := s.cont a ha
  cq := s.cont b hb
  cA := s.closed ha
  cB := s.closed hb
  cS := s.closed (s.add a b ha hb hab).1
  mA g hg := ⟨s.mK a ha g hg.1, by show P a (P a g) = P a g; rw [s.comp a a ha ha, s.idem a ha]⟩
  mB g hg := ⟨s.mK b hb g hg.1, by show P b (P b g) = P b g; rw [s.comp b b hb hb, s.idem b hb]⟩
  mul g hg := ((s.add a b ha hb hab).2 g).symm.trans hg.2
  hA g hg := by
    have h0 : P a g = g := hg.2
    have h1 : P b g = 1 := by rw [← h0, s.comp b a hb ha, mul_comm, hab, s.zero]
    exact ⟨⟨hg.1, by show P (a + b) g = g; rw [(s.add a b ha hb hab).2, h0, h1, mul_one]⟩, h0, h1⟩
  hB g hg := by
    have h0 : P b g = g := hg.2
    have h1 : P a g = 1 := by rw [← h0, s.comp a b ha hb, hab, s.zero]
    exact ⟨⟨hg.1, by show P (a + b) g = g; rw [(s.add a b ha hb hab).2, h0, h1, one_mul]⟩, h0, h1⟩

def CO (P : R → G →* G) (K : Subgroup G) (U : Set G) (a : R) : Prop :=
  IsCompact {x : part P K a | x.1 ∈ U} ∧ IsOpen {x : part P K a | x.1 ∈ U}

theorem Sys.good_sum (s : Sys P K U good) {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ i, good (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (c : R) (hc : good c) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0) :
    good (∑ i ∈ T, e i + c) := by
  induction T using Finset.induction_on with
  | empty => simpa using hc
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, add_assoc]
    refine (s.add _ _ (he i) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj)) ?_).1
    rw [mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)), hT i (Finset.mem_insert_self _ _),
      add_zero]

theorem Sys.prod (s : Sys P K U good) {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ i, good (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (c : R) (hc : good c) (α : ∀ i, Measure (part P K (e i)))
    (hα : ∀ i, (α i).IsHaarMeasure ∧ α i {x | x.1 ∈ U} = 1) (β : Measure (part P K c))
    (hβ : β.IsHaarMeasure ∧ β {x | x.1 ∈ U} = 1) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0)
    (hCO : ∀ T' ⊆ T, CO P K U (∑ i ∈ T', e i + c)) (b : R) (hb : b = ∑ i ∈ T, e i + c)
    (μ : Measure (part P K b)) (hμ : μ.IsHaarMeasure ∧ μ {x | x.1 ∈ U} = 1) (f : ι → G → ℂ) (g : G → ℂ)
    (hf : ∀ i ∈ T, Integrable (fun x : part P K (e i) => f i x) (α i)) (hg : Integrable (fun x : part P K c => g x) β) :
    Integrable (fun x : part P K b => (∏ i ∈ T, f i (P (e i) x)) * g (P c x)) μ ∧
      ∫ x : part P K b, (∏ i ∈ T, f i (P (e i) x)) * g (P c x) ∂μ =
        (∏ i ∈ T, ∫ x : part P K (e i), f i x ∂(α i)) * ∫ x : part P K c, g x ∂β := by
  induction T using Finset.induction_on generalizing b with
  | empty =>
    obtain rfl : b = c := by simpa using hb
    haveI := hμ.1; haveI := hβ.1
    haveI : LocallyCompactSpace (part P K b) := (s.closed hc).locallyCompactSpace
    have h1 := Measure.isMulLeftInvariant_eq_smul μ β
    have h2 : Measure.haarScalarFactor μ β = 1 := by
      have := hμ.2
      rw [h1, Measure.smul_apply, hβ.2] at this
      simpa using this
    rw [h2, one_smul] at h1
    have h3 : (fun x : part P K b => (∏ i ∈ (∅ : Finset ι), f i (P (e i) x)) * g (P b x)) = fun x : part P K b => g x := by
      funext x; rw [show P b x = x from x.2.2]; simp
    rw [h3, h1]; exact ⟨hg, by simp⟩
  | insert i T hi ih =>
    have hT' : ∀ j ∈ T, e j * c = 0 := fun j hj => hT j (Finset.mem_insert_of_mem hj)
    have hg' := s.good_sum e he ho c hc T hT'
    set b' := ∑ j ∈ T, e j + c with hb'
    have h0 : e i * b' = 0 := by
      rw [hb', mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)),
        hT i (Finset.mem_insert_self _ _), add_zero]
    obtain rfl : b = e i + b' := by rw [hb, Finset.sum_insert hi, add_assoc]
    obtain ⟨μ', hμ'⟩ := exists_haar _ (s.closed hg') U s.one (hCO T (Finset.subset_insert _ _)).1 (hCO T (Finset.subset_insert _ _)).2
    obtain ⟨i1, i2⟩ := ih hT' (fun T' h => hCO T' (h.trans (Finset.subset_insert _ _))) b' rfl μ' hμ'
      (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    haveI := hμ.1; haveI := hμ'.1; haveI := (hα i).1
    obtain ⟨k, -, k1, k2⟩ := (s.split (he i) hg' h0).fub μ (α i) μ'
    have hk : k = 1 := by
      have := k2 U s.mU fun x hx => ⟨fun h => ⟨s.pU _ (he i) _ h, s.pU _ hg' _ h⟩, fun h => by
        rw [← (s.split (he i) hg' h0).mul x hx]; exact s.mul _ h.1 _ h.2⟩
      rw [hμ.2, (hα i).2, hμ'.2] at this
      simpa using this.symm
    obtain ⟨j1, j2⟩ := k1 (f i) (fun y => (∏ j ∈ T, f j (P (e j) y)) * g (P c y)) (hf i (Finset.mem_insert_self _ _)) i1
    have h3 : (fun x : part P K (e i + b') => (∏ j ∈ insert i T, f j (P (e j) x)) * g (P c x)) =
        fun x : part P K (e i + b') => f i (P (e i) x) * ((∏ j ∈ T, f j (P (e j) (P b' x))) * g (P c (P b' x))) := by
      funext x
      rw [Finset.prod_insert hi, mul_assoc, s.comp c b' hc hg']
      have e1 : c * b' = c := by
        rw [hb', mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => by rw [mul_comm]; exact hT' j hj, zero_add, s.idem c hc]
      rw [e1]
      congr 2
      refine Finset.prod_congr rfl fun j hj => ?_
      have e2 : e j * b' = e j := by
        rw [hb', mul_add, hT' j hj, add_zero, Finset.mul_sum,
          Finset.sum_eq_single_of_mem j hj fun l _ hl => ho j l hl.symm, s.idem _ (he j)]
      rw [s.comp _ b' (he j) hg', e2]
    rw [h3]
    refine ⟨j1, ?_⟩
    rw [j2, i2, hk, Finset.prod_insert hi]; simp [mul_assoc]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] in

theorem transport {S S' : Subgroup G} (h : S = S') (mS : MeasurableSpace S) (hm : mS = borel S) (x : @Measure S mS) :
    ∃ x' : Measure S', (@Measure.IsHaarMeasure _ _ _ mS x → x'.IsHaarMeasure) ∧
      (∀ U : Set G, x' {y | y.1 ∈ U} = x {y | y.1 ∈ U}) ∧ ∀ f : G → ℂ,
        (Integrable (fun y : S' => f y) x' ↔ @Integrable _ _ _ _ mS (fun y : S => f y) x) ∧
          ∫ y : S', f y ∂x' = @integral _ _ _ _ mS x fun y : S => f y := by
  subst h
  have : mS = Subtype.instMeasurableSpace := hm.trans (@BorelSpace.measurable_eq S _ Subtype.instMeasurableSpace (Subtype.borelSpace _)).symm
  subst this
  exact ⟨x, id, fun _ => rfl, fun _ => ⟨Iff.rfl, rfl⟩⟩

def unitP {A : Type} [Ring A] [Algebra R A] (a : R) : Aˣ →* Aˣ := by
  classical
  exact if h : a * a = a then Units.map
    { toFun := fun x : A => a • x + (1 - a) • (1 : A)
      map_one' := by rw [← add_smul]; simp
      map_mul' := fun x y => by
        have h1 : a * (1 - a) = 0 := by rw [mul_sub, h]; simp
        have h2 : (1 - a) * a = 0 := by rw [mul_comm, h1]
        have h3 : (1 - a) * (1 - a) = 1 - a := by rw [mul_sub, h2]; simp
        simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, zero_smul, mul_one, add_zero, zero_add] } else 1

theorem coe_unitP {A : Type} [Ring A] [Algebra R A] {a : R} (h : a * a = a) (x : Aˣ) :
    (unitP a x : A) = a • (x : A) + (1 - a) • (1 : A) := by
  unfold unitP; rw [dif_pos h]; rfl

theorem unitInvariant_continuous {A : Type} [Ring A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A] [ContinuousConstSMul R A] {a : R}
    (h : a * a = a) : Continuous (unitP (A := A) a) := by
  unfold unitP; rw [dif_pos h]
  exact Continuous.units_map _ (by show Continuous fun x : A => a • x + (1 - a) • (1 : A); fun_prop)

theorem unitInvariant_comp {A : Type} [Ring A] [Algebra R A] {a b : R} (ha : a * a = a) (hb : b * b = b) (x : Aˣ) :
    unitP a (unitP b x) = unitP (a * b) x := by
  have : a * b * (a * b) = a * b := by rw [mul_mul_mul_comm, ha, hb]
  ext; rw [coe_unitP ha, coe_unitP hb, coe_unitP this]; module

theorem unitInvariant_zero {A : Type} [Ring A] [Algebra R A] (x : Aˣ) : unitP (0 : R) x = 1 := by
  ext; rw [coe_unitP (by simp)]; simp

theorem unitInvariant_one {A : Type} [Ring A] [Algebra R A] (x : Aˣ) : unitP (1 : R) x = x := by
  ext; rw [coe_unitP (by simp)]; simp

theorem idem_add {a b : R} (ha : a * a = a) (hb : b * b = b) (h : a * b = 0) : (a + b) * (a + b) = a + b := by
  linear_combination ha + hb + 2 * h

theorem unitInvariant_add {A : Type} [Ring A] [Algebra R A] {a b : R} (ha : a * a = a) (hb : b * b = b) (h : a * b = 0) (x : Aˣ) :
    unitP (a + b) x = unitP a x * unitP b x := by
  ext
  rw [Units.val_mul, coe_unitP ha, coe_unitP hb, coe_unitP (idem_add ha hb h)]
  have h1 : a * (1 - b) = a := by linear_combination -h
  have h2 : (1 - a) * b = b := by linear_combination -h
  have h3 : (1 - a) * (1 - b) = 1 - (a + b) := by linear_combination h
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, zero_smul, mul_one, one_mul, zero_add, add_smul]
  abel

end PositivityTheory.ThKG.Fub

end
