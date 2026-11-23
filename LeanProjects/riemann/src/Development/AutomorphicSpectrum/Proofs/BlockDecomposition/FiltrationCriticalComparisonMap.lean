import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.PolySes

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def ev (Q : Poly Φ) (T : C) : (ℕ →₀ Φ.A.obj T) →+ Φ.A.obj (Q.P T) where
  toFun c := c.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)
  map_zero' := Finsupp.sum_zero_index
  map_add' c c' := Finsupp.sum_add_index' (fun k => by simp) (fun k y y' => by simp [add_mul])

theorem ev_single (Q : Poly Φ) (T : C) (k : ℕ) (y : Φ.A.obj T) :
    ev Q T (Finsupp.single k y) = (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T) := by
  change (Finsupp.single k y).sum (fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) = _
  rw [Finsupp.sum_single_index]
  simp

theorem ev_smul (Q : Poly Φ) (T : C) (s : R) (c : ℕ →₀ Φ.A.obj T) : ev Q T (s • c) = s • ev Q T c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg, smul_add]
  | single k y => rw [Finsupp.smul_single, ev_single, ev_single, map_smul, smul_mul_assoc]

def sh {M : Type} [AddCommMonoid M] : (ℕ →₀ M) →+ (ℕ →₀ M) where
  toFun c := c.comapDomain (· + 1) (add_left_injective 1).injOn
  map_zero' := by ext; simp
  map_add' c c' := by ext; simp

@[simp] theorem sh_apply {M : Type} [AddCommMonoid M] (c : ℕ →₀ M) (k : ℕ) : sh c k = c (k + 1) := rfl

theorem sh_single_zero {M : Type} [AddCommMonoid M] (y : M) : sh (Finsupp.single 0 y) = 0 := by
  ext k; simp [Finsupp.single_apply]

theorem sh_single_succ {M : Type} [AddCommMonoid M] (n : ℕ) (y : M) :
    sh (Finsupp.single (n + 1) y) = Finsupp.single n y := by
  ext k; simp [Finsupp.single_apply]

theorem sh_smul {M : Type} [AddCommMonoid M] [Module R M] (s : R) (c : ℕ →₀ M) : sh (s • c) = s • sh c := by
  ext k; simp

def tr {T T' : C} (φ : T ⟶ T') (t : Φ.A.obj T') : (ℕ →₀ Φ.A.obj T) →+ (ℕ →₀ Φ.A.obj T') :=
  Finsupp.liftAddHom fun n =>
    { toFun := fun y => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, Finsupp.single p.1 ((Φ.A.map φ).hom y * Φ.dp p.2 t)
      map_zero' := by simp
      map_add' := fun y y' => by simp [add_mul, Finsupp.single_add, Finset.sum_add_distrib] }

theorem tr_single {T T' : C} (φ : T ⟶ T') (t : Φ.A.obj T') (n : ℕ) (y : Φ.A.obj T) :
    tr φ t (Finsupp.single n y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, Finsupp.single p.1 ((Φ.A.map φ).hom y * Φ.dp p.2 t) := by
  simp [tr]

theorem sh_tr {T T' : C} (φ : T ⟶ T') (t : Φ.A.obj T') (c : ℕ →₀ Φ.A.obj T) :
    sh (tr φ t c) = tr φ t (sh c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single n y =>
    cases n with
    | zero =>
      rw [sh_single_zero, tr_single, map_zero, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      exact sh_single_zero _
    | succ n =>
      rw [sh_single_succ, tr_single, tr_single, map_sum, Finset.Nat.sum_antidiagonal_succ, sh_single_zero, zero_add]
      exact Finset.sum_congr rfl fun p _ => sh_single_succ _ _

theorem ev_tr (Q : Poly Φ) {T T' : C} (φ : T ⟶ T') (ψ : Q.P T ⟶ Q.P T') (t : Φ.A.obj T')
    (hj : Q.j T ≫ ψ = φ ≫ Q.j T') (ht : t ∈ Φ.J.S T')
    (hX : (Φ.A.map ψ).hom (Q.X T) = Q.X T' + (Φ.A.map (Q.j T')).hom t) (c : ℕ →₀ Φ.A.obj T) :
    (Φ.A.map ψ).hom (ev Q T c) = ev Q T' (tr φ t c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single n y =>
    have hy : (Φ.A.map ψ).hom ((Φ.A.map (Q.j T)).hom y) = (Φ.A.map (Q.j T')).hom ((Φ.A.map φ).hom y) := by
      rw [← Cut.mapA_comp, ← Cut.mapA_comp, hj]
    have hjt : (Φ.A.map (Q.j T')).hom t ∈ Φ.J.S (Q.P T') := Φ.J.map_mem _ ht
    rw [ev_single, map_mul, hy, Φ.dp_map ψ n (Q.X_mem T), hX, Φ.dp_add n (Q.X_mem T') hjt, tr_single, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_single, map_mul, Φ.dp_map (Q.j T') p.2 ht]
    ring

theorem exists_rep (Q : Poly Φ) (a b : IdF Φ.A) {T : C} (x : sqM a b (Q.P T)) :
    ∃ c : ℕ →₀ Φ.A.obj T, ev Q T c ∈ a.S (Q.P T) ∧ x.1 = Ideal.Quotient.mk _ (ev Q T c) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  obtain ⟨c, rfl⟩ := Q.span T y
  exact ⟨c, hy, rfl⟩

theorem sqMap_val {T T' : C} (a b : IdF Φ.A) (φ : T ⟶ T') (z : sqM a b T) (y : Φ.A.obj T)
    (h : z.1 = Ideal.Quotient.mk _ y) : (sqMap a b φ z).1 = Ideal.Quotient.mk _ ((Φ.A.map φ).hom y) := by
  obtain ⟨z, hz⟩ := z
  obtain rfl : z = _ := h
  rfl

theorem ev_sh_mem (Q : Poly Φ) {a : ℤ → IdF Φ.A} {r : ℤ} (h : Q.Crit a r) (h' : Q.Crit a (r - 1)) {T : C}
    {c : ℕ →₀ Φ.A.obj T} (hc : ev Q T c ∈ (a r).S (Q.P T)) : ev Q T (sh c) ∈ (a (r - 1)).S (Q.P T) :=
  (h' T (sh c)).2 fun k => by
    have e : r - 1 - (k : ℤ) = r - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, sh_apply]
    exact (h T c).1 hc (k + 1)

theorem wd (Q : Poly Φ) {b : ℤ → IdF Φ.A} {r : ℤ} (h : Q.Crit b r) (h' : Q.Crit b (r - 1)) {T : C}
    {c c' : ℕ →₀ Φ.A.obj T}
    (e : (Ideal.Quotient.mk ((b r).S (Q.P T))) (ev Q T c) = Ideal.Quotient.mk _ (ev Q T c')) :
    (Ideal.Quotient.mk ((b (r - 1)).S (Q.P T))) (ev Q T (sh c)) = Ideal.Quotient.mk _ (ev Q T (sh c')) := by
  rw [Ideal.Quotient.eq] at e ⊢
  rw [← map_sub] at e
  rw [← map_sub, ← map_sub]
  exact ev_sh_mem Q h h' e

section

variable (Q : Poly Φ) {a b : ℤ → IdF Φ.A} {r : ℤ}

def rep (a b : IdF Φ.A) {T : C} (x : sqM a b (Q.P T)) : ℕ →₀ Φ.A.obj T := (exists_rep Q a b x).choose

theorem rep_mem (a b : IdF Φ.A) {T : C} (x : sqM a b (Q.P T)) : ev Q T (rep Q a b x) ∈ a.S (Q.P T) :=
  (exists_rep Q a b x).choose_spec.1

theorem rep_eq (a b : IdF Φ.A) {T : C} (x : sqM a b (Q.P T)) :
    x.1 = Ideal.Quotient.mk _ (ev Q T (rep Q a b x)) :=
  (exists_rep Q a b x).choose_spec.2

def dX (h₁ : Q.Crit a r) (h₂ : Q.Crit a (r - 1)) (h₃ : Q.Crit b r) (h₄ : Q.Crit b (r - 1)) (T : C) :
    sqM (a r) (b r) (Q.P T) →ₗ[R] sqM (a (r - 1)) (b (r - 1)) (Q.P T) where
  toFun x := ⟨Ideal.Quotient.mk _ (ev Q T (sh (rep Q _ _ x))),
    Ideal.mem_map_of_mem _ (ev_sh_mem Q h₁ h₂ (rep_mem Q _ _ x))⟩
  map_add' x y := Subtype.ext (by
    have e : Ideal.Quotient.mk ((b r).S (Q.P T)) (ev Q T (rep Q _ _ (x + y))) =
        Ideal.Quotient.mk _ (ev Q T (rep Q _ _ x + rep Q _ _ y)) := by
      rw [← rep_eq, map_add, map_add, ← rep_eq, ← rep_eq]
      rfl
    have := wd Q h₃ h₄ e
    rw [map_add, map_add, map_add] at this
    exact this)
  map_smul' s x := Subtype.ext (by
    have e : Ideal.Quotient.mk ((b r).S (Q.P T)) (ev Q T (rep Q _ _ (s • x))) =
        Ideal.Quotient.mk _ (ev Q T (s • rep Q _ _ x)) := by
      rw [← rep_eq, ev_smul]
      change s • x.1 = _
      rw [rep_eq Q _ _ x]
      rfl
    have := wd Q h₃ h₄ e
    rw [sh_smul, ev_smul] at this
    exact this)

theorem dX_eq (h₁ : Q.Crit a r) (h₂ : Q.Crit a (r - 1)) (h₃ : Q.Crit b r) (h₄ : Q.Crit b (r - 1)) {T : C}
    (x : sqM (a r) (b r) (Q.P T)) (z : sqM (a (r - 1)) (b (r - 1)) (Q.P T)) (c : ℕ →₀ Φ.A.obj T)
    (hx : x.1 = Ideal.Quotient.mk _ (ev Q T c)) (hz : z.1 = Ideal.Quotient.mk _ (ev Q T (sh c))) :
    dX Q h₁ h₂ h₃ h₄ T x = z := by
  refine Subtype.ext ?_
  rw [hz]
  exact wd Q h₃ h₄ ((rep_eq Q _ _ x).symm.trans hx)

theorem ev_single_zero {T : C} (w : Φ.A.obj T) : ev Q T (Finsupp.single 0 w) = (Φ.A.map (Q.j T)).hom w := by
  rw [ev_single, Φ.dp_zero (Q.X_mem T), mul_one]

theorem sqMap_j_inj (h₃ : Q.Crit b r) (a' : IdF Φ.A) (T : C) :
    Function.Injective (sqMap a' (b r) (Q.j T)) := by
  refine (injective_iff_map_eq_zero (sqMap a' (b r) (Q.j T))).2 fun x hx => ?_
  obtain ⟨x, hxm⟩ := x
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hxm
  have h0 := sqMap_val a' (b r) (Q.j T) ⟨_, hxm⟩ w rfl
  rw [hx] at h0
  have h1 : (Φ.A.map (Q.j T)).hom w ∈ (b r).S (Q.P T) := Ideal.Quotient.eq_zero_iff_mem.1 h0.symm
  rw [← ev_single_zero] at h1
  have h2 := (h₃ T (Finsupp.single 0 w)).1 h1 0
  simp only [Finsupp.single_eq_same, Nat.cast_zero, sub_zero] at h2
  exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 h2)

theorem dX_surj (h₁ : Q.Crit a r) (h₂ : Q.Crit a (r - 1)) (h₃ : Q.Crit b r) (h₄ : Q.Crit b (r - 1)) (T : C) :
    Function.Surjective (dX Q h₁ h₂ h₃ h₄ T) := by
  intro z
  obtain ⟨c', hm, hz⟩ := exists_rep Q _ _ z
  have inj : Function.Injective (· + 1 : ℕ → ℕ) := add_left_injective 1
  let c : ℕ →₀ Φ.A.obj T := Finsupp.mapDomain (· + 1) c'
  have hs : sh c = c' := by
    ext k
    exact Finsupp.mapDomain_apply inj c' k
  have hc : ev Q T c ∈ (a r).S (Q.P T) := by
    refine (h₁ T c).2 fun k => ?_
    cases k with
    | zero =>
      have : c 0 = 0 := Finsupp.mapDomain_notin_range _ _ (by simp)
      rw [this]
      exact Ideal.zero_mem _
    | succ k =>
      have e : r - ((k + 1 : ℕ) : ℤ) = r - 1 - (k : ℤ) := by push_cast; ring
      rw [e]
      have : c (k + 1) = c' k := Finsupp.mapDomain_apply inj c' k
      rw [this]
      exact (h₂ T c').1 hm k
  exact ⟨⟨_, Ideal.mem_map_of_mem _ hc⟩, dX_eq Q h₁ h₂ h₃ h₄ _ z c rfl (by rw [hs, hz])⟩

theorem dX_exact (h₁ : Q.Crit a r) (h₂ : Q.Crit a (r - 1)) (h₃ : Q.Crit b r) (h₄ : Q.Crit b (r - 1)) (T : C) :
    Function.Exact (sqMap (a r) (b r) (Q.j T)) (dX Q h₁ h₂ h₃ h₄ T) := by
  intro y
  constructor
  · intro hy
    obtain ⟨c, hm, hc⟩ := exists_rep Q _ _ y
    have hy0 : ev Q T (sh c) ∈ (b (r - 1)).S (Q.P T) := by
      have e := dX_eq Q h₁ h₂ h₃ h₄ y ⟨_, Ideal.mem_map_of_mem _ (ev_sh_mem Q h₁ h₂ hm)⟩ c hc rfl
      rw [hy] at e
      exact Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val e).symm
    have h0 : c 0 ∈ (a r).S T := by simpa using (h₁ T c).1 hm 0
    have hd : ev Q T (c - Finsupp.single 0 (c 0)) ∈ (b r).S (Q.P T) := by
      refine (h₃ T _).2 fun k => ?_
      cases k with
      | zero => simp
      | succ k =>
        have e : r - ((k + 1 : ℕ) : ℤ) = r - 1 - (k : ℤ) := by push_cast; ring
        rw [e]
        simpa [Finsupp.single_apply] using (h₄ T (sh c)).1 hy0 k
    refine ⟨⟨_, Ideal.mem_map_of_mem _ h0⟩, Subtype.ext ?_⟩
    rw [sqMap_val (a r) (b r) (Q.j T) _ (c 0) rfl, hc, ← ev_single_zero]
    refine (Ideal.Quotient.eq.2 ?_)
    rw [← map_sub]
    have := Ideal.neg_mem_iff _ |>.2 hd
    rwa [← map_neg, neg_sub] at this
  · rintro ⟨⟨x, hxm⟩, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hxm
    refine dX_eq Q h₁ h₂ h₃ h₄ _ 0 (Finsupp.single 0 w) ?_ ?_
    · rw [sqMap_val (a r) (b r) (Q.j T) ⟨_, hxm⟩ w rfl, ev_single_zero]
    · rw [sh_single_zero, map_zero, map_zero]
      rfl

theorem dX_nat {d : ℕ} {E : Frame Φ (d + 1)} (h₁ : Q.Crit a r) (h₂ : Q.Crit a (r - 1)) (h₃ : Q.Crit b r)
    (h₄ : Q.Crit b (r - 1)) {X Y : Pt E} (φ : X.T ⟶ Y.T) (z : sqM (a r) (b r) (Q.P X.T)) :
    dX Q h₁ h₂ h₃ h₄ Y.T (sqMap (a r) (b r) (Cut.Pmap Q φ) z) =
      sqMap (a (r - 1)) (b (r - 1)) (Cut.Pmap Q φ) (dX Q h₁ h₂ h₃ h₄ X.T z) := by
  obtain ⟨c, hm, hc⟩ := exists_rep Q _ _ z
  have key : ∀ c : ℕ →₀ Φ.A.obj X.T, (Φ.A.map (Cut.Pmap Q φ)).hom (ev Q X.T c) =
      ev Q Y.T (tr φ (E.τ 0 (X.s ≫ φ) Y.s) c) := fun c =>
    ev_tr Q φ (Cut.Pmap Q φ) _ (Cut.Pmap_j Q φ) (E.mem 0 _ _) (Cut.Pmap_X Q φ) c
  refine dX_eq Q h₁ h₂ h₃ h₄ _ _ (tr φ (E.τ 0 (X.s ≫ φ) Y.s) c) ?_ ?_
  · rw [sqMap_val _ _ _ z _ hc, key]
  · have e : dX Q h₁ h₂ h₃ h₄ X.T z = ⟨_, Ideal.mem_map_of_mem _ (ev_sh_mem Q h₁ h₂ hm)⟩ :=
      dX_eq Q h₁ h₂ h₃ h₄ z _ c hc rfl
    rw [e, sqMap_val _ _ _ _ (ev Q X.T (sh c)) rfl, key, sh_tr]

end

theorem ses : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {d : ℕ} (E : Frame Φ (d + 1))
    (a b : ℤ → IdF Φ.A) (r : ℤ), (∀ r' T, (b r').S T ≤ (a r').S T) → Q.Crit a r → Q.Crit a (r - 1) → Q.Crit b r → Q.Crit b (r - 1) →
    ∃ β : Cut.P0 Q ⋙ Cut.U E ⋙ sq (a r) (b r) ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq (a (r - 1)) (b (r - 1)),
      (∀ X, Function.Injective ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))).app X).hom) ∧
      (∀ X, Function.Exact ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))).app X).hom (β.app X).hom) ∧
      (∀ X, Function.Surjective (β.app X).hom) ∧
      ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (a r) (b r) (Q.P X.T)) (z' : sqM (a (r - 1)) (b (r - 1)) (Q.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        (β.app X).hom z = z' := by
  intro R _ C _ Φ Q d E a b r hle h₁ h₂ h₃ h₄
  refine ⟨{ app := fun X => ModuleCat.ofHom (dX Q h₁ h₂ h₃ h₄ X.T)
            naturality := fun X Y φ => ?_ }, fun X => ?_, fun X => ?_, fun X => ?_, ?_⟩
  · ext z
    exact dX_nat Q h₁ h₂ h₃ h₄ φ z
  · exact sqMap_j_inj Q h₃ _ X.T
  · exact dX_exact Q h₁ h₂ h₃ h₄ X.T
  · exact dX_surj Q h₁ h₂ h₃ h₄ X.T
  · intro X c c' z z' hk hz hz'
    have e : sh c = c' := Finsupp.ext fun k => (hk k).symm
    exact dX_eq Q h₁ h₂ h₃ h₄ z z' c hz (by rw [e]; exact hz')

end GlobalTheory.CompanionTheory.PolySes
