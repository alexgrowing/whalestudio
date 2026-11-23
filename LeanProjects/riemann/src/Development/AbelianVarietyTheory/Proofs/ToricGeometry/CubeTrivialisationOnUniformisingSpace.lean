import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.CubeValues

def ValueRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

section Values

variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

lemma le_preimage_inf (U V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) ↔ ⊤ ≤ x ⁻¹ᵁ U ∧ ⊤ ≤ x ⁻¹ᵁ V := by
  show ⊤ ≤ x ⁻¹ᵁ U ⊓ x ⁻¹ᵁ V ↔ _
  exact le_inf_iff

lemma val_unit_ne_zero (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val ≠ 0 := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  rw [he]
  exact (Units.map (e : Γ(X, U) →* ℂ) f).ne_zero

lemma val_unit_mul (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)ˣ) :
    valAt' x U (f * f').val = valAt' x U f.val * valAt' x U f'.val := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  rw [he, he, he, Units.val_mul, map_mul]

lemma val_unit_prod_zpow (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {K : Type} [Fintype K]
    (f : K → Γ(X, U)ˣ) (ε : K → ℤ) :
    valAt' x U (∏ k, f k ^ ε k).val = ∏ k, valAt' x U (f k).val ^ ε k := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  have hm : ∀ w : Γ(X, U)ˣ, valAt' x U w.val = ((Units.map (e : Γ(X, U) →* ℂ) w : ℂˣ) : ℂ) :=
    fun w => he w.val
  calc valAt' x U (∏ k, f k ^ ε k).val = ((Units.map (e : Γ(X, U) →* ℂ) (∏ k, f k ^ ε k) : ℂˣ) : ℂ) := hm _
    _ = ∏ k, ((Units.map (e : Γ(X, U) →* ℂ) (f k) : ℂˣ) : ℂ) ^ ε k := by
      rw [map_prod, Units.coe_prod]
      simp only [map_zpow, Units.val_zpow_eq_zpow_val]
    _ = ∏ k, valAt' x U (f k).val ^ ε k := by simp only [hm]

lemma val_res (hv : ValueRules) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)ˣ) :
    valAt' x V (res hVU f).val = valAt' x U f.val :=
  (hv X x).2.2.1 U V hVU f.val h

lemma val_pullU (hv : ValueRules) {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)ˣ) :
    valAt' x (φ ⁻¹ᵁ U) (pullU φ U f).val = valAt' (x ≫ φ) U f.val :=
  (hv X x).2.2.2.1 Y φ U f.val

lemma le_preimage_wchart {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K] (φ : K → (X ⟶ Y))
    (j : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ L.wchart φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  have key : ∀ q : Sp ℂ, q ∈ x ⁻¹ᵁ L.wchart φ j ↔ ∀ k, q ∈ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
    intro q
    show x q ∈ L.wchart φ j ↔ ∀ k, φ k (x q) ∈ L.U (j k)
    simp [LB.wchart]
  constructor
  · intro h k q _
    exact (key q).1 (h trivial) k
  · intro h q _
    exact (key q).2 (fun k => h k trivial)

lemma val_gen (hv : ValueRules) {L : LB X} (t : L.Gen) (ht : t.IsGen) (i j : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U i) (t.s i).val =
      valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j) (t.s j).val := by
  have hij : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  have e := congrArg (fun w : Γ(X, L.U i ⊓ L.U j)ˣ => valAt' x (L.U i ⊓ L.U j) w.val) (ht i j)
  rw [val_unit_mul x hv hij, val_res x hv _ hij, val_res x hv _ hij] at e
  exact e

lemma val_linComb (hv : ValueRules) {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K]
    (φ : K → (X ⟶ Y)) (ε : K → ℤ) (j j' : K → L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j) (hj' : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j') :
    valAt' x (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  have h2 : ⊤ ≤ x ⁻¹ᵁ (L.wchart φ j ⊓ L.wchart φ j') := (le_preimage_inf x _ _).2 ⟨hj, hj'⟩
  simp only [LB.LinComb]
  rw [val_unit_prod_zpow x hv h2]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  congr 1
  refine (val_res x hv _ h2 _).trans ?_
  exact val_pullU x hv (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k))

lemma val_cocycle (hv : ValueRules) {L : LB X} (hL : L.IsLB) (i j k : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j ⊓ L.U k) (L.g j k).val =
      valAt' x (L.U i ⊓ L.U k) (L.g i k).val := by
  obtain ⟨-, -, hc⟩ := hL
  have hij : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  have hijk : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := (le_preimage_inf x _ _).2 ⟨hij, hk⟩
  have e := congrArg (fun w : Γ(X, L.U i ⊓ L.U j ⊓ L.U k)ˣ => valAt' x _ w.val) (hc i j k)
  rw [val_unit_mul x hv hijk, val_res x hv _ hijk, val_res x hv _ hijk, val_res x hv _ hijk] at e
  exact e

end Values

section Points

variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)

lemma ex_zero : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)

lemma ex_add_period (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]

lemma comp_foldr {T T' : Over (Sp ℂ)} (p : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A)) (l : List (Fin n)) :
    p ≫ l.foldr (fun k acc => padd A (y k) acc) (pzero A T) = (l.map fun k => p ≫ y k).prod := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.prod_nil, pzero, Hom.one_def, comp_toUnit_assoc]
  | cons k l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, ← ih, padd, Hom.mul_def, comp_lift_assoc]

lemma ex_list_sum {κ : Type} (w : κ → Fin g → ℂ) (l : List κ) :
    u.ex (l.map w).sum = (l.map fun k => u.ex (w k)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, List.prod_nil, ex_zero]
  | cons k l ih => simp only [List.map_cons, List.sum_cons, List.prod_cons, u.ex_add, ih]

lemma comp_psum {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (w : Fin n → Fin g → ℂ) (h : ∀ k, p ≫ y k = u.ex (w k)) (I : Finset (Fin n)) :
    p ≫ psum A y I = u.ex (∑ a ∈ I, w a) := by
  have hs : ∑ a ∈ I, w a = (((List.finRange n).filter (fun a => decide (a ∈ I))).map w).sum := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    congr 1
    ext a
    simp
  rw [psum, comp_foldr, hs, ex_list_sum]
  exact congrArg List.prod (List.map_congr_left (fun k _ => h k))

def pt3 (x : Fin 3 → Fin g → ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ G3 A :=
  lift (u.ex (x 0)) (lift (u.ex (x 1)) (u.ex (x 2)))

lemma tripleProductPoint_comp_partialSum (x : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)) :
    (pt3 u x).left ≫ (psum A (x3 A) I).left = (u.ex (∑ a ∈ I, x a)).left := by
  rw [← Over.comp_left, comp_psum u (pt3 u x) (x3 A) x _ I]
  intro k
  fin_cases k <;> simp [pt3, x3]

lemma tripleProductPoint_add_period (x l : Fin 3 → Fin g → ℂ) (hl : ∀ a, l a ∈ u.Λ) :
    pt3 u (x + l) = pt3 u x := by
  simp only [pt3, Pi.add_apply, ex_add_period u _ _ (hl _)]

lemma hol_coord (a : Fin 3) (U : A.left.Opens) (f : Γ(A.left, U)) :
    IsOpen {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w : Fin 3 → Fin g → ℂ => valAt' (u.ex (w a)).left U f)
        {w | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} := by
  obtain ⟨ho, hd⟩ := u.hol U f
  have hset : {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} =
      (fun w : Fin 3 → Fin g → ℂ => w a) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
    ext w; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact ho.preimage (continuous_apply a)
  · exact hd.comp (differentiable_apply a).differentiableOn (fun w hw => hw.2)

private theorem pt3_preimage_theta_whole_iff {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ}
    (u : HolUnif A L₀ g) (L : LB A.left) (j : Finset (Fin 3) → L.ι) (x : Fin 3 → Fin g → ℂ) :
    ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j I.down) ↔
      ∀ I : Finset (Fin 3), ⊤ ≤ (u.ex (∑ a ∈ I, x a)).left ⁻¹ᵁ L.U (j I) := by
  show ⊤ ≤ (pt3 u x).left ⁻¹ᵁ
      L.wchart (fun I : ULift (Finset (Fin 3)) => (psum A (x3 A) I.down).left) (fun I => j I.down) ↔ _
  rw [le_preimage_wchart]
  simp only [tripleProductPoint_comp_partialSum]
  exact ⟨fun h I => h ⟨I⟩, fun h I => h I.down⟩

private theorem valAt_theta_transition_eq_prod_zpow (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left}
    {g : ℕ} (u : HolUnif A L₀ g) (L : LB A.left) (j j' : Finset (Fin 3) → L.ι) (x : Fin 3 → Fin g → ℂ)
    (hj : ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j I.down))
    (hj' : ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j' I.down)) :
    valAt' (pt3 u x).left ((Theta A L).U (fun I => j I.down) ⊓ (Theta A L).U (fun I => j' I.down))
        ((Theta A L).g (fun I => j I.down) (fun I => j' I.down)).val =
      ∏ I : Finset (Fin 3), valAt' (u.ex (∑ a ∈ I, x a)).left (L.U (j I) ⊓ L.U (j' I))
        (L.g (j I) (j' I)).val ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  have e := val_linComb (pt3 u x).left hv L
    (fun I : ULift (Finset (Fin 3)) => (psum A (x3 A) I.down).left)
    (fun I : ULift (Finset (Fin 3)) => (-1 : ℤ) ^ (3 - I.down.card)) (fun I => j I.down) (fun I => j' I.down) hj hj'
  simp only [tripleProductPoint_comp_partialSum] at e
  refine e.trans ?_
  exact Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)

end Points

end GlobalTheory.CubeValues

open GlobalTheory.CubeValues in

theorem GlobalTheory.cube_trivialisation_on_uniformising_space :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (L₀ L : LB A.left) (g : ℕ) (u : HolUnif A L₀ g), L.IsLB → ∀ t : LB.Gen (Theta A L), t.IsGen → ∀ (W : L.ι → Set (Fin g → ℂ)) (c : L.ι → L.ι → (Fin g → ℂ) → ℂ), W = (fun (i : L.ι) => {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}) → c = (fun (i j : L.ι) (z : Fin g → ℂ) => valAt' (u.ex z).left (L.U i ⊓ L.U j) (L.g i j).val) → ((∀ i, IsOpen (W i)) ∧ (∀ z, ∃ i, z ∈ W i) ∧ (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) ∧ (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) ∧ (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) ∧ (∀ i z, ∀ l ∈ u.Λ, z + l ∈ W i ↔ z ∈ W i) ∧ (∀ i j z, ∀ l ∈ u.Λ, c i j (z + l) = c i j z)) ∧ ∃ T : (Finset (Fin 3) → L.ι) → (Fin 3 → Fin g → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) ∧ (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) ∧ (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) ∧ (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ u.Λ) → T j (x + l) = T j x)) := by
  intro hv0 hlift A _ _ L₀ L g u hL t ht W c hW hc
  have hv : ValueRules := hv0
  subst hW hc
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact (u.hol (L.U i) 0).1
  · intro z
    have hq : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
      rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    exact ⟨i, ((hv _ (u.ex z).left).1 (L.U i)).2 hi⟩
  · intro i j
    have hset : ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j}) =
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j)} := by
      ext z
      exact (le_preimage_inf _ _ _).symm
    show DifferentiableOn ℂ (fun z => valAt' (u.ex z).left (L.U i ⊓ L.U j) (L.g i j).val)
      ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j})
    rw [hset]
    exact (u.hol _ _).2
  · intro i j z hi hj
    exact val_unit_ne_zero _ hv ((le_preimage_inf _ _ _).2 ⟨hi, hj⟩) _
  · intro i j k z hi hj hk
    exact val_cocycle _ hv hL i j k hi hj hk
  · intro i z l hl
    show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i
    rw [ex_add_period u z l hl]
  · intro i j z l hl
    show valAt' (u.ex (z + l)).left _ _ = valAt' (u.ex z).left _ _
    rw [ex_add_period u z l hl]
  · have hH := hlift (Fin 3 → Fin g → ℂ) Set.univ A (A ⊗ A) (fun w => u.ex (w 0))
      (fun w => lift (u.ex (w 1)) (u.ex (w 2))) (fun U f => hol_coord u 0 U f)
      (hlift (Fin 3 → Fin g → ℂ) Set.univ A A (fun w => u.ex (w 1)) (fun w => u.ex (w 2))
        (fun U f => hol_coord u 1 U f) (fun U f => hol_coord u 2 U f))
    refine ⟨fun j x => valAt' (pt3 u x).left ((Theta A L).U (fun I => j I.down)) (t.s (fun I => j I.down)).val,
      ?_, ?_, ?_, ?_⟩
    · intro j
      refine ((hH ((Theta A L).U (fun I => j I.down)) (t.s (fun I => j I.down)).val).2).mono ?_
      intro x hx
      exact ⟨trivial, (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx⟩
    · intro j x hx
      exact val_unit_ne_zero _ hv ((GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx) _
    · intro j j' x hx hx'
      have hi := (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx
      have hi' := (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j' x).2 hx'
      have e := val_gen (pt3 u x).left hv t ht _ _ hi hi'
      rw [GlobalTheory.CubeValues.valAt_theta_transition_eq_prod_zpow hv u L j j' x hi hi'] at e
      exact e
    · intro j x l hl
      show valAt' (pt3 u (x + l)).left _ _ = valAt' (pt3 u x).left _ _
      rw [tripleProductPoint_add_period u x l hl]
