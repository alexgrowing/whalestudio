import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruentOneMatricesTransitiveNearHermitianStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CongGrp

theorem finite_image_of_factor {α β γ : Type} (S : Set α) (f : α → β) (g : α → γ) [Finite β]
    (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y → g x = g y) : (g '' S).Finite := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x0, _⟩
  · simp
  haveI : Nonempty α := ⟨x0⟩
  refine (Set.finite_range fun t => g (Function.invFunOn f S t)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨f x, ?_⟩
  have hex : ∃ a ∈ S, f a = f x := ⟨x, hx, rfl⟩
  exact h _ (Function.invFunOn_mem hex) _ hx (Function.invFunOn_eq hex)

theorem cont_pos {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) (h : IsCO W0 S)
    (hS : S.Nonempty) : 0 < cont W0 S := by
  unfold cont
  rw [dif_pos h]
  obtain ⟨h1, h2, -, h4⟩ := h.choose_spec
  refine mul_pos ?_ (div_pos ?_ ?_)
  · exact_mod_cast (Set.ncard_pos h4).2 (hS.image _)
  · exact_mod_cast Nat.pos_of_ne_zero h2
  · exact_mod_cast Nat.pos_of_ne_zero h1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem intM_mul (L : LocE F E) {m : ℕ} {A B : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A)
    (hB : IsIntM L B) : IsIntM L (A * B) := fun a b => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA _ _) (hB _ _)

theorem intM_add (L : LocE F E) {m : ℕ} {A B : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A)
    (hB : IsIntM L B) : IsIntM L (A + B) := fun a b => add_mem (hA a b) (hB a b)

theorem intM_neg (L : LocE F E) {m : ℕ} {A : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A) :
    IsIntM L (-A) := fun a b => neg_mem (hA a b)

theorem intM_smul (L : LocE F E) {m : ℕ} {c : E} (hc : c ∈ L.O) {A : Matrix (Fin m) (Fin m) E}
    (hA : IsIntM L A) : IsIntM L (c • A) := fun a b => mul_mem hc (hA a b)

theorem intM_one (L : LocE F E) {m : ℕ} : IsIntM L (1 : Matrix (Fin m) (Fin m) E) := fun a b => by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem mem_congK (L : LocE F E) (ϖ : 𝒪[F]) {m i : ℕ} {A : Matrix (Fin m) (Fin m) E} :
    A ∈ congK L ϖ m i ↔ ∃ C, IsIntM L C ∧ A = 1 + algebraMap F E ((ϖ : F) ^ i) • C := by
  constructor
  · intro h
    choose C hC hA using h
    refine ⟨Matrix.of C, hC, ?_⟩
    ext a b
    have := hA a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination this
  · rintro ⟨C, hC, rfl⟩ a b
    exact ⟨C a b, hC a b, by simp⟩

theorem cT_mul (L : LocE F E) {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext a b
  simp [cT, Matrix.mul_apply, mul_comm]

theorem cT_cT (L : LocE F E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) : cT L (cT L A) = A := by
  ext a b
  simp [cT, L.cj_cj]

theorem cT_one (L : LocE F E) {m : ℕ} : cT L (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  ext a b
  simp [cT, Matrix.one_apply, eq_comm]

theorem mem_hermLat (L : LocE F E) {m : ℕ} {X : Matrix (Fin m) (Fin m) E} :
    X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X := by
  refine ⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨by ext a b; simp [cT], fun a b => zero_mem _⟩
  | add x y _ _ hx hy =>
    refine ⟨?_, intM_add L hx.2 hy.2⟩
    ext a b
    have h1 := congrFun (congrFun hx.1 a) b
    have h2 := congrFun (congrFun hy.1 a) b
    simp only [cT] at h1 h2
    simp [cT, h1, h2]
  | neg x _ hx =>
    refine ⟨?_, intM_neg L hx.2⟩
    ext a b
    have h1 := congrFun (congrFun hx.1 a) b
    simp only [cT] at h1
    simp [cT, h1]

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem int_mem (L : LocE F E) (c : 𝒪[F]) : algebraMap F E (c : F) ∈ L.O := by
  rw [L.O_def]
  exact isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := c)

theorem pow_mem' (L : LocE F E) (ϖ : 𝒪[F]) (i : ℕ) : algebraMap F E ((ϖ : F) ^ i) ∈ L.O := by
  have := int_mem L (ϖ ^ i)
  simpa using this

theorem norm_one_add (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {y : E} (hy : y ∈ L.O) :
    ∃ u : (𝒪[F])ˣ, (1 + algebraMap F E (ϖ : F) * y) * L.cj (1 + algebraMap F E (ϖ : F) * y) =
      algebraMap F E ((u : 𝒪[F]) : F) := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨-, ⟨t, ht⟩, n, hn⟩ := h2 y hy
  have hu : IsUnit (1 + ϖ * (t + ϖ * n)) := by
    have hm : ϖ * (t + ϖ * n) ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
      Ideal.mul_mem_right _ _ hϖ.not_isUnit
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem hm)
    simpa using this
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  have e : ((1 + ϖ * (t + ϖ * n) : 𝒪[F]) : F) = 1 + (ϖ : F) * ((t : F) + (ϖ : F) * (n : F)) := rfl
  rw [e]
  simp only [map_add, map_mul, map_one, AlgEquiv.commutes]
  rw [← ht, ← hn]
  ring

theorem vE_unit (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (u : (𝒪[F])ˣ) :
    vE L ϖ (algebraMap F E ((u : 𝒪[F]) : F)) = 0 := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hne : ∀ w : (𝒪[F])ˣ, ((w : 𝒪[F]) : F) ≠ 0 := fun w h => w.ne_zero (Subtype.ext h)
  have e1 := h1 1 1 one_ne_zero one_ne_zero
  have e2 := h1 _ _ (hne u) (hne u⁻¹)
  have e3 : ((u : 𝒪[F]) : F) * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
    rw [← Subring.coe_mul]; simp
  rw [e3] at e2
  rw [mul_one] at e1
  have a1 := (h3 _ (hne u)).2 (u : 𝒪[F]).2
  have a2 := (h3 _ (hne u⁻¹)).2 ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2
  omega

theorem exists_pow_mul_mem (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (x : E) :
    ∃ n : ℕ, algebraMap F E ((ϖ : F) ^ n) * x ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  have h1 : IsAlgebraic F x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic 𝒪[F] x := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1
  obtain ⟨r, hr, hi⟩ := h2.exists_integral_multiple
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  refine ⟨n, ?_⟩
  have h3 := mul_mem (int_mem L ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])) ((L.O_def _).2 hi)
  have e3 : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((u : 𝒪[F]) : F) = 1 := by
    rw [← Subring.coe_mul]; simp
  have e4 : ((u : 𝒪[F]) * ϖ ^ n) • x = algebraMap F E (((u : 𝒪[F]) : F) * (ϖ : F) ^ n) * x := by
    rw [Algebra.smul_def]
    rfl
  rw [e4, ← mul_assoc, ← map_mul, ← mul_assoc, e3, one_mul] at h3
  exact h3

theorem congK_basic (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {m i : ℕ} (hi : 1 ≤ i)
    {A : Matrix (Fin m) (Fin m) E} (hA : A ∈ congK L ϖ m i) :
    IsUnit A.det ∧ vE L ϖ (A.det * L.cj A.det) = 0 ∧ IsIntM L A⁻¹ := by
  obtain ⟨C, hC, hAC⟩ := (mem_congK L ϖ).1 hA
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  let C' : Matrix (Fin m) (Fin m) L.O :=
    Matrix.of fun a b => ⟨algebraMap F E ((ϖ : F) ^ k) * C a b, mul_mem (pow_mem' L ϖ k) (hC a b)⟩
  let p : L.O := ⟨algebraMap F E (ϖ : F), int_mem L ϖ⟩
  let A' : Matrix (Fin m) (Fin m) L.O := 1 + p • C'
  have hAA : A = L.O.subtype.mapMatrix A' := by
    rw [hAC]
    simp only [A', map_add, map_one]
    congr 1
    ext a b
    simp [C', p, pow_succ]
    ring
  obtain ⟨y, hy⟩ : ∃ y : L.O, A'.det = 1 + p * y := by
    refine ⟨C'.trace + Polynomial.eval p (1 + (Polynomial.X : Polynomial L.O) •
      C'.map Polynomial.C).det.divX.divX * p, ?_⟩
    simp only [A']
    rw [Matrix.det_one_add_smul]
    ring
  have hdet : A.det = 1 + algebraMap F E (ϖ : F) * (y : E) := by
    rw [hAA, ← RingHom.map_det, hy]
    rfl
  obtain ⟨u, hu⟩ := norm_one_add L ϖ hϖ y.2
  have e3 : ((u : 𝒪[F]) : F) * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
    rw [← Subring.coe_mul]; simp
  have hcj : L.cj (1 + algebraMap F E (ϖ : F) * (y : E)) ∈ L.O :=
    ((GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.1 _
      (add_mem (one_mem _) (mul_mem (int_mem L ϖ) y.2))).1
  have hU : IsUnit A'.det := by
    refine IsUnit.of_mul_eq_one
      (⟨_, mul_mem hcj (int_mem L ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]))⟩ : L.O) ?_
    rw [hy]
    apply Subtype.ext
    change (1 + algebraMap F E (ϖ : F) * (y : E)) * (_ * _) = 1
    rw [← mul_assoc, hu, ← map_mul, e3, map_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hAA, ← RingHom.map_det]
    exact hU.map _
  · rw [hdet, hu]
    exact vE_unit L ϖ hϖ u
  · have : A⁻¹ = L.O.subtype.mapMatrix A'⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [hAA, ← map_mul, Matrix.mul_nonsing_inv _ hU, map_one]
    rw [this]
    intro a b
    exact (A'⁻¹ a b).2

theorem congK_int (L : LocE F E) (ϖ : 𝒪[F]) {m i : ℕ}
    {A : Matrix (Fin m) (Fin m) E} (hA : A ∈ congK L ϖ m i) : IsIntM L A := by
  obtain ⟨C, hC, rfl⟩ := (mem_congK L ϖ).1 hA
  exact intM_add L (intM_one L) (intM_smul L (pow_mem' L ϖ i) hC)

theorem congK_mul (L : LocE F E) (ϖ : 𝒪[F]) {m i : ℕ} {A B : Matrix (Fin m) (Fin m) E}
    (hA : A ∈ congK L ϖ m i) (hB : B ∈ congK L ϖ m i) : A * B ∈ congK L ϖ m i := by
  have hB' := congK_int L ϖ hB
  obtain ⟨C, hC, rfl⟩ := (mem_congK L ϖ).1 hA
  obtain ⟨D, hD, hBD⟩ := (mem_congK L ϖ).1 hB
  refine (mem_congK L ϖ).2 ⟨D + C * B, intM_add L hD (intM_mul L hC hB'), ?_⟩
  rw [add_mul, one_mul, smul_add, ← add_assoc, ← hBD, Matrix.smul_mul]

theorem congK_one (L : LocE F E) (ϖ : 𝒪[F]) {m i : ℕ} :
    (1 : Matrix (Fin m) (Fin m) E) ∈ congK L ϖ m i := fun a b => ⟨0, zero_mem _, by simp⟩

theorem horb_isCO (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {m i : ℕ} (hi : 1 ≤ i)
    (Γ : Matrix (Fin m) (Fin m) E) (hΓ : IsHerm L Γ) (hdet : IsUnit Γ.det) :
    IsCO (hermLat L m) (horb L ϖ Γ i) := by
  obtain ⟨j, hj⟩ := GlobalTheory.T.congruentOneMatrices_transitive_near_hermitian L ϖ hϖ m Γ hΓ hdet i hi
  obtain ⟨-, hcj, -, -, -, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hpu : ∀ n : ℕ, IsUnit (algebraMap F E ((ϖ : F) ^ n)) := fun n =>
    (IsUnit.mk0 _ (pow_ne_zero n hϖ0)).map _
  let A : AddSubgroup (Matrix (Fin m) (Fin m) E) :=
    (hermLat L m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))
  have hA : ∀ X, X ∈ A ↔ ∃ D, (IsHerm L D ∧ IsIntM L D) ∧ algebraMap F E ((ϖ : F) ^ j) • D = X := by
    intro X
    simp only [A, AddSubgroup.mem_map, mem_hermLat]
    rfl
  have hfin : ∀ (c : ℕ) (S : Set (Matrix (Fin m) (Fin m) E)),
      (∀ X ∈ S, IsHerm L X ∧ IsIntM L (algebraMap F E ((ϖ : F) ^ c) • X)) →
      ((QuotientAddGroup.mk : _ → _ ⧸ A) '' S).Finite := by
    intro c S hS
    let I : Ideal L.O := Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ (c + j))}
    haveI : Finite (L.O ⧸ I) := by
      apply Nat.finite_of_card_ne_zero
      rw [hcard]
      exact pow_ne_zero _ (by omega)
    refine finite_image_of_factor S (fun X => fun a b : Fin m =>
      if h : algebraMap F E ((ϖ : F) ^ c) * X a b ∈ L.O then Ideal.Quotient.mk I ⟨_, h⟩ else 0) _ ?_
    intro X hX Y hY hXY
    have key : ∀ a b, ∃ d ∈ L.O, Y a b - X a b = algebraMap F E ((ϖ : F) ^ j) * d := by
      intro a b
      have h := congrFun (congrFun hXY a) b
      have h1 : algebraMap F E ((ϖ : F) ^ c) * X a b ∈ L.O := (hS X hX).2 a b
      have h2 : algebraMap F E ((ϖ : F) ^ c) * Y a b ∈ L.O := (hS Y hY).2 a b
      simp only [dif_pos h1, dif_pos h2] at h
      have h3 := Ideal.Quotient.eq.1 h.symm
      have hI : I = Ideal.span {(⟨_, pow_mem' L ϖ (c + j)⟩ : L.O)} := by
        simp only [I]
        congr 1
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff]
      rw [hI, Ideal.mem_span_singleton'] at h3
      obtain ⟨d, hd⟩ := h3
      refine ⟨d, d.2, (hpu c).mul_left_cancel ?_⟩
      have h4 : (d : E) * algebraMap F E ((ϖ : F) ^ (c + j)) =
        algebraMap F E ((ϖ : F) ^ c) * Y a b - algebraMap F E ((ϖ : F) ^ c) * X a b :=
        congrArg Subtype.val hd
      rw [pow_add, map_mul] at h4
      linear_combination -h4
    choose D hD hDe using key
    rw [QuotientAddGroup.eq, hA]
    refine ⟨Matrix.of D, ⟨?_, hD⟩, ?_⟩
    · ext a b
      apply (hpu j).mul_left_cancel
      have h1 := congrFun (congrFun (hS X hX).1 a) b
      have h2 := congrFun (congrFun (hS Y hY).1 a) b
      have h3 := congrArg L.cj (hDe b a)
      simp only [cT, map_sub, map_mul, AlgEquiv.commutes] at h1 h2 h3
      simp only [cT, Matrix.of_apply]
      rw [← h3, h1, h2, hDe]
    · ext a b
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.add_apply,
        Matrix.neg_apply]
      linear_combination -hDe a b
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · have h := AddSubgroup.relIndex_ker (hermLat L m) (QuotientAddGroup.mk' A)
    rw [QuotientAddGroup.ker_mk'] at h
    rw [h]
    have : Finite ((hermLat L m).map (QuotientAddGroup.mk' A)) :=
      hfin 0 (hermLat L m) fun X hX => by simpa using (mem_hermLat L).1 hX
    exact Nat.card_pos.ne'
  · have : A ≤ hermLat L m := by
      intro X hX
      obtain ⟨D, hD, rfl⟩ := (hA X).1 hX
      refine (mem_hermLat L).2 ⟨?_, intM_smul L (pow_mem' L ϖ j) hD.2⟩
      ext a b
      have h1 := congrFun (congrFun hD.1 a) b
      simp only [cT] at h1
      simp only [cT, Matrix.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, h1]
    rw [AddSubgroup.relIndex_eq_one.2 this]
    exact one_ne_zero
  · intro X hX a ha
    obtain ⟨D, hD, rfl⟩ := (hA a).1 ha
    obtain ⟨B, hB, hXB⟩ := hj X hX D hD.1 hD.2
    obtain ⟨C, hC, rfl⟩ := hX
    refine ⟨C * B, congK_mul L ϖ hC hB, ?_⟩
    rw [hXB, cT_mul]
    simp only [Matrix.mul_assoc]
  · choose n hn using fun a b => exists_pow_mul_mem L ϖ hϖ (Γ a b)
    let c : ℕ := Finset.univ.sup fun ab : Fin m × Fin m => n ab.1 ab.2
    have hc : IsIntM L (algebraMap F E ((ϖ : F) ^ c) • Γ) := by
      intro a b
      have hle : n a b ≤ c :=
        Finset.le_sup (f := fun ab : Fin m × Fin m => n ab.1 ab.2) (Finset.mem_univ (a, b))
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hle
      rw [hk, pow_add, map_mul, Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_mem (pow_mem' L ϖ k) (hn a b)
    refine hfin c _ ?_
    rintro _ ⟨C, hC, rfl⟩
    have hCi := congK_int L ϖ hC
    constructor
    · unfold IsHerm at hΓ ⊢
      rw [cT_mul, cT_mul, cT_cT, hΓ, Matrix.mul_assoc]
    · rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      exact intM_mul L (intM_mul L (fun a b => (hcj _ (hCi b a)).1) hc) hCi

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem congK_group : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m i : ℕ), 1 ≤ i → (1 : Matrix (Fin m) (Fin m) E) ∈ congK L ϖ m i ∧ (∀ A ∈ congK L ϖ m i, IsIntM L A ∧ IsUnit A.det ∧ vE L ϖ (A.det * L.cj A.det) = 0 ∧ A⁻¹ ∈ congK L ϖ m i ∧ (∀ B ∈ congK L ϖ m i, A * B ∈ congK L ϖ m i) ∧ ∀ i' ≥ i, ∀ B ∈ congK L ϖ m i', A⁻¹ * B * A ∈ congK L ϖ m i' ∧ B ∈ congK L ϖ m i) ∧ ∀ Γ : Matrix (Fin m) (Fin m) E, IsHerm L Γ → IsUnit Γ.det → IsCO (hermLat L m) (horb L ϖ Γ i) ∧ 0 < cont (hermLat L m) (horb L ϖ Γ i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ m i hi
  refine ⟨congK_one L ϖ, fun A hA => ?_, fun Γ hΓ hdet => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := congK_basic L ϖ hϖ hi hA
    have hAi := congK_int L ϖ hA
    have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A h1
    refine ⟨hAi, h1, h2, ?_, fun B hB => congK_mul L ϖ hA hB, fun i' hi' B hB => ⟨?_, ?_⟩⟩
    · obtain ⟨C, hC, hAC⟩ := (mem_congK L ϖ).1 hA
      refine (mem_congK L ϖ).2 ⟨-(A⁻¹ * C), intM_neg L (intM_mul L h3 hC), ?_⟩
      have : A⁻¹ * (1 + algebraMap F E ((ϖ : F) ^ i) • C) = 1 := by rw [← hAC, hinv]
      rw [mul_add, mul_one, Matrix.mul_smul] at this
      rw [smul_neg, ← sub_eq_add_neg]
      exact eq_sub_of_add_eq this
    · obtain ⟨D, hD, rfl⟩ := (mem_congK L ϖ).1 hB
      refine (mem_congK L ϖ).2 ⟨A⁻¹ * D * A, intM_mul L (intM_mul L h3 hD) hAi, ?_⟩
      rw [mul_add, add_mul, mul_one, hinv, Matrix.mul_smul, Matrix.smul_mul]
    · obtain ⟨D, hD, rfl⟩ := (mem_congK L ϖ).1 hB
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi'
      refine (mem_congK L ϖ).2 ⟨_, intM_smul L (pow_mem' L ϖ k) hD, ?_⟩
      rw [pow_add, map_mul, mul_smul]
  · have h := horb_isCO L ϖ hϖ hi Γ hΓ hdet
    exact ⟨h, cont_pos _ _ h ⟨_, 1, congK_one L ϖ, rfl⟩⟩

end GlobalTheory.CongGrp
