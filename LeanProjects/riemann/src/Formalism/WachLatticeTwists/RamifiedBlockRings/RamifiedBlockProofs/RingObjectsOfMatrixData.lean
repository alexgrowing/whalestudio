import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.FinrankRangeEq

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem rank_block {K : Type*} [Field K] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
    (bl : d → α) (k : α) (M : Matrix d d K) (hM : ∀ a b, (bl a ≠ k ∨ bl b ≠ k) → M a b = 0) :
    (M.toSquareBlock bl k).rank = M.rank := by
  let P : Matrix {a // bl a = k} d K := Matrix.of fun i a => if (i : d) = a then (1 : K) else 0
  have h1 : M.toSquareBlock bl k = P * M * P.transpose := by
    ext i j
    simp [P, Matrix.mul_apply, Matrix.toSquareBlock_def, Matrix.transpose_apply]
  have h2 : M = P.transpose * M.toSquareBlock bl k * P := by
    ext a b
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.toSquareBlock_def]
    by_cases ha : bl a = k
    · by_cases hb : bl b = k
      · rw [Finset.sum_eq_single ⟨b, hb⟩]
        · rw [Finset.sum_eq_single ⟨a, ha⟩]
          · simp
          · intro i _ hi
            have hne : (i : d) ≠ a := fun h => hi (Subtype.ext h)
            simp [hne]
          · simp
        · intro j _ hj
          have hne : (j : d) ≠ b := fun h => hj (Subtype.ext h)
          simp [hne]
        · simp
      · rw [hM a b (Or.inr hb)]
        refine (Finset.sum_eq_zero fun j _ => ?_).symm
        have hne : (j : d) ≠ b := fun h => hb (by rw [← h]; exact j.2)
        simp [hne]
    · rw [hM a b (Or.inl ha)]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      refine mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _
      have hne : (i : d) ≠ a := fun h => ha (by rw [← h]; exact i.2)
      simp [hne]
  apply le_antisymm
  · rw [h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · calc M.rank = (P.transpose * M.toSquareBlock bl k * P).rank := congrArg Matrix.rank h2
      _ ≤ (M.toSquareBlock bl k).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem eDiag' (A : Type) [CommRing A] (d : Type) [Fintype d] [DecidableEq d] (S : d → Prop)
    [DecidablePred S] (β : d → A) (t : ℕ) (α : ℕ → A) :
    (Matrix.diagonal fun a => if S a then (1 : A) else 0) * ((List.range t).tail.map fun i =>
      (Matrix.diagonal fun a => if S a then β a else 0) -
        α i • (Matrix.diagonal fun a => if S a then (1 : A) else 0)).prod =
      Matrix.diagonal fun a => if S a then ∏ i ∈ Finset.Ioo 0 t, (β a - α i) else 0 := by
  have hc : ∀ f g : d → A, Matrix.diagonal f * Matrix.diagonal g =
      Matrix.diagonal g * Matrix.diagonal f := by
    intro f g
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _
  have hf : ∀ i, (Matrix.diagonal fun a => if S a then β a else 0) -
      α i • (Matrix.diagonal fun a => if S a then (1 : A) else 0) =
      Matrix.diagonal fun a => if S a then β a - α i else 0 := by
    intro i
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hs : S a <;> simp [hs]
    · simp [Matrix.diagonal_apply, hab]
  have hp : ∀ l : List ℕ, (Matrix.diagonal fun a => if S a then (1 : A) else 0) *
      (l.map fun i => Matrix.diagonal fun a => if S a then β a - α i else 0).prod =
      Matrix.diagonal fun a => if S a then (l.map fun i => β a - α i).prod else 0 := by
    intro l
    induction l with
    | nil => simp only [List.map_nil, List.prod_nil, mul_one]
    | cons x l ih =>
      rw [List.map_cons, List.prod_cons, ← mul_assoc, hc, mul_assoc, ih,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      by_cases hs : S a <;> simp [hs]
  have hl : ∀ f : ℕ → A, ((List.range t).tail.map f).prod = ∏ i ∈ Finset.Ioo 0 t, f i := by
    intro f
    have hnd : (List.range t).tail.Nodup :=
      List.Nodup.sublist (List.tail_sublist _) (List.nodup_range ..)
    rw [← List.prod_toFinset f hnd]
    congr 1
    ext x
    rw [List.mem_toFinset, Finset.mem_Ioo]
    cases t with
    | zero => simp
    | succ n =>
      rw [List.range_succ_eq_map, List.tail_cons, List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [List.mem_range] at hy
        omega
      · intro h
        exact ⟨x - 1, List.mem_range.2 (by omega), by omega⟩
  simp only [hf]
  rw [hp]
  congr 1
  funext a
  simp only [hl]

set_option maxHeartbeats 8000000 in
theorem ring_objects_of_matrix_data (hEM : StatEMat) (hSP : StatSplitPts) (hKO : StatIdemKO) : RingObjectsExist := by
  intro O _ _ _ X _ T d _ _ G _ r₀ π t ht bl χ₁ ε hP hA eB e₁ hI g₀ s hX
  obtain ⟨hloc, hpts, hG1, hbd, hc1, hχ⟩ := hP
  obtain ⟨heBm, he1m, heBB, he11, heB1, he1B, hrkB, hrk1, heBπ, he1π⟩ := hI
  obtain ⟨hsm, hes, hse, hsπ, hroots⟩ := hX
  let K := FractionRing O
  let ι : O →+* K := algebraMap O K
  have hι : Function.Injective ι := IsFractionRing.injective O K
  have huniq : ∀ a b : d, bl a ≠ 0 → bl a = bl b → a = b := by
    intro a b ha hab
    have hs : Subsingleton {x // bl x = bl a} :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 _ ha))
    exact congrArg Subtype.val (hs.elim ⟨a, rfl⟩ ⟨b, hab.symm⟩)
  let X0 : X → Matrix d d O := eB * r₀ g₀ * eB + s
  have hX0m : X0 ∈ tSpan T r₀ := add_mem_tSpan T r₀
    (mul_mem_tSpan T r₀ (mul_mem_tSpan T r₀ heBm (r_mem T r₀ g₀)) heBm) hsm
  let P : X → Polynomial O := fun x => blockPoly (eB x) (X0 x)
  have hPc : ∀ k, (fun x => (P x).coeff k) ∈ T := blockPolyT O X T d G r₀ hG1 eB heBm X0 hX0m
  have hPK : ∀ x, (P x).map ι = blockPoly ((eB x).map ι) ((X0 x).map ι) :=
    fun x => blockPoly_map ι _ _
  have hPr : ∀ x, ∃ α : Fin t → O, Function.Injective α ∧
      P x = ∏ i, (Polynomial.X - Polynomial.C (α i)) := by
    intro x
    obtain ⟨α, hα, h⟩ := hroots x
    obtain ⟨β, hβ, hPβ⟩ := rootsInt O (P x) t α (by rw [hPK]; exact h)
    exact ⟨β, fun i j hij => hα (by rw [← hβ, ← hβ, hij]), hPβ⟩
  obtain ⟨b, hb0, hb1, hb2⟩ := hSP O X T t P hPc hPr
  let X' := SplitPts t P
  let p : X' → X := fun y => y.1.1
  let T' : Subalgebra O (X' → O) := splitT T t P
  have hTT' : ∀ f ∈ T, (fun y : X' => f (p y)) ∈ T' :=
    fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  let rr : ℕ → T' := fun i =>
    if h : i < t then ⟨splitRoot t P ⟨i, h⟩, Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)⟩ else 0
  have hrr : ∀ i (h : i < t) (y : X'), (rr i).1 y = y.1.2 ⟨i, h⟩ := by
    intro i h y
    simp only [rr, dif_pos h]; rfl
  let rK : G →* (X' → Matrix d d K) :=
    { toFun := fun g y => (r₀ g (p y)).map ι
      map_one' := by funext y; simp
      map_mul' := fun g h => by funext y; simp [Matrix.map_mul] }
  let R' : Subalgebra O (X' → Matrix d d K) := spanSub T' rK
  letI iA : Algebra T' R' := algRp T' rK
  letI iE : ∀ x', Module T' (EvalSp O d R' x') := modEvRp T' rK
  have hpull : ∀ a ∈ tSpan T r₀, (fun y : X' => (a (p y)).map ι) ∈ tSpan T' rK := by
    rintro a ⟨S, c, hc, rfl⟩
    refine ⟨S, fun g y => c g (p y), fun g => hTT' _ (hc g), ?_⟩
    funext y; ext i j
    simp [Finset.sum_apply, Matrix.sum_apply, rK, ι]
    exact Finset.sum_congr rfl fun g _ => (Algebra.smul_def _ _).symm
  have hint : ∀ a ∈ tSpan T' rK, ∀ y, ∃ A : Matrix d d O, A.map ι = a y := by
    rintro a ⟨S, c, hc, rfl⟩ y
    refine ⟨∑ g ∈ S, c g y • r₀ g (p y), ?_⟩
    ext i j
    simp [Finset.sum_apply, Matrix.sum_apply, rK, ι]
    exact Finset.sum_congr rfl fun g _ => (Algebra.smul_def _ _).symm

  let γ : ℕ → O := fun i => (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)
  have heBπ' : eB π = Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0 := by
    rw [heBπ]; congr 1; funext a; by_cases h : bl a = 0 <;> simp [h]
  have hX0π : X0 π = Matrix.diagonal fun a => if bl a ≠ 0 then γ ((bl a : ℕ) - 1) else 0 := by
    show eB π * r₀ g₀ π * eB π + s π = _
    rw [hsπ, add_zero, heBπ']
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : bl i = 0
      · simp [hi]
      · simp [hi, hχ g₀ i hi, γ]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hb : bl i = bl j
      · have hi : bl i = 0 := by
          by_contra hi
          exact hij (huniq i j hi hb)
        simp [hi]
      · rw [hbd g₀ i j hb]; simp
  have hPπ : P π = ∏ i : Fin t, (Polynomial.X - Polynomial.C (γ i)) := by
    let F : Fin (t + 1) → Polynomial O :=
      fun c => if c ≠ 0 then Polynomial.X - Polynomial.C (γ ((c : ℕ) - 1)) else 1
    have h1 : P π = ∏ a : d, F (bl a) := by
      show blockPoly (eB π) (X0 π) = _
      rw [heBπ', hX0π]
      unfold blockPoly
      have h2 : ((Polynomial.X : Polynomial O) •
          (Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0).map Polynomial.C -
          (Matrix.diagonal fun a => if bl a ≠ 0 then γ ((bl a : ℕ) - 1) else 0).map Polynomial.C +
          (1 - Matrix.diagonal fun a => if bl a ≠ 0 then (1 : O) else 0).map Polynomial.C) =
          Matrix.diagonal fun a => F (bl a) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          by_cases hi : bl i = 0 <;> simp [hi, F]
        · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      rw [h2, Matrix.det_diagonal]
    have h3 : ∏ a : d, F (bl a) = ∏ c, F c := by
      rw [← Finset.prod_fiberwise univ bl (fun a => F (bl a))]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [Finset.prod_congr rfl (fun a ha => by rw [(mem_filter.mp ha).2]), Finset.prod_const]
      by_cases hc : c = 0
      · simp [hc, F]
      · have : #{a ∈ (univ : Finset d) | bl a = c} = 1 := by
          have h := hc1 c hc
          rw [Fintype.card_subtype] at h
          convert h
        rw [this, pow_one]
    rw [h1, h3, Fin.prod_univ_succ]
    simp [F, Fin.succ_ne_zero]
  let π' : X' := ⟨(π, fun i => γ i), hPπ⟩
  have hpπ : p π' = π := rfl
  have hrrπ : ∀ i, i < t → (rr i).1 π' = γ i := fun i h => hrr i h π'

  let ρf : R' → Matrix d d O := fun a => Classical.choose (hint a.1 a.2 π')
  have hρf : ∀ a : R', (ρf a).map ι = a.1 π' := fun a => Classical.choose_spec (hint a.1 a.2 π')
  have hent : ∀ (a : R') i j, ι (ρf a i j) = a.1 π' i j :=
    fun a i j => congrFun (congrFun (hρf a) i) j
  let ρπ : R' →ₐ[O] Matrix d d O :=
    { toFun := ρf
      map_one' := by
        ext i j; apply hι; rw [hent]
        show (1 : Matrix d d K) i j = ι ((1 : Matrix d d O) i j)
        by_cases h : i = j <;> simp [h, Matrix.one_apply]
      map_mul' := fun a b => by
        ext i j; apply hι; rw [hent]
        show (a.1 π' * b.1 π') i j = _
        simp only [Matrix.mul_apply, map_sum, map_mul, hent]
      map_zero' := by
        ext i j; apply hι; rw [hent]
        show (0 : Matrix d d K) i j = ι ((0 : Matrix d d O) i j)
        simp
      map_add' := fun a b => by
        ext i j; apply hι; rw [hent]
        show a.1 π' i j + b.1 π' i j = ι (ρf a i j + ρf b i j)
        rw [map_add, hent, hent]
      commutes' := fun c => by
        ext i j; apply hι; rw [hent]
        show (algebraMap O (Matrix d d K) c) i j = ι ((algebraMap O (Matrix d d O) c) i j)
        by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply, ι] }
  have hentπ : ∀ (a : R') i j, ι (ρπ a i j) = a.1 π' i j := hent
  have hBDK : ∀ a ∈ tSpan T' rK, ∀ i j, bl i ≠ bl j → a π' i j = 0 := by
    rintro a ⟨S, c, hc, rfl⟩ i j hij
    have : ∀ g, rK g π' i j = 0 := fun g => by
      show ι (r₀ g π i j) = 0
      rw [hbd g i j hij, map_zero]
    simp [Finset.sum_apply, Matrix.sum_apply, this]
  have hBD : ∀ (a : R') i j, bl i ≠ bl j → ρπ a i j = 0 := fun a i j hij => by
    apply hι; rw [hentπ, hBDK a.1 a.2 i j hij, map_zero]
  let ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O := fun k =>
    { toFun := fun a => (ρπ a).toSquareBlock bl k
      map_one' := by
        rw [map_one]
        ext i j
        by_cases h : i = j
        · subst h; simp [Matrix.toSquareBlock_def]
        · have h' : i.1 ≠ j.1 := fun e => h (Subtype.ext e)
          simp [Matrix.toSquareBlock_def, Matrix.one_apply, h, h']
      map_mul' := fun a b => by rw [map_mul]; exact blk_mul bl (hBD a) k
      map_zero' := by rw [map_zero]; ext i j; simp [Matrix.toSquareBlock_def]
      map_add' := fun a b => by rw [map_add]; ext i j; simp [Matrix.toSquareBlock_def]
      commutes' := fun c => by
        rw [AlgHom.commutes]
        ext i j
        by_cases h : i = j
        · subst h; simp [Matrix.toSquareBlock_def, Matrix.algebraMap_matrix_apply]
        · have h' : i.1 ≠ j.1 := fun e => h (Subtype.ext e)
          simp [Matrix.toSquareBlock_def, Matrix.algebraMap_matrix_apply, h, h'] }
  have hρk : ∀ k (a : R') i j, ρk k a i j = ρπ a i.1 j.1 := fun k a i j => rfl
  letI iB : ∀ k, Module T' (blockRestrictedRepresentationType bl ρk k) := fun k =>
    Module.compHom _ ((Pi.evalRingHom (fun _ : X' => O) π').comp T'.val.toRingHom)
  have hactB : ∀ k (a : R') (m : blockRestrictedRepresentationType bl ρk k), a • m = fun i => ∑ j, ρk k a i j • (m j : KO O) :=
    fun k a m => rfl
  have hTB : ∀ (f : T') k (m : blockRestrictedRepresentationType bl ρk k), f • m = (f.1 π') • m := fun f k m => rfl
  have hTE : ∀ (f : T') x' (v : EvalSp O d R' x'), f • v = ι (f.1 x') • v := fun f x' v => rfl

  let rR : G →* R' :=
    { toFun := fun g => ⟨rK g, r_mem' T' rK g⟩
      map_one' := Subtype.ext (map_one rK)
      map_mul' := fun g h => Subtype.ext (map_mul rK g h) }
  let χ : G →* (T')ˣ := (Units.map (algebraMap O T').toMonoidHom).comp χ₁
  let eB' : R' := ⟨fun y => (eB (p y)).map ι, hpull eB heBm⟩
  let e₁' : R' := ⟨fun y => (e₁ (p y)).map ι, hpull e₁ he1m⟩
  let X₀' : R' := ⟨fun y => (X0 (p y)).map ι, hpull X0 hX0m⟩
  let E : R' := eB' * ((List.range t).tail.map fun i => X₀' - rr i • eB').prod
  let δ : T' := ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i)
  have hsv : ∀ (f : T') (a : R') y, (f • a : R').1 y = ι (f.1 y) • a.1 y := smul_val T' rK
  have hEy : ∀ y, E.1 y = eB'.1 y *
      ((List.range t).tail.map fun i => X₀'.1 y - ι ((rr i).1 y) • eB'.1 y).prod := by
    intro y
    show evalAt O d R' y E = _
    rw [map_mul, map_list_prod, List.map_map]
    refine congrArg₂ _ rfl (congrArg List.prod (List.map_congr_left fun i _ => ?_))
    show X₀'.1 y - (rr i • eB' : R').1 y = _
    rw [hsv]
  have hδy : ∀ y, ι (δ.1 y) = ∏ i ∈ Finset.Ioo 0 t, (ι ((rr 0).1 y) - ι ((rr i).1 y)) := by
    intro y
    have h1 : δ.1 y = ∏ i ∈ Finset.Ioo 0 t, ((rr 0).1 y - (rr i).1 y) := by
      show ((Pi.evalRingHom (fun _ : X' => O) y).comp T'.val.toRingHom) δ = _
      rw [map_prod]; rfl
    rw [h1, map_prod]
    simp only [map_sub]
  have heX0 : eB * X0 = X0 := by
    show eB * (eB * r₀ g₀ * eB + s) = eB * r₀ g₀ * eB + s
    rw [mul_add, hes, ← mul_assoc, ← mul_assoc, heBB]
  have hX0e : X0 * eB = X0 := by
    show (eB * r₀ g₀ * eB + s) * eB = eB * r₀ g₀ * eB + s
    rw [add_mul, hse, mul_assoc, heBB]
  have hmapmul : ∀ (u v w : X → Matrix d d O), u * v = w → ∀ x, (u x).map ι * (v x).map ι = (w x).map ι := by
    intro u v w h x
    rw [← Matrix.map_mul, ← h]; rfl
  have hyinj : ∀ y : X', Function.Injective y.1.2 := by
    intro y
    obtain ⟨α, hα, hPα⟩ := hPr (p y)
    have h2 : (P (p y)).map ι = ∏ i, (Polynomial.X - Polynomial.C (ι (y.1.2 i))) := by
      rw [show P (p y) = _ from y.2, Polynomial.map_prod]; simp
    have h3 : (P (p y)).map ι = ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
      rw [hPα, Polynomial.map_prod]; simp
    have h4 := inj_of_prod_eq (fun i => ι (y.1.2 i)) (fun i => ι (α i)) (hι.comp hα) (h2.symm.trans h3)
    exact fun i j hij => h4 (congrArg ι hij)
  have hpoly : ∀ y : X', blockPoly (eB'.1 y) (X₀'.1 y) =
      ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (ι ((rr i).1 y))) := by
    intro y
    show blockPoly ((eB (p y)).map ι) ((X0 (p y)).map ι) = _
    rw [← hPK, show P (p y) = _ from y.2, Polynomial.map_prod, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hrr i.1 i.2 y]; simp
  have hpt : ∀ y : X', E.1 y * E.1 y = ι (δ.1 y) • E.1 y ∧ (E.1 y).rank = 1 ∧ ι (δ.1 y) ≠ 0 := by
    intro y
    obtain ⟨h1, h2, -, -, -, h6⟩ := hEM K d (eB'.1 y) (X₀'.1 y) t (fun i => ι ((rr i).1 y)) ht
      (hmapmul eB eB eB heBB (p y)) (hmapmul eB X0 X0 heX0 (p y)) (hmapmul X0 eB X0 hX0e (p y))
      (hpoly y) (fun i j hi hj hij => by
        have hij' : ι ((rr i).1 y) = ι ((rr j).1 y) := hij
        rw [hrr i hi, hrr j hj] at hij'
        exact congrArg Fin.val (hyinj y (hι hij')))
    rw [hEy, hδy]
    exact ⟨h1, h2, h6⟩

  let δO : O := δ.1 π'
  let val : d → K := fun a => if bl a ≠ 0 then
    ∏ i ∈ Finset.Ioo 0 t, (ι (γ ((bl a : ℕ) - 1)) - ι ((rr i).1 π')) else 0
  have hEπ : E.1 π' = Matrix.diagonal val := by
    rw [hEy]
    have h1 : eB'.1 π' = Matrix.diagonal fun a => if bl a ≠ 0 then (1 : K) else 0 := by
      show (eB π).map ι = _
      rw [heBπ']
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hi : bl i = 0 <;> simp [hi]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have h2 : X₀'.1 π' = Matrix.diagonal fun a => if bl a ≠ 0 then ι (γ ((bl a : ℕ) - 1)) else 0 := by
      show (X0 π).map ι = _
      rw [hX0π]
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hi : bl i = 0 <;> simp [hi]
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [h1, h2]
    exact eDiag' K d (fun a => bl a ≠ 0) (fun a => ι (γ ((bl a : ℕ) - 1))) t
      (fun i => ι ((rr i).1 π'))
  have hval0 : ∀ a, bl a = 0 → val a = 0 := fun a h => by simp [val, h]
  have hval1 : ∀ a, (bl a : ℕ) = 1 → val a = ι δO := fun a h => by
    have h0 : bl a ≠ 0 := fun e => by rw [e] at h; simp at h
    simp only [val, if_pos h0, h, Nat.sub_self]
    rw [hδy, hrrπ 0 (by omega)]
  have hval2 : ∀ a, 2 ≤ (bl a : ℕ) → val a = 0 := fun a h => by
    have h0 : bl a ≠ 0 := fun e => by rw [e] at h; simp at h
    simp only [val, if_pos h0]
    have hlt : (bl a : ℕ) - 1 < t := by have := (bl a).2; omega
    refine Finset.prod_eq_zero (i := (bl a : ℕ) - 1) (Finset.mem_Ioo.mpr ⟨by omega, hlt⟩) ?_
    rw [hrrπ _ hlt, sub_self]
  have hscal : ∀ k (a : R') (w : O),
      (∀ i j : {a // bl a = k}, a.1 π' i.1 j.1 = if i = j then ι w else 0) →
      ∀ m : blockRestrictedRepresentationType bl ρk k, a • m = w • m := by
    intro k a w h m
    rw [hactB]
    funext i
    have h1 : ∀ j, ρk k a i j = if i = j then w else 0 := fun j => by
      apply hι; rw [hρk, hentπ, h]; split_ifs <;> simp
    show ∑ j, ρk k a i j • (m j : KO O) = w • (m i : KO O)
    simp only [h1, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hEblk : ∀ k (w : O), (∀ a, bl a = k → val a = ι w) → ∀ m : blockRestrictedRepresentationType bl ρk k, E • m = w • m := by
    intro k w h
    refine hscal k E w fun i j => ?_
    rw [hEπ, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [h i.1 i.2]
    · have h' : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
      simp [hij, h']
  have he1blk : ∀ k, k ≠ 0 → ∀ m : blockRestrictedRepresentationType bl ρk k, e₁' • m = 0 := by
    intro k hk m
    rw [hscal k e₁' 0 (fun i j => by
      show ι (e₁ π i.1 j.1) = _
      rw [he1π i.1 j.1 (Or.inl (by rw [i.2]; exact hk))]; simp), zero_smul]
  obtain ⟨sE, cE, hcE, hEsum⟩ := (E.2 : E.1 ∈ tSpan T' rK)
  let tE : G → T' := fun g => ⟨cE g, hcE g⟩
  have hEs : E = ∑ g ∈ sE, tE g • rR g := Subtype.ext (by
    show E.1 = R'.val (∑ g ∈ sE, tE g • rR g)
    rw [hEsum, map_sum]
    exact Finset.sum_congr rfl fun g _ => funext fun y => (hsv (tE g) (rR g) y).symm)
  let τ : T' := ∑ g ∈ sE, tE g * ((χ g : (T')ˣ) : T')
  let c1 : Fin (t + 1) := ⟨1, by omega⟩
  have hc10 : c1 ≠ 0 := fun e => by simpa [c1] using congrArg Fin.val e
  obtain ⟨a1⟩ : Nonempty {a // bl a = c1} := Fintype.card_pos_iff.mp (by rw [hc1 c1 hc10]; norm_num)
  have hτ : τ.1 π' = δO := by
    apply hι
    have h1 : τ.1 π' = ∑ g ∈ sE, cE g π' * (χ₁ g : O) := by
      show ((Pi.evalRingHom (fun _ : X' => O) π').comp T'.val.toRingHom) τ = _
      rw [map_sum]; rfl
    have h2 : E.1 π' a1.1 a1.1 = ι δO := by
      rw [hEπ, Matrix.diagonal_apply_eq]
      exact hval1 a1.1 (by rw [a1.2])
    rw [← h2, hEsum, h1, map_sum]
    simp only [Finset.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    show _ = ι (cE g π') • ι (r₀ g π a1.1 a1.1)
    rw [hχ g a1.1 (by rw [a1.2]; exact hc10), a1.2]
    simp [c1]
  have hfinX : Finite X' := by
    let Zs : Finset O := univ.biUnion fun x => (P x).roots.toFinset
    let f : X' → X × (Fin t → Zs) := fun y => (y.1.1, fun i => ⟨y.1.2 i, by
      refine mem_biUnion.mpr ⟨y.1.1, mem_univ _, ?_⟩
      have hy : P y.1.1 = ∏ i, (Polynomial.X - Polynomial.C (y.1.2 i)) := y.2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      refine ⟨?_, ?_⟩
      · rw [hy]
        exact (Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _).ne_zero
      · rw [Polynomial.IsRoot, hy, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (mem_univ i) (by simp)⟩)
    refine Finite.of_injective f fun y y' h => ?_
    have h1 : y.1.1 = y'.1.1 := congrArg (fun z => z.1) h
    have h2 : ∀ i, y.1.2 i = y'.1.2 i := fun i => congrArg (fun z => (z.2 i).1) h
    exact Subtype.ext (Prod.ext h1 (funext h2))
  have i1 : IsNoetherian R' R' := noeth O X' d R' (fun a ha x' i j => by
    obtain ⟨A, hA'⟩ := hint a ha x'
    exact ⟨A i j, congrFun (congrFun hA' i) j⟩)
  have i2 : ∀ x', IsScalarTower T' R' (EvalSp O d R' x') := fun x' => ⟨fun f a v => by
    rw [hTE]
    funext i
    show ∑ j, (f • a : R').1 x' i j • (v j : K) = ι (f.1 x') • ∑ j, a.1 x' i j • (v j : K)
    rw [hsv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]⟩
  have i3 : ∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k) := fun k =>
    ⟨fun a c m => LinearMap.map_smul (matEnd O (KO O) _ ((ρk k).toRingHom a)) c m⟩
  have hρsm : ∀ (f : T') (a : R') i j, ρπ (f • a) i j = f.1 π' * ρπ a i j := by
    intro f a i j
    apply hι
    rw [hentπ, hsv, map_mul, hentπ]; rfl
  have i4 : ∀ k, IsScalarTower T' R' (blockRestrictedRepresentationType bl ρk k) := fun k => ⟨fun f a m => by
    rw [hTB]
    funext i
    show ∑ j, ρk k (f • a) i j • (m j : KO O) = f.1 π' • ∑ j, ρk k a i j • (m j : KO O)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hρk, hρsm, mul_smul]; rfl⟩
  have i5 : ∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k) := fun k => ⟨fun c a m => by
    funext i
    show ∑ j, ρk k (c • a) i j • (m j : KO O) = c • ∑ j, ρk k a i j • (m j : KO O)
    rw [Finset.smul_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_smul]⟩
  have hρr : ∀ g, ρπ (rR g) = r₀ g π := fun g => by
    ext i j; apply hι; rw [hentπ]; rfl
  have hsurj : ∀ k, Function.Surjective (ρk k) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      let ρ0 : G →* Matrix {a // bl a = 0} {a // bl a = 0} O :=
        ((ρk 0).toRingHom.toMonoidHom).comp rR
      have h0 : (fun g => (ρ0 g).map (IsLocalRing.residue O)) =
          fun g => ((r₀ g π).toSquareBlock bl 0).map (IsLocalRing.residue O) := funext fun g => by
        show ((ρπ (rR g)).toSquareBlock bl 0).map _ = _
        rw [hρr]
      have hspan := ontoSpan O _ G ρ0 (h0 ▸ hA)
      intro B
      have hB : B ∈ Submodule.span O (Set.range ρ0) := hspan ▸ Submodule.mem_top
      have hle : Submodule.span O (Set.range ρ0) ≤ LinearMap.range (ρk 0).toLinearMap :=
        Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact ⟨rR g, rfl⟩)
      obtain ⟨a, ha⟩ := hle hB
      exact ⟨a, ha⟩
    · intro B
      have hs : Subsingleton {a // bl a = k} :=
        Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 k hk))
      obtain ⟨i0⟩ : Nonempty {a // bl a = k} :=
        Fintype.card_pos_iff.mp (by rw [hc1 k hk]; norm_num)
      refine ⟨algebraMap O R' (B i0 i0), ?_⟩
      rw [AlgHom.commutes]
      ext i j
      rw [hs.elim i i0, hs.elim j i0]
      simp [Matrix.algebraMap_matrix_apply]
  have he1e1 : e₁' * e₁' = e₁' := Subtype.ext (funext fun y => hmapmul e₁ e₁ e₁ he11 (p y))
  have hKO1 : Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁')) ≃ₗ[O] KO O) := by
    have h1 : DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁' = matEnd O (KO O) _ (ρk 0 e₁') :=
      LinearMap.ext fun m => rfl
    rw [h1]
    refine hKO O _ (ρk 0 e₁') (by rw [← map_mul, he1e1]) ?_
    have h2 : (ρk 0 e₁').map (algebraMap O (FractionRing O)) = ((e₁ π).map ι).toSquareBlock bl 0 := by
      ext i j
      exact hentπ e₁' i.1 j.1
    rw [h2, rank_block bl 0 ((e₁ π).map ι) (fun a b hab => by
      show ι (e₁ π a b) = 0
      rw [he1π a b hab, map_zero])]
    exact hrk1 π
  have hχinv : ∀ g, (((χ g)⁻¹ : (T')ˣ) : T').1 π' = (((χ₁ g)⁻¹ : Oˣ) : O) := fun g => by
    rw [← map_inv, ← map_inv]; rfl
  have hu1 : ∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt rR χ g • m = m := by
    intro g m
    have hs : Subsingleton {a // bl a = c1} :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 c1 hc10))
    rw [hscal c1 (uElt rR χ g) 1 (fun i j => by
      rw [if_pos (hs.elim i j), hs.elim j i]
      show ((((χ g)⁻¹ : (T')ˣ) : T') • rR g : R').1 π' i.1 i.1 = ι 1
      rw [hsv, hχinv]
      show ι _ • ι (r₀ g π i.1 i.1) = ι 1
      rw [hχ g i.1 (by rw [i.2]; exact hc10), i.2]
      have h0 : ((c1 : Fin (t + 1)) : ℕ) - 1 = 0 := rfl
      rw [h0, pow_zero, Units.val_one, mul_one, smul_eq_mul, ← map_mul, Units.inv_mul]), one_smul]
  have hG1' : ∀ (g : G) (k : ℕ), FromT T' (fun x => (Matrix.charpolyRev (rK g x)).coeff k) :=
    fun g k => ⟨fun y => (Matrix.charpolyRev (r₀ g (p y))).coeff k, hTT' _ (hG1 g k), fun y => by
      show ι _ = (Matrix.charpolyRev ((r₀ g (p y)).map ι)).coeff k
      rw [← charpolyRev_map, Polynomial.coeff_map]⟩
  have hcomp : (R'.val.toRingHom.toMonoidHom.comp rR) = rK := MonoidHom.ext fun g => rfl
  let D : RingData O X d G t bl :=
    { X' := X', T' := T', p := p, q := t.factorial, b := b, R' := R', algT := iA, modEv := iE,
      r := rR, χ := χ, eB := eB', e₁ := e₁', X₀ := X₀', E := E, rr := rr, π' := π', ρπ := ρπ,
      ρk := ρk, blockModuleStructure := iB, sE := sE, tE := tE }
  refine ⟨D, ⟨hpoly, ?_, ?_, rfl, rfl, hrrπ, fun g x' => rfl, ?_, hsv, hTE, hTB, fun g x' => rfl,
    fun x' => rfl, fun x' => rfl, fun x' => rfl, rfl, hρf, fun a k => rfl, hb0, hb1, ?_, hEs⟩,
    ⟨i1, i2, i3, i4, i5⟩, i3, ?_⟩
  · intro x α h
    have hPx : P x = ∏ i : Fin t, (Polynomial.X - Polynomial.C (α i)) := by
      apply Polynomial.map_injective ι hι
      rw [hPK, Polynomial.map_prod]
      refine Eq.trans h ?_
      rw [Finset.prod_range]
      exact Finset.prod_congr rfl fun i _ => by simp [ι] <;> rfl
    refine ⟨⟨(x, fun i => α i), hPx⟩, ⟨rfl, fun i hi => hrr i hi _⟩, ?_⟩
    rintro y ⟨hy1, hy2⟩
    exact Subtype.ext (Prod.ext hy1 (funext fun i => by
      rw [← hrr i.1 i.2 y]; exact hy2 i.1 i.2))
  · show Algebra.adjoin O _ = Algebra.adjoin O _
    congr 2
    ext f'
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, funext fun y => (hrr i.1 i.2 y).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, funext fun y => (hrr i hi y).symm⟩
  · intro a
    show a ∈ R' ↔ a ∈ tSpan T' (R'.val.toRingHom.toMonoidHom.comp rR)
    rw [hcomp]
    exact Iff.rfl
  · intro a _ h0
    funext k x
    refine congrFun (hb2 x (fun k => a k x) fun x' hx' => ?_) k
    have h1 := congrFun h0 x'
    rw [Finset.sum_apply] at h1
    rw [← hx']
    exact h1
  · show RingTop O X X' T T' p t.factorial b d R' T' G rR χ E e₁' δ π' ρπ t ht bl ρk sE tE δO
    refine ⟨hb1, hb2, fun g _ _ Θ => eta_determinant_comparison det_poly_statement blockDet O X' G T' d R' rK hG1'
      (fun a ha => ha) g Θ, ?_, he1e1, ?_, hρf, fun a i j hij => hBD a i j (ne_of_gt hij), hsurj,
      fun a k => rfl, hc1, hEs, ?_, fun m => hTB δ 0 m, ?_, hKO1, ?_, hu1, he1blk c1 hc10, ?_,
      fun m => hTB δ c1 m⟩
    · exact Subtype.ext (funext fun y => by
        show E.1 y * E.1 y = (scal T' rK δ).1 y * E.1 y
        rw [(hpt y).1, scal_apply, Matrix.smul_mul, Matrix.one_mul])
    · exact fun x' => ⟨ι (δ.1 x'), (hpt x').2.2, fun v => hTE δ x' v,
        by rw [finrank_range_eq]; exact (hpt x').2.1, by rw [finrank_range_eq]; exact hrk1 (p x')⟩
    · intro m
      rw [hEblk 0 0 (fun a ha => by rw [hval0 a ha, map_zero]), zero_smul]
    · intro m
      rw [hTB τ 0 m, hτ]
    · intro c hc
      have hc0 : c ≠ 0 := fun e => by rw [e] at hc; simp at hc
      refine ⟨he1blk c hc0, fun m => ?_, fun m => hTB δ c m, fun m => ?_⟩
      · rw [hEblk c 0 (fun a ha => by rw [hval2 a (by rw [ha]; exact hc), map_zero]), zero_smul]
      · rw [hTB τ c m, hτ]
    · exact hEblk c1 δO (fun a ha => hval1 a (by rw [ha]))

end Formalism.RepresentationBoundsCohomology.ringDataObjects
