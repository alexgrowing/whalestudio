import Mathlib
import GroundTheory.AutomorphicForms.SphericalSatake

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

variable (F) in

def Bdd (t : ℤ) (x : F) : Prop := valuation F x ≤ valuation F (uniformizer F : F) ^ t

theorem valuation_uniformizer_pos : 0 < valuation F (uniformizer F : F) :=
  zero_lt_iff.2 (valuation_uniformizer_ne_zero F)

theorem bdd_zero (t : ℤ) : Bdd F t 0 := by
  simp [Bdd]

theorem Bdd.add {t : ℤ} {x y : F} (hx : Bdd F t x) (hy : Bdd F t y) : Bdd F t (x + y) :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem Bdd.neg {t : ℤ} {x : F} (hx : Bdd F t x) : Bdd F t (-x) := by
  rwa [Bdd, Valuation.map_neg]

theorem bdd_sum {ι : Type*} (s : Finset ι) {t : ℤ} {f : ι → F} (h : ∀ i ∈ s, Bdd F t (f i)) :
    Bdd F t (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bdd_zero t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Bdd.mul {s t : ℤ} {x y : F} (hx : Bdd F s x) (hy : Bdd F t y) : Bdd F (s + t) (x * y) := by
  rw [Bdd, map_mul, zpow_add₀ (valuation_uniformizer_ne_zero F)]
  exact mul_le_mul' hx hy

theorem bdd_prod {ι : Type*} (s : Finset ι) {t : ι → ℤ} {f : ι → F} (h : ∀ i ∈ s, Bdd F (t i) (f i)) :
    Bdd F (∑ i ∈ s, t i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bdd]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem bdd_of_mem {x : F} (hx : x ∈ 𝒪[F]) : Bdd F 0 x := by
  rw [Bdd, zpow_zero]
  exact hx

theorem Bdd.mono {s t : ℤ} {x : F} (hx : Bdd F t x) (h : s ≤ t) : Bdd F s x :=
  hx.trans (zpow_le_zpow_right_of_le_one₀ valuation_uniformizer_pos
    (valuation_uniformizer_lt_one F).le h)

theorem bdd_zpow (t : ℤ) : Bdd F t ((uniformizer F : F) ^ t) := by
  rw [Bdd, map_zpow₀]

theorem le_of_bdd_zpow {s t : ℤ} (h : Bdd F t ((uniformizer F : F) ^ s)) : t ≤ s := by
  rwa [Bdd, map_zpow₀, zpow_le_zpow_iff_right_of_lt_one₀ valuation_uniformizer_pos
    (valuation_uniformizer_lt_one F)] at h

theorem mem_of_bdd {x : F} (h : Bdd F 0 x) : x ∈ 𝒪[F] := by
  rw [Bdd, zpow_zero] at h
  exact h

theorem det_mem_of_forall_mem {m : ℕ} {M : Matrix (Fin m) (Fin m) F} (hM : ∀ i j, M i j ∈ 𝒪[F]) :
    M.det ∈ 𝒪[F] := by
  let N : Matrix (Fin m) (Fin m) 𝒪[F] := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have : M = N.map (𝒪[F]).subtype := by
    ext i j
    rfl
  have h := RingHom.map_det (𝒪[F]).subtype N
  rw [RingHom.mapMatrix_apply] at h
  rw [this, ← h]
  exact (N.det).2

def tailEmb {m : ℕ} (hm : m ≤ n) (j : Fin m) : Fin n := ⟨n - m + j, by omega⟩

theorem tailEmb_injective {m : ℕ} (hm : m ≤ n) : Function.Injective (tailEmb hm) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [tailEmb] at this
  exact Fin.ext (by omega)

def tailSum (ν : Fin n → ℤ) {m : ℕ} (hm : m ≤ n) : ℤ := ∑ j : Fin m, ν (tailEmb hm j)

theorem tailSum_le_sum {ν : Fin n → ℤ} (hν : Antitone ν) {m : ℕ} (hm : m ≤ n) (S : Finset (Fin n))
    (hS : S.card = m) : tailSum ν hm ≤ ∑ i ∈ S, ν i := by
  classical
  set T := Finset.univ.image (tailEmb hm)
  have hT : T.card = m := by
    rw [Finset.card_image_of_injective _ (tailEmb_injective hm), Finset.card_univ, Fintype.card_fin]
  have hsumT : tailSum ν hm = ∑ i ∈ T, ν i := by
    rw [Finset.sum_image fun a _ b _ h => tailEmb_injective hm h]
    rfl
  have hmemT : ∀ y ∈ T, n - m ≤ y.val := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    simp [tailEmb]
  have hnotT : ∀ x, x ∉ T → x.val < n - m := by
    intro x hx
    by_contra h
    exact hx (Finset.mem_image.2 ⟨⟨x.val - (n - m), by omega⟩, Finset.mem_univ _,
      Fin.ext (by simp [tailEmb]; omega)⟩)
  have e1 := Finset.sum_sdiff (f := ν) (Finset.inter_subset_left (s₁ := S) (s₂ := T))
  have e2 := Finset.sum_sdiff (f := ν) (Finset.inter_subset_left (s₁ := T) (s₂ := S))
  rw [Finset.sdiff_inter_self_left] at e1 e2
  rw [Finset.inter_comm T S] at e2
  rw [hsumT, ← e1, ← e2]
  suffices key : ∑ i ∈ T \ S, ν i ≤ ∑ i ∈ S \ T, ν i by linarith
  have hcard : (T \ S).card = (S \ T).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm, hS, hT]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have : S = ∅ := Finset.card_eq_zero.1 hS
    have : T = ∅ := Finset.card_eq_zero.1 hT
    simp [*]
  · set c := ν ⟨n - m, by omega⟩
    calc ∑ i ∈ T \ S, ν i ≤ (T \ S).card • c :=
          Finset.sum_le_card_nsmul _ _ _ fun y hy =>
            hν (show (⟨n - m, by omega⟩ : Fin n) ≤ y from hmemT y (Finset.mem_sdiff.1 hy).1)
      _ = (S \ T).card • c := by rw [hcard]
      _ ≤ ∑ i ∈ S \ T, ν i :=
          Finset.card_nsmul_le_sum _ _ _ fun x hx =>
            hν (show x ≤ (⟨n - m, by omega⟩ : Fin n) from
              (Fin.le_def.2 (hnotT x (Finset.mem_sdiff.1 hx).2).le))

theorem bdd_det_submatrix {A B : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    (hB : ∀ i j, B i j ∈ 𝒪[F]) {ν : Fin n → ℤ} (hν : Antitone ν) {m : ℕ} (hm : m ≤ n)
    (r c : Fin m → Fin n) :
    Bdd F (tailSum ν hm)
      ((A * diagonal (fun i => (uniformizer F : F) ^ ν i) * B).submatrix r c).det := by
  classical
  set d : Fin n → F := fun i => (uniformizer F : F) ^ ν i
  set vec : Fin n → Fin m → F := fun l a => A (r a) l
  have hT : ((A * diagonal d * B).submatrix r c)ᵀ =
      fun j => ∑ l, (d l * B l (c j)) • vec l := by
    funext j a
    simp only [transpose_apply, submatrix_apply, Matrix.mul_apply, mul_diagonal, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, vec]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (∑ x, A (r a) x * diagonal d x l) = A (r a) l * d l by simp [diagonal_apply]]
    ring
  rw [← det_transpose, hT]
  change Bdd F _ ((detRowAlternating : (Fin m → F) [⋀^Fin m]→ₗ[F] F).toMultilinearMap
    (fun j => ∑ l, (d l * B l (c j)) • vec l))
  rw [MultilinearMap.map_sum]
  refine bdd_sum _ fun p _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  by_cases hp : Function.Injective p
  · have h1 : Bdd F (∑ j, ν (p j)) (∏ j, d (p j) * B (p j) (c j)) := by
      have := bdd_prod (Finset.univ : Finset (Fin m)) (t := fun j => ν (p j) + 0)
        (f := fun j => d (p j) * B (p j) (c j)) fun j _ => (bdd_zpow _).mul (bdd_of_mem (hB _ _))
      simpa using this
    have h2 : Bdd F 0 ((detRowAlternating : (Fin m → F) [⋀^Fin m]→ₗ[F] F).toMultilinearMap
        fun j => vec (p j)) := by
      refine bdd_of_mem ?_
      change (Matrix.of fun j a => A (r a) (p j)).det ∈ 𝒪[F]
      exact det_mem_of_forall_mem fun _ _ => hA _ _
    have h3 : tailSum ν hm ≤ ∑ j, ν (p j) := by
      have := tailSum_le_sum hν hm (Finset.univ.image p)
        (by rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin])
      rwa [Finset.sum_image fun a _ b _ h => hp h] at this
    simpa using (h1.mul h2).mono (by simpa using h3)
  · have : (detRowAlternating : (Fin m → F) [⋀^Fin m]→ₗ[F] F).toMultilinearMap
        (fun j => vec (p j)) = 0 := by
      rw [AlternatingMap.coe_multilinearMap]
      refine AlternatingMap.map_eq_zero_of_not_injective _ _ fun hinj => hp fun i j hij => ?_
      exact hinj (by simp only [hij])
    rw [this, mul_zero]
    exact bdd_zero _

theorem prod_zpow_uniformizer {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, (uniformizer F : F) ^ f i = (uniformizer F : F) ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
      zpow_add₀ (Cartan.uniformizer_ne_zero F)]

variable (F n) in

def cartanType (g : GL (Fin n) F) : Fin n → ℤ :=
  (Cartan.existsUnique_mem_doubleCoset F n g).exists.choose

theorem cartanType_spec (g : GL (Fin n) F) :
    Cartan.IsDominant (cartanType F n g) ∧
      g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n (cartanType F n g))
        (integralGL F n : Set (GL (Fin n) F)) (integralGL F n) :=
  (Cartan.existsUnique_mem_doubleCoset F n g).exists.choose_spec

theorem cartanType_eq {g : GL (Fin n) F} {μ : Fin n → ℤ} (hμ : Cartan.IsDominant μ)
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n μ)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    cartanType F n g = μ :=
  (Cartan.existsUnique_mem_doubleCoset F n g).unique (cartanType_spec g) ⟨hμ, hg⟩

theorem diagPow_eq_torusPow (μ : Fin n → ℤ) : Cartan.diagPow F n μ = torusPow F n μ :=
  Units.ext (by rw [Cartan.coe_diagPow, coe_torusPow])

theorem det_submatrix_tailEmb {u : GL (Fin n) F} (hu : u ∈ unipotent F n) (l : Fin n → ℤ) {m : ℕ}
    (hm : m ≤ n) :
    (((u * torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix (tailEmb hm)
      (tailEmb hm)).det = (uniformizer F : F) ^ tailSum l hm := by
  have hB : u * torusPow F n l ∈ borel F n := (borel F n).mul_mem hu.1 (torusPow_mem_borel F n l)
  have hmono : StrictMono (tailEmb hm) := fun i j hij => by
    simp only [tailEmb, Fin.lt_def] at hij ⊢
    omega
  have hup : (((u * torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix (tailEmb hm)
      (tailEmb hm)).IsUpperTriangular := fun i j hij => hB (hmono hij)
  rw [det_of_isUpperTriangular hup, tailSum, ← prod_zpow_uniformizer]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [submatrix_apply, Units.val_mul, coe_torusPow, mul_diagonal]
  have := hu.2 (tailEmb hm j)
  rw [this, one_mul]

theorem valuation_det_eq_one {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    valuation F (k : Matrix (Fin n) (Fin n) F).det = 1 := by
  have h1 := det_mem_of_forall_mem ((mem_integralGL_iff F n).1 hk).1
  have h2 := det_mem_of_forall_mem ((mem_integralGL_iff F n).1 hk).2
  have hu : IsUnit (⟨_, h1⟩ : 𝒪[F]) := IsUnit.of_mul_eq_one (⟨_, h2⟩ : 𝒪[F]) (Subtype.ext (by
    simp only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]
    rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]))
  exact (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.1 hu

theorem tailSum_le_iwasawaExponent {ν : Fin n → ℤ} (hν : Cartan.IsDominant ν) {g : GL (Fin n) F}
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n ν)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) {m : ℕ} (hm : m ≤ n) :
    tailSum ν hm ≤ tailSum (iwasawaExponent F n g) hm := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (Cartan.mem_doubleCoset_diagPow F n).1 hg
  obtain ⟨u, hu, k, hk, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F n
    (k₁ * Cartan.diagPow F n ν * k₂)
  set l := iwasawaExponent F n (k₁ * Cartan.diagPow F n ν * k₂)
  have heq : u * torusPow F n l = k₁ * Cartan.diagPow F n ν * (k₂ * k⁻¹) := by
    rw [← mul_assoc, he, mul_inv_cancel_right]
  have hb := bdd_det_submatrix (((mem_integralGL_iff F n).1 hk₁).1)
    (((mem_integralGL_iff F n).1 ((integralGL F n).mul_mem hk₂ ((integralGL F n).inv_mem hk))).1)
    hν hm (tailEmb hm) (tailEmb hm)
  rw [← Cartan.coe_diagPow, ← Units.val_mul, ← Units.val_mul, ← heq,
    det_submatrix_tailEmb hu] at hb
  exact le_of_bdd_zpow hb

theorem sum_iwasawaExponent {ν : Fin n → ℤ} {g : GL (Fin n) F}
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n ν)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    ∑ i, iwasawaExponent F n g i = ∑ i, ν i := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (Cartan.mem_doubleCoset_diagPow F n).1 hg
  obtain ⟨u, hu, k, hk, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F n
    (k₁ * Cartan.diagPow F n ν * k₂)
  set l := iwasawaExponent F n (k₁ * Cartan.diagPow F n ν * k₂)
  have hdet := congrArg (fun g : GL (Fin n) F => valuation F (g : Matrix (Fin n) (Fin n) F).det) he
  simp only [Units.val_mul, det_mul, map_mul, valuation_det_eq_one hk₁, valuation_det_eq_one hk₂,
    valuation_det_eq_one hk, one_mul, mul_one, coe_torusPow, Cartan.coe_diagPow, det_diagonal,
    prod_zpow_uniformizer, map_zpow₀] at hdet
  have hu1 : valuation F (u : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [det_of_isUpperTriangular (hu.1 : (u : Matrix (Fin n) (Fin n) F).BlockTriangular id)]
    simp [hu.2]
  rw [hu1, one_mul] at hdet
  have hp := valuation_uniformizer_pos (F := F)
  have h1 := valuation_uniformizer_lt_one F
  exact le_antisymm ((zpow_le_zpow_iff_right_of_lt_one₀ hp h1).1 hdet.le)
    ((zpow_le_zpow_iff_right_of_lt_one₀ hp h1).1 hdet.ge)

theorem tailSum_succ (l : Fin n → ℤ) {m : ℕ} (hm : m + 1 ≤ n) :
    tailSum l hm = l ⟨n - (m + 1), by omega⟩ + tailSum l (Nat.le_of_succ_le hm) := by
  rw [tailSum, Fin.sum_univ_succ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [tailEmb, Fin.val_succ, Fin.ext_iff]
  omega

theorem eq_of_tailSum_eq {l l' : Fin n → ℤ} (h : ∀ m (hm : m ≤ n), tailSum l hm = tailSum l' hm) :
    l = l' := by
  funext i
  have hm : n - 1 - i.val + 1 ≤ n := by omega
  have e1 := tailSum_succ l hm
  have e2 := tailSum_succ l' hm
  rw [h, h (n - 1 - i.val)] at e1
  have hi : (⟨n - (n - 1 - i.val + 1), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
  rw [hi] at e1 e2
  linarith

def ell (l : Fin n → ℤ) : ℤ := ∑ m : Fin (n + 1), tailSum l (Nat.lt_succ_iff.1 m.2)

theorem ell_le_iwasawaExponent {ν : Fin n → ℤ} (hν : Cartan.IsDominant ν) {g : GL (Fin n) F}
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n ν)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    ell ν ≤ ell (iwasawaExponent F n g) ∧
      (ell ν = ell (iwasawaExponent F n g) → iwasawaExponent F n g = ν) := by
  have hle : ∀ m ∈ (Finset.univ : Finset (Fin (n + 1))),
      tailSum ν (Nat.lt_succ_iff.1 m.2) ≤ tailSum (iwasawaExponent F n g) (Nat.lt_succ_iff.1 m.2) :=
    fun m _ => tailSum_le_iwasawaExponent hν hg _
  refine ⟨Finset.sum_le_sum hle, fun he => ?_⟩
  have := (Finset.sum_eq_sum_iff_of_le hle).1 he
  refine (eq_of_tailSum_eq fun m hm => ?_).symm
  exact this ⟨m, Nat.lt_succ_of_le hm⟩ (Finset.mem_univ _)

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem apply_eq_apply_cartanType (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (h : HeckeAlgebra μ) g = (h : HeckeAlgebra μ) (Cartan.diagPow F n (cartanType F n g)) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := (Cartan.mem_doubleCoset_diagPow F n).1 (cartanType_spec g).2
  conv_lhs => rw [hg]
  rw [(HeckeAlgebraLevel.val_mem _ _ h k₂ hk₂ _).2, HeckeAlgebraLevel.apply_mul_left _ _ h hk₁]

theorem apply_out (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (h : HeckeAlgebra μ) (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out =
      (h : HeckeAlgebra μ) g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) g
  rw [hk, (HeckeAlgebraLevel.val_mem _ _ h k k.2 g).2]

theorem iwasawaExponent_out (g : GL (Fin n) F) :
    iwasawaExponent F n (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out =
      iwasawaExponent F n g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) g
  rw [hk, iwasawaExponent_mul_of_mem_integralGL F n g k.2]

theorem satake_coeff (h : SphericalHecke μ (F := F) (n := n)) (l : Fin n → ℤ) :
    (satake μ h).coeff l = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
      ∑ x ∈ cosetSupport h,
        if iwasawaExponent F n x.out = l then (h : HeckeAlgebra μ) x.out else 0 := by
  classical
  rw [satake, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.finset_sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem satakeHom_injective : Function.Injective (satakeHom μ (F := F) (n := n)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro h h0
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, (h : HeckeAlgebra μ) g ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (HeckeAlgebraLevel.ext _ _ (HeckeAlgebra.ext fun x => by
      rw [hall x, HeckeAlgebraLevel.val_zero, HeckeAlgebra.coe_zero, Pi.zero_apply]))
  set D := (cosetSupport h).filter fun x => (h : HeckeAlgebra μ) x.out ≠ 0
  have hD : (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n) ∈ D := by
    have hv : (h : HeckeAlgebra μ) (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out ≠ 0 := by
      rw [apply_out]
      exact hg
    exact Finset.mem_filter.2 ⟨by by_contra hx; exact hv (apply_out_eq_zero hx), hv⟩
  obtain ⟨x₀, hx₀, hmin⟩ := D.exists_min_image (fun x => ell (cartanType F n x.out)) ⟨_, hD⟩
  set μ₀ := cartanType F n x₀.out
  set c := (h : HeckeAlgebra μ) (Cartan.diagPow F n μ₀)
  have hc : c ≠ 0 := by
    have := (Finset.mem_filter.1 hx₀).2
    rwa [apply_eq_apply_cartanType] at this
  have hclaim : ∀ x ∈ cosetSupport h,
      (if iwasawaExponent F n x.out = μ₀ then (h : HeckeAlgebra μ) x.out else 0) =
        if iwasawaExponent F n x.out = μ₀ ∧ (h : HeckeAlgebra μ) x.out ≠ 0 then c else 0 := by
    intro x hx
    by_cases hxz : (h : HeckeAlgebra μ) x.out = 0
    · simp [hxz]
    by_cases hi : iwasawaExponent F n x.out = μ₀
    · rw [if_pos hi, if_pos ⟨hi, hxz⟩]
      have h1 := hmin x (Finset.mem_filter.2 ⟨hx, hxz⟩)
      have h2 := ell_le_iwasawaExponent (cartanType_spec x.out).1 (cartanType_spec x.out).2
      rw [hi] at h2
      have heq : cartanType F n x.out = μ₀ := (h2.2 (le_antisymm h2.1 h1)).symm
      rw [apply_eq_apply_cartanType, heq]
    · rw [if_neg hi, if_neg fun h' => hi h'.1]
  have hcoeff := congrArg (fun p : LaurentRing n => p.coeff μ₀) h0
  simp only [satakeHom_apply, satake_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply] at hcoeff
  rw [Finset.sum_congr rfl hclaim, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hcoeff
  have hmem : (QuotientGroup.mk (Cartan.diagPow F n μ₀) : GL (Fin n) F ⧸ integralGL F n) ∈
      (cosetSupport h).filter (fun x => iwasawaExponent F n x.out = μ₀ ∧
        (h : HeckeAlgebra μ) x.out ≠ 0) := by
    have hv : (h : HeckeAlgebra μ)
        (QuotientGroup.mk (Cartan.diagPow F n μ₀) : GL (Fin n) F ⧸ integralGL F n).out ≠ 0 := by
      rw [apply_out]
      exact hc
    refine Finset.mem_filter.2 ⟨?_, ?_, hv⟩
    · by_contra hx
      exact hv (apply_out_eq_zero hx)
    · rw [iwasawaExponent_out, diagPow_eq_torusPow, iwasawaExponent_torusPow]
  have hcard := Finset.card_ne_zero.2 ⟨_, hmem⟩
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  rcases mul_eq_zero.1 hcoeff with h1 | h1
  · exact hK h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hcard (by exact_mod_cast h2)
    · exact hc h2

end Spherical

end GroundTheory.Automorphic
