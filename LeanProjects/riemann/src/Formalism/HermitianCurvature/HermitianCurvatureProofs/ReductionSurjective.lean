import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x2

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]

def IsUc (c : ι → ℕ) (x : Matrix ι ι A) : Prop :=
  ∀ i j, c j ≤ c i → x i j = (1 : Matrix ι ι A) i j

def IsLc (c : ι → ℕ) (x : Matrix ι ι A) : Prop := ∀ i j, c i ≠ c j → x i j = 0

variable {c : ι → ℕ} {x y : Matrix ι ι A}

theorem isUc_one : IsUc c (1 : Matrix ι ι A) := fun _ _ _ => rfl

theorem IsUc.mul (hx : IsUc c x) (hy : IsUc c y) : IsUc c (x * y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  have key : ∀ l ∈ Finset.univ, x i l * y l j = (1 : Matrix ι ι A) i l * y l j := by
    intro l _
    by_cases hl : c l ≤ c i
    · rw [hx i l hl]
    · have h1 : c j ≤ c l := by omega
      have hne : l ≠ j := by rintro rfl; omega
      rw [hy l j h1, Matrix.one_apply_ne hne, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl key, ← Matrix.mul_apply, Matrix.one_mul, hy i j hij]

theorem IsUc.blockTriangular (hx : IsUc c x) : BlockTriangular x c := by
  intro i j h
  have hne : i ≠ j := by rintro rfl; omega
  rw [hx i j h.le, Matrix.one_apply_ne hne]

theorem IsUc.det (hx : IsUc c x) : x.det = 1 := by
  rw [hx.blockTriangular.det]
  apply Finset.prod_eq_one
  intro a _
  have h1 : x.toSquareBlock c a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [Matrix.toSquareBlock_def, hx i j (by omega), Matrix.one_apply, Subtype.ext_iff]
  rw [h1, Matrix.det_one]

theorem IsUc.inv (hx : IsUc c x) : IsUc c x⁻¹ := by
  have hdet := hx.det
  let _ : Invertible x := Matrix.invertibleOfIsUnitDet x (by simp [hdet])
  have hT : BlockTriangular x⁻¹ c := Matrix.blockTriangular_inv_of_blockTriangular hx.blockTriangular
  intro i j hij
  have h1 : (x⁻¹ * x) i j = (1 : Matrix ι ι A) i j := by
    rw [Matrix.nonsing_inv_mul x (by simp [hdet])]
  rw [Matrix.mul_apply] at h1
  have key : ∀ l ∈ Finset.univ, x⁻¹ i l * x l j = x⁻¹ i l * (1 : Matrix ι ι A) l j := by
    intro l _
    by_cases hl : c j ≤ c l
    · rw [hx l j hl]
    · have h2 : c l < c i := by omega
      rw [hT h2, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl key, ← Matrix.mul_apply, Matrix.mul_one] at h1
  exact h1

theorem IsUc.conj {l l' n : Matrix ι ι A} (hl : IsLc c l) (hl' : IsLc c l') (h : l * l' = 1)
    (hn : IsUc c n) : IsUc c (l * n * l') := by
  intro i j hij
  have key : (l * (n - 1) * l') i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : c b = c j
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro a _
      by_cases ha : c i = c a
      · rw [Matrix.sub_apply, hn a b (by omega), sub_self, mul_zero]
      · rw [hl i a ha, zero_mul]
    · rw [hl' b j hb, mul_zero]
  have h2 : l * n * l' = l * (n - 1) * l' + 1 := by
    rw [mul_sub, sub_mul, mul_one, h]; abel
  rw [h2, Matrix.add_apply, key, zero_add]

theorem IsUc.map {B : Type} [CommRing B] (f : A →+* B) (hx : IsUc c x) : IsUc c (x.map f) := by
  intro i j hij
  rw [Matrix.map_apply, hx i j hij]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

variable (A) (c) in

def UcG : Subgroup (GL ι A) where
  carrier := {g | IsUc c (g : Matrix ι ι A)}
  one_mem' := by simpa using isUc_one
  mul_mem' := by intro a b ha hb; simpa using IsUc.mul ha hb
  inv_mem' := by intro a ha; simpa [Matrix.coe_units_inv] using IsUc.inv ha

noncomputable def toGL (x : Matrix ι ι A) (h : IsUnit x.det) : GL ι A := Matrix.nonsingInvUnit x h

@[simp] theorem coe_toGL (x : Matrix ι ι A) (h : IsUnit x.det) : (toGL x h : Matrix ι ι A) = x := rfl

theorem card_of_subgroupSet (P : Matrix ι ι A → Prop) (B : Subgroup (GL ι A))
    (h : ∀ x, P x ↔ ∃ g ∈ B, (g : Matrix ι ι A) = x) : Nat.card {x // P x} = Nat.card B := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun g : B => ⟨((g : GL ι A) : Matrix ι ι A), (h _).2 ⟨g, g.2, rfl⟩⟩) ⟨?_, ?_⟩
  · intro a b hab
    have h1 : ((a : GL ι A) : Matrix ι ι A) = ((b : GL ι A) : Matrix ι ι A) := congrArg Subtype.val hab
    exact Subtype.ext (Units.ext h1)
  · rintro ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := (h x).1 hx
    exact ⟨⟨g, hg⟩, rfl⟩

end Generic

section Prod

variable {G : Type} [Group G]

def prodG (N H : Subgroup G) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : Subgroup G where
  carrier := {g | ∃ n ∈ N, ∃ h ∈ H, g = n * h}
  one_mem' := ⟨1, N.one_mem, 1, H.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, h, hh, rfl⟩ ⟨n', hn', h', hh', rfl⟩
    exact ⟨n * (h * n' * h⁻¹), N.mul_mem hn (hnorm h hh n' hn'), h * h', H.mul_mem hh hh', by group⟩
  inv_mem' := by
    rintro _ ⟨n, hn, h, hh, rfl⟩
    exact ⟨h⁻¹ * n⁻¹ * (h⁻¹)⁻¹, hnorm _ (H.inv_mem hh) _ (N.inv_mem hn), h⁻¹, H.inv_mem hh, by group⟩

theorem card_prodG (N H : Subgroup G) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hd : Disjoint N H) : Nat.card (prodG N H hnorm) = Nat.card N * Nat.card H := by
  rw [← Nat.card_prod]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun p : N × H => ⟨(p.1 : G) * (p.2 : G), p.1, p.1.2, p.2, p.2.2, rfl⟩) ⟨?_, ?_⟩
  · intro a b hab
    exact Subgroup.mul_injective_of_disjoint hd (congrArg Subtype.val hab)
  · rintro ⟨_, n, hn, h, hh, rfl⟩
    exact ⟨(⟨n, hn⟩, ⟨h, hh⟩), rfl⟩

end Prod

section Specific

variable {A : Type} [CommRing A] {r k : ℕ}

def cI (r k : ℕ) : Idx r k → ℕ
  | Sum.inl a => a
  | Sum.inr (Sum.inl _) => r
  | Sum.inr (Sum.inr a) => r + 1 + a

theorem isN_iff (x : Matrix (Idx r k) (Idx r k) A) : IsN x ↔ IsUc (cI r k) x := by
  constructor
  · rintro ⟨h11, h33, h22, h21, h31, h32⟩
    rintro (a | a | a) (b | b | b) hij
    · simp only [cI] at hij
      rcases hij.lt_or_eq with h | h
      · have h1 : b11 x a b = 0 := h11.1 (by simpa using h)
        have hne : a ≠ b := by rintro rfl; omega
        simpa [b11, Matrix.one_apply, hne] using h1
      · have hab : a = b := Fin.ext h.symm
        subst hab
        simpa [b11] using h11.2 a
    · simp only [cI] at hij; have := a.2; omega
    · simp only [cI] at hij; have := a.2; omega
    · simpa [b21] using congrFun (congrFun h21 a) b
    · simpa [b22, Matrix.one_apply] using congrFun (congrFun h22 a) b
    · simp only [cI] at hij; omega
    · simpa [b31] using congrFun (congrFun h31 a) b
    · simpa [b32] using congrFun (congrFun h32 a) b
    · simp only [cI] at hij
      have hij' : (b : ℕ) ≤ a := by omega
      rcases hij'.lt_or_eq with h | h
      · have h1 : b33 x a b = 0 := h33.1 (by simpa using h)
        have hne : a ≠ b := by rintro rfl; omega
        simpa [b33, Matrix.one_apply, hne] using h1
      · have hab : a = b := Fin.ext h.symm
        subst hab
        simpa [b33] using h33.2 a
  · intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : b < a := hab
      have hne : a ≠ b := hab'.ne'
      have := h (Sum.inl a) (Sum.inl b) (by simp only [cI]; exact hab'.le)
      simpa [b11, Matrix.one_apply, hne] using this
    · intro a
      simpa [b11] using h (Sum.inl a) (Sum.inl a) le_rfl
    · intro a b hab
      have hab' : b < a := hab
      have hne : a ≠ b := hab'.ne'
      have := h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) (by simp only [cI]; have : (b : ℕ) < a := hab'; omega)
      simpa [b33, Matrix.one_apply, hne] using this
    · intro a
      simpa [b33] using h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr a)) le_rfl
    · ext a b
      simpa [b22, Matrix.one_apply] using h (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) le_rfl
    · ext a b
      simpa [b21] using h (Sum.inr (Sum.inl a)) (Sum.inl b) (by simp only [cI]; exact b.2.le)
    · ext a b
      simpa [b31] using h (Sum.inr (Sum.inr a)) (Sum.inl b) (by simp only [cI]; have := b.2; omega)
    · ext a b
      simpa [b32] using h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) (by simp only [cI]; omega)

theorem hEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : hEmb r (h * h') = hEmb r h * hEmb r h' := by
  simp [hEmb, midEmb, Matrix.fromBlocks_multiply]

theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb]

theorem hEmb_apply (h : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    hEmb r h (Sum.inr (Sum.inl (Sum.inl a))) (Sum.inr (Sum.inl (Sum.inl b))) = h a b := rfl

theorem hEmb_map {B : Type} [CommRing B] (f : A →+* B) (h : Matrix (Fin k) (Fin k) A) :
    (hEmb r h).map f = hEmb r (h.map f) := by
  simp [hEmb, midEmb, Matrix.fromBlocks_map]

theorem isLc_hEmb (h : Matrix (Fin k) (Fin k) A) : IsLc (cI r k) (hEmb r h) := by
  rintro (a | a | a) (b | b | b) hij
  · have hne : a ≠ b := by rintro rfl; exact hij rfl
    simp [hEmb, hne]
  · simp [hEmb]
  · simp [hEmb]
  · simp [hEmb]
  · exact absurd rfl hij
  · simp [hEmb]
  · simp [hEmb]
  · simp [hEmb]
  · have hne : a ≠ b := by rintro rfl; exact hij rfl
    simp [hEmb, hne]

variable (A r k) in

def hEmbHom : Matrix (Fin k) (Fin k) A →* Matrix (Idx r k) (Idx r k) A where
  toFun := hEmb r
  map_one' := hEmb_one
  map_mul' := hEmb_mul

variable (A r k) in

def phi : GL (Fin k) A →* GL (Idx r k) A := Units.map (hEmbHom A r k)

@[simp] theorem coe_phi (h : GL (Fin k) A) :
    (phi A r k h : Matrix (Idx r k) (Idx r k) A) = hEmb r (h : Matrix (Fin k) (Fin k) A) := rfl

theorem phi_injective : Function.Injective (phi A r k) := by
  intro a b hab
  apply Units.ext
  ext i j
  have h1 : hEmb r (a : Matrix (Fin k) (Fin k) A) = hEmb r (b : Matrix (Fin k) (Fin k) A) := by
    rw [← coe_phi, ← coe_phi, hab]
  rw [← hEmb_apply (r := r) (a : Matrix (Fin k) (Fin k) A), h1, hEmb_apply]

theorem norm_phi (V : Subgroup (GL (Fin k) A)) :
    ∀ h ∈ V.map (phi A r k), ∀ n ∈ UcG A (cI r k), h * n * h⁻¹ ∈ UcG A (cI r k) := by
  rintro _ ⟨h, -, rfl⟩ n hn
  rw [← map_inv]
  change IsUc (cI r k) (hEmb r (h : Matrix (Fin k) (Fin k) A) * (n : Matrix _ _ A) *
    hEmb r ((h⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A))
  refine IsUc.conj (isLc_hEmb _) (isLc_hEmb _) ?_ hn
  rw [← hEmb_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, hEmb_one]

theorem disj_phi (V : Subgroup (GL (Fin k) A)) : Disjoint (UcG A (cI r k)) (V.map (phi A r k)) := by
  rw [Subgroup.disjoint_def]
  rintro _ hx ⟨h, -, rfl⟩
  have h1 : h = 1 := by
    apply Units.ext
    ext a b
    have := hx (Sum.inr (Sum.inl (Sum.inl a))) (Sum.inr (Sum.inl (Sum.inl b))) le_rfl
    rw [coe_phi, hEmb_apply] at this
    simpa [Matrix.one_apply] using this
  rw [h1, map_one]

variable (r) in

def PG (V : Subgroup (GL (Fin k) A)) : Subgroup (GL (Idx r k) A) :=
  prodG (UcG A (cI r k)) (V.map (phi A r k)) (norm_phi V)

theorem card_PG (V : Subgroup (GL (Fin k) A)) :
    Nat.card (PG r V) = Nat.card (UcG A (cI r k)) * Nat.card V := by
  rw [PG, card_prodG _ _ _ (disj_phi V), Subgroup.card_map_of_injective phi_injective]

theorem mem_PG (V : Subgroup (GL (Fin k) A)) (g : GL (Idx r k) A) :
    g ∈ PG r V ↔ ∃ n : GL (Idx r k) A, ∃ h ∈ V, IsN (n : Matrix (Idx r k) (Idx r k) A) ∧
      g = n * phi A r k h := by
  constructor
  · rintro ⟨n, hn, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨n, h, hh, (isN_iff _).2 hn, rfl⟩
  · rintro ⟨n, h, hh, hn, rfl⟩
    exact ⟨n, (isN_iff _).1 hn, _, ⟨h, hh, rfl⟩, rfl⟩

theorem isN_isUnit_det {x : Matrix (Idx r k) (Idx r k) A} (hx : IsN x) : IsUnit x.det := by
  rw [((isN_iff x).1 hx).det]; exact isUnit_one

theorem isN_set (x : Matrix (Idx r k) (Idx r k) A) :
    IsN x ↔ ∃ g ∈ UcG A (cI r k), (g : Matrix (Idx r k) (Idx r k) A) = x := by
  constructor
  · intro hx
    exact ⟨toGL x (isN_isUnit_det hx), (isN_iff x).1 hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact (isN_iff _).2 hg

theorem isS_set (x : Matrix (Idx r k) (Idx r k) A) :
    IsS x ↔ ∃ g ∈ PG r (⊤ : Subgroup (GL (Fin k) A)), (g : Matrix (Idx r k) (Idx r k) A) = x := by
  constructor
  · rintro ⟨n, _, hn, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨toGL n (isN_isUnit_det hn) * phi A r k (toGL h hh),
      (mem_PG _ _).2 ⟨_, _, Subgroup.mem_top _, hn, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, h, -, hn, rfl⟩ := (mem_PG _ _).1 hg
    exact ⟨n, _, hn, ⟨h, (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit, rfl⟩, rfl⟩

theorem isNU_set (x : Matrix (Idx r k) (Idx r k) A) :
    IsNU x ↔ ∃ g ∈ PG r (upUniG A k), (g : Matrix (Idx r k) (Idx r k) A) = x := by
  constructor
  · rintro ⟨n, _, hn, ⟨u, hu, rfl⟩, rfl⟩
    have hd : IsUnit u.det := by rw [isUpUni_det A hu]; exact isUnit_one
    exact ⟨toGL n (isN_isUnit_det hn) * phi A r k (toGL u hd),
      (mem_PG _ _).2 ⟨_, toGL u hd, hu, hn, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, h, hh, hn, rfl⟩ := (mem_PG _ _).1 hg
    exact ⟨n, _, hn, ⟨h, hh, rfl⟩, rfl⟩

theorem isS_iff (g : GL (Idx r k) A) :
    IsS (g : Matrix (Idx r k) (Idx r k) A) ↔ g ∈ PG r (⊤ : Subgroup (GL (Fin k) A)) := by
  rw [isS_set]
  constructor
  · rintro ⟨g', hg', e⟩; rwa [← Units.ext e]
  · intro hg; exact ⟨g, hg, rfl⟩

theorem isNU_iff (g : GL (Idx r k) A) :
    IsNU (g : Matrix (Idx r k) (Idx r k) A) ↔ g ∈ PG r (upUniG A k) := by
  rw [isNU_set]
  constructor
  · rintro ⟨g', hg', e⟩; rwa [← Units.ext e]
  · intro hg; exact ⟨g, hg, rfl⟩

theorem PG_mono {V W : Subgroup (GL (Fin k) A)} (h : V ≤ W) : PG r V ≤ PG r W := by
  intro g hg
  obtain ⟨n, u, hu, hn, rfl⟩ := (mem_PG _ _).1 hg
  exact (mem_PG _ _).2 ⟨n, u, h hu, hn, rfl⟩

theorem card_N : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} = Nat.card (UcG A (cI r k)) :=
  card_of_subgroupSet _ _ isN_set

theorem card_S : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (PG r (⊤ : Subgroup (GL (Fin k) A))) :=
  card_of_subgroupSet _ _ isS_set

end Specific

section Local

variable (o : Type) [CommRing o] [IsLocalRing o]

local notation "𝔽" => IsLocalRing.ResidueField o

theorem coe_red (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι o) :
    (red o ι g : Matrix ι ι 𝔽) = (g : Matrix ι ι o).map (IsLocalRing.residue o) := rfl

theorem red_surjective (ι : Type) [Fintype ι] [DecidableEq ι] : Function.Surjective (red o ι) := by
  intro g
  let y : Matrix ι ι o := Matrix.of fun i j =>
    Function.surjInv IsLocalRing.residue_surjective ((g : Matrix ι ι 𝔽) i j)
  have hy : y.map (IsLocalRing.residue o) = (g : Matrix ι ι 𝔽) := by
    ext i j
    simp [y, Function.surjInv_eq]
  have hdet : IsUnit y.det := by
    have h1 : IsLocalRing.residue o y.det = (g : Matrix ι ι 𝔽).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hy]
    have h2 : IsUnit (IsLocalRing.residue o y.det) := by
      rw [h1]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact isUnit_of_map_unit (IsLocalRing.residue o) _ h2
  exact ⟨toGL y hdet, Units.ext hy⟩

variable {o} {r k : ℕ}

theorem red_phi (h : GL (Fin k) o) :
    red o (Idx r k) (phi o r k h) = phi 𝔽 r k (red o (Fin k) h) := by
  apply Units.ext
  rw [coe_red, coe_phi, coe_phi, coe_red, hEmb_map]

theorem lift_decomp (x : GL (Idx r k) o) (nb : GL (Idx r k) 𝔽) (hb : GL (Fin k) 𝔽)
    (hn : IsN (nb : Matrix (Idx r k) (Idx r k) 𝔽)) (hx : red o (Idx r k) x = nb * phi 𝔽 r k hb) :
    ∃ (n κ : GL (Idx r k) o) (h : GL (Fin k) o), IsN (n : Matrix (Idx r k) (Idx r k) o) ∧
      red o (Fin k) h = hb ∧ κ ∈ (red o (Idx r k)).ker ∧ x = n * phi o r k h * κ := by
  obtain ⟨h, rfl⟩ := red_surjective o (Fin k) hb
  let n0 : Matrix (Idx r k) (Idx r k) o := Matrix.of fun i j =>
    if cI r k j ≤ cI r k i then (1 : Matrix (Idx r k) (Idx r k) o) i j
    else Function.surjInv IsLocalRing.residue_surjective ((nb : Matrix (Idx r k) (Idx r k) 𝔽) i j)
  have hU : IsUc (cI r k) n0 := by
    intro i j hij
    simp [n0, hij]
  have hN : IsN n0 := (isN_iff _).2 hU
  have hmap : n0.map (IsLocalRing.residue o) = (nb : Matrix (Idx r k) (Idx r k) 𝔽) := by
    ext i j
    by_cases hij : cI r k j ≤ cI r k i
    · rw [(hU.map (IsLocalRing.residue o)) i j hij, (isN_iff _).1 hn i j hij]
    · simp [n0, hij, Function.surjInv_eq]
  let n : GL (Idx r k) o := toGL n0 (isN_isUnit_det hN)
  have hred : red o (Idx r k) n = nb := Units.ext hmap
  refine ⟨n, (n * phi o r k h)⁻¹ * x, h, hN, rfl, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hred, red_phi, hx]
  group

theorem isN_red {n : GL (Idx r k) o} (hn : IsN (n : Matrix (Idx r k) (Idx r k) o)) :
    IsN (red o (Idx r k) n : Matrix (Idx r k) (Idx r k) 𝔽) :=
  (isN_iff _).2 (((isN_iff _).1 hn).map _)

theorem Kpp_eq (L : Levels o r k) : L.Kpp = (PG r (upUniG 𝔽 k)).comap (red o (Idx r k)) := by
  ext x
  rw [L.mem_Kpp, Subgroup.mem_comap, isNU_iff]

theorem Knat_eq (L : Levels o r k) :
    L.Knat = (PG r (⊤ : Subgroup (GL (Fin k) 𝔽))).comap (red o (Idx r k)) := by
  ext x
  rw [L.mem_Knat, Subgroup.mem_comap, isS_iff]

theorem JH_eq (L : Levels o r k) : L.JH = (upUniG 𝔽 k).comap (red o (Fin k)) := by
  ext x
  rw [L.mem_JH, Subgroup.mem_comap]
  rfl

end Local

end Formalism.FourierDecayAlt.P.S3x2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2

theorem levels_exist' : Formalism.FourierDecayAlt.S3.LevelsExist := by
  intro o _ _ r k
  exact ⟨⟨(PG r (upUniG _ k)).comap (red o (Idx r k)), (PG r ⊤).comap (red o (Idx r k)),
    (upUniG _ k).comap (red o (Fin k)),
    fun x => by rw [Subgroup.mem_comap, isNU_iff], fun x => by rw [Subgroup.mem_comap, isS_iff],
    fun x => Iff.rfl⟩⟩

theorem reductionOnto_statement : Formalism.FourierDecayAlt.S3.ReductionOnto := by
  intro o _ _ ι _ _
  exact red_surjective o ι

theorem corner_level_index : Formalism.FourierDecayAlt.S3.IndexKpp := by
  intro o _ _ _ r k L
  rw [Kpp_eq L, Subgroup.index_comap_of_surjective _ (red_surjective o _), card_N, ← card_PG,
    Subgroup.index_mul_card]

theorem jordan_holder_index : Formalism.FourierDecayAlt.S3.IndexJH := by
  intro o _ _ _ r k L
  rw [JH_eq L, Subgroup.index_comap_of_surjective _ (red_surjective o _), Subgroup.index_mul_card]

theorem natural_level_index : Formalism.FourierDecayAlt.S3.IndexKnat := by
  intro o _ _ _ r k L
  refine ⟨?_, ?_, ?_⟩
  · rw [Knat_eq L, Subgroup.index_comap_of_surjective _ (red_surjective o _), card_S,
      Subgroup.index_mul_card]
  · rw [Kpp_eq L, Knat_eq L]
    exact Subgroup.comap_mono (PG_mono le_top)
  · rw [Kpp_eq L, Knat_eq L, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (red_surjective o _)]
    have h1 := Subgroup.relIndex_mul_relIndex ⊥ (PG r (upUniG (IsLocalRing.ResidueField o) k))
      (PG r ⊤) bot_le (PG_mono le_top)
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, card_PG, card_PG,
      Subgroup.card_top] at h1
    have hpos : 0 < Nat.card (UcG (IsLocalRing.ResidueField o) (cI r k)) := Nat.card_pos
    have h2 : Nat.card (UcG (IsLocalRing.ResidueField o) (cI r k)) *
        ((PG r (upUniG (IsLocalRing.ResidueField o) k)).relIndex (PG r ⊤) *
          Nat.card (upUniG (IsLocalRing.ResidueField o) k)) =
        Nat.card (UcG (IsLocalRing.ResidueField o) (cI r k)) *
          Nat.card (GL (Fin k) (IsLocalRing.ResidueField o)) := by
      rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem natural_level_product : Formalism.FourierDecayAlt.S3.KnatProduct := by
  intro o _ _ r k L x
  rw [L.mem_Knat, isS_iff]
  constructor
  · intro hx
    obtain ⟨nb, hb, -, hn, hx⟩ := (mem_PG _ _).1 hx
    obtain ⟨n, κ, h, hN, -, hκ, rfl⟩ := lift_decomp x nb hb hn hx
    exact ⟨n * phi o r k h, κ, (isS_iff _).2 ((mem_PG _ _).2 ⟨n, h, Subgroup.mem_top _, hN, rfl⟩),
      hκ, rfl⟩
  · rintro ⟨s, κ, hs, hκ, rfl⟩
    obtain ⟨n, h, -, hN, rfl⟩ := (mem_PG _ _).1 ((isS_iff _).1 hs)
    rw [map_mul, MonoidHom.mem_ker.1 hκ, mul_one, map_mul, red_phi]
    exact (mem_PG _ _).2 ⟨_, _, Subgroup.mem_top _, isN_red hN, rfl⟩

theorem corner_level_product : Formalism.FourierDecayAlt.S3.KppProduct := by
  intro o _ _ r k L x
  rw [L.mem_Kpp, isNU_iff]
  constructor
  · intro hx
    obtain ⟨nb, hb, hbU, hn, hx⟩ := (mem_PG _ _).1 hx
    obtain ⟨n, κ, h, hN, rfl, hκ, rfl⟩ := lift_decomp x nb hb hn hx
    exact ⟨n, κ, h, hN, (L.mem_JH h).2 hbU, hκ, rfl⟩
  · rintro ⟨n, κ, h, hN, hh, hκ, hx⟩
    have hx' : x = n * phi o r k h * κ := Units.ext hx
    rw [hx', map_mul, MonoidHom.mem_ker.1 hκ, mul_one, map_mul, red_phi]
    exact (mem_PG _ _).2 ⟨_, _, (L.mem_JH h).1 hh, isN_red hN, rfl⟩

end Formalism.FourierDecayAlt.P
