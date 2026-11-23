import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Formalism.BasicNotions Matrix

section Abs

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def geoGram (v : ι → S.V) : Matrix ι ι E := fun i k => S.hT (v i) (v k)

def geoC (v : ι → S.V) (i : ι) : S.V →ₗ[E] E := ∑ k, ((geoGram v)⁻¹ i k) • S.hT (v k)

def geoY (v w : ι → S.V) : S.V →ₗ[E] S.V := ∑ i, (geoC v i).smulRight (w i)

theorem geo_C_apply (v : ι → S.V) (i : ι) (y : S.V) :
    geoC v i y = ∑ k, (geoGram v)⁻¹ i k * S.hT (v k) y := by
  unfold geoC
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]

theorem geo_Y_apply (v w : ι → S.V) (y : S.V) : geoY v w y = ∑ i, geoC v i y • w i := by
  unfold geoY
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smulRight_apply]

theorem geo_repr (v : ι → S.V) (h : IsUnit (geoGram v).det) (l : ι) (y : S.V) :
    S.hT (v l) y = ∑ k, geoGram v l k * geoC v k y := by
  have hmul : geoGram v * (geoGram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have hrow : ∀ m, ∑ k, geoGram v l k * (geoGram v)⁻¹ k m = if l = m then 1 else 0 := by
    intro m
    have hm := congrFun (congrFun hmul l) m
    rw [Matrix.mul_apply, Matrix.one_apply] at hm
    exact hm
  simp_rw [geo_C_apply, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hrow]
  simp

theorem geo_C_v (v : ι → S.V) (h : IsUnit (geoGram v).det) (i l : ι) :
    geoC v i (v l) = if i = l then 1 else 0 := by
  rw [geo_C_apply]
  have h1 : (geoGram v)⁻¹ * geoGram v = 1 := Matrix.nonsing_inv_mul _ h
  have h2 := congrFun (congrFun h1 i) l
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  exact h2

theorem geo_Y_v (v w : ι → S.V) (h : IsUnit (geoGram v).det) (l : ι) : geoY v w (v l) = w l := by
  rw [geo_Y_apply]
  simp only [geo_C_v v h]
  simp

theorem geo_R (v : ι → S.V) (h : IsUnit (geoGram v).det) (z : S.V)
    (hz : z ∈ Submodule.span E (Set.range v)) (y : S.V) :
    S.hT z y = ∑ k, S.hT z (v k) * geoC v k y := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hz
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [geo_repr v h i y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [geoGram, mul_assoc]

theorem geo_skew (v w : ι → S.V) (h : IsUnit (geoGram v).det)
    (hw : ∀ i, w i ∈ Submodule.span E (Set.range v))
    (hsk : ∀ i k, S.hT (w i) (v k) + S.hT (v i) (w k) = 0) (x y : S.V) :
    S.hT (geoY v w x) y + S.hT x (geoY v w y) = 0 := by
  have e1 : S.hT (geoY v w x) y = ∑ i, ∑ k, star (geoC v i x) * (S.hT (w i) (v k) * geoC v k y) := by
    rw [geo_Y_apply]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [geo_R v h (w i) (hw i) y, Finset.mul_sum]
  have e2 : S.hT x (geoY v w y) = ∑ i, ∑ k, star (geoC v i x) * (S.hT (v i) (w k) * geoC v k y) := by
    rw [geo_Y_apply]
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hx : S.hT x (w k) = ∑ i, S.hT (v i) (w k) * star (geoC v i x) := by
      rw [← S.herm.eq (w k) x, geo_R v h (w k) (hw k) x, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, S.herm.eq, starRingEnd_apply]
    rw [hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  linear_combination (star (geoC v i x) * geoC v k y) * hsk i k

end Abs

section Flag

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem geo_fvec_cast (F : FlagG S r T) (a : Fin r) : F.fvec a.castSucc = F.e a := by
  simp [FlagG.fvec]

theorem geo_fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem geo_e_mem_Xa (F : FlagG S r T) (i : Fin r) (a : ℕ) (h : i.val < a) : F.e i ∈ F.Xa a := by
  unfold FlagG.Xa
  exact Submodule.subset_span ⟨i, h, rfl⟩

theorem geo_Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  unfold FlagG.Xa
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem geo_Xa_le_X (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

theorem geo_X_fvec (F : FlagG S r T) (x : S.V) (hx : x ∈ F.X) (p : Fin (r + 1)) : S.hT x (F.fvec p) = 0 := by
  have key : ∀ i, S.hT (F.e i) (F.fvec p) = 0 := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last p with ⟨a, rfl⟩ | rfl
    · rw [geo_fvec_cast]
      exact F.e_iso i a
    · rw [geo_fvec_last]
      exact F.z_orth i
  unfold FlagG.X at hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hx
  simp [key]

theorem geo_fvec_X (F : FlagG S r T) (x : S.V) (hx : x ∈ F.X) (p : Fin (r + 1)) : S.hT (F.fvec p) x = 0 := by
  rw [← S.herm.eq x (F.fvec p), geo_X_fvec F x hx p, map_zero]

theorem geo_X_X (F : FlagG S r T) (x y : S.V) (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have key : ∀ i, S.hT x (F.e i) = 0 := fun i => by
    rw [← geo_fvec_cast F i]
    exact geo_X_fvec F x hx _
  unfold FlagG.X at hy
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hy
  simp [key]

theorem geo_fvec_perp (F : FlagG S r T) (p : Fin (r + 1)) : F.fvec p ∈ perpS S F.X := by
  show ∀ x ∈ F.X, S.hT x (F.fvec p) = 0
  exact fun x hx => geo_X_fvec F x hx p

theorem geo_coefX (F : FlagG S r T) (a : Fin r) (c : E) (y : S.V) (hy : y ∈ F.Xa a.val) :
    F.coefX (c • F.e a + y) a = c := by
  classical
  unfold FlagG.Xa at hy
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := E)).1 hy
  have hmem : c • F.e a + Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e) := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)) ?_
    exact Submodule.span_mono (Set.image_subset_range _ _)
      ((Finsupp.mem_span_image_iff_linearCombination (R := E)).2 ⟨l, hl, rfl⟩)
  have hla : l a = 0 := by
    by_contra hne
    rw [Finsupp.mem_supported] at hl
    have := hl (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
    simp at this
  have heq : F.e_indep.repr ⟨_, hmem⟩ = Finsupp.single a c + l := by
    apply F.e_indep.repr_eq
    simp [Finsupp.linearCombination_single]
  unfold FlagG.coefX
  rw [dif_pos hmem, heq]
  simp [hla]

variable {j : ℕ} (hj : j ≤ r + 1)

theorem geo_castLE_eq (b : Fin j) (hb : b.val < r) : Fin.castLE hj b = Fin.castSucc ⟨b.val, hb⟩ := by
  exact Fin.ext rfl

theorem geo_W_mem (F : FlagG S r T) (A : Matrix (Fin j) (Fin j) E) (hA : StrictUp A) (a : Fin j) :
    ∑ b, A b a • F.fvec (Fin.castLE hj b) ∈ F.Xa a.val := by
  refine sum_mem fun b _ => ?_
  by_cases hba : a ≤ b
  · rw [hA b a hba, zero_smul]
    exact Submodule.zero_mem _
  · have hba' : b.val < a.val := Fin.lt_def.1 (not_le.1 hba)
    have hbr : b.val < r := by have := a.isLt; omega
    rw [geo_castLE_eq hj b hbr, geo_fvec_cast]
    exact Submodule.smul_mem _ _ (geo_e_mem_Xa F ⟨b.val, hbr⟩ a.val hba')

theorem geo_W_split (F : FlagG S r T) (A : Matrix (Fin j) (Fin j) E) (hA : StrictUp A) (a : Fin j) (i : Fin r)
    (hi : a.val = i.val + 1) :
    ∃ y ∈ F.Xa i.val, ∑ b, A b a • F.fvec (Fin.castLE hj b) =
      A ⟨i.val, by have := a.isLt; omega⟩ a • F.e i + y := by
  have hi0 : i.val < j := by have := a.isLt; omega
  refine ⟨∑ b ∈ Finset.univ.erase (⟨i.val, hi0⟩ : Fin j), A b a • F.fvec (Fin.castLE hj b), ?_, ?_⟩
  · refine sum_mem fun b hb => ?_
    have hne : b ≠ ⟨i.val, hi0⟩ := Finset.ne_of_mem_erase hb
    by_cases hba : a ≤ b
    · rw [hA b a hba, zero_smul]
      exact Submodule.zero_mem _
    · have hba' : b.val < a.val := Fin.lt_def.1 (not_le.1 hba)
      have hbv : b.val ≠ i.val := fun h => hne (Fin.ext h)
      have hbi : b.val < i.val := by omega
      have hbr : b.val < r := by have := i.isLt; omega
      rw [geo_castLE_eq hj b hbr, geo_fvec_cast]
      exact Submodule.smul_mem _ _ (geo_e_mem_Xa F ⟨b.val, hbr⟩ i.val hbi)
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i.val, hi0⟩ : Fin j)),
      geo_castLE_eq hj ⟨i.val, hi0⟩ i.isLt, geo_fvec_cast]

theorem geo_sum_range (hj' : j ≤ r + 1) (g : ℕ → E) (hg : ∀ i, j ≤ i + 1 → g i = 0) :
    ∑ i ∈ Finset.range r, g i = ∑ i ∈ Finset.range j, g i := by
  rcases Nat.lt_or_ge r j with h | h
  · have hj1 : j = r + 1 := by omega
    subst hj1
    rw [Finset.sum_range_succ, hg r le_rfl, add_zero]
  · rw [← Finset.sum_range_add_sum_Ico _ h]
    rw [Finset.sum_eq_zero (s := Finset.Ico j r) (fun i hi => hg i (by rw [Finset.mem_Ico] at hi; omega)),
      add_zero]

theorem geo_side (F : FlagG S r T) (A : Matrix (Fin j) (Fin j) E) (hA : StrictUp A) (Y : S.V →ₗ[E] S.V)
    (H1 : Y ∈ LieU S)
    (H2 : ∀ a : Fin j, Y (F.fvec (Fin.castLE hj a)) = ∑ b, A b a • F.fvec (Fin.castLE hj b))
    (H3 : ∀ x ∈ perpS S F.X, Y x ∈ F.X ∧ (j ≤ r → Y x ∈ F.Xa (j - 1))) :
    Y ∈ F.LieN ∧ F.ell Y = supSum A := by
  constructor
  · show Y ∈ LieU S ∧ (∀ a : ℕ, 1 ≤ a → a ≤ r → ∀ x ∈ F.Xa a, Y x ∈ F.Xa (a - 1)) ∧
      ∀ x ∈ perpS S F.X, Y x ∈ F.X
    refine ⟨H1, ?_, fun x hx => (H3 x hx).1⟩
    intro a ha1 har x hx
    have hsub : F.Xa a ≤ (F.Xa (a - 1)).comap Y := by
      show Submodule.span E (F.e '' {i | i.1 < a}) ≤ _
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i.val < a := hi
      show Y (F.e i) ∈ F.Xa (a - 1)
      by_cases hij : i.val < j
      · have he : F.e i = F.fvec (Fin.castLE hj ⟨i.val, hij⟩) := by
          rw [geo_castLE_eq hj ⟨i.val, hij⟩ i.isLt, geo_fvec_cast]
        have hle : i.val ≤ a - 1 := by omega
        rw [he, H2]
        exact geo_Xa_mono F hle (geo_W_mem hj F A hA ⟨i.val, hij⟩)
      · have hperp : F.e i ∈ perpS S F.X := by
          rw [← geo_fvec_cast F i]
          exact geo_fvec_perp F _
        have hjr : j ≤ r := by have := i.isLt; omega
        have hle : j - 1 ≤ a - 1 := by omega
        exact geo_Xa_mono F hle ((H3 _ hperp).2 hjr)
    exact hsub hx
  · let G : ℕ → E := fun n => if h : n + 1 < j then A ⟨n, by omega⟩ ⟨n + 1, h⟩ else 0
    have hg : ∀ i : Fin r, F.coefX (Y (F.fvec i.succ)) i = G i.val := by
      intro i
      by_cases h : i.val + 1 < j
      · simp only [G, dif_pos h]
        obtain ⟨y, hy, hyeq⟩ := geo_W_split hj F A hA ⟨i.val + 1, h⟩ i rfl
        have hsucc : F.fvec i.succ = F.fvec (Fin.castLE hj ⟨i.val + 1, h⟩) := rfl
        rw [hsucc, H2, hyeq]
        exact geo_coefX F i _ y hy
      · simp only [G, dif_neg h]
        have hjr : j ≤ r := by have := i.isLt; omega
        have hle : j - 1 ≤ i.val := by omega
        have hmem : Y (F.fvec i.succ) ∈ F.Xa i.val :=
          geo_Xa_mono F hle ((H3 _ (geo_fvec_perp F _)).2 hjr)
        have := geo_coefX F i 0 _ hmem
        rwa [zero_smul, zero_add] at this
    have e1 : F.ell Y = ∑ n ∈ Finset.range r, G n := by
      unfold FlagG.ell
      rw [← Fin.sum_univ_eq_sum_range G r]
      exact Finset.sum_congr rfl fun i _ => hg i
    have e2 : supSum A = ∑ n ∈ Finset.range j, G n := by
      rw [← Fin.sum_univ_eq_sum_range G j]
      rfl
    rw [e1, e2]
    exact geo_sum_range hj G fun n hn => by
      simp only [G]
      rw [dif_neg (show ¬ (n + 1 < j) by omega)]

end Flag

section Pair

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E} {j : ℕ}

def geoImg (F : FlagG S r T) (hj : j ≤ r + 1) (A : Matrix (Fin j) (Fin j) E) (a : Fin j) : S.V :=
  ∑ b, A b a • F.fvec (Fin.castLE hj b)

def geoV (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) : Fin j ⊕ Fin j → S.V :=
  Sum.elim (fun a => F.fvec (Fin.castLE hj a)) (fun a => F'.fvec (Fin.castLE hj a))

def geoW (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E) :
    Fin j ⊕ Fin j → S.V :=
  Sum.elim (geoImg F hj A) (geoImg F' hj A')

def GeoDec (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (Y : S.V →ₗ[E] S.V) : Prop :=
  ∀ y : S.V, ∃ α β : Fin j → E,
    Y y = ∑ a, α a • geoImg F hj A a + ∑ a, β a • geoImg F' hj A' a ∧
    (∀ a, S.hT (F.fvec (Fin.castLE hj a)) y =
      ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * α c +
        ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * β c) ∧
    (∀ a, S.hT (F'.fvec (Fin.castLE hj a)) y =
      ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * β c +
        ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * α c)

theorem GeoDec.symm {F : FlagG S r T} {F' : FlagG S r T'} {hj : j ≤ r + 1} {A A' : Matrix (Fin j) (Fin j) E}
    {Y : S.V →ₗ[E] S.V} (h : GeoDec F F' hj A A' Y) : GeoDec F' F hj A' A Y := by
  unfold GeoDec at h ⊢
  intro y
  obtain ⟨α, β, h1, h2, h3⟩ := h y
  exact ⟨β, α, by rw [h1, add_comm], h3, h2⟩

theorem geo_img_mem (F : FlagG S r T) (hj : j ≤ r + 1) (A : Matrix (Fin j) (Fin j) E) (hA : StrictUp A) (a : Fin j) :
    geoImg F hj A a ∈ F.Xa a.val := by
  exact geo_W_mem hj F A hA a

theorem geometric_decomposition_maps_perp_into_flag (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (hA : StrictUp A) (hA' : StrictUp A') (Y : S.V →ₗ[E] S.V) (hdec : GeoDec F F' hj A A' Y) (H1 : Y ∈ LieU S)
    (H2 : ∀ a : Fin j, Y (F.fvec (Fin.castLE hj a)) = geoImg F hj A a)
    (hcase : (j ≤ r ∧ (Matrix.of fun a c : Fin j =>
        S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c))).det ≠ 0) ∨
      (j = r + 1 ∧ ∀ y : S.V, (∀ a, S.hT (F.fvec a) y = 0) → S.hT y y = 0 → y ∈ F.X)) :
    ∀ x ∈ perpS S F.X, Y x ∈ F.X ∧ (j ≤ r → Y x ∈ F.Xa (j - 1)) := by
  intro x hx
  have hx' : ∀ u ∈ F.X, S.hT u x = 0 := hx
  have H1' : ∀ x y, S.hT (Y x) y + S.hT x (Y y) = 0 := H1
  obtain ⟨α, β, hYx, h2, -⟩ := hdec x
  have hP : ∑ a, α a • geoImg F hj A a ∈ F.X :=
    sum_mem fun a _ => Submodule.smul_mem _ _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA a))
  rcases hcase with ⟨hjr, hdet⟩ | ⟨hjr, han⟩
  · have hFX : ∀ a : Fin j, F.fvec (Fin.castLE hj a) ∈ F.X := by
      intro a
      have ha : a.val < r := by have := a.isLt; omega
      rw [geo_castLE_eq hj a ha, geo_fvec_cast]
      exact Submodule.subset_span ⟨_, rfl⟩
    have hβ : β = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
      funext a
      have e := h2 a
      have hz : ∀ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = 0 :=
        fun c => geo_X_X F _ _ (hFX a) (hFX c)
      rw [hx' _ (hFX a)] at e
      simp only [hz, zero_mul, Finset.sum_const_zero, zero_add] at e
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact e.symm
    subst hβ
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at hYx
    have hmem : Y x ∈ F.Xa (j - 1) := by
      rw [hYx]
      refine sum_mem fun a _ => Submodule.smul_mem _ _ ?_
      have ha : a.val ≤ j - 1 := by have := a.isLt; omega
      exact geo_Xa_mono F ha (geo_img_mem F hj A hA a)
    exact ⟨geo_Xa_le_X F _ hmem, fun _ => hmem⟩
  · refine ⟨?_, fun h => absurd h (by omega)⟩
    have hQ : ∑ a, β a • geoImg F' hj A' a ∈ F'.X :=
      sum_mem fun a _ => Submodule.smul_mem _ _ (geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' a))
    have hYimg : ∀ a : Fin j, Y (geoImg F hj A a) ∈ F.X := by
      intro a
      simp only [geoImg, map_sum, map_smul, H2]
      exact sum_mem fun b _ => Submodule.smul_mem _ _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA b))
    have hs1 : S.hT (Y x) (∑ a, α a • geoImg F hj A a) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [map_smul]
      have h1 := H1' x (geoImg F hj A a)
      have h0 : S.hT x (Y (geoImg F hj A a)) = 0 := by
        rw [← S.herm.eq (Y (geoImg F hj A a)) x, hx' _ (hYimg a), map_zero]
      rw [h0, add_zero] at h1
      rw [h1, smul_zero]
    set P := ∑ a, α a • geoImg F hj A a with hPdef
    set Q := ∑ a, β a • geoImg F' hj A' a with hQdef
    apply han
    · intro p
      have hp : p.val < j := by have := p.isLt; omega
      have hpe : F.fvec p = F.fvec (Fin.castLE hj ⟨p.val, hp⟩) := rfl
      have h1 := H1' (F.fvec p) x
      rw [hpe, H2, hx' _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA _)), zero_add] at h1
      rw [hpe]
      exact h1
    · have hPP : S.hT P P = 0 := geo_X_X F _ _ hP hP
      have hQQ : S.hT Q Q = 0 := geo_X_X F' _ _ hQ hQ
      have hQP : S.hT Q P = 0 := by
        have h5 := hs1
        rw [hYx, map_add, LinearMap.add_apply, hPP, zero_add] at h5
        exact h5
      have hPQ : S.hT P Q = 0 := by
        rw [← S.herm.eq Q P, hQP, map_zero]
      rw [hYx]
      simp only [map_add, LinearMap.add_apply, hPP, hQQ, hPQ, hQP, add_zero]

end Pair

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E} {j : ℕ}

theorem geo_hw (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (i : Fin j ⊕ Fin j) : geoW F F' hj A A' i ∈ Submodule.span E (Set.range (geoV F F' hj)) := by
  rcases i with a | a
  · simp only [geoW, Sum.elim_inl, geoImg]
    exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)
  · simp only [geoW, Sum.elim_inr, geoImg]
    exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

theorem geo_cross (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (a c : Fin j) :
    S.hT (geoImg F hj A a) (F'.fvec (Fin.castLE hj c)) + S.hT (F.fvec (Fin.castLE hj a)) (geoImg F' hj A' c) =
      (Aᴴ * (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) +
        (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) * A') a c := by
  simp only [geoImg, map_sum, map_smulₛₗ, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply, Zhat, brS]
  congr 1
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem geo_hsk (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (hA : StrictUp A) (hA' : StrictUp A')
    (hR : Aᴴ * (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) +
      (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) * A' = 0) (i k : Fin j ⊕ Fin j) :
    S.hT (geoW F F' hj A A' i) (geoV F F' hj k) + S.hT (geoV F F' hj i) (geoW F F' hj A A' k) = 0 := by
  rcases i with a | a <;> rcases k with c | c <;> simp only [geoW, geoV, Sum.elim_inl, Sum.elim_inr]
  · have h1 := geo_Xa_le_X F _ (geo_img_mem F hj A hA a)
    have h2 := geo_Xa_le_X F _ (geo_img_mem F hj A hA c)
    rw [geo_X_fvec F _ h1, geo_fvec_X F _ h2, add_zero]
  · have P := geo_cross F F' hj A A' a c
    rw [hR] at P
    simpa using P
  · have P := geo_cross F F' hj A A' c a
    rw [hR, Matrix.zero_apply] at P
    rw [← S.herm.eq (F.fvec (Fin.castLE hj c)) (geoImg F' hj A' a),
      ← S.herm.eq (geoImg F hj A c) (F'.fvec (Fin.castLE hj a)), add_comm, ← map_add, P, map_zero]
  · have h1 := geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' a)
    have h2 := geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' c)
    rw [geo_X_fvec F' _ h1, geo_fvec_X F' _ h2, add_zero]

theorem geo_Z_det (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (h : Dl F F' j ≠ 0) :
    ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det ≠ 0 := by
  unfold Dl leadMinorE at h
  rw [dif_pos hj] at h
  exact h

theorem geo_gram_unit (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1)
    (hcase : (j ≤ r ∧ Dl F F' j ≠ 0) ∨ (j = r + 1 ∧ Gflag F F' ≠ 0)) :
    IsUnit (geoGram (geoV F F' hj)).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  apply hw0
  have rowL : ∀ a : Fin j, ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) +
      ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) = 0 := by
    intro a
    have e := congrFun hw (Sum.inl a)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.zero_apply] at e
    exact e
  have rowR : ∀ a : Fin j, ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) +
      ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) = 0 := by
    intro a
    have e := congrFun hw (Sum.inr a)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.zero_apply] at e
    exact e
  have hZ : ∀ a c : Fin j, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) =
      ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ a c := by
    intro a c
    simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Zhat, brS]
    exact (S.herm.eq _ _).symm
  have hmvL : ∀ a : Fin j, (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ
      (fun c => w (Sum.inr c))) a =
      ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) := fun a => rfl
  have hmvR : ∀ a : Fin j, (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ
      (fun c => w (Sum.inl c))) a =
      ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) := by
    intro a
    simp only [Matrix.mulVec, dotProduct, hZ]
  have hw_of : (fun c => w (Sum.inl c)) = 0 → (fun c => w (Sum.inr c)) = 0 → w = 0 := by
    intro h1 h2
    funext k
    rcases k with c | c
    · exact congrFun h1 c
    · exact congrFun h2 c
  rcases hcase with ⟨hjr, hD⟩ | ⟨hjr, hG⟩
  · have hdet := geo_Z_det F F' hj hD
    have hFX : ∀ a : Fin j, F.fvec (Fin.castLE hj a) ∈ F.X := by
      intro a
      have ha : a.val < r := by have := a.isLt; omega
      rw [geo_castLE_eq hj a ha, geo_fvec_cast]
      exact Submodule.subset_span ⟨_, rfl⟩
    have hF'X : ∀ a : Fin j, F'.fvec (Fin.castLE hj a) ∈ F'.X := by
      intro a
      have ha : a.val < r := by have := a.isLt; omega
      rw [geo_castLE_eq hj a ha, geo_fvec_cast]
      exact Submodule.subset_span ⟨_, rfl⟩
    apply hw_of
    · have hdetH : (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ).det ≠ 0 := by
        rw [Matrix.det_conjTranspose]
        exact fun h0 => hdet (star_eq_zero.1 h0)
      refine Matrix.eq_zero_of_mulVec_eq_zero hdetH ?_
      funext a
      rw [hmvR a, Pi.zero_apply]
      have hz : ∀ c : Fin j, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) = 0 :=
        fun c => geo_X_X F' _ _ (hF'X a) (hF'X c)
      have e := rowR a
      simp only [hz, zero_mul, Finset.sum_const_zero, add_zero] at e
      exact e
    · refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
      funext a
      rw [hmvL a, Pi.zero_apply]
      have hz : ∀ c : Fin j, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = 0 :=
        fun c => geo_X_X F _ _ (hFX a) (hFX c)
      have e := rowL a
      simp only [hz, zero_mul, Finset.sum_const_zero, zero_add] at e
      exact e
  · subst hjr
    have hcl : ∀ c : Fin (r + 1), Fin.castLE hj c = c := fun c => Fin.ext rfl
    have hPL : ∀ a : Fin (r + 1), ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) *
        w (Sum.inl c) = if a = Fin.last r then -T * w (Sum.inl (Fin.last r)) else 0 := by
      intro a
      simp only [hcl]
      rw [Fin.sum_univ_castSucc]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · rw [if_neg (Fin.castSucc_lt_last b).ne]
        have he : ∀ c : Fin r, S.hT (F.fvec b.castSucc) (F.fvec c.castSucc) = 0 := fun c => by
          rw [geo_fvec_cast, geo_fvec_cast]
          exact F.e_iso b c
        simp only [he, zero_mul, Finset.sum_const_zero, zero_add]
        rw [geo_fvec_cast, geo_fvec_last, F.z_orth b, zero_mul]
      · rw [if_pos rfl]
        have hz0 : ∀ c : Fin r, S.hT (F.fvec (Fin.last r)) (F.fvec c.castSucc) = 0 := fun c => by
          rw [geo_fvec_last, geo_fvec_cast, ← S.herm.eq (F.e c) F.z, F.z_orth c, map_zero]
        simp only [hz0, zero_mul, Finset.sum_const_zero, zero_add]
        rw [geo_fvec_last, F.z_norm]
    have hUR : ∀ a : Fin (r + 1), ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) *
        w (Sum.inr c) = if a = Fin.last r then -T' * w (Sum.inr (Fin.last r)) else 0 := by
      intro a
      simp only [hcl]
      rw [Fin.sum_univ_castSucc]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · rw [if_neg (Fin.castSucc_lt_last b).ne]
        have he : ∀ c : Fin r, S.hT (F'.fvec b.castSucc) (F'.fvec c.castSucc) = 0 := fun c => by
          rw [geo_fvec_cast, geo_fvec_cast]
          exact F'.e_iso b c
        simp only [he, zero_mul, Finset.sum_const_zero, zero_add]
        rw [geo_fvec_cast, geo_fvec_last, F'.z_orth b, zero_mul]
      · rw [if_pos rfl]
        have hz0 : ∀ c : Fin r, S.hT (F'.fvec (Fin.last r)) (F'.fvec c.castSucc) = 0 := fun c => by
          rw [geo_fvec_last, geo_fvec_cast, ← S.herm.eq (F'.e c) F'.z, F'.z_orth c, map_zero]
        simp only [hz0, zero_mul, Finset.sum_const_zero, zero_add]
        rw [geo_fvec_last, F'.z_norm]
    have hZy : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ (fun c => w (Sum.inr c)) =
        Pi.single (Fin.last r) (T * w (Sum.inl (Fin.last r))) := by
      funext a
      have e := rowL a
      rw [hPL a] at e
      rw [hmvL a]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · rw [if_neg (Fin.castSucc_lt_last b).ne, zero_add] at e
        rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last b).ne]
        exact e
      · rw [if_pos rfl] at e
        rw [Pi.single_eq_same]
        linear_combination e
    have hZx : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ (fun c => w (Sum.inl c)) =
        Pi.single (Fin.last r) (T' * w (Sum.inr (Fin.last r))) := by
      funext a
      have e := rowR a
      rw [hUR a] at e
      rw [hmvR a]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · rw [if_neg (Fin.castSucc_lt_last b).ne, add_zero] at e
        rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last b).ne]
        exact e
      · rw [if_pos rfl] at e
        rw [Pi.single_eq_same]
        linear_combination e
    have hadj : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E) (s : E),
        M *ᵥ v = Pi.single (Fin.last r) s → M.det * v (Fin.last r) = M.adjugate (Fin.last r) (Fin.last r) * s := by
      intro M v s hv
      have h1 : M.adjugate *ᵥ (M *ᵥ v) = M.det • v := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
        funext i
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
      rw [hv] at h1
      have h2 := congrFun h1 (Fin.last r)
      simp only [Matrix.mulVec_single, Pi.smul_apply, smul_eq_mul] at h2
      exact h2.symm
    have hdl : Dl F F' r = (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix
        Fin.castSucc Fin.castSucc).det := by
      unfold Dl leadMinorE
      exact dif_pos (Nat.le_succ r)
    have hDl : Dl F F' (r + 1) = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
      unfold Dl leadMinorE
      exact dif_pos hj
    have hadjll : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).adjugate (Fin.last r) (Fin.last r) =
        Dl F F' r := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, hdl, Fin.val_last,
        (Even.neg_one_pow ⟨r, rfl⟩ : ((-1 : E) ^ (r + r)) = 1), one_mul]
    have E1 := hadj _ _ _ hZy
    have E2 := hadj _ _ _ hZx
    rw [hadjll, ← hDl] at E1
    rw [Matrix.det_conjTranspose, ← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply, hadjll, ← hDl] at E2
    unfold Gflag at hG
    have hx0 : w (Sum.inl (Fin.last r)) = 0 := by
      have h0 : w (Sum.inl (Fin.last r)) * (Dl F F' (r + 1) * star (Dl F F' (r + 1)) -
          T * T' * (Dl F F' r * star (Dl F F' r))) = 0 := by
        linear_combination Dl F F' (r + 1) * E2 + star (Dl F F' r) * T' * E1
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hG
    have hy0 : w (Sum.inr (Fin.last r)) = 0 := by
      have h0 : w (Sum.inr (Fin.last r)) * (Dl F F' (r + 1) * star (Dl F F' (r + 1)) -
          T * T' * (Dl F F' r * star (Dl F F' r))) = 0 := by
        linear_combination star (Dl F F' (r + 1)) * E1 + Dl F F' r * T * E2
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hG
    have hZy0 : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ (fun c => w (Sum.inr c)) = 0 := by
      rw [hZy, hx0, mul_zero, Pi.single_zero]
    have hZx0 : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ (fun c => w (Sum.inl c)) = 0 := by
      rw [hZx, hy0, mul_zero, Pi.single_zero]
    have lead : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E),
        M *ᵥ v = 0 → v (Fin.last r) = 0 → (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 → v = 0 := by
      intro M v hMv hvl hdet
      have hv' : (fun c : Fin r => v c.castSucc) = 0 := by
        refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
        funext a
        have e := congrFun hMv a.castSucc
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hvl, mul_zero, add_zero,
          Pi.zero_apply] at e
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
        exact e
      funext c
      rcases Fin.eq_castSucc_or_eq_last c with ⟨b, rfl⟩ | rfl
      · exact congrFun hv' b
      · exact hvl
    have full : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E),
        M *ᵥ v = 0 → v (Fin.last r) = 0 → (M.det ≠ 0 ∨ (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0) →
        v = 0 := by
      intro M v hMv hvl h
      rcases h with h | h
      · exact Matrix.eq_zero_of_mulVec_eq_zero h hMv
      · exact lead M v hMv hvl h
    have hor : Dl F F' (r + 1) ≠ 0 ∨ Dl F F' r ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hG
      rw [hc.1, hc.2]
      ring
    apply hw_of
    · apply full _ _ hZx0 hx0
      rcases hor with h | h
      · left
        rw [Matrix.det_conjTranspose, ← hDl]
        exact fun h0 => h (star_eq_zero.1 h0)
      · right
        rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, ← hdl]
        exact fun h0 => h (star_eq_zero.1 h0)
    · apply full _ _ hZy0 hy0
      rcases hor with h | h
      · left
        rw [← hDl]
        exact h
      · right
        rw [← hdl]
        exact h

theorem geo_dec (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (h : IsUnit (geoGram (geoV F F' hj)).det) :
    GeoDec F F' hj A A' (geoY (geoV F F' hj) (geoW F F' hj A A')) := by
  unfold GeoDec
  intro y
  refine ⟨fun a => geoC (geoV F F' hj) (Sum.inl a) y, fun a => geoC (geoV F F' hj) (Sum.inr a) y, ?_, ?_, ?_⟩
  · have e := geo_Y_apply (geoV F F' hj) (geoW F F' hj A A') y
    rw [Fintype.sum_sum_type] at e
    exact e
  · intro a
    have e := geo_repr (geoV F F' hj) h (Sum.inl a) y
    rw [Fintype.sum_sum_type] at e
    exact e
  · intro a
    have e := geo_repr (geoV F F' hj) h (Sum.inr a) y
    rw [Fintype.sum_sum_type, add_comm] at e
    exact e

theorem geo_main (K : Type) [Field K] [Algebra K E] (F : FlagG S r T) (F' : FlagG S r T')
    (han : ∀ y : S.V, (∀ a, S.hT (F.fvec a) y = 0) → S.hT y y = 0 → y ∈ F.X)
    (han' : ∀ y : S.V, (∀ a, S.hT (F'.fvec a) y = 0) → S.hT y y = 0 → y ∈ F'.X)
    (hrel : Relevant K F F') (hj : j ≤ r + 1)
    (hcase : (j ≤ r ∧ Dl F F' j ≠ 0) ∨ (j = r + 1 ∧ Gflag F F' ≠ 0)) (A A' : Matrix (Fin j) (Fin j) E)
    (hA : StrictUp A) (hA' : StrictUp A')
    (hR : Aᴴ * (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) +
      (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) * A' = 0) :
    Algebra.trace K E (supSum A) = Algebra.trace K E (supSum A') := by
  have hu := geo_gram_unit F F' hj hcase
  set Y := geoY (geoV F F' hj) (geoW F F' hj A A') with hY
  have H1 : Y ∈ LieU S := fun x y =>
    geo_skew _ _ hu (geo_hw F F' hj A A') (geo_hsk F F' hj A A' hA hA' hR) x y
  have H2 : ∀ a : Fin j, Y (F.fvec (Fin.castLE hj a)) = geoImg F hj A a := fun a =>
    geo_Y_v (geoV F F' hj) (geoW F F' hj A A') hu (Sum.inl a)
  have H2' : ∀ a : Fin j, Y (F'.fvec (Fin.castLE hj a)) = geoImg F' hj A' a := fun a =>
    geo_Y_v (geoV F F' hj) (geoW F F' hj A A') hu (Sum.inr a)
  have hdec := geo_dec F F' hj A A' hu
  have c1 : (j ≤ r ∧ (Matrix.of fun a c : Fin j =>
        S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c))).det ≠ 0) ∨
      (j = r + 1 ∧ ∀ y : S.V, (∀ a, S.hT (F.fvec a) y = 0) → S.hT y y = 0 → y ∈ F.X) := by
    rcases hcase with ⟨h, hD⟩ | ⟨h, _⟩
    · exact Or.inl ⟨h, geo_Z_det F F' hj hD⟩
    · exact Or.inr ⟨h, han⟩
  have c2 : (j ≤ r ∧ (Matrix.of fun a c : Fin j =>
        S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c))).det ≠ 0) ∨
      (j = r + 1 ∧ ∀ y : S.V, (∀ a, S.hT (F'.fvec a) y = 0) → S.hT y y = 0 → y ∈ F'.X) := by
    rcases hcase with ⟨h, hD⟩ | ⟨h, _⟩
    · refine Or.inl ⟨h, ?_⟩
      have e : (Matrix.of fun a c : Fin j => S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c))) =
          ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ := by
        ext a c
        show S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = star (S.hT (F.fvec _) (F'.fvec _))
        rw [← S.herm.eq]; rfl
      rw [e, Matrix.det_conjTranspose]
      exact star_ne_zero.2 (geo_Z_det F F' hj hD)
    · exact Or.inr ⟨h, han'⟩
  have s1 := geo_side hj F A hA Y H1 H2 (geometric_decomposition_maps_perp_into_flag F F' hj A A' hA hA' Y hdec H1 H2 c1)
  have s2 := geo_side hj F' A' hA' Y H1 H2' (geometric_decomposition_maps_perp_into_flag F' F hj A' A hA' hA Y hdec.symm H1 H2' c2)
  have := hrel Y ⟨s1.1, s2.1⟩
  unfold FlagG.dpsi at this
  rwa [s1.2, s2.2] at this

theorem geo_supSum_smul {n : ℕ} (c : E) (A : Matrix (Fin n) (Fin n) E) : supSum (c • A) = c * supSum A := by
  unfold supSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

theorem geo_strict_smul {n : ℕ} (c : E) (A : Matrix (Fin n) (Fin n) E) (h : StrictUp A) : StrictUp (c • A) := by
  unfold StrictUp at h ⊢
  intro a b hab
  simp [h a b hab]

end Main

theorem cell_geom : LeadingBlocksRelevant := by
  unfold LeadingBlocksRelevant
  intro K E _ _ _ _ _ S r T T' F F' htr han han' hrel j hj hcase
  unfold MatRel
  intro A A' hA hA' hR
  have key : ∀ c : E, Algebra.trace K E (c * supSum A) = Algebra.trace K E (star c * supSum A') := by
    intro c
    have h := geo_main K F F' han han' hrel hj hcase (c • A) (star c • A') (geo_strict_smul c A hA)
      (geo_strict_smul (star c) A' hA') (by
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hR, smul_zero])
    rwa [geo_supSum_smul, geo_supSum_smul] at h
  have h1 := congrArg (algebraMap K E) (key (star (supSum A - star (supSum A'))))
  rw [htr, htr] at h1
  simp only [star_mul', star_star, star_sub] at h1
  have h2 : (supSum A - star (supSum A')) * (star (supSum A) - supSum A') = 0 := by
    linear_combination (1 / 2 : E) * h1
  have h3 : supSum A - star (supSum A') = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · have h4 : star (supSum A - star (supSum A')) = 0 := by
        rw [star_sub, star_star]
        exact h
      exact star_eq_zero.1 h4
  exact sub_eq_zero.1 h3

end Formalism.MainNotions.BridgeLemma

end
