import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem not_le_hyperplane {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) (r : ℕ)
    (t e : Fin r → R) (l : Fin r) (hI : Ideal.span (Set.range t) = I)
    (hz : ∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
      ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hl : IsUnit (e l)) :
    ¬ I ≤ IsLocalRing.maximalIdeal R * I ⊔
      Ideal.span (Set.range fun i => e l * t i - e i * t l) := by
  intro hle
  have htl : t l ∈ I := hI ▸ Ideal.subset_span ⟨l, rfl⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hle htl)
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hq
  simp only [smul_eq_mul] at hx
  let S : R := ∑ j, x j * e j
  let z : Fin r → R := fun i => -(x i * e l) + if i = l then 1 + S else 0
  have hsum : ∑ i, z i * t i = p := by
    have h1 : ∑ i, z i * t i = -(e l * ∑ i, x i * t i) + (1 + S) * t l := by
      simp only [z, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : q = e l * ∑ i, x i * t i - S * t l := by
      rw [← hx]
      simp only [S, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    linear_combination h2 - hpq
  have hzm := hz z (hsum ▸ hp)
  have hxm : ∀ i, i ≠ l → x i ∈ IsLocalRing.maximalIdeal R := fun i hi => by
    have := hzm i
    simp only [z, if_neg hi, add_zero, neg_mem_iff] at this
    exact (Ideal.unit_mul_mem_iff_mem _ hl).1 (by rwa [mul_comm])
  have hS : S - x l * e l ∈ IsLocalRing.maximalIdeal R := by
    have : S - x l * e l = ∑ j ∈ Finset.univ.erase l, x j * e j := by
      have h5 : S = x l * e l + ∑ j ∈ Finset.univ.erase l, x j * e j :=
        (Finset.add_sum_erase _ (fun j => x j * e j) (Finset.mem_univ l)).symm
      rw [h5]
      ring
    rw [this]
    exact Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ (hxm j (Finset.ne_of_mem_erase hj))
  have h3 := hzm l
  simp only [z, if_true] at h3
  have h4 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have : (1 : R) = (-(x l * e l) + (1 + S)) - (S - x l * e l) := by ring
    rw [this]
    exact Ideal.sub_mem _ h3 hS
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h4

theorem corrected_compat {R B : Type} [CommRing R] [CommRing B] (c : R →+* B) (I m J : Ideal R)
    (hIm : I ≤ m) (hmI : m * I ≤ J) (r : ℕ) (t e : Fin r → R) (l : Fin r) (a' : R)
    (ha : a' * e l = 1) (ht : ∀ i, t i ∈ I) (hJ : ∀ i, e l * t i - e i * t l ∈ J)
    (ua uc g βa βc : B) (b : Fin r → B)
    (hD : ua - g * uc * (1 + ∑ i, c (t i) * b i) ∈ (m * I).map c)
    (hQ : ∑ i, c (e i) * b i - (βa - βc) ∈ m.map c) :
    ua * (1 - c (a' * t l) * βa) - g * (uc * (1 - c (a' * t l) * βc)) ∈ J.map c := by
  have hII : I * I ≤ J := (Ideal.mul_mono_left hIm).trans hmI
  have hIm' : I * m ≤ J := by rwa [mul_comm]
  have hE : c (a' * t l) ∈ I.map c := Ideal.mem_map_of_mem _ (I.mul_mem_left _ (ht l))
  have hT : ∑ i, c (t i) * b i ∈ I.map c :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ht i))
  have hTE : (∑ i, c (t i) * b i) * c (a' * t l) ∈ J.map c :=
    Ideal.map_mono hII (by rw [Ideal.map_mul]; exact Ideal.mul_mem_mul hT hE)
  have hEQ : c (a' * t l) * (∑ i, c (e i) * b i - (βa - βc)) ∈ J.map c :=
    Ideal.map_mono hIm' (by rw [Ideal.map_mul]; exact Ideal.mul_mem_mul hE hQ)
  have hP : ∑ i, c (a' * (e l * t i - e i * t l)) * b i ∈ J.map c :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ (J.mul_mem_left _ (hJ i)))
  have hDJ := Ideal.map_mono hmI hD
  have hT' : ∑ i, c (t i) * b i = ∑ i, c (a' * (e l * t i - e i * t l)) * b i +
      c (a' * t l) * ∑ i, c (e i) * b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : c a' * c (e l) = 1 := by rw [← map_mul, ha, map_one]
    simp only [map_mul, map_sub]
    linear_combination (-(c (t i) * b i)) * h1
  generalize hTd : ∑ i, c (t i) * b i = T at *
  generalize hPd : ∑ i, c (a' * (e l * t i - e i * t l)) * b i = P at *
  generalize hSd : ∑ i, c (e i) * b i = Sg at *
  generalize c (a' * t l) = E at *
  have key : ua * (1 - E * βa) - g * (uc * (1 - E * βc)) =
      (ua - g * uc * (1 + T)) * (1 - E * βa) +
        g * uc * (P + E * (Sg - (βa - βc)) - T * E * βa) := by
    rw [hT']; ring
  rw [key]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hDJ) (Ideal.mul_mem_left _ _
    (Ideal.sub_mem _ (Ideal.add_mem _ hP hEQ) (Ideal.mul_mem_right _ _ hTE)))

theorem exists_correction : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ IsLocalRing.maximalIdeal R →
    (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
    ∀ (M : LB X) (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a))
      (b : Fin r → ∀ a c, Γ(X, V a ⊓ V c)) (e : Fin r → R) (β : ∀ a, Γ(X, V a)) (l : Fin r),
      (∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
        (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a ⊓ V c)) →
      IsUnit (e l) →
      (∀ a c, ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
        ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c)) →
      ∃ (J : Ideal R) (y z : ∀ a, Γ(X, V a)), ¬ I ≤ J ∧ (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a c, rs X inf_le_left (y a) - tr M V j hj a c * rs X inf_le_right (y c) ∈ ext s J (V a ⊓ V c) := by
  intro R _ _ X s I r t hI hIm hz M A V j hj u w b e β l huw hD hl hQ
  obtain ⟨a', ha'⟩ := hl.exists_left_inv
  have hrs : ∀ {U W : X.Opens} (h : W ≤ U) (x : R),
      rs X h (GlobalTheory.SmallExtLift.cst s U x) = GlobalTheory.SmallExtLift.cst s W x := fun {U W} h x =>
    GlobalTheory.SmallExtLift.gr_ext fun y hy => by
      rw [GlobalTheory.SmallExtLift.gr_res, GlobalTheory.SmallExtLift.gr_cst, GlobalTheory.SmallExtLift.gr_cst]
  have hmJ : IsLocalRing.maximalIdeal R * I ≤ IsLocalRing.maximalIdeal R * I ⊔
      Ideal.span (Set.range fun i => e l * t i - e i * t l) := le_sup_left
  refine ⟨IsLocalRing.maximalIdeal R * I ⊔ Ideal.span (Set.range fun i => e l * t i - e i * t l),
    fun a => u a * (1 - GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a),
    fun a => w a * (1 + GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a),
    not_le_hyperplane I r t e l hI hz hl, fun a => ?_, fun a c => ?_⟩
  · have htl : t l ∈ I := hI ▸ Ideal.subset_span ⟨l, rfl⟩
    have hE2 : GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) * GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) ∈
        ext s (IsLocalRing.maximalIdeal R * I ⊔
          Ideal.span (Set.range fun i => e l * t i - e i * t l)) (V a) := by
      rw [← map_mul]
      refine Ideal.mem_map_of_mem _ (hmJ ?_)
      exact Ideal.mul_mem_mul (hIm (I.mul_mem_left _ htl)) (I.mul_mem_left _ htl)
    have h1 := Ideal.map_mono hmJ (huw a)
    have key : u a * (1 - GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a) *
        (w a * (1 + GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a)) - 1 =
        (u a * w a - 1) - (u a * w a * β a * β a) * (GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) *
          GlobalTheory.SmallExtLift.cst s (V a) (a' * t l)) := by ring
    rw [key]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ hE2)
  · have := corrected_compat (GlobalTheory.SmallExtLift.cst s (V a ⊓ V c)) I (IsLocalRing.maximalIdeal R) _
      hIm hmJ r t e l a' ha' (fun i => hI ▸ Ideal.subset_span ⟨i, rfl⟩)
      (fun i => Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
      (rs X inf_le_left (u a)) (rs X inf_le_right (u c)) (tr M V j hj a c)
      (rs X inf_le_left (β a)) (rs X inf_le_right (β c)) (fun i => b i a c) (hD a c) (hQ a c)
    simpa only [map_mul, map_sub, map_one, hrs] using this

end GlobalTheory.CompanionTheory.FewEq
