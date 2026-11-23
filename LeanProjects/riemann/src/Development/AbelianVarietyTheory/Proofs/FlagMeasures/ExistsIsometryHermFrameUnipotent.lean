import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
open Matrix

noncomputable section
open scoped BigOperators

namespace GlobalTheory.RatIsoFrame

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r : ℕ}

def bl (y : V) : V →ₗ[K] K := H.B.flip y

@[simp] theorem bl_apply (y v : V) : bl H y v = H.B v y := rfl

def crd (e f : Fin r → V) (z : V) (g h : Fin r → V) (t : V) : V →ₗ[K] V :=
  ∑ a, (bl H (f a)).smulRight (g a) + ∑ a, (bl H (e a)).smulRight (h a) +
    ((H.B z z)⁻¹ • bl H z).smulRight t

theorem crd_apply (e f : Fin r → V) (z : V) (g h : Fin r → V) (t v : V) :
    crd H e f z g h t v = ∑ a, H.B v (f a) • g a + ∑ a, H.B v (e a) • h a +
      ((H.B z z)⁻¹ * H.B v z) • t := by
  simp [crd, LinearMap.sum_apply, smul_eq_mul]

def nil (e f : Fin r → V) : V →ₗ[K] V := LinearMap.id - ∑ b, (bl H (f b)).smulRight (e b)

theorem nil_apply (e f : Fin r → V) (w : V) : nil H e f w = w - ∑ b, H.B w (f b) • e b := by
  simp [nil, LinearMap.sum_apply]

def rmap (e f : Fin r → V) (z : V) (e' f' : Fin r → V) (z' : V) : V →ₗ[K] V :=
  crd H e' f' z' e f z + nil H e f ∘ₗ (LinearMap.id - crd H e' f' z' e' f' z')

theorem herm0 {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by rw [← H.herm, h, star_zero]

theorem gram (e f : Fin r → V) (z : V)
    (hee : ∀ a b, H.B (e a) (e b) = 0) (hff : ∀ a b, H.B (f a) (f b) = 0)
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, H.B (e a) z = 0) (hfz : ∀ a, H.B (f a) z = 0)
    (α β α' β' : Fin r → K) (γ γ' : K) :
    H.B (∑ a, α a • e a + ∑ a, β a • f a + γ • z) (∑ a, α' a • e a + ∑ a, β' a • f a + γ' • z) =
      ∑ a, α a * star (β' a) + ∑ a, β a * star (α' a) + γ * star γ' * H.B z z := by
  have hfe : ∀ a b, H.B (f a) (e b) = if a = b then 1 else 0 := by
    intro a b; rw [← H.herm, hef]; split_ifs with h1 h2 h2 <;> simp_all
  have hze : ∀ a, H.B z (e a) = 0 := fun a => herm0 H (hez a)
  have hzf : ∀ a, H.B z (f a) = 0 := fun a => herm0 H (hfz a)
  simp only [map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, hee, hff, hef, hfe, hez, hfz, hze, hzf]
  simp only [mul_comm (star _)]; ring

theorem rem_perp (e f : Fin r → V) (z : V)
    (hee : ∀ a b, H.B (e a) (e b) = 0) (hff : ∀ a b, H.B (f a) (f b) = 0)
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, H.B (e a) z = 0) (hfz : ∀ a, H.B (f a) z = 0) (hzz : H.B z z ≠ 0) (v : V) :
    (∀ a, H.B (v - crd H e f z e f z v) (e a) = 0) ∧ (∀ a, H.B (v - crd H e f z e f z v) (f a) = 0) ∧
      H.B (v - crd H e f z e f z v) z = 0 := by
  have hfe : ∀ a b, H.B (f a) (e b) = if a = b then 1 else 0 := by
    intro a b; rw [← H.herm, hef]; split_ifs with h1 h2 h2 <;> simp_all
  have hze : ∀ a, H.B z (e a) = 0 := fun a => herm0 H (hez a)
  have hzf : ∀ a, H.B z (f a) = 0 := fun a => herm0 H (hfz a)
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩ <;>
    simp only [crd_apply, map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, hee, hff, hef, hfe, hez, hfz, hze, hzf, sub_self]
  field_simp
  simp

theorem spanL {S : Set V} {y : V} (h : ∀ s ∈ S, H.B s y = 0) :
    ∀ x ∈ Submodule.span K S, H.B x y = 0 := by
  intro x hx
  have : Submodule.span K S ≤ LinearMap.ker (bl H y) := Submodule.span_le.2 (fun s hs => h s hs)
  exact this hx

theorem spanR {S : Set V} {y : V} (h : ∀ s ∈ S, H.B y s = 0) :
    ∀ x ∈ Submodule.span K S, H.B y x = 0 := by
  intro x hx
  have : Submodule.span K S ≤ LinearMap.ker (H.B y) := Submodule.span_le.2 (fun s hs => h s hs)
  exact this hx

theorem zz_eq (e : Fin r → V) (z z' : V) (hee : ∀ a b, H.B (e a) (e b) = 0)
    (hez : ∀ a, H.B (e a) z = 0) (hx : z' - z ∈ Submodule.span K (Set.range e)) :
    H.B z' z' = H.B z z := by
  set x := z' - z
  have hz' : z' = z + x := by simp [x]
  have h1 : H.B x z = 0 := spanL H (by rintro _ ⟨a, rfl⟩; exact hez a) x hx
  have h2 : H.B z x = 0 := herm0 H h1
  have h3 : ∀ a, H.B x (e a) = 0 := fun a => spanL H (by rintro _ ⟨b, rfl⟩; exact hee b a) x hx
  have h4 : H.B x x = 0 := spanR H (by rintro _ ⟨b, rfl⟩; exact h3 b) x hx
  rw [hz']; simp [h1, h2, h4]

theorem nil_perp (e f : Fin r → V) (z : V) (hee : ∀ a b, H.B (e a) (e b) = 0) (hff : ∀ a b, H.B (f a) (f b) = 0)
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, H.B (e a) z = 0) (hfz : ∀ a, H.B (f a) z = 0) (w : V) (hw : ∀ a, H.B w (e a) = 0) :
    (∀ a, H.B (nil H e f w) (e a) = 0) ∧ (∀ a, H.B (nil H e f w) (f a) = 0) ∧
      H.B (nil H e f w) z = H.B w z := by
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩ <;>
    simp only [nil_apply, map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, hee, hef, hez, hw, sub_self]

theorem nil_isom (e f : Fin r → V) (hee : ∀ a b, H.B (e a) (e b) = 0) (w w' : V)
    (hw : ∀ a, H.B w (e a) = 0) (hw' : ∀ a, H.B w' (e a) = 0) :
    H.B (nil H e f w) (nil H e f w') = H.B w w' := by
  have hw'' : ∀ a, H.B (e a) w' = 0 := fun a => herm0 H (hw' a)
  simp only [nil_apply, map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, hee, hw, hw'', sub_self]

theorem rem_all (e f e' f' : Fin r → V) (z z' : V) (he'e : ∀ a b, H.B (e' a) (e' b) = 0) (hf'f : ∀ a b, H.B (f' a) (f' b) = 0)
    (he'f : ∀ a b, H.B (e' a) (f' b) = if a = b then 1 else 0)
    (he'z : ∀ a, H.B (e' a) z' = 0) (hf'z : ∀ a, H.B (f' a) z' = 0) (hzz'0 : H.B z' z' ≠ 0)
    (hsp : ∀ a, e a ∈ Submodule.span K (Set.range e')) (hzd : z' - z ∈ Submodule.span K (Set.range e))
    (u : V) :
    (∀ a, H.B (u - crd H e' f' z' e' f' z' u) (e' a) = 0) ∧ (∀ a, H.B (u - crd H e' f' z' e' f' z' u) (f' a) = 0) ∧
      H.B (u - crd H e' f' z' e' f' z' u) z' = 0 ∧ (∀ a, H.B (u - crd H e' f' z' e' f' z' u) (e a) = 0) ∧
      H.B (u - crd H e' f' z' e' f' z' u) z = 0 := by
  obtain ⟨h1, h2, h3⟩ := rem_perp H e' f' z' he'e hf'f he'f he'z hf'z hzz'0 u
  have h4 : ∀ a, H.B (u - crd H e' f' z' e' f' z' u) (e a) = 0 :=
    fun a => spanR H (by rintro _ ⟨b, rfl⟩; exact h1 b) _ (hsp a)
  have h5 : H.B (u - crd H e' f' z' e' f' z' u) (z' - z) = 0 := spanR H (by rintro _ ⟨b, rfl⟩; exact h4 b) _ hzd
  refine ⟨h1, h2, h3, h4, ?_⟩
  have : H.B (u - crd H e' f' z' e' f' z' u) z = H.B (u - crd H e' f' z' e' f' z' u) z' - H.B (u - crd H e' f' z' e' f' z' u) (z' - z) := by
    rw [map_sub (H.B (u - crd H e' f' z' e' f' z' u)) z' z, sub_sub_cancel]
  rw [this, h3, h5, sub_zero]

theorem rmap_apply (e f e' f' : Fin r → V) (z z' v : V) :
    rmap H e f z e' f' z' v = crd H e' f' z' e f z v + nil H e f (v - crd H e' f' z' e' f' z' v) := by
  simp [rmap]

theorem rmap_isom (e f e' f' : Fin r → V) (z z' : V) (hee : ∀ a b, H.B (e a) (e b) = 0) (hff : ∀ a b, H.B (f a) (f b) = 0)
    (hef : ∀ a b, H.B (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, H.B (e a) z = 0) (hfz : ∀ a, H.B (f a) z = 0) (hzz : H.B z z ≠ 0) (he'e : ∀ a b, H.B (e' a) (e' b) = 0) (hf'f : ∀ a b, H.B (f' a) (f' b) = 0)
    (he'f : ∀ a b, H.B (e' a) (f' b) = if a = b then 1 else 0)
    (he'z : ∀ a, H.B (e' a) z' = 0) (hf'z : ∀ a, H.B (f' a) z' = 0)
    (hsp : ∀ a, e a ∈ Submodule.span K (Set.range e')) (hzd : z' - z ∈ Submodule.span K (Set.range e))
    (v v' : V) : H.B (rmap H e f z e' f' z' v) (rmap H e f z e' f' z' v') = H.B v v' := by
  have hzz' : H.B z' z' = H.B z z := zz_eq H e z z' hee hez hzd
  have hzz'0 : H.B z' z' ≠ 0 := hzz' ▸ hzz
  obtain ⟨a1, a2, a3, a4, a5⟩ := rem_all H e f e' f' z z' he'e hf'f he'f he'z hf'z hzz'0 hsp hzd v
  obtain ⟨b1, b2, b3, b4, b5⟩ := rem_all H e f e' f' z z' he'e hf'f he'f he'z hf'z hzz'0 hsp hzd v'
  have hv : H.B v v' = H.B (crd H e' f' z' e' f' z' v + (v - crd H e' f' z' e' f' z' v)) (crd H e' f' z' e' f' z' v' + (v' - crd H e' f' z' e' f' z' v')) := by
    simp only [add_sub_cancel]
  rw [hv, rmap_apply, rmap_apply]
  generalize v - crd H e' f' z' e' f' z' v = w at a1 a2 a3 a4 a5 ⊢
  generalize v' - crd H e' f' z' e' f' z' v' = w' at b1 b2 b3 b4 b5 ⊢
  obtain ⟨n1, n2, n3⟩ := nil_perp H e f z hee hff hef hez hfz _ a4
  obtain ⟨m1, m2, m3⟩ := nil_perp H e f z hee hff hef hez hfz _ b4
  have b1' : ∀ a, H.B (e' a) w' = 0 := fun a => herm0 H (b1 a)
  have b2' : ∀ a, H.B (f' a) w' = 0 := fun a => herm0 H (b2 a)
  have b3' : H.B z' w' = 0 := herm0 H b3
  have m1' : ∀ a, H.B (e a) (nil H e f w') = 0 := fun a => herm0 H (m1 a)
  have m2' : ∀ a, H.B (f a) (nil H e f w') = 0 := fun a => herm0 H (m2 a)
  have m3' : H.B z (nil H e f w') = 0 := herm0 H (m3.trans b5)
  have hA : H.B (crd H e' f' z' e f z v) (crd H e' f' z' e f z v') = H.B (crd H e' f' z' e' f' z' v) (crd H e' f' z' e' f' z' v') := by
    rw [crd_apply, crd_apply, crd_apply, crd_apply, gram H e f z hee hff hef hez hfz,
      gram H e' f' z' he'e hf'f he'f he'z hf'z, hzz']
  have c1 : H.B (crd H e' f' z' e f z v) (nil H e f w') = 0 := by
    rw [crd_apply]; simp only [map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, m1', m2', m3']
  have c2 : H.B (nil H e f w) (crd H e' f' z' e f z v') = 0 := by
    rw [crd_apply]; simp only [map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, n1, n2, n3, a5]
  have c3 : H.B (crd H e' f' z' e' f' z' v) w' = 0 := by
    rw [crd_apply]; simp only [map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, b1', b2', b3']
  have c4 : H.B w (crd H e' f' z' e' f' z' v') = 0 := by
    rw [crd_apply]; simp only [map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, a1, a2, a3]
  simp only [map_add, LinearMap.add_apply]
  rw [hA, c1, c2, c3, c4, nil_isom H e f hee _ _ a4 b4]

theorem rmap_vals (e f e' f' : Fin r → V) (z z' : V) (he'e : ∀ a b, H.B (e' a) (e' b) = 0) (hf'f : ∀ a b, H.B (f' a) (f' b) = 0)
    (he'f : ∀ a b, H.B (e' a) (f' b) = if a = b then 1 else 0)
    (he'z : ∀ a, H.B (e' a) z' = 0) (hf'z : ∀ a, H.B (f' a) z' = 0) (hzz'0 : H.B z' z' ≠ 0) :
    (∀ a, rmap H e f z e' f' z' (e' a) = e a) ∧ (∀ a, rmap H e f z e' f' z' (f' a) = f a) ∧
      rmap H e f z e' f' z' z' = z := by
  have hf'e : ∀ a b, H.B (f' a) (e' b) = if a = b then 1 else 0 := by
    intro a b; rw [← H.herm, he'f]; split_ifs with h1 h2 h2 <;> simp_all
  have hz'e : ∀ a, H.B z' (e' a) = 0 := fun a => herm0 H (he'z a)
  have hz'f : ∀ a, H.B z' (f' a) = 0 := fun a => herm0 H (hf'z a)
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩ <;>
    simp only [rmap_apply, crd_apply, map_add, map_sub, map_neg, map_sum, map_smul, map_smulₛₗ, map_zero, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sub_zero, mul_ite, ite_mul, mul_one, one_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_zero, star_one, ite_smul, one_smul, zero_smul, Finset.sum_const_zero, he'e, hf'f, he'f, hf'e, he'z, hf'z, hz'e, hz'f,
      inv_mul_cancel₀ hzz'0, sub_self, nil_apply]

theorem rmap_perp (e f e' f' : Fin r → V) (z z' : V)
    (hsp' : ∀ a, e' a - e a ∈ Submodule.span K (Set.range e)) (hzd : z' - z ∈ Submodule.span K (Set.range e))
    (y : V) (hy : ∀ a, H.B (e a) y = 0) :
    rmap H e f z e' f' z' y - y ∈ Submodule.span K (Set.range e) := by
  have he' : ∀ a, e' a ∈ Submodule.span K (Set.range e) := fun a => by
    have : e' a = (e' a - e a) + e a := by abel
    rw [this]; exact Submodule.add_mem _ (hsp' a) (Submodule.subset_span ⟨a, rfl⟩)
  have hβ : ∀ a, H.B y (e' a) = 0 := fun a =>
    herm0 H (spanL H (by rintro _ ⟨b, rfl⟩; exact hy b) _ (he' a))
  have heq : rmap H e f z e' f' z' y - y =
      ∑ a, H.B y (f' a) • (e a - e' a) + ((H.B z' z')⁻¹ * H.B y z') • (z - z') -
        ∑ b, H.B (y - crd H e' f' z' e' f' z' y) (f b) • e b := by
    rw [rmap_apply, nil_apply]
    generalize H.B (y - crd H e' f' z' e' f' z' y) = φ
    rw [crd_apply, crd_apply]
    simp only [hβ, zero_smul, Finset.sum_const_zero, add_zero, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [heq]
  refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
    (Submodule.smul_mem _ _ ?_)) (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
  · rw [← neg_sub]; exact Submodule.neg_mem _ (hsp' a)
  · rw [← neg_sub]; exact Submodule.neg_mem _ hzd

theorem tri_span (e e' : Fin r → V) (h : ∀ a, e' a - e a ∈ Submodule.span K (e '' {b | b < a})) :
    ∀ a, e a ∈ Submodule.span K (Set.range e') := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
  have hsub : Submodule.span K (e '' {b | b < a}) ≤ Submodule.span K (Set.range e') :=
    Submodule.span_le.2 (by rintro _ ⟨b, hb, rfl⟩; exact ih b hb)
  have : e a = e' a - (e' a - e a) := by abel
  rw [this]; exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩) (hsub (h a))

theorem tri_le (e : Fin r → V) (T : V →ₗ[K] V) (a : Fin r)
    (h : ∀ b < a, T (e b) - e b ∈ Submodule.span K (e '' {c | c < b})) :
    Submodule.span K (e '' {b | b < a}) ≤ (Submodule.span K (e '' {b | b < a})).comap T := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  have : T (e b) = (T (e b) - e b) + e b := by abel
  rw [this]
  refine Submodule.add_mem _ ?_ (Submodule.subset_span ⟨b, hb, rfl⟩)
  exact Submodule.span_mono (Set.image_mono (f := e) (fun c (hc : c < b) => lt_trans hc hb)) (h b hb)

theorem tri_map (e e' : Fin r → V) (T : V →ₗ[K] V) (hT : ∀ a, T (e' a) = e a)
    (h : ∀ a, e' a - e a ∈ Submodule.span K (e '' {b | b < a})) :
    ∀ a, T (e a) - e a ∈ Submodule.span K (e '' {b | b < a}) := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
  have hle := tri_le e T a ih
  have : T (e a) - e a = -(T (e' a - e a)) := by rw [map_sub, hT]; abel
  rw [this]; exact Submodule.neg_mem _ (hle (h a))

theorem symm_mem [FiniteDimensional K V] (m : V ≃ₗ[K] V) (S : Submodule K V)
    (hS : S ≤ S.comap (m : V →ₗ[K] V)) : ∀ x ∈ S, m.symm x ∈ S := by
  have hle : S.map (m : V →ₗ[K] V) ≤ S := Submodule.map_le_iff_le_comap.2 hS
  have heq : S.map (m : V →ₗ[K] V) = S :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq m S)
  intro x hx
  rw [← heq] at hx
  exact (Submodule.mem_map_equiv S).1 hx

theorem exists_isometry_frame_unipotent : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r : ℕ} (e f e' f' : Fin r → V) (z z' : V),
    (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (f a) (f b) = 0) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, H.B (e a) z = 0) → (∀ a, H.B (f a) z = 0) → H.B z z ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) → (∀ a b, H.B (f' a) (f' b) = 0) →
    (∀ a b, H.B (e' a) (f' b) = if a = b then 1 else 0) →
    (∀ a, H.B (e' a) z' = 0) → (∀ a, H.B (f' a) z' = 0) →
    (∀ a, e' a - e a ∈ Submodule.span K (e '' {b | b < a})) →
    z' - z ∈ Submodule.span K (Set.range e) →
    ∃ m : V ≃ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) ∧ (∀ a, m (e' a) = e a) ∧ (∀ a, m (f' a) = f a) ∧
      m z' = z ∧ (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) ∧
      (∀ a, m.symm (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m.symm y - y ∈ Submodule.span K (Set.range e)) := by
  intro K V _ _ _ _ _ H r e f e' f' z z' hee hff hef hez hfz hzz he'e hf'f he'f he'z hf'z htri hzd
  have hsp : ∀ a, e a ∈ Submodule.span K (Set.range e') := tri_span e e' htri
  have hsp' : ∀ a, e' a - e a ∈ Submodule.span K (Set.range e) :=
    fun a => Submodule.span_mono (Set.image_subset_range e _) (htri a)
  have hzz'0 : H.B z' z' ≠ 0 := (zz_eq H e z z' hee hez hzd) ▸ hzz
  have hiso := rmap_isom H e f e' f' z z' hee hff hef hez hfz hzz he'e hf'f he'f he'z hf'z hsp hzd
  obtain ⟨v1, v2, v3⟩ := rmap_vals H e f e' f' z z' he'e hf'f he'f he'z hf'z hzz'0
  have hinj : Function.Injective (rmap H e f z e' f' z') := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply H.nondeg
    intro w
    rw [← hiso x w, hx, map_zero, LinearMap.zero_apply]
  set T := rmap H e f z e' f' z' with hTdef
  let m : V ≃ₗ[K] V := LinearEquiv.ofInjectiveEndo T hinj
  have hm : ∀ x, m x = T x := fun x => rfl
  have h5 : ∀ a, T (e a) - e a ∈ Submodule.span K (e '' {b | b < a}) := tri_map e e' T v1 htri
  have h6 : ∀ y, (∀ a, H.B (e a) y = 0) → T y - y ∈ Submodule.span K (Set.range e) :=
    fun y hy => rmap_perp H e f e' f' z z' hsp' hzd y hy
  have hX : Submodule.span K (Set.range e) ≤ (Submodule.span K (Set.range e)).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have : T (e a) = (T (e a) - e a) + e a := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.span_mono (Set.image_subset_range e _) (h5 a))
      (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨m, fun x y => hiso x y, v1, v2, v3, h5, h6, fun a => ?_, fun y hy => ?_⟩
  · have hS := symm_mem m _ (tri_le e T a (fun b _ => h5 b)) _ (h5 a)
    have : m.symm (e a) - e a = -(m.symm (T (e a) - e a)) := by
      rw [map_sub, ← hm, LinearEquiv.symm_apply_apply]; abel
    rw [this]; exact Submodule.neg_mem _ hS
  · have hy' : ∀ a, H.B (e a) (m.symm y) = 0 := by
      intro a
      have : H.B (e a) (m.symm y) = H.B (T (e a)) y := by
        rw [← hiso (e a) (m.symm y), ← hm (m.symm y), LinearEquiv.apply_symm_apply]
      rw [this]
      exact spanL H (by rintro _ ⟨b, rfl⟩; exact hy b) _ (hX (Submodule.subset_span ⟨a, rfl⟩))
    have h := h6 (m.symm y) hy'
    rw [← hm, LinearEquiv.apply_symm_apply] at h
    rw [← neg_sub]; exact Submodule.neg_mem _ h

end GlobalTheory.RatIsoFrame
