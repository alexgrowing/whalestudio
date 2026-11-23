import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.NullHtpyStair

variable {R : Type} [CommRing R]

theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m' hm] at h0
  obtain ⟨β, hβ⟩ := h0
  refine ⟨sglι A ≫ β.v 0 m' (by omega), ?_⟩
  have := congrArg (fun c => c.v 0 m (zero_add m)) hβ
  beta_reduce at this
  rw [δ_v m' m hm β 0 m (zero_add m) m' 1 (by omega) (by omega), Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v] at this
  have hd : (sgl A).d 0 1 = 0 := (HomologicalComplex.isZero_single_obj_X _ _ _ 1 (by omega)).eq_of_tgt _ _
  rw [hd, zero_comp, smul_zero, add_zero] at this
  rw [Category.assoc, this]
  exact Iso.inv_hom_id_assoc _ _

theorem comp_d_eq_zero {K M : Cx R} {n : ℤ} (c : Cochain K M n) (hc : δ n (n + 1) c = 0) (p : ℤ)
    (h1 : ∀ q hq, c.v (p + 1) q hq = 0) : c.v p (p + n) rfl ≫ M.d (p + n) (p + n + 1) = 0 := by
  have := congrArg (fun c' => c'.v p (p + n + 1) (by omega)) hc
  simp only [Cochain.zero_v] at this
  rw [δ_v n (n + 1) rfl c p (p + n + 1) (by omega) (p + n) (p + 1) (by omega) rfl, h1, comp_zero, smul_zero,
    add_zero] at this
  exact this

def Good {K M : Cx R} {n : ℤ} (z : Cocycle K M n) (k : ℕ) (y : Cochain K M (n - 1)) : Prop :=
  ∀ p q (hpq : p + n = q), -(k : ℤ) < p → (δ (n - 1) n y).v p q hpq = (z : Cochain K M n).v p q hpq

theorem step {K M : Cx R} {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k : ℕ) (y : Cochain K M (n - 1)) (hy : Good z k y) :
    ∃ g : K.X (-(k : ℤ)) ⟶ M.X (-(k : ℤ) + (n - 1)), Good z (k + 1) (y + Cochain.single g (n - 1)) := by
  let c : Cochain K M n := (z : Cochain K M n) - δ (n - 1) n y
  have hc : δ n (n + 1) c = 0 := by
    simp only [c, δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]
  have h1 : ∀ q hq, c.v (-(k : ℤ) + 1) q hq = 0 := fun q hq => by
    simp only [c, Cochain.sub_v, hy (-(k : ℤ) + 1) q hq (by omega), sub_self]
  obtain ⟨g, hg⟩ := hK (-(k : ℤ)) (-(k : ℤ) + (n - 1)) (-(k : ℤ) + n) (by omega) (by omega)
    (c.v (-(k : ℤ)) (-(k : ℤ) + n) rfl) (comp_d_eq_zero c hc _ h1)
  refine ⟨g, fun p q hpq hp => ?_⟩
  rw [δ_add, Cochain.add_v]
  by_cases hpp : p = -(k : ℤ)
  · subst hpp
    obtain rfl : q = -(k : ℤ) + n := by omega
    rw [δ_v (n - 1) n (by omega) (Cochain.single g (n - 1)) _ _ hpq (-(k : ℤ) + (n - 1)) (-(k : ℤ) + 1) (by omega) rfl,
      Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), comp_zero, smul_zero, add_zero, hg]
    simp only [c, Cochain.sub_v]
    abel
  · rw [hy p q hpq (by omega), δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega), Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
    simp

def seq {K M : Cx R} [K.IsStrictlyLE 0] {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k : ℕ) : {y : Cochain K M (n - 1) // Good z k y} :=
  Nat.rec (motive := fun k => {y : Cochain K M (n - 1) // Good z k y})
    (⟨0, fun p q hpq hp => (K.isZero_of_isStrictlyLE 0 p (by omega)).eq_of_src _ _⟩ : {y : Cochain K M (n - 1) // Good z 0 y})
    (fun k ih => ⟨ih.1 + Cochain.single (step hK z k _ ih.2).choose (n - 1), (step hK z k _ ih.2).choose_spec⟩) k

theorem seq_agree {K M : Cx R} [K.IsStrictlyLE 0] {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k j : ℕ) (hkj : k ≤ j) (p q : ℤ) (hpq : p + (n - 1) = q) (hp : -(k : ℤ) < p) :
    (seq hK z j).1.v p q hpq = (seq hK z k).1.v p q hpq := by
  induction j, hkj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [← ih]
    show ((seq hK z j).1 + Cochain.single _ (n - 1)).v p q hpq = _
    rw [Cochain.add_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), add_zero]

end GlobalTheory.NullHtpyStair

open GlobalTheory.NullHtpyStair in

theorem GlobalTheory.nullHtpy_stair : ∀ (R : Type) [CommRing R] (K M : Cx R) [K.IsStrictlyLE 0],
    (∀ p n : ℤ, p ≤ 0 → Subsingleton (CohomologyClass (sgl (K.X p)) M n)) → ∀ n : ℤ,
    Subsingleton (CohomologyClass K M n) := by
  intro R _ K M _ hA n
  have hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f :=
    fun p m' m hp hm f hf => lift_of_subsingleton hm (hA p m hp) f hf
  suffices h : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨Cochain.mk (fun p q hpq => (seq hK z ((-p).toNat + 1)).1.v p q hpq), ?_⟩
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl, Cochain.mk_v, Cochain.mk_v,
    ← seq_agree hK z ((-(p + 1)).toNat + 1) ((-p).toNat + 1) (by omega) (p + 1) q _ (by omega),
    ← δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl]
  exact (seq hK z ((-p).toNat + 1)).2 p q hpq (by omega)
