import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSubConjNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReflection
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeProjectionMemOfUnitLength
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabLatInfStabVec
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RestrHomSurjective

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG

namespace GlobalTheory.UnramSelfDual

section Form

variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)

def hLin (x : Fin M → A) : (Fin M → A) →ₗ[A] A where
  toFun y := hform c J x y
  map_add' y z := by simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hLin_apply (x y : Fin M → A) : hLin c J x y = hform c J x y := rfl

theorem h_smul_right (x y : Fin M → A) (a : A) : hform c J x (a • y) = a * hform c J x y :=
  (hLin c J x).map_smul a y

theorem h_add_right (x y z : Fin M → A) :
    hform c J x (y + z) = hform c J x y + hform c J x z := (hLin c J x).map_add y z

theorem h_smul_left (x y : Fin M → A) (a : A) : hform c J (a • x) y = c a * hform c J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem h_add_left (x y z : Fin M → A) :
    hform c J (x + y) z = hform c J x z + hform c J y z := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem h_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin M → A) (z : Fin M → A) :
    hform c J (∑ i ∈ s, x i) z = ∑ i ∈ s, hform c J (x i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hform]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_left, ih]

variable {c J}

theorem h_conj (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j) (x y : Fin M → A) :
    c (hform c J x y) = hform c J y x := by
  simp only [hform, map_sum, map_mul, hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem h_mulVec (P Q : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    hform c J (P *ᵥ x) (Q *ᵥ y) = hform c (cT c P * J * Q) x y := by
  have e : ∀ (K : Matrix (Fin M) (Fin M) A) (x y : Fin M → A),
      hform c K x y = (c ∘ x) ⬝ᵥ K *ᵥ y := by
    intro K x y
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp, mul_assoc]
  have e2 : c ∘ (P *ᵥ x) = (c ∘ x) ᵥ* cT c P := by
    ext i
    simp [cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [e, e, e2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem h_unitary {g : GL (Fin M) A} (hg : g ∈ UJ c J) (x y : Fin M → A) :
    hform c J ((g : Matrix (Fin M) (Fin M) A) *ᵥ x) ((g : Matrix (Fin M) (Fin M) A) *ᵥ y) =
      hform c J x y := by
  rw [h_mulVec]
  exact congrArg (fun K => hform c K x y) hg

theorem cT_mul_of (e : Fin M → Fin M → A) (y : Fin M → A) (i : Fin M) :
    ((cT c (Matrix.of e)ᵀ * J) *ᵥ y) i = hform c J (e i) y := by
  simp only [cT, hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  rw [Finset.sum_comm]

theorem gram_one {e : Fin M → Fin M → A}
    (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) :
    cT c (Matrix.of e)ᵀ * J * (Matrix.of e)ᵀ = 1 := by
  ext i j
  rw [Matrix.one_apply, ← he, ← cT_mul_of]
  rfl

theorem expand {e : Fin M → Fin M → A}
    (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) (y : Fin M → A) :
    ∑ i, hform c J (e i) y • e i = y := by
  have h1 := mul_eq_one_comm.1 (gram_one he)
  have h2 := congrArg (fun K => K *ᵥ y) h1
  simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h2
  conv_rhs => rw [← h2]
  ext k
  simp only [Matrix.mulVec_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.mulVec_mulVec]
  simp only [← cT_mul_of]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem exists_unitary {e e' : Fin M → Fin M → A}
    (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0)
    (he' : ∀ i j, hform c J (e' i) (e' j) = if i = j then 1 else 0) :
    ∃ g ∈ UJ c J, ∀ i, (g : Matrix (Fin M) (Fin M) A) *ᵥ e i = e' i := by
  have h1 := gram_one he
  have h2 := mul_eq_one_comm.1 h1
  have h1' := gram_one he'
  have h2' := mul_eq_one_comm.1 h1'
  set P := (Matrix.of e)ᵀ with hP
  set P' := (Matrix.of e')ᵀ with hP'
  set Q := cT c P * J with hQ
  set Q' := cT c P' * J with hQ'
  refine ⟨⟨P' * Q, P * Q', ?_, ?_⟩, ?_, fun i => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, h1, Matrix.one_mul, h2']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q', h1', Matrix.one_mul, h2]
  · show cT c (P' * Q) * J * (P' * Q) = J
    have h3 : cT c Q * cT c P = 1 := by rw [← cT_mul, h2, cT_one]
    calc cT c (P' * Q) * J * (P' * Q) = cT c Q * (Q' * P') * Q := by
          rw [cT_mul, hQ']; simp only [Matrix.mul_assoc]
      _ = (cT c Q * cT c P) * J := by rw [h1', Matrix.mul_one, Matrix.mul_assoc]
      _ = J := by rw [h3, Matrix.one_mul]
  · show (P' * Q) *ᵥ e i = e' i
    rw [← Matrix.mulVec_mulVec]
    have : Q *ᵥ e i = Pi.single i 1 := by
      ext k
      rw [hQ, hP, cT_mul_of, he, Pi.single_apply]
    rw [this]
    ext k
    simp [hP']

end Form

section Lattice

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {O : Subalgebra R A}
  {c : A →+* A} {M : ℕ} {J : Matrix (Fin M) (Fin M) A} {L : Submodule O (Fin M → A)}

theorem smul_mem' {a : A} (ha : a ∈ O) {y : Fin M → A} (hy : y ∈ L) : a • y ∈ L :=
  L.smul_mem (⟨a, ha⟩ : O) hy

theorem mem_iff_coord (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O) {e : Fin M → Fin M → A}
    (heL : ∀ i, e i ∈ L) (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0)
    (y : Fin M → A) : y ∈ L ↔ ∀ i, hform c J (e i) y ∈ O := by
  refine ⟨fun hy i => (hL y).1 hy _ (heL i), fun h => ?_⟩
  rw [← expand he y]
  exact sum_mem fun i _ => smul_mem' (h i) (heL i)

theorem exists_next [Nontrivial A] (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (hO : ∀ a ∈ O, c a ∈ O) {p q : A} (hp : p ∈ O) (hpc : c p = p) (hpq : p * q = 1)
    (hq : q ∉ O)
    (hloc : ∀ a ∈ O, c a = a → (∃ b ∈ O, a * b = 1) ∨ ∃ b ∈ O, a = p * b)
    (hθ : ∃ θ ∈ O, ∃ b ∈ O, (θ - c θ) * b = 1)
    (hnorm : ∀ a ∈ O, c a = a → (∃ b ∈ O, a * b = 1) → ∃ x ∈ O, c x * x = a)
    (hfg : L.FG) (hsp : Submodule.span A (L : Set (Fin M → A)) = ⊤)
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O)
    {k : ℕ} (hk : k < M) {e : Fin k → Fin M → A} (heL : ∀ i, e i ∈ L)
    (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) :
    ∃ y ∈ L, (∀ i, hform c J (e i) y = 0) ∧ hform c J y y = 1 := by
  by_contra hcon
  let π : (Fin M → A) →ₗ[A] (Fin M → A) :=
    LinearMap.id - ∑ i, (hLin c J (e i)).smulRight (e i)
  have hπ : ∀ y, π y = y - ∑ i, hform c J (e i) y • e i := fun y => by
    simp [π, LinearMap.sum_apply, hLin_apply]
  have hπL : ∀ y ∈ L, π y ∈ L := fun y hy => by
    rw [hπ]
    exact sub_mem hy (sum_mem fun i _ => smul_mem' ((hL y).1 hy _ (heL i)) (heL i))
  have hπe : ∀ y j, hform c J (e j) (π y) = 0 := fun y j => by
    rw [hπ, ← hLin_apply, map_sub, map_sum]
    simp [hLin_apply, he]
  let N : Submodule O (Fin M → A) := L.map (π.restrictScalars O)
  have hN : ∀ y, y ∈ N ↔ y ∈ L ∧ ∀ j, hform c J (e j) y = 0 := fun y => by
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hπL z hz, hπe z⟩
    · rintro ⟨hy, h⟩
      refine ⟨y, hy, ?_⟩
      show π y = y
      rw [hπ]; simp [h]
  have hqc : c q = q := by
    have := congrArg c hpq
    rw [map_mul, hpc, map_one] at this
    linear_combination q * this - c q * hpq

  have h1 : ∀ y ∈ N, q * hform c J y y ∈ O := by
    intro y hy
    obtain ⟨hyL, hy0⟩ := (hN y).1 hy
    have hfix := h_conj hc hJ y y
    rcases hloc _ ((hL y).1 hyL y hyL) hfix with ⟨b, hb, hb1⟩ | ⟨b, hb, hb1⟩
    · exfalso
      have hbc : c b = b := by
        have := congrArg c hb1
        rw [map_mul, hfix, map_one] at this
        linear_combination b * this - c b * hb1
      obtain ⟨a, ha, hab⟩ := hnorm b hb hbc ⟨_, (hL y).1 hyL y hyL, by rw [mul_comm, hb1]⟩
      refine hcon ⟨a • y, smul_mem' ha hyL, fun i => ?_, ?_⟩
      · rw [h_smul_right, hy0, mul_zero]
      · rw [h_smul_right, h_smul_left]
        linear_combination hform c J y y * hab + hb1
    · have : q * hform c J y y = b := by rw [hb1]; linear_combination b * hpq
      rwa [this]

  have h2 : ∀ y ∈ N, ∀ z ∈ N, q * hform c J z y ∈ O := by
    intro y hy z hz
    have htr : ∀ a ∈ O, q * (a * hform c J z y + c a * hform c J y z) ∈ O := by
      intro a ha
      have e1 := h1 _ (add_mem hz (smul_mem' ha hy))
      have e2 : q * (a * hform c J z y + c a * hform c J y z) =
          q * hform c J (z + a • y) (z + a • y) - q * hform c J z z -
            (c a * a) * (q * hform c J y y) := by
        simp only [h_add_left, h_add_right, h_smul_left, h_smul_right]
        ring
      rw [e2]
      exact sub_mem (sub_mem e1 (h1 z hz)) (mul_mem (mul_mem (hO a ha) ha) (h1 y hy))
    obtain ⟨θ, hθO, b, hb, hθb⟩ := hθ
    have e3 : q * hform c J z y = b * (q * (θ * hform c J z y + c θ * hform c J y z) -
        c θ * (q * (1 * hform c J z y + c 1 * hform c J y z))) := by
      rw [map_one]
      linear_combination (-(q * hform c J z y)) * hθb
    rw [e3]
    exact mul_mem hb (sub_mem (htr θ hθO) (mul_mem (hO θ hθO) (htr 1 (one_mem _))))
  have h3 : ∀ y ∈ N, q • y ∈ N := by
    intro y hy
    obtain ⟨hyL, hy0⟩ := (hN y).1 hy
    refine (hN _).2 ⟨(hL _).2 fun z hz => ?_, fun j => by rw [h_smul_right, hy0, mul_zero]⟩
    have e1 : z = π z + ∑ i, hform c J (e i) z • e i := by rw [hπ, sub_add_cancel]
    rw [h_smul_right, e1, h_add_left, h_sum_left]
    simp only [h_smul_left, hy0, mul_zero, Finset.sum_const_zero, add_zero]
    exact h2 y hy _ ⟨z, hz, rfl⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {(⟨p, hp⟩ : O)}) N (hfg.map _) fun y hy => by
      have : y = (⟨p, hp⟩ : O) • (q • y) := by
        show y = p • (q • y)
        rw [smul_smul, hpq, one_smul]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (h3 y hy)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hr
  have ha' : (a : A) * p = r - 1 := congrArg Subtype.val ha
  have hca : c a * p = c r - 1 := by
    have := congrArg c ha'
    rwa [map_mul, hpc, map_sub, map_one] at this
  have hru : ∃ b, b * (r : A) = 1 := by
    rcases hloc (c r * r) (mul_mem (hO _ r.2) r.2) (by rw [map_mul, hc, mul_comm]) with
      ⟨b, -, hb⟩ | ⟨b, hb, hb1⟩
    · exact ⟨c r * b, by linear_combination hb⟩
    · exfalso
      apply hq
      have : q = b - c a * r - a := by
        linear_combination q * hb1 + q * r * hca + q * ha' + (b - c a * r - a) * hpq
      rw [this]
      exact sub_mem (sub_mem hb (mul_mem (hO _ a.2) r.2)) a.2
  obtain ⟨b, hb⟩ := hru
  have h4 : ∀ y, π y = 0 := by
    have : Submodule.span A (L : Set (Fin M → A)) ≤ LinearMap.ker π := by
      refine Submodule.span_le.2 fun y hy => ?_
      have h5 : (r : A) • π y = 0 := hr0 _ ⟨y, hy, rfl⟩
      show π y = 0
      rw [← one_smul A (π y), ← hb, mul_smul, h5, smul_zero]
    intro y
    exact this (hsp ▸ Submodule.mem_top)
  have h6 : Submodule.span A (Set.range e) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have := h4 y
    rw [hπ, sub_eq_zero] at this
    rw [this]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h7 := finrank_le_of_span_eq_top h6
  simp at h7
  omega

theorem exists_family (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (step : ∀ k < M, ∀ e : Fin k → Fin M → A, (∀ i, e i ∈ L) →
      (∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) →
      ∃ y ∈ L, (∀ i, hform c J (e i) y = 0) ∧ hform c J y y = 1)
    {x : Fin M → A} (hx : x ∈ L) (hx1 : hform c J x x = 1) (k : ℕ) (hk : k + 1 ≤ M) :
    ∃ e : Fin (k + 1) → Fin M → A, (∀ i, e i ∈ L) ∧
      (∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) ∧ e 0 = x := by
  induction k with
  | zero => exact ⟨fun _ => x, fun _ => hx, fun i j => by
      rw [hx1, if_pos (Subsingleton.elim (α := Fin 1) i j)], rfl⟩
  | succ k ih =>
    obtain ⟨e, heL, he, he0⟩ := ih (by omega)
    obtain ⟨y, hy, hy0, hy1⟩ := step (k + 1) (by omega) e heL he
    refine ⟨Fin.snoc (α := fun _ => Fin M → A) e y, fun i => ?_, fun i j => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hy
      · simpa using heL i
    · refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hy1
      · have := h_conj hc hJ (e j) y
        rw [hy0, map_zero] at this
        simp [← this, (Fin.castSucc_lt_last j).ne']
      · simp [hy0, (Fin.castSucc_lt_last i).ne]
      · simp [he]
    · rw [← he0, ← Fin.castSucc_zero, Fin.snoc_castSucc]

theorem exists_basis (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O) {e : Fin M → Fin M → A}
    (heL : ∀ i, e i ∈ L) (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) :
    ∃ b : Module.Basis (Fin M) O L, ∀ i, (b i : Fin M → A) = e i := by
  let f : Fin M → L := fun i => ⟨e i, heL i⟩
  have hli : LinearIndependent O f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : ∑ i, (g i : A) • e i = 0 := by
      have := congrArg Subtype.val hg
      simpa [f, Subalgebra.smul_def] using this
    have h2 := congrArg (hLin c J (e j)) h1
    rw [map_sum, map_zero] at h2
    simp only [map_smul, hLin_apply, he, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
    exact Subtype.ext h2
  have hsp : ⊤ ≤ Submodule.span O (Set.range f) := by
    intro y _
    have : y = ∑ i, (⟨hform c J (e i) y, (hL y).1 y.2 _ (heL i)⟩ : O) • f i := by
      apply Subtype.ext
      conv_lhs => rw [← expand he y]
      simp [f, Subalgebra.smul_def]
    rw [this]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => by simp [f]⟩

theorem exists_unitary_lat {L' : Submodule O (Fin M → A)}
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O)
    (hL' : ∀ y, y ∈ L' ↔ ∀ z ∈ L', hform c J z y ∈ O) {e e' : Fin M → Fin M → A}
    (heL : ∀ i, e i ∈ L) (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0)
    (heL' : ∀ i, e' i ∈ L') (he' : ∀ i j, hform c J (e' i) (e' j) = if i = j then 1 else 0) :
    ∃ g ∈ UJ c J, (∀ i, (g : Matrix (Fin M) (Fin M) A) *ᵥ e i = e' i) ∧
      ∀ y, y ∈ L ↔ (g : Matrix (Fin M) (Fin M) A) *ᵥ y ∈ L' := by
  obtain ⟨g, hg, hge⟩ := exists_unitary he he'
  refine ⟨g, hg, hge, fun y => ?_⟩
  rw [mem_iff_coord hL heL he, mem_iff_coord hL' heL' he']
  simp only [← hge, h_unitary hg]

theorem exists_image (hfg : L.FG) (hsp : Submodule.span A (L : Set (Fin M → A)) = ⊤)
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O) {g : GL (Fin M) A} (hg : g ∈ UJ c J) :
    ∃ L' : Submodule O (Fin M → A), L'.FG ∧ Submodule.span A (L' : Set (Fin M → A)) = ⊤ ∧
      (∀ y, y ∈ L' ↔ ∀ z ∈ L', hform c J z y ∈ O) ∧
      ∀ y ∈ L, (g : Matrix (Fin M) (Fin M) A) *ᵥ y ∈ L' := by
  let f : (Fin M → A) →ₗ[A] (Fin M → A) := Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) A)
  have hs : Function.Surjective f := fun y =>
    ⟨((g⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) *ᵥ y, by
      simp only [f, Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  refine ⟨L.map (f.restrictScalars O), hfg.map _, ?_, fun y => ?_, fun y hy => ⟨y, hy, rfl⟩⟩
  · show Submodule.span A (f '' (L : Set (Fin M → A))) = ⊤
    rw [← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top.2 hs]
  · obtain ⟨y, rfl⟩ := hs y
    constructor
    · rintro ⟨y', hy', hyy⟩ _ ⟨z, hz, rfl⟩
      rw [← hyy]
      exact (h_unitary hg z y').symm ▸ (hL y').1 hy' z hz
    · intro h
      refine ⟨y, (hL y).2 fun z hz => ?_, rfl⟩
      exact h_unitary hg z y ▸ h _ ⟨z, hz, rfl⟩

end Lattice

section Local

open GlobalTheory.SelfDualLatticeCompare IsLocalRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))

theorem sigR_algebraMap (a : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Ev F E v) a) = algebraMap (Fv F v) (Ev F E v) a := by
  show a ⊗ₜ[F] σ 1 = a ⊗ₜ[F] (1 : E)
  rw [map_one]

theorem exists_of_fixed (h : IsCMExt F E σ) {a : Ev F E v} (ha : sigR (Fv F v) σ a = a) :
    ∃ k, algebraMap (Fv F v) (Ev F E v) k = a := by
  have h2 : algebraMap (Fv F v) (Ev F E v) (algebraMap F (Fv F v) (1 / 2)) * 2 = 1 := by
    rw [← IsScalarTower.algebraMap_apply, ← map_ofNat (algebraMap F (Ev F E v)) 2, ← map_mul,
      show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  refine ⟨algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Ev F E v) a, ?_⟩
  rw [map_mul, trace_tensor _ h, ha, ← two_mul, ← mul_assoc, h2, one_mul]

theorem exists_of_fixed_int (h : IsCMExt F E σ) {a : Ev F E v} (hO : a ∈ OEv F E v)
    (ha : sigR (Fv F v) σ a = a) :
    ∃ r : v.adicCompletionIntegers F, algebraMap _ (Ev F E v) r = a := by
  obtain ⟨a, rfl⟩ := exists_of_fixed v h ha
  have hi : IsIntegral (v.adicCompletionIntegers F) a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (v.adicCompletionIntegers F)
      (v.adicCompletion F) (Ev F E v)) (algebraMap (Fv F v) (Ev F E v)).injective).1 hO
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨b, rfl⟩

theorem exists_uniformiser (h : IsCMExt F E σ) :
    ∃ p q : Ev F E v, p ∈ OEv F E v ∧ sigR (Fv F v) σ p = p ∧ p * q = 1 ∧ q ∉ OEv F E v ∧
      ∀ a ∈ OEv F E v, sigR (Fv F v) σ a = a →
        (∃ b ∈ OEv F E v, a * b = 1) ∨ ∃ b ∈ OEv F E v, a = p * b := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have h0 : (ϖ : Fv F v) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  refine ⟨algebraMap (Fv F v) _ (ϖ : Fv F v), algebraMap (Fv F v) _ (ϖ : Fv F v)⁻¹,
    (OEv F E v).algebraMap_mem ϖ, sigR_algebraMap v _, ?_, fun hq => ?_, fun a ha hc => ?_⟩
  · rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  · obtain ⟨r, hr⟩ := exists_of_fixed_int v h hq (sigR_algebraMap v _)
    have hr' : (r : Fv F v) = (ϖ : Fv F v)⁻¹ := (algebraMap (Fv F v) (Ev F E v)).injective hr
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one r (Subtype.ext ?_))
    show (ϖ : Fv F v) * r = 1
    rw [hr', mul_inv_cancel₀ h0]
  · obtain ⟨r, rfl⟩ := exists_of_fixed_int v h ha hc
    by_cases hr : IsUnit r
    · obtain ⟨b, hb⟩ := hr.exists_right_inv
      exact Or.inl ⟨_, (OEv F E v).algebraMap_mem b, by rw [← map_mul, hb, map_one]⟩
    · have : r ∈ maximalIdeal _ := hr
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
      obtain ⟨b, rfl⟩ := this
      exact Or.inr ⟨_, (OEv F E v).algebraMap_mem b, by rw [map_mul]; rfl⟩

theorem exists_norm (h : IsCMExt F E σ)
    (hθ : ∃ θ ∈ OEv F E v, ∃ b ∈ OEv F E v, (θ - sigR (Fv F v) σ θ) * b = 1) :
    ∀ a ∈ OEv F E v, sigR (Fv F v) σ a = a → (∃ b ∈ OEv F E v, a * b = 1) →
      ∃ x ∈ OEv F E v, sigR (Fv F v) σ x * x = a := by
  rintro a ha hc ⟨b, hb, hab⟩
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  let c : OEv F E v →+* OEv F E v :=
    (sigR (Fv F v) σ).restrict (OEv F E v).toSubring (OEv F E v).toSubring fun _ => sigR_mem σ v
  obtain ⟨θ, hθO, t, ht, hθt⟩ := hθ
  obtain ⟨x, hx⟩ := GlobalTheory.UnramifiedHermitian.exists_norm_eq_of_henselian
    (R₀ := v.adicCompletionIntegers F) c (fun x => Subtype.ext (sigR_sigR (Fv F v) h (x : Ev F E v)))
    (fun r => Subtype.ext (sigR_algebraMap v (r : Fv F v)))
    (fun x hx => by
      obtain ⟨r, hr⟩ := exists_of_fixed_int v h x.2 (congrArg Subtype.val hx)
      exact ⟨r, Subtype.ext hr⟩)
    ⟨⟨θ, hθO⟩, IsUnit.of_mul_eq_one ⟨t, ht⟩ (Subtype.ext hθt)⟩
    (u := ⟨a, ha⟩) (Subtype.ext hc) (IsUnit.of_mul_eq_one ⟨b, hb⟩ (Subtype.ext hab))
  exact ⟨x, x.2, by rw [mul_comm]; exact congrArg Subtype.val hx⟩

variable {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem JR_herm (hJ : IsHermND σ J) (i j : Fin M) :
    sigR (Fv F v) σ (JR (F := F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by
  show (1 : Fv F v) ⊗ₜ[F] σ (J j i) = (1 : Fv F v) ⊗ₜ[F] J i j
  rw [hJ.1]

theorem JR_det (hJ : IsHermND σ J) : IsUnit (JR (F := F) (Fv F v) J).det := by
  have := (IsUnit.mk0 _ hJ.2).map (inclR (F := F) (E := E) (Fv F v))
  rwa [RingHom.map_det] at this

theorem sd_iff {L : Submodule (OEv F E v) (Fin M → Ev F E v)} (hL : IsSDLat σ J v L) (y) :
    y ∈ L ↔ ∀ z ∈ L, hform (sigR (Fv F v) σ) (JR (Fv F v) J) z y ∈ OEv F E v :=
  (hL.2.2 y).trans ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

theorem exists_frame (h : IsCMExt F E σ) (hv : UnramAt F E v) {m : ℕ}
    {J : Matrix (Fin (m + 1)) (Fin (m + 1)) E} (hJ : IsHermND σ J)
    {L : Submodule (OEv F E v) (Fin (m + 1) → Ev F E v)} (hL : IsSDLat σ J v L) :
    (∃ x ∈ L, hR (Fv F v) σ J x x = 1) ∧ ∀ x ∈ L, hR (Fv F v) σ J x x = 1 →
      ∃ e : Fin (m + 1) → Fin (m + 1) → Ev F E v, (∀ i, e i ∈ L) ∧
        (∀ i j, hform (sigR (Fv F v) σ) (JR (Fv F v) J) (e i) (e j) = if i = j then 1 else 0) ∧
        e 0 = x := by
  obtain ⟨p, q, hp, hpc, hpq, hq, hloc⟩ := exists_uniformiser v h
  have hθ := GlobalTheory.UnramConjUnit.exists_sub_conj_unit F E σ h v hv
  have step := fun k (hk : k < m + 1) (e : Fin k → Fin (m + 1) → Ev F E v) heL he =>
    exists_next (sigR_sigR _ h) (JR_herm v hJ) (fun _ => sigR_mem σ v) hp hpc hpq hq hloc hθ
      (exists_norm v h hθ) hL.1 hL.2.1 (sd_iff v hL) hk (e := e) heL he
  refine ⟨?_, fun x hx hx1 =>
    exists_family (sigR_sigR _ h) (JR_herm v hJ) step hx hx1 m le_rfl⟩
  obtain ⟨y, hy, -, hy1⟩ := step 0 (Nat.succ_pos m) Fin.elim0 (fun i => i.elim0)
    (fun i => i.elim0)
  exact ⟨y, hy, hy1⟩

end Local

open GlobalTheory.SelfDualLatticeCompare in

theorem selfDualLattices : SelfDualLattices := by
  intro F E _ _ _ _ _ σ h M J hJ hM v hv L hL
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  obtain ⟨⟨x₀, hx₀, hx₀1⟩, hfr⟩ := exists_frame v h hv hJ hL
  obtain ⟨e, heL, he, -⟩ := hfr x₀ hx₀ hx₀1
  have hθ := GlobalTheory.UnramConjUnit.exists_sub_conj_unit F E σ h v hv
  refine ⟨?_, fun L₁ hL₁ => ?_, fun β => ?_⟩
  · obtain ⟨b, hb⟩ := exists_basis (sd_iff v hL) heL he
    exact ⟨b, fun i j => by rw [hb, hb]; exact he i j⟩
  · obtain ⟨⟨x₁, hx₁, hx₁1⟩, hfr₁⟩ := exists_frame v h hv hJ hL₁
    obtain ⟨e₁, heL₁, he₁, -⟩ := hfr₁ x₁ hx₁ hx₁1
    obtain ⟨g, hg, -, hgL⟩ := exists_unitary_lat (sd_iff v hL) (sd_iff v hL₁) heL he heL₁ he₁
    exact ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), hgL⟩
  set B : Ev F E v := algebraMap (v.adicCompletionIntegers F) _ β with hB
  set B' : Ev F E v := algebraMap (v.adicCompletionIntegers F) _ (β⁻¹ : (v.adicCompletionIntegers F)ˣ)
    with hB'
  have hBB : B * B' = 1 := by rw [hB, hB', ← map_mul, Units.mul_inv, map_one]
  have hBO : B ∈ OEv F E v := (OEv F E v).algebraMap_mem _
  have hB'O : B' ∈ OEv F E v := (OEv F E v).algebraMap_mem _
  have hq : ∀ x, qR (Fv F v) σ J x = ((β : v.adicCompletionIntegers F) : Fv F v) ↔
      hR (Fv F v) σ J x x = B := fun x => by
    rw [hR_self _ h hJ]
    exact ((algebraMap (Fv F v) (Ev F E v)).injective.eq_iff).symm
  obtain ⟨a, ha, haB⟩ := exists_norm v h hθ B hBO (sigR_algebraMap v _) ⟨B', hB'O, hBB⟩
  have hS : a • x₀ ∈ SL σ J v L ((β : v.adicCompletionIntegers F) : Fv F v) := by
    refine ⟨smul_mem' ha hx₀, (hq _).2 ?_⟩
    have : hform (sigR (Fv F v) σ) (JR (Fv F v) J) x₀ x₀ = 1 := hx₀1
    rw [hR, h_smul_left, h_smul_right, this, mul_one, haB]
  have hunit : ∀ x, qR (Fv F v) σ J x = ((β : v.adicCompletionIntegers F) : Fv F v) →
      ∃ b ∈ OEv F E v, hR (Fv F v) σ J x x * b = 1 :=
    fun x hx => ⟨B', hB'O, by rw [(hq x).1 hx, hBB]⟩
  have hwitt : ∀ x x', qR (Fv F v) σ J x = ((β : v.adicCompletionIntegers F) : Fv F v) →
      qR (Fv F v) σ J x' = ((β : v.adicCompletionIntegers F) : Fv F v) →
      ∃ g ∈ UJ (sigR (Fv F v) σ) (JR (Fv F v) J),
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ev F E v)) *ᵥ x = x' := by
    intro x x' hx hx'
    refine GlobalTheory.WittTransitivity.witt_transitive (Ev F E v) (sigR (Fv F v) σ) (sigR_sigR _ h) (fun a ha h0 => ?_) ?_ ?_ ?_
      _ _ (JR_herm v hJ) (JR_det v hJ) x x' (((hq x).1 hx).trans ((hq x').1 hx').symm) ?_
    · obtain ⟨k, rfl⟩ := exists_of_fixed v h ha
      exact (IsUnit.mk0 k fun hk => h0 (by rw [hk, map_zero])).map _
    · rw [← map_ofNat (algebraMap F (Ev F E v)) 2]
      exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
    · rw [← map_ofNat (algebraMap F (Ev F E v)) 3]
      exact ((IsUnit.mk0 (3 : F) three_ne_zero).map _).ne_zero
    · obtain ⟨θ, -, b, -, hb⟩ := hθ
      exact ⟨θ, IsUnit.of_mul_eq_one b hb⟩
    · obtain ⟨b, -, hb⟩ := hunit x hx
      exact IsUnit.of_mul_eq_one b hb
  refine ⟨⟨_, hS⟩, fun x hx => GlobalTheory.SelfDualLatticeSplit.unit_vector_splits F E σ h _ J hJ v L hL x hx.1 (hunit x hx.2),
    fun x hx x' hx' => ?_, fun x hx => ?_, fun x hx x' hx' => ?_, fun x hx => ?_⟩
  · set a' := sigR (Fv F v) σ a * B' with ha'
    have haa : a * a' = 1 := by rw [ha']; linear_combination B' * haB + hBB
    have ha'O : a' ∈ OEv F E v := mul_mem (sigR_mem σ v ha) hB'O
    have hca : sigR (Fv F v) σ a * sigR (Fv F v) σ a' = 1 := by rw [← map_mul, haa, map_one]
    have key : ∀ y ∈ SL σ J v L ((β : v.adicCompletionIntegers F) : Fv F v),
        hR (Fv F v) σ J (a' • y) (a' • y) = 1 := fun y hy => by
      have : hform (sigR (Fv F v) σ) (JR (Fv F v) J) y y = B := (hq y).1 hy.2
      rw [hR, h_smul_left, h_smul_right, this, ← haB]
      linear_combination (a * a') * hca + haa
    obtain ⟨f, hfL, hf, hf0⟩ := hfr _ (smul_mem' ha'O hx.1) (key x hx)
    obtain ⟨f', hfL', hf', hf0'⟩ := hfr _ (smul_mem' ha'O hx'.1) (key x' hx')
    obtain ⟨g, hg, hge, hgL⟩ := exists_unitary_lat (sd_iff v hL) (sd_iff v hL) hfL hf hfL' hf'
    refine ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), hgL, ?_⟩
    have h1 := congrArg (fun y => a • y) (hge 0)
    simp only [hf0, hf0', Matrix.mulVec_smul, smul_smul, haa, one_smul] at h1
    exact h1
  · have h1 := GlobalTheory.UnitVectorStabEq.stabLat_inf_stabVec F E σ h _ J hJ v L hL x hx.1 (hunit x hx.2)
    obtain ⟨b, -, hb⟩ := hunit x hx.2
    obtain ⟨φ, hφ⟩ := GlobalTheory.UnitVectorStabiliser.stabiliser_iso F E σ h _ J hJ v L x (IsUnit.of_mul_eq_one b hb)
    exact ⟨h1, (MulEquiv.subgroupCongr h1).trans φ, fun g y => hφ _ y⟩
  · obtain ⟨g, hg, hgx⟩ := hwitt x x' hx.2 hx'.2
    exact ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), hgx⟩
  · obtain ⟨g, hg, hgx⟩ := hwitt _ x hS.2 hx.2
    obtain ⟨L', h1, h2, h3, h4⟩ := exists_image hL.1 hL.2.1 (sd_iff v hL) hg
    have hL' : IsSDLat σ J v L' :=
      ⟨h1, h2, fun y => (h3 y).trans ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩⟩
    have hxL : x ∈ L' := hgx ▸ h4 _ hS.1
    exact ⟨⟨L', hL', hxL⟩, _, (GlobalTheory.SelfDualLatticeSplit.unit_vector_splits F E σ h _ J hJ v L' hL' x hxL (hunit x hx.2)).2⟩

end GlobalTheory.UnramSelfDual
