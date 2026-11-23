import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open MvPolynomial Formalism.L2.Pj

variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)

def Dom (a : T → ℕ → ℕ) : Prop := ∀ (σ : T) (i j : Fin (r σ)), i ≤ j → a σ j ≤ a σ i

def GoodL (β : (Σ σ : T, Fin (r σ)) → Fin n) : Set (Letter T r n) := {ℓ | ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2}

def diagExp (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) : Letter T r n →₀ ℕ :=
  ∑ p : Σ σ : T, Fin (r σ), Finsupp.single ⟨p.1, p.2, β p⟩ (a p.1 p.2)

def crMinor (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (σ : T) (kk : Fin (r σ)) :
    Matrix (Fin (kk.val + 1)) (Fin (kk.val + 1)) (MvPolynomial (Letter T r n) R) :=
  fun i j => X ⟨σ, Fin.castLE kk.isLt i, β ⟨σ, Fin.castLE kk.isLt j⟩⟩

def crExp (a : T → ℕ → ℕ) (σ : T) (kk : Fin (r σ)) : ℕ :=
  a σ kk - (if kk.val + 1 < r σ then a σ (kk.val + 1) else 0)

def crP (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) :
    MvPolynomial (Letter T r n) R :=
  ∏ σ : T, ∏ kk : Fin (r σ), (crMinor r n R β σ kk).det ^ crExp r a σ kk

def Pmin (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) : MvPolynomial (Letter T r n) ℤ :=
  crP r n ℤ β a

section Part1

variable {r n}

theorem crP_map (k : Type) [CommRing k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) :
    MvPolynomial.map (Int.castRingHom k) (Pmin r n β a) = crP r n k β a := by
  unfold Pmin crP
  rw [map_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun kk _ => ?_
  have hM : (MvPolynomial.map (Int.castRingHom k)).mapMatrix (crMinor r n ℤ β σ kk) =
      crMinor r n k β σ kk := by
    ext i j
    simp [crMinor, RingHom.mapMatrix_apply]
  rw [map_pow, RingHom.map_det, hM]

theorem crX_mem {R : Type} [CommRing R] {s : Set (Letter T r n)} {ℓ : Letter T r n} (h : ℓ ∈ s) :
    (X ℓ : MvPolynomial (Letter T r n) R) ∈ supported R s := by
  exact Algebra.subset_adjoin ⟨ℓ, h, rfl⟩

theorem crP_mem_supported (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) :
    crP r n R β a ∈ supported R (GoodL r n β) := by
  unfold crP
  refine Subalgebra.prod_mem _ fun σ _ => Subalgebra.prod_mem _ fun kk _ => Subalgebra.pow_mem _ ?_ _
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun π _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (Subalgebra.prod_mem _ fun i _ => ?_) _
  exact crX_mem ⟨Fin.castLE kk.isLt i, rfl⟩

theorem crPderiv_supported {R : Type} [CommRing R] {s : Set (Letter T r n)} (i : Letter T r n)
    {p : MvPolynomial (Letter T r n) R} (hp : p ∈ supported R s) : pderiv i p ∈ supported R s := by
  classical
  have hp' : p ∈ Algebra.adjoin R ((X : Letter T r n → MvPolynomial (Letter T r n) R) '' s) := hp
  clear hp
  show pderiv i p ∈ Algebra.adjoin R ((X : Letter T r n → MvPolynomial (Letter T r n) R) '' s)
  induction hp' using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, -, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | algebraMap c =>
    rw [Derivation.map_algebraMap]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hx' hy) (mul_mem hy' hx)

private theorem crPderiv_zero_lemma {R : Type} [CommRing R] {s : Set (Letter T r n)} (i : Letter T r n)
    (hi : i ∉ s) {p : MvPolynomial (Letter T r n) R} (hp : p ∈ supported R s) : pderiv i p = 0 := by
  classical
  have hp' : p ∈ Algebra.adjoin R ((X : Letter T r n → MvPolynomial (Letter T r n) R) '' s) := hp
  clear hp
  induction hp' using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply, if_neg]
    rintro rfl
    exact hi hj
  | algebraMap c => exact Derivation.map_algebraMap _ _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

theorem crP_mem_harmK (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (cc : T → T)
    (isX : T → Prop) (hcc : ∀ τ, isX τ → cc τ ≠ τ) (hβ : Function.Injective β) :
    crP r n k β a ∈ harmK r n k cc isX (fun _ => 1) := by
  unfold harmK lap
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Derivation.coeFn_coe]
  intro τ hτ x x'
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hbb : b = b'
  · subst hbb
    have hsup := crPderiv_supported ⟨cc τ, (x', b)⟩ (crP_mem_supported k β a)
    by_cases hg : (⟨τ, (x, b)⟩ : Letter T r n) ∈ GoodL r n β
    · have hg' : (⟨cc τ, (x', b)⟩ : Letter T r n) ∉ GoodL r n β := by
        rintro ⟨j, hj⟩
        obtain ⟨i0, hi0⟩ := hg
        have := hβ (hi0.trans hj.symm)
        exact hcc τ hτ (Sigma.mk.inj this).1.symm
      rw [crPderiv_zero_lemma _ hg' (crP_mem_supported k β a), map_zero, smul_zero]
    · rw [crPderiv_zero_lemma _ hg hsup, smul_zero]
  · rw [Matrix.one_apply_ne hbb, zero_smul]

end Part1

section Part2

variable {r n}

theorem crSig_iff {τ : T} {x i : Fin (r τ)} {y : Fin n} :
    (∃ b : Fin n, (⟨τ, x, y⟩ : Letter T r n) = ⟨τ, i, b⟩) ↔ x = i := by
  constructor
  · rintro ⟨b, h⟩
    exact (Prod.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).1
  · rintro rfl
    exact ⟨y, rfl⟩

theorem crSig_ne {τ σ : T} (h : τ ≠ σ) {x : Fin (r τ)} {y : Fin n} {i : Fin (r σ)} :
    ¬ ∃ b : Fin n, (⟨τ, x, y⟩ : Letter T r n) = ⟨σ, i, b⟩ := by
  rintro ⟨b, hb⟩
  exact h (Sigma.mk.inj hb).1

theorem crP_rowInv (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) :
    RowInv r n k (crP r n k β a) := by
  unfold RowInv rowShift
  intro σ i i' hii' t
  have hlt : (i' : ℕ) < i := hii'
  unfold crP
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun kk _ => ?_
  rw [map_pow, AlgHom.map_det]
  congr 1
  by_cases hcase : τ = σ ∧ (i : ℕ) ≤ kk
  · obtain ⟨rfl, hik⟩ := hcase
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin ((kk : ℕ) + 1), (i₀ : ℕ) = i := ⟨⟨i, by omega⟩, rfl⟩
    obtain ⟨i₁, hi₁⟩ : ∃ i₁ : Fin ((kk : ℕ) + 1), (i₁ : ℕ) = i' := ⟨⟨i', by omega⟩, rfl⟩
    have hne : i₀ ≠ i₁ := by
      intro h
      subst h
      omega
    conv_rhs => rw [← Matrix.det_updateRow_add_smul_self _ hne (C t)]
    congr 1
    ext p q
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, crMinor, aeval_X, Matrix.updateRow_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, crSig_iff]
    by_cases hp : p = i₀
    · subst hp
      have h1 : Fin.castLE kk.isLt p = i := Fin.ext (by simp [hi₀])
      have h2 : Fin.castLE kk.isLt i₁ = i' := Fin.ext (by simp [hi₁])
      simp [h1, h2]
    · have h1 : Fin.castLE kk.isLt p ≠ i := by
        intro h
        apply hp
        have h4 := congrArg Fin.val h
        simp at h4
        exact Fin.ext (by omega)
      simp [h1, hp]
  · congr 1
    ext p q
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, crMinor, aeval_X]
    rw [if_neg]
    rintro ⟨b, hb⟩
    apply hcase
    obtain ⟨h1, h2⟩ := Sigma.mk.inj hb
    refine ⟨h1, ?_⟩
    subst h1
    have h3 := (Prod.mk.inj (eq_of_heq h2)).1
    have h4 := congrArg Fin.val h3
    have hp := p.isLt
    simp at h4
    omega

end Part2

section Part3

variable {r n}

def crW (σ : T) (i : ℕ) : Letter T r n → ℕ := fun ℓ => if ℓ.1 = σ ∧ (ℓ.2.1 : ℕ) = i then 1 else 0

theorem crMinor_hom (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (τ : T) (kk : Fin (r τ))
    (w : Letter T r n → ℕ) (D : ℕ)
    (hw : ∀ π : Equiv.Perm (Fin (kk.val + 1)),
      ∑ j, w ⟨τ, Fin.castLE kk.isLt (π j), β ⟨τ, Fin.castLE kk.isLt j⟩⟩ = D) :
    IsWeightedHomogeneous w (crMinor r n R β τ kk).det D := by
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun π _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← hw π]
  refine IsWeightedHomogeneous.prod _ _ _ fun j _ => ?_
  apply isWeightedHomogeneous_X

theorem crP_isWeightedHomogeneous (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (w : Letter T r n → ℕ) (D : ∀ τ : T, Fin (r τ) → ℕ)
    (hD : ∀ τ kk, IsWeightedHomogeneous w (crMinor r n R β τ kk).det (D τ kk)) :
    IsWeightedHomogeneous w (crP r n R β a) (∑ τ, ∑ kk, crExp r a τ kk • D τ kk) := by
  unfold crP
  exact IsWeightedHomogeneous.prod _ _ _ fun τ _ =>
    IsWeightedHomogeneous.prod _ _ _ fun kk _ => (hD τ kk).pow _

theorem crRowSum (τ σ : T) (m i0 : ℕ) :
    (∑ j : Fin m, if τ = σ ∧ (j : ℕ) = i0 then 1 else 0) = if τ = σ ∧ i0 < m then 1 else 0 := by
  by_cases h : τ = σ
  · subst h
    simp only [eq_self_iff_true, true_and]
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = i0 then 1 else 0) m, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
  · simp [h]

theorem crTele (f : ℕ → ℕ) (R : ℕ) (hf : ∀ j, j < R → f (j + 1) ≤ f j) (hR : f R = 0) :
    ∀ d i, i + d = R → ∑ j ∈ Finset.range R, (if i ≤ j then f j - f (j + 1) else 0) = f i := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp only [Nat.add_zero] at hi
    subst hi
    rw [hR]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega)]
  | succ d ih =>
    intro i hi
    have h1 := ih (i + 1) (by omega)
    have hsplit : ∀ j, (if i ≤ j then f j - f (j + 1) else 0) =
        (if i + 1 ≤ j then f j - f (j + 1) else 0) + (if j = i then f j - f (j + 1) else 0) := by
      intro j
      by_cases h : j = i
      · subst h
        simp
      · by_cases h' : i ≤ j
        · rw [if_pos h', if_pos (by omega), if_neg h, add_zero]
        · rw [if_neg h', if_neg (by omega), if_neg h, add_zero]
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, h1, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr (by omega))]
    have := hf i (by omega)
    omega

theorem crExpSum (a : T → ℕ → ℕ) (ha : Dom r a) (σ : T) (i : Fin (r σ)) :
    (∑ kk : Fin (r σ), if (i : ℕ) < (kk : ℕ) + 1 then crExp r a σ kk else 0) = a σ i := by
  have hi := i.isLt
  let f : ℕ → ℕ := fun j => if j < r σ then a σ j else 0
  have hf : ∀ j, j < r σ → f (j + 1) ≤ f j := by
    intro j hj
    simp only [f]
    by_cases h : j + 1 < r σ
    · rw [if_pos h, if_pos hj]
      exact ha σ ⟨j, hj⟩ ⟨j + 1, h⟩ (Fin.mk_le_mk.mpr (Nat.le_succ j))
    · rw [if_neg h]
      exact Nat.zero_le _
  have hR : f (r σ) = 0 := by simp [f]
  have key := crTele f (r σ) hf hR (r σ - i) i (by omega)
  have e1 : (∑ kk : Fin (r σ), if (i : ℕ) < (kk : ℕ) + 1 then crExp r a σ kk else 0) =
      ∑ j ∈ Finset.range (r σ), (if (i : ℕ) ≤ j then f j - f (j + 1) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun kk _ => ?_
    have hk := kk.isLt
    simp only [f, crExp, if_pos hk, Nat.lt_add_one_iff]
  rw [e1, key]
  simp [f, hi]

theorem crP_isWeightedHomogeneous_crW (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (ha : Dom r a) (σ : T) (i : Fin (r σ)) :
    IsWeightedHomogeneous (crW (r := r) (n := n) σ i.val) (crP r n R β a) (a σ i) := by
  have hD : ∀ τ (kk : Fin (r τ)), IsWeightedHomogeneous (crW (r := r) (n := n) σ i.val)
      (crMinor r n R β τ kk).det (if τ = σ ∧ (i : ℕ) < (kk : ℕ) + 1 then 1 else 0) := by
    intro τ kk
    apply crMinor_hom
    intro π
    rw [← crRowSum τ σ ((kk : ℕ) + 1) (i : ℕ)]
    rw [← Equiv.sum_comp π (fun j : Fin ((kk : ℕ) + 1) => if τ = σ ∧ (j : ℕ) = (i : ℕ) then 1 else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [crW]
  have h := crP_isWeightedHomogeneous R β a _ _ hD
  convert h using 1
  rw [Finset.sum_eq_single σ]
  · rw [← crExpSum a ha σ i]
    refine Finset.sum_congr rfl fun kk _ => ?_
    by_cases hk : (i : ℕ) < (kk : ℕ) + 1
    · simp [hk]
    · simp [hk]
  · intro τ _ hτ
    apply Finset.sum_eq_zero
    intro kk _
    simp [hτ]
  · intro h
    exact absurd (Finset.mem_univ σ) h

theorem crW_weight (m : Letter T r n →₀ ℕ) (σ : T) (i : Fin (r σ)) :
    Finsupp.weight (crW (r := r) (n := n) σ i.val) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
  classical
  have hinj : Function.Injective (fun b : Fin n => (⟨σ, i, b⟩ : Letter T r n)) := by
    intro b b' h
    exact (Prod.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hw : ∀ ℓ : Letter T r n, crW (r := r) (n := n) σ i.val ℓ =
      if ℓ ∈ Finset.univ.image (fun b : Fin n => (⟨σ, i, b⟩ : Letter T r n)) then 1 else 0 := by
    rintro ⟨τ, x, y⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, crW]
    by_cases h : τ = σ
    · subst h
      by_cases hx : x = i
      · subst hx
        rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨y, rfl⟩]
      · rw [if_neg (by simp [Fin.val_inj, hx]), if_neg]
        rintro ⟨b, hb⟩
        exact hx ((Prod.mk.inj (eq_of_heq (Sigma.mk.inj hb).2)).1).symm
    · rw [if_neg (by simp [h]), if_neg]
      rintro ⟨b, hb⟩
      exact h (Sigma.mk.inj hb).1.symm
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [hw, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem]
  have hsub : ∑ ℓ ∈ m.support ∩ Finset.univ.image (fun b : Fin n => (⟨σ, i, b⟩ : Letter T r n)), m ℓ =
      ∑ ℓ ∈ Finset.univ.image (fun b : Fin n => (⟨σ, i, b⟩ : Letter T r n)), m ℓ := by
    refine Finset.sum_subset Finset.inter_subset_right fun ℓ hℓS hℓ => ?_
    by_contra h0
    exact hℓ (Finset.mem_inter.mpr ⟨Finsupp.mem_support_iff.mpr h0, hℓS⟩)
  rw [hsub, Finset.sum_image (fun b _ b' _ h => hinj h)]

theorem crP_rowDeg (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (ha : Dom r a) : RowDeg r n k a (crP r n k β a) := by
  intro m hm σ i
  have h := crP_isWeightedHomogeneous_crW k β a ha σ i (MvPolynomial.mem_support_iff.mp hm)
  rw [crW_weight] at h
  exact h

end Part3

section Part4

variable {r n}

def crDl (β : (Σ σ : T, Fin (r σ)) → Fin n) : (Σ σ : T, Fin (r σ)) → Letter T r n :=
  fun p => ⟨p.1, p.2, β p⟩

theorem crDl_inj (β : (Σ σ : T, Fin (r σ)) → Fin n) : Function.Injective (crDl (r := r) (n := n) β) := by
  rintro ⟨σ, i⟩ ⟨τ, j⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  subst h1
  obtain ⟨h3, -⟩ := Prod.mk.inj (eq_of_heq h2)
  subst h3
  rfl

theorem crDiagExp_apply (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (ℓ : Letter T r n) :
    diagExp r n β a ℓ = ∑ p, if crDl β p = ℓ then a p.1 p.2 else 0 := by
  simp only [diagExp, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rfl

theorem crDiagExp_dl (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (p : Σ σ : T, Fin (r σ)) :
    diagExp r n β a (crDl β p) = a p.1 p.2 := by
  rw [crDiagExp_apply, Finset.sum_eq_single p]
  · rw [if_pos rfl]
  · intro q _ hq
    exact if_neg (fun h => hq (crDl_inj β h))
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem crDiagExp_off (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (ℓ : Letter T r n)
    (h : ∀ p, crDl β p ≠ ℓ) : diagExp r n β a ℓ = 0 := by
  rw [crDiagExp_apply]
  exact Finset.sum_eq_zero fun p _ => if_neg (h p)

def crRho (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) :
    MvPolynomial (Letter T r n) R →ₐ[R] MvPolynomial (Letter T r n) R :=
  aeval fun ℓ => if ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩ then X ℓ else 0

def crDiag (β : (Σ σ : T, Fin (r σ)) → Fin n) : Set (Letter T r n) := {ℓ | ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩}

theorem crRho_monomial (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (u : Letter T r n →₀ ℕ) (c : R) :
    crRho R β (monomial u c) =
      if (∀ ℓ ∈ u.support, ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩) then monomial u c else 0 := by
  rw [crRho, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    simp only [if_pos (h ℓ hℓ)]
  · push_neg at h
    obtain ⟨ℓ, hℓ, hne⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hℓ, mul_zero]
    simp only [if_neg hne]
    exact zero_pow (Finsupp.mem_support_iff.mp hℓ)

theorem crRho_coeff (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (p : MvPolynomial (Letter T r n) R) (m : Letter T r n →₀ ℕ)
    (hm : ∀ ℓ ∈ m.support, ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩) : coeff m (crRho R β p) = coeff m p := by
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro u c
    rw [crRho_monomial]
    split_ifs with h
    · rfl
    · rw [coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact h hm
  · intro p q hp hq
    rw [map_add, coeff_add, coeff_add, hp, hq]

theorem crRho_supported (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (p : MvPolynomial (Letter T r n) R) : crRho R β p ∈ supported R (crDiag β) := by
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro u c
    rw [crRho_monomial]
    split_ifs with h
    · rw [monomial_eq, ← MvPolynomial.algebraMap_eq]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
        (Subalgebra.prod_mem _ fun ℓ hℓ => Subalgebra.pow_mem _ (crX_mem (h ℓ hℓ)) _)
    · exact Subalgebra.zero_mem _
  · intro p q hp hq
    rw [map_add]
    exact Subalgebra.add_mem _ hp hq

theorem crRho_minor (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (hβ : Function.Injective β) (τ : T) (kk : Fin (r τ)) :
    (crRho R β).mapMatrix (crMinor r n R β τ kk) =
      Matrix.diagonal (fun q => X ⟨τ, Fin.castLE kk.isLt q, β ⟨τ, Fin.castLE kk.isLt q⟩⟩) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [crMinor, crRho]
  · have hne : β ⟨τ, Fin.castLE kk.isLt j⟩ ≠ β ⟨τ, Fin.castLE kk.isLt i⟩ := by
      intro h'
      have h3 : Fin.castLE kk.isLt j = Fin.castLE kk.isLt i := eq_of_heq (Sigma.mk.inj (hβ h')).2
      exact h (Fin.castLE_injective _ h3).symm
    simp [crMinor, crRho, Matrix.diagonal_apply_ne _ h, hne]

def crIsMono {R : Type} [CommRing R] (p : MvPolynomial (Letter T r n) R) : Prop :=
  ∃ E, p = monomial E 1

theorem crIsMono_mul {R : Type} [CommRing R] {p q : MvPolynomial (Letter T r n) R} (hp : crIsMono p)
    (hq : crIsMono q) : crIsMono (p * q) := by
  obtain ⟨E, rfl⟩ := hp
  obtain ⟨F, rfl⟩ := hq
  exact ⟨E + F, by rw [monomial_mul, one_mul]⟩

theorem crIsMono_one {R : Type} [CommRing R] : crIsMono (1 : MvPolynomial (Letter T r n) R) := by
  refine ⟨0, ?_⟩
  rw [← C_1, C_apply]

theorem crIsMono_pow {R : Type} [CommRing R] {p : MvPolynomial (Letter T r n) R} (hp : crIsMono p)
    (e : ℕ) : crIsMono (p ^ e) := by
  induction e with
  | zero =>
    rw [pow_zero]
    exact crIsMono_one
  | succ e ih =>
    rw [pow_succ]
    exact crIsMono_mul ih hp

theorem crIsMono_prod {R : Type} [CommRing R] {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Letter T r n) R) (h : ∀ i ∈ s, crIsMono (f i)) : crIsMono (∏ i ∈ s, f i) := by
  exact Finset.prod_induction f crIsMono (fun _ _ ha hb => crIsMono_mul ha hb) crIsMono_one h

theorem crRho_P (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (hβ : Function.Injective β) : crIsMono (crRho R β (crP r n R β a)) := by
  unfold crP
  rw [map_prod]
  refine crIsMono_prod _ _ fun σ _ => ?_
  rw [map_prod]
  refine crIsMono_prod _ _ fun kk _ => ?_
  rw [map_pow]
  refine crIsMono_pow ?_ _
  rw [AlgHom.map_det, crRho_minor R β hβ σ kk, Matrix.det_diagonal]
  exact crIsMono_prod _ _ fun q _ => ⟨Finsupp.single _ 1, rfl⟩

theorem crP_coeff_diag (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (hβ : Function.Injective β) (ha : Dom r a) : (crP r n k β a).coeff (diagExp r n β a) = 1 := by
  obtain ⟨E, hE⟩ := crRho_P k β a hβ
  have hEdiag : ∀ ℓ ∈ E.support, ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩ := by
    have h1 := crRho_supported k β (crP r n k β a)
    rw [hE, mem_supported, vars_monomial one_ne_zero] at h1
    intro ℓ hℓ
    exact h1 hℓ
  have hcoeffE : (crP r n k β a).coeff E = 1 := by
    rw [← crRho_coeff k β _ E hEdiag, hE, coeff_monomial, if_pos rfl]
  have hEeq : E = diagExp r n β a := by
    ext ℓ
    obtain ⟨σ, i, b⟩ := ℓ
    by_cases hb : b = β ⟨σ, i⟩
    · subst hb
      have hd : diagExp r n β a (crDl β ⟨σ, i⟩) = a σ i := crDiagExp_dl β a ⟨σ, i⟩
      have hw := crP_isWeightedHomogeneous_crW k β a ha σ i
        (show (crP r n k β a).coeff E ≠ 0 by rw [hcoeffE]; exact one_ne_zero)
      rw [crW_weight] at hw
      change E ⟨σ, i, β ⟨σ, i⟩⟩ = diagExp r n β a (crDl β ⟨σ, i⟩)
      rw [hd, ← hw, Finset.sum_eq_single (β ⟨σ, i⟩)]
      · intro b' _ hb'
        by_contra hne
        exact hb' (hEdiag _ (Finsupp.mem_support_iff.mpr hne))
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [crDiagExp_off]
      · by_contra hne
        exact hb (hEdiag _ (Finsupp.mem_support_iff.mpr hne))
      · intro p hp
        apply hb
        obtain ⟨σ', i'⟩ := p
        obtain ⟨h1, h2⟩ := Sigma.mk.inj hp
        subst h1
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq h2)
        rfl
  rw [← hEeq]
  exact hcoeffE

end Part4

variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)

theorem Pmin_mem (O : Subring k) (cc : T → T) (isX : T → Prop) (hcc : ∀ τ, isX τ → cc τ ≠ τ)
    (hβ : Function.Injective β) (ha : Dom r a) :
    MvPolynomial.map (Int.castRingHom k) (Pmin r n β a) ∈ HaO r n k O cc isX a := by
  unfold HaO HHa
  refine ⟨?_, fun m => ?_⟩
  · rw [crP_map]
    exact ⟨crP_mem_harmK k β a cc isX hcc hβ, crP_rowInv k β a, crP_rowDeg k β a ha⟩
  · rw [coeff_map, eq_intCast]
    exact intCast_mem O _

theorem Pmin_coeff_diag (hβ : Function.Injective β) (ha : Dom r a) :
    (MvPolynomial.map (Int.castRingHom k) (Pmin r n β a)).coeff (diagExp r n β a) = 1 := by
  rw [crP_map]
  exact crP_coeff_diag k β a hβ ha

theorem Pmin_good (m : Letter T r n →₀ ℕ) (hm : m ∈ (MvPolynomial.map (Int.castRingHom k) (Pmin r n β a)).support)
    (ℓ : Letter T r n) (hℓ : m ℓ ≠ 0) : ℓ ∈ GoodL r n β := by
  rw [crP_map] at hm
  have h1 := crP_mem_supported k β a
  rw [mem_supported] at h1
  exact h1 ((mem_vars ℓ).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hℓ⟩)

theorem Pmin_degree (ha : Dom r a) (m : Letter T r n →₀ ℕ)
    (hm : m ∈ (MvPolynomial.map (Int.castRingHom k) (Pmin r n β a)).support) :
    m.degree = ∑ σ : T, ∑ i : Fin (r σ), a σ i := by
  rw [crP_map] at hm
  have hD : ∀ τ (kk : Fin (r τ)), IsWeightedHomogeneous (fun _ : Letter T r n => (1 : ℕ))
      (crMinor r n k β τ kk).det ((kk : ℕ) + 1) := by
    intro τ kk
    apply crMinor_hom
    intro π
    simp
  have h : Finsupp.weight (fun _ : Letter T r n => (1 : ℕ)) m =
      ∑ τ, ∑ kk : Fin (r τ), crExp r a τ kk • ((kk : ℕ) + 1) :=
    crP_isWeightedHomogeneous k β a _ _ hD (MvPolynomial.mem_support_iff.mp hm)
  have hsum : (∑ τ, ∑ kk : Fin (r τ), crExp r a τ kk • ((kk : ℕ) + 1)) =
      ∑ σ : T, ∑ i : Fin (r σ), a σ i := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hx : ∀ i : Fin (r τ), a τ i =
        ∑ kk : Fin (r τ), if (i : ℕ) < (kk : ℕ) + 1 then crExp r a τ kk else 0 :=
      fun i => (crExpSum a ha τ i).symm
    rw [Finset.sum_congr rfl fun i _ => hx i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun kk _ => ?_
    have hcard : (Finset.univ.filter fun i : Fin (r τ) => (i : ℕ) < (kk : ℕ) + 1).card = (kk : ℕ) + 1 := by
      rw [show (Finset.univ.filter fun i : Fin (r τ) => (i : ℕ) < (kk : ℕ) + 1) = Finset.Iic kk by
        ext i
        rw [Finset.mem_filter, Finset.mem_Iic]
        constructor
        · intro h
          exact Fin.le_def.mpr (by have := h.2; omega)
        · intro h
          exact ⟨Finset.mem_univ _, by have := Fin.le_def.mp h; omega⟩]
      exact Fin.card_Iic kk
    rw [← Finset.sum_filter, Finset.sum_const, hcard, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [← hsum, ← h]
  rw [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum]
  simp

theorem diagExp_degree : (diagExp r n β a).degree = ∑ σ : T, ∑ i : Fin (r σ), a σ i := by
  have h1 : (diagExp r n β a).degree =
      ∑ p : (Σ σ : T, Fin (r σ)), (Finsupp.single (crDl β p) (a p.1 p.2)).degree := by
    unfold diagExp
    exact map_sum Finsupp.degree _ _
  rw [h1, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finsupp.degree_apply]
  by_cases hc : a σ i = 0
  · simp [hc]
  · rw [Finsupp.support_single_ne_zero _ hc, Finset.sum_singleton, Finsupp.single_eq_same]

end Formalism.L2.Pj.Crude
