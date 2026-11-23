import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

noncomputable section

open Matrix NumberField
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisSec

open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global

section Alg

variable {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι]

def tri (a b : K) : Matrix (ι ⊕ ι) (ι ⊕ ι) K := Matrix.fromBlocks (Matrix.of fun _ _ => a) (Matrix.of fun _ _ => b) 0 1

theorem sum_one {i : ι} (hi : ∀ x, x = i) (f : ι → K) : ∑ x, f x = f i :=
  Fintype.sum_eq_single i fun x h => absurd (hi x) h

theorem mul2 {i : ι} (hi : ∀ x, x = i) (M N : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (r c : ι ⊕ ι) :
    (M * N) r c = M r (Sum.inl i) * N (Sum.inl i) c + M r (Sum.inr i) * N (Sum.inr i) c := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type, sum_one hi, sum_one hi]

theorem ext2 {i : ι} (hi : ∀ x, x = i) {M N : Matrix (ι ⊕ ι) (ι ⊕ ι) K}
    (h11 : M (.inl i) (.inl i) = N (.inl i) (.inl i)) (h12 : M (.inl i) (.inr i) = N (.inl i) (.inr i))
    (h21 : M (.inr i) (.inl i) = N (.inr i) (.inl i)) (h22 : M (.inr i) (.inr i) = N (.inr i) (.inr i)) : M = N := by
  ext r c
  rcases r with r | r <;> rcases c with c | c <;> rw [hi r, hi c] <;> assumption

@[simp] theorem tri_inl_inl (a b : K) (i j : ι) : (tri a b : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl j) = a := rfl
@[simp] theorem cechTripleProjFirstSecond (a b : K) (i j : ι) : (tri a b : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inr j) = b := rfl
@[simp] theorem triangular_lower_left (a b : K) (i j : ι) : (tri a b : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inl j) = 0 := rfl
@[simp] theorem triangular_lower_right_diag (a b : K) (i : ι) : (tri a b : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inr i) = 1 := by
  simp [tri]

theorem tri_mul {i : ι} (hi : ∀ x, x = i) (a b c d : K) :
    (tri a b * tri c d : Matrix (ι ⊕ ι) (ι ⊕ ι) K) = tri (a * c) (a * d + b) :=
  ext2 hi (by simp [mul2 hi]) (by simp [mul2 hi]) (by simp [mul2 hi]) (by simp [mul2 hi])

theorem tri_one {i : ι} (hi : ∀ x, x = i) : (tri 1 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) K) = 1 :=
  ext2 hi (by simp) (by simp) (by simp) (by simp)

theorem tri_det {i : ι} (hi : ∀ x, x = i) (a b : K) : (tri a b : Matrix (ι ⊕ ι) (ι ⊕ ι) K).det = a := by
  haveI : Unique ι := ⟨⟨i⟩, fun x => hi x⟩
  rw [tri, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.det_one, mul_one]
  rfl

def triU {i : ι} (hi : ∀ x, x = i) (a b a' b' : K) (h1 : a * a' = 1) (h2 : a * b' + b = 0) : GL (ι ⊕ ι) K where
  val := tri a b
  inv := tri a' b'
  val_inv := by rw [tri_mul hi, h1, h2, tri_one hi]
  inv_val := by
    have h3 : a' * b + b' = 0 := by linear_combination a' * h2 - b' * h1
    rw [tri_mul hi, mul_comm a' a, h1, h3, tri_one hi]

theorem tri_map {K' : Type} [CommRing K'] {i : ι} (hi : ∀ x, x = i) (f : K →+* K') (a b : K) :
    (tri a b : Matrix (ι ⊕ ι) (ι ⊕ ι) K).map f = tri (f a) (f b) :=
  ext2 hi (by simp) (by simp) (by simp) (by simp)

theorem tri_cont {T : Type} [TopologicalSpace T] [TopologicalSpace K] {f g : T → K} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun p => (tri (f p) (g p) : Matrix (ι ⊕ ι) (ι ⊕ ι) K) := by
  refine continuous_matrix fun a b => ?_
  rcases a with a | a <;> rcases b with b | b
  · exact hf
  · exact hg
  · exact continuous_const
  · exact continuous_const

theorem dg_conj (v : Kˣ) (g : GL (ι ⊕ ι) K) (a b : ι ⊕ ι) :
    (((dg ι v)⁻¹ * g * dg ι v : GL (ι ⊕ ι) K) : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b =
      Sum.elim (fun _ => 1) (fun _ => ((v⁻¹ : Kˣ) : K)) a * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b *
        Sum.elim (fun _ => 1) (fun _ => (v : K)) b := by
  rw [Units.val_mul, Units.val_mul]
  show (Matrix.diagonal (Sum.elim (fun _ => (1 : K)) fun _ => ((v⁻¹ : Kˣ) : K)) *
    (g : Matrix (ι ⊕ ι) (ι ⊕ ι) K) * Matrix.diagonal (Sum.elim (fun _ => (1 : K)) fun _ => (v : K)) :
      Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dg_tri {i : ι} (hi : ∀ x, x = i) (v : Kˣ) (g : GL (ι ⊕ ι) K) (a b : K)
    (h : (g : Matrix (ι ⊕ ι) (ι ⊕ ι) K) = tri a b) :
    (((dg ι v)⁻¹ * g * dg ι v : GL (ι ⊕ ι) K) : Matrix (ι ⊕ ι) (ι ⊕ ι) K) = tri a (b * v) :=
  ext2 hi (by simp [dg_conj, h]) (by simp [dg_conj, h]) (by simp [dg_conj, h]) (by simp [dg_conj, h])

theorem scal {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {e t b t' q q' d d' : K} (he : e * e = 1) (h1 : t * q = 1)
    (h2 : t' * q' = 1) (h3 : t * σ t' = 1) (h4 : e * t' * σ b + b * σ t' = 0) (h5 : d * d' = 1)
    (h6 : σ d = -(e * d)) :
    σ (t * q') = t * q' ∧ σ (t' * q) = t' * q ∧ σ (b * q' * d') = b * q' * d' := by
  have a1 : q = σ t' := by linear_combination (σ t') * h1 - q * h3
  have a2 : σ t * t' = 1 := by
    have := congrArg σ h3
    rwa [map_mul, hσ, map_one] at this
  have a3 : q' = σ t := by linear_combination (σ t) * h2 - q' * a2
  have a4 : σ q' = t := by rw [a3, hσ]
  have a5 : σ q = t' := by rw [a1, hσ]
  have h7 : -(e * d) * σ d' = 1 := by
    rw [← h6, ← map_mul, h5, map_one]
  have a6 : σ d' = -(e * d') := by
    linear_combination (-(e * d')) * h7 - (σ d') * he - (σ d') * e * e * h5
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, a4, a3]; ring
  · rw [map_mul, a5, a1]; ring
  · rw [map_mul, map_mul, a4, a6]
    linear_combination (-d') * (q' * t * h4 - e * σ b * t * h2 - b * q' * h3)

end Alg

section Unitary

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem unit_tri {i : ι} (hi : ∀ x, x = i) (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hM : M ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ)
    (h21 : M (.inr i) (.inl i) = 0) :
    star (M (.inl i) (.inl i)) * M (.inl i) (.inl i) = 1 ∧ M (.inl i) (.inr i) = 0 ∧
      star (M (.inr i) (.inr i)) * M (.inr i) (.inr i) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.1 hM
  have e11 := congrFun (congrFun h (.inl i)) (.inl i)
  have e12 := congrFun (congrFun h (.inl i)) (.inr i)
  have e22 := congrFun (congrFun h (.inr i)) (.inr i)
  rw [mul2 hi] at e11 e12 e22
  simp only [Matrix.star_apply, h21, star_zero, zero_mul, add_zero, Matrix.one_apply_eq, mul_zero, zero_add] at e11 e12 e22
  have e12' : M (.inl i) (.inr i) = 0 := by
    have hne : star (M (.inl i) (.inl i)) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at e11; exact zero_ne_one e11
    have : star (M (.inl i) (.inl i)) * M (.inl i) (.inr i) = 0 := by simpa using e12
    exact (mul_eq_zero.1 this).resolve_left hne
  rw [e12'] at e22
  exact ⟨e11, e12', by simpa using e22⟩

theorem tri_unitary {i : ι} (hi : ∀ x, x = i) (c : ℂ) (hc : star c * c = 1) :
    (tri c 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ := by
  have hc' : (starRingEnd ℂ) c * c = 1 := hc
  refine Matrix.mem_unitaryGroup_iff'.2 (ext2 hi ?_ ?_ ?_ ?_) <;> simp [mul2 hi, Matrix.star_apply, hc']

end Unitary

section Main

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {A : Ad E R} {ε : ℤˣ}

abbrev pm (p : A.uQ ε (Set.univ : Set ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) R := ((p.1.1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)

abbrev qm (p : A.uQ ε (Set.univ : Set ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  (((p.1.1 : GL (ι ⊕ ι) R)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)

theorem ent {i : ι} (hi : ∀ x, x = i) (p : A.uQ ε (Set.univ : Set ι)) :
    pm p (.inr i) (.inl i) = 0 ∧ qm p (.inr i) (.inl i) = 0 ∧
    pm p (.inl i) (.inl i) * qm p (.inl i) (.inl i) = 1 ∧ pm p (.inr i) (.inr i) * qm p (.inr i) (.inr i) = 1 ∧
    pm p (.inl i) (.inl i) * A.σ (pm p (.inr i) (.inr i)) = 1 ∧
    ((ε : ℤ) : R) * pm p (.inr i) (.inr i) * A.σ (pm p (.inl i) (.inr i)) +
      pm p (.inl i) (.inr i) * A.σ (pm p (.inr i) (.inr i)) = 0 := by
  have hs : p.1.1 ∈ stab R (Sum.inl '' (Set.univ : Set ι)) := Subgroup.mem_subgroupOf.1 p.2
  obtain ⟨e21, f21⟩ := hs (.inr i) (by simp) (.inl i) (by simp)
  have hpq : pm p * qm p = 1 := Units.mul_inv _
  have d1 := congrFun (congrFun hpq (.inl i)) (.inl i)
  have d2 := congrFun (congrFun hpq (.inr i)) (.inr i)
  rw [mul2 hi] at d1 d2
  have hu : (pm p)ᵀ * Ad.J R ε ι * (pm p).map A.σ = Ad.J R ε ι := p.1.2
  have u1 := congrFun (congrFun hu (.inl i)) (.inr i)
  have u2 := congrFun (congrFun hu (.inr i)) (.inr i)
  rw [mul2 hi] at u1 u2
  simp only [mul2 hi, Matrix.transpose_apply, Matrix.map_apply, Ad.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply_eq, Matrix.smul_apply,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at u1 u2
  refine ⟨e21, f21, ?_, ?_, ?_, ?_⟩
  · simpa [f21] using d1
  · simpa [e21] using d2
  · simpa [e21] using u1
  · linear_combination u2

variable [TopologicalSpace R] {ν : 𝔸[F] →+* R} {r : R → 𝔸[F]} {δ : Eˣ} {α : IdeleGroup F} {ω : HeckeCharacter F}

abbrev dU (A : Ad E R) (δ : Eˣ) : Rˣ := Units.map A.i.toMonoidHom δ

abbrev xs (p : A.uQ ε (Set.univ : Set ι)) (i : ι) : R := pm p (.inl i) (.inl i) * qm p (.inr i) (.inr i)

abbrev xs' (p : A.uQ ε (Set.univ : Set ι)) (i : ι) : R := pm p (.inr i) (.inr i) * qm p (.inl i) (.inl i)

abbrev ys (p : A.uQ ε (Set.univ : Set ι)) (i : ι) (δ : Eˣ) : R :=
  pm p (.inl i) (.inr i) * qm p (.inr i) (.inr i) * ((dU A δ)⁻¹ : Rˣ)

abbrev ys' (p : A.uQ ε (Set.univ : Set ι)) (i : ι) (δ : Eˣ) : R := -(xs' p i * ys p i δ)

theorem eps_sq (ε : ℤˣ) : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rcases Int.units_eq_one_or ε with h | h <;> simp [h]

theorem fixes (hg : A.Good) (hb : Base A ε ν r δ α ω) {i : ι} (hi : ∀ x, x = i) (p : A.uQ ε (Set.univ : Set ι)) :
    ν (r (xs p i)) = xs p i ∧ ν (r (xs' p i)) = xs' p i ∧ ν (r (ys p i δ)) = ys p i δ ∧
      ν (r (ys' p i δ)) = ys' p i δ := by
  obtain ⟨e21, f21, d1, d2, u1, u2⟩ := ent hi p
  have hd : (A.i δ) * ((dU A δ)⁻¹ : Rˣ) = 1 := Units.mul_inv (dU A δ)
  obtain ⟨s1, s2, s3⟩ := scal hg.σσ (eps_sq ε) d1 d2 u1 u2 hd hb.δσ
  refine ⟨hb.rfix _ s1, hb.rfix _ s2, hb.rfix _ s3, hb.rfix _ ?_⟩
  rw [map_neg, map_mul, s2, s3]

theorem exists_cov (hg : A.Good) (hb : Base A ε ν r δ α ω) {i : ι} (hi : ∀ x, x = i) (p : A.uQ ε (Set.univ : Set ι)) :
    ∃ c : cover A ν ι, ((c.1.1 : Rˣ) : R) = pm p (.inr i) (.inr i) ∧ (((c.1.1)⁻¹ : Rˣ) : R) = qm p (.inr i) (.inr i) ∧
      ((c.1.2 : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = tri (r (xs p i)) (r (ys p i δ)) ∧
      (((c.1.2)⁻¹ : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = tri (r (xs' p i)) (r (ys' p i δ)) := by
  obtain ⟨e21, f21, d1, d2, u1, u2⟩ := ent hi p
  obtain ⟨n1, n2, n3, n4⟩ := fixes hg hb hi p
  have hxx : xs p i * xs' p i = 1 := by
    simp only [xs, xs']; linear_combination (pm p (.inr i) (.inr i) * qm p (.inr i) (.inr i)) * d1 + d2
  have h1 : r (xs p i) * r (xs' p i) = 1 := hb.inj (by rw [map_mul, n1, n2, hxx, map_one])
  have h2 : r (xs p i) * r (ys' p i δ) + r (ys p i δ) = 0 :=
    hb.inj (by
      rw [map_add, map_mul, n1, n3, n4, map_zero]
      simp only [ys']
      linear_combination (-(ys p i δ)) * hxx)
  let a : Rˣ := ⟨pm p (.inr i) (.inr i), qm p (.inr i) (.inr i), d2, by rw [mul_comm]; exact d2⟩
  let h : GL (ι ⊕ ι) 𝔸[F] := triU hi _ _ _ _ h1 h2
  refine ⟨⟨(a, h), ?_⟩, rfl, rfl, rfl, rfl⟩
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  have hdet : ν (Matrix.GeneralLinearGroup.det h : 𝔸[F]ˣ) = xs p i := by
    have : ((Matrix.GeneralLinearGroup.det h : 𝔸[F]ˣ) : 𝔸[F]) = r (xs p i) := tri_det hi _ _
    rw [this, n1]
  show pm p (.inr i) (.inr i) * A.σ (pm p (.inr i) (.inr i)) * ν (Matrix.GeneralLinearGroup.det h : 𝔸[F]ˣ) = 1
  rw [hdet]
  simp only [xs]
  linear_combination (A.σ (pm p (.inr i) (.inr i))) * (pm p (.inl i) (.inl i)) * d2 + u1

theorem j_eq {j : cover A ν ι →* A.U ε ι} (hj : IsJ δ j) {i : ι} (hi : ∀ x, x = i) (c : cover A ν ι) (g : A.U ε ι)
    (x y : 𝔸[F]) (hc : ((c.1.1 : Rˣ) : R) = (g.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (.inr i) (.inr i))
    (hh : ((c.1.2 : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = tri x y)
    (h11 : (g.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (.inr i) (.inr i) * ν x = (g.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (.inl i) (.inl i))
    (h12 : (g.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (.inr i) (.inr i) * (ν y * A.i δ) =
      (g.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (.inl i) (.inr i))
    (h21 : (g.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (.inr i) (.inl i) = 0) : j c = g := by
  refine Subtype.ext (Units.ext ?_)
  have hm : ((Matrix.GeneralLinearGroup.map ν c.1.2 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = tri (ν x) (ν y) := by
    show ((c.1.2 : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν = _
    rw [hh, tri_map hi]
  have hdi : (((dU A δ)⁻¹ : Rˣ) : R) * A.i δ = 1 := Units.inv_mul (dU A δ)
  rw [hj c]
  refine ext2 hi ?_ ?_ ?_ ?_ <;> rw [Matrix.smul_apply, dg_conj, hm, hc]
  · simpa using h11
  · simpa using h12
  · simpa using h21.symm
  · have hdi' : A.i ((δ : E)⁻¹) * A.i δ = 1 := by
      rw [← map_mul, inv_mul_cancel₀ δ.ne_zero, map_one]
    simp [hdi']

theorem j_sec (hg : A.Good) (hb : Base A ε ν r δ α ω) {i : ι} (hi : ∀ x, x = i) {j : cover A ν ι →* A.U ε ι}
    (hj : IsJ δ j) (p : A.uQ ε (Set.univ : Set ι)) (c : cover A ν ι)
    (h1 : ((c.1.1 : Rˣ) : R) = pm p (.inr i) (.inr i))
    (h3 : ((c.1.2 : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = tri (r (xs p i)) (r (ys p i δ))) :
    j c = p.1 := by
  obtain ⟨e21, f21, d1, d2, u1, u2⟩ := ent hi p
  obtain ⟨n1, n2, n3, n4⟩ := fixes hg hb hi p
  have hd : (A.i δ) * ((dU A δ)⁻¹ : Rˣ) = 1 := Units.mul_inv (dU A δ)
  refine j_eq hj hi c p.1 _ _ h1 h3 ?_ ?_ e21
  · show pm p (.inr i) (.inr i) * ν (r (xs p i)) = pm p (.inl i) (.inl i)
    rw [n1]
    simp only [xs]
    linear_combination (pm p (.inl i) (.inl i)) * d2
  · show pm p (.inr i) (.inr i) * (ν (r (ys p i δ)) * A.i δ) = pm p (.inl i) (.inr i)
    rw [n3]
    simp only [ys]
    linear_combination (pm p (.inl i) (.inr i)) * d2 +
      (pm p (.inr i) (.inr i) * pm p (.inl i) (.inr i) * qm p (.inr i) (.inr i)) * hd

theorem tri_mem {K : Type} [CommRing K] (S : Subring K) {a b : K} (ha : a ∈ S) (hb : b ∈ S) (x y : ι ⊕ ι) :
    (tri a b : Matrix (ι ⊕ ι) (ι ⊕ ι) K) x y ∈ S := by
  rcases x with x | x <;> rcases y with y | y
  · exact ha
  · exact hb
  · exact S.zero_mem
  · by_cases h : x = y
    · subst h
      rw [triangular_lower_right_diag]
      exact S.one_mem
    · show (1 : Matrix ι ι K) x y ∈ S
      rw [Matrix.one_apply_ne h]
      exact S.zero_mem

theorem tri_mem_k {i : ι} (hi : ∀ x, x = i) (κ : GL (ι ⊕ ι) 𝔸[F]) (a b a' b' : 𝔸[F])
    (hv : (κ : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = tri a b)
    (hv' : ((κ⁻¹ : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = tri a' b')
    (ha : a ∈ intAd F) (hb : b ∈ intAd F) (ha' : a' ∈ intAd F) (hb' : b' ∈ intAd F)
    (hu : ∀ v, star ((adStd F).φ v a) * (adStd F).φ v a = 1 ∧ (adStd F).φ v b = 0) :
    κ ∈ (adStd F).kGL (ι ⊕ ι) := by
  refine ⟨fun x y => ⟨?_, ?_⟩, fun v => ?_⟩
  · rw [hv]; exact tri_mem _ ha hb x y
  · rw [hv']; exact tri_mem _ ha' hb' x y
  · rw [hv, tri_map hi, (hu v).2]
    exact tri_unitary hi _ (hu v).1

theorem sec_mem (hg : A.Good) (hb : Base A ε ν r δ α ω) {i : ι} (hi : ∀ x, x = i) {j : cover A ν ι →* A.U ε ι}
    (p : A.uQ ε (Set.univ : Set ι)) (hp : (p : A.U ε ι) ∈ A.uK ε ι) (c : cover A ν ι)
    (h3 : ((c.1.2 : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = tri (r (xs p i)) (r (ys p i δ)))
    (h4 : (((c.1.2)⁻¹ : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = tri (r (xs' p i)) (r (ys' p i δ)))
    (hjc : j c = p.1) : c ∈ cK α j := by
  obtain ⟨e21, f21, d1, d2, u1, u2⟩ := ent hi p
  obtain ⟨n1, n2, n3, n4⟩ := fixes hg hb hi p
  have hk : p.1.1 ∈ A.kGL (ι ⊕ ι) := Subgroup.mem_subgroupOf.1 hp
  obtain ⟨hO, hU⟩ := hk
  obtain ⟨u, hu, huO, huO', -⟩ := hb.δα
  have hw : (((dU A δ)⁻¹ : Rˣ) : R) * ν α = ((u⁻¹ : Rˣ) : R) := by
    have h1 : (((dU A δ)⁻¹ : Rˣ) : R) * A.i δ = 1 := Units.inv_mul (dU A δ)
    have h2 : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := Units.mul_inv u
    rw [hu] at h1
    linear_combination ((u⁻¹ : Rˣ) : R) * h1 - ((((dU A δ)⁻¹ : Rˣ) : R) * ν α) * h2
  have hy : ys p i δ * ν α = pm p (.inl i) (.inr i) * (qm p (.inr i) (.inr i) * ((u⁻¹ : Rˣ) : R)) := by
    simp only [ys]
    linear_combination (pm p (.inl i) (.inr i) * qm p (.inr i) (.inr i)) * hw
  have hyO : ys p i δ * ν α ∈ A.O := by
    rw [hy]
    exact A.O.mul_mem (hO _ _).1 (A.O.mul_mem (hO _ _).2 huO')
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show j c ∈ A.uK ε ι
    rw [hjc]
    exact hp
  · refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨(dg ι (α : 𝔸[F]ˣ))⁻¹ * c.1.2 * dg ι (α : 𝔸[F]ˣ), ?_, ?_⟩)
    swap
    · show dg ι (α : 𝔸[F]ˣ) * ((dg ι (α : 𝔸[F]ˣ))⁻¹ * c.1.2 * dg ι (α : 𝔸[F]ˣ)) * (dg ι (α : 𝔸[F]ˣ))⁻¹ = c.1.2
      group
    · have hinv : ((dg ι (α : 𝔸[F]ˣ))⁻¹ * c.1.2 * dg ι (α : 𝔸[F]ˣ))⁻¹ =
          (dg ι (α : 𝔸[F]ˣ))⁻¹ * (c.1.2)⁻¹ * dg ι (α : 𝔸[F]ˣ) := by group
      refine tri_mem_k hi _ (r (xs p i)) (r (ys p i δ) * (α : 𝔸[F]ˣ)) (r (xs' p i)) (r (ys' p i δ) * (α : 𝔸[F]ˣ))
        (dg_tri hi _ _ _ _ h3) (by rw [hinv]; exact dg_tri hi _ _ _ _ h4) ?_ ?_ ?_ ?_ ?_
      · refine (hb.int _).1 ?_
        rw [n1]
        exact A.O.mul_mem (hO _ _).1 (hO _ _).2
      · refine (hb.int _).1 ?_
        rw [map_mul, n3]
        exact hyO
      · refine (hb.int _).1 ?_
        rw [n2]
        exact A.O.mul_mem (hO _ _).1 (hO _ _).2
      · refine (hb.int _).1 ?_
        rw [map_mul, n4]
        have : ys' p i δ * ν α = -(xs' p i * (ys p i δ * ν α)) := by simp only [ys']; ring
        rw [this]
        exact A.O.neg_mem (A.O.mul_mem (A.O.mul_mem (hO _ _).1 (hO _ _).2) hyO)
      · intro v
        obtain ⟨w, hw'⟩ := hb.inf' v
        obtain ⟨t1, t2, t3⟩ := unit_tri hi ((pm p).map (A.φ w)) (hU w) (by simp [e21])
        simp only [Matrix.map_apply] at t1 t2 t3
        have hq : A.φ w (pm p (.inr i) (.inr i)) * A.φ w (qm p (.inr i) (.inr i)) = 1 := by
          rw [← map_mul, d2, map_one]
        have hqs : star (A.φ w (pm p (.inr i) (.inr i))) * star (A.φ w (qm p (.inr i) (.inr i))) = 1 := by
          rw [← star_mul', hq, star_one]
        have hq2 : star (A.φ w (qm p (.inr i) (.inr i))) * A.φ w (qm p (.inr i) (.inr i)) = 1 := by
          linear_combination (-(star (A.φ w (qm p (.inr i) (.inr i))) * A.φ w (qm p (.inr i) (.inr i)))) * t3 +
            (A.φ w (qm p (.inr i) (.inr i)) * A.φ w (pm p (.inr i) (.inr i))) * hqs + hq
        refine ⟨?_, ?_⟩
        · rw [← hw', n1, map_mul, star_mul']
          linear_combination (star (A.φ w (qm p (.inr i) (.inr i))) * A.φ w (qm p (.inr i) (.inr i))) * t1 + hq2
        · rw [← hw', map_mul, n3, hy, map_mul, t2, zero_mul]

theorem cont_pm (a b : ι ⊕ ι) : Continuous fun p : A.uQ ε (Set.univ : Set ι) => pm p a b :=
  (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem a b

theorem cont_qm (a b : ι ⊕ ι) : Continuous fun p : A.uQ ε (Set.univ : Set ι) => qm p a b :=
  (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem a b

end Main

theorem jSec : JSec := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hg hb hi hj
  choose s h1 h2 h3 h4 using fun p => exists_cov (ι := ι) (ε := ε) hg hb hi p
  have hjs : ∀ p, j (s p) = p := fun p => j_sec hg hb hi hj p (s p) (h1 p) (h3 p)
  refine ⟨s, ?_, hjs, fun p hp => sec_mem hg hb hi p hp (s p) (h3 p) (h4 p) (hjs p)⟩
  have cx : Continuous fun p : A.uQ ε (Set.univ : Set ι) => xs p i := (cont_pm _ _).mul (cont_qm _ _)
  have cx' : Continuous fun p : A.uQ ε (Set.univ : Set ι) => xs' p i := (cont_pm _ _).mul (cont_qm _ _)
  have cy : Continuous fun p : A.uQ ε (Set.univ : Set ι) => ys p i δ :=
    ((cont_pm _ _).mul (cont_qm _ _)).mul continuous_const
  have cy' : Continuous fun p : A.uQ ε (Set.univ : Set ι) => ys' p i δ := (cx'.mul cy).neg
  refine continuous_induced_rng.2 ?_
  show Continuous fun p => ((s p).1.1, (s p).1.2)
  refine Continuous.prodMk (Units.continuous_iff.2 ⟨?_, ?_⟩) (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact (cont_pm _ _).congr fun p => (h1 p).symm
  · exact (cont_qm _ _).congr fun p => (h2 p).symm
  · exact (tri_cont (hb.rcont.comp cx) (hb.rcont.comp cy)).congr fun p => (h3 p).symm
  · exact (tri_cont (hb.rcont.comp cx') (hb.rcont.comp cy')).congr fun p => (h4 p).symm

theorem jSec_of_top : JTop → JSec := fun _ => jSec

end GlobalTheory.CompanionTheory.EisSec
