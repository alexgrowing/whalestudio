import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisJ

section Ring

variable {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_entry (d : Sˣ) (g : GL (ι ⊕ ι) S) (r c : ι ⊕ ι) :
    (((dg ι d)⁻¹ * g * dg ι d : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c =
      Sum.elim (fun _ => (1 : S)) (fun _ => ((d⁻¹ : Sˣ) : S)) r * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c *
        Sum.elim (fun _ => (1 : S)) (fun _ => (d : S)) c := by
  have h1 : (((dg ι d)⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) =
      Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => ((d⁻¹ : Sˣ) : S)) := rfl
  have h2 : ((dg ι d : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) =
      Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => (d : S)) := rfl
  rw [Units.val_mul, Units.val_mul, h1, h2, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_stab_line {i : ι} (hi : ∀ x, x = i) (s : Set (ι ⊕ ι)) (hs : s = {Sum.inl i}) (g : GL (ι ⊕ ι) S) :
    g ∈ stab S s ↔ (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (Sum.inr i) (Sum.inl i) = 0 ∧
      ((g⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (Sum.inr i) (Sum.inl i) = 0 := by
  subst hs
  have e : g ∈ stab S ({Sum.inl i} : Set (ι ⊕ ι)) ↔ ∀ r ∉ ({Sum.inl i} : Set (ι ⊕ ι)), ∀ c ∈ ({Sum.inl i} : Set (ι ⊕ ι)),
      (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c = 0 ∧ ((g⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c = 0 := Iff.rfl
  rw [e]
  constructor
  · intro h
    exact h _ (by simp) _ rfl
  · rintro h r hr c hc
    obtain rfl : c = Sum.inl i := hc
    rcases r with y | y
    · exact absurd (by rw [hi y]; rfl) hr
    · rw [hi y]; exact h

theorem det_tri {i : ι} (hi : ∀ x, x = i) (h : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (h0 : h (Sum.inr i) (Sum.inl i) = 0) :
    h.det = h (Sum.inl i) (Sum.inl i) * h (Sum.inr i) (Sum.inr i) := by
  haveI : Unique ι := ⟨⟨i⟩, hi⟩
  have e : h = Matrix.fromBlocks h.toBlocks₁₁ h.toBlocks₁₂ 0 h.toBlocks₂₂ := by
    ext r c
    rcases r with y | y <;> rcases c with z | z
    · rfl
    · rfl
    · rw [hi y, hi z]; simpa using h0
    · rfl
  rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.det_unique]
  have hd : (default : ι) = i := hi _
  simp [hd, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem bdet_val {κ : Type} [Fintype κ] [DecidableEq κ] (s : Set κ) (c : κ) (hs : s = {c}) (g : GL κ S)
    (hu : IsUnit ((g : Matrix κ κ S) c c)) : ((bdet s g : Sˣ) : S) = (g : Matrix κ κ S) c c := by
  subst hs
  have e : ∀ (f : Fintype ↥({c} : Set κ)) (dq : DecidableEq ↥({c} : Set κ)),
      @Matrix.det _ dq f S _ ((g : Matrix κ κ S).submatrix (Subtype.val : ({c} : Set κ) → κ) Subtype.val) =
        (g : Matrix κ κ S) c c := by
    intro f dq
    exact Matrix.det_eq_elem_of_subsingleton _ (⟨c, rfl⟩ : ({c} : Set κ))
  unfold bdet
  split_ifs with h
  · exact h.unit_spec.trans (e _ _)
  · exact absurd (by rw [e]; exact hu) h

end Ring

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R]
  {A : Ad E R} {ν : 𝔸[F] →+* R} {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ℤˣ}

theorem j_entry {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (x : cover A ν ι) (r c : ι ⊕ ι) :
    (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) r c = (x.1.1 : R) *
      (Sum.elim (fun _ => (1 : R)) (fun _ => (((Units.map A.i.toMonoidHom δ)⁻¹ : Rˣ) : R)) r *
        ν ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) r c) *
        Sum.elim (fun _ => (1 : R)) (fun _ => ((Units.map A.i.toMonoidHom δ : Rˣ) : R)) c) := by
  rw [hJ x, Matrix.smul_apply, smul_eq_mul, conj_entry]
  rfl

theorem j_low {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (hν : Function.Injective ν) (x : cover A ν ι)
    (i : ι) : (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl i) = 0 ↔
      (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inr i) (Sum.inl i) = 0 := by
  rw [j_entry hJ x, Sum.elim_inr, Sum.elim_inl, mul_one, Units.mul_right_eq_zero, Units.mul_right_eq_zero,
    map_eq_zero_iff ν hν]

theorem image_univ {i : ι} (hi : ∀ x, x = i) : (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) = {Sum.inl i} := by
  ext y
  constructor
  · rintro ⟨z, -, rfl⟩
    rw [hi z]; rfl
  · intro h
    obtain rfl : y = Sum.inl i := h
    exact ⟨i, trivial, rfl⟩

theorem compl_inr {i : ι} (hi : ∀ x, x = i) : ({Sum.inr i}ᶜ : Set (ι ⊕ ι)) = {Sum.inl i} := by
  ext y
  rcases y with y | y
  · rw [hi y]; simp
  · rw [hi y]; simp

theorem comap_uQ {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (hν : Function.Injective ν) {i : ι}
    (hi : ∀ x, x = i) :
    (A.uQ ε Set.univ).comap j = (stab 𝔸[F] {Sum.inl i}).comap (prj A ν ι) := by
  ext x
  have e1 : x ∈ (A.uQ ε Set.univ).comap j ↔ (j x).1 ∈ stab R (Sum.inl '' (Set.univ : Set ι)) := Iff.rfl
  have e2 : x ∈ (stab 𝔸[F] {Sum.inl i}).comap (prj A ν ι) ↔ x.1.2 ∈ stab 𝔸[F] ({Sum.inl i} : Set (ι ⊕ ι)) := Iff.rfl
  have e3 : ((j x).1)⁻¹ = (j x⁻¹).1 := by rw [map_inv]; rfl
  have e4 : (x.1.2)⁻¹ = (x⁻¹).1.2 := rfl
  rw [e1, e2, mem_stab_line hi _ (image_univ hi), mem_stab_line hi _ rfl, e3, e4, j_low hJ hν, j_low hJ hν]

theorem blocks {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) {i : ι} (hi : ∀ x, x = i) (x : cover A ν ι)
    (hx : prj A ν ι x ∈ stab 𝔸[F] {Sum.inl i}) :
    bdet (Sum.inl '' (Set.univ : Set ι)) (j x).1 = x.1.1 * Units.map ν.toMonoidHom (bdet {Sum.inl i} (prj A ν ι x)) ∧
    Matrix.GeneralLinearGroup.det (prj A ν ι x) = bdet {Sum.inl i} (prj A ν ι x) * bdet {Sum.inr i} (prj A ν ι x) := by
  have hp : ((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = x.1.2 := rfl
  have h0 := ((mem_stab_line hi _ rfl _).1 hx).1
  have hdet := det_tri hi _ h0
  have hu : IsUnit (((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inl i) (Sum.inl i) *
      ((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inr i) (Sum.inr i)) := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (prj A ν ι x).isUnit
  have h1 := isUnit_of_mul_isUnit_left hu
  have h2 := isUnit_of_mul_isUnit_right hu
  have b1 := bdet_val _ _ rfl _ h1
  have b2 := bdet_val _ _ rfl _ h2
  have he := j_entry hJ x (Sum.inl i) (Sum.inl i)
  rw [Sum.elim_inl, Sum.elim_inl, one_mul, mul_one] at he
  have hju : IsUnit ((((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)) := by
    rw [he]
    exact x.1.1.isUnit.mul (h1.map ν)
  refine ⟨Units.ext ?_, Units.ext ?_⟩
  · rw [bdet_val _ (Sum.inl i) (image_univ hi) _ hju, he, Units.val_mul]
    congr 1
    exact (congrArg ν b1).symm
  · rw [Units.val_mul, b1, b2, ← hdet]
    rfl

theorem jPar : JPar := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j _ hB hi hJ
  exact ⟨by rw [compl_inr hi], comap_uQ hJ hB.inj hi, fun x hx => blocks hJ hi x hx⟩

end GlobalTheory.CompanionTheory.EisJ
