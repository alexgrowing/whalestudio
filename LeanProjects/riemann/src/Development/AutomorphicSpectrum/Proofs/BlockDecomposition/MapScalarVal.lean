import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.RgEisJRat

open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global

section Gen

variable {R S : Type} [CommRing R] [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem dg_val (x : Rˣ) : ((dg ι x : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => (x : R)) := rfl

theorem dg_inv_val (x : Rˣ) : (((dg ι x)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => ((x⁻¹ : Rˣ) : R)) := rfl

theorem dg_map (f : R →+* S) (x : Rˣ) :
    Matrix.GeneralLinearGroup.map f (dg ι x) = dg ι (Units.map f.toMonoidHom x) := by
  apply Units.ext
  ext a b
  rw [Matrix.GeneralLinearGroup.map_apply, dg_val, dg_val]
  by_cases h : a = b
  · subst h
    cases a <;> simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem dg_mem_stab (x : Rˣ) (i : ι) : dg ι x ∈ stab R ({Sum.inl i} : Set (ι ⊕ ι)) := by
  intro r hr c hc
  have hrc : r ≠ c := fun h => hr (h ▸ hc)
  rw [dg_inv_val, dg_val]
  exact ⟨Matrix.diagonal_apply_ne _ hrc, Matrix.diagonal_apply_ne _ hrc⟩

theorem conj_apply (t : Rˣ) (g : GL (ι ⊕ ι) R) (m n : ι ⊕ ι) :
    ((dg ι t * g * (dg ι t)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) m n =
      Sum.elim (fun _ => 1) (fun _ => (t : R)) m * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) m n *
        Sum.elim (fun _ => 1) (fun _ => ((t⁻¹ : Rˣ) : R)) n := by
  rw [Units.val_mul, Units.val_mul, dg_inv_val, dg_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem det_two (i : ι) (hi : ∀ x, x = i) (M : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    M.det = M (Sum.inl i) (Sum.inl i) * M (Sum.inr i) (Sum.inr i) -
      M (Sum.inl i) (Sum.inr i) * M (Sum.inr i) (Sum.inl i) := by
  let e : Fin 2 ≃ ι ⊕ ι :=
    { toFun := ![Sum.inl i, Sum.inr i]
      invFun := Sum.elim (fun _ => 0) (fun _ => 1)
      left_inv := fun a => by fin_cases a <;> rfl
      right_inv := fun a => by
        rcases a with a | a
        · rw [hi a]; rfl
        · rw [hi a]; rfl }
  rw [← Matrix.det_submatrix_equiv_self e M, Matrix.det_fin_two]
  rfl

theorem det_dg (i : ι) (hi : ∀ x, x = i) (x : Rˣ) :
    Matrix.GeneralLinearGroup.det (dg ι x) = x := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_two i hi, dg_val]
  simp

end Gen

section Sig

variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ring_id (p q r s P Q R' S' e t T : R) (he : e * e = 1)
    (h1 : r * e * P + p * R' = 0) (h2 : r * e * Q + p * S' = 1)
    (h3 : s * e * P + q * R' = e) (h4 : s * e * Q + q * S' = 0) :
    (p * s - q * r) * P = p ∧ (p * s - q * r) * (Q * (-(e * T))) = q * T ∧
      (p * s - q * r) * (-(e * t) * R') = t * r ∧
      (p * s - q * r) * (-(e * t) * S' * (-(e * T))) = t * s * T := by
  have c1 : (p * s - q * r) * P = p := by
    linear_combination p * (e * h3 - (s * P - 1) * he) - q * (e * h1 - r * P * he)
  have c2 : (p * s - q * r) * Q = -(e * q) := by
    linear_combination p * (e * h4 - s * Q * he) - q * (e * h2 - r * Q * he)
  have c3 : (p * s - q * r) * R' = -(e * r) := by
    linear_combination s * h1 - r * h3
  have c4 : (p * s - q * r) * S' = s := by
    linear_combination s * h2 - r * h4
  refine ⟨c1, ?_, ?_, ?_⟩
  · linear_combination (-(e * T)) * c2 + (q * T) * he
  · linear_combination (-(e * t)) * c3 + (t * r) * he
  · linear_combination (e * e * t * T) * c4 + (t * s * T) * he

theorem sig_entries (A : Ad E R) (ε : ℤˣ) (t : Rˣ) (ht : A.σ t = -(((ε : ℤ) : R) * t)) (i : ι)
    (hi : ∀ x, x = i) (g : GL (ι ⊕ ι) R) (hg : g ∈ A.uSub ε ι) (m n : ι ⊕ ι) :
    ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) *
      A.σ (((dg ι t * g * (dg ι t)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) m n) =
      ((dg ι t * g * (dg ι t)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) m n := by
  haveI : Unique ι := ⟨⟨i⟩, hi⟩
  have hd : (default : ι) = i := hi _
  have hg' : (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ = Ad.J R ε ι := hg
  rw [conj_apply, Matrix.GeneralLinearGroup.val_det_apply, det_two i hi]
  set M : Matrix (ι ⊕ ι) (ι ⊕ ι) R := (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) with hM
  set e : R := ((ε : ℤ) : R) with he'
  have he : e * e = 1 := by
    rw [he', ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  have entry : ∀ a b, (Mᵀ * Ad.J R ε ι * M.map A.σ) a b = Ad.J R ε ι a b := fun a b => by rw [hg']
  have h1 := entry (Sum.inl i) (Sum.inl i)
  have h2 := entry (Sum.inl i) (Sum.inr i)
  have h3 := entry (Sum.inr i) (Sum.inl i)
  have h4 := entry (Sum.inr i) (Sum.inr i)
  have hone : (1 : Matrix ι ι R) i default = 1 := by rw [hd, Matrix.one_apply_eq]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique, Ad.J, hd, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.zero_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_zero, mul_one,
    zero_add, add_zero, zero_mul, ← he', hone] at h1 h2 h3 h4
  set T : R := ((t⁻¹ : Rˣ) : R) with hTd
  have hT : (t : R) * T = 1 := Units.mul_inv t
  have hs : -(e * (t : R)) * A.σ T = 1 := by rw [← ht, ← map_mul, hT, map_one]
  have hσT : A.σ T = -(e * T) := by
    linear_combination (-(e * T)) * hs - A.σ T * he - (e * e * A.σ T) * hT
  obtain ⟨c1, c2, c3, c4⟩ := ring_id _ _ _ _ _ _ _ _ e (t : R) T he h1 h2 h3 h4
  rcases m with a | a <;> rcases n with b | b <;> rw [hi a, hi b] <;>
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, mul_one, map_mul, ht, hσT]
  · exact c1
  · exact c2
  · exact c3
  · exact c4

end Sig

section Main

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_cover (A : Ad E R) (ν : 𝔸[F] →+* R) (x : Rˣ × GL (ι ⊕ ι) 𝔸[F]) :
    x ∈ cover A ν ι ↔ (x.1 : R) * A.σ (x.1 : R) *
      ν ((Matrix.GeneralLinearGroup.det x.2 : 𝔸[F]ˣ) : 𝔸[F]) = 1 := by
  unfold cover
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp [MonoidHom.mul_apply]

theorem map_scalar_val (f : E →+* R) (e : Eˣ) :
    ((Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (ι ⊕ ι) e) : GL (ι ⊕ ι) R) :
      Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (f e) • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
  ext a b
  rw [Matrix.GeneralLinearGroup.map_apply]
  by_cases h : a = b
  · subst h; simp [Matrix.GeneralLinearGroup.scalar]
  · simp [Matrix.GeneralLinearGroup.scalar, h]

theorem map_map_rat (A : Ad E R) (ν : 𝔸[F] →+* R)
    (hrat : ∀ y : F, ν (algebraMap F 𝔸[F] y) = A.i (algebraMap F E y)) (h₀ : GL (ι ⊕ ι) F) :
    Matrix.GeneralLinearGroup.map ν (Matrix.GeneralLinearGroup.map (algebraMap F 𝔸[F]) h₀) =
      Matrix.GeneralLinearGroup.map A.i (Matrix.GeneralLinearGroup.map (algebraMap F E) h₀) := by
  apply Units.ext
  ext a b
  simp only [Matrix.GeneralLinearGroup.map_apply, hrat]

theorem sub_rat {ε : ℤˣ} (A : Ad E R) (ν : 𝔸[F] →+* R)
    (hrat : ∀ y : F, ν (algebraMap F 𝔸[F] y) = A.i (algebraMap F E y)) (δ : Eˣ)
    (j : cover A ν ι →* A.U ε ι) (hj : IsJ δ j) (x : cover A ν ι) (hx : x ∈ cΓ A ν ι) :
    j x ∈ A.uΓ ε ι := by
  obtain ⟨⟨e, he⟩, ⟨h₀, hh⟩⟩ := Subgroup.mem_subgroupOf.1 hx
  refine Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.scalar (ι ⊕ ι) e *
    ((dg ι δ)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap F E) h₀ * dg ι δ), ?_⟩
  apply Units.ext
  rw [hj x]
  have hh' : x.1.2 = Matrix.GeneralLinearGroup.map (algebraMap F 𝔸[F]) h₀ := hh.symm
  rw [hh', ← he, map_mul, Units.val_mul, map_scalar_val, Matrix.smul_mul, Matrix.one_mul, map_mul, map_mul, map_inv,
    dg_map, map_map_rat A ν hrat]
  rfl

theorem fix_aux (A : Ad E R) (d b c a : R) (hc : d * A.σ c = c) (hda : d * A.σ a = a) (hb : a * b = 1) :
    A.σ (b * c) = b * c := by
  have hσ : A.σ a * A.σ b = 1 := by rw [← map_mul, hb, map_one]
  rw [map_mul]
  linear_combination b * hc + A.σ c * b * d * hσ - A.σ c * A.σ b * b * hda - A.σ c * A.σ b * hb

theorem sup_rat [TopologicalSpace R] {ε : ℤˣ} (A : Ad E R) (ν : 𝔸[F] →+* R) (r : R → 𝔸[F]) (δ : Eˣ)
    (α : IdeleGroup F) (ω : HeckeCharacter F) (hinj : Function.Injective A.i)
    (hB : Base A ε ν r δ α ω) (i : ι) (hi : ∀ x, x = i)
    (j : cover A ν ι →* A.U ε ι) (hj : IsJ δ j) (g : A.U ε ι) (hg : g ∈ A.uΓ ε ι) :
    ∃ x ∈ cΓ A ν ι, j x = g := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.1 hg
  have hg₀' : Matrix.GeneralLinearGroup.map A.i g₀ = g.1 := hg₀
  set t : Rˣ := Units.map A.i.toMonoidHom δ with ht
  set n₀ : GL (ι ⊕ ι) E := dg ι δ * g₀ * (dg ι δ)⁻¹ with hn₀
  set G : GL (ι ⊕ ι) R := dg ι t * g.1 * (dg ι t)⁻¹ with hGd
  have hG : Matrix.GeneralLinearGroup.map A.i n₀ = G := by
    rw [hn₀, hGd, map_mul, map_mul, map_inv, dg_map, hg₀']
  have hGe : ∀ m n, A.i ((n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E) m n) = (G : Matrix (ι ⊕ ι) (ι ⊕ ι) R) m n := fun m n => by
    rw [← hG, Matrix.GeneralLinearGroup.map_apply]
  have hsig : ∀ m n, ((Matrix.GeneralLinearGroup.det g.1 : Rˣ) : R) * A.σ ((G : Matrix (ι ⊕ ι) (ι ⊕ ι) R) m n) =
      (G : Matrix (ι ⊕ ι) (ι ⊕ ι) R) m n := sig_entries A ε t hB.δσ i hi g.1 g.2
  have hdn : (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have hdd : A.i (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E).det = ((Matrix.GeneralLinearGroup.det g.1 : Rˣ) : R) := by
    have e1 : Matrix.GeneralLinearGroup.det G = Matrix.GeneralLinearGroup.det g.1 := by
      rw [hGd, map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det (dg ι t)), mul_inv_cancel_right]
    rw [← e1, ← hG, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  obtain ⟨m, n, hmn⟩ : ∃ m n, (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E) m n ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hdn
    rw [det_two i hi]
    simp [hc]
  set a₀ : E := (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E) m n with ha₀
  set d : R := ((Matrix.GeneralLinearGroup.det g.1 : Rˣ) : R) with hd
  have hda : d * A.σ (A.i a₀) = A.i a₀ := by rw [ha₀, hGe]; exact hsig m n
  have hab : A.i a₀ * A.i a₀⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hmn, map_one]
  have hy : ∀ m' n', ∃ y : F, algebraMap F E y = a₀⁻¹ * (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E) m' n' := by
    intro m' n'
    have hfix : A.σ (A.i (a₀⁻¹ * (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E) m' n')) =
        A.i (a₀⁻¹ * (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E) m' n') := by
      rw [map_mul]
      exact fix_aux A d _ _ _ (by rw [hGe]; exact hsig m' n') hda hab
    have h1 := hB.rfix _ hfix
    obtain ⟨y, hy⟩ := hB.rat' _ _ h1.symm
    refine ⟨y, hinj ?_⟩
    rw [← hB.rat y, ← hy, h1]
  choose y hy using hy
  let h₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) F := Matrix.of y
  have hdet : algebraMap F E h₀.det = a₀⁻¹ * a₀⁻¹ * (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E).det := by
    rw [det_two i hi h₀, det_two i hi (n₀ : Matrix (ι ⊕ ι) (ι ⊕ ι) E)]
    simp only [h₀, Matrix.of_apply, map_sub, map_mul, hy]
    ring
  have hdet0 : h₀.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdet
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hmn) (inv_ne_zero hmn)) hdn hdet.symm
  let hF : GL (ι ⊕ ι) F := Matrix.GeneralLinearGroup.mkOfDetNeZero h₀ hdet0
  let a : Rˣ := Units.map A.i.toMonoidHom (Units.mk0 a₀ hmn)
  let h : GL (ι ⊕ ι) 𝔸[F] := Matrix.GeneralLinearGroup.map (algebraMap F 𝔸[F]) hF
  have hνd : ν ((Matrix.GeneralLinearGroup.det h : 𝔸[F]ˣ) : 𝔸[F]) = A.i (algebraMap F E h₀.det) := by
    rw [← hB.rat, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det (algebraMap F 𝔸[F]) h₀]
    rfl
  have hc : (a, h) ∈ cover A ν ι := by
    rw [mem_cover, hνd, hdet]
    change A.i a₀ * A.σ (A.i a₀) * _ = 1
    rw [map_mul, map_mul, hdd]
    linear_combination (A.i a₀ * A.i a₀⁻¹ * A.i a₀⁻¹) * hda + (A.i a₀ * A.i a₀⁻¹ + 1) * hab
  refine ⟨⟨(a, h), hc⟩, Subgroup.mem_subgroupOf.2 ⟨⟨_, rfl⟩, ⟨hF, rfl⟩⟩, ?_⟩
  have hsm : (a : R) • ((Matrix.GeneralLinearGroup.map ν h : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
      (G : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    ext m' n'
    rw [Matrix.smul_apply, Matrix.GeneralLinearGroup.map_apply, smul_eq_mul, ← hGe]
    change A.i a₀ * ν (algebraMap F 𝔸[F] (y m' n')) = _
    rw [hB.rat, hy, map_mul, ← mul_assoc, hab, one_mul]
  apply Subtype.ext
  apply Units.ext
  rw [hj ⟨(a, h), hc⟩]
  change (a : R) • (((dg ι t)⁻¹ * Matrix.GeneralLinearGroup.map ν h * dg ι t : GL (ι ⊕ ι) R) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) R) = _
  rw [Units.val_mul, Units.val_mul, ← Matrix.smul_mul, ← Matrix.mul_smul, hsm, ← Units.val_mul, ← Units.val_mul, hGd]
  congr 1
  group

theorem second (A : Ad E R) (ν : 𝔸[F] →+* R) (i : ι) (hi : ∀ x, x = i) (g : GL (ι ⊕ ι) 𝔸[F])
    (hg : g ∈ (adStd F).ratGL (ι ⊕ ι)) :
    ∃ γ ∈ cΓ A ν ι, g * (prj A ν ι γ)⁻¹ ∈ stab 𝔸[F] ({Sum.inl i} : Set (ι ⊕ ι)) := by
  obtain ⟨g₀, rfl⟩ := hg
  let hF : GL (ι ⊕ ι) F := (dg ι (Matrix.GeneralLinearGroup.det g₀))⁻¹ * g₀
  let h : GL (ι ⊕ ι) 𝔸[F] := Matrix.GeneralLinearGroup.map (algebraMap F 𝔸[F]) hF
  have hF1 : Matrix.GeneralLinearGroup.det hF = 1 := by
    simp only [hF, map_mul, map_inv, det_dg i hi, inv_mul_cancel]
  have hdet : Matrix.GeneralLinearGroup.det h = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    have : algebraMap F 𝔸[F] (hF : Matrix (ι ⊕ ι) (ι ⊕ ι) F).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hF1, Units.val_one, map_one]
    rw [← this, RingHom.map_det]
    rfl
  have hc : ((1 : Rˣ), h) ∈ cover A ν ι := by
    rw [mem_cover]
    simp [hdet]
  refine ⟨⟨(1, h), hc⟩, Subgroup.mem_subgroupOf.2 ⟨one_mem _, ⟨hF, rfl⟩⟩, ?_⟩
  have : Matrix.GeneralLinearGroup.map (adStd F).i g₀ * (prj A ν ι ⟨(1, h), hc⟩)⁻¹ =
      dg ι (Units.map (algebraMap F 𝔸[F]).toMonoidHom (Matrix.GeneralLinearGroup.det g₀)) := by
    rw [← dg_map]
    show Matrix.GeneralLinearGroup.map (algebraMap F 𝔸[F]) g₀ *
      (Matrix.GeneralLinearGroup.map (algebraMap F 𝔸[F]) hF)⁻¹ = _
    rw [← map_inv, ← map_mul]
    congr 1
    simp [hF]
  rw [this]
  exact dg_mem_stab _ i

theorem jRat : JRat := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hA hB hi hj
  refine ⟨?_, fun g hg => second A ν i hi g hg⟩
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sub_rat A ν hB.rat δ j hj x hx
  · intro hg
    obtain ⟨x, hx, rfl⟩ := sup_rat A ν r δ α ω hA.iinj hB i hi j hj g hg
    exact ⟨x, hx, rfl⟩

end Main

end GlobalTheory.CompanionTheory.RgEisJRat
