import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

namespace Formalism.L2.DIV

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

section Fin

variable {κ : Type} [CommRing κ] {n : ℕ}

def blk2 (r : ℕ) (a : Fin n) : ℕ := if a.val < r then 0 else 1

def blkOf (r t : ℕ) (a : Fin n) : ℕ := if a.val < r then 0 else (a.val - r) / t + 1

def blockTri (b : Fin n → ℕ) : Subgroup (GL (Fin n) κ) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) κ).BlockTriangular b}
  one_mem' := by
    show ((1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular b
    rw [Units.val_one]; exact blockTriangular_one
  mul_mem' := by
    intro x y hx hy
    show ((x * y : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular b
    rw [Units.val_mul]; exact BlockTriangular.mul hx hy
  inv_mem' := by
    intro x hx
    show ((x⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular b
    have : Invertible (x : Matrix (Fin n) (Fin n) κ) := x.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hx

theorem mem_blockTri {b : Fin n → ℕ} {g : GL (Fin n) κ} :
    g ∈ blockTri b ↔ ∀ i j, b j < b i → (g : Matrix (Fin n) (Fin n) κ) i j = 0 := Iff.rfl

theorem blockTri_blkOf_le (r t : ℕ) : blockTri (κ := κ) (n := n) (blkOf r t) ≤ blockTri (blk2 r) := by
  intro g hg i j hij
  refine hg ?_
  unfold blk2 at hij
  unfold blkOf
  by_cases hj : j.val < r
  · by_cases hi : i.val < r
    · simp [hj, hi] at hij
    · simp [hj, hi]
  · by_cases hi : i.val < r <;> simp [hj, hi] at hij

theorem submatrix_mul_of_zero {ι : Type} [Fintype ι] (e : ι → Fin n) (he : Function.Injective e)
    (M N : Matrix (Fin n) (Fin n) κ) (h : ∀ i j l, l ∉ Set.range e → M (e i) l * N l (e j) = 0) :
    (M * N).submatrix e e = M.submatrix e e * N.submatrix e e := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  exact (Fintype.sum_of_injective e he _ _ (fun l hl => h i j l hl) (fun _ => rfl)).symm

def blkMat (b : Fin n → ℕ) (c : ℕ) :
    blockTri (κ := κ) b →* Matrix {a : Fin n // b a = c} {a : Fin n // b a = c} κ where
  toFun g := ((g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).submatrix Subtype.val Subtype.val
  map_one' := by
    ext i j
    simp [Matrix.one_apply, Subtype.ext_iff]
  map_mul' := by
    intro x y
    show ((x.1 * y.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).submatrix _ _ = _
    rw [Units.val_mul]
    refine submatrix_mul_of_zero _ Subtype.val_injective _ _ fun i j l hl => ?_
    have hl' : b l ≠ c := fun h => hl ⟨⟨l, h⟩, rfl⟩
    rcases lt_or_gt_of_ne hl' with h | h
    · rw [x.2 (show b l < b i.1 by rw [i.2]; exact h), zero_mul]
    · rw [y.2 (show b j.1 < b l by rw [j.2]; exact h), mul_zero]

def blkDet (b : Fin n → ℕ) (c : ℕ) : blockTri (κ := κ) b →* κˣ :=
  (Matrix.detMonoidHom.comp (blkMat b c)).toHomUnits

def blkR {r : ℕ} (hr : r ≤ n) : blockTri (κ := κ) (n := n) (blk2 r) →* GL (Fin r) κ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ((g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).submatrix (Fin.castLE hr) (Fin.castLE hr)
      map_one' := by
        ext i j
        simp [Matrix.one_apply]
      map_mul' := by
        intro x y
        show ((x.1 * y.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).submatrix _ _ = _
        rw [Units.val_mul]
        refine submatrix_mul_of_zero _ (Fin.castLE_injective hr) _ _ fun i j l hl => ?_
        have hl' : ¬ l.val < r := fun h => hl ⟨⟨l.val, h⟩, by ext; rfl⟩
        have : (y.1 : Matrix (Fin n) (Fin n) κ) l (Fin.castLE hr j) = 0 := by
          refine y.2 ?_
          have hj : (Fin.castLE hr j).val < r := j.2
          simp only [blk2, hj, hl', if_true, if_false]
          exact Nat.zero_lt_one
        rw [this, mul_zero] }

def ext1 {G N : Type} [Group G] [One N] [Mul N] (P : Subgroup G) (f : P → N) (x : G) : N :=
  open Classical in if h : x ∈ P then f ⟨x, h⟩ else 1

theorem extendOne_of_mem {G N : Type} [Group G] [One N] [Mul N] {P : Subgroup G} (f : P → N) {x : G} (h : x ∈ P) :
    ext1 P f x = f ⟨x, h⟩ := by
  unfold ext1; rw [dif_pos h]

theorem blockDiagonalExtendByOnePrimeField_one {G N : Type} [Group G] [MulOneClass N] (P : Subgroup G) (f : P →* N) : ext1 P f 1 = 1 := by
  rw [extendOne_of_mem _ P.one_mem]; exact f.map_one

theorem extendMatrixByIdentityAlongIndices_mul {G N : Type} [Group G] [MulOneClass N] {P : Subgroup G} (f : P →* N) {x y : G} (hx : x ∈ P)
    (hy : y ∈ P) : ext1 P f (x * y) = ext1 P f x * ext1 P f y := by
  rw [extendOne_of_mem _ hx, extendOne_of_mem _ hy, extendOne_of_mem _ (P.mul_mem hx hy), ← f.map_mul]; rfl

theorem extendOne_inv {G N : Type} [Group G] [Group N] {P : Subgroup G} (f : P →* N) {x : G} (hx : x ∈ P) :
    ext1 P f x⁻¹ = (ext1 P f x)⁻¹ := by
  rw [extendOne_of_mem _ hx, extendOne_of_mem _ (P.inv_mem hx), ← f.map_inv]; rfl

def upperLeftBlock {r : ℕ} (hr : r ≤ n) : GL (Fin n) κ → GL (Fin r) κ := ext1 (blockTri (blk2 r)) (blkR hr)

def dBlk (b : Fin n → ℕ) (c : ℕ) : GL (Fin n) κ → κˣ := ext1 (blockTri b) (blkDet b c)

theorem upper_block_val_submatrix {r : ℕ} (hr : r ≤ n) {g : GL (Fin n) κ} (h : g ∈ blockTri (blk2 r)) :
    ((upperLeftBlock hr g : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) =
      (g : Matrix (Fin n) (Fin n) κ).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
  unfold upperLeftBlock; rw [extendOne_of_mem _ h]; rfl

theorem diag_block_det_val {b : Fin n → ℕ} (c : ℕ) {g : GL (Fin n) κ} (h : g ∈ blockTri b) :
    ((dBlk b c g : κˣ) : κ) =
      ((g : Matrix (Fin n) (Fin n) κ).submatrix (Subtype.val : {a : Fin n // b a = c} → Fin n) Subtype.val).det := by
  unfold dBlk; rw [extendOne_of_mem _ h]; rfl

theorem diag_block_det_mul {b : Fin n → ℕ} {c : ℕ} {x y : GL (Fin n) κ} (hx : x ∈ blockTri b) (hy : y ∈ blockTri b) :
    dBlk b c (x * y) = dBlk b c x * dBlk b c y := extendMatrixByIdentityAlongIndices_mul _ hx hy

end Fin

section Unip

variable {κ : Type} [CommRing κ] {r : ℕ}

def unip (κ : Type) [CommRing κ] (r : ℕ) : Subgroup (GL (Fin r) κ) where
  carrier := {g | g ∈ blockTri (κ := κ) (fun a : Fin r => a.val) ∧
    ∀ i, (g : Matrix (Fin r) (Fin r) κ) i i = 1}
  one_mem' := ⟨Subgroup.one_mem _, fun i => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    refine ⟨Subgroup.mul_mem _ hx hy, fun i => ?_⟩
    rw [Units.val_mul, mul_apply, Finset.sum_eq_single i, hx1, hy1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hx (show l.val < i.val from h), zero_mul]
      · rw [hy (show i.val < l.val from h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    have hi := Subgroup.inv_mem _ hx
    refine ⟨hi, fun i => ?_⟩
    have h1 : ((x * x⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i i = 1 := by simp
    rw [Units.val_mul, mul_apply, Finset.sum_eq_single i, hx1, one_mul] at h1
    · exact h1
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hx (show l.val < i.val from h), zero_mul]
      · rw [hi (show i.val < l.val from h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem unip_lower {g : GL (Fin r) κ} (hg : g ∈ unip κ r) {i j : Fin r} (h : j < i) :
    (g : Matrix (Fin r) (Fin r) κ) i j = 0 := hg.1 (show j.val < i.val from h)

theorem unip_diag {g : GL (Fin r) κ} (hg : g ∈ unip κ r) (i : Fin r) :
    (g : Matrix (Fin r) (Fin r) κ) i i = 1 := hg.2 i

theorem unip_mul_entry {x y : GL (Fin r) κ} (hx : x ∈ unip κ r) (hy : y ∈ unip κ r) {i j : Fin r} (hij : i < j)
    (hmid : ∀ l, i < l → l < j →
      (x : Matrix (Fin r) (Fin r) κ) i l * (y : Matrix (Fin r) (Fin r) κ) l j = 0) :
    ((x * y : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (x : Matrix (Fin r) (Fin r) κ) i j + (y : Matrix (Fin r) (Fin r) κ) i j := by
  rw [Units.val_mul, mul_apply, Finset.sum_eq_add i j (ne_of_lt hij), unip_diag hx, unip_diag hy, one_mul, mul_one,
    add_comm]
  · rintro l _ ⟨hli, hlj⟩
    rcases lt_or_gt_of_ne hli with h | h
    · rw [unip_lower hx h, zero_mul]
    · rcases lt_or_gt_of_ne hlj with h' | h'
      · exact hmid l h h'
      · rw [unip_lower hy h', mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
  · intro h; exact absurd (Finset.mem_univ j) h

def unipCol (κ : Type) [CommRing κ] (r a c : ℕ) : Subgroup (GL (Fin r) κ) where
  carrier := {g | g ∈ unip κ r ∧ ∀ i j : Fin r, a ≤ i.val → i.val < c → j.val = c →
    (g : Matrix (Fin r) (Fin r) κ) i j = 0}
  one_mem' := ⟨Subgroup.one_mem _, fun i j _ h1 h2 => by
    have : i ≠ j := fun h => by rw [h] at h1; omega
    simp [this]⟩
  mul_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    refine ⟨Subgroup.mul_mem _ hx hy, fun i j h0 h1 h2 => ?_⟩
    rw [unip_mul_entry hx hy (show i < j by show i.val < j.val; omega), hx0 i j h0 h1 h2, hy0 i j h0 h1 h2, add_zero]
    intro l hil hlj
    rw [hy0 l j (le_trans h0 (le_of_lt hil)) (by have : l.val < j.val := hlj; omega) h2, mul_zero]
  inv_mem' := by
    rintro x ⟨hx, hx0⟩
    have hi := Subgroup.inv_mem _ hx
    refine ⟨hi, fun i j h0 h1 h2 => ?_⟩
    have hij : i < j := by show i.val < j.val; omega
    have h := unip_mul_entry hi hx hij (fun l hil hlj => by
      rw [hx0 l j (le_trans h0 (le_of_lt hil)) (by have : l.val < j.val := hlj; omega) h2, mul_zero])
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (ne_of_lt hij), hx0 i j h0 h1 h2, add_zero] at h
    exact h.symm

theorem unipCol_le (r a c : ℕ) : unipCol κ r a c ≤ unip κ r := fun _ h => h.1

def edgeSum (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (g : GL (Fin r) κ) : κ :=
  ∑ i, ∑ j, if Ed i j then (g : Matrix (Fin r) (Fin r) κ) i j else 0

def supEdge (i j : Fin r) : Prop := j.val = i.val + 1

instance : DecidableRel (supEdge (r := r)) := fun i j => inferInstanceAs (Decidable (j.val = i.val + 1))

def symEdge (ρ k : ℕ) (i j : Fin r) : Prop :=
  (j.val = i.val + 1 ∧ i.val + 1 ≠ ρ ∧ i.val + 1 ≠ ρ + k) ∨ (i.val + 1 = ρ ∧ j.val = ρ + k)

instance (ρ k : ℕ) : DecidableRel (symEdge (r := r) ρ k) := fun i j =>
  inferInstanceAs (Decidable ((j.val = i.val + 1 ∧ i.val + 1 ≠ ρ ∧ i.val + 1 ≠ ρ + k) ∨
    (i.val + 1 = ρ ∧ j.val = ρ + k)))

def edgeHom (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (H : Subgroup (GL (Fin r) κ))
    (hone : ∀ i j, Ed i j → i ≠ j)
    (hadd : ∀ x ∈ H, ∀ y ∈ H, ∀ i j, Ed i j → ((x * y : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (x : Matrix (Fin r) (Fin r) κ) i j + (y : Matrix (Fin r) (Fin r) κ) i j) :
    H →* Multiplicative κ where
  toFun g := Multiplicative.ofAdd (edgeSum Ed (g : GL (Fin r) κ))
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · simp [Matrix.one_apply_ne (hone i j h)]
    · rfl
  map_mul' := by
    intro x y
    rw [← ofAdd_add]
    congr 1
    unfold edgeSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · exact hadd x.1 x.2 y.1 y.2 i j h
    · rw [add_zero]

def supHom (κ : Type) [CommRing κ] (r : ℕ) : unip κ r →* Multiplicative κ :=
  edgeHom supEdge (unip κ r) (fun i j h e => by unfold supEdge at h; rw [e] at h; omega)
    (fun x hx y hy i j h => unip_mul_entry hx hy (by show i.val < j.val; unfold supEdge at h; omega)
      (fun l h1 h2 => by
        have h1' : i.val < l.val := h1
        have h2' : l.val < j.val := h2
        unfold supEdge at h; omega))

def unipSym (κ : Type) [CommRing κ] (r ρ k : ℕ) : Subgroup (GL (Fin r) κ) := unipCol κ r ρ (ρ + k)

def symHom (κ : Type) [CommRing κ] (r ρ k : ℕ) : unipSym κ r ρ k →* Multiplicative κ :=
  edgeHom (symEdge ρ k) (unipSym κ r ρ k)
    (fun i j h e => by unfold symEdge at h; rw [e] at h; omega)
    (fun x hx y hy i j h => unip_mul_entry hx.1 hy.1 (by show i.val < j.val; unfold symEdge at h; omega)
      (fun l h1 h2 => by
        have h1' : i.val < l.val := h1
        have h2' : l.val < j.val := h2
        unfold symEdge at h
        rcases h with h | h
        · omega
        · rw [hy.2 l j (by omega) (by omega) h.2, mul_zero]))

def addCharHom {LL : Type} [CommRing LL] {G : Type} [Group G] (ψ : AddChar κ LL) (f : G →* Multiplicative κ) :
    G →* LLˣ :=
  (ψ.toMonoidHom.comp f).toHomUnits

end Unip

section Res

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oToS : 𝓞 E →+* intAf F E :=
  ((inclE (F := F) (E := E) (Af F)).comp (algebraMap (𝓞 E) E)).codRestrict (intAf F E)
    (fun b => Formalism.UG.CS.incl_int b)

variable {E}

def idS (I : Ideal (𝓞 E)) : Ideal (intAf F E) := I.map (oToS F E)

def cmpS (I : Ideal (𝓞 E)) : 𝓞 E ⧸ I →+* intAf F E ⧸ idS F I :=
  Ideal.quotientMap _ (oToS F E) Ideal.le_comap_map

variable {F}

theorem oToS_coe (b : 𝓞 E) : ((oToS F E b : intAf F E) : E ⊗[F] Af F) = (algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : Af F) := rfl

theorem cmpS_surj (I : Ideal (𝓞 E)) (h : I ≠ ⊥) : Function.Surjective (cmpS F I) := by
  classical
  set π : intAf F E →+* intAf F E ⧸ idS F I := Ideal.Quotient.mk (idS F I) with hπ
  set T : Subring (intAf F E) := ((π.comp (oToS F E)).range).comap π with hT
  have hO : ∀ b : 𝓞 E, oToS F E b ∈ T := fun b => ⟨b, rfl⟩
  have hN : ((Ideal.absNorm I : ℕ) : intAf F E) ∈ idS F I := by
    have : oToS F E ((Ideal.absNorm I : ℕ) : 𝓞 E) ∈ idS F I := Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
    simpa using this
  have hD : ((Ideal.absNorm I : ℕ) : 𝓞 F) ≠ 0 := by
    have : Ideal.absNorm I ≠ 0 := fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hle : intAf F E ≤ T.map (intAf F E).subtype := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      refine ⟨oToS F E b0, hO b0, ?_⟩
      show (algebraMap (𝓞 E) E b0) ⊗ₜ[F] (1 : Af F) = _
      rw [hb0]
    · obtain ⟨r, y', hy', e⟩ := Formalism.UG.P.integral_adele_approximation_holds F _ hD (y : Af F) y.2
      have hy1 : (1 : E) ⊗ₜ[F] (y' : Af F) ∈ intAf F E :=
        Subring.subset_closure (Or.inr ⟨⟨y', hy'⟩, rfl⟩)
      refine ⟨oToS F E (algebraMap (𝓞 F) (𝓞 E) r) + ((Ideal.absNorm I : ℕ) : intAf F E) * ⟨_, hy1⟩, ?_, ?_⟩
      · refine T.add_mem (hO _) ?_
        have h0 : π (((Ideal.absNorm I : ℕ) : intAf F E) * ⟨_, hy1⟩) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ hN)
        rw [hT, Subring.mem_comap, h0]
        exact Subring.zero_mem _
      · show (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) ⊗ₜ[F] (1 : Af F) +
          (((Ideal.absNorm I : ℕ) : intAf F E) : E ⊗[F] Af F) * ((1 : E) ⊗ₜ[F] (y' : Af F)) = (1 : E) ⊗ₜ[F] (y : Af F)
        have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap F E (algebraMap (𝓞 F) F r) := by
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        have h2 : (algebraMap F E (algebraMap (𝓞 F) F r)) ⊗ₜ[F] (1 : Af F) =
            (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (Af F) r) := by
          rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
            ← IsScalarTower.algebraMap_apply]
        have h3 : (((Ideal.absNorm I : ℕ) : intAf F E) : E ⊗[F] Af F) =
            (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (Af F) ((Ideal.absNorm I : ℕ) : 𝓞 F)) := by
          rw [map_natCast]
          have : ((1 : E) ⊗ₜ[F] ((Ideal.absNorm I : ℕ) : Af F) : E ⊗[F] Af F) =
              (Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F) ((Ideal.absNorm I : ℕ) : Af F) := rfl
          rw [this, map_natCast]
          simp
        rw [h1, h2, h3, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
  intro q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨s', hs', e⟩ := hle s.2
  have : s' = s := Subtype.ext e
  subst this
  obtain ⟨b, hb⟩ := hs'
  exact ⟨Ideal.Quotient.mk I b, hb⟩

theorem cmpS_inj (I : Ideal (𝓞 E)) (h : I ≠ ⊥) : Function.Injective (cmpS F I) := by
  classical
  refine Ideal.quotientMap_injective' ?_
  intro b hb
  have hb' : oToS F E b ∈ idS F I := hb
  set φ : 𝓞 E →ₗ[𝓞 E] (Fin 1 → E) := LinearMap.pi (fun _ => Algebra.linearMap (𝓞 E) E) with hφ
  set Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.map φ I with hΛ
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 ((IsNoetherian.noetherian I).map φ)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have ha0' : algebraMap (𝓞 E) E a ≠ 0 := by
      simpa using ha0
    refine eq_top_iff.2 fun x _ => ?_
    have : x = (x 0 / algebraMap (𝓞 E) E a) • φ a := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [hφ, div_mul_cancel₀ _ ha0']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, haI, rfl⟩)
  have key : ∀ s ∈ idS F I, (fun _ : Fin 1 => ((s : intAf F E) : E ⊗[F] Af F)) ∈
      latS (F := F) (Af F) (intAf F E) Λ := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => (fun _ : Fin 1 => ((s : intAf F E) : E ⊗[F] Af F)) ∈
      latS (F := F) (Af F) (intAf F E) Λ) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨a, ha, rfl⟩
      exact Submodule.subset_span ⟨φ a, ⟨a, ha, rfl⟩, rfl⟩
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      exact Submodule.smul_mem _ c hx
  have hg := Formalism.UG.P.global_lattice_one_holds F E (Fin 1) Λ hfin hspan
  have hmem : φ b ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin 1) (E ⊗[F] Af F)) : Matrix (Fin 1) (Fin 1) (E ⊗[F] Af F)) *ᵥ
      (fun i => inclE (F := F) (Af F) (φ b i)) ∈ latS (F := F) (Af F) (intAf F E) Λ
    rw [inv_one, Units.val_one, one_mulVec]
    exact key _ hb'
  rw [hg] at hmem
  obtain ⟨a, ha, e⟩ := hmem
  have : algebraMap (𝓞 E) E a = algebraMap (𝓞 E) E b := congrFun e 0
  have : a = b := RingOfIntegers.coe_injective this
  exact this ▸ ha

theorem cmpS_bij (I : Ideal (𝓞 E)) (h : I ≠ ⊥) : Function.Bijective (cmpS F I) :=
  ⟨cmpS_inj I h, cmpS_surj I h⟩

end Res

section Red

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev Pl (E : Type) [Field E] [NumberField E] : Type := HeightOneSpectrum (𝓞 E)

abbrev kP (PP : Pl E) : Type := 𝓞 E ⧸ PP.asIdeal

def resS (F : Type) [Field F] [NumberField F] [Algebra F E] (PP : Pl E) : intAf F E →+* kP PP :=
  ((RingEquiv.ofBijective (cmpS F PP.asIdeal) (cmpS_bij (F := F) PP.asIdeal PP.ne_bot)).symm : _ →+* kP PP).comp
    (Ideal.Quotient.mk (idS F PP.asIdeal))

theorem resS_oToS (PP : Pl E) (a : 𝓞 E) : resS F PP (oToS F E a) = Ideal.Quotient.mk PP.asIdeal a := by
  unfold resS
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F PP.asIdeal) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

def intGL (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    GL (Fin n) (intAf F E) →* GL (Fin n) (E ⊗[F] Af F) := bc (intAf F E).subtype

def frGL (β : GL (Fin n) (E ⊗[F] Af F)) : GL (Fin n) (intAf F E) →* GL (Fin n) (E ⊗[F] Af F) :=
  (MulAut.conj β).toMonoidHom.comp (intGL F E n)

theorem intGL_injective : Function.Injective (intGL F E n) := by
  intro x y h
  apply Units.ext
  ext i j
  have := congrArg (fun g : GL (Fin n) (E ⊗[F] Af F) => (g : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j) h
  exact this

theorem frGL_injective (β : GL (Fin n) (E ⊗[F] Af F)) : Function.Injective (frGL β) :=
  (MulAut.conj β).injective.comp intGL_injective

def St (β : GL (Fin n) (E ⊗[F] Af F)) : Subgroup (GL (Fin n) (E ⊗[F] Af F)) := (frGL β).range

def pullFr (β : GL (Fin n) (E ⊗[F] Af F)) : St β ≃* GL (Fin n) (intAf F E) :=
  (MonoidHom.ofInjective (frGL_injective β)).symm

theorem frGL_pullFr (β : GL (Fin n) (E ⊗[F] Af F)) (x : St β) : frGL β (pullFr β x) = x := by
  have := (MonoidHom.ofInjective (frGL_injective β)).apply_symm_apply x
  exact congrArg Subtype.val this

theorem pullFr_frGL (β : GL (Fin n) (E ⊗[F] Af F)) (y : GL (Fin n) (intAf F E)) :
    pullFr β ⟨frGL β y, ⟨y, rfl⟩⟩ = y :=
  (MonoidHom.ofInjective (frGL_injective β)).symm_apply_apply y

def redAt (β : GL (Fin n) (E ⊗[F] Af F)) (PP : Pl E) : St β →* GL (Fin n) (kP PP) :=
  (bc (resS F PP)).comp (pullFr β).toMonoidHom

def redFn (β : GL (Fin n) (E ⊗[F] Af F)) (PP : Pl E) : GL (Fin n) (E ⊗[F] Af F) → GL (Fin n) (kP PP) :=
  ext1 (St β) (redAt β PP)

theorem redFn_frGL (β : GL (Fin n) (E ⊗[F] Af F)) (PP : Pl E) (y : GL (Fin n) (intAf F E)) :
    redFn β PP (frGL β y) = bc (resS F PP) y := by
  unfold redFn
  rw [extendOne_of_mem _ (⟨y, rfl⟩ : frGL β y ∈ St β)]
  show bc (resS F PP) (pullFr β ⟨frGL β y, ⟨y, rfl⟩⟩) = _
  rw [pullFr_frGL]

theorem redFn_int (PP : Pl E) (g : GL (Fin n) (𝓞 E)) :
    redFn (1 : GL (Fin n) (E ⊗[F] Af F)) PP (intGL F E n (bc (oToS F E) g)) = bc (Ideal.Quotient.mk PP.asIdeal) g := by
  have h : intGL F E n (bc (oToS F E) g) = frGL 1 (bc (oToS F E) g) := by
    simp [frGL]
  rw [h, redFn_frGL]
  apply Units.ext
  ext i j
  exact resS_oToS PP _

def IsFrame (β : GL (Fin n) (E ⊗[F] Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ x : Fin n → E ⊗[F] Af F, x ∈ hatL (F := F) Λ ↔
    ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)).mulVec x i ∈ intAf F E

def parah (β : GL (Fin n) (E ⊗[F] Af F)) (PP : Pl E) (b : Fin n → ℕ) : Subgroup (GL (Fin n) (E ⊗[F] Af F)) :=
  ((blockTri b).comap (redAt β PP)).map (St β).subtype

theorem mem_parah {β : GL (Fin n) (E ⊗[F] Af F)} {PP : Pl E} {b : Fin n → ℕ} {x : GL (Fin n) (E ⊗[F] Af F)} :
    x ∈ parah β PP b ↔ x ∈ St β ∧ redFn β PP x ∈ blockTri b := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    show ext1 (St β) (redAt β PP) y.1 ∈ _
    rw [extendOne_of_mem _ y.2]
    exact hy
  · rintro ⟨h1, h2⟩
    unfold redFn at h2
    rw [extendOne_of_mem _ h1] at h2
    exact ⟨⟨x, h1⟩, h2, rfl⟩

def princAt (β : GL (Fin n) (E ⊗[F] Af F)) (PP : Pl E) : Subgroup (GL (Fin n) (E ⊗[F] Af F)) :=
  ((redAt β PP).ker).map (St β).subtype

theorem mem_princAt {β : GL (Fin n) (E ⊗[F] Af F)} {PP : Pl E} {x : GL (Fin n) (E ⊗[F] Af F)} :
    x ∈ princAt β PP ↔ x ∈ St β ∧ redFn β PP x = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    show ext1 (St β) (redAt β PP) y.1 = 1
    rw [extendOne_of_mem _ y.2]
    exact hy
  · rintro ⟨h1, h2⟩
    unfold redFn at h2
    rw [extendOne_of_mem _ h1] at h2
    exact ⟨⟨x, h1⟩, h2, rfl⟩

end Red

section Spaces

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

def stdSpace (n : ℕ) (neg : Bool) : HSpace E :=
  Formalism.BasicNotions.Examples₂.stdSpace Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => neg) (if neg then 0 else n) (if neg then n else 0)

theorem stdSpace_gram (n : ℕ) (neg : Bool) :
    (stdSpace (E := E) n neg).gram = Matrix.diagonal (fun _ => (Formalism.BasicNotions.Examples₂.sgn neg : E)) := by
  ext i j
  have h := Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => neg)
    (if neg then 0 else n) (if neg then n else 0) i j
  rw [Matrix.diagonal_apply]
  exact h

structure IsDefUnimod (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) : Prop where
  herm : IsHerm (hc.sig : E →+* E) J
  unit : IsUnit J.det
  tdef : IsTotDef hc.sig J
  lat : Submodule.IsLattice E L
  selfdual : dualSet (hc.sig : E →+* E) J L = (L : Set (Fin n → E))

def IsPosUnimod (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsDefUnimod hc J L ∧ IsTotPosDef hc.sig J

abbrev UR (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) : Subgroup (GL (Fin n) E) := UJ (hc.sig : E →+* E) J

abbrev UA (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) : Subgroup (GL (Fin n) (E ⊗[F] Af F)) :=
  UPts hc.sig J (Af F)

abbrev UQ (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) : Subgroup (UA hc J) :=
  (ratPts hc.sig J (Af F)).subgroupOf (UA hc J)

theorem UA_gram (hc : CMData F E) (S : HSpace E) : UA hc S.gram = UAf hc S := rfl

theorem UQ_gram (hc : CMData F E) (S : HSpace E) : UQ hc S.gram = UFin hc S := rfl

theorem UR_gram (hc : CMData F E) (S : HSpace E) : UR hc S.gram = UF hc S := rfl

end Spaces

section G0

variable {E : Type} [Field E] [NumberField E]

open Classical in

def primesOf (a : 𝓞 E) : Finset (Pl E) :=
  if h : a = 0 then ∅ else
    (Ideal.finite_factors (I := Ideal.span {a}) (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact h)).toFinset

theorem mem_primesOf {a : 𝓞 E} {PP : Pl E} : PP ∈ primesOf a ↔ a ≠ 0 ∧ a ∈ PP.asIdeal := by
  unfold primesOf
  split_ifs with h
  · simp [h]
  · simp [h, Ideal.dvd_span_singleton]

structure IsTypeDatum [StarRing E] (gp : Fin 2 → ℕ) (pb : Fin 2 → 𝓞 E) : Prop where
  prime : ∀ i, (gp i).Prime
  ne : gp 0 ≠ gp 1
  norm : ∀ i, (pb i : E) * star (pb i : E) = (gp i : E)
  deg1 : ∀ i, ∀ PP : Pl E, pb i ∈ PP.asIdeal → Nat.card (kP PP) = gp i
  unram : ∀ i, ∀ PP : Pl E, pb i ∈ PP.asIdeal → pb i ∉ PP.asIdeal ^ 2
  split : ∀ i, ∀ PP : Pl E, pb i ∈ PP.asIdeal → ∀ c : 𝓞 E, (c : E) = star (pb i : E) → c ∉ PP.asIdeal

abbrev G0 (Pg : Finset (Pl E)) (r : ℕ) : Type := ∀ PP : ↥Pg, GL (Fin r) (kP PP.1)

structure LevelP (Pg : Finset (Pl E)) (r : ℕ) (LL : Type) [CommRing LL] where
  H : Subgroup (G0 Pg r)
  chi : H →* LLˣ

namespace LevelP

variable {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]

def triv (Pg : Finset (Pl E)) (r : ℕ) (LL : Type) [CommRing LL] : LevelP Pg r LL := ⟨⊥, 1⟩

def full (Pg : Finset (Pl E)) (r : ℕ) (LL : Type) [CommRing LL] : LevelP Pg r LL := ⟨⊤, 1⟩

def conj (P : LevelP Pg r LL) : LevelP Pg r LL := ⟨P.H, P.chi⁻¹⟩

def prj (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (PP : ↥Pg) :
    (Subgroup.pi Set.univ Hl : Subgroup (G0 Pg r)) →* Hl PP :=
  ((Pi.evalMonoidHom (fun PP : ↥Pg => GL (Fin r) (kP PP.1)) PP).comp (Subgroup.subtype _)).codRestrict (Hl PP)
    (fun x => x.2 PP (Set.mem_univ _))

def ofLocal (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* LLˣ) :
    LevelP Pg r LL where
  H := Subgroup.pi Set.univ Hl
  chi := ∏ PP : ↥Pg, (cl PP).comp (prj Hl PP)

end LevelP

variable {LL : Type} [CommRing LL]

def P0 (Pg : Finset (Pl E)) (r : ℕ) (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) : LevelP Pg r LL :=
  LevelP.ofLocal (fun PP => unip (kP PP.1) r) (fun PP => addCharHom (ψ PP.1) (supHom (kP PP.1) r))

def Psharp (Pg : Finset (Pl E)) (r k : ℕ) (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) : LevelP Pg r LL :=
  LevelP.ofLocal (fun PP => unipCol (kP PP.1) r 0 k)
    (fun PP => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (Subgroup.inclusion (unipCol_le r 0 k)))

def PsharpSym (Pg : Finset (Pl E)) (r ρ k : ℕ) (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) : LevelP Pg r LL :=
  LevelP.ofLocal (fun PP => unipSym (kP PP.1) r ρ k) (fun PP => addCharHom (ψ PP.1) (symHom (kP PP.1) r ρ k))

def IsGenericPsi (Pg : Finset (Pl E)) (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) : Prop := ∀ PP ∈ Pg, ψ PP ≠ 1

end G0

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {LL : Type} [CommRing LL]

structure LevDat (E : Type) [Field E] [NumberField E] (LL : Type) [CommRing LL] (n : ℕ) where
  r : ℕ
  hr : r ≤ n
  t : ℕ
  s : ℕ
  Pg : Finset (Pl E)
  Q : Finset (Pl E)
  P : LevelP Pg r LL
  cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* LLˣ
  xq : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ

def Kg (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F)) (T : Finset (Pl E)) :
    Subgroup (GL (Fin n) (E ⊗[F] Af F)) :=
  UA hc J ⊓ St β ⊓ ⨅ PP ∈ T, princAt β PP

def parLev (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n) :
    Subgroup (GL (Fin n) (E ⊗[F] Af F)) :=
  UA hc J ⊓ St β ⊓ (⨅ PP ∈ D.Pg, parah β PP (blkOf D.r D.t)) ⊓ (⨅ PP ∈ D.Q, parah β PP (blk2 D.r))

def rTup (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n) (x : GL (Fin n) (E ⊗[F] Af F)) : G0 D.Pg D.r :=
  fun PP => upperLeftBlock D.hr (redFn β PP.1 x)

variable {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β : GL (Fin n) (E ⊗[F] Af F)} {D : LevDat E LL n}

theorem parLev_UA {x : GL (Fin n) (E ⊗[F] Af F)} (h : x ∈ parLev hc J β D) : x ∈ UA hc J := h.1.1.1

theorem parLev_St {x : GL (Fin n) (E ⊗[F] Af F)} (h : x ∈ parLev hc J β D) : x ∈ St β := h.1.1.2

theorem parLev_g {x : GL (Fin n) (E ⊗[F] Af F)} (h : x ∈ parLev hc J β D) {PP : Pl E} (hP : PP ∈ D.Pg) :
    redFn β PP x ∈ blockTri (blkOf D.r D.t) := by
  have h1 : x ∈ ⨅ PP ∈ D.Pg, parah β PP (blkOf D.r D.t) := h.1.2
  exact (mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2

theorem parLev_q {x : GL (Fin n) (E ⊗[F] Af F)} (h : x ∈ parLev hc J β D) {PP : Pl E} (hP : PP ∈ D.Q) :
    redFn β PP x ∈ blockTri (blk2 D.r) := by
  have h1 : x ∈ ⨅ PP ∈ D.Q, parah β PP (blk2 D.r) := h.2
  exact (mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2

theorem redFn_mul {x y : GL (Fin n) (E ⊗[F] Af F)} (hx : x ∈ St β) (hy : y ∈ St β) (PP : Pl E) :
    redFn β PP (x * y) = redFn β PP x * redFn β PP y := extendMatrixByIdentityAlongIndices_mul _ hx hy

theorem redFn_one (PP : Pl E) : redFn β PP 1 = 1 := blockDiagonalExtendByOnePrimeField_one _ _

theorem redFn_inv {x : GL (Fin n) (E ⊗[F] Af F)} (hx : x ∈ St β) (PP : Pl E) :
    redFn β PP x⁻¹ = (redFn β PP x)⁻¹ := extendOne_inv _ hx

theorem rTup_one : rTup β D 1 = 1 := by
  funext PP
  show upperLeftBlock D.hr (redFn β PP.1 1) = 1
  rw [redFn_one]; exact blockDiagonalExtendByOnePrimeField_one _ _

theorem rTup_mul {x y : GL (Fin n) (E ⊗[F] Af F)} (hx : x ∈ parLev hc J β D) (hy : y ∈ parLev hc J β D) :
    rTup β D (x * y) = rTup β D x * rTup β D y := by
  funext PP
  show upperLeftBlock D.hr (redFn β PP.1 (x * y)) = upperLeftBlock D.hr (redFn β PP.1 x) * upperLeftBlock D.hr (redFn β PP.1 y)
  rw [redFn_mul (parLev_St hx) (parLev_St hy)]
  exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (parLev_g hx PP.2)) (blockTri_blkOf_le _ _ (parLev_g hy PP.2))

theorem rTup_inv {x : GL (Fin n) (E ⊗[F] Af F)} (hx : x ∈ parLev hc J β D) :
    rTup β D x⁻¹ = (rTup β D x)⁻¹ := by
  funext PP
  show upperLeftBlock D.hr (redFn β PP.1 x⁻¹) = (upperLeftBlock D.hr (redFn β PP.1 x))⁻¹
  rw [redFn_inv (parLev_St hx)]
  exact extendOne_inv _ (blockTri_blkOf_le _ _ (parLev_g hx PP.2))

def rHom (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n) :
    parLev hc J β D →* G0 D.Pg D.r where
  toFun x := rTup β D x.1
  map_one' := rTup_one
  map_mul' x y := rTup_mul x.2 y.2

def lev (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n) :
    Subgroup (GL (Fin n) (E ⊗[F] Af F)) where
  carrier := {x | x ∈ parLev hc J β D ∧ rTup β D x ∈ D.P.H}
  one_mem' := ⟨Subgroup.one_mem _, by rw [rTup_one]; exact Subgroup.one_mem _⟩
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
    rw [rTup_mul hx.1 hy.1]; exact Subgroup.mul_mem _ hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
    rw [rTup_inv hx.1]; exact Subgroup.inv_mem _ hx.2⟩

def levFn (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n) (x : GL (Fin n) (E ⊗[F] Af F)) : LLˣ :=
  ext1 D.P.H D.P.chi (rTup β D x) *
    (∏ PP ∈ D.Pg, ∏ c ∈ Finset.range D.s, D.cg (c + 1) PP (dBlk (blkOf D.r D.t) (c + 1) (redFn β PP x))) *
    ∏ PP ∈ D.Q, D.xq PP (dBlk (blk2 D.r) 1 (redFn β PP x))

theorem mul3 {M : Type} [CommMonoid M] (a a' b b' c c' : M) :
    a * a' * (b * b') * (c * c') = a * b * c * (a' * b' * c') := by
  simp only [mul_left_comm, mul_comm]

def levChar (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n) :
    lev hc J β D →* LLˣ where
  toFun x := levFn β D x.1
  map_one' := by
    show levFn β D 1 = 1
    unfold levFn
    rw [rTup_one, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · intro PP _
      rw [redFn_one, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
    · intro PP _
      refine Finset.prod_eq_one fun c _ => ?_
      rw [redFn_one, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  map_mul' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    show levFn β D (x * y) = levFn β D x * levFn β D y
    unfold levFn
    rw [rTup_mul hx.1 hy.1, extendMatrixByIdentityAlongIndices_mul _ hx.2 hy.2]
    have e1 : ∏ PP ∈ D.Pg, ∏ c ∈ Finset.range D.s,
          D.cg (c + 1) PP (dBlk (blkOf D.r D.t) (c + 1) (redFn β PP (x * y))) =
        (∏ PP ∈ D.Pg, ∏ c ∈ Finset.range D.s, D.cg (c + 1) PP (dBlk (blkOf D.r D.t) (c + 1) (redFn β PP x))) *
        ∏ PP ∈ D.Pg, ∏ c ∈ Finset.range D.s, D.cg (c + 1) PP (dBlk (blkOf D.r D.t) (c + 1) (redFn β PP y)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun PP hP => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [redFn_mul (parLev_St hx.1) (parLev_St hy.1), diag_block_det_mul (parLev_g hx.1 hP) (parLev_g hy.1 hP), map_mul]
    have e2 : ∏ PP ∈ D.Q, D.xq PP (dBlk (blk2 D.r) 1 (redFn β PP (x * y))) =
        (∏ PP ∈ D.Q, D.xq PP (dBlk (blk2 D.r) 1 (redFn β PP x))) *
        ∏ PP ∈ D.Q, D.xq PP (dBlk (blk2 D.r) 1 (redFn β PP y)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun PP hP => ?_
      rw [redFn_mul (parLev_St hx.1) (parLev_St hy.1), diag_block_det_mul (parLev_q hx.1 hP) (parLev_q hy.1 hP), map_mul]
    rw [e1, e2]
    exact mul3 _ _ _ _ _ _

theorem levChar_apply (x : lev hc J β D) : levChar hc J β D x = levFn β D x.1 := rfl

theorem mem_lev {x : GL (Fin n) (E ⊗[F] Af F)} :
    x ∈ lev hc J β D ↔ x ∈ parLev hc J β D ∧ rTup β D x ∈ D.P.H := Iff.rfl

theorem mem_parLev {x : GL (Fin n) (E ⊗[F] Af F)} :
    x ∈ parLev hc J β D ↔ x ∈ UA hc J ∧ x ∈ St β ∧ (∀ PP ∈ D.Pg, redFn β PP x ∈ blockTri (blkOf D.r D.t)) ∧
      ∀ PP ∈ D.Q, redFn β PP x ∈ blockTri (blk2 D.r) := by
  constructor
  · exact fun h => ⟨parLev_UA h, parLev_St h, fun PP hP => parLev_g h hP, fun PP hP => parLev_q h hP⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_parah.2 ⟨h2, h3 PP hP⟩⟩,
      Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_parah.2 ⟨h2, h4 PP hP⟩⟩

theorem lev_le_parLev : lev hc J β D ≤ parLev hc J β D := fun _ h => h.1

theorem lev_le_UA : lev hc J β D ≤ UA hc J := fun _ h => parLev_UA h.1

theorem Kg_le_lev {T : Finset (Pl E)} (hg : D.Pg ⊆ T) (hq : D.Q ⊆ T) : Kg hc J β T ≤ lev hc J β D := by
  intro x hx
  have h3 : ∀ PP ∈ T, redFn β PP x = 1 := by
    have h1 : x ∈ ⨅ PP ∈ T, princAt β PP := hx.2
    exact fun PP hP => (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  refine ⟨⟨⟨hx.1, ?_⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_parah.2 ⟨hx.1.2, ?_⟩
    rw [h3 PP (hg hP)]; exact Subgroup.one_mem _
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_parah.2 ⟨hx.1.2, ?_⟩
    rw [h3 PP (hq hP)]; exact Subgroup.one_mem _
  · have : rTup β D x = 1 := by
      funext PP
      show upperLeftBlock D.hr (redFn β PP.1 x) = 1
      rw [h3 PP.1 (hg PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
    show rTup β D x ∈ D.P.H
    rw [this]; exact Subgroup.one_mem _

def datX (r t m : ℕ) (Pg Q : Finset (Pl E)) (P : LevelP Pg r LL) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* LLˣ)
    (ξ : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) : LevDat E LL (r + m * t) where
  r := r
  hr := Nat.le_add_right _ _
  t := t
  s := m
  Pg := Pg
  Q := Q
  P := P
  cg := χ
  xq := fun PP => (ξ PP)⁻¹

def datV (r t j : ℕ) (Pg Q : Finset (Pl E)) (P : LevelP Pg r LL) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* LLˣ)
    (ξ : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) : LevDat E LL (r + t) where
  r := r
  hr := Nat.le_add_right _ _
  t := t
  s := 1
  Pg := Pg
  Q := Q
  P := P.conj
  cg := fun _ PP => (χ j PP)⁻¹
  xq := ξ

abbrev levX (hc : CMData F E) (r t m : ℕ) (J : Matrix (Fin (r + m * t)) (Fin (r + m * t)) E)
    (β : GL (Fin (r + m * t)) (E ⊗[F] Af F)) (Pg Q : Finset (Pl E)) (P : LevelP Pg r LL)
    (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) (ξ : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) :
    Subgroup (GL (Fin (r + m * t)) (E ⊗[F] Af F)) :=
  lev hc J β (datX r t m Pg Q P χ ξ)

abbrev levV (hc : CMData F E) (r t j : ℕ) (J : Matrix (Fin (r + t)) (Fin (r + t)) E)
    (β : GL (Fin (r + t)) (E ⊗[F] Af F)) (Pg Q : Finset (Pl E)) (P : LevelP Pg r LL)
    (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) (ξ : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) :
    Subgroup (GL (Fin (r + t)) (E ⊗[F] Af F)) :=
  lev hc J β (datV r t j Pg Q P χ ξ)

end Lev

section Cls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

abbrev Cl (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (K : Subgroup (GL (Fin n) (E ⊗[F] Af F))) : Type :=
  ClassSet (UQ hc J) (K.subgroupOf (UA hc J))

variable {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {K : Subgroup (GL (Fin n) (E ⊗[F] Af F))}

def rep (c : Cl hc J K) : UA hc J := Quotient.out c

theorem mk_rep (c : Cl hc J K) : (Quotient.mk'' (rep c) : Cl hc J K) = c := Quotient.out_eq c

def latAt (L : Submodule (𝓞 E) (Fin n → E)) (c : Cl hc J K) : Submodule (𝓞 E) (Fin n → E) :=
  Formalism.UG.CS.globLat ((rep c : UA hc J) : GL (Fin n) (E ⊗[F] Af F)) L

def conjIn (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (y : GL (Fin n) (E ⊗[F] Af F)) :
    UR hc J →* GL (Fin n) (E ⊗[F] Af F) :=
  (MulAut.conj y⁻¹).toMonoidHom.comp ((bc (inclE (F := F) (Af F))).comp (UR hc J).subtype)

theorem conjIn_apply (y : GL (Fin n) (E ⊗[F] Af F)) (γ : UR hc J) :
    conjIn hc J y γ = y⁻¹ * bc (inclE (F := F) (Af F)) (γ : GL (Fin n) E) * y := by
  simp [conjIn]

def Gam (c : Cl hc J K) : Subgroup (UR hc J) :=
  K.comap (conjIn hc J ((rep c : UA hc J) : GL (Fin n) (E ⊗[F] Af F)))

def gamTo (c : Cl hc J K) : Gam c →* K :=
  ((conjIn hc J ((rep c : UA hc J) : GL (Fin n) (E ⊗[F] Af F))).comp (Gam c).subtype).codRestrict K (fun x => x.2)

def gamChar {LL : Type} [CommRing LL] (lam : K →* LLˣ) (c : Cl hc J K) : Gam c →* LLˣ := lam.comp (gamTo c)

def minkExp (N p : ℕ) : ℕ := ∑ i ∈ Finset.range (N + 1), N / (p ^ i * (p - 1))

def minkNum (N : ℕ) : ℕ := ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ minkExp N p

end Cls

end Formalism.L2.DIV

end
