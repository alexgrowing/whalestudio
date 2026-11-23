import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Formalism.LocalRingCardinality.DataLevel

noncomputable section

open Matrix Formalism.UG NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

structure IsQuadInvol (F E : Type) [Field F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E) : Prop where
  etale : Algebra.Etale F E
  finrank_eq : Module.finrank F E = 2
  invol : ∀ e, σ (σ e) = e
  ne_id : ∃ e, σ e ≠ e

section Ring

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def form (σ : A →+* A) (J : Matrix n n A) (y y' : n → A) : A := hform σ J y' y

def adj (σ : A →+* A) (J l : Matrix n n A) : Matrix n n A := J⁻¹ * cT σ l * J

def genAlg (γ : Matrix n n A) : Subalgebra A (Matrix n n A) := Algebra.adjoin A {γ}

instance (γ : Matrix n n A) : CommRing (genAlg γ) :=
  { (inferInstance : Ring (genAlg γ)) with
    mul_comm := fun a b =>
      (Algebra.isMulCommutative_adjoin_singleton A γ).is_comm.comm a b }

def gen (γ : Matrix n n A) : genAlg γ := ⟨γ, Algebra.self_mem_adjoin_singleton A γ⟩

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj_eq_iff (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (l m : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J l = m ↔ _root_.Formalism.UG.cT σ l * J = J * m := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj
  constructor
  · intro h
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ,
      Matrix.one_mul]
  · intro h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    _root_.Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold _root_.Formalism.UG.hform
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form_adj (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (l : Matrix n n A) (y y' : n → A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form σ J y (l *ᵥ y') =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form σ J (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J l *ᵥ y) y' := by
  have hJJ : J * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J l = _root_.Formalism.UG.cT σ l * J := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul]
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.form, _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq]
  rw [mulVec_mulVec, hJJ, ← mulVec_mulVec, dotProduct_mulVec (fun i => σ (y' i))]
  congr 1
  funext i
  unfold _root_.Formalism.UG.cT
  simp [vecMul, mulVec, dotProduct, map_sum, mul_comm]

end Ring

section Objects

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def plusAlg (σ : E →ₐ[F] E) (J γ : Matrix n n E) : Subalgebra F (genAlg γ) where
  carrier := {l | cT (σ : E →+* E) (l : Matrix n n E) * J = J * (l : Matrix n n E)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have hc : ((a * b : genAlg γ) : Matrix n n E) = (b : Matrix n n E) * a := by
      rw [mul_comm a b]; rfl
    have hd : ((a * b : genAlg γ) : Matrix n n E) = (a : Matrix n n E) * b := rfl
    conv_lhs => rw [hd, cT_mul, Matrix.mul_assoc, ha, ← Matrix.mul_assoc, hb]
    rw [hc, Matrix.mul_assoc]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have hd : ((a + b : genAlg γ) : Matrix n n E) = (a : Matrix n n E) + b := rfl
    have he : cT (σ : E →+* E) ((a : Matrix n n E) + (b : Matrix n n E)) =
        cT (σ : E →+* E) (a : Matrix n n E) + cT (σ : E →+* E) (b : Matrix n n E) := by
      ext i j; simp [cT]
    rw [hd, he, Matrix.add_mul, Matrix.mul_add, ha, hb]
  algebraMap_mem' := by
    intro r
    simp only [Set.mem_setOf_eq]
    have hd : ((algebraMap F (genAlg γ) r : genAlg γ) : Matrix n n E) = r • (1 : Matrix n n E) := by
      rw [Algebra.algebraMap_eq_smul_one]; rfl
    have he : cT (σ : E →+* E) (r • (1 : Matrix n n E)) = r • (1 : Matrix n n E) := by
      ext i j; by_cases h : i = j <;> simp [cT, Matrix.one_apply, h, eq_comm]
    rw [hd, he]; simp

def plusTensor (σ : E →ₐ[F] E) (J γ : Matrix n n E) :
    plusAlg σ J γ ⊗[F] E →ₐ[F] genAlg γ :=
  Algebra.TensorProduct.productMap (plusAlg σ J γ).val (IsScalarTower.toAlgHom F E (genAlg γ))

abbrev LPts (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] : Type :=
  plusAlg σ J γ ⊗[F] (E ⊗[F] R)

def lConj (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    LPts σ J γ R →ₐ[F] LPts σ J γ R :=
  Algebra.TensorProduct.map (AlgHom.id F _) (Algebra.TensorProduct.map σ (AlgHom.id F R))

def normOne (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (LPts σ J γ R)ˣ where
  carrier := {u | (u : LPts σ J γ R) * lConj σ J γ R u = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    rw [mul_mul_mul_comm, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h : ((a⁻¹ : _ˣ) : LPts σ J γ R) * lConj σ J γ R (a⁻¹ : _ˣ) * (a * lConj σ J γ R a) = 1 := by
      rw [mul_mul_mul_comm, ← map_mul]; simp
    rwa [ha, mul_one] at h

def toMat (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    LPts σ J γ R →ₐ[F] Matrix n n (E ⊗[F] R) :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] R)).comp
      (((genAlg γ).val.restrictScalars F).comp (plusAlg σ J γ).val))
    (IsScalarTower.toAlgHom F (E ⊗[F] R) (Matrix n n (E ⊗[F] R)))
    (fun _ a => (Algebra.commutes a _).symm)

def centPts (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) (R : Type) [CommRing R]
    [Algebra F R] : Subgroup (GL n (E ⊗[F] R)) :=
  UPts σ J R ⊓ Subgroup.centralizer {bc (inclE (F := F) R) γ}

def centRat (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Subgroup (GL n E) :=
  UJ (σ : E →+* E) J ⊓ Subgroup.centralizer {γ}

structure SplitSubtorus (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) (k : ℕ) where
  hom : ∀ (R : Type) [CommRing R] [Algebra F R], (Fin k → Rˣ) →* GL n (E ⊗[F] R)
  mem : ∀ (R : Type) [CommRing R] [Algebra F R] (t : Fin k → Rˣ), hom R t ∈ centPts σ J γ R
  inj : ∀ (R : Type) [CommRing R] [Algebra F R], Function.Injective (hom R)
  natural : ∀ (R S : Type) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (f : R →ₐ[F] S) (t : Fin k → Rˣ),
    hom S (fun i => Units.map (f : R →* S) (t i)) =
      bc (Algebra.TensorProduct.map (AlgHom.id F E) f).toRingHom (hom R t)

def HasSplitRank (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) (s : ℕ) : Prop :=
  IsGreatest {k | Nonempty (SplitSubtorus σ J γ k)} s

structure IsRegular (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop where
  quad : IsQuadInvol F E σ
  herm : IsHerm (σ : E →+* E) J
  nondeg : IsUnit J.det
  mem : γ ∈ UJ (σ : E →+* E) J
  sep : (γ : Matrix n n E).charpoly.Separable

def ClauseAlg (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  (∃ e : AdjoinRoot (γ : Matrix n n E).charpoly ≃ₐ[E] genAlg (γ : Matrix n n E),
      e (AdjoinRoot.root _) = gen (γ : Matrix n n E)) ∧
  Algebra.Etale E (genAlg (γ : Matrix n n E)) ∧
  Nonempty (Module.Basis n E (genAlg (γ : Matrix n n E))) ∧
  (∃ v : n → E, Function.Bijective
      (fun l : genAlg (γ : Matrix n n E) => (l : Matrix n n E) *ᵥ v)) ∧
  (∀ l ∈ genAlg (γ : Matrix n n E), adj (σ : E →+* E) J l ∈ genAlg (γ : Matrix n n E)) ∧
  adj (σ : E →+* E) J (γ : Matrix n n E) = ((γ⁻¹ : GL n E) : Matrix n n E) ∧
  ∀ e : E, adj (σ : E →+* E) J (algebraMap E (Matrix n n E) e) = algebraMap E (Matrix n n E) (σ e)

def ClausePlus (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  Algebra.Etale F (plusAlg σ J (γ : Matrix n n E)) ∧
  Nonempty (Module.Basis n F (plusAlg σ J (γ : Matrix n n E))) ∧
  Function.Bijective (plusTensor σ J (γ : Matrix n n E))

def ClauseCent (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  (∀ (R : Type) [CommRing R] [Algebra F R],
    Function.Injective (toMat σ J (γ : Matrix n n E) R) ∧
    (∀ u, toMat σ J (γ : Matrix n n E) R (lConj σ J (γ : Matrix n n E) R u) =
      adj (sigR σ R) (J.map (inclE (F := F) R)) (toMat σ J (γ : Matrix n n E) R u)) ∧
    ∀ g : GL n (E ⊗[F] R), g ∈ centPts σ J γ R ↔
      ∃ u ∈ normOne σ J (γ : Matrix n n E) R,
        toMat σ J (γ : Matrix n n E) R (u : LPts σ J (γ : Matrix n n E) R) =
          (g : Matrix n n (E ⊗[F] R))) ∧
  (∀ g : GL n E, g ∈ centRat σ J γ ↔
    (g : Matrix n n E) ∈ genAlg (γ : Matrix n n E) ∧
      (g : Matrix n n E) * adj (σ : E →+* E) J (g : Matrix n n E) = 1) ∧
  ∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω],
    ∃ φ : LPts σ J (γ : Matrix n n E) Ω ≃ₐ[F] (n → Ω × Ω),
      (∀ ω : Ω, φ (1 ⊗ₜ (1 ⊗ₜ ω)) = fun _ => (ω, ω)) ∧
      ∀ u i, φ (lConj σ J (γ : Matrix n n E) Ω u) i = (φ u i).swap

def ClauseRank (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  (∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)),
    Nonempty (plusAlg σ J (γ : Matrix n n E) ≃ₐ[F] ∀ i, K i)) ∧
  ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
    Nonempty (plusAlg σ J (γ : Matrix n n E) ≃ₐ[F] ∀ i, K i) →
      HasSplitRank σ J γ (Nat.card {i : Fin k // ¬ IsField (K i ⊗[F] E)}) ∧
      (Nonempty n → 1 ≤ k) ∧
      (IsField (genAlg (γ : Matrix n n E)) ↔ k = 1 ∧ ∀ i, IsField (K i ⊗[F] E))

def ClauseProper (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  (∀ (R : Type) [CommRing R] [Algebra F R], ∀ a ∈ centPts σ J γ R, ∀ b ∈ centPts σ J γ R,
    a * b = b * a) ∧
  (IsField E → ∀ (s : ℕ), 1 ≤ s → ∀ A : SplitSubtorus σ J γ s,
    ∃ g ∈ UPts σ J F, ∃ t : Fin s → Fˣ, g * A.hom F t ≠ A.hom F t * g)

def ClauseTrace (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  ∃ (x : (plusAlg σ J (γ : Matrix n n E))ˣ) (v : n → E),
    Function.Bijective (fun l : genAlg (γ : Matrix n n E) => (l : Matrix n n E) *ᵥ v) ∧
    ∀ y y' : genAlg (γ : Matrix n n E), ∃ z : genAlg (γ : Matrix n n E),
      (z : Matrix n n E) = adj (σ : E →+* E) J (y' : Matrix n n E) ∧
      form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) ((y' : Matrix n n E) *ᵥ v) =
        Algebra.trace E (genAlg (γ : Matrix n n E))
          (((x : plusAlg σ J (γ : Matrix n n E)) : genAlg (γ : Matrix n n E)) * y * z)

end Objects

def AdelicCompact {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  CompactSpace (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
    ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F)))

def RegularStructure : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
      ClauseAlg σ J γ ∧ ClausePlus σ J γ ∧ ClauseCent σ J γ ∧ ClauseRank σ J γ ∧
        ClauseProper σ J γ ∧ ClauseTrace σ J γ

def RegularAdelic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
      ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
        Nonempty (plusAlg σ J (γ : Matrix n n E) ≃ₐ[F] ∀ i, K i) →
          (AdelicCompact σ J γ ↔ ∀ i, IsField (K i ⊗[F] E))

def RegularSemisimple : Prop := RegularStructure ∧ RegularAdelic

theorem isQuadInvol_complex : IsQuadInvol ℝ ℂ (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) where
  etale := ⟨Algebra.FormallyEtale.of_isSeparable ℝ ℂ,
    Algebra.FinitePresentation.of_finiteType.1 inferInstance⟩
  finrank_eq := Complex.finrank_real_complex
  invol := by intro e; simp
  ne_id := ⟨Complex.I, by simp [Complex.ext_iff]; norm_num⟩

def exElt : GL (Fin 2) ℂ where
  val := !![2, 0; 0, 1 / 2]
  inv := !![1 / 2, 0; 0, 2]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem isRegular_exElt :
    IsRegular (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) exElt where
  quad := isQuadInvol_complex
  herm := by ext i j; fin_cases i <;> fin_cases j <;> simp [cT]
  nondeg := by simp [Matrix.det_fin_two]
  mem := by
    show cT _ _ * _ * _ = _
    have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [cT, exElt, Matrix.mul_apply, Fin.sum_univ_two, h2]
  sep := by
    have h : (exElt : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![2, 1 / 2] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [exElt]
    rw [h, Matrix.charpoly_diagonal]
    refine Polynomial.separable_prod_X_sub_C_iff.2 ?_
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> norm_num at hij

def exDiag (R : Type) [CommRing R] [Algebra ℝ R] :
    (Fin 1 → Rˣ) →* Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] R) where
  toFun t := Matrix.diagonal ![1 ⊗ₜ (t 0 : R), 1 ⊗ₜ (((t 0)⁻¹ : Rˣ) : R)]
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Algebra.TensorProduct.one_def]
  map_mul' a b := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i; fin_cases i <;> simp [mul_comm]

def exSplit : SplitSubtorus (Complex.conjAe : ℂ →ₐ[ℝ] ℂ)
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) exElt 1 where
  hom R _ _ := (exDiag R).toHomUnits
  mem R _ _ t := by
    refine ⟨?_, ?_⟩
    · show cT _ (exDiag R t) * _ * exDiag R t = _
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [cT, exDiag, sigR, Matrix.mul_apply, Fin.sum_univ_two, Algebra.TensorProduct.one_def]
    · refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_)
      show exDiag R t * (exElt : Matrix (Fin 2) (Fin 2) ℂ).map _ =
        (exElt : Matrix (Fin 2) (Fin 2) ℂ).map _ * exDiag R t
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [exDiag, exElt, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  inj R _ _ a b h := by
    have h1 : exDiag R a 0 0 = exDiag R b 0 0 := by
      have := congrArg Units.val h
      exact congrFun (congrFun this 0) 0
    have h2 : (Algebra.TensorProduct.includeRight : R →ₐ[ℝ] ℂ ⊗[ℝ] R) (a 0) =
        (Algebra.TensorProduct.includeRight : R →ₐ[ℝ] ℂ ⊗[ℝ] R) (b 0) := by
      simpa [exDiag] using h1
    have h3 := Algebra.TensorProduct.includeRight_injective (algebraMap ℝ ℂ).injective h2
    funext i; fin_cases i; exact Units.ext h3
  natural R S _ _ _ _ f t := by
    refine Units.ext ?_
    show exDiag S _ = (exDiag R t).map _
    ext i j; fin_cases i <;> fin_cases j <;> simp [exDiag]

end GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
