import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.ConclusionA2

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G

namespace Formalism.MainNotions.CovariantDegrees

lemma genMat_map_eval {n : ℕ} {R : Type} [CommRing R] (f : ℤ →+* R) (g : Matrix (Fin n) (Fin n) R) :
    (MvPolynomial.eval₂Hom f (fun ab : Fin n × Fin n => g ab.1 ab.2)).mapMatrix (genMat ℤ n) = g := by
  ext a b
  simp [genMat]

def evGL {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : GLCoord ℤ n →+* R :=
  IsLocalization.Away.lift (genMat ℤ n).det
    (g := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ab : Fin n × Fin n => g.val ab.1 ab.2))
    (by rw [RingHom.map_det, genMat_map_eval]; exact Matrix.isUnits_det_units g)

lemma genMat_map_coord {n : ℕ} (F : Type) [CommRing F] :
    (MvPolynomial.map (Int.castRingHom F)).mapMatrix (genMat ℤ n) = genMat F n := by
  ext a b
  simp [genMat]

def mapCoord {n : ℕ} (F : Type) [CommRing F] : GLCoord ℤ n →+* GLCoord F n :=
  IsLocalization.Away.lift (genMat ℤ n).det
    (g := (algebraMap (MvPolynomial (Fin n × Fin n) F) (GLCoord F n)).comp (MvPolynomial.map (Int.castRingHom F)))
    (by rw [RingHom.comp_apply, RingHom.map_det, genMat_map_coord]
        exact IsLocalization.Away.algebraMap_isUnit _)

structure GLMod (n : ℕ) where
  ι : Type
  [fi : Fintype ι]
  [de : DecidableEq ι]
  A : Matrix ι ι (GLCoord ℤ n)
  mul : ∀ (R : Type) [CommRing R] (g h : GL (Fin n) R), A.map (evGL (g * h)) = A.map (evGL g) * A.map (evGL h)
  one : ∀ (R : Type) [CommRing R], A.map (evGL (1 : GL (Fin n) R)) = 1

attribute [instance] GLMod.fi GLMod.de

def TCols {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Finset ℤ := Finset.Ioc (mu (lastIdx n)) (mu 0)

abbrev TIdx {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :=
  (c : ↥(TCols mu)) → {J : Finset (Fin n) // J.card = colH mu c}

lemma colH_le {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : colH mu c ≤ n := by
  unfold colH
  exact (Finset.card_filter_le _ _).trans (by simp)

def canT {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : TIdx mu :=
  fun c => ⟨(univ : Finset (Fin (colH mu c))).map (Fin.castLEEmb (colH_le mu c)), by simp⟩

def minorC {n h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) : GLCoord ℤ n :=
  algebraMap _ (GLCoord ℤ n)
    (Matrix.det (Matrix.of fun a b : Fin h => genMat ℤ n (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)))

def detU (n : ℕ) : (GLCoord ℤ n)ˣ := (IsLocalization.Away.algebraMap_isUnit (genMat ℤ n).det).unit

def TMat {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Matrix (TIdx mu) (TIdx mu) (GLCoord ℤ n) :=
  fun J I => ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
    ∏ c : ↥(TCols mu), minorC (J c).1 (I c).1 (J c).2 (I c).2

def brk {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) : GLCoord ℤ n := TMat mu (canT mu) I

def StdT {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) : Prop :=
  ∀ (c : ↥(TCols mu)) (hc : (c : ℤ) + 1 ∈ TCols mu) (t : Fin n),
    ((I ⟨(c : ℤ) + 1, hc⟩).1.filter (· ≤ t)).card ≤ ((I c).1.filter (· ≤ t)).card

def dMu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : ℕ := Nat.card {I : TIdx mu // StdT I}

def SMu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Submodule ℤ (GLCoord ℤ n) :=
  Submodule.span ℤ (Set.range (brk mu))

def torusPt (n : ℕ) : GL (Fin n) (AddMonoidAlgebra ℤ (Fin n → ℤ)) where
  val := Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a 1) 1
  inv := Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (-1)) 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2
    funext a; rw [AddMonoidAlgebra.single_mul_single, ← Pi.single_add]; simp [AddMonoidAlgebra.one_def]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2
    funext a; rw [AddMonoidAlgebra.single_mul_single, ← Pi.single_add]; simp [AddMonoidAlgebra.one_def]

def prMu {n : ℕ} (M : GLMod n) (mu : Fin n → ℤ) : Matrix M.ι M.ι ℤ :=
  fun i j => (evGL (torusPt n) (M.A i j)).coeff mu

def IsHighest {n : ℕ} (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) (x : M.ι → R) : Prop :=
  Matrix.mulVec ((prMu M mu).map (Int.castRingHom R)) x = x ∧
  ∀ (R' : Type) [CommRing R'] [Algebra R R'] (u : GL (Fin n) R'), (∀ a, u.val a a = 1) →
    (∀ a b, b < a → u.val a b = 0) → Matrix.mulVec (M.A.map (evGL u)) (fun i => algebraMap R R' (x i)) = fun i => algebraMap R R' (x i)

def typeSum {n : ℕ} (M : GLMod n) (pi : Set (Fin n → ℤ)) : Submodule ℚ (M.ι → ℚ) :=
  Submodule.span ℚ {y | ∃ mu ∈ pi, ∃ v, IsHighest M ℚ mu v ∧ ∃ g : GL (Fin n) ℚ, y = Matrix.mulVec (M.A.map (evGL g)) v}

def DomLE {n : ℕ} (nu mu : Fin n → ℤ) : Prop :=
  (∀ a : Fin n, ∑ b ∈ univ.filter (· ≤ a), nu b ≤ ∑ b ∈ univ.filter (· ≤ a), mu b) ∧ ∑ b, nu b = ∑ b, mu b

def DomLowerSet {n : ℕ} (pi : Set (Fin n → ℤ)) : Prop :=
  (∀ mu ∈ pi, Dominant mu) ∧ ∀ mu ∈ pi, ∀ nu, Dominant nu → DomLE nu mu → nu ∈ pi

structure ColFam {n : ℕ} [NeZero n] (M : GLMod n) where
  J : Type
  [fJ : Fintype J]
  [dJ : DecidableEq J]
  mu : J → Fin n → ℤ
  dom : ∀ j, Dominant (mu j)
  ph : (j : J) → Matrix M.ι (TIdx (mu j)) ℤ
  equiv : ∀ j, M.A * (ph j).map (Int.castRingHom _) = (ph j).map (Int.castRingHom _) * TMat (mu j)
  indepP : ∀ (p : ℕ), p.Prime → ∀ nu : Fin n → ℤ,
    LinearIndependent (ZMod p) (fun j : {j : J // mu j = nu} => fun i => ((ph j.1 i (canT (mu j.1)) : ℤ) : ZMod p))
  indepQ : ∀ nu : Fin n → ℤ,
    LinearIndependent ℚ (fun j : {j : J // mu j = nu} => fun i => ((ph j.1 i (canT (mu j.1)) : ℤ) : ℚ))
  rank : Fintype.card M.ι = ∑ j, dMu (mu j)

attribute [instance] ColFam.fJ ColFam.dJ

def ColFam.vec {n : ℕ} [NeZero n] {M : GLMod n} (CF : ColFam M) (j : CF.J) (I : TIdx (CF.mu j)) : M.ι → ℤ :=
  fun i => CF.ph j i I

def ColFam.Mpi {n : ℕ} [NeZero n] {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) : Submodule ℤ (M.ι → ℤ) :=
  Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), x = CF.vec j I}

def ColFam.MM {n : ℕ} [NeZero n] {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) : Submodule ℤ (M.ι → ℤ) :=
  Submodule.span ℤ {x | ∃ j, CF.mu j = mu ∧ x = CF.vec j (canT (CF.mu j))}

abbrev SymIdx (n b : ℕ) := {α : Fin n → Fin (b + 1) // ∑ a, (α a : ℕ) = b}

def symMono {n b : ℕ} (α : SymIdx n b) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => (α.1 a : ℕ)

def SymMat (n b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) (GLCoord ℤ n) :=
  fun α β => MvPolynomial.coeff (symMono α)
    (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (algebraMap _ (GLCoord ℤ n) (genMat ℤ n a m)) * X a) ^ (β.1 m : ℕ))

def ginvC (n : ℕ) (a b : Fin n) : GLCoord ℤ n :=
  (((detU n)⁻¹ : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * algebraMap _ (GLCoord ℤ n) ((genMat ℤ n).adjugate a b)

def SymDMat (n b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) (GLCoord ℤ n) :=
  fun α β => MvPolynomial.coeff (symMono α)
    (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (ginvC n m a) * X a) ^ (β.1 m : ℕ))

abbrev LamIdx (n b : ℕ) := {J : Finset (Fin n) // J.card = b}

def LamMat (n b : ℕ) : Matrix (LamIdx n b) (LamIdx n b) (GLCoord ℤ n) :=
  fun J I => minorC J.1 I.1 J.2 I.2

def IsTensor {n : ℕ} (M M' : GLMod n) {κ : Type} (B : Matrix κ κ (GLCoord ℤ n)) (e : M'.ι ≃ M.ι × κ) : Prop :=
  ∀ i j, M'.A i j = M.A (e i).1 (e j).1 * B (e i).2 (e j).2

def IsSMu {n : ℕ} [NeZero n] (M : GLMod n) (mu : Fin n → ℤ) (β : M.ι → GLCoord ℤ n) : Prop :=
  LinearIndependent ℤ β ∧ Submodule.span ℤ (Set.range β) = SMu mu ∧
  ∀ (R : Type) [CommRing R] (x g : GL (Fin n) R) (i : M.ι),
    evGL (x * g) (β i) = ∑ j, evGL g (M.A j i) * evGL x (β j)

def Interl {m : ℕ} (lam : Fin (m + 1) → ℤ) (nu : Fin m → ℤ) : Prop :=
  ∀ a : Fin m, nu a ≤ lam a.castSucc ∧ lam a.succ ≤ nu a

def IsBlock {m : ℕ} {R : Type} [CommRing R] (h : GL (Fin (m + 1)) R) (g1 : GL (Fin m) R) (t : Rˣ) : Prop :=
  (∀ a b : Fin m, h.val a.castSucc b.castSucc = g1.val a b) ∧ h.val (Fin.last m) (Fin.last m) = t ∧
  ∀ a : Fin m, h.val a.castSucc (Fin.last m) = 0 ∧ h.val (Fin.last m) a.castSucc = 0

lemma genMat_map_evalR {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (g : Matrix (Fin n) (Fin n) R') :
    (MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g ab.1 ab.2)).mapMatrix (genMat R n) = g := by
  ext a b
  simp [genMat]

def evGLR {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') : GLCoord R n →+* R' :=
  IsLocalization.Away.lift (genMat R n).det
    (g := MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g.val ab.1 ab.2))
    (by rw [RingHom.map_det, genMat_map_evalR]; exact Matrix.isUnits_det_units g)

def inducedSections {n : ℕ} (R : Type) [CommRing R] (mu : Fin n → ℤ) : Set (GLCoord R n) :=
  {f | ∀ (R' : Type) [CommRing R'] [Algebra R R'] (b g : GL (Fin n) R'), (∀ a c : Fin n, a < c → b.val a c = 0) →
    evGLR (b * g) f * ∏ a, b.val a a ^ (-(mu a)).toNat = (∏ a, b.val a a ^ (mu a).toNat) * evGLR g f}

def rowLetters (n : ℕ) : Letters (Fin n) := ⟨fun _ => true⟩

def brkPol {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) : MvPolynomial (Fin n × Fin n) ℤ :=
  (genMat ℤ n).det ^ (mu (lastIdx n)).toNat *
    ∏ c : ↥(TCols mu), Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat ℤ n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b))

def PathPairCorrespondence (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu → ∀ (F : Type) [Field F],
    LinearIndependent F (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1))

def admB2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    LinearIndependent ℤ (fun I : {I : TIdx mu // StdT I} => brk mu I.1) ∧
    Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) = SMu mu

def admB3 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M),
    (LinearIndependent ℤ (fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => CF.vec x.1 x.2.1) ∧
      Submodule.span ℤ (Set.range fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => CF.vec x.1 x.2.1) = ⊤) ∧
    ∀ (R : Type) [CommRing R],
      LinearIndependent R (fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => fun i => (CF.vec x.1 x.2.1 i : R)) ∧
      Submodule.span R (Set.range fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) =>
        fun i => (CF.vec x.1 x.2.1 i : R)) = ⊤

def ColumnFamilyLowerSet (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    CF.Mpi pi = Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} ∧
    (∀ x : M.ι → ℤ, x ∈ CF.Mpi pi ↔ (fun i => (x i : ℚ)) ∈ typeSum M pi) ∧
    (∀ x ∈ CF.Mpi pi, ∀ ℓ : GLCoord ℤ n →ₗ[ℤ] ℤ,
      (fun i => ℓ (Matrix.mulVec M.A (fun j => ((x j : ℤ) : GLCoord ℤ n)) i)) ∈ CF.Mpi pi) ∧
    (∃ C : Submodule ℤ (M.ι → ℤ), IsCompl (CF.Mpi pi) C) ∧
    ∀ mu ∈ pi, (∀ nu ∈ pi, DomLE mu nu → nu = mu) →
      (∃ Φ : (↥(CF.Mpi pi) ⧸ (CF.Mpi (pi \ {mu})).comap (CF.Mpi pi).subtype) ≃ₗ[ℤ]
          TensorProduct ℤ ↥(SMu mu) ↥(CF.MM mu),
        ∀ (j : CF.J) (I : TIdx (CF.mu j)) (x : ↥(CF.Mpi pi)) (y : ↥(SMu mu)) (z : ↥(CF.MM mu)),
          CF.mu j = mu → StdT I → x.1 = CF.vec j I → y.1 = brk (CF.mu j) I → z.1 = CF.vec j (canT (CF.mu j)) →
          Φ (Submodule.Quotient.mk x) = y ⊗ₜ z) ∧
      (CF.MM mu : Set (M.ι → ℤ)) = {x | IsHighest M ℤ mu x}

def GenericProjectionCriterion (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ (F : Type) [Field F] (x : M.ι → F),
      x ∈ Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ y = fun i => (CF.vec j I i : F)} ↔
      ∀ mu, Dominant mu → mu ∉ pi →
        Matrix.mulVec ((prMu M mu).map (Int.castRingHom (GLCoord F n)))
          (Matrix.mulVec (M.A.map (mapCoord F)) (fun i => algebraMap F (GLCoord F n) (x i))) = 0

def ColumnFamilyClosure (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n],
    (∀ M : GLMod n, Fintype.card M.ι = 1 → (∀ i j, M.A i j = 1) → Nonempty (ColFam M)) ∧
    (∀ (M : GLMod n) (mu : Fin n → ℤ) (β : M.ι → GLCoord ℤ n), Dominant mu → IsSMu M mu β → Nonempty (ColFam M)) ∧
    ∀ (M M' : GLMod n) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ e : M'.ι ≃ M.ι,
      (∀ i j, M'.A i j = ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i) (e j)) →
      Nonempty (ColFam M) → Nonempty (ColFam M')

def TensorColumnFamily (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n] (M M' : GLMod n) (b : ℕ), Nonempty (ColFam M) →
    (∀ e, IsTensor M M' (SymMat n b) e → Nonempty (ColFam M')) ∧
    (∀ e, IsTensor M M' (SymDMat n b) e → Nonempty (ColFam M')) ∧
    (∀ e, IsTensor M M' (LamMat n b) e → Nonempty (ColFam M'))

def BranchingColumnFamily (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (m : ℕ) [NeZero m] (M : GLMod (m + 1)) (lam : Fin (m + 1) → ℤ) (β : M.ι → GLCoord ℤ (m + 1)),
    Dominant lam → IsSMu M lam β →
    ∃ (Sg : Finset (Fin m → ℤ)) (ph : (nu : ↥Sg) → Matrix M.ι (TIdx (nu : Fin m → ℤ)) ℤ),
      (∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu) ∧
      (∀ (nu : ↥Sg) (R : Type) [CommRing R] (h : GL (Fin (m + 1)) R) (g1 : GL (Fin m) R) (t : Rˣ), IsBlock h g1 t →
        M.A.map (evGL h) * (ph nu).map (Int.castRingHom R) =
          (((t ^ (∑ a, lam a - ∑ a, (nu : Fin m → ℤ) a) : Rˣ) : R)) • ((ph nu).map (Int.castRingHom R) *
            (TMat (nu : Fin m → ℤ)).map (evGL g1))) ∧
      (∀ nu : ↥Sg, (∀ (p : ℕ), p.Prime → (fun i => ((ph nu i (canT _) : ℤ) : ZMod p)) ≠ 0) ∧
        (fun i => ((ph nu i (canT _) : ℤ) : ℚ)) ≠ 0) ∧
      Fintype.card M.ι = ∑ nu : ↥Sg, dMu (nu : Fin m → ℤ)

def GlobalSectionsSchur (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (R : Type) [CommRing R] [IsDomain R],
    (IsField R ∨ IsDiscreteValuationRing R ∨ Nonempty (R ≃+* ℤ)) →
    (Dominant mu → inducedSections R mu = (Submodule.span R (Set.range fun I : TIdx mu => mapCoord (n := n) R (brk mu I)) : Set _)) ∧
    (¬ Dominant mu → inducedSections R mu = {0})

def BracketPolynomialSpan (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    (Submodule.span ℤ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ))
          (MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu (canT mu)))}

def GradedLatticeStable (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (La : Submodule O V),
    IsGLRep E → Dominant mu → isoSub E mu = ⊤ → UZLattice E La →
    (∀ x ∈ La, ∀ nu e, IsWtProj E nu e → e x ∈ La) →
    Submodule.span O {x | ∃ u ∈ UZmon E, ∃ y ∈ La, y ∈ weightSp E mu ∧ x = u y} ≤ La ∧
    ∀ y ∈ La, ∀ u ∈ UZmon E, ∀ e, IsWtProj E mu e → e (u y) ∈ La ∧ e (u y) ∈ weightSp E mu

def NestedTypeBound (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B)
    (I : ℤ → Finset (Fin n)) (i : Fin (N + 1)),
    Psi F P.mu I ∈ ⨆ lam ∈ {lam : Fin n → ℤ | Dominant lam ∧ DomLE lam (P.mu i)},
      isoSub (glOps F n LL {j | j.val < i.val}) lam

def TypeDecompositionsCommute (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N n : ℕ) (LL : Letters (Fin N)) (i j : Fin (N + 1)) (lam lam' : Fin n → ℤ)
    (e e' : Module.End F (MvPolynomial (Fin N × Fin n) F)),
    IsIsoProj (glOps F n LL {l | l.val < i.val}) lam e → IsIsoProj (glOps F n LL {l | l.val < j.val}) lam' e' →
    e * e' = e' * e

def JointComponentsPaths (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (lam : Fin (N + 1) → Fin n → ℤ),
    ((∃ P : PPath n N LL B, P.mu = lam) →
      Module.finrank F ↥(Pol F n B ⊓ (⨅ i : Fin (N + 1), isoSub (glOps F n LL {l | l.val < i.val}) (lam i))) =
        Nat.card {I : ℤ → Finset (Fin n) // IsSt lam I}) ∧
    ((¬ ∃ P : PPath n N LL B, P.mu = lam) →
      Pol F n B ⊓ (⨅ i : Fin (N + 1), isoSub (glOps F n LL {l | l.val < i.val}) (lam i)) = ⊥)

def nestLat (O : Type) [CommRing O] [IsDomain O] (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (pi : Fin (N + 1) → Set (Fin n → ℤ)) (Ix : Set (Fin (N + 1))) : Set (MvPolynomial (Fin N × Fin n) O) :=
  {G | G ∈ Pol O n B ∧ ∀ i ∈ Ix, MvPolynomial.map (algebraMap O (KK O)) G ∈
    ⨆ lam ∈ pi i, isoSub (glOps (KK O) n LL {l | l.val < i.val}) lam}

def nestSpan (O : Type) [CommRing O] (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (pi : Fin (N + 1) → Set (Fin n → ℤ)) (Ix : Set (Fin (N + 1))) : Submodule O (MvPolynomial (Fin N × Fin n) O) :=
  Submodule.span O {G | ∃ P : PPath n N LL B, ∃ I, IsSt P.mu I ∧ (∀ i ∈ Ix, P.mu i ∈ pi i) ∧ G = Psi O P.mu I}

def SaturatedLowerSetSpan (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N n : ℕ) (LL : Letters (Fin N))
    (B : Fin N → ℕ) (pi : Fin (N + 1) → Set (Fin n → ℤ)), (∀ i, DomLowerSet (pi i)) →
    (∀ Ix : Set (Fin (N + 1)), nestLat O N n LL B pi Ix = (nestSpan O N n LL B pi Ix : Set _)) ∧
    ∀ (p E : ℕ),
      (⨅ i : Fin (N + 1), (nestSpan O N n LL B pi {i} ⊔ (Ideal.span {((p : O) ^ E)}) • Pol O n B)) =
        (⨅ i : Fin (N + 1), nestSpan O N n LL B pi {i}) ⊔ (Ideal.span {((p : O) ^ E)}) • Pol O n B

def AutomorphicSideConclusion (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (N n : ℕ) (LL : Letters (Fin N))
    (B : Fin N → ℕ) (mu : Fin n → ℤ),
    (∀ P : PPath n N LL B, pEnd P.mu = mu → IsHWVPol O LL mu (Psi O P.mu (Ican P.mu))) ∧
    LinearIndependent (FF O) (fun P : {P : PPath n N LL B // pEnd P.mu = mu} => Psi (FF O) P.1.mu (Ican P.1.mu))

def A3at (R : Type) [CommRing R] (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (th M : Fin N → ℤ) : Prop :=
  {G : MvPolynomial (Fin N × Fin n) R | G ∈ Pol R n B ∧ ∀ i : Fin N,
      ((th i : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} G ∧ lam1S LL {j | j ≤ i} G ≤ ((M i : ℤ) : WithBot ℤ)} =
    (Submodule.span R {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧
      (∀ i : Fin N, th i ≤ P.mu i.succ (lastIdx n) ∧ P.mu i.succ 0 ≤ M i) ∧ G = Psi R P.mu I} : Set _)

def DefiniteRankOne (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (N n : ℕ) [NeZero n] (LL : Letters (Fin N))
    (B : Fin N → ℕ) (th M : Fin N → ℤ), A3at O N n LL B th M ∧ A3at (FF O) N n LL B th M

def CondC {N r K : ℕ} [NeZero r] [NeZero K] (LL : Letters (Fin N)) (nu : Fin (N + 1) → Fin r → ℤ)
    (ka : Fin (N + 1) → Fin K → ℤ) (i : Fin N) : Prop :=
  if LL.vec i then ka i.succ 0 ≤ nu i.castSucc (lastIdx r) else ka i.castSucc 0 ≤ nu i.succ (lastIdx r)

def RotatedSumBound (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (N r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ), N + r ≤ K →
    ∀ (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ),
      (∃ P : PPath (r + K) N LL B, P.mu = joinPT nu ka) ↔
      ∃ b' b'' : Fin N → ℕ, (∀ i, b' i + b'' i = B i) ∧ (∃ P1 : PPath r N LL b', P1.mu = nu) ∧
        (∃ P2 : PPath K N LL b'', P2.mu = ka) ∧ ∀ i, CondC LL nu ka i

def PathWeightComponents (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (N r K : ℕ) [NeZero r] [NeZero K]
    (LL : Letters (Fin N)) (B : Fin N → ℕ) (om : Fin N → ℕ), N + r ≤ K → StrictAnti om → (∀ i, 0 < om i) →
    ∀ (P : PPath (r + K) N LL B) (c : ℤ) (J : Finset (Fin (r + K))),
      (∀ m ∈ (Kcol O P.mu c N J).support, oc om P.mu c ≤ monWt LL om m) ∧
      weightedHomogeneousComponent (symWt (r := r) (K := K) LL om) (oc om P.mu c) (Kcol O P.mu c N J) =
        plTanCol O P.mu c J

def Saturated {O σ : Type*} [CommRing O] (X : Submodule O (MvPolynomial σ O)) : Prop :=
  ∀ (f : MvPolynomial σ O) (a : O), a ≠ 0 → a • f ∈ X → f ∈ X

def XXZ (O : Type) [CommRing O] {N r K : ℕ}
    (PP : Set ((Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ))) :
    Submodule O (MvPolynomial (Fin N × Fin (r + K)) O) :=
  Submodule.span O {G | ∃ q ∈ PP, ∃ I' I'', IsSt q.1 I' ∧ IsSt q.2 I'' ∧ G = PsiPl O q.1 I' * PsiTan O q.2 I''}

open Classical in

def glOpsE (F : Type*) [Field F] {N m k : ℕ} (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k) :
    GLOps m F (MvPolynomial (Fin N × Fin k) F) :=
  fun a b => ∑ l : Fin N,
    if l ∈ S then
      (if LL.vec l then (LinearMap.mulLeft F (X (l, e a))) ∘ₗ (pderiv (l, e b)).toLinearMap
       else -((LinearMap.mulLeft F (X (l, e b))) ∘ₗ (pderiv (l, e a)).toLinearMap))
    else 0

def jointType (F : Type*) [Field F] {N r K : ℕ} (LL : Letters (Fin N)) (nu : Fin (N + 1) → Fin r → ℤ)
    (ka : Fin (N + 1) → Fin K → ℤ) : Submodule F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  ⨅ i : Fin (N + 1), isoSub (glOpsE F LL {j | j.val < i.val} (Fin.castAdd K)) (nu i) ⊓
    isoSub (glOpsE F LL {j | j.val < i.val} (Fin.natAdd r)) (ka i)

inductive PathInequality (N : ℕ) where
  | nuGe (i : Fin (N + 1)) (th : ℤ)
  | kaLe (i : Fin (N + 1)) (M : ℤ)
  | mix (j i : Fin (N + 1)) (m : ℤ)

def PathInequality.Sat {N r K : ℕ} [NeZero r] [NeZero K] (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) :
    PathInequality N → Prop
  | .nuGe i th => th ≤ nu i (lastIdx r)
  | .kaLe i M => ka i 0 ≤ M
  | .mix j i m => ka j 0 + m ≤ nu i (lastIdx r)

def ConclusionB3 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (N r K : ℕ) [NeZero r] [NeZero K]
    (LL : Letters (Fin N)) (B : Fin N → ℕ) (om : Fin N → ℕ), N + r ≤ K → StrictAnti om → (∀ i, 0 < om i) →
    ∀ PP : Set ((Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ)),
      (∀ q ∈ PP, ∃ P : PPath (r + K) N LL B, P.mu = joinPT q.1 q.2) →
      Saturated (XXZ O PP) ∧
      (∀ q ∈ PP, ∀ (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)), IsSt q.1 I' → IsSt q.2 I'' →
        ∃ I : ℤ → Finset (Fin (r + K)),
          (∀ m ∈ (Psi O (joinPT q.1 q.2) I).support,
            (∑ c ∈ colRange (joinPT q.1 q.2), oc om (joinPT q.1 q.2) c) ≤ monWt LL om m) ∧
          weightedHomogeneousComponent (symWt (r := r) (K := K) LL om)
              (∑ c ∈ colRange (joinPT q.1 q.2), oc om (joinPT q.1 q.2) c) (Psi O (joinPT q.1 q.2) I) =
            PsiPl O q.1 I' * PsiTan O q.2 I'') ∧
      (∀ L : List (PathInequality N),
        PP = {q | (∃ P : PPath (r + K) N LL B, P.mu = joinPT q.1 q.2) ∧ ∀ e ∈ L, e.Sat q.1 q.2} →
        (XXZ O PP : Set _) = {f | MvPolynomial.map (algebraMap O (KK O)) f ∈
          ⨆ q ∈ PP, jointType (KK O) LL q.1 q.2})

def CoefficientDependence (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p f) O] (S : UniformizedDVR p O), 5 ≤ p → 1 ≤ f →
    ∀ (r K : ℕ) (ι : Type) (LL : LiftLetters ι) (g g' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)),
      IsGLW g → IsGLW g' →
      (ratPlane p f r g = ratPlane p f r g' →
        ∀ F : MvPolynomial (ι × Fin (r + K)) (KK O), InWjRg p f O S.w r LL g F 0 ↔ InWjRg p f O S.w r LL g' F 0) ∧
      ∀ F : MvPolynomial (ι × Fin (r + K)) (KK O), InA F →
        ∀ m, ∃ a : O, (liftSubst p f O S.w r LL g F).coeff m = algebraMap O (KK O) (S.w ^ degUS LL r m * a)

def CanonicalTranslateJetIdentity (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF p f) O] (S : UniformizedDVR p O), 5 ≤ p → 1 ≤ f → S.SqP →
    ∀ (N r K : ℕ) [NeZero N] [NeZero r] [NeZero K] (LL : LiftLetters (Fin N)) (B : Fin N → ℕ) (z : ℤ),
      N + r ≤ K → Monotone LL.pos → (∀ i, LL.pos i ≤ z) →
      ∀ (P : PPath (r + K) N LL.toLetters B) (g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)), IsGLW g →
      ∀ c : ℤ, (∀ i j : Fin N, i < j → IsUsed P.mu c i → IsCostly P.mu c j → LL.pos i < LL.pos j) →
      ∀ J : Finset (Fin (r + K)),
        InA (KKc p f (O := O) LL g z P.mu c J) ∧
        (∀ m ∈ (KKc p f (O := O) LL g z P.mu c J).support, ∀ i, IsUsed P.mu c i →
          multideg m i = p ^ (z - LL.pos i).toNat) ∧
        (∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f), IsGLW g' →
          InWjRg p f O S.w r LL g' (KKc p f (O := O) LL g z P.mu c J)
            (oc (fun i => p ^ (z - LL.pos i).toNat) P.mu c)) ∧
        InWj S.w (liftSubst p f O S.w r LL g (KKc p f (O := O) LL g z P.mu c J) -
            C (algebraMap O (KK O) S.w ^ oc (fun i => p ^ (z - LL.pos i).toNat) P.mu c) *
              powSubst p LL z (plTanCol O P.mu c J))
          (oc (fun i => p ^ (z - LL.pos i).toNat) P.mu c + 1) ∧
        oc (fun i => p ^ (z - LL.pos i).toNat) P.mu c ≤ 2 * p ^ (z - LL.pos 0).toNat

def Conclusion2 (D : Formalism.BasicNotions.D7) : Prop :=
  AutomorphicSideConclusion D ∧ DefiniteRankOne D ∧ RotatedSumBound D ∧ PathWeightComponents D ∧ ConclusionB3 D ∧ CoefficientDependence D ∧ CanonicalTranslateJetIdentity D

def PairPath {N r K : ℕ} (LL : Letters (Fin N)) (B : Fin N → ℕ) (nu : Fin (N + 1) → Fin r → ℤ)
    (ka : Fin (N + 1) → Fin K → ℤ) : Prop :=
  ∃ b' b'' : Fin N → ℕ, (∀ i, b' i + b'' i = B i) ∧ (∃ P1 : PPath r N LL b', P1.mu = nu) ∧
    ∃ P2 : PPath K N LL b'', P2.mu = ka

def PairedPathIndependence (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N r K : ℕ) [NeZero r] [NeZero K]
    (LL : Letters (Fin N)) (B : Fin N → ℕ),
    (LinearIndependent O (fun x : {x : ((Fin (N + 1) → Fin r → ℤ) × (ℤ → Finset (Fin r))) ×
          ((Fin (N + 1) → Fin K → ℤ) × (ℤ → Finset (Fin K))) //
          PairPath LL B x.1.1 x.2.1 ∧ IsSt x.1.1 x.1.2 ∧ IsSt x.2.1 x.2.2} =>
        PsiPl (K := K) O x.1.1.1 x.1.1.2 * PsiTan (r := r) O x.1.2.1 x.1.2.2) ∧
      Submodule.span O {G | ∃ (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) (I' : ℤ → Finset (Fin r))
          (I'' : ℤ → Finset (Fin K)), PairPath LL B nu ka ∧ IsSt nu I' ∧ IsSt ka I'' ∧
          G = PsiPl O nu I' * PsiTan O ka I''} = Pol O (r + K) B) ∧
    ∀ (pi' : Fin (N + 1) → Set (Fin r → ℤ)) (pi'' : Fin (N + 1) → Set (Fin K → ℤ)),
      (∀ i, DomLowerSet (pi' i)) → (∀ i, DomLowerSet (pi'' i)) →
      {f : MvPolynomial (Fin N × Fin (r + K)) O | f ∈ Pol O (r + K) B ∧ MvPolynomial.map (algebraMap O (KK O)) f ∈
          ⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) | ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i},
            jointType (KK O) LL q.1 q.2} =
        (Submodule.span O {G | ∃ (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ)
          (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)), PairPath LL B nu ka ∧
          (∀ i, nu i ∈ pi' i ∧ ka i ∈ pi'' i) ∧ IsSt nu I' ∧ IsSt ka I'' ∧
          G = PsiPl O nu I' * PsiTan O ka I''} : Set _)

def PathBasisOverRing (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (R : Type) [CommRing R] (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ),
    LinearIndependent R (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} =>
      Psi R x.1.1.mu x.1.2) ∧
    Submodule.span R {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi R P.mu I} =
      Pol R n B

def FirstLettersLowerSet (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (F : Type) [Field F] (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : Fin (N + 1))
    (pi : Set (Fin n → ℤ)), DomLowerSet pi → ∀ G ∈ Pol F n B,
    (G ∈ Submodule.span F {H | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ P.mu i ∈ pi ∧
        H = Psi F P.mu I} ↔
      ∀ mu ∈ polWts LL {j : Fin N | j.val < i.val} (polGenSub F LL {j : Fin N | j.val < i.val} G),
        Dominant mu → mu ∈ pi)

def dualOps {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) :
    GLOps n K (Module.Dual K V) := fun a b => -(LinearMap.dualMap (E a b))

def WeylDualityLattice (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    (Delta (O := O) E v : Set V) =
      {x | ∀ φ ∈ Nabla (O := O) (dualOps E) (dualWt mu) v', φ x ∈ Set.range (algebraMap O (KK O))}

def PathColumnBasis (D : Formalism.BasicNotions.D7) : Prop := HyperplaneRank D

theorem path_basis_of_field_basis (D : Formalism.BasicNotions.D7) (h : PathBasisOverRing D) : PathColumnBasis D := by
  unfold PathColumnBasis HyperplaneRank
  intro O _ _ _ N n _ LL B
  exact h O N n LL B

def AdmB (D : Formalism.BasicNotions.D7) : Prop :=
  PathPairCorrespondence D ∧ admB2 D ∧ admB3 D ∧ ColumnFamilyLowerSet D ∧ GenericProjectionCriterion D ∧ ColumnFamilyClosure D ∧ TensorColumnFamily D ∧ BranchingColumnFamily D ∧ GlobalSectionsSchur D ∧ BracketPolynomialSpan D ∧
    GradedLatticeStable D ∧ NestedTypeBound D ∧ TypeDecompositionsCommute D ∧ JointComponentsPaths D ∧ SaturatedLowerSetSpan D ∧ PairedPathIndependence D ∧ PathBasisOverRing D ∧ FirstLettersLowerSet D ∧ WeylDualityLattice D ∧ PathColumnBasis D

def HodgeTateFromSandwich (D : Formalism.BasicNotions.D7) : Prop := admitted D → ValuationLemmaField D → AdmB D → Conclusion2 D

def Stmt (D : Formalism.BasicNotions.D7) : Prop := admitted D → AdmB D → Conclusion1 D ∧ Conclusion2 D

theorem statement_of_degree_and_bound (D : Formalism.BasicNotions.D7) (h1 : IntegralityFromMetric D) (h2 : HodgeTateFromSandwich D) : Stmt D := by
  intro hA hB
  have p1 := h1 hA
  exact ⟨p1, h2 hA p1.2.1 hB⟩

def SecondPartClosed (D : Formalism.BasicNotions.D7) : Prop := HodgeTateFromSandwich D

def ClosedFormOfAdmitted (D : Formalism.BasicNotions.D7) : Prop := Stmt D

def AdmBF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), AdmB (Fm.D x i)

def ValuationLemmaFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ i : Fm.Ix x, ValuationLemmaField (Fm.D x i)

def Conclusion2Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i)

def SecondPartFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → ValuationLemmaFamily Fm → AdmBF Fm → Conclusion2Family Fm

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → AdmBF Fm → Conclusion1Family Fm ∧ Conclusion2Family Fm

def SecondPartFamilyClosed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := SecondPartFamily Fm

def FamilyClosedForm {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := KudlaFamilyStatement Fm

end Formalism.MainNotions.CovariantDegrees
