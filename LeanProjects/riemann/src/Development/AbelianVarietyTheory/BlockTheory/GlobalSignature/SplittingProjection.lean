import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SatakeDualWeyl.StatementC
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsSplitting (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)) ∧
  (∀ x, x ∈ intV E v ↔
    (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F)

variable {v : HeightOneSpectrum (𝓞 F)}
  (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

def prP : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom

def prPbar : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.snd _ _).comp φ.toRingHom

def primeOf (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) : Ideal (intV E v) :=
  Ideal.span {a : intV E v | Valued.v (p a) < 1}

def partOf {n : Type} (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (Λ : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F)) :
    Submodule (v.adicCompletionIntegers F) (n → v.adicCompletion F) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : n → E ⊗[F] v.adicCompletion F => fun i => p (x i)) '' (Λ : Set _))

abbrev locLat {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (n → E)) : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

theorem mem_primeOf_prP {σ : E →ₐ[F] E} (hφ : IsSplitting σ v φ) (a : intV E v) :
    a ∈ primeOf (prP φ) ↔ Valued.v (prP φ a) < 1 := by
  refine ⟨fun h => ?_, fun h => Ideal.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    have hc : Valued.v (prP φ c) ≤ 1 := ((hφ.2.2 c).1 c.2).1
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc zero_le' hx

theorem primeOf_prP_ne_top {σ : E →ₐ[F] E} (hφ : IsSplitting σ v φ) : primeOf (prP φ) ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one, mem_primeOf_prP φ hφ]
  simp

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev dualLb (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧ N ≤ dualLb L ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → locLat v N = locLat v L.Lb

def LocalAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal)
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=

  IsSplitting sp.cm.sig v φ ∧

  (∀ x : locLat v (dualLb L), (∀ i, prP φ (x.1 i) = 0) → L.fT v h x = 0) ∧

  Nonempty ((locLat v (dualLb L) ⧸ (locLat v L.Lb).submoduleOf (locLat v (dualLb L))) ≃ₗ[intV E v]
    (intV E v ⧸ primeOf (prP φ)) × (intV E v ⧸ primeOf (prPbar φ))) ∧

  partOf (prP φ) (locLat v N) = partOf (prP φ) (locLat v (dualLb L)) ∧
  partOf (prPbar φ) (locLat v N) = partOf (prPbar φ) (locLat v L.Lb) ∧

  (∀ g' : GL (Fin R.k) (v.adicCompletion F),
    ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (prP φ) g.1 = g') ∧

  (∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
    g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ bc (prP φ) g ∈ stabGL (partOf (prP φ) (locLat v N))) ∧

  (∃ b : GL (Fin R.k) (v.adicCompletion F),
    (∀ y : Fin R.k → v.adicCompletion F,
      (b : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ y ∈ partOf (prP φ) (locLat v N) ↔
        ∀ i, y i ∈ v.adicCompletionIntegers F) ∧
    ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (prP φ) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range) ∧

  ∃ (f : partOf (prP φ) (locLat v N) →ₗ[v.adicCompletionIntegers F]
      IsLocalRing.ResidueField (v.adicCompletionIntegers F))
    (ε : L.fM v h ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F)),
    (∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP φ a →
      ∀ m, ε (a • m) = a' • ε m) ∧
    (∀ (x : locLat v (dualLb L)) (y : partOf (prP φ) (locLat v N)),
      (∀ i, y.1 i = prP φ (x.1 i)) → f y = ε (L.fT v h x)) ∧
    f ≠ 0 ∧
    (∀ y, f ((A.T : v.adicCompletionIntegers F) • y) = 0) ∧
    (∀ y, f y = 0 ↔ y.1 ∈ partOf (prP φ) (locLat v L.Lb)) ∧
    ∀ g, g ∈ L.Uloc v ↔
      g ∈ levelVL sp.cm.sig sp.gram0 v N ∧ bc (prP φ) g ∈ stabFun (partOf (prP φ) (locLat v N)) f

def HasOverLattice (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  (∀ i : Fin 2, A.T ≠ gp i) ∧
  ∃ N : Submodule (𝓞 E) (Fin R.k → E), IsOverLattice L N ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal), ∃ φ, LocalAtT L N v h φ) ∧
    (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
    L.U ≤ levelAfL sp.cm.sig sp.gram0 N

def IndexAtT (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ N, IsOverLattice L N → ∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal) φ,
    LocalAtT L N v h φ → (L.Uloc v).relIndex (levelVL sp.cm.sig sp.gram0 v N) = A.T ^ R.k - 1

end Level

def SelfDualOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → HasOverLattice (Lv u)

def IndexOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → IndexAtT (Lv u)

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
