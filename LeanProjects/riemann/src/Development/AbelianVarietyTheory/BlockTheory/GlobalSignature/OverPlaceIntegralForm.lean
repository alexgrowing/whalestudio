import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SatakeDualWeyl.StatementC
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

def stabRow {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (φ : n → A) :
    Subgroup (GL n A) where
  carrier := {g | φ ᵥ* (g : Matrix n n A) = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : φ ᵥ* (a : Matrix n n A) = φ := ha
    have hb' : φ ᵥ* (b : Matrix n n A) = φ := hb
    show φ ᵥ* ((a * b : GL n A) : Matrix n n A) = φ
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha', hb']
  inv_mem' := by
    intro g hg
    have hg' : φ ᵥ* (g : Matrix n n A) = φ := hg
    show φ ᵥ* ((g⁻¹ : GL n A) : Matrix n n A) = φ
    conv_lhs => rw [← hg']
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]

example {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] :
    stabRow (0 : n → A) = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  show (0 : n → A) ᵥ* (g : Matrix n n A) = 0
  simp

example : (-1 : GL (Fin 1) ℚ) ∉ stabRow (fun _ : Fin 1 => (1 : ℚ)) := by
  intro h
  have h' : (fun _ : Fin 1 => (1 : ℚ)) ᵥ* ((-1 : GL (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ) =
      fun _ => 1 := h
  have := congrFun h' 0
  simp [Matrix.vecMul, dotProduct] at this
  norm_num at this

section Local

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def toIntV : 𝓞 E →+* intV E v :=
  ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict (intV E v)
    (fun a => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E a, ⟨a, rfl⟩⟩, rfl⟩))

variable {E} {n : Type}

abbrev latV (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

variable {v}

def pr₁ (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (x : n → E ⊗[F] v.adicCompletion F) : n → v.adicCompletion F := fun i => (s (x i)).1

def pr₂ (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (x : n → E ⊗[F] v.adicCompletion F) : n → v.adicCompletion F := fun i => (s (x i)).2

def IsSplitting (σ : E →ₐ[F] E) (P Pb : HeightOneSpectrum (𝓞 E))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  P ≠ Pb ∧
  v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * Pb.asIdeal ∧
  (∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, s (sigR σ (v.adicCompletion F) x) = swapR _ (s x)) ∧
  (∀ x, x ∈ intV E v ↔
    (s x).1 ∈ v.adicCompletionIntegers F ∧ (s x).2 ∈ v.adicCompletionIntegers F) ∧
  (∀ a : 𝓞 E, a ∈ P.asIdeal ↔ Valued.v (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 < 1) ∧
  (∀ a : 𝓞 E, a ∈ Pb.asIdeal ↔ Valued.v (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1)

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev baseDual (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def OverAt (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) : Prop :=
  ∃ (P Pb : HeightOneSpectrum (𝓞 E))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),

    IsSplitting sp.cm.sig P Pb s ∧

    (∀ x : latV v (baseDual L), pr₁ s (x : Fin R.k → _) = 0 → L.fT v hv x = 0) ∧

    (∀ x : latV v (baseDual L),
      L.fT v hv x = 0 ↔ pr₁ s (x : Fin R.k → _) ∈ pr₁ s '' (latV v L.Lb : Set (Fin R.k → _))) ∧

    Nonempty ((latV v (baseDual L) ⧸ (latV v L.Lb).submoduleOf (latV v (baseDual L))) ≃ₗ[intV E v]
      ((intV E v ⧸ P.asIdeal.map (toIntV E v)) × (intV E v ⧸ Pb.asIdeal.map (toIntV E v)))) ∧

    pr₁ s '' (latV v N : Set (Fin R.k → _)) = pr₁ s '' (latV v (baseDual L) : Set (Fin R.k → _)) ∧
    pr₂ s '' (latV v N : Set (Fin R.k → _)) = pr₂ s '' (latV v L.Lb : Set (Fin R.k → _)) ∧

    (∃ hle : latV v N ≤ latV v (baseDual L),
      (L.fT v hv).comp (Submodule.inclusion hle) ≠ 0 ∧
      L.Uloc v = levelVL sp.cm.sig sp.gram0 v N ⊓
        stabFun (latV v N) ((L.fT v hv).comp (Submodule.inclusion hle))) ∧

    ∃ (h : GL (Fin R.k) (v.adicCompletion F))
      (φ : Fin R.k → v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
      (e : L.fM v hv ≃+
        v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)),
      pr₁ s '' (latV v N : Set (Fin R.k → _)) =
        Set.range (fun y : Fin R.k → v.adicCompletionIntegers F =>
          (h : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ fun i => (y i : v.adicCompletion F)) ∧
      Set.BijOn (fun g : GL (Fin R.k) (E ⊗[F] v.adicCompletion F) =>
          h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) g * h)
        (levelVL sp.cm.sig sp.gram0 v N)
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range ∧
      φ ≠ 0 ∧
      (∀ (x : latV v (baseDual L)) (y : Fin R.k → v.adicCompletionIntegers F),
        pr₁ s (x : Fin R.k → _) =
          (h : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ (fun i => (y i : v.adicCompletion F)) →
        e (L.fT v hv x) = ∑ i, φ i * Ideal.Quotient.mk _ (y i)) ∧
      ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
        g ∈ L.Uloc v ↔ h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) g * h ∈
          congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (stabRow φ)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧
  Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧
  (N : Set (Fin R.k → E)) ⊆ dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb ∧
  (∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → latV v N = latV v L.Lb) ∧
  (∀ (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal), OverAt L N v hv) ∧
  L.U ≤ levelAfL sp.cm.sig sp.gram0 N

end Level

def OverLatticeAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T →
    (∀ i : Fin 2, (D.mem u).A.T ≠ D.host.g i) ∧
    ∃ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsOverLattice (Lv u) N

def OverLattice : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), OverLatticeAt D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm

end
