import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg
open scoped TensorProduct ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianLocalData

variable {F : Type} [Field F] [NumberField F]

abbrev Pl (F : Type) [Field F] [NumberField F] : Type := HeightOneSpectrum (𝓞 F)

abbrev Ev (E : Type) [Field E] [Algebra F E] (v : Pl F) : Type := Fv F v ⊗[F] E

def IsDiffGen (v : Pl F) (δ : Fv F v) : Prop :=
  ∀ y : Fv F v, (∃ a ∈ v.adicCompletionIntegers F, y = δ * a) ↔
    y ∈ AddSubgroup.closure {z : Fv F v | ∃ a ∈ v.adicCompletionIntegers F,
      ∃ d ∈ differentIdeal ℤ (𝓞 F), z = a * algebraMap F (Fv F v) (d : F)}

open scoped Classical in

def lev (g₁ g₂ : ℕ) (v : Pl F) : ℕ :=
  if (g₁ : 𝓞 F) ∈ v.asIdeal then g₁ else if (g₂ : 𝓞 F) ∈ v.asIdeal then g₂ else 1

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

def Ov (E : Type) [Field E] [NumberField E] [Algebra F E] (v : Pl F) : Subring (Ev E v) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def Pv (E : Type) [Field E] [NumberField E] [Algebra F E] (v : Pl F) : AddSubgroup (Ev E v) :=
  AddSubgroup.closure {y | ∃ a : Fv F v, Valued.v a < 1 ∧ ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def locLat (v : Pl F) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → Ev E v) :=
  AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x ∈ Λ, y = fun i => a ⊗ₜ[F] x i}

def PrimV (v : Pl F) {n a : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (X : Fin a → Fin n → Ev E v) :
    Prop :=
  ∃ e : Fin n → Fin n → Ev E v, LinearIndependent (Ev E v) e ∧
    (∀ y, y ∈ locLat v Λ ↔ ∃ c : Fin n → Ev E v, (∀ j, c j ∈ Ov E v) ∧ y = ∑ j, c j • e j) ∧
    ∃ s : Fin a ↪ Fin n, ∀ b, X b = e (s b)

def aEnt (E : Type) [Field E] [Algebra F E] {v : Pl F} (δ : Fv F v) (r : ℕ) (b : Fin (r + 1)) :
    Ev E v := (δ⁻¹ ^ (r - (b : ℕ))) ⊗ₜ[F] (1 : E)

def locFr {v : Pl F} (δ : Fv F v) {n r : ℕ} (X : Fin (r + 1) → Fin n → Ev E v) :
    Fin (r + 1) → Fin n → Ev E v := fun b => aEnt E δ r b • X b

def gInv (E : Type) [Field E] [Algebra F E] (v : Pl F) (g : ℕ) : Ev E v :=
  inclR (Fv F v) ((g : E)⁻¹)

def TFE (E : Type) [Field E] [Algebra F E] (r : ℕ) (T : 𝓞 F) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E := TF r (algebraMap F E (T : F))

def yV {v : Pl F} (δ : Fv F v) (g : ℕ) {n r : ℕ} (X X' : Fin (r + 1) → Fin n → Ev E v) :
    Fin (r + 1) → Fin n → Ev E v := fun b => gInv E v g • (locFr δ X' b - locFr δ X b)

section Loc

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
  (r : ℕ) (T T' : 𝓞 F) {v : Pl F} (δ : Fv F v) (g : ℕ)

def Om : Set ((Fin (r + 1) → Fin n → Ev E v) × (Fin (r + 1) → Fin n → Ev E v)) :=
  {p | gramR (Fv F v) σ J p.1 = (TFE E r T).map (inclR (Fv F v)) ∧
    gramR (Fv F v) σ J p.2 = (TFE E r T').map (inclR (Fv F v)) ∧
    PrimV v Λ (locFr δ p.1) ∧ PrimV v Λ (locFr δ p.2) ∧ ∀ b, yV δ g p.1 p.2 b ∈ locLat v Λ}

def OmGen : Set (Fin ((r + 1) + (r + 1)) → Fin n → Ev E v) :=
  {X | ((fun b => X (Fin.castAdd (r + 1) b)), (fun b => X (Fin.natAdd (r + 1) b))) ∈
      Om σ J Λ r T T' δ g ∧
    PrimV v Λ (Fin.append (locFr δ fun b => X (Fin.castAdd (r + 1) b))
      (yV δ g (fun b => X (Fin.castAdd (r + 1) b)) (fun b => X (Fin.natAdd (r + 1) b))))}

def zLoc (Z : Fin (r + 1) → Fin (r + 1) → Ev E v) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ev E v) :=
  Matrix.of fun a b => sigR (Fv F v) σ (aEnt E δ r a) * Z a b * aEnt E δ r b

def y0 (Z : Fin (r + 1) → Fin (r + 1) → Ev E v) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ev E v) :=
  gInv E v g • (zLoc σ r δ Z - (TFE E r T).map (inclR (Fv F v)))

def ZZ : Set (Fin (r + 1) → Fin (r + 1) → Ev E v) :=
  {Z | (∀ a b, y0 σ r T δ g Z a b ∈ Ov E v) ∧
    ∀ a b, gInv E v g * (y0 σ r T δ g Z a b + sigR (Fv F v) σ (y0 σ r T δ g Z b a) -
      gInv E v g * inclR (Fv F v) (TFE E r T' a b - TFE E r T a b)) ∈ Ov E v}

def T3 (Z : Fin (r + 1) → Fin (r + 1) → Ev E v) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) (Ev E v) :=
  Matrix.fromBlocks ((TFE E r T).map (inclR (Fv F v))) (y0 σ r T δ g Z)
    (cT (sigR (Fv F v) σ) (y0 σ r T δ g Z))
    ((gInv E v g * gInv E v g) • ((TFE E r T').map (inclR (Fv F v)) - zLoc σ r δ Z -
      cT (sigR (Fv F v) σ) (zLoc σ r δ Z) + (TFE E r T).map (inclR (Fv F v))))

end Loc

def corankV (v : Pl F) {ι : Type} [Fintype ι] (S : Matrix ι ι (Ev E v)) : ℕ :=
  sInf {c | ∃ G : Matrix ι (Fin c) (Ev E v), (∀ a j, G a j ∈ Ov E v) ∧
    ∀ x : ι → Ev E v, (∀ a, x a ∈ Ov E v) →
      ∃ (u : ι → Ev E v) (w : Fin c → Ev E v), (∀ a, u a ∈ Ov E v) ∧ (∀ j, w j ∈ Ov E v) ∧
        ∀ a, (x - S *ᵥ u - G *ᵥ w) a ∈ Pv E v}

open scoped Classical in

def aP (E : Type) [Field E] [Algebra F E] (v : Pl F) (n r : ℕ) (T : 𝓞 F) : ℝ :=
  GlobalTheory.SgDen.densF (Ideal.absNorm v.asIdeal) (GlobalTheory.SgDen.eta (Ev E v)) n (r + 1)
    (if T ∈ v.asIdeal then r + 1 else r)

def densClosed (σ : E →ₐ[F] E) (n r : ℕ) (T T' : 𝓞 F) {v : Pl F} (δ : Fv F v) (g : ℕ)
    (Z : Fin (r + 1) → Fin (r + 1) → Ev E v) : ℝ :=
  GlobalTheory.SgDen.densF (Ideal.absNorm v.asIdeal) (GlobalTheory.SgDen.eta (Ev E v)) n (2 * r + 2)
               (corankV v (T3 σ r T T' δ g Z)) /
    (if g = 1 then aP E v n r T * aP E v n r T' else aP E v n r T)

def T2 (σ : E →ₐ[F] E) (r : ℕ) (T T' : 𝓞 F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin ((r + 1) + (r + 1))) (Fin ((r + 1) + (r + 1))) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (TFE E r T) Z (cT (σ : E →+* E) Z) (TFE E r T'))

omit [NumberField F] [NumberField E] in
theorem TFE_herm (σ : E →ₐ[F] E) (r : ℕ) (T : 𝓞 F) (a b : Fin (r + 1)) :
    σ (TFE E r T b a) = TFE E r T a b := by
  unfold TFE TF
  by_cases h : a = b
  · subst h
    by_cases h' : a = Fin.last r <;> simp [h']
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem blockMatrix_hermitian {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (r : ℕ) (T T' : 𝓞 F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin ((r + 1) + (r + 1))) :
    σ (T2 σ r T T' Z b a) = T2 σ r T T' Z a b := by
  unfold T2
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm a with a | a <;> rcases finSumFinEquiv.symm b with b | b <;>
    simp [cT, TFE_herm, sig_sig h]

section Meas

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def IsOm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (ψR : R → ℂ) (a : ℕ)
    (fib : HermR R σ a → Measure (Fin a → Fin n → R ⊗[F] E)) : Prop :=
  ∃ (μ : Measure (Fin a → Fin n → R ⊗[F] E)) (ν : Measure (HermR R σ a)),
    SdW F E σ n J R ψR a μ ∧ SdHerm F E σ R ψR a ν ∧
      IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ fib

def IsProdG (μ : Measure (HA (AF F) σ J)) (μi : Measure (HA (Ainf F) σ J))
    (μf : Measure (HA (Af F) σ J)) : Prop :=
  ∀ (B : Set (HA (Ainf F) σ J)) (C : Set (HA (Af F) σ J)), MeasurableSet B → MeasurableSet C →
    μ {h | (∃ b ∈ B, ((HA.mat (Ainf F) σ J b : GL (Fin n) (Ainf F ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
        ((HA.mat (AF F) σ J h : GL (Fin n) (AF F ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
            (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))) ∧
      ∃ c ∈ C, ((HA.mat (Af F) σ J c : GL (Fin n) (Af F ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) = Formalism.MainNotions.StandardLattice.finMat σ J h} = μi B * μf C

def Kf (Λ : Submodule (𝓞 E) (Fin n → E)) : Set (HA (Af F) σ J) :=
  {h | ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔
    ((HA.mat (Af F) σ J h : GL (Fin n) (Af F ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E))}

def IsStabMeas {a : ℕ} (μG : Measure (HA (Ainf F) σ J))
    (ω : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (X₀ : Fin a → Fin n → Ainf F ⊗[F] E)
    (μB : Measure (MulAction.stabilizer (HA (Ainf F) σ J) X₀)) : Prop :=
  μB.IsHaarMeasure ∧ ∀ φ : HA (Ainf F) σ J → ℝ≥0∞, Measurable φ →
    ∀ s : (Fin a → Fin n → Ainf F ⊗[F] E) → HA (Ainf F) σ J,
      (∀ y, (∃ g : HA (Ainf F) σ J, g • X₀ = y) → s y • X₀ = y) →
      ∫⁻ g, φ g ∂μG = ∫⁻ y, ∫⁻ b, φ (s y * (b : HA (Ainf F) σ J)) ∂μB ∂ω

def IsRho (r : ℕ) (T T' : 𝓞 F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (μG : Measure (HA (Ainf F) σ J))
    (ω : Measure (Fin ((r + 1) + (r + 1)) → Fin n → Ainf F ⊗[F] E)) (ρ : ℝ) : Prop :=
  0 < ρ ∧
  AllSome (fun p => p ∈ XZ (σ : E →+* E) J (algebraMap F E (T : F)) (algebraMap F E (T' : F)) Z)
    fun p => AllSome (IsStabMeas σ J μG ω
        (ratTup (F := F) (Ainf F) (Fin.append (fun b i => p.1 i b) (fun b i => p.2 i b))))
      fun μB => μB Set.univ = ENNReal.ofReal ρ⁻¹

end Meas

def AbsConv {ι : Type} (x : ι → ℝ) : Prop := Summable fun v => |x v - 1|

def SplitsCompl (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E

def HasSig {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (p q : ℕ) : Prop :=
  p + q = n ∧ ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ,
    Aᴴ * Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)) * A = J.map τ

def MassFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ), Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
  ∀ (k r n : ℕ), 3 ≤ k → n = k + 2 * r + 1 →
  ∀ (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → HasSig J (k + r) (r + 1) →
  ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ →
  ∀ (g₁ g₂ : ℕ), g₁ ≠ g₂ → SplitsCompl E g₁ → SplitsCompl E g₂ →
  ∀ (T T' : 𝓞 F), GlobalTheory.SgGlob.TotPos (algebraMap F E (T : F)) →
    GlobalTheory.SgGlob.TotPos (algebraMap F E (T' : F)) →
    ((g₁ * g₂ : ℕ) : 𝓞 F) ^ 2 ∣ T - 1 → ((g₁ * g₂ : ℕ) : 𝓞 F) ^ 2 ∣ T' - 1 →

  AllSome (fun δ : ∀ v : Pl F, Fv F v => ∀ v, IsDiffGen v (δ v)) fun δ =>
  AllSome (IsCharAF F) fun ψ =>
  AllSome (fun μi : Measure (HA (Ainf F) σ J) => μi.IsHaarMeasure) fun μi =>
  AllSome (fun μf : Measure (HA (Af F) σ J) => μf.IsHaarMeasure) fun μf =>
  AllSome (fun μ : Measure (HA (AF F) σ J) => μ.IsHaarMeasure ∧ IsProdG σ J μ μi μf) fun μ =>
  AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) fun 𝓕 =>

  AllSome (IsOm σ J (Ainf F) (psiInf F ψ) ((r + 1) + (r + 1))) fun ωi =>
  AllSome (fun ω₂ : ∀ v : Pl F, HermR (Fv F v) σ ((r + 1) + (r + 1)) →
      Measure (Fin ((r + 1) + (r + 1)) → Fin n → Ev E v) =>
    ∀ v, IsOm σ J (Fv F v) (psiV F ψ v) ((r + 1) + (r + 1)) (ω₂ v)) fun ω₂ =>
  AllSome (fun ω₁ : ∀ v : Pl F, HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Ev E v) =>
    ∀ v, IsOm σ J (Fv F v) (psiV F ψ v) (r + 1) (ω₁ v)) fun ω₁ =>
  AllSome (fun dZ : ∀ v : Pl F, Measure (Fin (r + 1) → Fin (r + 1) → Ev E v) =>
    ∀ v, SdW F E σ (r + 1) 1 (Fv F v) (psiV F ψ v) (r + 1) (dZ v)) fun dZ =>
  let G := fun Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E =>
    Gq (σ : E →+* E) (algebraMap F E (T : F)) (algebraMap F E (T' : F)) Z
  let mass := fun Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E =>
    GlobalTheory.SgGlob.Mass (σ : E →+* E) J (algebraMap F E (T : F)) (algebraMap F E (T' : F)) (g₁ * g₂) Z
  let Zv := fun (v : Pl F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) =>
    (fun a b => inclR (Fv F v) (Z a b) : Fin (r + 1) → Fin (r + 1) → Ev E v)
  let rho := fun (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (ρ : ℝ) =>
    IsRho σ J r T T' Z μi (ωi (hermOf (Ainf F) σ (T2 σ r T T' Z) (blockMatrix_hermitian hσ r T T' Z))) ρ
  let M : Pl F → ℝ≥0∞ := fun v =>
    ((ω₁ v (hermOf (Fv F v) σ (TFE E r T) (TFE_herm σ r T))).prod
      (ω₁ v (hermOf (Fv F v) σ (TFE E r T') (TFE_herm σ r T'))))
      (Om σ J Λ r T T' (δ v) (lev g₁ g₂ v))
  let volZ : Pl F → ℝ≥0∞ := fun v => dZ v (ZZ σ r T T' (δ v) (lev g₁ g₂ v))
  let m := fun (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Pl F) =>
    ω₂ v (hermOf (Fv F v) σ (T2 σ r T T' Z) (blockMatrix_hermitian hσ r T T' Z))
      (OmGen σ J Λ r T T' (δ v) (lev g₁ g₂ v))
  let dens := fun (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Pl F) =>
    (m Z v).toReal * (volZ v).toReal / (M v).toReal

  AllSome (fun C : ℝ => 0 < C ∧ ∀ Z, GlobalTheory.SgGlob.TotPos (G Z) →
    rho Z (C * GlobalTheory.SgGlob.normInf (G Z) ^ (k - 1))) fun C =>
  let AA : ℝ := (μ 𝓕).toReal * C * (∏' v, (M v).toReal / (volZ v).toReal) / (μf (Kf σ J Λ)).toReal
  (μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤) ∧ (μf (Kf σ J Λ) ≠ 0 ∧ μf (Kf σ J Λ) ≠ ⊤) ∧
  (∀ v, M v ≠ 0 ∧ M v ≠ ⊤ ∧ volZ v ≠ 0 ∧ volZ v ≠ ⊤) ∧
  AbsConv (fun v => (M v).toReal / (volZ v).toReal) ∧
  ∀ Z, G Z ≠ 0 →
    (¬ (GlobalTheory.SgGlob.TotPos (G Z) ∧ ∀ v, Zv v Z ∈ ZZ σ r T T' (δ v) (lev g₁ g₂ v)) → mass Z = 0) ∧
    (GlobalTheory.SgGlob.TotPos (G Z) → (∀ v, Zv v Z ∈ ZZ σ r T T' (δ v) (lev g₁ g₂ v)) →
      (∀ v, m Z v ≠ ⊤) ∧ AbsConv (fun v => (m Z v).toReal) ∧ AbsConv (dens Z) ∧
      (∀ v, dens Z v = densClosed σ n r T T' (δ v) (lev g₁ g₂ v) (Zv v Z)) ∧
      (AllSome (rho Z) fun ρ => mass Z = ENNReal.ofReal
        ((μ 𝓕).toReal * ρ * (∏' v, (m Z v).toReal) / (μf (Kf σ J Λ)).toReal)) ∧
      mass Z = ENNReal.ofReal (AA * GlobalTheory.SgGlob.normInf (G Z) ^ (k - 1) * ∏' v, dens Z v))

example (v : Pl F) (h₁ : ((2 : ℕ) : 𝓞 F) ∈ v.asIdeal) : lev 2 3 v = 2 := by
  unfold lev; rw [if_pos h₁]

example {v : Pl F} (δ : Fv F v) (r : ℕ) : aEnt E δ r (Fin.last r) = 1 := by
  simp [aEnt, Algebra.TensorProduct.one_def]

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianLocalData
