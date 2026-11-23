import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.SiegelWeilFormula.Densx
open scoped TensorProduct ENNReal NNReal Matrix Classical

set_option linter.unusedVariables false

namespace PositivityTheory.Rg.Base1

section Ideles

variable {F : Type} [Field F] [NumberField F]

def md (a : (AF F)ˣ) : ℝ := (IdeleGroup.ideleModule F a : ℝ)

def pr (t : Fˣ) : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom t

def th (f : (AF F)ˣ → ℝ≥0∞) (a : (AF F)ˣ) : ℝ≥0∞ := ∑' t : Fˣ, f (pr t * a)

def IsRay (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ) : Prop := ∀ δ : ℝ, 0 < δ → ((r δ : AF F).1 = θ δ ∧ (r δ : AF F).2 = 1)

def zi (f : (AF F)ˣ → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ := ∫⁻ a, f a * ENNReal.ofReal (md a ^ s) ∂(ideleMeasure F)

def Asym (r : ℝ → (AF F)ˣ) (H : Subgroup (AF F)ˣ) (f : (AF F)ˣ → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  (∃ C : ℝ≥0, ∀ a, ENNReal.ofReal (md a) * th f a ≤ C) ∧ (∃ R : ℝ, ∀ a, R < md a → th f a = 0) ∧ (∀ a, a ∉ H → th f a = 0) ∧
    ∀ a ∈ H, Tendsto (fun δ : ℝ => ENNReal.ofReal (md (a * r δ)) * th f (a * r δ)) (𝓝[>] 0) (𝓝 c)

def rv (v : HeightOneSpectrum (𝓞 F)) (e : ℝ) (s : Fv F v) : ℝ :=
  ∑' i : ℕ, if s ≠ 0 ∧ Valued.v s ≤ ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then e ^ i else 0

def pure (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (a : (AF F)ˣ) : ℝ≥0∞ :=
  ENNReal.ofReal (G (a : AF F).1 * (∏ v ∈ S, g v ((a : AF F).2 v)) * ∏ᶠ v : {v // v ∉ S}, w v.1 ((a : AF F).2 v.1))

end Ideles

def Tate : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r →
  ∃ V : ℝ≥0∞, V ≠ 0 ∧ V ≠ ⊤ ∧ ∀ H : Subgroup (AF F)ˣ, IsOpen (H : Set (AF F)ˣ) → H.index ≠ 0 → (∀ t, pr t ∈ H) →
    (∀ δ : ℝ, 0 < δ → r δ ∈ H) → ∀ (f : (AF F)ˣ → ℝ≥0∞) (c : ℝ≥0∞), Measurable f → Asym r H f c →
      (∀ s : ℝ, 1 < s → zi f s ≠ ⊤) ∧
      Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * zi f s) (𝓝[>] 1) (𝓝 (c * V / (H.index : ℝ≥0∞)))

def PsiSide : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r →
  ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ y, 0 ≤ G y) → (∀ v y, 0 ≤ g v y) →
    (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    Measurable (pure S G g fun v => rv v 0) ∧
      Asym r ⊤ (pure S G g fun v => rv v 0) (ENNReal.ofReal ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v)))

def Ratio : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (e : HeightOneSpectrum (𝓞 F) → ℝ),
    Continuous G → (∀ y, 0 ≤ G y) → (∀ v y, 0 ≤ g v y) → (∀ v ∈ S, Continuous (g v)) → (∀ v, e v = 1 ∨ e v = -1) →
    Measurable (pure S G g fun v => rv v (e v)) ∧ ∀ s : ℝ, 1 < s → zi (pure S G g fun v => rv v 0) s ≠ ⊤ →
      ENNReal.ofReal (∏' v : {v // v ∉ S}, (1 - e v.1 * (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s))) *
        zi (pure S G g fun v => rv v (e v)) s = zi (pure S G g fun v => rv v 0) s

def ForOne (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 1 → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 1 → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 1 → Fv F v ⊗[F] E)),
    IsCMExt F E σ → IsHermND σ J → IsStdInf li → (∀ v, IsStdV v (lam v)) → IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 →
    IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 1) (coordHerm (Ainf F) σ b li 1) mi →
    (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 1) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) →
    P F E σ J d b li lam μ 𝓕 mi m

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {J : Matrix (Fin 1) (Fin 1) E} {d : ℕ}

def sph (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (β : F) : Set (Fin 1 → Fin 1 → E) :=
  {X | gramE σ J X = fun _ _ => algebraMap F E β}

def EP (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 1 → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (β : F) (c : ℝ≥0) : Prop :=
  IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J β)) c (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    fun v => cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β))

def IsTest (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) : Prop :=
  Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧ tsupport φ ⊆ {X | IsUnit (gramR (Ainf F) σ J X).det} ∧
    (∀ v ∈ S, IsCompact (A v) ∧ IsOpen (A v) ∧ A v ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det}) ∧ ∀ v, v ∉ S → A v = latV b v

def vol (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) : ℝ≥0∞ :=
  (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 1 (A v)

def Gi (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 1 → Ainf F ⊗[F] E)) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (s : Ainf F) : ℝ := ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))

def gv (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) : ℝ :=
  (cfac E v : ℝ) * (m v (hermScal (Fv F v) σ s) (A v)).toReal

def IsNm (σ : E →ₐ[F] E) (x : (AF F ⊗[F] E)ˣ) (a : (AF F)ˣ) : Prop :=
  (a : AF F) ⊗ₜ[F] (1 : E) = sigR (AF F) σ x * x

def mean (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (x : (AF F ⊗[F] E)ˣ) : ℝ≥0∞ :=
  ∫⁻ X in {X | ∀ v, projV v (projFin fun a i => (x : AF F ⊗[F] E) * X a i) ∈ A v},
    ENNReal.ofReal (φ (projInf fun a i => (x : AF F ⊗[F] E) * X a i)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 1 → E | X ≠ 0})

def IsH (σ : E →ₐ[F] E) (H : Subgroup (AF F)ˣ) : Prop := ∀ a, a ∈ H ↔ ∃ t x n, IsNm σ x n ∧ a = pr t * n

end

def HEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∃ H : Subgroup (AF F)ˣ, IsH σ H ∧ IsOpen (H : Set (AF F)ˣ) ∧ H.index = 2

def Scal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ J : Matrix (Fin 1) (Fin 1) E, IsHermND σ J →
  ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R →
  ∀ (μ : Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (ν : Measure (HermR R σ 1)) (m : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J 1 μ ν m →
    ∀ (x : (R ⊗[F] E)ˣ) (n s : R), n ⊗ₜ[F] (1 : E) = sigR R σ x * x → IsUnit s →
      (m (hermScal R σ s)).map (fun X a i => (x : R ⊗[F] E) * X a i) = m (hermScal R σ (n * s))

def LocR : Prop := ForOne fun F E _ _ _ _ _ σ _ _ b _ _ _ _ _ m => ∀ᶠ v in cofinite, ∀ s : Fv F v, s ≠ 0 →
  (cfac E v : ℝ) * (m v (hermScal (Fv F v) σ s) (latV b v)).toReal = rv v (eR E v) s

def Prop1 : Prop := ForOne fun F _ _ _ _ _ _ _ _ _ b _ _ μ 𝓕 mi m => ∀ β : F, β ≠ 0 → ∃ c, EP b μ 𝓕 mi m β c

def Simil : Prop := ForOne fun F _ _ _ _ _ _ σ J _ b _ _ μ 𝓕 mi m => ∀ β β' : F, β ≠ 0 → β' ≠ 0 →
  (sph σ J β).Nonempty → (sph σ J β').Nonempty → ∀ c, EP b μ 𝓕 mi m β c → EP b μ 𝓕 mi m β' c

def Hasse : Prop := ForOne fun F _ _ _ _ _ _ σ J _ _ _ _ _ _ mi m => ∀ β : F, β ≠ 0 →
  mi (hermScal (Ainf F) σ (algebraMap F _ β)) ≠ 0 → (∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0) → (sph σ J β).Nonempty

def TestEx : Prop := ForOne fun F _ _ _ _ _ _ σ J _ b li lam _ _ _ _ => ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
  ∃ φ A, IsTest σ J b S φ A ∧ vol b li lam S φ A ≠ 0 ∧ vol b li lam S φ A ≠ ⊤

def Dens : Prop := ForOne fun F E _ _ _ _ _ σ J _ b li lam _ _ mi m => ∀ S φ A, IsTest σ J b S φ A →
  Continuous (Gi mi φ) ∧ HasCompactSupport (Gi mi φ) ∧ (∀ v ∈ S, Continuous (gv m A v) ∧ HasCompactSupport (gv m A v)) ∧
    ENNReal.ofReal ((∫ y, Gi mi φ y ∂li) * ∏ v ∈ S, ∫ s, gv m A v s ∂(lam v)) =
      (∏ v ∈ S, (cfac E v : ℝ≥0∞)) * vol b li lam S φ A

def LSide : Prop := ForOne fun F E _ _ _ _ _ σ J _ b li lam μ 𝓕 _ _ => ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ S φ A,
  IsTest σ J b S φ A →
    (∃ C : ℝ≥0, ∀ x n, IsNm σ x n → ENNReal.ofReal (md n) * mean σ J μ 𝓕 φ A x ≤ C) ∧
    (∃ R : ℝ, ∀ x n, IsNm σ x n → R < md n → mean σ J μ 𝓕 φ A x = 0) ∧
    ∀ x n, IsNm σ x n → Tendsto (fun ε : ℝ => ENNReal.ofReal (md (n * r (ε ^ 2))) *
      mean σ J μ 𝓕 φ A (x * Units.map (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toMonoidHom (r ε)))
        (𝓝[>] 0) (𝓝 (vol b li lam S φ A))

def ThetaId : Prop := ForOne fun F E _ _ _ _ _ σ J _ b _ _ μ 𝓕 mi m => ∀ κ : ℝ≥0, (∀ β : F, β ≠ 0 → EP b μ 𝓕 mi m β κ) →
  ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ φ A, IsTest σ J b S φ A →
    (∀ x n, IsNm σ x n → mean σ J μ 𝓕 φ A x = κ * th (pure S (Gi mi φ) (gv m A) fun v => rv v (eR E v)) n) ∧
    ∀ H, IsH σ H → ∀ a, a ∉ H → pure S (Gi mi φ) (gv m A) (fun v => rv v (eR E v)) a = 0

def Cnt : Prop := ForOne fun F E _ _ _ _ _ _ _ _ b _ _ μ 𝓕 mi m => ∀ κ : ℝ≥0, (∀ β : F, β ≠ 0 → EP b μ 𝓕 mi m β κ) →
  ∀ Λ : ℂ, IsLamLim F E Λ → ((κ : ℝ) : ℂ) = Λ / 2

end PositivityTheory.Rg.Base1

end
