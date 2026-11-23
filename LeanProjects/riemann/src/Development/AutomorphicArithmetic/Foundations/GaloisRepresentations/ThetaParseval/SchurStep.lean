import Development.WeilBound.ThetaLifts.LatticeBasics.BadStmt
import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol
import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TP

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def lift (M : Model σ X W) (om : Rep σ X W) (Φ : Fn F n d) (φ : UA σ X.J → ℂ) (h : UA σ W.J) : ℂ :=
  ∫ g in M.dom, theta om Φ g h * star (φ g) ∂M.μ

def mc (M : Model σ X W) (φ : UA σ X.J → ℂ) (g : UA σ X.J) : ℂ := pet M.μ M.dom (fun y => φ (y * g)) φ

variable (σ X) in

def gInf : Subgroup (UA σ X.J) := Subgroup.closure (UAt σ X (evI F))

variable (σ X) in

def gAt (S : Finset (Pl F)) : Subgroup (UA σ X.J) := ⨆ v ∈ S, locGrp σ X v

variable (σ X) in

def gOff (S : Finset (Pl F)) : Subgroup (UA σ X.J) :=
  Subgroup.closure {g | (∀ w : InfinitePlace F, (mat g).map (compInf F E w) = 1) ∧ ∀ v ∈ S, OffAt v g}

def IntAll (g : UA σ X.J) : Prop := ∀ v, IntAt v g

def IsFn (φ : UA σ X.J → ℂ) : Prop := Continuous φ ∧ ∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g

def IsBump (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (v : Pl F) (H : Subgroup (UA σ X.J))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  φ ∈ SB (Fin n × Fin d → Fv F v) ∧ φ ≠ 0 ∧ H ≤ locGrp σ X v ∧ (∀ g ∈ H, IntAt v g) ∧
    (∃ O : Set (UA σ X.J), IsOpen O ∧ 1 ∈ O ∧ ∀ g ∈ locGrp σ X v, g ∈ O → g ∈ H) ∧
    (∀ g ∈ H, Acts (evFin F v) (om (g, 1)) φ φ) ∧
    ∀ g ∈ locGrp σ X v, g ∉ H → ∃ (u : Matrix (Fin n) (Fin d) (AE F E)) (c c' : ℂ), At (evFin F v) u ∧ c ≠ c' ∧
      Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) ∧ Acts (evFin F v) (M.co.rho B.ψ (mat g * u)) φ (c' • φ)

end Gen

structure Tools : Prop where
  swFull : SWFullX
  boxSec : BoxSecX
  dbl : DblX
  stab2 : Stab2Cpt
  cpt : CptAll
  basic : ThetaBasic
  polSch : PolSch
  unfold0 : Unfold0
  pairEx : PositivityTheory.ThKG.Tow.PairEx
  split : SplitModel
  vacFix : VacFix2
  acts : ActsEx
  lie1 : GlobalTheory.RealLift.LieFirst
  lie2 : GlobalTheory.RealLift.LieSecond

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable (E) in

abbrev cj : E →ₐ[maximalRealSubfield E] E := (IsCMField.complexConj E).toAlgHom

structure IsBr {n : ℕ} (X : Spc (maximalRealSubfield E) E n) (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) : Prop where
  rat : ∀ g, e g ∈ ratU (cj E) X.J ↔ g ∈ GlobalTheory.UnitaryBC.ratU E n
  inf : ∀ g, e g ∈ gInf (cj E) X ↔ g ∈ GlobalTheory.UnitaryBC.infU E n
  fin : ∀ g, e g ∈ gOff (cj E) X ∅ ↔ g ∈ GlobalTheory.UnitaryBC.finU E n
  loc : ∀ (w : HeightOneSpectrum (𝓞 E)) g,
    e g ∈ locGrp (cj E) X (w.under (𝓞 (maximalRealSubfield E))) ↔ g ∈ GlobalTheory.UnitaryBC.locU n w
  emb : ∀ (w : InfinitePlace (maximalRealSubfield E)) (τ : EmbOver E w) g,
    (mat (e g)).map (piInf τ) = (GlobalTheory.UnitaryBC.cEmb τ.1 g).val
  spl : ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) g,
    ((mat (e g)).map (piW t)).map (complMap (splitPrime_under t)) = (GlobalTheory.UnitaryBC.cLoc (splitPrime t) g).val

abbrev CompAt {n : ℕ} (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E))
    (τ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  GlobalTheory.UnitaryBC.IsCompAlong U (GlobalTheory.UnitaryBC.locU n w) ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU n w).subtype) τ.ρ

def LocPair {n d : ℕ} {v : Pl (maximalRealSubfield E)} (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v)
    (χX χW : Chr (maximalRealSubfield E) E) (τ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) ((splitPrime t).adicCompletion E)))
    (τ' : GlobalTheory.CuspRep.SmIrr (GL (Fin d) ((splitPrime t).adicCompletion E))) : Prop :=
  ∃ β : SB (Matrix (Fin n) (Fin d) (Fv (maximalRealSubfield E) v)) →ₗ[ℂ] τ.V →ₛₗ[starRingEnd ℂ] τ'.V, β ≠ 0 ∧
    ∀ (g : GL (Fin n) (Fv (maximalRealSubfield E) v)) (h : GL (Fin d) (Fv (maximalRealSubfield E) v))
      (Φ Φ₁ : SB (Matrix (Fin n) (Fin d) (Fv (maximalRealSubfield E) v))),
      Φ₁.1 = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g h Φ.1 → ∀ x,
        β Φ₁ (τ.ρ (Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) g) x) =
          τ'.ρ (Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) h) (β Φ x)

def IsLiftWt {n d : ℕ} (lam : DomWeight n) (mX mW : ℤ) (lam' : DomWeight d) : Prop :=
  ∀ k : Fin d, 2 * lam'.w k = (if h : (k : ℕ) < n then 2 * lam.w ⟨k, h⟩ - d - mW else 0) + n + mX

structure IsLift {n d : ℕ} (B : Base (maximalRealSubfield E) E) (χX χW : Chr (maximalRealSubfield E) E)
    (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n)
    (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)) : Prop where
  aut : GlobalTheory.UnitaryBC.IsAutRepU U'
  wt : ∀ w, ∃ lam' : DomWeight d, GlobalTheory.UnitaryBC.HasWeightAt U' (B.emb w).1 lam' ∧ IsLiftWt (lam w) (mX w) (mW w) lam'
  loc : ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) τ τ',
    CompAt U (splitPrime t) τ → CompAt U' (splitPrime t) τ' → LocPair t χX χW τ τ'

end CM

def TLift : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E), B.IsGood (cj E) →
    ∀ (n : ℕ), 1 ≤ n → ∀ X : Spc (maximalRealSubfield E) E n, X.J = 1 → X.IsHerm (cj E) B n 0 →
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (W : Spc (maximalRealSubfield E) E d) (δ : E), W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
      W.IsSkew (cj E) B d 0 → ∀ (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ),
      IsHecke (maximalRealSubfield E) E χX → IsHecke (maximalRealSubfield E) E χW →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χW d →
      HasExp B.emb χX mX → HasExp B.emb χW mW →
      ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
        GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
        (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ), IsLift B χX χW mX mW lam U U'

def IsFin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) ∧ ∀ᶠ v in cofinite, φ v = M.vac v

def BrEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (X : Spc (maximalRealSubfield E) E n) (δ : E), δ ≠ 0 →
    X.J = δ • (1 : Matrix (Fin n) (Fin n) E) → ∃ e, IsBr X e

def HgtFst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∃ t₀ : ℝ, ∀ μ : Measure (UA σ X.J), μ.IsHaarMeasure → ∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) μ

def Rallis : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∀ φ, IsFn φ →
      Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ ∧
        (lift M om Φ φ = 0 → ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ = 0)

def Decomp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B n 0 → ∀ S : Finset (Pl F),
    (∃ j : gInf σ X × gAt σ X S × gOff σ X S ≃ₜ* UA σ X.J, ∀ x, j x = x.1.1 * x.2.1.1 * x.2.2.1) ∧
    IsCompact (gInf σ X : Set (UA σ X.J)) ∧ IsClosed (gAt σ X S : Set (UA σ X.J)) ∧ IsClosed (gOff σ X S : Set (UA σ X.J)) ∧
    IsCompact {g : UA σ X.J | IntAll g} ∧ IsOpen {g : UA σ X.J | IntAll g} ∧ (∀ g ∈ gInf σ X, IntAll g) ∧
    (∀ b ∈ gAt σ X S, ∃ c : Pl F → UA σ X.J, (∀ v, c v ∈ locGrp σ X v) ∧ (∀ v ∈ S, OffAt v ((c v)⁻¹ * b)) ∧
      ∀ H : Subgroup (UA σ X.J), (∀ v ∈ S, c v ∈ H) → b ∈ H) ∧
    ∀ g : UA σ X.J, {v | ¬ IntAt v g}.Finite

def BumpAny : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n → 2 * n ≤ d →
    ∀ v, ∀ N ∈ 𝓝 (1 : UA σ X.J), ∃ H φ, IsBump B M om v H φ ∧ (H : Set (UA σ X.J)) ⊆ N

def Datum : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ S : Finset (Pl F), UnrOff χW (S : Set (Pl F)) →
    ∀ (H : Pl F → Subgroup (UA σ X.J)) φ, IsFin M φ → (∀ v ∈ S, IsBump B M om v (H v) (φ v)) → (∀ v ∉ S, φ v = M.vac v) →
    ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → coef om ν (pure f₀ φ) 1 ≠ 0 ∧
      ∀ x ∈ gInf σ X, ∀ b ∈ gAt σ X S, ∀ c ∈ gOff σ X S, (b ∉ ⨆ v ∈ S, H v → coef om ν (pure f₀ φ) (x * b * c) = 0) ∧
        ∃ s : ℂ, ‖s‖ = a (e (c, 1)) ^ ((d : ℝ) / 2) ∧ (IntAll c → s = 1) ∧
          ∀ x' ∈ gInf σ X, ∀ b' ∈ ⨆ v ∈ S, H v, coef om ν (pure f₀ φ) (x' * b' * c) = s * coef om ν (pure f₀ φ) x'

def Tail : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ (μ : Measure (UA σ X.J)) (t : ℝ), μ.IsHaarMeasure → Integrable (fun g => a (e (g, 1)) ^ t) μ → ∀ S₀ : Finset (Pl F),
      ∃ S : Finset (Pl F), S₀ ⊆ S ∧ ∀ μC : Measure (gOff σ X S), μC.IsHaarMeasure →
        ∫⁻ c in {c : gOff σ X S | ¬ IntAll c.1}, ENNReal.ofReal (a (e (c.1, 1)) ^ t) ∂μC < μC {c | IntAll c.1}

def AbsNe : Prop :=
  ∀ (A B C : Type) [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC] (H : Set B) (K : Set C), MeasurableSet H → MeasurableSet K → μB H ≠ 0 → μB H ≠ ⊤ →
    μC K ≠ ⊤ → ∀ (f : A × B × C → ℂ) (m : A → C → ℂ) (s c₀ : C → ℂ) (κ : ℂ) (r : ℝ) (w : C → ENNReal), κ ≠ 0 → 0 < r →
    Integrable f (μA.prod (μB.prod μC)) → (∀ x b c, b ∉ H → f (x, b, c) = 0) → (∀ x c, ∀ b ∈ H, f (x, b, c) = s c * m x c) →
    (∀ c, ∫ x, m x c ∂μA = κ * c₀ c) → (∀ c ∈ K, s c = 1 ∧ c₀ c = r) → (∀ c, ‖c₀ c‖ ≤ r ∧ ‖s c‖ₑ ≤ w c) →
    ∫⁻ c in Kᶜ, w c ∂μC < μC K → ∫ y, f y ∂(μA.prod (μB.prod μC)) ≠ 0

def SameType {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
    (om : Rep (cj E) X W) (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ))
    (f₀ : SInf (maximalRealSubfield E) (Fin n × Fin d)) (φ : GlobalTheory.UnitaryBC.UA E n → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (ρ : Representation ℂ (GlobalTheory.UnitaryBC.infU E n) V)
    (i : V →ₗ[ℂ] SInf (maximalRealSubfield E) (Fin n × Fin d)) (j : V →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ)) (x₀ : V), ρ.IsIrreducible ∧
    i x₀ = f₀ ∧ j x₀ = φ ∧ (∀ x, j x ∈ U) ∧ (∀ k x, Acts (evI (maximalRealSubfield E)) (om (e k.1, 1)) (i x) (i (ρ k x))) ∧
    ∀ k x, j (ρ k x) = GlobalTheory.UnitaryBC.RU E n k.1 (j x)

def HasType {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
    (B : Base (maximalRealSubfield E) E) (M : Model (cj E) X W) (om : Rep (cj E) X W) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J)
    (f₀ : SInf (maximalRealSubfield E) (Fin n × Fin d)) (w : InfinitePlace (maximalRealSubfield E)) (lam' : DomWeight d) : Prop :=
  (GlobalTheory.Branching.sqRep ℂ d lam').IsIrreducible ∧ ∃ i : nablaSq ℂ d lam' →ₗ[ℂ] SInf (maximalRealSubfield E) (Fin n × Fin d),
    (∀ x, i x ∈ M.Pol B.ψ B.emb) ∧ (∃ x, i x = f₀) ∧ ∀ k ∈ GlobalTheory.UnitaryBC.embU d (B.emb w).1, ∀ x,
      Acts (evI (maximalRealSubfield E)) (om (1, e' k)) (i x) (i (GlobalTheory.Branching.sqRep ℂ d lam' (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k) x))

def RealPair : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' → n ≤ d →
    ∀ (δ : E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ), X.J = 1 → W.J = δ • (1 : Matrix (Fin d) (Fin d) E) → HasExp B.emb χX mX →
    HasExp B.emb χW mW → ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
      GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
      (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∃ φ ∈ U, φ ≠ 0 ∧ SameType om e U f₀ φ ∧
        ∀ w, ∃ lam', IsLiftWt (lam w) (mX w) (mW w) lam' ∧ HasType B M om e' f₀ w lam'

def SchurStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ f₀, f₀ ≠ 0 → ∀ φ, φ ≠ 0 → SameType om e U f₀ φ →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ φf, IsFin M φf → ∀ μA : Measure (gInf (cj E) X), μA.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ c ∈ gOff (cj E) X ∅, ∫ x, coef om ν (pure f₀ φf) x.1 * star (mc M (φ ∘ e.symm) (x.1 * c)) ∂μA =
      κ * coef om ν (pure f₀ φf) 1 * star (mc M (φ ∘ e.symm) c)

def NonVan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' → 2 * n ≤ d →
    ∀ K a (ε : UA (cj E) X.J × UA (cj E) X.J →* G2 (cj E) X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (ε (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (ε (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → ∀ φ, φ ≠ 0 →
      SameType om e U f₀ φ → ∃ φf, IsFin M φf ∧ lift M om (pure f₀ φf) (φ ∘ e.symm) ≠ 0

def LiftAut : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∃ Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ),
      ∀ (Φ : PolData B M) φ, GlobalTheory.UnitaryBC.IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧ GlobalTheory.UnitaryBC.IsAutFormU (Θ Φ φ) ∧
        ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
          Θ Φ₁ (GlobalTheory.UnitaryBC.RU E n g φ) = GlobalTheory.UnitaryBC.RU E d h (Θ Φ φ)

def ProjEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (ψ : GlobalTheory.UnitaryBC.UA E d → ℂ), GlobalTheory.UnitaryBC.IsAutFormU ψ → ψ ≠ 0 →
    ∃ (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)) (pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)),
      GlobalTheory.UnitaryBC.IsAutRepU U' ∧ pr ψ ≠ 0 ∧ ∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧
        ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f)

def AbsIso : Prop :=
  ∀ (G V T : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℂ T] (ρ : Representation ℂ G V)
    (U : Submodule ℂ V) (H : Subgroup G) (τ : Representation ℂ H T), (∀ g : G, ∃ h ∈ H, ∀ h' ∈ H, Commute (h⁻¹ * g) h') →
    (∀ g, ∀ u ∈ U, ρ g u ∈ U) → (∀ W ≤ U, (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W = ⊥ ∨ W = U) → τ.IsIrreducible →
    ∀ f : T →ₗ[ℂ] V, f ≠ 0 → (∀ x, f x ∈ U) → (∀ (h : H) x, f (τ h x) = ρ h (f x)) → ∀ u ∈ U,
      (∃ (m : ℕ) (c : Fin m → T →ₗ[ℂ] V) (x : Fin m → T), (∀ i y, c i y ∈ U) ∧ (∀ i (h : H) y, c i (τ h y) = ρ h (c i y)) ∧
        u = ∑ i, c i (x i)) ∧
      (u ≠ 0 → ∃ p : V →ₗ[ℂ] T, p u ≠ 0 ∧ ∀ (h : H), ∀ y ∈ U, p (ρ h y) = τ h (p y))

def ReadLift : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ))
      (pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → GlobalTheory.UnitaryBC.IsAutRepU U' →
      (∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧ ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f)) →
      ∀ f₀ ∈ M.Pol B.ψ B.emb, ∀ φ ∈ U, ∀ φf, IsFin M φf → pr (lift M om (pure f₀ φf) (φ ∘ e.symm) ∘ e') ≠ 0 →
      (∀ w lam', HasType B M om e' f₀ w lam' → GlobalTheory.UnitaryBC.HasWeightAt U' (B.emb w).1 lam') ∧
      ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) τ τ', CompAt U (splitPrime t) τ → CompAt U' (splitPrime t) τ' →
        LocPair t χX χW τ τ'

theorem tLift_of (T : Tools) (hH : HgtEx) (h1 : BrEx) (h2 : HgtFst) (h3 : RealPair) (h4 : NonVan) (h5 : LiftAut) (h6 : ProjEx)
    (h7 : ReadLift) : TLift := by
  intro E _ _ _ B hB n hn X hXJ hX
  obtain ⟨⟨K, a, hK, ha, -⟩, ε, -, hε⟩ := hH _ E (cj E) B n X n 0 hB (Or.inl hX)
  obtain ⟨t₀, ht₀⟩ := h2 _ E (cj E) B n X hB hX K a ε hK ha hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * t₀)
  refine ⟨max N (2 * n), fun d hd W δ hWJ hW χX χW mX mW hχX hχW rX rW eX eW U lam hU hwt hdom => ?_⟩
  have hd1 : 2 * n ≤ d := (le_max_right _ _).trans hd
  have hd2 : t₀ < (d : ℝ) / 2 := by
    have : (N : ℝ) ≤ d := by exact_mod_cast (le_max_left _ _).trans hd
    linarith
  have hδ : δ ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
    obtain ⟨-, A, hA⟩ := hW.sig w
    have := congrFun (congrFun hA (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    simp [hWJ] at this
  obtain ⟨⟨M, hM⟩, hom⟩ := T.pairEx _ E (cj E) B hB n d X W n 0 d 0 hX hW
  obtain ⟨om, hP⟩ := hom χX χW hχX hχW rX rW M hM
  obtain ⟨e, he⟩ := h1 E n X 1 one_ne_zero (by rw [hXJ, one_smul])
  obtain ⟨e', he'⟩ := h1 E d W δ hδ hWJ
  obtain ⟨f₀, hf₀, hf0, φ, hφ, hφ0, hS, hT⟩ := h3 E B n d X W M χX χW om hP hn e e' he he' (by omega) δ mX mW hXJ hWJ eX eW U lam hU hwt hdom
  obtain ⟨φf, hfin, hne⟩ := h4 E B n d X W M χX χW om hP hn e e' he he' hd1 K a ε hK ha hε t₀ (ht₀ M.μ hM.haar) hd2 U hU f₀ hf₀ hf0 φ hφ0 hS
  obtain ⟨Θ, hΘ⟩ := h5 E B n d X W M χX χW om hP hn e e' he he'
  have hmem : pure f₀ φf ∈ PolData B M := Submodule.subset_span ⟨f₀, hf₀, φf, hfin.1, hfin.2, rfl⟩
  obtain ⟨q1, q2, -⟩ := hΘ ⟨_, hmem⟩ φ (hU.aut φ hφ)
  have hne' : Θ ⟨_, hmem⟩ φ ≠ 0 := by
    rw [q1]
    intro h0
    apply hne
    funext h
    have := congrFun h0 (e'.symm h)
    simpa using this
  obtain ⟨U', pr, hU', hpr, hp⟩ := h6 E d _ q2 hne'
  rw [q1] at hpr
  obtain ⟨r1, r2⟩ := h7 E B n d X W M χX χW om hP hn e e' he he' U U' pr hU hU' hp f₀ hf₀ φ hφ φf hfin hpr
  exact ⟨U', hU', fun w => (hT w).imp fun lam' h => ⟨r1 w lam' h.2, h.1⟩, r2⟩

end UpperTheory.TP

end
