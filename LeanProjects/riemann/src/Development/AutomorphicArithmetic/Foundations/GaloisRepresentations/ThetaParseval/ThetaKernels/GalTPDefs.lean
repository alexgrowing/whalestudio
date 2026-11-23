import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtX
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseKPair
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseCpt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtN
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowStmt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitModelK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadStmt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
end Gen
structure Tools_k : Prop where
  swFull : _root_.GlobalTheory.ThK.Dbl.SWFullX_k
  boxSec : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k
  dbl : _root_.GlobalTheory.ThK.Dbl.DblX_k
  stab2 : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k
  cpt : _root_.GlobalTheory.ThK.Dbl.CptAll_k
  basic : _root_.GlobalTheory.ThK.ThetaBasic_k
  polSch : _root_.GlobalTheory.ThK.Dbl.PolSch_k
  unfold0 : _root_.GlobalTheory.ThK.Dbl.Unfold0_k
  pairEx : _root_.PositivityTheory.ThKG.Tow.PairEx_k
  split : _root_.GlobalTheory.ThK.Dbl.SplitModel_k
  vacFix : _root_.GlobalTheory.ThK.Dbl.VacFix2_k
  acts : _root_.GlobalTheory.ThK.ActsEx_k
  lie1 : GlobalTheory.RealLift.LieFirst
  lie2 : GlobalTheory.RealLift.LieSecond
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end CM
def TLift_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E), _root_.UpperTheory.TP.W.GoodK (cj E) B →
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
def HgtFst_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∃ t₀ : ℝ, ∀ μ : Measure (UA σ X.J), μ.IsHaarMeasure → ∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) μ
def Rallis_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∀ φ, IsFn φ →
      Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ ∧
        (lift M om Φ φ = 0 → ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ = 0)
def Decomp_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 → ∀ S : Finset (Pl F),
    (∃ j : gInf σ X × gAt σ X S × gOff σ X S ≃ₜ* UA σ X.J, ∀ x, j x = x.1.1 * x.2.1.1 * x.2.2.1) ∧
    IsCompact (gInf σ X : Set (UA σ X.J)) ∧ IsClosed (gAt σ X S : Set (UA σ X.J)) ∧ IsClosed (gOff σ X S : Set (UA σ X.J)) ∧
    IsCompact {g : UA σ X.J | IntAll g} ∧ IsOpen {g : UA σ X.J | IntAll g} ∧ (∀ g ∈ gInf σ X, IntAll g) ∧
    (∀ b ∈ gAt σ X S, ∃ c : Pl F → UA σ X.J, (∀ v, c v ∈ locGrp σ X v) ∧ (∀ v ∈ S, OffAt v ((c v)⁻¹ * b)) ∧
      ∀ H : Subgroup (UA σ X.J), (∀ v ∈ S, c v ∈ H) → b ∈ H) ∧
    ∀ g : UA σ X.J, {v | ¬ IntAt v g}.Finite
def BumpAny_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → 2 * n ≤ d →
    ∀ v, ∀ N ∈ 𝓝 (1 : UA σ X.J), ∃ H φ, IsBump B M om v H φ ∧ (H : Set (UA σ X.J)) ⊆ N
def Datum_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ S : Finset (Pl F), UnrOff χW (S : Set (Pl F)) →
    ∀ (H : Pl F → Subgroup (UA σ X.J)) φ, IsFin M φ → (∀ v ∈ S, IsBump B M om v (H v) (φ v)) → (∀ v ∉ S, φ v = M.vac v) →
    ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → coef om ν (pure f₀ φ) 1 ≠ 0 ∧
      ∀ x ∈ gInf σ X, ∀ b ∈ gAt σ X S, ∀ c ∈ gOff σ X S, (b ∉ ⨆ v ∈ S, H v → coef om ν (pure f₀ φ) (x * b * c) = 0) ∧
        ∃ s : ℂ, ‖s‖ = a (e (c, 1)) ^ ((d : ℝ) / 2) ∧ (IntAll c → s = 1) ∧
          ∀ x' ∈ gInf σ X, ∀ b' ∈ ⨆ v ∈ S, H v, coef om ν (pure f₀ φ) (x' * b' * c) = s * coef om ν (pure f₀ φ) x'
def Tail_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ (μ : Measure (UA σ X.J)) (t : ℝ), μ.IsHaarMeasure → Integrable (fun g => a (e (g, 1)) ^ t) μ → ∀ S₀ : Finset (Pl F),
      ∃ S : Finset (Pl F), S₀ ⊆ S ∧ ∀ μC : Measure (gOff σ X S), μC.IsHaarMeasure →
        ∫⁻ c in {c : gOff σ X S | ¬ IntAll c.1}, ENNReal.ofReal (a (e (c.1, 1)) ^ t) ∂μC < μC {c | IntAll c.1}
def RealPair_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' → n ≤ d →
    ∀ (δ : E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ), X.J = 1 → W.J = δ • (1 : Matrix (Fin d) (Fin d) E) → HasExp B.emb χX mX →
    HasExp B.emb χW mW → ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
      GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
      (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∃ φ ∈ U, φ ≠ 0 ∧ SameType om e U f₀ φ ∧
        ∀ w, ∃ lam', IsLiftWt (lam w) (mX w) (mW w) lam' ∧ HasType B M om e' f₀ w lam'
def SchurStep_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ f₀, f₀ ≠ 0 → ∀ φ, φ ≠ 0 → SameType om e U f₀ φ →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ φf, IsFin M φf → ∀ μA : Measure (gInf (cj E) X), μA.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ c ∈ gOff (cj E) X ∅, ∫ x, coef om ν (pure f₀ φf) x.1 * star (mc M (φ ∘ e.symm) (x.1 * c)) ∂μA =
      κ * coef om ν (pure f₀ φf) 1 * star (mc M (φ ∘ e.symm) c)
def NonVan_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' → 2 * n ≤ d →
    ∀ K a (ε : UA (cj E) X.J × UA (cj E) X.J →* G2 (cj E) X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (ε (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (ε (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → ∀ φ, φ ≠ 0 →
      SameType om e U f₀ φ → ∃ φf, IsFin M φf ∧ lift M om (pure f₀ φf) (φ ∘ e.symm) ≠ 0
def LiftAut_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∃ Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ),
      ∀ (Φ : PolData B M) φ, GlobalTheory.UnitaryBC.IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧ GlobalTheory.UnitaryBC.IsAutFormU (Θ Φ φ) ∧
        ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
          Θ Φ₁ (GlobalTheory.UnitaryBC.RU E n g φ) = GlobalTheory.UnitaryBC.RU E d h (Θ Φ φ)
def ReadLift_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ))
      (pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → GlobalTheory.UnitaryBC.IsAutRepU U' →
      (∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧ ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f)) →
      ∀ f₀ ∈ M.Pol B.ψ B.emb, ∀ φ ∈ U, ∀ φf, IsFin M φf → pr (lift M om (pure f₀ φf) (φ ∘ e.symm) ∘ e') ≠ 0 →
      (∀ w lam', HasType B M om e' f₀ w lam' → GlobalTheory.UnitaryBC.HasWeightAt U' (B.emb w).1 lam') ∧
      ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) τ τ', CompAt U (splitPrime t) τ → CompAt U' (splitPrime t) τ' →
        LocPair t χX χW τ τ'
theorem tLift_of_k (T : _root_.UpperTheory.TP.Tools_k) (hH : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) (h1 : BrEx) (h2 : _root_.UpperTheory.TP.HgtFst_k) (h3 : _root_.UpperTheory.TP.RealPair_k) (h4 : _root_.UpperTheory.TP.NonVan_k) (h5 : _root_.UpperTheory.TP.LiftAut_k) (h6 : ProjEx)
    (h7 : _root_.UpperTheory.TP.ReadLift_k) : _root_.UpperTheory.TP.TLift_k := by
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
end
