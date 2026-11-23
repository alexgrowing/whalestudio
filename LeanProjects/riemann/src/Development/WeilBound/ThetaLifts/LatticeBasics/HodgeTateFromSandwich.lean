import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locField' (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

def SplitModel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinW B.ψ t 1 1 ι) ∧ ∀ ι, M.IsLinW B.ψ t 1 1 ι →
      ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)),
        g₀.1 = (mat g).map (piW t) → h₀.1 = (mat h).map (piW t) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (g, h)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ)

def coef {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (ν : @Measure (Fin n × Fin d → AF F) (borel _)) (Φ : Fn F n d)
    (g : UA σ X.J) : ℂ := ∫ u, om (g, 1) Φ u * star (Φ u) ∂ν

def zint {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (ν : @Measure (Fin n × Fin d → AF F) (borel _))
    (a : G2 σ X → ℝ) (e : UA σ X.J × UA σ X.J →* G2 σ X) (Φ : Fn F n d) (s : ℂ) (g : UA σ X.J) : ℂ :=
  (a (e (g, 1)) : ℂ) ^ (s - ((d : ℂ) - n) / 2) * coef om ν Φ g

variable (σ Y) in

def locGrp (v : Pl F) : Subgroup (UA σ Y.J) := Subgroup.closure (UAt σ Y (evFin F v))

def IntAt (v : Pl F) (g : UA σ Y.J) : Prop :=
  ∀ z ∈ latHat Y, At (evFin F v) z → mat g *ᵥ z ∈ latHat Y ∧ mat g⁻¹ *ᵥ z ∈ latHat Y

def OffAt (v : Pl F) (g : UA σ Y.J) : Prop := (mat g).map (compFin F E v) = 1

def IsSphAt (K : Subgroup (G2 σ Y)) (χ : Chr F E) (v : Pl F) (z : ℂ) (f : G2 σ Y → ℂ) : Prop :=
  ∀ p t, IsPar p t → At (evFin F v) (mat2 p - 1) → ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
    f (p * k) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) * ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z

open Classical in
variable (E) in

def locD (n : ℕ) (v : Pl F) (s : ℂ) : ℂ :=
  ∏ i ∈ Finset.range n, (1 - (if Nonempty (E →ₐ[F] Fv F v) then 1 else -1) ^ (n - (i + 1)) *
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * s + (i + 1 : ℕ))))⁻¹

def NormZeta : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → min r' s' = 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∃ (U : Set ℂ) (Z : ℂ → ℂ) (t₀ : ℝ),
      IsOpen U ∧ (∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) ∧ ((d : ℂ) - n) / 2 ∈ U ∧ DifferentiableOn ℂ Z U ∧
      (∀ z : ℂ, t₀ < z.re → z ∈ U ∧ Integrable (zint om ν a e Φ z) M.μ ∧ Z z = ∫ g, zint om ν a e Φ z g ∂M.μ) ∧
      (M.I om Φ = 0 → Z (((d : ℂ) - n) / 2) = 0)

def EulerProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (T : Finset (Pl F)) (μ : Measure (UA σ Y.J)),
    μ.IsHaarMeasure → ∀ (μl : ∀ v, Measure (locGrp σ Y v)), (∀ v, (μl v).IsHaarMeasure ∧ μl v {g | IntAt v g.1} = 1) →
    ∀ (f : UA σ Y.J → ℂ) (fl : Pl F → UA σ Y.J → ℂ), Integrable f μ →
      (∀ v ∉ T, (∀ u ∈ locGrp σ Y v, ∀ g, OffAt v g → f (u * g) = fl v u * f g) ∧ (∀ u ∈ locGrp σ Y v, IntAt v u → fl v u = 1) ∧
        Integrable (fun u : locGrp σ Y v => fl v u.1) (μl v)) →
      Tendsto (fun S : Finset {v : Pl F // v ∉ T} => (∏ v ∈ S, ∫ u, fl v.1 u.1 ∂μl v.1) * ∫ g in {g | ∀ v ∉ T, IntAt v g}, f g ∂μ)
        atTop (𝓝 (∫ g, f g ∂μ))

def LocMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ v,
    ∃ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure ∧ μ {g | IntAt v g.1} = 1

def LocUnr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (χ : Chr F E), IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ K (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure → μ {g | IntAt v g.1} = 1 → ∀ (z : ℂ) f, (n : ℝ) / 2 < z.re →
      IsSphAt K χ v (z + n / 2) f → Integrable (fun u : locGrp σ Y v => f (e (u.1, 1))) μ ∧
        (∫ u, f (e (u.1, 1)) ∂μ) * locD E n v z = ∏ i ∈ Finset.range n, Lv (charFam χ) v (z + n / 2 - i)

def BadFactor : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → min r' s' = 0 → n ≤ d → Even d → ∀ T : Finset (Pl F), T ⊆ B.P → UnrOff χX (T : Set (Pl F)) →
    UnrOff χW (T : Set (Pl F)) → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → (∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f₀ f₀) →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ Φ ∈ PolData B M,
      (∀ (z : ℂ), ∀ v ∉ T, ∃ f, IsSphAt K χW v (z + n / 2) f ∧ ∀ u ∈ locGrp σ X v, (IntAt v u → f (e (u, 1)) = 1) ∧
        ∀ g, OffAt v g → zint om ν a e Φ z (u * g) = f (e (u, 1)) * zint om ν a e Φ z g) ∧
      Differentiable ℂ (fun z => ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ z g ∂M.μ) ∧
      ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ (((d : ℂ) - n) / 2) g ∂M.μ ≠ 0

def RealInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] [Nontrivial P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P),
    RealQuot B M om p → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f₀ f₀

def DProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (T : Finset (Pl F)), ∃ d : ℂ → ℂ,
    DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re → d z ≠ 0 ∧
      HasProd (fun v : {v : Pl F // v ∉ T} => locD E n v.1 z) (d z)

def IsReps (v : Pl F) {j : ℕ} (R : Finset (GL (Fin (j + 1)) (Fv F v))) : Prop :=
  ∀ g : GL (Fin (j + 1)) (Fv F v), (∃ k ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (j + 1)), ∃ k' ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (j + 1)),
      g.1 = k.1 * Matrix.diagonal (Function.update 1 0 (unifAt v : Fv F v)) * k'.1) ↔
    ∃! x, x ∈ R ∧ x⁻¹ * g ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (j + 1))

def actL {v : Pl F} {n j m : ℕ} (ξ : (Fv F v)ˣ →* ℂˣ) (g : GL (Fin j) (Fv F v)) :
    Module.End ℂ (Matrix (Fin n) (Fin j) (Fv F v) × Matrix (Fin n) (Fin m) (Fv F v) → ℂ) where
  toFun φ y := ξ (Matrix.GeneralLinearGroup.det g) * φ (y.1 * g.1, y.2)
  map_add' _ _ := funext fun _ => mul_add _ _ _
  map_smul' _ _ := funext fun _ => mul_left_comm _ _ _

def LocHecke : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (n j m : ℕ) (ξ₁ ξ₂ : (Fv F v)ˣ →* ℂˣ), GlobalTheory.SplitFlip.CondLE (unifAt v) 0 ξ₂ →
    ∀ l : (Matrix (Fin n) (Fin (j + 1)) (Fv F v) × Matrix (Fin n) (Fin m) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ φ ∈ SB _, ∀ γ : GL (Fin n) (Fv F v), l (fun y => φ ((γ⁻¹).1 * y.1, (γ⁻¹).1 * y.2)) = ξ₁ (Matrix.GeneralLinearGroup.det γ) * l φ) →
    (∀ φ ∈ SB _, ∀ b : Matrix (Fin (j + 1)) (Fin m) (Fv F v), l (fun y => φ (y.1, y.2 + y.1 * b)) = l φ) →
    ∀ R, IsReps v R → ∀ φ ∈ SB _, (∀ k ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (j + 1)), actL ξ₂ k φ = φ) → ∀ x y : ℂ,
      let q : ℂ := Ideal.absNorm v.asIdeal
      let A : ℕ → ℂ := fun r => ξ₂ (unifAt v) * (ξ₁ (unifAt v) : ℂ)⁻¹ * q ^ ((n : ℤ) - r - m)
      let c : ℕ → ℂ := fun r => A r * ∑ i ∈ Finset.range r, q ^ i + ξ₂ (unifAt v) * ∑ i ∈ Finset.Ico r (j + 1), q ^ i
      let z : ℕ → ℂ := fun r => A r ^ r * (ξ₂ (unifAt v) : ℂ) ^ (j + 1 - r)
      let T : ℕ → Module.End ℂ (Matrix (Fin n) (Fin (j + 1)) (Fv F v) × Matrix (Fin n) (Fin m) (Fv F v) → ℂ) := fun r =>
        x • ∑ g ∈ R, actL ξ₂ g + y • actL ξ₂ (Matrix.GeneralLinearGroup.scalar _ (unifAt v)) - (x * c r + y * z r) • 1
      l (((List.range (j + 2)).map T).prod φ) = 0

end GlobalTheory.ThK.Dbl

end
