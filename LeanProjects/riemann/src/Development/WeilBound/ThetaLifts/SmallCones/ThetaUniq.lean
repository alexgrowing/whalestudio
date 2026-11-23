import Mathlib
import Development.WeilBound.ThetaLifts.CTKernel
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Notions

variable {n d n₁ d₁ m : ℕ}

variable (σ) in

abbrev sy (X : Spc F E n) (W : Spc F E d) : Ten F E n d → Ten F E n d → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)

def lin (u : Fin m → Matrix (Fin n) (Fin d) E) (y : Fin m → AF F) : Ten F E n d := ∑ j, y j • incM F (u j)

variable (σ) in

structure Dual (X : Spc F E n) (W : Spc F E d) (I : Set (Ten F E n d)) (u z : Fin m → Matrix (Fin n) (Fin d) E) : Prop where
  mem : ∀ j (a : AF F), a • incM F (z j) ∈ I
  pair : ∀ i j, sy σ X W (incM F (z i)) (incM F (u j)) = if i = j then 1 else 0

variable (σ) in

structure Polar (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (ι : Matrix (Fin n) (Fin n₁) E)
    (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Ten F E n d)) (u z : Fin m → Matrix (Fin n) (Fin d) E) : Prop
    extends Dual σ X W I u z where
  uu : ∀ i j, sy σ X W (incM F (u i)) (incM F (u j)) = 0
  zz : ∀ i j, sy σ X W (incM F (z i)) (incM F (z j)) = 0
  um : ∀ i (w : Ten F E n₁ d₁), sy σ X W (incM F (u i)) (incM F ι * w * (incM F ι')ᵀ) = 0
  zm : ∀ i (w : Ten F E n₁ d₁), sy σ X W (incM F (z i)) (incM F ι * w * (incM F ι')ᵀ) = 0
  iso : ∀ w w' : Ten F E n₁ d₁, sy σ X W (incM F ι * w * (incM F ι')ᵀ) (incM F ι * w' * (incM F ι')ᵀ) = sy σ X₁ W₁ w w'
  span : ∀ x : Matrix (Fin n) (Fin d) E, ∃ (a b : Fin m → F) (x₁ : Matrix (Fin n₁) (Fin d₁) E),
    x = ∑ j, a j • u j + ∑ j, b j • z j + ι * x₁ * ι'ᵀ

variable (σ) in

abbrev IsoV (X : Spc F E n) : Type := {x : Fin n → E // x ≠ 0 ∧ form σ X.J x x = 0}

def Moves {X : Spc F E n} (H : Plane E n n₁) (γ : IsoV σ X → UA σ X.J) : Prop :=
  ∀ x, γ x ∈ ratU σ X.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x

def Iwa {X : Spc F E n} (H : Plane E n n₁) (K : Subgroup (UA σ X.J)) : Prop :=
  IsCompact (K : Set (UA σ X.J)) ∧
    ∀ g, ∃ (p k : UA σ X.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k

def KFinite {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (K : Subgroup (UA σ X.J)) (Φ : Fn F n d) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om (k.1, 1) Φ))

def thv (B : Base F E) {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (u : Ten F E n d) (Φ : Fn F n d) (h : UA σ W.J) (g : UA σ X.J) : ℂ := thetaSum F (e (M.co.rho B.ψ u (om (g, h) Φ)))

def coneI (B : Base F E) {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (om : Rep σ X W)
    (M₀ : Model σ X₁ W₁) (om₀ : Rep σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (K : Subgroup (UA σ X.J)) (μK : Measure K)
    (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Ten F E n d) (ν : Chr F E) (z : ℕ) (Φ : Fn F n d) (h₁ : UA σ W₁.J) : ℂ :=
  ∫ k, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) h₁ * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ ∂μK

def Mix2 {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (H : Plane E n n₁) (H' : Plane E d d₁)
    (χX χW : Chr F E) (rX rW : ℝ) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) : Prop :=
  ∀ t g₁ p, IsLevi H t g₁ p → ∀ u ∈ unip σ X H, ∀ t' h₁ p', IsLevi H' t' h₁ p' → ∀ u' ∈ unip σ W H', ∀ Φ ∈ schA F (Fin n × Fin d),
    e (om (u * p, u' * p') Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) *
      ((χX t' : ℂ) * (((absE F E t' : ℝ) ^ rW : ℝ) : ℂ))) • om₀ (g₁, h₁) (e Φ)

end Notions

def ThetaUniq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ l ∈ (adeleClass F).adm κ, (∀ ξ η : κ → F, ∀ Φ ∈ schA F κ,
      l (schr ψ (fun i => algebraMap F (AF F) (ξ i), fun i => algebraMap F (AF F) (η i)) Φ) = l Φ) →
    ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * thetaSum F Φ

def ThetaInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ Φ ∈ schA F κ, (∀ w, thetaSum F (schr ψ w Φ) = 0) → Φ = 0

def Slice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ ι ι' I e, IsEv B M M₁ ι ι' I e → ∀ (m : ℕ) (u z : Fin m → Matrix (Fin n) (Fin d) E), Dual σ X W I u z →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ (r : ℕ) (φ₁ : Fin r → (Fin n₁ × Fin d₁ → Af F) → ℂ) (C : Set (Fin m → Af F))
      (A : Fin r → (Fin m → AF F) → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)),
      (∀ i, φ₁ i ∈ SB _) ∧ IsCompact C ∧ (∀ i f, Continuous fun y => A i y f) ∧
      (∀ y (f : SInf F (Fin n × Fin d)), e (M.co.rho B.ψ (lin u y) (pureA F f φ)) = ∑ i, pureA F (A i y f) (φ₁ i)) ∧
      (∀ i y, (fun j => (y j).2) ∉ C → A i y = 0) ∧
      ∀ (q : Seminorm ℂ (SInf F (Fin n₁ × Fin d₁))) (N : ℕ), Continuous q → ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)),
        Continuous p ∧ ∀ i y f, q (A i y f) * (1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j))) ^ N ≤ p f

def EvAdm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → M.IsGood B.ψ → M₁.IsGood B.ψ →
    (∃ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), ∀ Φ ∈ schA F _, l Φ = thetaSum F Φ) ∧
    (∀ u, ∀ Φ ∈ schA F _, M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d)) ∧
    ∀ ι ι' I e, IsEv B M M₁ ι ι' I e → ∀ u, ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
      ∃ l' ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F _, l' Φ = l (e (M.co.rho B.ψ u Φ))

def ThetaExp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ ι ι' I e, IsEv B M M₁ ι ι' I e → ∀ (m : ℕ) (u z : Fin m → Matrix (Fin n) (Fin d) E), Polar σ X W X₁ W₁ ι ι' I u z →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ Φ ∈ schA F _, HasSum (fun y : Fin m → F =>
      C * thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (thetaSum F Φ)

def EvUniq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ ι ι' I e e', IsEv B M M₁ ι ι' I e → IsEv B M M₁ ι ι' I e' →
    ∀ (m : ℕ) (u z : Fin m → Matrix (Fin n) (Fin d) E), Polar σ X W X₁ W₁ ι ι' I u z →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F _, e' Φ = c • e Φ

def SchInt : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (α : Type) [TopologicalSpace α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α) (G : α → SchwartzMap V ℂ), Continuous G →
    (∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ) →
    ∃ f : SchwartzMap V ℂ, ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Integrable (fun a => T (G a)) μ ∧ T f = ∫ a, T (G a) ∂μ

def TateAbs : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure → ∀ z : ℕ, 2 ≤ z → ∃ N : ℕ, ∀ C : Set (AE F E), IsCompact C →
    ∫⁻ l in {l : (AE F E)ˣ | ∃ c ∈ C, At (evI F) ((l : AE F E) - c)},
      ENNReal.ofReal ((absE F E l : ℝ) ^ z / (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N) ∂μ < ⊤

def LineInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ ι ι' I e, IsEv B M M₁ ι ι' I e → ∀ v₀ z₀ : Matrix (Fin n) (Fin d) E, (∀ a : AE F E, a • incM F z₀ ∈ I) →
    IsUnit (hTens (cA σ) (incM F X.J) (incM F W.J) (incM F z₀) (incM F v₀)) →
    ∀ τ : AE F E →ₐ[AF F] AE F E, τ = AlgHom.id _ _ ∨ τ = cA σ → ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure →
    ∀ (z : ℕ) (ν : Chr F E), 2 ≤ z → Continuous ν → ∀ Ψ ∈ schA F (Fin n × Fin d),
      (∀ om₁ : Rep σ X₁ W₁, (∀ x, ∀ Φ ∈ schA F (Fin n₁ × Fin d₁), om₁ x Φ ∈ schA F _) → (Dom M₁ om₁ {φ | φ ∈ SB _} ∨ (Dom M₁ om₁ (soFin B M₁) ∧
          ∀ a : AE F E, e (M.co.rho B.ψ (a • incM F v₀) Ψ) ∈ M₁.So B.ψ B.τ₁)) → ∀ h₁,
        ∫⁻ l, (∫⁻ g in M₁.dom, ‖theta om₁ (e (M.co.rho B.ψ (τ l.1 • incM F v₀) Ψ)) g h₁‖ₑ ∂M₁.μ) *
          ENNReal.ofReal ((absE F E l : ℝ) ^ z) ∂μ < ⊤) ∧
      ∃ Ψ₁ ∈ schA F (Fin n₁ × Fin d₁), ∀ l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
        Integrable (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (τ l.1 • incM F v₀) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) μ ∧
        l₁ Ψ₁ = ∫ l, l₁ (e (M.co.rho B.ψ (τ l.1 • incM F v₀) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ

def Low : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ), B.IsGood σ → H.IsAdapted σ B Y Y₁ i₀ i₁ →
    (Y.IsHerm σ B r s → 1 ≤ r ∧ 1 ≤ s ∧ Y₁.IsHerm σ B (r - 1) (s - 1)) ∧
      (Y.IsSkew σ B r s → 1 ≤ r ∧ 1 ≤ s ∧ Y₁.IsSkew σ B (r - 1) (s - 1))

def Witt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    (min r s = 0 → ∀ x, form σ X.J x x = 0 → x = 0) ∧
    ∀ (n₁ : ℕ) (H : Plane E n n₁), H.x ≠ 0 → form σ X.J H.x H.x = 0 → ∃ γ, Moves (σ := σ) (X := X) H γ

def UnipEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → H.IsAdapted σ B Y Y₁ i₀ i₁ →
    (∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1) ∧
    (∃ C : Set (unip σ Y H), IsCompact C ∧ ∀ u : unip σ Y H, ∃ γ : unip σ Y H, γ.1 ∈ ratU σ Y.J ∧ γ * u ∈ C) ∧
    IsClosed (unip σ Y H : Set (UA σ Y.J)) ∧ (∀ μ : Measure (unip σ Y H), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧
    (∃ lev : (AE F E)ˣ × UA σ Y₁.J →* UA σ Y.J, Continuous lev ∧ (∀ t g, IsLevi H t g (lev (t, g))) ∧
      ∀ t g p, IsLevi H t g p → p = lev (t, g)) ∧
    (∀ u ∈ unip σ Y H, mat u *ᵥ incV F H.x = incV F H.x ∧
      ∃ (y : Fin n₁ → AE F E) (c : AE F E), mat u *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ y + c • incV F H.x) ∧
    ∃ t : (AE F E)ˣ, 1 < (absE F E t : ℝ)

def IwaEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (r s : ℕ) (H : Plane E n n₁), B.IsGood σ → X.IsHerm σ B r s → H.x ≠ 0 →
    form σ X.J H.x H.x = 0 → ∀ K : Subgroup (UA σ X.J), IsStab B K → Iwa H K

def Unfold : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    H.IsAdapted σ B X X₁ j₀ j₁ → ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ) (ν : Measure (UA σ X.J))
      (D : Set (UA σ X.J)) (ν₁ : Measure (UA σ X₁.J)) (D₁ : Set (UA σ X₁.J)) (lev : (AE F E)ˣ × UA σ X₁.J → UA σ X.J),
    Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure → ν.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) D ν → ν₁.IsHaarMeasure →
    IsFundamentalDomain (ratU σ X₁.J) D₁ ν₁ → (∀ t g, IsLevi H t g (lev (t, g))) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ γ, Moves (σ := σ) (X := X) H γ → ∀ f : UA σ X.J → ℂ, Continuous f → (∀ u ∈ unip σ X H, ∀ g, f (u * g) = f g) →
      (∀ δ ∈ ratU σ X.J, mat δ *ᵥ incV F H.x = incV F H.x → ∀ g, f (δ * g) = f g) →
      ∫⁻ k, ∫⁻ l, (∫⁻ g in D₁, ‖f (lev (l, g) * k.1)‖ₑ ∂ν₁) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μ ∂μK < ⊤ →
      (∀ᵐ g ∂(ν.restrict D), Summable fun x => f (γ x * g)) ∧ IntegrableOn (fun g => ∑' x, f (γ x * g)) D ν ∧
        ∫ g in D, ∑' x, f (γ x * g) ∂ν =
          κ * ∫ k, ∫ l, (∫ g in D₁, f (lev (l, g) * k.1) ∂ν₁) * (((absE F E l : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) ∂μ ∂μK

def KFinData : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ Φ ∈ PolData B M, Φ ∈ schA F _ ∧ KFinite om K Φ

def MixAB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
    (∀ e, IsEv B M M₀ H.ι H'.ι (isoA H H') e → Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e) ∧
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoB H H') e → Mix2 H H' χX χW ((d : ℝ) / 2) ((n₁ : ℝ) / 2) om om₀ e

def TwoExp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₀.IsGood B.ψ →
    ∀ eA eB, IsEv B M M₀ H.ι H'.ι (isoA H H') eA → IsEv B M M₀ H.ι H'.ι (isoB H H') eB → ∃ c : ℂ, c ≠ 0 ∧ ∀ Ψ ∈ schA F _,
      (Summable fun ξ : E => thetaSum F (eA (M.co.rho B.ψ (incM F (ξ • Matrix.vecMulVec H.x H'.y)) Ψ))) ∧
      (Summable fun ξ : E => thetaSum F (eB (M.co.rho B.ψ (incM F (ξ • Matrix.vecMulVec H.y H'.x)) Ψ))) ∧
      ∑' ξ : E, thetaSum F (eA (M.co.rho B.ψ (incM F (ξ • Matrix.vecMulVec H.x H'.y)) Ψ)) =
        c * ∑' ξ : E, thetaSum F (eB (M.co.rho B.ψ (incM F (ξ • Matrix.vecMulVec H.y H'.x)) Ψ))

def SoStab : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ x, ∀ Φ ∈ M.So B.ψ B.τ₁, om x Φ ∈ M.So B.ψ B.τ₁

def SoEv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₀.IsGood B.ψ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoB H H') e → ∀ Ψ ∈ M.So B.ψ B.τ₁, e Ψ = 0 ∧
      ∀ a : AE F E, e (M.co.rho B.ψ (a • incM F (Matrix.vecMulVec H.y H'.x)) Ψ) ∈ M₀.So B.ψ B.τ₁

def SoZeroA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₀.IsGood B.ψ → ∀ M₁ : Model σ X W₁, M₁.IsGood B.ψ →
    ∀ e₀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ Ψ ∈ schA F _,
      e₀ Ψ ∈ M₁.So B.ψ B.τ₁ → e Ψ = 0

def CTFub : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ Φ ∈ schA F _,
    (∃ (C : ℝ) (k : ℕ), ∀ h, ∫⁻ g in M.dom, ‖theta om Φ g h‖ₑ ∂M.μ ≤ ENNReal.ofReal (C * (ht h : ℝ) ^ k)) →
    ∀ c : UA σ X.J → UA σ W.J → ℂ, (∀ g, IsCT H' (theta om Φ g) (c g)) →
      (∀ h, IntegrableOn (fun g => c g h) M.dom M.μ) ∧ IsCT H' (M.I om Φ) fun h => ∫ g in M.dom, c g h ∂M.μ

def GenAniso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r' s' r₁ s₁ : ℕ)
    (X' : Spc F E n) (M : Model σ X W) (M₁ : Model σ X' W₁), X' = X → min r s = 0 → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e → ∃ C : ℂ, C ≠ 0 ∧ ∀ χX χW om om₁, IsPair B M χX χW om r s r' s' →
      IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ Φ ∈ schA F _, ∃ A₀, IsCT H' (M.I om Φ) A₀ ∧ HasLaw W₁ H' χX ((n : ℝ) / 2) A₀ ∧
        ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h, A₀ (p * h) = C * M₁.I om₁ (e (om (1, h) Φ)) h₁

def GenBig : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (M₁ : Model σ X W₁) e₀ e, M₁.IsGood B.ψ → M₀.IsGood B.ψ → IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → IsEv B M M₀ H.ι H'.ι (isoA H H') e →
    ∀ z : ℕ, 2 * n = d + 2 * z ∧ min r s + 2 ≤ z → ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure →
    μ.IsHaarMeasure → ∃ C₀ C₁ : ℂ, C₀ ≠ 0 ∧ C₁ ≠ 0 ∧ ∀ χX χW om om₁ om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) →
      IsPair B M₁ χX χW om₁ (r + 1) (s + 1) r' s' → IsPair B M₀ χX χW om₀ r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), KFinite om K Φ →
      ∃ A₀ A₁ : UA σ W.J → ℂ, IsCT H' (M.I om Φ) (A₀ + A₁) ∧ HasLaw W₁ H' χX ((n : ℝ) / 2) A₀ ∧
        HasLaw W₁ H' (χX / χW) (((d : ℝ) - n) / 2) A₁ ∧ ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h,
          A₁ (p * h) = C₁ * M₀.I om₀ (cone B M om e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ)) h₁ ∧
          A₀ (p * h) = C₀ * M₁.I om₁ (e₀ (om (1, h) Φ)) h₁

def GenSmall : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (M₁ : Model σ X W₁) e₀ e, M₁.IsGood B.ψ → M₀.IsGood B.ψ → IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → IsEv B M M₀ H.ι H'.ι (isoB H H') e →
    ∀ z : ℕ, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z → ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure →
    μ.IsHaarMeasure → ∃ C₀ C₁ : ℂ, C₀ ≠ 0 ∧ C₁ ≠ 0 ∧ ∀ χX χW om om₁ om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) →
      IsPair B M₁ χX χW om₁ (r + 1) (s + 1) r' s' → IsPair B M₀ χX χW om₀ r s r' s' → ∀ Φ ∈ M.So B.ψ B.τ₁, KFinite om K Φ →
      ∃ A₀ A₁ : UA σ W.J → ℂ, IsCT H' (M.I om Φ) (A₀ + A₁) ∧ HasLaw W₁ H' χX ((n : ℝ) / 2) A₀ ∧
        HasLaw W₁ H' (χX / χW) (((d : ℝ) - n) / 2) A₁ ∧ ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h,
          A₁ (p * h) = C₁ * M₀.I om₀ (cone B M om e K μK μ (shiftB σ H H') χW z (om (1, h) Φ)) h₁ ∧
          (e₀ (om (1, h) Φ) ∈ M₁.So B.ψ B.τ₁ → A₀ (p * h) = C₀ * M₁.I om₁ (e₀ (om (1, h) Φ)) h₁)

end PositivityTheory.ThKCT

end
