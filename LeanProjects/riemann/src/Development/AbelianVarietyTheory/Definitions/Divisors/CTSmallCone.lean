import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

namespace GlobalTheory.ThK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev Fn (F : Type) [Field F] [NumberField F] (n d : ℕ) : Type := (Fin n × Fin d → AF F) → ℂ

variable (F) in

def incV {n : ℕ} (x : Fin n → E) : Fin n → AE F E := fun i => inclR (F := F) (AF F) (x i)

scoped instance measIdele : MeasurableSpace (AE F E)ˣ := borel _

section Pair

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsPair (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ) : Prop where
  base : B.IsGood σ
  herm : X.IsHerm σ B r s
  skew : W.IsSkew σ B r' s'
  good : M.IsGood B.ψ
  hX : IsHecke F E χX
  hW : IsHecke F E χW
  resX : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n
  resW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d
  weil : M.IsWeil B.ψ χX χW om

def PolData (B : Base F E) (M : Model σ X W) : Submodule ℂ (Fn F n d) :=
  Submodule.span ℂ {Φ | ∃ f ∈ M.Pol B.ψ B.emb, ∃ φ, (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in cofinite, φ v = M.vac v) ∧ Φ = pure f φ}

structure IsEv (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) : Prop where
  maps : ∀ Φ ∈ schA F _, e Φ ∈ schA F _
  Heisenberg₂ : ∀ z, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = M₁.co.rho B.ψ z (e Φ)
  inv : ∀ u ∈ I, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ u Φ) = e Φ
  loc : ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 ∧
    (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

def iso0 (n : ℕ) (H' : Plane E d d₁) : Set (Matrix (Fin n) (Fin d) (AE F E)) := {u | ∃ y, u = Matrix.vecMulVec y (incV F H'.x)}

def isoA (H : Plane E n n₁) (H' : Plane E d d₁) : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
  iso0 n H' ∪ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)}

def isoB (H : Plane E n n₁) (H' : Plane E d d₁) : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
  {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} ∪ {u | ∃ y, u = Matrix.vecMulVec (incM F H.ι *ᵥ y) (incV F H'.x)}

variable (X) in

def latHat : AddSubgroup (Fin n → AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ X.L, z = a • incV F x}

def IsStab (B : Base F E) (K : Subgroup (UA σ X.J)) : Prop :=
  ∀ g, g ∈ K ↔ (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧ ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X

def cone (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (K : Subgroup (UA σ X.J)) (μK : Measure K)
    (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ) (Φ : Fn F n d) : Fn F n₁ d₁ :=
  fun y => ∫ k, ∫ l, e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ ∂μK

def shiftA (H : Plane E n n₁) (H' : Plane E d d₁) (l : (AE F E)ˣ) : Matrix (Fin n) (Fin d) (AE F E) :=
  l.1 • Matrix.vecMulVec (incV F H.x) (incV F H'.y)

variable (σ) in

def shiftB (H : Plane E n n₁) (H' : Plane E d d₁) (l : (AE F E)ˣ) : Matrix (Fin n) (Fin d) (AE F E) :=
  cA σ l.1 • Matrix.vecMulVec (incV F H.y) (incV F H'.x)

variable (σ W) in

def unip (H' : Plane E d d₁) : Subgroup (UA σ W.J) :=
  Subgroup.closure {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}

def IsCT (H' : Plane E d d₁) (f c : UA σ W.J → ℂ) : Prop :=
  ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h, c h = ∫ u in 𝓕, f (u.1 * h) ∂μ

def IsLevi (H' : Plane E d d₁) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (h : UA σ W.J) : Prop :=
  mat h *ᵥ incV F H'.x = t.1 • incV F H'.x ∧ mat h *ᵥ incV F H'.y = cA σ (t⁻¹).1 • incV F H'.y ∧
    mat h * incM F H'.ι = incM F H'.ι * mat h₁

variable (W₁) in

def HasLaw (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (T : UA σ W.J → ℂ) : Prop :=
  ∀ t m, IsLevi (W₁ := W₁) H' t 1 m → ∀ h, T (m * h) = (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) * T h

end Pair

variable {a a' : ℕ}

def Split2 {W : Spc F E (a + a')} {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (X : Chars F E) (f fa fb : UA σ W.J → ℂ) : Prop :=
  IsCT H' f (fa + fb) ∧ HasLaw W₁ H' X.α ((a' : ℝ) / 2) fa ∧ HasLaw W₁ H' X.β ((a : ℝ) / 2) fb

def PolConst (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a') (c : ℂ) : Prop :=
  ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ h, G.M.I om Φ h = c * G.M'.I om' Φ' h

def reS {n : ℕ} (X Y : Spc F E n) : Spc F E n := { X with θ := Y.θ, bas := Y.bas }

def reG (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) : Geo σ a a' where
  p := G.p
  q := G.q
  V := reS G.V V
  V' := reS G.V' V'
  W := reS G.W W
  M := ⟨G.M.co, G.M.vac, G.M.μ, G.M.dom⟩
  M' := ⟨G.M'.co, G.M'.vac, G.M'.μ, G.M'.dom⟩

structure CfgB (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)) : Prop where
  eV : G₁.V = G.V
  ep : G₁.p = G.p
  eq : G₁.q + 1 = G.q
  hH : H.IsAdapted σ B G.V' G₁.V' 0 (b + 1)
  hH' : H'.IsAdapted σ B G.W G₁.W a (a + b + 1)

structure CfgA (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')) : Prop where
  eV : G₁.V' = G.V'
  q0 : G.q = 0
  q1 : G₁.q = 0
  ep : G₁.p + 1 = G.p
  hH : H.IsAdapted σ B G.V G₁.V 0 (b + 1)
  hH' : H'.IsAdapted σ B G.W G₁.W 0 (b + 1)

def ThetaBasic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    (∀ Φ ∈ schA F _, Continuous (fun x : UA σ X.J × UA σ W.J => theta om Φ x.1 x.2) ∧
      (∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) ∧
      ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ g h, Continuous fun f : SInf F (Fin n × Fin d) => theta om (pureA F f φ) g h

def ModelChange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (om₁ : Rep σ X W), IsPair B M₁ χX χW om₁ r s r' s' →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), c ≠ 0 ∧ IsEv B M M₁ 1 1 ∅ e ∧ Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧
        ∀ Φ ∈ schA F _, thetaSum F (e Φ) = c * thetaSum F Φ ∧ ∀ x, e (om x Φ) = om₁ x (e Φ)

def WeilConv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → d + 2 * min r s < 2 * n ∨ min r s = 0 →
    (∀ Φ ∈ schA F _, M.Conv om Φ ∧ ∃ (C : ℝ) (k : ℕ), ∀ h, ∫ g in M.dom, ‖theta om Φ g h‖ ∂M.μ ≤ C * (ht h : ℝ) ^ k) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f φ) h

def SoDecay : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ M.So B.ψ B.τ₁, ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ * (qht g : ℝ) ^ N ≤ C * (ht h : ℝ) ^ k

def SoCont : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (m : ℕ) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ) (f : Fin m → SInf F (Fin n × Fin d)) (u : ℕ → Fin m → SInf F (Fin n × Fin d)),
      (∀ j, φ j ∈ SB _ ∧ Tendsto (u · j) atTop (𝓝 (f j))) → (∀ k, ∑ j, pureA F (u k j) (φ j) ∈ M.So B.ψ B.τ₁) →
      ∑ j, pureA F (f j) (φ j) ∈ M.So B.ψ B.τ₁ →
      ∀ h, Tendsto (fun k => M.I om (∑ j, pureA F (u k j) (φ j)) h) atTop (𝓝 (M.I om (∑ j, pureA F (f j) (φ j)) h))

def EvZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (X₁ : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X₁ W₁), X₁ = X → H'.IsAdapted σ B W W₁ i₀ i₁ →
      M₁.IsGood B.ψ → (∃ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e) ∧
        ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e → (PolData B M).map e = PolData B M₁

def EvCone : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ d₁ : ℕ) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (i₀ i₁ j₀ j₁ : ℕ) (M₁ : Model σ X₁ W₁),
      H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
      (∃ e, IsEv B M M₁ H.ι H'.ι (isoA H H') e) ∧ ∃ e, IsEv B M M₁ H.ι H'.ι (isoB H H') e

def StabEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K ∧ IsCompact (K : Set (UA σ X.J)) ∧
      μK.IsHaarMeasure ∧ μ.IsHaarMeasure

def TowerB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → 1 ≤ G.q →
    ∃ V V' W, IsTriple B (reG G V V' W) X om om' ∧ ∃ (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)),
      CfgB B (reG G V V' W) G₁ H H' ∧ ∃ om₁ om₁', IsTriple B G₁ X om₁ om₁'

def TowerA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 → 1 ≤ G.p →
    ∃ V V' W, IsTriple B (reG G V V' W) X om om' ∧ ∃ (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')),
      CfgA B (reG G V V' W) G₁ H H' ∧ ∃ om₁ om₁', IsTriple B G₁ X om₁ om₁'

def MatchEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    (∀ Φ ∈ PolData B G.M, ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ') ∧
    (∀ Φ' ∈ PolData B G.M', ∃ Φ, PolMatch B G X R Rf Φ Φ') ∧
    ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' ∧ Match B G X R Rf Φ Φ'

def SqInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
      (∀ Φ ∈ PolData B G.M, IntegrableOn (fun h => ‖G.M.I om Φ h‖ ^ 2) 𝓕 μ) ∧
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, IntegrableOn (fun h => ‖G.M'.I om' Φ' h‖ ^ 2) 𝓕 μ

def SplitEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
      (∀ Φ ∈ PolData B G.M, ∃! x : (UA σ G.W.J → ℂ) × (UA σ G.W.J → ℂ), Split2 W₁ H' X (G.M.I om Φ) x.1 x.2) ∧
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃! x : (UA σ G.W.J → ℂ) × (UA σ G.W.J → ℂ), Split2 W₁ H' X (G.M'.I om' Φ') x.1 x.2

def Factor : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    (∀ Φ, PolMatch B G X R Rf Φ 0 → G.M.I om Φ = 0) ∧ ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf 0 Φ' → G.M'.I om' Φ' = 0

def NonZeroAn : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    (G.p = 0 → ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0) ∧ (G.q = 0 → ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ' ≠ 0)

def NonZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    (∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0) ∧ ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ' ≠ 0

def CTBigZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ ∈ PolData B G.M, ∀ fa fb, Split2 G₁.W H' X (G.M.I om Φ) fa fb → ∀ h₁ m, IsLevi H' 1 h₁ m → ∀ h,
        fb (m * h) = C * G₁.M.I om₁ (e (om (1, h) Φ)) h₁

def CTSmallCone : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ fa fb, Split2 G₁.W H' X (G.M'.I om' Φ') fa fb → ∀ h₁ m, IsLevi H' 1 h₁ m → ∀ h,
        fb (m * h) = C * G₁.M'.I om₁' (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ')) h₁

def CTBigCone : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ ∈ PolData B G.M, ∀ fa fb, Split2 G₁.W H' X (G.M.I om Φ) fa fb → ∀ h₁ m, IsLevi H' 1 h₁ m → ∀ h,
        fa (m * h) = C * G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, h) Φ)) h₁

def CTSmallZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M', ∃ fa, Split2 G₁.W H' X (G.M'.I om' Φ') fa 0 ∧ ∀ h₁ m, IsLevi H' 1 h₁ m → ∀ h,
        fa (m * h) = C * G₁.M'.I om₁' (e' (om' (1, h) Φ')) h₁

def LocB : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e e', IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e →
      IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) Φ' ∈ G₁.M'.So B.ψ B.τ₁ ∧
        PolMatch B G₁ X R₁ Rf₁ ((C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) *
          charL X.ν (X.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 : ℕ) : ℂ) + 1)) • e Φ) (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) Φ')

def LocA : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a') e e', IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
      IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' →
        PolMatch B G₁ X R₁ Rf₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ) ((C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) *
          charL X.ν (X.S₀ : Set (Pl F)) (((b + 2 - a') / 2 : ℕ) : ℂ)) • e' Φ')

def FacNe : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (e₁ e₂ s : ℤˣ) 𝔟 𝔠 (z : ℤ), stepFac B X e₁ e₂ s 𝔟 𝔠 z ≠ 0 ∧
    ∀ k : ℕ, 2 ≤ k → charL X.ν (X.S₀ : Set (Pl F)) (k : ℂ) ≠ 0

def AnAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 →
    ∀ c, PolConst B G X om om' R Rf c → ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' → ∀ h, G.M.I om Φ h = c * G.M'.I om' Φ' h

def EndB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → ∀ h₁ m, IsLevi (W₁ := W₁) H' 1 h₁ m → fb m = c * fb' m) → PolConst B G X om om' R Rf c

def EndA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → ∀ h₁ m, IsLevi (W₁ := W₁) H' 1 h₁ m → fa m = c * fa' m) → PolConst B G X om om' R Rf c

def PolZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 → ∃ c, c ≠ 0 ∧ PolConst B G X om om' R Rf c

def PolRe : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ V V' W R₂ Rf₂, IsMatched B (reG G V V' W) X om om' R₂ Rf₂ → (∃ c, c ≠ 0 ∧ PolConst B (reG G V V' W) X om om' R₂ Rf₂ c) →
      ∃ c, c ≠ 0 ∧ PolConst B G X om om' R Rf c

def PolAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∃ c, c ≠ 0 ∧ PolConst B G X om om' R Rf c

def FinInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (v : Pl F) w, Formalism.UG.IsInertAt F E v w →
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module ℂ P) (p : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] P)
      (p' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] P), (SB _).map p = ⊤ ∧ (SB _).map p' = ⊤ ∧
      augAt om v ≤ LinearMap.ker p ∧ augAt om' v ≤ LinearMap.ker p' ∧ Nontrivial P ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → p φ = p' φ' → p φ₁ = p' φ₁') ∧
      (∀ N : Submodule ℂ P, (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
        Acts (evFin F v) (om (1, h)) φ φ₁ → p φ ∈ N → p φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      (v ∉ X.T → p (G.M.vac v) = p' (G.M'.vac v) ∧ p (G.M.vac v) ≠ 0)

def FinSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (v : Pl F) (_ : E →ₐ[F] Fv F v), v ∉ X.T →
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module ℂ P) (p : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] P)
      (p' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] P), (SB _).map p = ⊤ ∧ (SB _).map p' = ⊤ ∧
      augAt om v ≤ LinearMap.ker p ∧ augAt om' v ≤ LinearMap.ker p' ∧ Nontrivial P ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → p φ = p' φ' → p φ₁ = p' φ₁') ∧
      (∀ N : Submodule ℂ P, (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
        Acts (evFin F v) (om (1, h)) φ φ₁ → p φ ∈ N → p φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      (v ∉ X.T → p (G.M.vac v) = p' (G.M'.vac v) ∧ p (G.M.vac v) ≠ 0)

def ActsEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ v : Pl F,
    (∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁) ∧
    (∀ u, At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∀ x ∈ U, x.1 ∈ UAt σ X (evFin F v) →
      x.2 ∈ UAt σ W (evFin F v) → Acts (evFin F v) (om x) φ φ

end GlobalTheory.ThK

end
