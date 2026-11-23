import Development.WeilBound.ThetaLifts.CTKernel

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F) in

abbrev Fl (v : Pl F) (n d : ℕ) : Type := (Fin n × Fin d → Fv F v) → ℂ

variable (F) in

def idem (v : Pl F) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)

open Classical in

def opF {κ : Type} [Fintype κ] (v : Pl F) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ : (κ → Fv F v) → ℂ) : (κ → Fv F v) → ℂ :=
  if h : ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ φ₁ then h.choose else 0

open Classical in

def opI {κ : Type} [Fintype κ] (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f : SInf F κ) : SInf F κ :=
  if h : ∃ f₁ : SInf F κ, Acts (evI F) T f f₁ then h.choose else 0

variable (E) in

def idAt {R : Type} [Zero R] (ev : AF F → R) : Subgroup (AE F E)ˣ :=
  Subgroup.closure {l | At ev ((l : AE F E) - 1)}

section Pair

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def kAt {R : Type} [Zero R] (K : Subgroup (UA σ X.J)) (ev : AF F → R) : Subgroup (UA σ X.J) :=
  K ⊓ Subgroup.closure (UAt σ X ev)

structure LocMeas (K : Subgroup (UA σ X.J)) where

  kf : ∀ v : Pl F, Measure (kAt K (evFin F v))

  xf : ∀ v : Pl F, @Measure (idAt E (evFin F v)) (borel _)

  ki : Measure (kAt K (evI F))

  xi : @Measure (idAt E (evI F)) (borel _)

structure LocMeas.Is {K : Subgroup (UA σ X.J)} (m : LocMeas K) : Prop where
  kf : ∀ v, (m.kf v).IsHaarMeasure ∧ m.kf v Set.univ = 1
  xf : ∀ v, @Measure.IsHaarMeasure _ _ _ (borel _) (m.xf v) ∧
    m.xf v {l | IsCompact (closure (Subgroup.zpowers l : Set (idAt E (evFin F v))))} = 1
  ki : m.ki.IsHaarMeasure
  xi : @Measure.IsHaarMeasure _ _ _ (borel _) m.xi

structure IsEvLoc (M : Model σ X W) (M₁ : Model σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) (ev : ∀ v : Pl F, Fl F v n d →ₗ[ℂ] Fl F v n₁ d₁) : Prop where
  ne : ei ≠ 0
  vac : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _
  pure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

def coneF (B : Base F E) (M : Model σ X W) (om : Rep σ X W) {K : Subgroup (UA σ X.J)} (m : LocMeas K) (v : Pl F)
    (ev : Fl F v n d →ₗ[ℂ] Fl F v n₁ d₁) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)
    (φ : Fl F v n d) : Fl F v n₁ d₁ :=
  fun y => ∫ k, @integral _ _ _ _ (borel _) (m.xf v) (fun l =>
    ev (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) ∂(m.kf v)

def IsConeI (B : Base F E) (M : Model σ X W) (om : Rep σ X W) {K : Subgroup (UA σ X.J)} (m : LocMeas K)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E)
    (z : ℕ) (L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) : Prop :=
  ∀ f y, L f y = ∫ k, @integral _ _ _ _ (borel _) m.xi (fun l =>
    ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u l.1) (om (k.1, 1) Φ)) f) y * (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) ∂m.ki

def IsFiniteLocalEquivariantMap (om : Rep σ X W) (om₁ : Rep σ X₁ W₁) (H' : Plane E d d₁) (v : Pl F) (χ : Chr F E) (r : ℝ) {P P₁ : Type}
    [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁] (p : Fl F v n d →ₗ[ℂ] P) (p₁ : Fl F v n₁ d₁ →ₗ[ℂ] P₁)
    (lam : P →ₗ[ℂ] P₁) : Prop :=
  ∀ t h₁ m, IsLevi H' t h₁ m → ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → m ∈ UAt σ W (evFin F v) →
    ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _, Acts (evFin F v) (om (1, u * m)) φ φ' →
      Acts (evFin F v) (om₁ (1, h₁)) φ₁ φ₁' → lam (p φ) = p₁ φ₁ →
      lam (p φ') = ((χ t : ℂ) * (((absE F E t : ℝ) ^ r : ℝ) : ℂ)) • p₁ φ₁'

structure IsArchimedeanLocalEquivariantMap (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (om : Rep σ X W) (om₁ : Rep σ X₁ W₁)
    (H' : Plane E d d₁) (χ : Chr F E) (r : ℝ) {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (lam : P →ₗ[ℂ] P₁) : Prop where
  unip : ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f' : SInf F _,
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f' → lam (p f') = 0
  levi : ∀ γ ∈ Lines σ W, ∀ γ₁ ∈ Lines σ W₁, ∀ τ : ℝ → (AE F E)ˣ,
    (∀ s, IsLevi H' (τ s) (γ₁ (Multiplicative.ofAdd s)) (γ (Multiplicative.ofAdd s))) → ∀ c : ℂ,
    HasDerivAt (fun s => (χ (τ s) : ℂ) * (((absE F E (τ s) : ℝ) ^ r : ℝ) : ℂ)) c 0 →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ ∈ M₁.Pol B.ψ B.emb, ∀ (f' : SInf F _) (f₁' : SInf F _),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f' →
    ActsD (evI F) (fun t => om₁ (1, γ₁ (Multiplicative.ofAdd t))) f₁ f₁' → lam (p f) = p₁ f₁ →
      lam (p f') = c • p₁ f₁ + p₁ f₁'
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ k₁ ∈ KInf σ W₁ B.emb, ∀ t, IsLevi H' t k₁ k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ ∈ M₁.Pol B.ψ B.emb, ∀ (f' : SInf F _) (f₁' : SInf F _), Acts (evI F) (om (1, k)) f f' →
    Acts (evI F) (om₁ (1, k₁)) f₁ f₁' → lam (p f) = p₁ f₁ →
      lam (p f') = ((χ t : ℂ) * (((absE F E t : ℝ) ^ r : ℝ) : ℂ)) • p₁ f₁'

end Pair

def NZ {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) : Prop :=
  (∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0) ∧ ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ' ≠ 0

end PositivityTheory.ThKG.Loc

end
