import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped ENNReal TensorProduct

abbrev RightCosets {G' G : Type} [Group G'] [Group G] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotientMeasure {G' G : Type} [Group G'] [Group G] [MeasurableSpace G'] [MeasurableSpace G]
    (j : G' →* G) (m' : Measure G') (m : Measure G) (ν : Measure (RightCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂m = ∫⁻ c, ∫⁻ g', f (j g' * Quotient.out c) ∂m' ∂ν

def IsStabEmb {P' Q' P Q : ℕ} (x₀ : Fin P ⊕ Fin Q → ℂ) (j : UpqT P' Q' →* UpqT P Q) : Prop :=
  ∃ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ,
    Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' ∧
    (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x₀ = 0 ∧
    ∀ g' : UpqT P' Q', UpqT.mat (j g') *ᵥ x₀ = x₀ ∧ UpqT.mat (j g') * C = C * UpqT.mat g'

def piEmb {T : Type} {P' Q' P Q : ℕ} (j : T → (UpqT P' Q' →* UpqT P Q)) :
    (T → UpqT P' Q') →* (T → UpqT P Q) where
  toFun g ρ := j ρ (g ρ)
  map_one' := by funext ρ; simp
  map_mul' g h := by funext ρ; simp

def infCoord {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M P Q : ℕ}
    (θ : Ainf F ⊗[F] E →+* ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) : Fin P ⊕ Fin Q → ℂ :=
  A *ᵥ fun i => θ (Y 0 i)

def phiLat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator 1 (projFin X 0) * Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) x)

def coordTup {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) (x : W.V) :
    Fin 1 → Fin W.rank → E :=
  fun _ i => W.frame.repr x i

def UnfoldAt (D : D7) : letI := D.host.cmStar;
    ∀ (W W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ) (_β : D.host.E) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' β x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram))
    (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
    AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
      ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
    AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
    AllSome (fun j : D.what₂.Tau → (UpqT P' Q' →* UpqT P Q) =>
      ∀ ρ, IsStabEmb (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) (j ρ)) fun j =>
    AllSome (IsQuotientMeasure (piEmb j) (Measure.pi fun _ => D.cd.cd P' Q')
      (Measure.pi fun _ => D.cd.cd P Q)) fun ν =>
    AllSome (fun pt : (D.what₂.Tau → UpqT P Q) →
        (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
      ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) =
        UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i))) fun pt =>
    ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = β},
          atInv D.sp.cm.sig W.gram (phiLat (L0c D W) Φi) h (coordTup W x'.1) ∂μ =
        μ' 𝓕' * ∫⁻ c, Φi (pt (Quotient.out c)) ∂ν

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) → x ∈ W.L0 →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) →
      (∀ y, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
      UnfoldAt D W W' P Q (if s then P - 1 else P) (if s then Q else Q - 1) (if s then 1 else -1) x

def UnfoldingAnyLattice (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) → x ∈ W.L0 →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) →
      UnfoldAt D W W' P Q (if s then P - 1 else P) (if s then Q else Q - 1) (if s then 1 else -1) x

theorem IsStabEmb.inv_mul_fix {P' Q' P Q : ℕ} {x₀ : Fin P ⊕ Fin Q → ℂ} {j : UpqT P' Q' →* UpqT P Q}
    (hj : IsStabEmb x₀ j) (g' : UpqT P' Q') (g : UpqT P Q) :
    UpqT.mat (j g' * g)⁻¹ *ᵥ x₀ = UpqT.mat g⁻¹ *ᵥ x₀ := by
  obtain ⟨C, -, -, h⟩ := hj
  have h1 := (h g'⁻¹).1
  have e : UpqT.mat (j g' * g)⁻¹ = UpqT.mat g⁻¹ * UpqT.mat (j g'⁻¹) := by
    rw [_root_.mul_inv_rev, ← map_inv]; rfl
  rw [e, ← Matrix.mulVec_mulVec, h1]

example (P Q : ℕ) : IsStabEmb (0 : Fin P ⊕ Fin Q → ℂ) (MonoidHom.id (UpqT P Q)) :=
  ⟨1, by simp, by simp, fun g => ⟨by simp, by simp⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
