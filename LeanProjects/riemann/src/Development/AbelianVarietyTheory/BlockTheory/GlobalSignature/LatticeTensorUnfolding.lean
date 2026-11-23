import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal TensorProduct

abbrev RCosets {G G' : Type} [Group G] [Group G'] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotMeasure {G G' : Type} [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G']
    (j : G' →* G) (μ : Measure G) (μ' : Measure G') (ν : Measure (RCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂μ = ∫⁻ c : RCosets j, ∫⁻ h, f (j h * c.out) ∂μ' ∂ν

example {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) :
    IsQuotMeasure (1 : PUnit →* G) μ (Measure.dirac PUnit.unit)
      (μ.map (Quotient.mk (QuotientGroup.rightRel (1 : PUnit →* G).range))) := by
  intro f hf
  have hout : ∀ g : G,
      (Quotient.mk (QuotientGroup.rightRel (1 : PUnit →* G).range) g).out = g := by
    intro g
    have h := Quotient.mk_out (s := QuotientGroup.rightRel (1 : PUnit →* G).range) g
    rw [QuotientGroup.rightRel_apply] at h
    obtain ⟨u, hu⟩ := h
    have h1 : (1 : G) = g * (Quotient.mk (QuotientGroup.rightRel (1 : PUnit →* G).range) g).out⁻¹ := by
      simpa using hu
    exact (mul_inv_eq_one.1 h1.symm).symm
  have hm : Measurable fun c : RCosets (1 : PUnit →* G) => f c.out := by
    rw [measurable_from_quotient]
    have : ((fun c : RCosets (1 : PUnit →* G) => f c.out) ∘ Quotient.mk'') = f := by
      funext g; exact congrArg f (hout g)
    rw [this]; exact hf
  simp only [MonoidHom.one_apply, one_mul, lintegral_const, measure_univ, mul_one]
  rw [lintegral_map hm measurable_quotient_mk'']
  exact lintegral_congr fun g => (congrArg f (hout g)).symm

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def coords (W : HSpace E) (x : W.V) : Fin 1 → Fin W.rank → E := fun _ i => W.frame.repr x i

end Coord

def latTensor {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator (fun _ => (1 : ℝ≥0∞)) (projFin X 0) *
    Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (y : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) y)

def IsInfQuotIntegral (D : D7) : letI := D.host.cmStar; ∀ (W : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_x : W.V) (_Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞)
    (_I : ℝ≥0∞), Prop :=
  letI := D.host.cmStar
  fun W P Q P' Q' x Φi I =>
  AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
    ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
  AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
  let xr : D.what₂.Tau → (Fin P ⊕ Fin Q → ℂ) :=
    fun ρ => A ρ *ᵥ fun i => embOf D ρ (coords W x 0 i)
  AllSome (fun C : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ =>
    ∀ ρ, (C ρ)ᴴ * Formalism.UG.Jpq P Q * C ρ = Formalism.UG.Jpq P' Q' ∧
      ((C ρ)ᴴ * Formalism.UG.Jpq P Q) *ᵥ xr ρ = 0) fun C =>
  AllSome (fun j : (D.what₂.Tau → UpqT P' Q') →* (D.what₂.Tau → UpqT P Q) =>
    ∀ b ρ, UpqT.mat (j b ρ) * C ρ = C ρ * UpqT.mat (b ρ) ∧
      UpqT.mat (j b ρ) *ᵥ xr ρ = xr ρ) fun j =>
  AllSome (fun o : (D.what₂.Tau → UpqT P Q) →
      (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    ∀ g ρ, (A ρ *ᵥ fun i => θ ρ (o g 0 i)) = UpqT.mat (g ρ)⁻¹ *ᵥ xr ρ) fun o =>
  AllSome (IsQuotMeasure j (Measure.pi fun _ => D.cd.cd P Q) (Measure.pi fun _ => D.cd.cd P' Q'))
    fun ν => ∫⁻ c : RCosets j, Φi (o c.out) ∂ν = I

def HidaSetting {E : Type} [Field E] [NumberField E] [StarRing E] (W W' : HSpace E)
    (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[E] W.V) : Prop :=
  W.SigOK ∧ (∀ τ, W.sig τ = (P, Q)) ∧ 3 ≤ W.rank ∧
  (if s then P = P' + 1 ∧ Q = Q' else P = P' ∧ Q = Q' + 1) ∧
  W.hT x x = (if s then 1 else -1) ∧ x ∈ W.L0 ∧
  HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧
  W'.SigOK ∧ (∀ τ, W'.sig τ = (P', Q'))

def UnfoldAt (D : D7) : letI := D.host.cmStar; ∀ (W _W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_s : Bool) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' s x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
  ∀ (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
  ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
    ∃ I : ℝ≥0∞, IsInfQuotIntegral D W P Q P' Q' x Φi I ∧
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)},
        atInv D.sp.cm.sig W.gram (latTensor (L0c D W) Φi) h (coords W x'.1) ∂μ = μ' 𝓕' * I

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V),
    HidaSetting W W' P Q P' Q' s x ι → (∀ y : W'.V, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
    UnfoldAt D W W' P Q P' Q' s x

def UnfoldingAnyLattice (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V),
    HidaSetting W W' P Q P' Q' s x ι → UnfoldAt D W W' P Q P' Q' s x

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding
