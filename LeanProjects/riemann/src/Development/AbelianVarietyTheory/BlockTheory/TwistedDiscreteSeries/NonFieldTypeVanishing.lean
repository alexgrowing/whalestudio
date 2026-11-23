import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.Orb NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms (plusAlg genAlg)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH NoFixed radical)
open Formalism.UG (cT)
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

section Class

variable {G : Type} [Group G]

def ratClass (Γ : Subgroup G) (γ : G) : Set G := {δ | ∃ g ∈ Γ, δ = g⁻¹ * γ * g}

def classKernel (Γ : Subgroup G) (γ : G) (f : G → ℂ) (x : G) : ℂ := ∑' δ : ratClass Γ γ, f (x⁻¹ * δ * x)

def HasClassInt [MeasurableSpace G] (Γ : Subgroup G) (μ : Measure G) (𝓕 : Set G) (γ : G) (f : G → ℂ) (c : ℂ) : Prop :=
  (∀ x, Summable fun δ : ratClass Γ γ => f (x⁻¹ * δ * x)) ∧ IntegrableOn (classKernel Γ γ f) 𝓕 μ ∧
    ∫ x in 𝓕, classKernel Γ γ f x ∂μ = c

theorem classKernel_mul {Γ : Subgroup G} (γ : G) (f : G → ℂ) {g : G} (hg : g ∈ Γ) (x : G) :
    classKernel Γ γ f (g * x) = classKernel Γ γ f x := by
  have key : ∀ g ∈ Γ, ∀ δ ∈ ratClass Γ γ, g⁻¹ * δ * g ∈ ratClass Γ γ := by
    rintro g hg _ ⟨a, ha, rfl⟩
    exact ⟨a * g, mul_mem ha hg, by group⟩
  let e : ratClass Γ γ ≃ ratClass Γ γ :=
    { toFun := fun δ => ⟨g⁻¹ * δ * g, key g hg _ δ.2⟩
      invFun := fun δ => ⟨g⁻¹⁻¹ * δ * g⁻¹, key _ (inv_mem hg) _ δ.2⟩
      left_inv := fun δ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun δ => Subtype.ext (by simp [mul_assoc]) }
  rw [classKernel, classKernel, ← e.tsum_eq fun δ => f (x⁻¹ * δ * x)]
  exact tsum_congr fun δ => congrArg f (by simp [e, mul_assoc])

end Class

section TypeOf

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J γ : Matrix (Fin n) (Fin n) E)

def IsNonFieldAniso : Prop :=
  IsRegSS γ ∧ ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)),
    Nonempty (plusAlg σ J γ ≃ₐ[F] ∀ i, K i) ∧ 2 ≤ k ∧ ∀ i, IsField (K i ⊗[F] E)

variable {σ J γ}

def factorIdem {k : ℕ} {K : Fin k → Type} [∀ i, Field (K i)] [∀ i, Algebra F (K i)]
    (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) : Matrix (Fin n) (Fin n) E :=
  ((e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ)

def IsOrthSplit (σ : E →ₐ[F] E) (J γ ε : Matrix (Fin n) (Fin n) E) : Prop :=
  ε * ε = ε ∧ cT (σ : E →+* E) ε * J = J * ε ∧ cT (σ : E →+* E) (1 - ε) * J * ε = 0 ∧
    (∀ l ∈ genAlg γ, l * ε = ε * l) ∧ 0 < ε.rank ∧ ε.rank < n

end TypeOf

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

def LocalClause (T : TypeDataG V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (γ : GRat D.sp.cm.sig V.gram) : Prop :=
  ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra D.host.F (K i)]
    (e : plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, K i) (i : Fin k),
    IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (factorIdem e i) ∧
    (factorIdem e i).rank = Module.finrank D.host.E (D.host.E ⊗[D.host.F] K i) ∧
    ∀ v : T.S, NoFixed (T.τ v) (radical (ResF v.1) V.rank (factorIdem e i).rank) →
      ∀ dt : Measure (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))), dt.IsHaarMeasure →
        HasOrbInt (μf v) (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) dt (ff v) 0

def ProductClause (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (μ : Measure (GA D V)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ)
    (γ : GA D V) : Prop :=
  ∀ (dta : ∀ w, Measure (cent (projArch D.sp.cm.sig V.gram w γ)))
    (dtf : ∀ v, Measure (cent (proj D.sp.cm.sig V.gram v γ))) (dt : Measure (cent γ)),
    IsCentProd (frameLat V) γ dta dtf dt →
    ∀ 𝓣 : Set (cent γ), IsFundamentalDomain ((GQ V).subgroupOf (cent γ)) 𝓣 dt →
      dt 𝓣 < ∞ ∧
      ∃ (oa : InfinitePlace D.host.F → ℂ) (ob : HeightOneSpectrum (𝓞 D.host.F) → ℂ),
        (∀ w, HasOrbInt (μa w) (projArch D.sp.cm.sig V.gram w γ) (dta w) (fa w) (oa w)) ∧
        (∀ v, HasOrbInt (μf v) (proj D.sp.cm.sig V.gram v γ) (dtf v) (ff v) (ob v)) ∧
        (∀ᶠ v in cofinite, ob v = 1) ∧
        HasOrbInt μ γ dt (tensor D.sp.cm.sig V.gram fa ff) ((∏ w, oa w) * ∏ᶠ v, ob v) ∧
        ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ →
          HasClassInt (GQ V) μ 𝓕 γ (tensor D.sp.cm.sig V.gram fa ff) (dt.real 𝓣 * ((∏ w, oa w) * ∏ᶠ v, ob v))

def ZeroClause (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ : GA D V) : Prop :=
  ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ → HasClassInt (GQ V) μ 𝓕 γ f 0

def NonFieldTypeVanishing : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank →
  ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V),
    HypH (k := fun v : T.S => ResF v.1) T.τ →
  ∀ (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ →
  ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestArchG M μa fa → IsTestFin T U μf ff →
  ∀ γ : GRat D.sp.cm.sig V.gram, IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 →
    LocalClause T μf ff γ ∧
    ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ) ∧
    ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ)

theorem NonFieldTypeVanishing.zero (h : NonFieldTypeVanishing) (hr : Odd V.rank) {S : D.what₂.Tau → SPar}
    {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} (hH : HypH (k := fun v : T.S => ResF v.1) T.τ)
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) {f : GA D V → ℂ}
    (hf : IsTestFnG M T U μa μf f) {γ : GRat D.sp.cm.sig V.gram}
    (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) : ZeroClause μ f (ratEmb D.sp.cm.sig V.gram γ) := by
  obtain ⟨fa, ff, ha, hb, rfl⟩ := hf
  exact (h D V hr S M T U hH μa μf μ hμ fa ff ha hb γ hγ).2.2

end Record

example {G : Type} [CommGroup G] (Γ : Subgroup G) (γ : G) (f : G → ℂ) (x : G) : classKernel Γ γ f x = f γ := by
  have e : ratClass Γ γ = {γ} := Set.ext fun δ =>
    ⟨fun ⟨g, _, h⟩ => by simp [h], fun h => ⟨1, one_mem _, by simpa using h⟩⟩
  rw [classKernel, e, tsum_singleton γ fun δ => f (x⁻¹ * δ * x)]
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
