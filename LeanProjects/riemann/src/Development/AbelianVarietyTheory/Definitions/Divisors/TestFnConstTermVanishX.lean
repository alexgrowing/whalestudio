import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing

section
noncomputable section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Orb
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.Pc

section Real

variable {H n : Type} [Group H] [TopologicalSpace H] [Fintype n] [DecidableEq n]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace H] [CompleteSpace V]

structure IsPCG (ι : H →* Matrix n n ℂ) (μ : Measure H) (D : H →* (V →L[ℂ] V)) (f : H → ℂ) : Prop where

  mem : f ∈ CcMat ι

  trace_self : HasTrace (repOp D μ f) 1

  trace_other : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    (π : H →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ¬ IsUnitEquiv π D → HasTrace (repOp π μ f) 0

  orb_noncompact : ∀ s, IsRegSS (ι s) → ¬ IsCompact (cent s : Set H) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], HasOrbInt μ s dt f 0

end Real

open Formalism.REAL (UJ KG)
open Formalism.MainNotions.S (IsDS)

theorem IsPC'.isPCG {r : ℕ} {ε : Fin r → Bool} {lam : Fin r → ℤ} {μ : Measure (UJ ε)} {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] {D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)} {hD : IsDS ε (fun a => (lam a : ℝ)) D}
    {f : UJ ε → ℂ} (h : IsPC' ε lam μ D hD f) : haveI := hD.1; IsPCG (ujMat ε) μ (ujRep hD.2.2.1) f :=
  haveI := hD.1
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

end GlobalTheory.PsCo.Pc

end
end

section
open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.SplitWeil NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AutomorphicL2Unitary (conv starFn IsTopIrreducible)
open scoped TensorProduct Topology Pointwise ComplexConjugate ContDiff Matrix
noncomputable section
namespace GlobalTheory.Orb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable (L : Submodule (𝓞 E) (Fin n → E))
variable {σ J L} {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
variable [Submodule.IsLattice E L]
namespace SplitAt
omit [Submodule.IsLattice E L]
variable {v : HeightOneSpectrum (𝓞 F)} (s : SplitAt σ J L v)
variable {W : Type} [AddCommGroup W] [Module ℂ W] (μ : Measure (GLoc σ J v))
  (τ : Representation ℂ (GL (Fin n) (ResF v)) W)
end SplitAt
attribute [instance] TypeData.acg TypeData.mod TypeData.fd
section ArchFamily
variable {Hs : InfinitePlace F → Type} [∀ w, NormedAddCommGroup (Hs w)] [∀ w, InnerProductSpace ℂ (Hs w)]
  [∀ w, CompleteSpace (Hs w)]
variable {Ψ : ∀ w : InfinitePlace F, EmbOver E w} {D : ∀ w, GArch σ J w →* (Hs w →L[ℂ] Hs w)} {T : TypeData σ J L} {U : UnitaryAuxiliaryPlaceData σ J L}
  {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)}
end ArchFamily
section Cent
end Cent
section Record
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} (V : HSp D)
variable {V} {S : D.what₂.Tau → SPar} (M : DSModel V S)

def IsTestArchGX (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) : Prop :=
  ∀ ρ, haveI := (M.ds ρ).1
    GlobalTheory.PsCo.Pc.IsPCG (matAt V ρ) (μa (placeOf D ρ)) (dsRep M ρ) (fa (placeOf D ρ))

def IsTestFnGX (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (f : GA D V → ℂ) : Prop :=
  ∃ fa ff, IsTestArchGX M μa fa ∧ IsTestFin T U μf ff ∧ f = tensor D.sp.cm.sig V.gram fa ff
variable {M} {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}

theorem IsTestArchGX.mem {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} (h : IsTestArchGX M μa fa)
    (w : InfinitePlace D.host.F) : fa w ∈ CcArch D.sp.cm.sig V.gram w := by
  obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
  have := (M.ds ρ).1
  exact ccArch_eq (isCMExt_host D) (embOverOf D ρ) ▸ (h ρ).mem

theorem IsTestFnGX.isPureTensor {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {f : GA D V → ℂ} (h : IsTestFnGX M T U μa μf f) :
    IsPureTensor D.sp.cm.sig V.gram (frameLat V) f ∧ f ∈ CcGA V := by
  obtain ⟨fa, ff, ha, hf, rfl⟩ := h
  exact ⟨⟨fa, ff, ha.mem, hf.isFinFamily, rfl⟩, tensor_mem_ccAd ha.mem hf.isFinFamily⟩
end Record
end GlobalTheory.Orb
end
end

section
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TestFnConstTermVanishX : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V), HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (U : AuxiliaryPlaceHermitianSpace V)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, (μa w).IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (f : GA D V → ℂ), IsTestFnGX M T U μa μf f →
    ∀ 𝔉 : IsoFlag V, 𝔉.Proper → UnipIntegralsVanish 𝔉 f ∧ UnipIntegralsVanish 𝔉 (starFn f)

def ParabolicAndConstTermX : Prop := ParabolicAtSplitPlaces ∧ TestFnConstTermVanishX
end GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing
end
end

section
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
end Class
section TypeOf
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J γ : Matrix (Fin n) (Fin n) E)
variable {σ J γ}
end TypeOf
section Record
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {V : HSp D}

def NonFieldTypeVanishingX : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank →
  ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V),
    HypH (k := fun v : T.S => ResF v.1) T.τ →
  ∀ (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ →
  ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestArchGX M μa fa → IsTestFin T U μf ff →
  ∀ γ : GRat D.sp.cm.sig V.gram, IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 →
    LocalClause T μf ff γ ∧
    ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ) ∧
    ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ)

theorem NonFieldTypeVanishingX.zero (h : NonFieldTypeVanishingX) (hr : Odd V.rank) {S : D.what₂.Tau → SPar}
    {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} (hH : HypH (k := fun v : T.S => ResF v.1) T.τ)
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) {f : GA D V → ℂ}
    (hf : IsTestFnGX M T U μa μf f) {γ : GRat D.sp.cm.sig V.gram}
    (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) : ZeroClause μ f (ratEmb D.sp.cm.sig V.gram γ) := by
  obtain ⟨fa, ff, ha, hb, rfl⟩ := hf
  exact (h D V hr S M T U hH μa μf μ hμ fa ff ha hb γ hγ).2.2
end Record
end GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
end
end

section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ComplexConjugate Matrix
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
section Poly
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ)
variable {σ r} (P : PPol σ r)
variable (k : Type) [CommRing k] [Algebra F k]
variable {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {P k J}
variable [TopologicalSpace k]
variable (dg : Measure (HA k σ J)) (dt : Measure (Tor P k)) (f : HA k σ J → ℂ)
end Poly
section Weyl
variable {r : ℕ}
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
end Weyl
section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
end Global
section Record
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

def IsTestDataX (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V))
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : Prop :=
  Odd V.rank ∧ (∀ ρ, Gap (lam ρ)) ∧ (∀ ρ i, M.lam ρ i = lam ρ i) ∧ NoFixed T ∧
    IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ ∧ IsTestArchGX M μa fa ∧ IsTestFin T U μf ff
section Terms
variable (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
  (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ)
  (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (P : PPol D.sp.cm.sig V.rank)
  (dta : ∀ w : InfinitePlace D.host.F, Measure (Tor P w.Completion))
  (dtf : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Measure (Tor P (Fv D.host.F v)))
  (dt : Measure (Tor P (AF D.host.F)))
end Terms

def EllipticPartX : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V))
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestDataX V lam M T U μa μf μ fa ff →
    ∀ (dta : ∀ (P : PPol D.sp.cm.sig V.rank) (w : InfinitePlace D.host.F), Measure (Tor P w.Completion))
      (dtf : ∀ (P : PPol D.sp.cm.sig V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)), Measure (Tor P (Fv D.host.F v)))
      (dt : ∀ P : PPol D.sp.cm.sig V.rank, Measure (Tor P (AF D.host.F))),
      (∀ P, IsTorusMeas P (dta P) (dtf P) (dt P)) →
      (∀ P, FinOK V μf ff P (dtf P) (dt P) ∧ ∀ w, PhiOK (J := V.gram) (μa w) (dta P w) (fa w)) ∧
      (Function.support fun P => termOrb V μa μf fa ff P (dta P) (dtf P) (dt P)).Finite ∧
      Integrable (descend (GQ V) (ellKernel V (tensor D.sp.cm.sig V.gram fa ff))) (autMeasure V μ) ∧
      ∫ q, descend (GQ V) (ellKernel V (tensor D.sp.cm.sig V.gram fa ff)) q ∂autMeasure V μ =
        ∑ᶠ P, termOrb V μa μf fa ff P (dta P) (dtf P) (dt P)
end Record
end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)
noncomputable section
namespace GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

def SpecTraceX : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestDataX V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs →
      (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
        mCuspDS μ σ M ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ i, Nonempty (σ.Equiv (σs i))) →
      ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) →
        HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) (∑ i, ((mCuspDS μ (σs i) M).toNat : ℂ) * c i)

def HyperZeroX : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestDataX V lam M T U μa μf μ fa ff →
    ∀ γ : GRat D.sp.cm.sig V.gram, IsRegSS γ.1.1 → ¬ Irreducible γ.1.1.charpoly →
      ¬ GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 →
      GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ)

def EllTraceX : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestDataX V lam M T U μa μf μ fa ff →
      HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff))
        (∫ q, descend (GQ V) (ellKernel V (tensor D.sp.cm.sig V.gram fa ff)) q ∂autMeasure V μ)
end GlobalTheory.TrMult
end
end
