import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VLeOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem GlobalTheory.CommonReading.norm_aut {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem GlobalTheory.CommonReading.norm_aut_le {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (x : Formalism.L2.TwC.intOf l K) : ‖τ x‖ ≤ 1 := by
  rw [GlobalTheory.CommonReading.norm_aut, ← PadicAlgCl.valuation_coe]
  exact_mod_cast x.2.2

namespace GlobalTheory.HeightCounting.SameTw

def Reads (D : D7) (C : NChoice D) (w : D.what₂.places.Pl) {Λ : Type} [Field Λ] (e : D.what₂.LL →+* Λ)
    (φ : D.ntw.O0 (C.twI w) →+* Λ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (τ : Λ →+* Ω) (ι : FractionRing (C.Oe w) →+* Ω),
    (∀ y, τ (φ y) = ι (algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) y)))) ∧
    ∀ x : D.what₂.LL, τ (e x) = ι (C.embW w x)

theorem exists_reads (D : D7) (C : NChoice D) (F : TwFrameC D) {low : Finset ℕ} (hF : TwistFrameLowIndexCompatibility D F low) (w : D.what₂.places.Pl)
    (l : ℕ) [Fact l.Prime] (hl : D.ntw.l (C.twI w) = l) (e : D.what₂.LL →+* PadicAlgCl l)
    (he : ∀ x, 0 ≤ D.what₂.places.val w x ↔ ‖e x‖ ≤ 1) :
    ∃ φ : D.ntw.O0 (C.twI w) →+* PadicAlgCl l, Reads D C w e φ ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
      (∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ y, φ y ∈ K) ∧
      ∀ (z : ℤ_[D.ntw.l (C.twI w)]) (z' : ℤ_[l]), HEq z z' →
        φ (algebraMap _ (D.ntw.O0 (C.twI w)) z) = algebraMap ℚ_[l] (PadicAlgCl l) (z' : ℚ_[l]) := by
  subst hl
  haveI := C.Oe_fin w
  obtain ⟨σ, ι, h1, h2⟩ := GlobalTheory.CommonReading.exists_common (C.Oe_inj w)
    ((Subring.subtype _).comp (F.eOk (C.twI w) (C.k' w)).toRingHom)
    (Subtype.val_injective.comp (F.eOk (C.twI w) (C.k' w)).injective)
    (fun y => (F.eOk (C.twI w) (C.k' w) y).2.2) (C.embW w) e fun x => (C.embW_w w x).symm.trans (he x)
  refine ⟨σ.symm.toAlgHom.toRingHom.comp ((Subring.subtype _).comp (F.eO0 (C.twI w)).toRingHom),
    ⟨ℂ_[D.ntw.l (C.twI w)], inferInstance, (algebraMap (PadicAlgCl (D.ntw.l (C.twI w))) ℂ_[D.ntw.l (C.twI w)]).comp
      σ.toAlgHom.toRingHom, ι, fun y => ?_,
      fun x => (h2 x).symm⟩, fun y => ?_, ⟨(F.K0 (C.twI w)).1.map σ.symm.toAlgHom, ?_, fun y => ⟨_, (F.eO0 (C.twI w) y).2.1, rfl⟩⟩, ?_⟩
  · rw [h1]
    refine Eq.trans ?_ ((hF.eOk_alg _ _ _).trans (hF.eO_alg _ y)).symm
    simp
  · exact GlobalTheory.CommonReading.norm_aut_le σ.symm _ (F.eO0 (C.twI w) y)
  · haveI := (F.K0 (C.twI w)).2
    exact LinearEquiv.finiteDimensional (IntermediateField.equivMap _ σ.symm.toAlgHom).toLinearEquiv
  · rintro z _ ⟨⟩
    change σ.symm (F.eO0 (C.twI w) _ : PadicAlgCl _) = _
    rw [hF.ringSpec_baseIntegersEquiv_algebraMap, AlgEquiv.commutes]

theorem Reads.emb {D : D7} {C : NChoice D} (hC : ChoiceC D C) {w : D.what₂.places.Pl} (hw : TwistedAt D w) {Λ : Type} [Field Λ]
    {e : D.what₂.LL →+* Λ} {φ : D.ntw.O0 (C.twI w) →+* Λ} (h : Reads D C w e φ) (x : D.LL0) (y : D.ntw.O0 (C.twI w))
    (hy : algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y =
      (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x) : e x = φ y := by
  obtain ⟨Ω, _, τ, ι, h1, h2⟩ := h
  apply τ.injective
  rw [h1, h2, hC.emb_side w hw x]
  have : (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x) =
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y := by
    rw [hy]; split_ifs <;> rfl
  rw [this, fracOe, IsFractionRing.map, IsLocalization.map_eq]
  rfl

theorem Reads.of_comp {D : D7} {C : NChoice D} {w : D.what₂.places.Pl} {Λ Λ' : Type} [Field Λ] [Field Λ'] (q : Λ →+* Λ')
    {e : D.what₂.LL →+* Λ} {φ : D.ntw.O0 (C.twI w) →+* Λ} (h : Reads D C w (q.comp e) (q.comp φ)) : Reads D C w e φ :=
  let ⟨Ω, i, τ, ι, h1, h2⟩ := h
  ⟨Ω, i, τ.comp q, ι, h1, h2⟩

def OneField (D : D7) (C : NChoice D) : Prop :=
  ∀ a : D.nd.Loc, ∃ f : D.ntw.O0 (C.twI (D.nd.w a)) →+* D.nd.O a, HEq f (D.ntw.twist₂ a) ∧
    Reads D C (D.nd.w a) (D.nd.embK a) ((algebraMap (D.nd.O a) (FractionRing (D.nd.O a))).comp f)

def TwReads {D : D7} (C : NChoice D) (X : LocNd (lay0 D)) (T : LocTw X) : Prop :=
  ∀ a : X.nd.Loc, ∃ f : D.ntw.O0 (C.twI (X.nd.w a)) →+* X.nd.O a, HEq f (T.twist₂ a) ∧
    Reads D C (X.nd.w a) (X.nd.embK a) ((algebraMap (X.nd.O a) (FractionRing (X.nd.O a))).comp f)

set_option maxHeartbeats 2000000 in

theorem oneField_withLoc {D : D7} (L : LocAll (lay0 D)) (C : NChoice D) :
    OneField (withLoc L) (chL L C) ↔ TwReads C L.X L.T := Iff.rfl

theorem sameChar_of_inj {O₀ O₁ O₂ Γ Ω : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ] [CommRing Ω]
    (f₁ : O₀ →+* O₁) (f₂ : O₀ →+* O₂) (ψ₁ : Γ →* O₁ˣ) (ψ₂ : Γ →* O₂ˣ) (j₁ : O₁ →+* Ω) (j₂ : O₂ →+* Ω)
    (h₁ : Function.Injective j₁) (h₂ : Function.Injective j₂) (hf : ∀ y, j₁ (f₁ y) = j₂ (f₂ y))
    (hψ : ∀ g, j₁ (ψ₁ g : O₁ˣ) = j₂ (ψ₂ g : O₂ˣ)) : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂ := by
  intro F
  rw [← map_eq_zero_iff j₁ h₁, ← map_eq_zero_iff j₂ h₂]
  simp only [Finsupp.sum, map_sum, map_mul, hf, hψ]

theorem sameTwist_of_oneField (D : D7) (C : NChoice D) (hT : NChTie D C) (h : OneField D C) : GlobalTheory.PtCore.SameTwist D C := by
  intro a
  obtain ⟨f, hf, Ω, _, ιA, ιB, h1, h2⟩ := h a
  obtain ⟨ψ0, -, hw, hl⟩ := hT.psi_eq
  refine (GlobalTheory.PtCore.sameTwistAt_iff D a _ _ _).2 ⟨hT.twOf_eq a, f, hf, ?_⟩
  refine sameChar_of_inj _ _ _ _ (ιA.comp (algebraMap (D.nd.O a) (FractionRing (D.nd.O a))))
    (ιB.comp ((algebraMap (C.Oe (D.nd.w a)) (FractionRing (C.Oe (D.nd.w a)))).comp
      (algebraMap (D.ntw.Ok (C.twI (D.nd.w a)) (C.k' (D.nd.w a))) (C.Oe (D.nd.w a)))))
    (ιA.injective.comp (IsFractionRing.injective _ _))
    (ιB.injective.comp ((IsFractionRing.injective (C.Oe (D.nd.w a)) _).comp (C.Oe_inj _))) h1 fun g => ?_
  have := h2 ((ψ0 (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL)
  rw [hl, hw] at this
  exact this

end GlobalTheory.HeightCounting.SameTw
