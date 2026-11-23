import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValApplySubLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (lamF upIdele)

namespace GlobalTheory.ToricRational

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

def RatioConj : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ →
    ∀ (Ω : Type) [Field Ω] [Algebra H.K Ω] [IsAlgClosure H.K Ω] (j : Ω →+* ℂ) (τ₀ : I),
    (∀ x : H.K, j (algebraMap H.K Ω x) = φ τ₀ x) →
    ∀ art : Ideles H.K →* Gab H.K Ω, IsGlobalArtin art →
    ∀ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ → T₀ ≠ 0 →
    ∀ Q : Finset (HeightOneSpectrum (OF H.E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → Finite (PicO (condQ 𝔣 Q)) →
    ∀ T : PicO (condQ 𝔣 Q) → ℂ, (∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q)) →
    ∃ ρ : (PicO (condQ 𝔣 Q) →* Ωˣ) → Ω,
      (∀ ψ, j (ρ ψ) = (∑ᶠ q, (j (ψ q))⁻¹ * T q) / T₀) ∧
      ∀ g : G H.K Ω, (∀ (x : Ω) (τ : I) (y : H.E), j x = φ τ y → g x = x) → (∀ (x : Ω) (y : (Af H.E)ˣ), j x = lamF s χ y → g x = x) →
        ∀ t : (Af H.K)ˣ, art (finIdele H.K t) = toAb H.K Ω g⁻¹ → ∀ ψ : PicO (condQ 𝔣 Q) →* Ωˣ,
          g (ρ ψ) = (g (ψ (QuotientGroup.mk (upIdele H.K H.E t))))⁻¹ * ρ ((Units.map g.toRingEquiv.toMonoidHom).comp ψ)

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def setTh (th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i)) : NTw D.R D.host D.what₂ D.LL0 N :=
  { X with th := th }

def IsValueCharAt (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (s : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E),
    IsHostDatum D.host φ s κ 𝔣 χ ∧ (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
    ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (val χ P : ℂ) = 1

def IsValueTied : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s → IsValueCharAt X i (atSide X (X.sideL i lam) ι) lam s

def IsGalTied : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ (e : FractionRing (X.O0 i) →+* Qbar (X.l i)) (ι : Qbar (X.l i) ≃+* ℂ)
    (art : Ideles D.host.E →* Gab D.host.E N.Om), IsGlobalArtin art ∧
    (∀ z : ℤ_[X.l i], e (algebraMap (X.O0 i) _ (algebraMap ℤ_[X.l i] (X.O0 i) z)) =
      algebraMap ℚ_[X.l i] (Qbar (X.l i)) (z : ℚ_[X.l i])) ∧
    (∀ x : D.LL0, ι (e (X.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s →
      ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E)
        (n : (D.host.E →+* ℂ) → ℤ) (r : G D.host.E N.Om →* (X.O0 i)ˣ),
        IsHostDatum D.host φ s κ 𝔣 χ ∧ (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
        GlobalTheory.GalChar.IsGal art e (GlobalTheory.GalChar.sideIso ι (X.sideL i lam)) χ n r ∧
        X.lamG i lam = (Units.map (algebraMap (X.O0 i) (X.O i)).toMonoidHom).comp r

variable {X}

theorem isValueTied_of_isToricElt (h : IsToricElt X) : IsValueTied X := fun i hi =>
  let ⟨ι, h1, h2⟩ := h i hi
  ⟨ι, h1, fun lam s hs =>
    let ⟨I, j, φ, κ, 𝔣, χ, _, a, b, c, _⟩ := h2 lam s hs
    ⟨I, j, φ, κ, 𝔣, χ, a, b, c⟩⟩

theorem toBar_algebraMap (i : X.Tw) (a : X.O0 i) :
    toBar X i (algebraMap (X.O0 i) _ a) = algebraMap (X.O i) (Kbar X i) (algebraMap (X.O0 i) (X.O i) a) := by
  rw [toBar, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem IsGalTied.isValueTied (h : IsGalTied X) : IsValueTied X := by
  intro i hi
  obtain ⟨e, ι, art, ha, he, hι, hl⟩ := h i hi
  let _ : Algebra (FractionRing (X.O0 i)) (Qbar (X.l i)) := e.toAlgebra
  let _ : Algebra (FractionRing (X.O0 i)) (Kbar X i) := (toBar X i).toAlgebra
  have : Algebra.IsAlgebraic (FractionRing (X.O0 i)) (Qbar (X.l i)) := ⟨fun x => by
    have h1 : IsAlgebraic ℤ_[X.l i] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[X.l i] ℚ_[X.l i] _).2 (Algebra.IsAlgebraic.isAlgebraic x)
    refine h1.ringHom_of_comp_eq ((algebraMap (X.O0 i) _).comp (algebraMap ℤ_[X.l i] (X.O0 i))) (RingHom.id _)
      (fun a b hab => ?_) (RingHom.ext he)
    have := congrArg e hab
    rw [RingHom.comp_apply, RingHom.comp_apply, he, he] at this
    exact Subtype.ext ((algebraMap ℚ_[X.l i] (Qbar (X.l i))).injective this)⟩
  let J : Qbar (X.l i) →ₐ[FractionRing (X.O0 i)] Kbar X i := IsAlgClosed.lift
  have hJ : ∀ x, J (e x) = toBar X i x := J.commutes
  refine ⟨J.toRingHom.comp ι.symm.toRingHom, fun x => ?_, fun lam s hs => ?_⟩
  · rw [← hι, ← hJ]
    exact congrArg J (ι.symm_apply_apply _)
  obtain ⟨I, _, φ, κ, 𝔣, χ, n, r, hD, h𝔣, hr, hG⟩ := hl lam s hs
  refine ⟨I, inferInstance, φ, κ, 𝔣, χ, hD, h𝔣, fun P hP => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 P)
  have hu : χ.UnrAt P := by
    have e := (hD.2.2.2.2.2.2.2.2 _ P (over_below P)).2 (Finset.notMem_empty _)
    rwa [expIn, multiplicity_eq_zero.2 fun h => hP (h𝔣 P h), expAt_zero_iff] at e
  have h1 := hr.frob ha (Or.inl fun h => hP (X.twistExcludedPlaces_contains_residueChar i h)) hu (N.plOm.2 P) hσ
  have h2 : ∀ b x, atSide X b (J.toRingHom.comp ι.symm.toRingHom) (GlobalTheory.GalChar.sideIso ι b x) = J x := fun b x => by
    cases b
    · show J (ι.symm (starRingEnd ℂ (starRingEnd ℂ (ι x)))) = _
      rw [Complex.conj_conj, ι.symm_apply_apply]
    · exact congrArg J (ι.symm_apply_apply x)
  have h3 := congrArg (atSide X (X.sideL i lam) (J.toRingHom.comp ι.symm.toRingHom)) h1
  rw [h2, map_inv₀, GlobalTheory.GalChar.toQ, RingHom.comp_apply, hJ, toBar_algebraMap] at h3
  rw [X.Xv_def i lam P hP σ hσ, hG]
  exact (congrArg (· * _) h3).trans (inv_mul_cancel₀ ((map_ne_zero _).2 (Units.ne_zero _)))

end GlobalTheory.ToricRational
