import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingExtensionOfRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystemsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertEigenvaluesIffThetaLiftInertLabelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem exists_passage_of_labels {Ix C α β L : Type} [Infinite L] (S : Finset (α → L)) (r : β → α) (hr : Function.Injective r)
    (e : Ix → α → L) (hS : ∀ p, e p ∈ S) (Car : Ix → C → Prop) (Sys : C → (β → L) → Prop) (Lab : C → C → Prop)
    (hE : ∀ p p' c c', Car p c → Car p' c' → ((∀ k, e p (r k) = e p' (r k)) ↔ Lab c c'))
    (hW : ∀ c c' f f', Sys c f → Sys c' f' → ((∀ k, f k = f' k) ↔ Lab c c')) :
    ∃ t : (α → L) → α → L, (∀ p c, Car p c → ∀ f, Sys c f → ∀ k, f k = t (e p) (r k)) ∧
      ∀ a ∈ S, ∀ b ∈ S, (∃ k, a (r k) ≠ b (r k)) → ∃ k, t a (r k) ≠ t b (r k) := by
  obtain ⟨t, h1, h2⟩ := exists_separating_extension_of_rel S r
    (fun a f => ∃ p, e p = a ∧ ∃ c, Car p c ∧ Sys c f) hr (by
      rintro a - b - f f' ⟨p, rfl, c, hc, hf⟩ ⟨p', rfl, c', hc', hf'⟩
      constructor
      · intro h
        funext k
        exact (hW c c' f f' hf hf').2 ((hE p p' c c' hc hc').1 fun k => congrFun h k) k
      · intro h
        funext k
        exact (hE p p' c c' hc hc').2 ((hW c c' f f' hf hf').1 fun k => congrFun h k) k)
  exact ⟨t, fun p c hc f hf k => h1 (e p) (hS p) f ⟨p, rfl, c, hc, hf⟩ k, h2⟩

theorem exists_inert_passage_separating : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hO hC hE hS hT hJ hI
  classical
  haveI : Infinite D.what₂.LL := Infinite.of_injective (Nat.cast : ℕ → D.what₂.LL) Nat.cast_injective
  have hr : Function.Injective (fun k : A3.okI A3.A.μ0 × List ℕ => ((k.1.1, k.2) : I0 × List ℕ)) := by
    rintro ⟨⟨a, ha⟩, b⟩ ⟨⟨a', ha'⟩, b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have key : ∀ j : Fin D.R.m, ∃ t : (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL,
      (∀ (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ), R.Carries p c → ∀ f : A3.okI A3.A.μ0 × List ℕ → D.what₂.LL,
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        ∀ k, f k = t p.1.2 (k.1.1, k.2)) ∧
      ∀ a ∈ ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd,
      ∀ b ∈ ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd,
        (∃ k : A3.okI A3.A.μ0 × List ℕ, a (k.1.1, k.2) ≠ b (k.1.1, k.2)) →
        ∃ k : A3.okI A3.A.μ0 × List ℕ, t a (k.1.1, k.2) ≠ t b (k.1.1, k.2) := by
    intro j
    have hE' : ∀ (p p' : A3.fam3.base3.Ix) (c c' : Pl D.host.E → List ℤ → ℂ), R.Carries p c → R.Carries p' c' →
        ((∀ k : A3.okI A3.A.μ0 × List ℕ, p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2)) ↔
          (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) :=
      fun p p' c c' hc hc' => GlobalTheory.T.inertValues_iff_inertLabels_carriedEigensystems R F hL hO hC hE hS hT hJ hI j p p' c c' hc hc'
    have hW' : ∀ (c c' : Pl D.host.E → List ℤ → ℂ) (f f' : A3.okI A3.A.μ0 × List ℕ → D.what₂.LL),
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f' k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c' ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        ((∀ k, f k = f' k) ↔
          (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
      rintro c c' f f' ⟨u, x, hf, a1, a2, a3⟩ ⟨u', x', hf', b1, b2, b3⟩
      have V := GlobalTheory.T.inertEigenvalues_iff_thetaLift_inertLabels R F hL hO hC hE hS hT hJ j c c' u u' x x' a1 b1 a2 b2 a3 b3
      refine Iff.trans ?_ V
      exact forall_congr' fun k => by rw [hf k, hf' k]
    exact exists_passage_of_labels (Ix := A3.fam3.base3.Ix) (C := Pl D.host.E → List ℤ → ℂ) (L := D.what₂.LL)
      (((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd)
      (fun k : A3.okI A3.A.μ0 × List ℕ => ((k.1.1, k.2) : I0 × List ℕ)) hr (fun p => p.1.2)
      (fun p => Finset.mem_image.2 ⟨p.1, p.2, rfl⟩) (fun p c => R.Carries p c)
      (fun c f => ∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0)
      (fun c c' => ∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d) hE' hW'
  choose tr h1 h2 using key
  refine ⟨tr, ?_, ?_⟩
  · rintro j p c hc u ⟨x, -, a1, a2, a3⟩ k
    exact h1 j p c hc (fun k => u (Sum.inr k)) ⟨u, x, fun _ => rfl, a1, a2, a3⟩ k
  · intro j p hp p' hp' h
    exact h2 j p.2 (Finset.mem_image.2 ⟨p, hp, rfl⟩) p'.2 (Finset.mem_image.2 ⟨p', hp', rfl⟩) h

end GlobalTheory
