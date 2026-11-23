import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPosIffMemExample
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.Top.TwChar
theorem exists_twisted_cohomology_class_lift_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (X : Stages) (f : Fr X.B.toPre) (pl : Finset ℕ) (A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)) (σ : Seed X.toD7 A) (Av : ℕ → Finset ℕ), (∀ v, TwistedAt X.toD7 v → X.B.places.resChar v ∈ pl) → (∀ v v', OverOne X.toD7 v v' → TwistedAt X.toD7 v → TwistedAt X.toD7 v') → (∀ i (p : ℕ), p ∈ offSet X.B.toPre ∨ p ∈ Av (X.toD7.ntw.l i) → p.Prime → placesOver X.toD7.host.E p ⊆ ↑(A i)) → ∀ S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ, (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) → ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B') (h : Enl X.B B'), HEq f' f ∧ T'.pl = pl ∧ T'.Avoids Av ∧ (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ Coh B' T' ∧ TwFrom X σ h T' := by
  intro hP X f pl A σ Av hpl hsat hA S₂ h₂
  obtain ⟨art, ha⟩ := hP.what₂.art X.toD7.host.E X.toD7.nd.Om
  obtain ⟨h1, T₁, e1, hav, hT, hT', hS⟩ := exists_twDat_stagesOn X f pl {v | TwistedAt X.toD7 v} hpl
    (twistedAt_conj X.toD7) σ.s (fun w => let ⟨_, hb⟩ := σ.reads w; hb.l_eq) (fun w _ => σ.conj w) art ha A σ.Q σ.k σ.ψ
    (fun i => rootIsoAt X.toD7 i (σ.k i)) Av hA (fun w hw => σ.psiOk hw)
  obtain ⟨B', h, a, b, e⟩ := hS (S₂ X.B.toPre f (T₁.set f)) (h₂ _ _ _)
  have e2 : ∀ (P : Pre) (_ : P = X.B.toPre) (g : Fr P) (Ξ : Set (HChar P.host.E)), HEq g f → HEq Ξ (T₁.set f) →
      S₂ P g Ξ = S₂ X.B.toPre f (T₁.set f) := by
    intro P eP g Ξ h1 h2
    subst eP
    rw [eq_of_heq h1, eq_of_heq h2]
  refine ⟨B', tr h.1 Fr f, pull h T₁, h, tr_heq _ _ _, e1, avoids_pull h hav, ?_, ⟨fun v v' hv => ?_, fun v => ?_⟩,
    b, fun v => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rw [e2 _ h.1 _ _ (tr_heq _ _ _) e]
    exact a
  · have ho := overOne_plUnder X h v v' hv
    have key : T₁.psi (plUnder h v) = T₁.psi (plUnder h v') ∧ T₁.Q (plUnder h v) = T₁.Q (plUnder h v') ∧
        T₁.k (plUnder h v) = T₁.k (plUnder h v') := by
      by_cases hw : TwistedAt X.toD7 (plUnder h v)
      · have hw' := hsat _ _ ho hw
        obtain ⟨x, y, z⟩ := hT _ hw
        obtain ⟨x', y', z'⟩ := hT _ hw'
        rw [σ.same _ _ hw hw' ho] at x' y' z'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
      · have hw' : ¬ TwistedAt X.toD7 (plUnder h v') := fun h' => hw (hsat _ _ (fun x => (ho x).symm) h')
        obtain ⟨x, y, z⟩ := hT' _ hw
        obtain ⟨x', y', z'⟩ := hT' _ hw'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
    exact ⟨congrArg (tr h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E)))) key.2.1, key.2.2,
      congrArg (tr h.1 (fun P => HChar P.host.E)) key.1⟩
  · have hn : B'.places.resChar v ^ (pull h T₁).k v ≠ 0 := pow_ne_zero _ (B'.places.resChar_prime v).ne_zero
    have hz := Complex.isPrimitiveRoot_exp _ hn
    obtain ⟨x, hx⟩ := b v _ hz.pow_eq_one
    exact ⟨x, IsPrimitiveRoot.of_map_of_injective (hx ▸ hz) B'.embLL.injective⟩
  · obtain ⟨x, y, z⟩ := hT (plUnder h v) hw
    exact ⟨(tr_heq h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) _).trans (heq_of_eq y), z, _, _,
      (h1 _ (σ.psiOk hw)).2.1, (tr_heq h.1 (fun P => HChar P.host.E) _).trans (heq_of_eq x)⟩
  · exact (congrArg (tr h.1 (fun P => HChar P.host.E)) (hT' _ hw).1).trans (tr_one _)
end GlobalTheory.HeightCounting.Up
end
end
end
