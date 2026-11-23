import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FlagWD
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published GlobalTheory.Pst UpperTheory.V UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Lev.flagAb (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} {w : HeightOneSpectrum (𝓞 L)}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ)
    (ha : IsLocalArtin h a) (r : Dec (F := L) A →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hh : Fin n → (L →+* Qbar l) → ℤ)
    (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ)
    (hψ : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) (hf : W.HasFlag r ψ) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l L Ω (Dec (F := L) A) O) (hj : GlobalTheory.Pst.Induces Bw) (d : IsdRAt (Loc.PP l) Bw r) :
    Lev.AbW (wdAt (Loc.PP l) ι Bw h hj r) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hc := fun i => (UpperTheory.V.Loc.charDR hN h hw ι a ha (ω i) (hh i) (ψ i) (hψ i)).1 O Bw hj
  obtain ⟨-, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj r (fun i => GlobalTheory.TripleGal.rk1 (ψ i)) M
    (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [GlobalTheory.TripleGal.rk1]))
  refine (Lev.ssCalc L Ω A w h).1 n _ (fun j => (ω j).comp a) fun s => ?_
  rw [(F₂ (hN.aut.berger.isPstAt T Bw r (Units.continuous_val.comp hr) d)).2 s]
  exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
