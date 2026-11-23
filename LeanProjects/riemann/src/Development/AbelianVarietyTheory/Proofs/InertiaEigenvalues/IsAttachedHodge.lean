import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin

noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

structure IsAttachedAway : Prop where
  cont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))
  ss : IsSSRep r
  away : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r = T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))
  temp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.tempered (D.naut.locG π w)

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {w : PlE D.host}
  (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O)

structure IsDeRhamOf : Prop where
  deRham : IsdRAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)
  jumps : ∀ (τ : D.host.E →+* Qbar l) (L : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced Bw τ τ' →
    ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      (D.naut.infG π (ι.toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)) + ((a : ℂ) - 1) / 2) ∧
      IsJumpsAt (D.loc l) Bw (resDec D.nd.plOm.1 r w) τ J

structure IsAttachedAll : Prop extends IsAttachedAway D T ι π s r where
  above : ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O) (hj : Induces Bw),
    IsDeRhamOf D ι π s r Bw ∧ wdAt (D.loc l) ι Bw (D.nd.plOm.2 w) hj (resDec D.nd.plOm.1 r w) =
      T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))

structure IsAttachedHodge : Prop extends IsAttachedAway D T ι π s r where
  above : ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
    IsDeRhamOf D ι π s r Bw ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)) ∧
      (D.naut.mono0 (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w))

def GalAll : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r) (s : ℝ), D.naut.csd π → RegAlgShift D.naut π s →
    ∃ r, IsAttachedAll D T ι π s r

def GalHodge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r) (s : ℝ), D.naut.csd π → RegAlgShift D.naut π s →
    ∃ r, IsAttachedHodge D T ι π s r

def FrobMatch {K : Type} [CommRing K] (φ : K →+* ℂ) (M : G D.host.E D.nd.Om →* GL (Fin a) K) (u : ℝ) : Prop :=
  ∀ᶠ w : PlE D.host in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    (M σ : Matrix (Fin a) (Fin a) K).charpoly.map φ =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) u)).map fun α => X - C α).prod

variable {D T ι π s r}

theorem IsAttachedAll.hodge (hB : GlobalTheory.Published.DeRhamPotSemistable) (h : IsAttachedAll D T ι π s r) :
    IsAttachedHodge D T ι π s r := by
  refine ⟨h.toIsAttachedAway, fun w hw O _ _ _ Bw hj => ?_⟩
  obtain ⟨h1, h2⟩ := h.above w hw O Bw hj
  have hp := hB.isPstAt (D.locT l) Bw (resDec D.nd.plOm.1 r w) (h.cont.comp continuous_subtype_val) h1.deRham
  refine ⟨h1, fun hu => ?_, fun hm => ?_⟩
  · rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw (D.nd.plOm.2 w) hj (D.loc l) ι _ hp, h2, ← T.unr, D.naut.unr_tw]
    exact hu
  · rw [← GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw (D.nd.plOm.2 w) hj (D.loc l) ι _ hp, h2, ← T.mono0, D.naut.monomial_twist_iff]
    exact hm

theorem GalAll.hodge (hB : GlobalTheory.Published.DeRhamPotSemistable) (h : GalAll D T) : GalHodge D T :=
  fun l _ ι π s hc hr => (h l ι π s hc hr).imp fun _ H => H.hodge hB

theorem IsAttachedAway.frob (h : IsAttachedAway D T ι π s r) {w : PlE D.host}
    (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (hu : D.naut.unr (D.naut.locG π w)) :
    (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), r σ = 1) ∧
    ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))).map fun α => X - C α).prod := by
  have h1 := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
  have h2 : (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r).unr := by rw [h.away w hl, ← T.unr]; exact h1
  refine ⟨(GlobalTheory.WeilDeligne.unr_wdOf_iff hl ι h.cont).1 h2, fun B σ hB hσ => ?_⟩
  rw [GlobalTheory.WeilDeligne.frobEig_wdOf hl ι h.cont h2 hB hσ, h.away w hl, T.frobEig w _ h1]

theorem IsAttachedAway.isGaloisRepOf (h : IsAttachedAway D T ι π 0 r) : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.IsGaloisRepOf D π l ι r := by
  refine ⟨h.cont, h.ss, fun w hw => ⟨fun σ hσ => ?_, ?_, fun hu B σ hB hσ => ?_⟩⟩
  · rw [GlobalTheory.WeilDeligne.inePol_wdOf hw ι h.cont hσ, h.away w hw, zero_add, T.inePol w _ σ hσ]
  · rw [← GlobalTheory.WeilDeligne.weilDeligneParam_monodromy_eq_zero_iff hw ι h.cont, h.away w hw, zero_add, T.mono0]
  · simpa only [zero_add, galPol] using (h.frob hw hu).2 B σ hB hσ

end GlobalTheory.TripleLocal

end
