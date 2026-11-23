import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def maxLam (i : X.Tw) (M : ℕ) (ι : Type) : Ideal (abelian₂ X i M ι) :=
  (IsLocalRing.maximalIdeal (X.O0 i)).map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ⊔
    Ideal.span (Set.range fun q : ι => toLam X i M ι (MvPolynomial.X q))

def ResLam (i : X.Tw) (M : ℕ) (ι : Type) : Type := abelian₂ X i M ι ⧸ maxLam X i M ι

instance (i : X.Tw) (M : ℕ) (ι : Type) : AddCommGroup (ResLam X i M ι) :=
  inferInstanceAs (AddCommGroup (abelian₂ X i M ι ⧸ maxLam X i M ι))

instance (i : X.Tw) (M : ℕ) (ι : Type) : Module (abelian₂ X i M ι) (ResLam X i M ι) :=
  inferInstanceAs (Module (abelian₂ X i M ι) (abelian₂ X i M ι ⧸ maxLam X i M ι))

instance (i : X.Tw) (M : ℕ) (ι : Type) : TopologicalSpace (ResLam X i M ι) := ⊥

instance (i : X.Tw) (M : ℕ) (ι : Type) : DiscreteTopology (ResLam X i M ι) := ⟨rfl⟩

theorem maxLam_ne_top (i : X.Tw) (M : ℕ) (ι : Type) : maxLam X i M ι ≠ ⊤ := by
  classical
  let ε : abelian₂ X i M ι →ₐ[X.O0 i] X.O0 i := MonoidAlgebra.lift (X.O0 i) (X.O0 i) (Del X i M ι) 1
  let φ : abelian₂ X i M ι →+* IsLocalRing.ResidueField (X.O0 i) :=
    (IsLocalRing.residue (X.O0 i)).comp ε.toRingHom
  have hle : maxLam X i M ι ≤ RingHom.ker φ := by
    unfold maxLam
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa [φ, ε, IsLocalRing.residue_eq_zero_iff] using hc
    · rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      simp [φ, ε, toLam]
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top φ) hle

def HidaSetting (i : X.Tw) (M : ℕ) {ι : Type} (P : ι → PlE D.host) (Q : Finset (PlE D.host))
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  1 ≤ M ∧ IsQ P Q ∧ (∀ q q', Over (P q) (P q') → q = q') ∧
    (∀ v ∈ Q, v ∉ placesOver D.host.E (X.l i) ∧ v ∉ Spl i) ∧
    ∀ q, IsOpen ((d q).ker : Set (GE N)) ∧ TrivAbove (d q) (X.l i) ∧
      ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q →
        ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, d q σ = 1

variable {X} (bkP : BKPh X)

def TripleHyp (i : X.Tw) (s : X.Sig i) : Prop :=
  IsotypicValuationAtRing bkP i s ∧ ValuationStabilityAtRing X i s ∧ SelfDual i s ∧ NoJump bkP i s ∧ Gen.adm3 D ∧ 3 ≤ D.R.r

def IsSelMatrix (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
    (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) : Prop :=
  Computes bkP i s M d Q Φ ∧
    Module.length (abelian₂ X i M ι) ↥(selOn bkP i (Tgl i s) (delInv i M d) (ResLam X i M ι) Q) = (a : ℕ∞) ∧
    ∀ x y, Φ x y ∈ maxLam X i M ι

def SelMatrixAt (i : X.Tw) (s : X.Sig i) : Prop :=
  TripleHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) (Q : Finset (PlE D.host))
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))), HidaSetting X i M P Q d →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), IsSelMatrix bkP i s M d Q a Φ

def SelMatrix : Prop := ∀ (i : X.Tw) (s : X.Sig i), SelMatrixAt bkP i s

def SelmerMatrixChosenPrimes : Prop :=
  ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ), 1 ≤ M → ∀ (A : Finset (PlE D.host)) (ι : Type) [Fintype ι]
    (P : ι → PlE D.host) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)),
    SlopeTestRemainingChoices X i M A P d → IsQ P Q →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), IsSelMatrix bkP i s M d Q a Φ

variable (X) in

theorem setting_of_auxiliaryPrimes (i : X.Tw) (M : ℕ) (hM : 1 ≤ M) (A : Finset (PlE D.host)) {ι : Type} (P : ι → PlE D.host)
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host))
    (h : SlopeTestRemainingChoices X i M A P d) (hQ : IsQ P Q) : HidaSetting X i M P Q d := by
  obtain ⟨hv, hinj, hgood⟩ := h
  refine ⟨hM, hQ, hinj, ?_, ?_⟩
  · intro v hvQ
    obtain ⟨q, hq⟩ := (hQ v).1 hvQ
    have hS0 : v ∉ X.S0 i := (hv q v hq).2.2.2.1
    refine ⟨fun hl => hS0 (X.twistExcludedPlaces_contains_residueChar i hl), fun hsp => hS0 ?_⟩
    simp only [Spl, Set.mem_sdiff, Set.mem_union, Set.mem_iUnion] at hsp
    rcases hsp.1 with ⟨k, hk⟩ | hp
    · exact X.placesOver_subset_exceptional i k hk
    · exact X.primes_subset_exceptional i hp
  · intro q
    obtain ⟨hopen, -, htriv, hout, -⟩ := hgood q
    refine ⟨hopen, htriv, ?_⟩
    intro v _ _ hvQ B hB σ hσ
    exact hout v (fun ho => hvQ ((hQ v).2 ⟨q, ho⟩)) B hB σ hσ

theorem selmerMatrixAuxiliaryPrimes_of_selMatrix (h : SelMatrix bkP) : SelmerMatrixChosenPrimes bkP := by
  unfold SelmerMatrixChosenPrimes
  intro i s hG M hM A ι _ P d Q haux hQ
  unfold GalHyp at hG
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := hG
  have hT : TripleHyp bkP i s := by
    unfold TripleHyp
    exact ⟨h1, h2, h3, h4, h6, by omega⟩
  exact h i s hT M ι P Q d (setting_of_auxiliaryPrimes X i M hM A P d Q haux hQ)

end GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

end
