import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualBoundAdmissible

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open GlobalTheory.IndefiniteRowSideFullHecke.ResidualBoundAdmissible

namespace GlobalTheory.TwSys.ResidualCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isConjPl_unique {P v v' : PlE D.host} (h : IsConjPl D.host P v) (h' : IsConjPl D.host P v') : v = v' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

theorem exists_isQ {ι : Type} [Finite ι] (P : ι → PlE D.host) : ∃ Q, IsQ P Q := by
  have hf : (⋃ q, {v | Over (P q) v}).Finite := by
    refine Set.finite_iUnion fun q => ?_
    have h2 : {v | IsConjPl D.host (P q) v}.Subsingleton := fun _ h _ h' => isConjPl_unique h h'
    exact ((Set.finite_singleton (P q)).union h2.finite).subset fun v hv => hv
  exact ⟨hf.toFinset, fun v => by simp⟩

theorem isQ_unique {ι : Type} {P : ι → PlE D.host} {Q Q' : Finset (PlE D.host)} (h : IsQ P Q) (h' : IsQ P Q') :
    Q = Q' := Finset.ext fun v => (h v).trans (h' v).symm

theorem not_goodChar_one (i : X.Tw) {M : ℕ} (hM : 1 ≤ M) (P : PlE D.host) : ¬ GoodChar X i M P 1 := by
  intro h
  have : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) (X.lPrime i).out.one_lt⟩
  obtain ⟨σ, -, hσ⟩ := h.2.2.2.2 P (Or.inl rfl) _ (N.plOm.2 P) (Multiplicative.ofAdd 1)
  have h1 : (0 : ZMod (X.l i ^ M)) = 1 := congrArg Multiplicative.toAdd hσ
  exact zero_ne_one h1

theorem addVal_le_zero_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : O) :
    IsDiscreteValuationRing.addVal O x ≤ 0 ↔ IsUnit x := by
  rw [nonpos_iff_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff]

variable (bkP : BKPh X)

def AtLevel₁ (i : X.Tw) (T : Set (X.Sig i)) (R n M : ℕ) : Prop :=
  ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
        Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ n ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤ 0

def AtLevel₂ (i : X.Tw) (T : Set (X.Sig i)) (R n M : ℕ) : Prop :=
  ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host))
    (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))), AdmFam X i M H S d →
    ∀ z : GE N, IsTameInertiaElementAtTwistPrime X i z →
    ∀ H' : Subgroup (GE N), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host),
      ∃ (P : Fin R ⊕ Fin R → PlE D.host) (Q : Finset (PlE D.host)),
        (∀ q, AdmPl H S (P q)) ∧
        SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
        Steps X i M H' z P (fun q => d (P q)) ∧
        IsQ P Q ∧
        ∀ s ∈ T, ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
          Computes bkP i s M (fun q => d (P q)) Q Φ → OrdLE X i M (Fin R ⊕ Fin R) n Φ.det

theorem ordBound_zero_iff (i : X.Tw) : OrdBound bkP i 0 ↔
    ∀ T : Set (X.Sig i), (∀ s ∈ T, GalHyp bkP i s) → ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₁ bkP i T R n M := Iff.rfl

theorem residualBoundOn_iff (i : X.Tw) (T : Set (X.Sig i)) : ResidualBoundOn bkP i T ↔
    (nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R : ℕ, ∀ M : ℕ, 4 * D.R.r * R + 1 < X.l i ^ M → AtLevel₂ bkP i T R (4 * D.R.r * R) M) := Iff.rfl

theorem atLevel₁_of_atLevel₂ {i : X.Tw} {T : Set (X.Sig i)} {R n M : ℕ} (h : AtLevel₂ bkP i T R n M) :
    AtLevel₁ bkP i T R n M := by
  intro H S d hd z hz H' ho hn A
  obtain ⟨P, Q, -, h2, h3, h4, h5⟩ := h H S d hd z hz H' ho hn A
  refine ⟨P, h2, h3, fun s hs Q' hQ' a Φ hΦ F hF => ?_⟩
  obtain rfl := isQ_unique h4 hQ'
  obtain ⟨m, hm, hu⟩ := h5 s hs a Φ hΦ F hF
  exact ⟨m, hm, (addVal_le_zero_iff _).2 hu⟩

theorem atLevel₂_of_atLevel₁ {i : X.Tw} {T : Set (X.Sig i)} {R n M : ℕ} (hM : 1 ≤ M) (h : AtLevel₁ bkP i T R n M) :
    AtLevel₂ bkP i T R n M := by
  classical
  intro H S d hd z hz H' ho hn A
  let d' : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M))) := fun P => if AdmPl H S P then d P else 1
  have hd' : AdmFam X i M H S d' := by
    refine ⟨hd.1, hd.2.1, hd.2.2.1, fun P h1 h2 h3 => ?_⟩
    have : d' P = d P := if_pos ⟨h1, h2, h3⟩
    rw [this]
    exact hd.2.2.2 P h1 h2 h3
  obtain ⟨P, h2, h3, h5⟩ := h H S d' hd' z hz H' ho hn A
  have hadm : ∀ q, AdmPl H S (P q) := by
    intro q
    by_contra hq
    have h6 : GoodChar X i M (P q) (d' (P q)) := h2.2.2 q
    have : d' (P q) = 1 := if_neg hq
    rw [this] at h6
    exact not_goodChar_one i hM _ h6
  have he : (fun q => d' (P q)) = fun q => d (P q) := funext fun q => if_pos (hadm q)
  rw [he] at h2 h3 h5
  obtain ⟨Q, hQ⟩ := exists_isQ P
  refine ⟨P, Q, hadm, h2, h3, hQ, fun s hs a Φ hΦ F hF => ?_⟩
  obtain ⟨m, hm, hu⟩ := h5 s hs Q hQ a Φ hΦ F hF
  exact ⟨m, hm, (addVal_le_zero_iff _).1 hu⟩

theorem atLevel_iff (i : X.Tw) (T : Set (X.Sig i)) (R n : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    AtLevel₁ bkP i T R n M ↔ AtLevel₂ bkP i T R n M :=
  ⟨atLevel₂_of_atLevel₁ bkP hM, atLevel₁_of_atLevel₂ bkP⟩

theorem residual_bound_iff_free_level : ResidualBoundOddPrimes bkP ↔ ∀ (i : X.Tw) (T : Set (X.Sig i)), nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
    ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₂ bkP i T R n M := by
  constructor
  · intro h i T hl hT
    obtain ⟨R, n, M₀, hM⟩ := (ordBound_zero_iff bkP i).1 (h i hl) T hT
    exact ⟨R, n, max M₀ 1, fun M hle =>
      atLevel₂_of_atLevel₁ bkP (le_trans (le_max_right _ _) hle) (hM M (le_trans (le_max_left _ _) hle))⟩
  · intro h i hl
    refine (ordBound_zero_iff bkP i).2 fun T hT => ?_
    obtain ⟨R, n, M₀, hM⟩ := h i T hl hT
    exact ⟨R, n, M₀, fun M hle => atLevel₁_of_atLevel₂ bkP (hM M hle)⟩

theorem residualBoundOn_iff_sharp (i : X.Tw) (T : Set (X.Sig i)) : ResidualBoundOn bkP i T ↔
    (nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R : ℕ, ∀ M : ℕ, 4 * D.R.r * R + 1 < X.l i ^ M → AtLevel₁ bkP i T R (4 * D.R.r * R) M) := by
  rw [residualBoundOn_iff]
  refine forall₂_congr fun _ _ => exists_congr fun R => forall₂_congr fun M hM => (atLevel_iff bkP i T R _ ?_).symm
  rcases Nat.eq_zero_or_pos M with rfl | h
  · simp at hM
  · exact h

theorem loose_of_residualBoundOn {i : X.Tw} {T : Set (X.Sig i)} (h : ResidualBoundOn bkP i T) (hl : nu X i = 0)
    (hT : ∀ s ∈ T, GalHyp bkP i s) : ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₁ bkP i T R n M := by
  obtain ⟨R, hR⟩ := (residualBoundOn_iff_sharp bkP i T).1 h hl hT
  refine ⟨R, 4 * D.R.r * R, 4 * D.R.r * R + 1, fun M hM => hR M ?_⟩
  exact lt_of_le_of_lt hM (Nat.lt_pow_self (X.lPrime i).out.one_lt)

theorem residual_bound_of_bound_on_sets (h : ∀ (i : X.Tw) (T : Set (X.Sig i)), ResidualBoundOn bkP i T) : ResidualBoundOddPrimes bkP :=
  fun i hl => (ordBound_zero_iff bkP i).2 fun T hT => loose_of_residualBoundOn bkP (h i T) hl hT

theorem AtLevel₁.mono {i : X.Tw} {T T' : Set (X.Sig i)} {R n M : ℕ} (hT : T' ⊆ T) (h : AtLevel₁ bkP i T R n M) :
    AtLevel₁ bkP i T' R n M := by
  intro H S d hd z hz H' ho hn A
  obtain ⟨P, h2, h3, h5⟩ := h H S d hd z hz H' ho hn A
  exact ⟨P, h2, h3, fun s hs => h5 s (hT hs)⟩

theorem ordBound_of_residualBound (i : X.Tw) (hl : nu X i = 0) (hg : ∀ s, goodS bkP i s ↔ GalHyp bkP i s)
    (h : ResidualBound bkP i) : OrdBound bkP i 0 := by
  refine (ordBound_zero_iff bkP i).2 fun T hT => ?_
  obtain ⟨R, n, M₀, hM⟩ := loose_of_residualBoundOn bkP h hl fun s hs => (hg s).1 hs
  exact ⟨R, n, M₀, fun M hle => (hM M hle).mono bkP fun s hs => (hg s).2 (hT s hs)⟩

theorem good_rows_at_level_of_residual (h : ResidualBoundOddPrimes bkP) (i : X.Tw) (hl : nu X i = 0)
    (hg : ∀ s, goodS bkP i s → GalHyp bkP i s) :
    ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₂ bkP i {s | goodS bkP i s} R n M :=
  (residual_bound_iff_free_level bkP).1 h i _ hl hg

theorem comparison :
    (∀ (i : X.Tw) (T : Set (X.Sig i)) (R n M : ℕ), 1 ≤ M → (AtLevel₁ bkP i T R n M ↔ AtLevel₂ bkP i T R n M)) ∧
    (ResidualBoundOddPrimes bkP ↔ ∀ (i : X.Tw) (T : Set (X.Sig i)), nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₂ bkP i T R n M) ∧
    (∀ (i : X.Tw) (T : Set (X.Sig i)), ResidualBoundOn bkP i T ↔ (nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R : ℕ, ∀ M : ℕ, 4 * D.R.r * R + 1 < X.l i ^ M → AtLevel₁ bkP i T R (4 * D.R.r * R) M)) ∧
    ((∀ (i : X.Tw) (T : Set (X.Sig i)), ResidualBoundOn bkP i T) → ResidualBoundOddPrimes bkP) :=
  ⟨fun i T R n _ hM => atLevel_iff bkP i T R n hM, residual_bound_iff_free_level bkP, residualBoundOn_iff_sharp bkP,
    residual_bound_of_bound_on_sets bkP⟩

end GlobalTheory.TwSys.ResidualCompare

end
