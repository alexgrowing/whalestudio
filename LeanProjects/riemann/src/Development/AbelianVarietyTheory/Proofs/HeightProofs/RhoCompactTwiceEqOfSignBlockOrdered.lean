import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsGoodFamily
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVectorStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLieStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDimStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelowStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroupStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar

section Par

variable {n : ℕ}

def ratEntry (P : SignedPar n) (a : Fin n) : ℚ := ((n : ℚ) - 1) / 2 + (P.hc.2 a).choose

theorem ratEntry_cast (P : SignedPar n) (a : Fin n) : ((ratEntry P a : ℚ) : ℝ) = P.lam a := by
  have := (P.hc.2 a).choose_spec
  unfold ratEntry
  push_cast
  linarith

def toSPar (P : SignedPar n) : SPar := Finset.univ.image fun a => (ratEntry P a, P.sgn a)

theorem isEnum_iff_eq (S : SPar) (P : SignedPar n) : IsEnum S P.lam P.sgn ↔ S = toSPar P := by
  constructor
  · rintro ⟨-, q, hq, rfl⟩
    have : q = ratEntry P := funext fun a => by
      have := hq a
      rw [← ratEntry_cast] at this
      exact_mod_cast this.symm
    rw [this]; rfl
  · rintro rfl
    exact ⟨P.hc.1, ratEntry P, fun a => (ratEntry_cast P a).symm, rfl⟩

theorem isEnum_toSPar (P : SignedPar n) : IsEnum (toSPar P) P.lam P.sgn := (isEnum_iff_eq _ P).2 rfl

theorem goodPar_iff (p q : ℕ) (S : SPar) :
    GoodPar n p q S ↔ ∃ P : SignedPar n, P.IsOfSig p q ∧ S = toSPar P := by
  constructor
  · rintro ⟨lam, ε, h1, h2, h3, h4⟩
    exact ⟨⟨lam, ε, h2⟩, ⟨h3, h4⟩, (isEnum_iff_eq S ⟨lam, ε, h2⟩).1 h1⟩
  · rintro ⟨P, h, rfl⟩
    exact ⟨P.lam, P.sgn, isEnum_toSPar P, P.hc, h.1, h.2⟩

theorem toSPar_injective : Function.Injective (toSPar (n := n)) := by
  intro P P' h
  have h1 := isEnum_toSPar P
  rw [h] at h1
  obtain ⟨a, b⟩ := GlobalTheory.SignedParTest.isEnum_unique h1 (isEnum_toSPar P')
  cases P; cases P'
  simp only at a b
  subst a b
  rfl

def parEquiv (n p q : ℕ) : {P : SignedPar n // P.IsOfSig p q} ≃ {S : SPar // GoodPar n p q S} :=
  Equiv.ofBijective (fun P => ⟨toSPar P.1, (goodPar_iff p q _).2 ⟨P.1, P.2, rfl⟩⟩)
    ⟨fun P P' h => Subtype.ext (toSPar_injective (congrArg Subtype.val h)), fun S => by
      obtain ⟨P, h, e⟩ := (goodPar_iff p q _).1 S.2
      exact ⟨⟨P, h⟩, Subtype.ext e.symm⟩⟩

end Par

section Iso

variable {n : ℕ}

theorem cdom_le {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : CDom ε μ Λ) :
    ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x ≤ ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x ∧
      (∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x = ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x → Λ = μ) := by
  obtain ⟨c, hc, e⟩ := h
  have r : ∀ a b : Fin n, ∑ x : Fin n, ((x : ℕ) : ℝ) * Formalism.REAL.root a b x = (a : ℕ) - (b : ℕ) := by
    intro a b
    simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have key : ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x - ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x =
      ∑ a, ∑ b, (c a b : ℝ) * (((b : ℕ) : ℝ) - (a : ℕ)) := by
    have : ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x - ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x = -∑ x : Fin n, ((x : ℕ) : ℝ) * (Λ - μ) x := by
      simp [mul_sub, Finset.sum_sub_distrib]
    rw [this, e]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have := r a b
    simp only [mul_left_comm _ (c a b : ℝ), ← Finset.mul_sum, this]
    ring
  have nn : ∀ a b, 0 ≤ (c a b : ℝ) * (((b : ℕ) : ℝ) - (a : ℕ)) ∧
      ((c a b : ℝ) * (((b : ℕ) : ℝ) - (a : ℕ)) = 0 → c a b = 0) := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have h1 : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast (hc a b h0).1
      have h2 : (0 : ℝ) < c a b := by exact_mod_cast Nat.pos_of_ne_zero h0
      have := mul_pos h2 (sub_pos.2 h1)
      exact ⟨this.le, fun h => absurd h this.ne'⟩
  have n2 : ∀ a, 0 ≤ ∑ b, (c a b : ℝ) * (((b : ℕ) : ℝ) - (a : ℕ)) := fun a => Finset.sum_nonneg fun b _ => (nn a b).1
  refine ⟨by have := Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => n2 a; linarith, fun h => ?_⟩
  rw [h, sub_self, eq_comm, Finset.sum_eq_zero_iff_of_nonneg fun a _ => n2 a] at key
  have : ∀ a b, c a b = 0 := fun a b => (nn a b).2
    ((Finset.sum_eq_zero_iff_of_nonneg fun b _ => (nn a b).1).1 (key a (Finset.mem_univ _)) b (Finset.mem_univ _))
  simpa [this, sub_eq_zero] using e

theorem cdom_antisymm {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : CDom ε μ Λ) (h' : CDom ε Λ μ) : Λ = μ :=
  (cdom_le h).2 (le_antisymm (cdom_le h).1 (cdom_le h').1)

theorem ujset_const (s : Bool) : UJset (fun _ : Fin n => s) = (Matrix.unitaryGroup (Fin n) ℂ : Set _) := by
  rw [← GlobalTheory.DefiniteCheck.kset_const]
  ext g
  simp [Formalism.REAL.Kset, GlobalTheory.DefiniteCheck.jm_const]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isKTypeOf_const (s : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    IsKTypeOf (fun _ => s) σ Λ S ↔ IsKTypeOf (allPos n) σ Λ S := by
  have : Formalism.REAL.Kset (fun _ : Fin n => s) = Formalism.REAL.Kset (allPos n) := by
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.kset_const, GlobalTheory.DefiniteCheck.kset_const, ujset_const, ujset_const]
  simp only [IsKTypeOf, IsKStableOn, this, CDom, allPos]

theorem isDS_const_iff (s : Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsDS (fun _ => s) lam σ ↔ IsHCTypeU n lam σ := by
  have hl : Formalism.QuantumDeterminants.lowK (fun _ : Fin n => s) lam = Formalism.QuantumDeterminants.lowK (allPos n) lam := by
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const, GlobalTheory.DefiniteCheck.lowK_const]
  have hu : UJset (fun _ : Fin n => s) = UJset (allPos n) := by
    unfold allPos
    rw [ujset_const, ujset_const]
  constructor
  · intro h
    have ht := GlobalTheory.DefiniteCheck.isDS_const_top h
    have := ht.1
    refine ⟨h.2.1, Module.Finite.equiv Submodule.topEquiv (M := (⊤ : Submodule ℂ H)), hu ▸ h.2.2.1, ?_⟩
    rwa [← isKTypeOf_const s, ← hl]
  · rintro ⟨h1, h2, h3, h4⟩
    rw [← isKTypeOf_const s, ← hl] at h4
    rw [← hu] at h3
    refine ⟨FiniteDimensional.complete ℂ H, h1, h3, fun S _ hS => ?_, fun v w => ?_, ⟨⊤, h4⟩, fun μ S hS => ?_⟩
    · exact h4.2.2.1 S le_top fun g hg => hS g (by rwa [← GlobalTheory.DefiniteCheck.kset_const])
    · have hemb := Formalism.REAL.isClosedEmbeddingMatrix n (fun _ => s)
      have : CompactSpace (Formalism.REAL.UJ (fun _ : Fin n => s)) := by
        rw [← isCompact_univ_iff, hemb.1.isEmbedding.isCompact_iff, Set.image_univ, hemb.2]
        have := (Formalism.REAL.maximal_compact_facts n (fun _ => s)).2.1
        rwa [GlobalTheory.DefiniteCheck.kset_const] at this
      have hc : Continuous (coefOn (ε := fun _ : Fin n => s) σ v w) :=
        continuous_const.inner ((h3.2.2 v).comp_continuous hemb.1.continuous fun g => g.2)
      exact hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · obtain ⟨v, hv, hv0, hw⟩ := hS.2.2.2.1
      have hT : S = ⊤ := (h4.2.2.1 S le_top hS.2.1).resolve_left fun h0 => hv0 (by simpa [h0] using hv)
      subst hT
      obtain ⟨v', hv', hv0', hw'⟩ := h4.2.2.2.1
      rw [cdom_antisymm (h4.2.2.2.2 μ v hv hv0 hw) (hS.2.2.2.2 _ v' hv' hv0' hw')]

theorem IsFrame.conj_mem {ε ε' : Fin n → Bool} {J A B A' : Matrix (Fin n) (Fin n) ℂ} (h : IsFrame ε J A B)
    (h' : A'ᴴ * Formalism.REAL.Jm ε' * A' = J) : (A' * B)ᴴ * Formalism.REAL.Jm ε' * (A' * B) = Formalism.REAL.Jm ε := by
  calc (A' * B)ᴴ * Formalism.REAL.Jm ε' * (A' * B) = Bᴴ * (A'ᴴ * Formalism.REAL.Jm ε' * A') * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (A * B)ᴴ * Formalism.REAL.Jm ε * (A * B) := by
        rw [h', ← h.1]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h.2.1]; simp

theorem exists_frame {p q : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Formalism.UG.HasSignature J p q) (P : SignedPar n)
    (hP : P.IsOfSig p q) : ∃ A B, IsFrame P.sgn J A B := by
  obtain ⟨e', he'⟩ := exists_blockOrd P.sgn hP.1 hP.2
  obtain ⟨e, Q, hQ⟩ := hJ
  have hQ' : (Q : Mat p q)ᴴ * J.reindex e e * (Q : Mat p q) = Formalism.BasicNotions.TH.Jm p q := hQ
  have h1 : ((Q⁻¹ : GL _ ℂ) : Mat p q)ᴴ * Formalism.BasicNotions.TH.Jm p q * ((Q⁻¹ : GL _ ℂ) : Mat p q) = J.reindex e e := by
    rw [← hQ']
    calc _ = ((Q : Mat p q) * ((Q⁻¹ : GL _ ℂ) : Mat p q))ᴴ * J.reindex e e * ((Q : Mat p q) * ((Q⁻¹ : GL _ ℂ) : Mat p q)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv]; simp
  refine ⟨((Q⁻¹ : GL _ ℂ) : Mat p q).submatrix e'.symm e, (Q : Mat p q).submatrix e e'.symm, ?_, ?_, ?_⟩
  · rw [← he'.reindex_Jm, Matrix.conjTranspose_submatrix, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, h1]
    simp
  · rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]
  · rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]

end Iso

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def transAt (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (GA D V → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun x : GA D V => x * atTau θ V τ g

end Adelic

section Degree

variable {D : D7}

abbrev recMeasure (D : D7) {n : ℕ} (ε : Fin n → Bool) : Measure (Formalism.REAL.UJ ε) :=
  (D.s.cdScale n ε : ENNReal) • Formalism.REAL.muG ε

def rowPar (D : D7) (τ : D.what₂.Tau) : SignedPar (2 * D.R.rS + D.R.k + 1) :=
  ⟨lamSH D.R (D.hc τ), epsSH D.R, Formalism.MainNotions.StandardLattice.line_param_harish_chandra D τ⟩

theorem isFdeg_unique {n : ℕ} {ε : Fin n → Bool} {μ : Measure (Formalism.REAL.UJ ε)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d d' : ℝ}
    (h : IsFdeg μ σ d) (h' : IsFdeg μ σ d') : d = d' := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have e := (h.2 v v v v).2.symm.trans (h'.2 v v v v).2
  have h0 : inner ℂ v v * inner ℂ v v ≠ 0 := mul_ne_zero (inner_self_ne_zero.2 hv) (inner_self_ne_zero.2 hv)
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_inj' h0, _root_.inv_inj] at e
  exact_mod_cast e

end Degree

section Low

variable {p q n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool}

theorem card_filter_equiv (e : Ix p q ≃ Fin n) (P : Ix p q → Prop) (Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ b, P b ↔ Q (e b)) : (Finset.univ.filter P).card = (Finset.univ.filter Q).card :=
  Finset.card_equiv e (by simp [h])

theorem rhoCompact_twice_eq_of_signBlockOrdered (h : BlockOrd e ε) (a : Ix p q) : ((rhoOfIndex a : ℚ) : ℝ) = 2 * Formalism.REAL.rhoC ε (e a) := by
  classical
  unfold rhoOfIndex Formalism.REAL.rhoC
  rw [card_filter_equiv e _ (fun b => e a < b ∧ ε b = ε (e a)) fun b => by rw [h.posC_iff, eq_comm],
    card_filter_equiv e _ (fun b => b < e a ∧ ε b = ε (e a)) fun b => by rw [h.posC_iff]]
  push_cast
  ring

theorem vogan_eq (h : BlockOrd e ε) (μ : Ix p q → ℚ) :
    ((vogan μ : ℚ) : ℝ) = vNormSq ε fun i => (μ (e.symm i) : ℝ) := by
  unfold vogan vNormSq Formalism.REAL.nsq Formalism.REAL.dot
  rw [← e.sum_comp]
  push_cast
  simp [rhoCompact_twice_eq_of_signBlockOrdered h, sq]

theorem blattner_eq (P : SignedPar n) (h : BlockOrd e P.sgn) {lam : Ix p q → ℚ} (hl : ∀ a, (lam a : ℝ) = P.lam (e a))
    (a : Ix p q) : ((blattner lam a : ℚ) : ℝ) = P.low (e a) := by
  have lt : ∀ a b, lam b < lam a ↔ e a < e b := fun a b => by
    rw [← P.hc.1.lt_iff_gt, ← hl, ← hl, Rat.cast_lt]
  unfold blattner rhoNC SignedPar.low Formalism.QuantumDeterminants.lowK
  simp only [Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  rw [card_filter_equiv e _ (fun b => e a < b ∧ P.sgn b ≠ P.sgn (e a)) fun b => by
      rw [h.sameBlock_iff, lt, and_comm, eq_comm],
    card_filter_equiv e _ (fun b => b < e a ∧ P.sgn b ≠ P.sgn (e a)) fun b => by
      rw [h.sameBlock_iff, lt, and_comm, eq_comm],
    card_filter_equiv e _ (fun b => e a < b ∧ P.sgn b = P.sgn (e a)) fun b => by
      rw [h.sameBlock_iff, lt, and_comm, eq_comm],
    card_filter_equiv e _ (fun b => b < e a ∧ P.sgn b = P.sgn (e a)) fun b => by
      rw [h.sameBlock_iff, lt, and_comm, eq_comm]]
  push_cast
  rw [hl]
  ring

def blockPar (P : SignedPar n) (e : Ix p q ≃ Fin n) : Ix p q → ℚ := fun a => ratEntry P (e a)

theorem isParam_blockPar (P : SignedPar n) (h : BlockOrd e P.sgn) : IsParam (blockPar P e) := by
  refine ⟨fun a b hab => e.injective (P.hc.1.injective ?_), fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [← ratEntry_cast, ← ratEntry_cast]; exact congrArg _ hab
  · have := P.hc.1 (h.2.2 a b hab)
    rw [← ratEntry_cast, ← ratEntry_cast] at this
    exact_mod_cast this
  · exact ⟨n - 1 + 2 * (P.hc.2 (e a)).choose, by unfold blockPar ratEntry; push_cast; ring⟩
  · exact ⟨(P.hc.2 (e a)).choose - (P.hc.2 (e b)).choose, by unfold blockPar ratEntry; push_cast; ring⟩

theorem exists_blockPar {lam : Ix p q → ℚ} (h : IsParam lam) (hi : ∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m) :
    ∃ (P : SignedPar (p + q)) (e : Ix p q ≃ Fin (p + q)), P.IsOfSig p q ∧ BlockOrd e P.sgn ∧ lam = blockPar P e := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : Fin (p + q) ≃ Ix p q, ∀ i j, i < j → lam (f j) < lam (f i) := by
    refine ⟨(Tuple.sort fun i => -lam (finSumFinEquiv.symm i)).trans finSumFinEquiv.symm, fun i j hij => ?_⟩
    have := (Tuple.monotone_sort fun i => -lam (finSumFinEquiv.symm i)).strictMono_of_injective
      ((neg_injective.comp (h.1.comp finSumFinEquiv.symm.injective)).comp (Equiv.injective _)) hij
    exact neg_lt_neg_iff.1 this
  let P : SignedPar (p + q) := ⟨fun i => lam (f i), fun i => (f i).isLeft,
    fun i j hij => Rat.cast_lt.2 (hf i j hij), fun i => by
      obtain ⟨m, hm⟩ := hi (f i)
      refine ⟨m, ?_⟩
      have := congrArg (fun x : ℚ => (x : ℝ)) hm
      simpa using this⟩
  have hb : BlockOrd f.symm P.sgn := by
    refine ⟨fun i => by simp [P], fun i => by simp [P], fun a b hab => ?_⟩
    have h1 := h.2.1 a b hab
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with x | x
    · have := hf _ _ x
      simp only [Equiv.apply_symm_apply] at this
      exact lt_asymm h1 this
    · rw [f.symm.injective x] at h1
      exact lt_irrefl _ h1
  refine ⟨P, f.symm, ⟨?_, ?_⟩, hb, funext fun a => Rat.cast_injective (α := ℝ) ?_⟩
  · unfold SignedPar.p
    rw [← card_filter_equiv f.symm (fun a => a.isLeft = true) _ fun b => by simp [P], Finset.card_filter,
      Fintype.sum_sum_type]
    simp
  · unfold SignedPar.q
    rw [← card_filter_equiv f.symm (fun a => a.isLeft = false) _ fun b => by simp [P], Finset.card_filter,
      Fintype.sum_sum_type]
    simp
  · unfold blockPar
    rw [ratEntry_cast]
    simp [P]

theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, wtSub, sub_eq_zero]

theorem isKC_Eab {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro x y hxy
  refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
  rintro ⟨rfl, rfl⟩
  exact hxy h

theorem Eab_bracket (x a b : Ix p q) : Eab x x * Eab a b - Eab a b * Eab x x =
    (((if x = a then 1 else 0) - (if x = b then 1 else 0) : ℝ) : ℂ) • Eab a b := by
  unfold Eab
  rw [Complex.ofReal_sub, sub_smul]
  congr 1
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h)]

theorem root_apply (e : Ix p q ≃ Fin n) (x a b : Ix p q) :
    Formalism.REAL.root (e a) (e b) (e x) = (if x = a then 1 else 0) - (if x = b then 1 else 0) := by
  simp [Formalism.REAL.root, Pi.single_apply]

variable {T : GrpData p q} (R : DSRep T) {σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)}

theorem comap_kstable (h : BlockOrd e ε) (hσ : Factors R.U e σ) {S : Submodule ℂ R.U.H} (hf : FiniteDimensional ℂ S)
    (hS : IsKStableOn ε σ S) : FiniteDimensional ℂ (S.comap R.ι) ∧ (S.comap R.ι).map R.ι = S ∧
      KStable R.HK.act (S.comap R.ι) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finiteDim_kStable_subspace_kFinite_lie p q n e ε T R σ h hσ
  have e1 : (S.comap R.ι).map R.ι = S := Submodule.map_comap_eq_of_le (h1 S hf hS)
  have e2 : FiniteDimensional ℂ (S.comap R.ι) := by
    have : FiniteDimensional ℂ ((S.comap R.ι).map R.ι) := by rwa [e1]
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ R.ι_inj _).symm
  exact ⟨e2, e1, h2 _ e2 (by rwa [e1])⟩

theorem isHW_of_isKTypeOf (h : BlockOrd e ε) (hσ : Factors R.U e σ) (μ : Ix p q → ℚ) {S : Submodule ℂ R.U.H}
    (hS : IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S) : ∃ v, Formalism.BasicNotions.TH.IsHW R.HK.act μ v := by
  obtain ⟨-, e1, hK⟩ := comap_kstable R h hσ hS.1 hS.2.1
  obtain ⟨v, hv, hv0, hw⟩ := hS.2.2.2.1
  rw [← e1] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  have hw' := (GlobalTheory.T.torusWeightVector_iff_cartanWeightVector p q n e ε T R σ h hσ _ v).1 hw
  simp only [Equiv.symm_apply_apply] at hw'
  refine ⟨v, fun h0 => hv0 (by rw [h0, map_zero]), (mem_hwSub _ _ _).2 ⟨fun a => by simpa using hw' a, fun a b hab => ?_⟩⟩
  by_contra hu
  have hab' := (h.posC_iff a b).1 hab
  have hm := hK _ (isKC_Eab ((h.sameBlock_iff a b).2 hab'.2)) v hv
  have h1 : IsWtOn (Formalism.REAL.Kset ε) σ ((fun i => (μ (e.symm i) : ℝ)) + Formalism.REAL.root (e a) (e b))
      (R.ι (R.HK.act (Eab a b) v)) := by
    refine (GlobalTheory.T.torusWeightVector_iff_cartanWeightVector p q n e ε T R σ h hσ _ _).2 fun x => ?_
    have := congrArg (fun f : Module.End ℂ R.HK.V => f v) (R.HK.lie (Eab x x) (Eab a b))
    simp only [Eab_bracket, map_smul, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, hw'] at this
    rw [Pi.add_apply, root_apply, Equiv.symm_apply_apply, Complex.ofReal_add, add_smul, this]
    abel
  have h2 := hS.2.2.2.2 _ _ hm (fun h0 => hu (R.ι_inj (by rw [h0, map_zero]))) h1
  have h3 : CDom ε (fun i => (μ (e.symm i) : ℝ)) ((fun i => (μ (e.symm i) : ℝ)) + Formalism.REAL.root (e a) (e b)) := by
    refine ⟨fun i j => if i = e a ∧ j = e b then 1 else 0, fun i j hij => ?_, ?_⟩
    · have : i = e a ∧ j = e b := by by_contra hn; exact hij (if_neg hn)
      rw [this.1, this.2]; exact hab'
    · simp [ite_and]
  have h4 := congrFun (cdom_antisymm h2 h3) (e a)
  have hne : a ≠ b := fun x => hab'.1.ne (congrArg e x)
  simp [root_apply, hne] at h4

theorem kstable_orthogonal (h : BlockOrd e ε) (hσ : Factors R.U e σ) {S : Submodule ℂ R.U.H} (hS : IsKStableOn ε σ S) :
    IsKStableOn ε σ Sᗮ := by
  obtain ⟨⟨hm, hi, -⟩, -⟩ := GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q n e ε T R σ h hσ
  intro k hk x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hk' := Formalism.REAL.Kset_star ε hk
  have u1 : k ∈ UJset ε := (Formalism.REAL.maximal_compact_facts n ε).1 _ hk
  have u2 : star k ∈ UJset ε := (Formalism.REAL.maximal_compact_facts n ε).1 _ hk'
  have e1 := hm.2 _ u1 _ u2
  rw [Unitary.mul_star_self_of_mem hk.1, hm.1] at e1
  have e2 : y = σ k (σ (star k) y) := congrArg (fun f : R.U.H →L[ℂ] R.U.H => f y) e1
  rw [e2]
  exact ((⟨(σ k : R.U.H →ₗ[ℂ] R.U.H), hi k u1⟩ : R.U.H →ₗᵢ[ℂ] R.U.H).inner_map_map _ _).trans (hx _ (hS _ hk' y hy))

theorem isKTypeOf_of_isHW (h : BlockOrd e ε) (hσ : Factors R.U e σ) (μ : Ix p q → ℚ)
    (hv : ∃ v, Formalism.BasicNotions.TH.IsHW R.HK.act μ v) : ∃ S, IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S := by
  classical
  let G : Submodule ℂ R.HK.V → Prop := fun W =>
    FiniteDimensional ℂ W ∧ KStable R.HK.act W ∧ ∃ v ∈ W, Formalism.BasicNotions.TH.IsHW R.HK.act μ v
  have hex : ∃ m, ∃ W, G W ∧ Module.finrank ℂ W = m := by
    obtain ⟨v, hv⟩ := hv
    obtain ⟨W, a, b, c⟩ := R.HK.kfin v
    exact ⟨_, W, ⟨a, c, v, b, hv⟩, rfl⟩
  obtain ⟨W, ⟨hf, hK, v, hvW, hv⟩, hW⟩ := Nat.find_spec hex
  have hmin : ∀ W', W' ≤ W → KStable R.HK.act W' → ∀ v' ∈ W', Formalism.BasicNotions.TH.IsHW R.HK.act μ v' → W' = W := by
    intro W' h1 h2 v' h3 h4
    refine Submodule.eq_of_le_of_finrank_le h1 ?_
    rw [hW]
    exact Nat.find_min' hex ⟨W', ⟨Submodule.finiteDimensional_of_le h1, h2, v', h3, h4⟩, rfl⟩
  have hSK := GlobalTheory.T.isKStableOn_of_lieStable_finiteDim p q n e ε T R σ h hσ W hf hK
  obtain ⟨hw1, hw2⟩ := (mem_hwSub _ _ _).1 hv.2
  have hle : ∀ S' : Submodule ℂ R.U.H, S' ≤ W.map R.ι → S'.comap R.ι ≤ W := fun S' h' =>
    (Submodule.comap_mono h').trans (Submodule.comap_map_eq_of_injective R.ι_inj W).le
  refine ⟨W.map R.ι, inferInstance, hSK, fun S' h1 h2 => ?_, ⟨R.ι v, ⟨v, hvW, rfl⟩,
    fun h0 => hv.1 (R.ι_inj (by rw [h0, map_zero])), ?_⟩, ?_⟩
  · have f1 : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le h1
    have f2 : FiniteDimensional ℂ (S'ᗮ ⊓ W.map R.ι : Submodule ℂ R.U.H) := Submodule.finiteDimensional_of_le inf_le_right
    have k2 : IsKStableOn ε σ (S'ᗮ ⊓ W.map R.ι) := fun k hk x hx =>
      ⟨kstable_orthogonal R h hσ h2 k hk x hx.1, hSK k hk x hx.2⟩
    obtain ⟨-, a1, a2⟩ := comap_kstable R h hσ f1 h2
    obtain ⟨-, b1, b2⟩ := comap_kstable R h hσ f2 k2
    obtain ⟨y, hy, z, hz, hyz⟩ := S'.exists_add_mem_mem_orthogonal (R.ι v)
    have hz' : z ∈ W.map R.ι := by
      rw [← sub_eq_iff_eq_add'.2 hyz]
      exact Submodule.sub_mem _ ⟨v, hvW, rfl⟩ (h1 hy)
    obtain ⟨y, -, rfl⟩ := h1 hy
    obtain ⟨z, hzW, rfl⟩ := id hz'
    have hv' : v = y + z := R.ι_inj (by rw [hyz, map_add])
    have split : ∀ X, IsKC X → ∀ c : ℂ, R.HK.act X v = c • v → R.HK.act X y = c • y ∧ R.HK.act X z = c • z := by
      intro X hX c hc
      have m1 : R.HK.act X y - c • y ∈ S'.comap R.ι := Submodule.sub_mem _ (a2 X hX y hy) (Submodule.smul_mem _ _ hy)
      have m2 : R.HK.act X z - c • z ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι :=
        Submodule.sub_mem _ (b2 X hX z ⟨hz, hz'⟩) (Submodule.smul_mem _ _ ⟨hz, hz'⟩)
      have e0 : R.HK.act X y - c • y = -(R.HK.act X z - c • z) := by
        rw [hv', map_add, smul_add] at hc
        rw [eq_neg_iff_add_eq_zero, sub_add_sub_comm, hc, sub_self]
      have m3 : R.ι (R.HK.act X y - c • y) ∈ S' ⊓ S'ᗮ := ⟨m1, by rw [e0, map_neg]; exact Submodule.neg_mem _ m2.1⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at m3
      have m4 : R.HK.act X y - c • y = 0 := R.ι_inj (by rw [m3, map_zero])
      exact ⟨sub_eq_zero.1 m4, sub_eq_zero.1 (neg_eq_zero.1 (e0.symm.trans m4))⟩
    have s1 := fun a => split _ (isKC_Eab ((h.sameBlock_iff a a).2 rfl)) _ (hw1 a)
    have s2 := fun a b hab => split _ (isKC_Eab ((h.sameBlock_iff a b).2 ((h.posC_iff a b).1 hab).2)) 0
      (by rw [zero_smul]; exact hw2 a b hab)
    by_cases hy0 : y = 0
    · left
      have hz0 : z ≠ 0 := fun h0 => hv.1 (by rw [hv', hy0, h0, add_zero])
      have := hmin _ (hle _ inf_le_right) b2 z ⟨hz, hz'⟩
        ⟨hz0, (mem_hwSub _ _ _).2 ⟨fun a => (s1 a).2, fun a b hab => by simpa using (s2 a b hab).2⟩⟩
      rw [this] at b1
      rw [← S'.inf_orthogonal_eq_bot]
      exact le_antisymm (le_inf le_rfl (h1.trans (b1.le.trans inf_le_left))) inf_le_left
    · right
      have := hmin _ (hle _ h1) a2 y hy
        ⟨hy0, (mem_hwSub _ _ _).2 ⟨fun a => (s1 a).1, fun a b hab => by simpa using (s2 a b hab).1⟩⟩
      rw [← this, a1]
  · exact (GlobalTheory.T.torusWeightVector_iff_cartanWeightVector p q n e ε T R σ h hσ _ v).2 fun a => by simpa using hw1 a
  · obtain ⟨W0, c1, c2, c3, c4⟩ := GlobalTheory.T.highestWeight_generated_weights_below p q R.HK.V R.HK.act R.HK.lie μ v hv
    have := hmin W0 (c3 W hvW hK) c2 v c1 hv
    subst this
    rintro ν _ ⟨w, hw, rfl⟩ hw0 hwt
    obtain ⟨c, d1, d2⟩ := c4 (fun a => ν (e a)) w hw (fun h0 => hw0 (by rw [h0, map_zero]))
      ((GlobalTheory.T.torusWeightVector_iff_cartanWeightVector p q n e ε T R σ h hσ _ w).1 hwt)
    refine ⟨fun i j => c (e.symm i) (e.symm j), fun i j hij => by simpa using (h.posC_iff _ _).1 (d1 _ _ hij), ?_⟩
    funext i
    obtain ⟨x, rfl⟩ := e.surjective i
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply, d2]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, root_apply]

theorem isHW_iff_isKTypeOf (h : BlockOrd e ε) (hσ : Factors R.U e σ) (μ : Ix p q → ℚ) :
    (∃ v, Formalism.BasicNotions.TH.IsHW R.HK.act μ v) ↔ ∃ S, IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S :=
  ⟨isKTypeOf_of_isHW R h hσ μ, fun ⟨_, hS⟩ => isHW_of_isKTypeOf R h hσ μ hS⟩

theorem weight_int {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h1 : σ 1 = 1) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ μ S) (i : Fin n) : ∃ m : ℤ, μ i = m := by
  obtain ⟨v, -, hv0, hw⟩ := hS.2.2.2.1
  have e1 : Matrix.diagonal (fun a => Complex.exp (((Pi.single i (2 * Real.pi) : Fin n → ℝ) a : ℂ) * Complex.I)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases ha : a = i
    · subst ha; simp
    · simp [ha]
  have := hw (Pi.single i (2 * Real.pi)) (by rw [e1]; exact ⟨one_mem _, by simp⟩)
  rw [e1, h1] at this
  have e2 : Complex.exp (((∑ a, μ a * (Pi.single i (2 * Real.pi) : Fin n → ℝ) a : ℝ) : ℂ) * Complex.I) = 1 := by
    refine smul_left_injective ℂ hv0 ?_
    simpa using this.symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 e2
  refine ⟨m, ?_⟩
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hm
  have h3 : ((μ i : ℝ) : ℂ) = m := by
    refine mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [← hm]; push_cast; ring
  exact_mod_cast h3

theorem hasParam_iff_isDSPar (P : SignedPar n) (h : BlockOrd e P.sgn) (hσ : Factors R.U e σ) :
    HasParam R (blockPar P e) ↔ IsDSPar P σ := by
  obtain ⟨u1, u2⟩ := GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q n e _ T R σ h hσ
  have u3 := GlobalTheory.T.block_ordered_square_integrable p q n e _ T R σ h hσ
  have hb : (fun i => ((blattner (blockPar P e) (e.symm i) : ℚ) : ℝ)) = Formalism.QuantumDeterminants.lowK P.sgn P.lam := funext fun i => by
    rw [blattner_eq P h (lam := blockPar P e) fun a => ratEntry_cast P (e a), Equiv.apply_symm_apply]; rfl
  unfold HasParam IsDSPar IsDS
  rw [isHW_iff_isKTypeOf R h hσ, hb]
  constructor
  · rintro ⟨a, b⟩
    refine ⟨inferInstance, R.nontriv, u1, u2, u3, a, fun μ S hS => ?_⟩
    choose m hm using weight_int u1.1.1 hS
    have hμ : (fun i => (((fun a => (m (e a) : ℚ)) (e.symm i) : ℚ) : ℝ)) = μ := funext fun i => by simp [hm]
    obtain ⟨v, hv⟩ := isHW_of_isKTypeOf R h hσ (fun a => (m (e a) : ℚ)) (S := S) (by rwa [hμ])
    rw [← hb, ← hμ, ← vogan_eq h, ← vogan_eq h fun a => (m (e a) : ℚ)]
    exact_mod_cast b _ v hv
  · rintro ⟨-, -, -, -, -, a, b⟩
    refine ⟨a, fun μ v hv => ?_⟩
    obtain ⟨S, hS⟩ := isKTypeOf_of_isHW R h hσ μ ⟨v, hv⟩
    have := b _ S hS
    rw [← hb, ← vogan_eq h, ← vogan_eq h] at this
    exact_mod_cast this

theorem blattner_int (P : SignedPar n) (h : BlockOrd e P.sgn) (a : Ix p q) :
    ∃ m : ℤ, blattner (blockPar P e) a = m := by
  classical
  have hp := isParam_blockPar P h
  have h1 := GlobalTheory.SignedParTest.blattner_add_rho2C hp a
  have h2 : ((Finset.univ.filter fun b => blockPar P e b < blockPar P e a).card : ℚ) +
      (Finset.univ.filter fun b => blockPar P e a < blockPar P e b).card + 1 = n := by
    have h3 : (n : ℚ) = ∑ _b : Ix p q, 1 := by simp [← Fintype.card_sum, Fintype.card_congr e]
    have h4 : (1 : ℚ) = ∑ b : Ix p q, if b = a then 1 else 0 := by simp
    rw [h3, Finset.card_filter, Finset.card_filter]
    nth_rw 1 [h4]
    push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy (blockPar P e b) (blockPar P e a) with x | x | x
    · have : b ≠ a := by rintro rfl; exact lt_irrefl _ x
      simp [x, x.not_gt, this]
    · simp [hp.1 x]
    · have : b ≠ a := by rintro rfl; exact lt_irrefl _ x
      simp [x, x.not_gt, this]
  refine ⟨(P.hc.2 (e a)).choose + (Finset.univ.filter fun b => blockPar P e b < blockPar P e a).card -
    (Finset.univ.filter fun b => posC a b).card + (Finset.univ.filter fun b => posC b a).card, ?_⟩
  have h5 : blockPar P e a = ((n : ℚ) - 1) / 2 + (P.hc.2 (e a)).choose := rfl
  unfold rhoOfIndex at h1
  push_cast
  linarith

theorem isHW_int (h : BlockOrd e ε) (hσ : Factors R.U e σ) {μ : Ix p q → ℚ} {v : R.HK.V}
    (hv : Formalism.BasicNotions.TH.IsHW R.HK.act μ v) (a : Ix p q) : ∃ m : ℤ, μ a = m := by
  obtain ⟨S, hS⟩ := isKTypeOf_of_isHW R h hσ μ ⟨v, hv⟩
  obtain ⟨m, hm⟩ := weight_int (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q n e ε T R σ h hσ).1.1.1 hS (e a)
  rw [Equiv.symm_apply_apply] at hm
  exact ⟨m, by exact_mod_cast hm⟩

theorem hasParam_iff_factors (hn : 0 < n) (P : SignedPar n) (h : BlockOrd e P.sgn) :
    HasParam R (blockPar P e) ↔ ∃ σ, Factors R.U e σ ∧ IsDSPar P σ := by
  refine ⟨fun hR => ?_, fun ⟨σ, h1, h2⟩ => (hasParam_iff_isDSPar R P h h1).2 h2⟩
  rcases Cover.trivial_or_twist R with k | k
  · obtain ⟨σ, hσ⟩ := exists_factors R.U e k
    exact ⟨σ, hσ, (hasParam_iff_isDSPar R P h hσ).1 hR⟩
  · exfalso
    obtain ⟨σ, hσ⟩ := exists_factors _ e k
    obtain ⟨v, hv⟩ := hR.1
    have hv' : Formalism.BasicNotions.TH.IsHW (Cover.twist R).HK.act (fun a => blattner (blockPar P e) a - 1 / 2) v :=
      (Cover.isHW_twAct R.HK.act _ v).2 (by simpa using hv)
    obtain ⟨m, hm⟩ := isHW_int (Cover.twist R) h hσ hv' (e.symm ⟨0, hn⟩)
    obtain ⟨m', hm'⟩ := blattner_int P h (e.symm ⟨0, hn⟩)
    have h1 : ((2 * m' : ℤ) : ℚ) = (2 * m + 1 : ℤ) := by push_cast; linarith
    have h2 : 2 * m' = 2 * m + 1 := by exact_mod_cast h1
    omega

theorem factors_twist_iff (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)) :
    Factors (Cover.twist R).U e σ ↔
      ∀ x, R.U.π x = ((T.sq x : ℂˣ) : ℂ) • σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q)) :=
  forall_congr' fun x => inv_smul_eq_iff₀ (T.sq x).ne_zero

theorem hasParam_half_iff (hn : 0 < n) (P : SignedPar n) (h : BlockOrd e P.sgn) :
    HasParam R (fun a => blockPar P e a + 1 / 2) ↔ ∃ σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H),
      (∀ x, R.U.π x = ((T.sq x : ℂˣ) : ℂ) • σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))) ∧
        IsDSPar P σ := by
  rw [← Cover.hasParam_twist, hasParam_iff_factors _ hn P h]
  exact exists_congr fun σ => and_congr_left' (factors_twist_iff R σ)

theorem isParam_cases {lam : Ix p q → ℚ} (h : IsParam lam) :
    ∃ (P : SignedPar (p + q)) (e : Ix p q ≃ Fin (p + q)), P.IsOfSig p q ∧ BlockOrd e P.sgn ∧
      (lam = blockPar P e ∨ lam = fun a => blockPar P e a + 1 / 2) := by
  by_cases hi : ∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m
  · obtain ⟨P, e, a, b, c⟩ := exists_blockPar h hi
    exact ⟨P, e, a, b, Or.inl c⟩
  · obtain ⟨a, ha⟩ := not_forall.1 hi
    have h' : IsParam fun b => lam b - 1 / 2 := by
      refine ⟨fun x y e => h.1 (sub_left_injective e), fun x y e => sub_lt_sub_right (h.2.1 x y e) _, fun x => ?_,
        fun x y => by simpa using h.2.2.2 x y⟩
      obtain ⟨k, hk⟩ := h.2.2.1 x
      exact ⟨k - 1, by push_cast; linarith⟩
    obtain ⟨P, e, a, b, c⟩ := exists_blockPar h' fun b => by
      obtain ⟨k, hk⟩ := h.2.2.1 a
      obtain ⟨l, hl⟩ := h.2.2.2 b a
      obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (k - (p + q : ℕ))
      · have : ((k - (p + q : ℕ) : ℤ) : ℚ) = (2 * j : ℤ) := by rw [hj]
        exact ⟨j + l, by push_cast at this ⊢; linarith⟩
      · have : ((k - (p + q : ℕ) : ℤ) : ℚ) = (2 * j + 1 : ℤ) := by rw [hj]
        exact absurd ⟨j + 1, by push_cast at this ⊢; linarith⟩ ha
    exact ⟨P, e, a, b, Or.inr (funext fun x => by rw [← c]; ring)⟩

theorem isParam_half (P : SignedPar n) (h : BlockOrd e P.sgn) : IsParam fun a => blockPar P e a + 1 / 2 := by
  have h0 := isParam_blockPar P h
  refine ⟨fun x y e => h0.1 (add_left_injective _ e), fun x y e => by simpa using h0.2.1 x y e, fun x => ?_,
    fun x y => by simpa using h0.2.2.2 x y⟩
  obtain ⟨k, hk⟩ := h0.2.2.1 x
  exact ⟨k + 1, by push_cast; linarith⟩

end Low

end GlobalTheory.RealPar

end
