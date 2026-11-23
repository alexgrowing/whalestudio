import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLx
import Mathlib
import Formalism.FormalDegreeBessel.FinalDS

open MeasureTheory Finset
open scoped Matrix

noncomputable section

namespace Formalism.MainNotions.DiscreteSeriesWeylDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HasTypeU (k : ℕ) (u : Fin k → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π

def HighestWeightExists : Prop := ∀ (k : ℕ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.IsHCParam u → HasTypeU k u

theorem dimPiU_eq (hW : LocalBesselAndTopKernel.AdmittedWeylDimension) {k : ℕ} {u : Fin k → ℝ} (hu : StrictAnti u) (hE : HasTypeU k u) :
    (dimPiU k u : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  obtain ⟨H, i1, i2, π, hπ⟩ := hE
  have hmem : dimPiU k u ∈ {d | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π ∧ Module.finrank ℂ H = d} :=
    Nat.sInf_mem ⟨_, H, i1, i2, π, hπ, rfl⟩
  obtain ⟨H', j1, j2, π', hπ', hd⟩ := hmem
  rw [← hd]
  exact @hW k u H' j1 j2 π' hu hπ'

theorem uS_anti (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : StrictAnti (uS D u τ) := by
  have step : ∀ (n : ℕ) (h : n + 1 < D.R.k),
      (D.hcW u τ).u ⟨n + 1, h⟩ < (D.hcW u τ).u ⟨n, by omega⟩ := by
    intro n h
    have h1 := (D.hcW u τ).v_gt_u ⟨n, by omega⟩
    have h2 := (D.hcW u τ).u_gt_v ⟨n, by omega⟩
    exact h1.trans h2
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  have hij' : i + 1 ≤ j := hij
  clear hij
  unfold uS
  simp only [Rat.cast_lt]
  induction j, hij' using Nat.le_induction with
  | base => exact step i hj
  | succ j hij2 ih => exact (step j hj).trans (ih (by omega))

section Family

variable {eps : ℝ} (Fm : FamP eps)

private theorem isHCParam_uS' (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsHCParam (uS D w τ) := by
  refine ⟨uS_anti D w τ, fun a => ?_⟩
  obtain ⟨z, hz⟩ := (D.hcW w τ).u_half a
  obtain ⟨r, hr⟩ := D.R.k_even
  have hk : (D.R.k : ℝ) = r + r := by exact_mod_cast hr
  refine ⟨z + 1 - r, ?_⟩
  show ((D.hcW w τ).u a : ℝ) - ((D.R.k : ℝ) - 1) / 2 = ((z + 1 - r : ℤ) : ℝ)
  rw [hz, hk]
  push_cast
  ring

theorem weyl_dimension_of_highest_weight (weylLawBound : LocalBesselAndTopKernel.FirstSizeStatement) (hE : HighestWeightExists) (gc : AdmissibleBoundsFromSource.GivC) : AdmissibleBoundsFromSource.FamilyWeylDimension Fm gc := by
  unfold AdmissibleBoundsFromSource.FamilyWeylDimension OwnEv
  refine ⟨0, fun x _ i => ?_⟩
  intro _ u τ
  exact dimPiU_eq weylLawBound (uS_anti _ u τ) (hE _ _ (isHCParam_uS' _ u τ))

theorem lWeylU_of_open (weylLawBound : LocalBesselAndTopKernel.FirstSizeStatement) (hE : HighestWeightExists) :
    ∀ Cg cb Cu cT CT C0, VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 := by
  intro Cg cb Cu cT CT C0
  unfold VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient OwnEv
  refine ⟨0, fun x _ i => ?_⟩
  intro _ w τ
  exact dimPiU_eq weylLawBound (uS_anti _ w τ) (hE _ _ (isHCParam_uS' _ w τ))

end Family

section SmallRank

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end SmallRank

theorem isFdeg_smul {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {μ : Measure (Formalism.REAL.UJ ε)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (c : NNReal) (hc : 0 < c)
    (h : IsFdeg μ σ d) : IsFdeg ((c : ENNReal) • μ) σ (d / c) := by
  obtain ⟨hd, hI⟩ := h
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hc0 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨div_pos hd (by exact_mod_cast hc), fun v w v' w' =>
    ⟨(hI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
  rw [integral_smul_measure, (hI v w v' w').2, ENNReal.coe_toReal, Complex.real_smul, Complex.ofReal_div]
  first
  | (field_simp; done)
  | (field_simp; ring)

def DiscreteSeriesExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ

section FamilyDS

variable {eps : ℝ} (Fm : FamP eps)

end FamilyDS

theorem isURepOn_mono {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {G G' : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : G' ⊆ G)
    (hU : IsURepOn G σ) : IsURepOn G' σ := by
  obtain ⟨⟨h1, hm⟩, hn, hc⟩ := hU
  exact ⟨⟨h1, fun a ha b hb => hm a (h ha) b (h hb)⟩, fun g hg => hn g (h hg), fun v => (hc v).mono h⟩

theorem kset_subset {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Kset ε ⊆ UJset ε := by
  intro g hg
  obtain ⟨hu, hc⟩ := hg
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  have hgg : gᴴ * g = 1 := by
    have h' := Matrix.mem_unitaryGroup_iff'.mp hu
    simpa [Matrix.star_eq_conjTranspose] using h'
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hgg, Matrix.one_mul]

def WeylForK : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Formalism.REAL.Kset ε) σ → IsKTypeOf ε σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + Formalism.REAL.rhoC ε) a - (Λ + Formalism.REAL.rhoC ε) b)) /
      ((∏ i ∈ Finset.range (LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ))

def LowKMultOne : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S'

theorem lowK_add_rhoC_sub {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) {a b : Fin N} (hab : a < b) (he : ε a = ε b) :
    (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) a - (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) b =
      lam a - lam b + ((Finset.univ.filter (fun c => a < c ∧ c < b ∧ ε c ≠ ε a)).card : ℝ) := by
  have hN : (univ.filter fun c => a < c ∧ ε c ≠ ε a).card + (univ.filter fun c => c < b ∧ ε c ≠ ε a).card
      = (univ.filter fun c => b < c ∧ ε c ≠ ε a).card + (univ.filter fun c => c < a ∧ ε c ≠ ε a).card
        + 2 * (univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card := by
    simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ε c = ε a
    · simp [hc]
    · have hca : (c : ℕ) ≠ a := fun h => hc (by rw [Fin.ext h])
      have hcb : (c : ℕ) ≠ b := fun h => hc (by rw [Fin.ext h, he])
      have hab' : (a : ℕ) < b := hab
      simp only [hc, ne_eq, not_false_eq_true, and_true]
      split_ifs <;> simp only [Fin.lt_def] at * <;> omega
  have hR : ((univ.filter fun c => a < c ∧ ε c ≠ ε a).card : ℝ)
        + ((univ.filter fun c => c < b ∧ ε c ≠ ε a).card : ℝ)
      = ((univ.filter fun c => b < c ∧ ε c ≠ ε a).card : ℝ)
        + ((univ.filter fun c => c < a ∧ ε c ≠ ε a).card : ℝ)
        + 2 * ((univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card : ℝ) := by
    exact_mod_cast hN
  simp only [Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Pi.add_apply, Pi.sub_apply, ← he]
  linarith

theorem dTauF_eq {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) :
    LocalBesselAndTopKernel.dTauF ε lam =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) a - (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) b)) /
      ((∏ i ∈ Finset.range (LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ)) := by
  unfold LocalBesselAndTopKernel.dTauF
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
  obtain ⟨hab, he⟩ := (Finset.mem_filter.mp hb).2
  exact (lowK_add_rhoC_sub ε lam hab he).symm

theorem lDTau_of_open (hW : WeylForK) (hM : LowKMultOne) : LocalBesselAndTopKernel.FamilyMassTheoremTwo := by
  unfold LocalBesselAndTopKernel.FamilyMassTheoremTwo LocalBesselAndTopKernel.FamilyMassLastLine
  intro N ε lam H _ _ σ hlam hDS
  obtain ⟨_, _, hU, _, _, ⟨S, hS⟩, _⟩ := id hDS
  have hset : {S' | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = {S} := by
    ext S'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => hM N ε lam H σ hlam hDS S' S h hS, fun h => h ▸ hS⟩
  have hsup : lowKSub ε lam σ = S := by
    unfold lowKSub
    rw [hset, sSup_singleton]
  rw [hsup, dTauF_eq]
  exact hW N ε _ H σ S (isURepOn_mono (kset_subset ε) hU) hS

theorem lowest_K_type_count_of_weyl (D : D7) (hW : WeylForK) (hM : LowKMultOne) : StandardLattice.FamilyMassLastLine D := by
  unfold StandardLattice.FamilyMassLastLine
  intro n ε lam hlam H _ _ _ σ hDS
  obtain ⟨_, _, hU, _, _, ⟨S, hS⟩, _⟩ := id hDS
  have hset : {S' | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = {S} := by
    ext S'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => hM n ε lam H σ hlam hDS S' S h hS, fun h => h ▸ hS⟩
  have hsup : lowKSub ε lam σ = S := by
    unfold lowKSub
    rw [hset, sSup_singleton]
  refine ⟨hsup ▸ hS, ?_⟩
  have e := lDTau_of_open hW hM n ε lam H σ hlam hDS
  rw [e]
  unfold StandardLattice.dTau LocalBesselAndTopKernel.dTauF
  congr 1
  · refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
    obtain ⟨hab, he⟩ := (Finset.mem_filter.mp hb).2
    have h := lowK_add_rhoC_sub ε lam hab he
    simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply] at h
    have ha : StandardLattice.rhoN ε a = Formalism.REAL.rhoN ε a := rfl
    have hb' : StandardLattice.rhoN ε b = Formalism.REAL.rhoN ε b := rfl
    rw [ha, hb']
    linarith

section FamilyRk

variable {eps : ℝ} (Fm : FamP eps)

end FamilyRk

section FamilyExp

variable {eps : ℝ} (Fm : FamP eps)

end FamilyExp

def TermsSummable (D : D7) (X : TermTie D) : Prop :=
  ∀ u u' : D.what₂.Word, Summable (fun t : D.s.Term u u' => BridgeLemma.aT X t)

def PairFibres (D : D7) : Prop :=
  ∀ u u' : D.what₂.Word, ∃ M : ℕ, ∀ t t' : D.s.Term u u',
    {p : D.s.Pair u u' | D.s.pfst p = t ∧ D.s.psnd p = t'}.encard ≤ M

def PairMajorant (D : D7) (X : TermTie D) : Prop :=
  ∀ u u' : D.what₂.Word, Summable (fun p : D.s.Pair u u' => BridgeLemma.wP X p)

section FamilyExp2

variable {eps : ℝ} (Fm : FamP eps)

def ExpansionF : Prop := PX.Under Fm fun x i => ∀ u u' : (Fm.D x i).what₂.Word, KExpansion (Fm.D x i).s u u'

end FamilyExp2

def BetaRigid (D : D7) (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (p q : D.s.Pair u u'), D.s.pfst p = D.s.pfst q → D.s.psnd p = D.s.psnd q →
    ∀ x ∈ Lat.orth (Lat.hS D) (Lat.Xsp (X.fl' (D.s.pfst q))),
      X.beta q x - X.beta p x ∈ Lat.Xsp (X.fl' (D.s.psnd q))

section FamilyRigid

variable {eps : ℝ} (Fm : FamP eps)

end FamilyRigid

section FiniteOrder

open Polynomial

end FiniteOrder

section FiniteOrderMat

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {N : Type*} [Fintype N] [DecidableEq N]

structure UnramAt (ϖ : R) (p : ℕ) : Prop where
  prime : Prime ϖ
  sep : ∀ x : R, (∀ n : ℕ, ϖ ^ n ∣ x) → x = 0
  pPrime : p.Prime
  three_le : 3 ≤ p
  unram : ∃ u : R, ¬ ϖ ∣ u ∧ (p : R) = u * ϖ
  other : ∀ l : ℕ, l.Prime → l ≠ p → ¬ ϖ ∣ (l : R)

theorem pow_congr_one {ϖ : R} {β : Matrix N N R} (h1 : ∃ X : Matrix N N R, β = 1 + ϖ • X) (m : ℕ) :
    ∃ X : Matrix N N R, β ^ m = 1 + ϖ • X := by
  obtain ⟨X, rfl⟩ := h1
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨Y + X + ϖ • (Y * X), ?_⟩
    rw [pow_succ, hY]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel

end FiniteOrderMat

end Formalism.MainNotions.DiscreteSeriesWeylDimension

end
