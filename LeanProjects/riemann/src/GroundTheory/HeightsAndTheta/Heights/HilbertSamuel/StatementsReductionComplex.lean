import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreSectionLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreReduction

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem idealOver_int (y : (Σ k, ι k) → Ω) : GenOnFibres.idealOver y ℤ = mCoordIdeal y := by
  have h : (MvPolynomial.map (Int.castRingHom ℤ) : MRingOver ℤ ι →+* MRingOver ℤ ι) = RingHom.id _ := by
    refine RingHom.ext fun f => ?_
    rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, map_id]
    rfl
  show Ideal.map _ _ = _
  rw [h, Ideal.map_id]

def redRing (y : (Σ k, ι k) → Ω) (p : ℕ) :
    (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) →+* (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) :=
  Ideal.quotientMap _ (MvPolynomial.map (Int.castRingHom (ZMod p))) (by
    rw [idealOver_int]
    exact Ideal.le_comap_map)

theorem redRing_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (f : MRingOver ℤ ι) :
    redRing y p (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom (ZMod p)) f) :=
  Ideal.quotientMap_mk

theorem redRing_smul (y : (Σ k, ι k) → Ω) (p : ℕ) (r : MRingOver ℤ ι)
    (x : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) :
    redRing y p (r • x) = MvPolynomial.map (Int.castRingHom (ZMod p)) r • redRing y p x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GenOnFibres.smul_mk, redRing_mk, redRing_mk, GenOnFibres.smul_mk, map_mul]

theorem map_mem_cellMon (p : ℕ) {I : ∀ k, Finset (ι k)} {t : MRingOver ℤ ι} (ht : t ∈ KH.cellMon ℤ I) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) t ∈ KH.cellMon (ZMod p) I := by
  unfold KH.cellMon at ht ⊢
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [map_X]
    exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul f g _ _ hf hg => rw [map_mul]; exact mul_mem hf hg

def redLocFun (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)) :
    LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) :=
  x.liftOn (fun mt => LocalizedModule.mk (redRing y p mt.1) ⟨_, map_mem_cellMon p mt.2.2⟩) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    refine LocalizedModule.mk_eq.mpr ⟨⟨_, map_mem_cellMon p u.2⟩, ?_⟩
    have h := congrArg (redRing y p) hu
    simp only [Submonoid.smul_def, redRing_smul] at h ⊢
    exact h)

theorem redLocFun_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) (t : KH.cellMon ℤ I) :
    redLocFun y p I (LocalizedModule.mk m t) =
      LocalizedModule.mk (redRing y p m) ⟨_, map_mem_cellMon p t.2⟩ := by
  unfold redLocFun
  exact LocalizedModule.liftOn_mk _ _ _

def redLoc (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k)) :
    LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) →+
      LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) where
  toFun := redLocFun y p I
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, redLocFun_mk, map_zero, LocalizedModule.zero_mk]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, redLocFun_mk, redLocFun_mk, redLocFun_mk, LocalizedModule.mk_add_mk, map_add]
      simp only [Submonoid.smul_def, redRing_smul]
      congr 1
      exact Subtype.ext (map_mul _ _ _)

theorem redLoc_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) (t : KH.cellMon ℤ I) :
    redLoc y p I (LocalizedModule.mk m t) = LocalizedModule.mk (redRing y p m) ⟨_, map_mem_cellMon p t.2⟩ :=
  redLocFun_mk y p I m t

def redCoch (y : (Σ k, ι k) → Ω) (p n : ℕ) :
    KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n →+
      KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n :=
  { toFun := fun w I => redLoc y p I.1 (w I)
    map_zero' := funext fun I => map_zero (redLoc y p I.1)
    map_add' := fun w w' => funext fun I => map_add (redLoc y p I.1) (w I) (w' I) }

theorem redCoch_apply (y : (Σ k, ι k) → Ω) (p n : ℕ)
    (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) (I : KH.Cell K ι n) :
    redCoch y p n w I = redLoc y p I.1 (w I) :=
  rfl

end FibreReduction

def ReductionComplex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D p : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime →
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p (n + 1) (KH.cechD ℤ ι _ n w) =
        KH.cechD (ZMod p) ι _ n (FibreReduction.redCoch y p n w)) ∧
    (∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w ∈
        KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n) ∧
    (∀ n : ℕ, ∀ z ∈ KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n,
      ∃ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, FibreReduction.redCoch y p n w = z) ∧
    (∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w') ∧
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), (p : ℤ) • w = 0 → w = 0) ∧
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0)

theorem ReductionComplex.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := PtIdx) unitPoint) (0 + 1) ∧ Nat.Prime 2 :=
  ⟨FibreSectionLift.hyps_inhabited.1, FibreSectionLift.hyps_inhabited.2.1⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
