import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.RingHypothesesOfCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachOperatorProductShiftMemLatticeStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem qp_isUnit (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  obtain ⟨wq, hwq⟩ := hR9.qq
  have h1 : IsUnit (algebraMap (LetA O n) W.EE (W.φA letπ)) := by
    have := W.EE_π.map W.φE
    rw [W.φE_ext] at this
    exact this
  rw [W.φA_π, map_mul] at h1
  have h2 := (IsUnit.mul_iff.1 h1).2
  rw [hwq, map_mul] at h2
  exact (IsUnit.mul_iff.1 h2).2

theorem qp_pow_inj (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) (k : ℕ) {x : W.DD T}
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = 0) : x = 0 := by
  have hu := (qp_isUnit W hR9).pow k
  rw [← map_pow] at hu
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) x] at h
  exact hu.smul_left_cancel.1 (h.trans (smul_zero _).symm)

theorem dl_of_qp (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) {i : ZMod n} {y : ℕ} {z : W.DD T}
    (h : Formalism.MainNotions.LiftingTheory.InNΔi W T i (Formalism.MainNotions.LiftingTheory.qp W ^ y • z)) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧ Formalism.MainNotions.LiftingTheory.qp W ^ y • z ∈ W.N T := by
  obtain ⟨hNΔ, hl⟩ := h
  have hN : Formalism.MainNotions.LiftingTheory.qp W ^ y • z ∈ W.N T := hNΔ.1
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ y • z) = Formalism.MainNotions.LiftingTheory.qp W ^ y • z := hNΔ.2
  obtain ⟨m, -, hme⟩ := Submodule.mem_map.1 hl
  refine ⟨⟨?_, fun δ hδ => ?_⟩, hN⟩
  · refine sub_eq_zero.1 (qp_pow_inj W hR9 y ?_)
    rw [smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ y) (letE i : LetA O n) z, ← hme]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self, sub_self]
  · refine sub_eq_zero.1 (qp_pow_inj W hR9 y ?_)
    have hq : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ y) = Formalism.MainNotions.LiftingTheory.qp W ^ y :=
      (W.AΔ.pow_mem (Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.qp_mem hR9) y) δ hδ
    have e : Formalism.MainNotions.LiftingTheory.qp W ^ y • W.γD T δ z = W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ y • z) := by
      rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, hq]
    rw [smul_sub, e, hΔ δ hδ, sub_self]

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

def pseq (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) (k : ℕ) : W.DD T :=
  Polynomial.aeval dop (((xs.take k).map fun x => Polynomial.X - Polynomial.C (cc x)).prod) z

theorem pseq_zero (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) :
    pseq W dop cc xs z 0 = z := by
  simp [pseq]

theorem pseq_succ (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) (k : ℕ)
    (hk : k < xs.length) :
    pseq W dop cc xs z (k + 1) = dop (pseq W dop cc xs z k) - cc (xs.getD k 0) • pseq W dop cc xs z k := by
  have ht : xs.take (k + 1) = xs.take k ++ [xs.getD k 0] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
    rfl
  unfold pseq
  rw [ht, List.map_append, List.prod_append, mul_comm, map_mul, Module.End.mul_apply]
  simp [Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

theorem pseq_length (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (X : Finset ℤ) (z : W.DD T) :
    pseq W dop cc X.toList z X.toList.length =
      Polynomial.aeval dop (∏ x ∈ X, (Polynomial.X - Polynomial.C (cc x))) z := by
  unfold pseq
  rw [List.take_length, Finset.prod_map_toList]

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem eigenvalue_product_maps_letter_lattice_local (l : ℕ) (hpl : PD.p = l)
    (hR9 : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T)
    (hdss : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (y' Y : ℕ)
      (cO : ℤ → O), (∀ x : ℤ, ((l : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) →
      ∀ xs : List ℤ, (∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i →
        IsJumpV PD T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) →
      ∀ seq : ℕ → W.DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp W ^ Y • seq 0 ∈ W.N T →
      (∀ k < xs.length, W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) =
        W.γD T W.gam (seq k) - seq k) →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq xs.length ∈ W.N T) :
    Formalism.MainNotions.N.LetterConditionLocal W := by
  intro hCA T hT i y _ dop hdop cc hcc X hX z hz
  obtain ⟨hDL, hzN⟩ := dl_of_qp W (hR9 hCA T hT) hz
  have hcc' : ∀ x : ℤ, ((l : ℕ) : O) * cc x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
    intro x
    have e := hcc x
    rw [hpl] at e
    linear_combination -e
  have hj : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i →
      IsJumpV PD T.ρ τ a → 0 < j → j ≤ y → a + (j : ℤ) ∈ X.toList :=
    fun τ a j ho hja h1 h2 => Finset.mem_toList.2 (hX τ a j ho hja h1 h2)
  have hrec : ∀ k < X.toList.length, W.π₀ • (pseq W dop cc X.toList z (k + 1) +
      cc (X.toList.getD k 0) • pseq W dop cc X.toList z k) =
      W.γD T W.gam (pseq W dop cc X.toList z k) - pseq W dop cc X.toList z k := by
    intro k hk
    rw [pseq_succ W dop cc X.toList z k hk, sub_add_cancel]
    exact hdop _
  have key := hdss hCA T hT i 0 y cc hcc' X.toList hj (pseq W dop cc X.toList z)
    (by rw [pseq_zero]; exact hDL) (by rw [pseq_zero]; exact hzN) hrec
  rw [pseq_length] at key
  obtain ⟨hD, hNl⟩ := key
  rw [pow_zero, one_smul] at hNl
  refine ⟨⟨hNl, hD.2⟩, Submodule.mem_map.2 ⟨_, hNl, ?_⟩⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact hD.1

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

open Formalism.BasicNotions.Loc

theorem eigenvalue_product_maps_letter_lattice_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := by
  intro D HW F Cm hN l _ K s LL h hCA
  have hs : s = 1 := by rw [← (HW l).W_s K s LL h]; exact hCA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, h⟩
    obtain ⟨w, hw⟩ := hCA.1.2 ⟨x, hx⟩
    have h2 := w.2.2
    have : ((w : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hw
    rw [this] at h2
    exact h2
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL h) := hN.2.2.2.2.2.2.2.2.1 l K 1 LL h
  exact eigenvalue_product_maps_letter_lattice_local _ l hpl (fun hA T hT => Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.ring_hypotheses_of_crystalline _ hA h9 T hT)
    (fun _ => GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl) hCA

end GlobalTheory.PrimeSequence

example : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions
