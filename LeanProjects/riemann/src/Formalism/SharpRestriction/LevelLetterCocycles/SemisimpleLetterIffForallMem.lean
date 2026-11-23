import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExtensionClauses
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators

noncomputable section

namespace Formalism.MainNotions.UnusedSlot35.DssRec

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem rec_exists {R E M : Type} [CommRing R] [CommRing E] [Algebra R E] [AddCommGroup M]
    [Module R M] [Module E M] [IsScalarTower R E M] (p : R) (hp : IsUnit (algebraMap R E p))
    (F : ℕ → M → M) (y₀ : M) : ∃ s : ℕ → M, s 0 = y₀ ∧ ∀ k, p • s (k + 1) = F k (s k) := by
  obtain ⟨u, hu⟩ := hp
  let s : ℕ → M := fun k => Nat.rec y₀ (fun k sk => ((u⁻¹ : Eˣ) : E) • F k sk) k
  refine ⟨s, rfl, fun k => ?_⟩
  show p • (((u⁻¹ : Eˣ) : E) • F k (s k)) = F k (s k)
  rw [← algebraMap_smul E p, ← hu, smul_smul, Units.mul_inv, one_smul]

theorem smul_inj {R E M : Type} [CommRing R] [CommRing E] [Algebra R E] [AddCommGroup M]
    [Module R M] [Module E M] [IsScalarTower R E M] (p : R) (hp : IsUnit (algebraMap R E p))
    {a b : M} (h : p • a = p • b) : a = b := by
  obtain ⟨u, hu⟩ := hp
  have h' : (u : E) • a = (u : E) • b := by
    rw [hu, algebraMap_smul, algebraMap_smul]
    exact h
  have := congrArg (fun m => ((u⁻¹ : Eˣ) : E) • m) h'
  simpa [smul_smul] using this

theorem rec_unique {R E O M : Type} [CommRing R] [CommRing E] [CommRing O] [Algebra R E]
    [AddCommGroup M] [Module R M] [Module E M] [Module O M] [IsScalarTower R E M] (p : R)
    (hp : IsUnit (algebraMap R E p)) (c : ℕ → O) (Gm : M → M) (L : ℕ) (s s' : ℕ → M)
    (h0 : s 0 = s' 0)
    (hs : ∀ k, k < L → p • (s (k + 1) + c k • s k) = Gm (s k))
    (hs' : ∀ k, k < L → p • (s' (k + 1) + c k • s' k) = Gm (s' k)) :
    ∀ k, k ≤ L → s k = s' k := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have ih' := ih (by omega)
    have h1 := hs k (by omega)
    have h2 := hs' k (by omega)
    rw [← ih'] at h2
    have := smul_inj (E := E) p hp (h1.trans h2.symm)
    exact add_right_cancel this

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem π₀_unit (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
  have hK : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨w, hw⟩ := ((h9 T hT hA.2.1 hA.2.2).2.2 hK).1.2.2.1
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

def DssMem (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (Y : ℕ) (y₀ : W.DD T), Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∀ seq : ℕ → W.DD T, seq 0 = y₀ →
        (∀ k : ℕ, k < (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length →
          W.π₀ • (seq (k + 1) + cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi)
            (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • seq k) = W.γD T W.gam (seq k) - seq k) →
        seq (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length ∈ W.N T

theorem coreDss_iff_mem (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.LiftingTheory.coreDss W ↔ DssMem W := by
  constructor
  · intro hc hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ seq h0 hrec
    obtain ⟨s, hs0, hsrec, hsN⟩ := hc hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ
    have hu := π₀_unit W h9 hA T hT
    have heq := rec_unique (E := W.EE) W.π₀ hu
      (fun k => cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0))
      (fun m => W.γD T W.gam m - m) _ s seq (hs0.trans h0.symm) hsrec hrec _ le_rfl
    rw [← heq]
    exact hsN
  · intro hm hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ
    have hu := π₀_unit W h9 hA T hT
    obtain ⟨s, hs0, hs⟩ := rec_exists (E := W.EE) W.π₀ hu
      (fun k m => (W.γD T W.gam m - m) -
        W.π₀ • (cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • m)) y₀
    have hrec : ∀ k : ℕ, k < (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length →
        W.π₀ • (s (k + 1) + cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • s k) =
          W.γD T W.gam (s k) - s k := by
      intro k _
      rw [smul_add, hs]
      abel
    exact ⟨s, hs0, hrec, hm hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ s hs0 hrec⟩

def DssLetMem (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (i : ZMod n) (y' Y : ℕ) (y₀ : W.DD T), y' ≤ Y → Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.Nl T i →
      (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∀ seq : ℕ → W.DD T, seq 0 = y₀ →
        (∀ k : ℕ, k < (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length →
          W.π₀ • (seq (k + 1) + cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • seq k) =
            W.γD T W.gam (seq k) - seq k) →
        Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length ∈ W.Nl T i

theorem dssLet_iff_mem (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.RamifiedCoefficientChains.DssLet W ↔ DssLetMem W := by
  constructor
  · intro hc hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ seq h0 hrec
    obtain ⟨s, hs0, hsrec, hsN⟩ := hc hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ
    have hu := π₀_unit W h9 hA T hT
    have heq := rec_unique (E := W.EE) W.π₀ hu
      (fun k => cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0))
      (fun m => W.γD T W.gam m - m) _ s seq (hs0.trans h0.symm) hsrec hrec _ le_rfl
    rw [← heq]
    exact hsN
  · intro hm hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ
    have hu := π₀_unit W h9 hA T hT
    obtain ⟨s, hs0, hs⟩ := rec_exists (E := W.EE) W.π₀ hu
      (fun k m => (W.γD T W.gam m - m) -
        W.π₀ • (cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • m)) y₀
    have hrec : ∀ k : ℕ, k < (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length →
        W.π₀ • (s (k + 1) + cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • s k) =
          W.γD T W.gam (s k) - s k := by
      intro k _
      rw [smul_add, hs]
      abel
    exact ⟨s, hs0, hrec, hm hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ s hs0 hrec⟩

end Core

theorem semisimpleProductTheorem_iff_dssMem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) :
    Formalism.MainNotions.UnusedSlot35.SemisimpleProductTheorem D HW F Cm ↔ (Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm →
      ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
        DssMem ((HW l).W K s LL h)) := by
  constructor
  · intro h hAdm l _ K s LL hG
    have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL hG) := hAdm.2.2.2.1 l K s LL hG
    exact (coreDss_iff_mem _ h9).1 (h hAdm l K s LL hG)
  · intro h hAdm l _ K s LL hG
    have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL hG) := hAdm.2.2.2.1 l K s LL hG
    exact (coreDss_iff_mem _ h9).2 (h hAdm l K s LL hG)

theorem semisimple_letter_iff_forall_mem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) :
    Formalism.MainNotions.UnusedSlot35.SemisimpleLetterTheorem D HW F Cm ↔ (Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm →
      ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
        DssLetMem ((HW l).W K s LL h)) := by
  constructor
  · intro h hAdm l _ K s LL hG
    have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL hG) := hAdm.2.2.2.1 l K s LL hG
    exact (dssLet_iff_mem _ h9).1 (h hAdm l K s LL hG)
  · intro h hAdm l _ K s LL hG
    have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL hG) := hAdm.2.2.2.1 l K s LL hG
    exact (dssLet_iff_mem _ h9).2 (h hAdm l K s LL hG)

end Formalism.MainNotions.UnusedSlot35.DssRec
