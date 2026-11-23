import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKSwapCup

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem liftQ_mem (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (q : ↥L.T ⧸ I) :
    Formalism.MainNotions.LocalSituation.liftQ L I q ∈ L.T :=
  (Submodule.Quotient.mk_surjective I q).choose.2

theorem mk_liftQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (q : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L I q, liftQ_mem L I q⟩ : ↥L.T) : ↥L.T ⧸ I) = q :=
  (Submodule.Quotient.mk_surjective I q).choose_spec

theorem liftQ_sub (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (x : ↥L.T)
    (q : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (hq : Submodule.Quotient.mk x = q) :
    ∃ t ∈ L.T, Formalism.MainNotions.LocalSituation.liftQ L _ q - (x : V) = (algebraMap O LL ϖ) ^ r • t := by
  have h : (⟨Formalism.MainNotions.LocalSituation.liftQ L _ q, liftQ_mem L _ q⟩ : ↥L.T) - x ∈
      (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) :=
    (Submodule.Quotient.eq _).1 ((mk_liftQ L _ q).trans hq.symm)
  generalize hy : (⟨Formalism.MainNotions.LocalSituation.liftQ L _ q, liftQ_mem L _ q⟩ : ↥L.T) - x = y at h
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨t, -, ht⟩ := h
  subst ht
  refine ⟨t, t.2, ?_⟩
  rw [← map_pow, algebraMap_smul, ← Submodule.coe_smul, ← hy]
  rfl

theorem inv_pow_mul_pow_mem (ϖ : O) (r : ℕ) :
    ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * (algebraMap O LL ϖ) ^ r = algebraMap O LL e := by
  rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨1, by subst hr; simp⟩
    · exact ⟨0, by rw [h, zero_pow hr.ne', mul_zero, map_zero]⟩
  · exact ⟨1, by rw [← mul_pow, inv_mul_cancel₀ h, one_pow, map_one]⟩

end Gen
end GlobalTheory.BKSwapCup

namespace GlobalTheory.BKSwapCup

section Cong
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def swapF (L : Lattice (O := O) ρ) (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O) (r : ℕ)
    (s : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (d : G → V') (g : G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (d g)

theorem swap_cong (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hint : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ e : O, P x y = algebraMap O LL e)
    (χ : G → LL) (hχ : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (s : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (hs : ∀ g h, s (g * h) = s g + actQ L _ hI g (s h))
    (d : G → V') (hdT : ∀ g, d g ∈ L'.T) (hdmul : ∀ g h, d (g * h) = d g + ρ' g (d h))
    (q : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T))
    (hq : ∀ h, Submodule.Quotient.mk (⟨d h, hdT h⟩ : ↥L'.T) = q h) (g h : G) :
    ∃ e : O, GlobalTheory.BKFinLevel.cupQ L L' P ϖ r s q (g, h)
      + cupLD L P.flip d (fun g => GlobalTheory.BKFinLevel.ioL L ϖ r (s g)) (g, h)
      + (χ g * swapF L P ϖ r s d h - swapF L P ϖ r s d (g * h) + swapF L P ϖ r s d g)
      = algebraMap O LL e := by
  have huT : ∀ g, Formalism.MainNotions.LocalSituation.liftQ L _ (s g) ∈ L.T := fun g => liftQ_mem L _ (s g)
  have hmk : ∀ g, (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s g), huT g⟩ : ↥L.T) :
      ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) = s g :=
    fun g => mk_liftQ L _ (s g)

  have hq3 : (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s g), huT g⟩ +
      actT L g ⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s h), huT h⟩ : ↥L.T) :
      ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) = s (g * h) := by
    rw [hs g h]
    exact (Submodule.Quotient.mk_add _).trans
      (congrArg₂ (· + ·) (hmk g) (congrArg (actQ L _ hI g) (hmk h)))
  obtain ⟨t3, ht3, hu3⟩ := liftQ_sub L ϖ r _ _ hq3

  obtain ⟨t1, ht1, hd1⟩ := liftQ_sub L' ϖ r _ _ (hq h)

  have hio : GlobalTheory.BKFinLevel.ioL L ϖ r (s h) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) :=
    (congrArg (GlobalTheory.BKFinLevel.ioL L ϖ r) (mk_liftQ L _ (s h))).symm.trans
      (GlobalTheory.BKFinLevel.ioL_mk L ϖ r _)
  have hl : (Submodule.Quotient.mk (liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h))) : V ⧸ L.T) =
      GlobalTheory.BKFinLevel.ioL L ϖ r (s h) :=
    (Submodule.Quotient.mk_surjective L.T _).choose_spec
  have ht2 := (Submodule.Quotient.eq _).1 (hl.trans hio)
  show ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (ρ' g (Formalism.MainNotions.LocalSituation.liftQ L' _ (q h)))
      + P.flip (d g) (ρ g (liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h))))
      + (χ g * ((algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) (d h))
        - (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s (g * h))) (d (g * h))
        + (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (d g)) = algebraMap O LL e
  generalize liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h)) = w at ht2 ⊢
  obtain ⟨t2, ht2', rfl⟩ : ∃ t2 ∈ L.T,
      w = (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ L _ (s h) + t2 :=
    ⟨_, ht2, by abel⟩
  have E1 : Formalism.MainNotions.LocalSituation.liftQ L' _ (q h) = d h + (algebraMap O LL ϖ) ^ r • t1 :=
    sub_eq_iff_eq_add'.1 hd1
  have E3 : Formalism.MainNotions.LocalSituation.liftQ L _ (s (g * h)) = Formalism.MainNotions.LocalSituation.liftQ L _ (s g) +
      ρ g (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) + (algebraMap O LL ϖ) ^ r • t3 :=
    sub_eq_iff_eq_add'.1 hu3
  obtain ⟨e0, he0⟩ := inv_pow_mul_pow_mem (LL := LL) ϖ r
  obtain ⟨e1, he1⟩ := hint _ (huT g) _ (L'.stable g _ ht1)
  obtain ⟨e2, he2⟩ := hint _ (L.stable g _ ht2') _ (hdT g)
  obtain ⟨e3, he3⟩ := hint t3 ht3 (d g + ρ' g (d h)) (by rw [← hdmul]; exact hdT _)
  refine ⟨e0 * e1 + e2 - e0 * e3, ?_⟩
  have E5 : χ g * ((algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) (d h)) =
      (algebraMap O LL ϖ)⁻¹ ^ r * P (ρ g (Formalism.MainNotions.LocalSituation.liftQ L _ (s h))) (ρ' g (d h)) := by
    rw [hχ]; ring
  rw [E1, E3, hdmul, E5]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.flip_apply] at he3 ⊢
  rw [map_sub, map_add, map_mul, map_mul, ← he0, ← he1, ← he2, ← he3]
  ring

end Cong
end GlobalTheory.BKSwapCup

namespace GlobalTheory.BKSwapCup

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem cobO_swap (hopen : IsOpen (Set.range (algebraMap O LL)))
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL)) {A A' : GRep G Qp LL O}
    (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hm : IsDualLat1 PD LA LA' m) (ϖ : O) (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (s : G → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hs : s ∈ quotientCocycles LA _ hI)
    (d : ↥(latticeCocycles LA')) :
    CobO PD L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔
      CobO PD L1 (cupLD LA m.flip (d : G → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  have hdT : ∀ g, (d : G → A'.V) g ∈ LA'.T := fun g => d.2.2 g (Set.mem_univ g)
  have hint : ∀ x ∈ LA.T, ∀ y ∈ LA'.T, ∃ e : O, m x y = algebraMap O LL e :=
    fun x hx y hy => (hm.2 y).1 hy x hx
  have key := swap_cong LA LA' m hint (fun g => ((cycLL PD LL g : LLˣ) : LL)) hm.1.1 ϖ r hI s
    hs.2 (d : G → A'.V) hdT d.2.1.2 (redT LA' _ d) (fun _ => rfl)
  let Fq : G → LL ⧸ L1.T := fun g =>
    Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) g)
  have hFq : Fq ∈ ReciprocityTheory.Def.C1 G (⊤ : Submodule O (LL ⧸ L1.T)) := by
    refine ⟨?_, fun _ => Submodule.mem_top⟩
    have hT : IsOpen (L1.T : Set LL) := by rw [hL1]; exact hopen
    have hu : Continuous fun g => Formalism.MainNotions.LocalSituation.liftQ LA _ (s g) :=
      (hs.1.comp (Formalism.MainNotions.LocalSituation.liftQ LA _)).continuous
    have hc : Continuous (swapF LA m ϖ r s (d : G → A'.V)) :=
      continuous_const.mul ((IsModuleTopology.continuous_bilinear_of_finite_left m).comp
        (hu.prodMk d.2.1.1))
    exact Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hT _ hc
  have hD : ReciprocityTheory.Def.d1 (repD L1) Fq ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := ⟨Fq, hFq, rfl⟩
  have heq : (fun x => (Submodule.Quotient.mk
      (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d) x) : LL ⧸ L1.T)) =
      -((fun x => (Submodule.Quotient.mk (cupLD LA m.flip (d : G → A'.V)
        (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g)) x) : LL ⧸ L1.T)) +
          ReciprocityTheory.Def.d1 (repD L1) Fq) := by
    funext x
    obtain ⟨g, h⟩ := x
    obtain ⟨e, he⟩ := key g h
    show (Submodule.Quotient.mk (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d) (g, h)) :
        LL ⧸ L1.T) = -(Submodule.Quotient.mk (cupLD LA m.flip (d : G → A'.V)
          (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g)) (g, h)) +
        (Submodule.Quotient.mk (((cycLL PD LL g : LLˣ) : LL) * swapF LA m ϖ r s (d : G → A'.V) h)
          - Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) (g * h))
          + Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) g)))
    rw [eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add,
      ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, ← add_assoc, he,
      Submodule.Quotient.mk_eq_zero, hL1]
    exact ⟨e, rfl⟩
  unfold CobO
  rw [heq, neg_mem_iff, Submodule.add_mem_iff_left _ hD]

end Cob

theorem cobO_cupQ_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ s ∈ quotientCocycles LA _ hI, ∀ d : ↥(latticeCocycles LA'), CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔ CobO (P.PD K) L1 (cupLD LA m.flip (d : ↥(GK K) → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm ϖ r hI s hs d
  obtain ⟨-, -, -, htr, hopen⟩ := hO
  haveI := htr
  exact cobO_swap (P.PD K) hopen L1 hL1 LA LA' m hm ϖ r hI s hs d

end GlobalTheory.BKSwapCup
