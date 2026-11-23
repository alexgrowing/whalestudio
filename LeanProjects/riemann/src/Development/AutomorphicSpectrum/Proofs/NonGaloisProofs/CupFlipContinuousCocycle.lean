import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.CupFlip

section Top

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

theorem continuous_act (A : GRep G Qp LL O) : Continuous fun p : G × A.V => A.ρ p.1 p.2 := by
  have := IsModuleTopology.toContinuousSMul LL A.V
  let b := Module.finBasis LL A.V
  have e : (fun p : G × A.V => A.ρ p.1 p.2) =
      fun p => ∑ i, (b.repr p.2 i) • A.ρ p.1 (b i) := by
    funext p
    have h := congrArg (A.ρ p.1) (b.sum_repr p.2)
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h.symm
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 : Continuous fun v : A.V => b.coord i v :=
    IsModuleTopology.continuous_of_linearMap (b.coord i)
  exact (h1.comp continuous_snd).smul ((A.cont (b i)).comp continuous_fst)

theorem continuous_pair (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) :
    Continuous fun p : A.V × A'.V => P p.1 p.2 := by
  have := IsModuleTopology.toContinuousSMul LL A'.V
  exact IsModuleTopology.continuous_bilinear_of_finite_left P

theorem continuous_cup (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) {a : G → A.V}
    {b : G → A'.V} (ha : Continuous a) (hb : Continuous b) : Continuous (cupL A'.ρ P a b) :=
  (continuous_pair A A' P).comp ((ha.comp continuous_fst).prodMk
    ((continuous_act A').comp (continuous_fst.prodMk (hb.comp continuous_snd))))

end Top

section Cup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} {P : V →ₗ[LL] V' →ₗ[LL] LL}

omit [TopologicalSpace G] in

theorem char_pair (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    (g : G) (x : V) (y : V') : charRep (cycLL PD LL) g (P x y) = P (ρ g x) (ρ' g y) := by
  rw [hd]
  rfl

theorem d2_cup (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) :
    ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) (cupL ρ' P a b) = 0 := by
  funext ⟨g, h, k⟩
  show charRep (cycLL PD LL) g (P (a h) (ρ' h (b k))) - P (a (g * h)) (ρ' (g * h) (b k)) +
    P (a g) (ρ' g (b (h * k))) - P (a g) (ρ' g (b h)) = 0
  rw [char_pair PD hd, ha, hb, map_mul, Module.End.mul_apply]
  simp only [map_add, LinearMap.add_apply]
  ring

theorem d1_pair (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) (fun g => P (a g) (b g)) =
      -cupL ρ' P a b - cupL ρ P.flip b a := by
  funext ⟨g, h⟩
  show charRep (cycLL PD LL) g (P (a h) (b h)) - P (a (g * h)) (b (g * h)) + P (a g) (b g) =
    -P (a g) (ρ' g (b h)) - P (ρ g (a h)) (b g)
  rw [char_pair PD hd, ha, hb]
  simp only [map_add, LinearMap.add_apply]
  ring

variable [TopologicalSpace LL]

theorem cob_of_flip [IsTopologicalRing LL]
    (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) (hc : Continuous fun g => P (a g) (b g))
    (h : CobL PD (cupL ρ P.flip b a)) : CobL PD (cupL ρ' P a b) := by
  obtain ⟨u, hu, e⟩ := h
  refine ⟨-u - fun g => P (a g) (b g), hu.neg.sub hc, ?_⟩
  rw [map_sub, map_neg, e, d1_pair PD hd ha hb]
  abel

theorem cob_of_left (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} {x : V} (ha : ∀ g, a g = ρ g x - x)
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) (hc : Continuous fun g => P x (b g)) :
    CobL PD (cupL ρ' P a b) := by
  refine ⟨fun g => P x (b g), hc, ?_⟩
  funext ⟨g, h⟩
  show charRep (cycLL PD LL) g (P x (b h)) - P x (b (g * h)) + P x (b g) =
    P (a g) (ρ' g (b h))
  rw [char_pair PD hd, ha, hb]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  ring

end Cup

theorem cup_flip : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P → IsDual1 ((D.loc l).PD K) A'.ρ A.ρ P.flip ∧ ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, Continuous (cupL A'.ρ P a b) ∧ ReciprocityTheory.Def.d2 (charRep (cycLL ((D.loc l).PD K) LL)) (cupL A'.ρ P a b) = 0 ∧ (CobL ((D.loc l).PD K) (cupL A'.ρ P a b) ↔ CobL ((D.loc l).PD K) (cupL A.ρ P.flip b a)) ∧ ((a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ) → CobL ((D.loc l).PD K) (cupL A'.ρ P a b)) := by
  intro D l _ K LL _ _ _ O _ _ hO A A' P hP
  have : IsTopologicalRing LL := hO.2.2.2.1
  have hd := hP.1
  have hdf : ∀ g y x, P.flip (A'.ρ g y) (A.ρ g x) =
      ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL) * P.flip y x := fun g y x => hd g x y
  refine ⟨⟨hdf, hP.2.2.1, hP.2.1, hP.2.2.2.symm⟩, fun a ha b hb => ?_⟩
  obtain ⟨hac, hacoc⟩ := ha
  obtain ⟨hbc, hbcoc⟩ := hb
  have hc : Continuous fun g => P (a g) (b g) := (continuous_pair A A' P).comp (hac.prodMk hbc)
  have hflip : CobL ((D.loc l).PD K) (cupL A.ρ P.flip b a) →
      CobL ((D.loc l).PD K) (cupL A'.ρ P a b) := cob_of_flip _ hd hacoc hbcoc hc
  refine ⟨continuous_cup A A' P hac hbc, d2_cup _ hd hacoc hbcoc, ⟨fun h => ?_, hflip⟩, ?_⟩
  · refine cob_of_flip _ (P := P.flip) hdf hbcoc hacoc hc ?_
    rwa [LinearMap.flip_flip]
  · rintro (h | h)
    · obtain ⟨x, hx⟩ := LinearMap.mem_range.1 h
      exact cob_of_left _ hd (x := x) (fun g => by rw [← hx]; rfl) hbcoc
        ((continuous_pair A A' P).comp (continuous_const.prodMk hbc))
    · obtain ⟨y, hy⟩ := LinearMap.mem_range.1 h
      exact hflip (cob_of_left _ (P := P.flip) hdf (x := y) (fun g => by rw [← hy]; rfl) hacoc
        ((continuous_pair A' A P.flip).comp (continuous_const.prodMk hac)))

end GlobalTheory.CompanionTheory.CupFlip
