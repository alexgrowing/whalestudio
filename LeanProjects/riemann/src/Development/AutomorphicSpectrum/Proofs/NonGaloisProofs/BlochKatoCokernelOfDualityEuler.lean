import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.CompanionTheory.BKTorsion

open Formalism.MainNotions.BlochKatoDuality.Br Formalism.MainNotions.LocalSituation

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL] {A A' : GRep G Qp LL O}

abbrev aT (L : Lattice (O := O) A.ρ) (a : O) : Submodule O ↥L.T := Ideal.span {a} • ⊤

theorem mem_aT {L : Lattice (O := O) A.ρ} {a : O} {x : ↥L.T} :
    x ∈ aT L a ↔ ∃ y : ↥L.T, x = a • y := by
  rw [aT, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩

theorem liftQ_mem (L : Lattice (O := O) A.ρ) (I : Submodule O ↥L.T) (c : ↥L.T ⧸ I) :
    liftQ L I c ∈ L.T := (Submodule.Quotient.mk_surjective I c).choose.2

theorem liftQ_mk (L : Lattice (O := O) A.ρ) (a : O) (t : ↥L.T) :
    ∃ y : ↥L.T, liftQ L (aT L a) (Submodule.Quotient.mk t) = (t : A.V) + a • (y : A.V) := by
  have h := (Submodule.Quotient.mk_surjective (aT L a) (Submodule.Quotient.mk t)).choose_spec
  obtain ⟨y, hy⟩ := mem_aT.1 ((Submodule.Quotient.eq _).1 h)
  refine ⟨y, ?_⟩
  have := congrArg (fun z : ↥L.T => (z : A.V)) hy
  simp only [Submodule.coe_sub, Submodule.coe_smul] at this
  rw [← this, liftQ]
  abel

theorem inv_smul_smul {a : O} (ha : a ≠ 0) (v : A.V) :
    (algebraMap O LL a)⁻¹ • a • v = v := by
  have : algebraMap O LL a ≠ 0 := fun h => ha (IsFractionRing.injective O LL (by rw [h, map_zero]))
  rw [← algebraMap_smul LL a v, smul_smul, inv_mul_cancel₀ this, one_smul]

def io (L : Lattice (O := O) A.ρ) (a : O) (c : ↥L.T ⧸ aT L a) : A.V ⧸ L.T :=
  Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • liftQ L (aT L a) c)

theorem io_mk (L : Lattice (O := O) A.ρ) {a : O} (ha : a ≠ 0) (t : ↥L.T) :
    io L a (Submodule.Quotient.mk t) = Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • (t : A.V)) := by
  obtain ⟨y, hy⟩ := liftQ_mk L a t
  rw [io, hy, smul_add, inv_smul_smul ha, Submodule.Quotient.eq, add_sub_cancel_left]
  exact y.2

theorem io_Z1D (L : Lattice (O := O) A.ρ) {a : O} (ha : a ≠ 0) (hI : StableSub L (aT L a))
    {c : G → ↥L.T ⧸ aT L a} (hc : c ∈ quotientCocycles L _ hI) : (fun g => io L a (c g)) ∈ divisibleCocycles L := by
  refine ⟨hc.1.comp (io L a), fun g h => ?_⟩
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (c g)
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (c h)
  have e : c (g * h) = Submodule.Quotient.mk (s + actT L g t) := by
    rw [hc.2 g h, ← hs, ← ht]; rfl
  show io L a (c (g * h)) = io L a (c g) + actD L g (io L a (c h))
  rw [e, ← hs, ← ht, io_mk L ha, io_mk L ha, io_mk L ha, Submodule.coe_add, smul_add]
  show _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk (A.ρ g (_ • (t : A.V)))
  rw [map_smul]
  rfl

theorem mem_HfQ (L : Lattice (O := O) A.ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (c : G → ↥L.T ⧸ I) :
    c ∈ HfQ PD L I hI ↔ ∃ d : ↥(latticeCocycles L), (d : G → A.V) ∈ latticeFiniteCocycles PD L ∧ c = redT L I d := by
  constructor
  · intro hc
    obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have ht : cob A.ρ (t : A.V) ∈ latticeCocycles L :=
      ⟨coboundary_mem_cocycles A _, fun g _ => L.T.sub_mem (L.stable g _ t.2) t.2⟩
    refine ⟨d + ⟨_, ht⟩, (latticeFiniteCocycles PD L).add_mem hd ⟨ht, coboundary_mem_finite_cocycles PD A _⟩, ?_⟩
    rw [map_add]
    rfl
  · rintro ⟨d, hd, rfl⟩
    exact Submodule.mem_sup_left ⟨d, hd, rfl⟩

theorem mem_HfD (L : Lattice (O := O) A.ρ) (c : G → A.V ⧸ L.T) :
    c ∈ HfD PD L ↔ ∃ b ∈ finiteCocycles PD A.ρ, c = fun g => Submodule.Quotient.mk (b g) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨d + cob A.ρ t, (finiteCocycles PD A.ρ).add_mem hd (coboundary_mem_finite_cocycles PD A _), rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact Submodule.mem_sup_left ⟨d, hd, rfl⟩

theorem mem_HfQ_iff_io (L : Lattice (O := O) A.ρ) {a : O} (ha : a ≠ 0) (hI : StableSub L (aT L a))
    (c : G → ↥L.T ⧸ aT L a) : c ∈ HfQ PD L _ hI ↔ (fun g => io L a (c g)) ∈ HfD PD L := by
  rw [mem_HfQ, mem_HfD]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(algebraMap O LL a)⁻¹ • (d : G → A.V), (finiteCocycles PD A.ρ).smul_mem _ hd.2, ?_⟩
    funext g
    exact io_mk L ha (evT L g d)
  · rintro ⟨b, hb, h⟩
    have key : ∀ g, ∃ t y : ↥L.T, c g = Submodule.Quotient.mk t ∧ a • b g = (t : A.V) - a • (y : A.V) := by
      intro g
      obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (c g)
      have h1 : io L a (c g) = Submodule.Quotient.mk (b g) := congrFun h g
      rw [← ht, io_mk L ha, Submodule.Quotient.eq] at h1
      refine ⟨t, ⟨_, h1⟩, ht.symm, ?_⟩
      show _ = (t : A.V) - a • (_ - b g)
      rw [smul_sub, smul_comm, inv_smul_smul ha, sub_sub_cancel]
    have hab : a • b ∈ finiteCocycles PD A.ρ := ((finiteCocycles PD A.ρ).restrictScalars O).smul_mem a hb
    have hT : a • b ∈ latticeCocycles L := by
      refine ⟨hab.1, fun g _ => ?_⟩
      obtain ⟨t, y, -, e⟩ := key g
      show a • b g ∈ L.T
      rw [e]
      exact L.T.sub_mem t.2 (L.T.smul_mem a y.2)
    refine ⟨⟨_, hT⟩, ⟨hT, hab⟩, ?_⟩
    funext g
    obtain ⟨t, y, hc, e⟩ := key g
    rw [hc]
    refine (Submodule.Quotient.eq _).2 (mem_aT.2 ⟨y, Subtype.ext ?_⟩)
    show (t : A.V) - a • b g = a • (y : A.V)
    rw [e, sub_sub_cancel]

def cupQ (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (a : O) (c : G → ↥LA.T ⧸ aT LA a) (c' : G → ↥LA'.T ⧸ aT LA' a) (x : G × G) : LL :=
  (algebraMap O LL a)⁻¹ * P (liftQ LA _ (c x.1)) (A'.ρ x.1 (liftQ LA' _ (c' x.2)))

variable {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL) {a : O} (ha : a ≠ 0)

include ha in
theorem cupQ_red_left (d : ↥(latticeCocycles LA)) (c' : G → ↥LA'.T ⧸ aT LA' a) (x : G × G) :
    (Submodule.Quotient.mk (cupQ LA LA' P a (redT LA _ d) c' x) : LL ⧸ L1.T) =
      torsionPairing PD hd L1 hL1 (repD LA' x.1 (io LA' a (c' x.2))) (evT LA x.1 d) := by
  obtain ⟨y, hy⟩ := liftQ_mk LA a (evT LA x.1 d)
  show Submodule.Quotient.mk (_ * P (liftQ LA _ (Submodule.Quotient.mk (evT LA x.1 d))) _) =
    Submodule.Quotient.mk (P (evT LA x.1 d : A.V) (A'.ρ x.1 (_ • liftQ LA' _ (c' x.2))))
  rw [hy, Submodule.Quotient.eq, map_smul, map_smul, ← smul_eq_mul, ← LinearMap.smul_apply,
    ← map_smul, smul_add, inv_smul_smul ha, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, add_sub_cancel_left, hL1]
  obtain ⟨z, hz⟩ := (hd.2 _).1 (LA'.stable x.1 _ (liftQ_mem LA' _ (c' x.2))) y y.2
  exact ⟨z, hz.symm⟩

include ha in
theorem cupQ_red_right (c : G → ↥LA.T ⧸ aT LA a) (d' : ↥(latticeCocycles LA')) (x : G × G) :
    (Submodule.Quotient.mk (cupQ LA LA' P a c (redT LA' _ d') x) : LL ⧸ L1.T) =
      torsionPairing PD (isDualLat1_flip PD hd) L1 hL1 (io LA a (c x.1))
        (actT LA' x.1 (evT LA' x.2 d')) := by
  obtain ⟨y, hy⟩ := liftQ_mk LA' a (evT LA' x.2 d')
  show Submodule.Quotient.mk (_ * P _ (A'.ρ x.1 (liftQ LA' _ (Submodule.Quotient.mk (evT LA' x.2 d'))))) =
    Submodule.Quotient.mk (P (_ • liftQ LA _ (c x.1)) (A'.ρ x.1 (evT LA' x.2 d' : A'.V)))
  rw [hy, Submodule.Quotient.eq, map_smul, LinearMap.smul_apply, ← smul_eq_mul, ← map_smul,
    ← map_smul, smul_add, inv_smul_smul ha, map_add, map_add, map_smul, map_smul,
    add_sub_cancel_left, hL1]
  obtain ⟨z, hz⟩ := (hd.2 _).1 (LA'.stable x.1 _ y.2) _ (liftQ_mem LA _ (c x.1))
  exact ⟨z, hz.symm⟩

include hd hL1 ha in

theorem right_half (hO : GoodO (Qp := Qp) LL O) (hB : bkBCore PD) (hA : IsDR PD A.ρ)
    (hI : StableSub LA (aT LA a)) (hI' : StableSub LA' (aT LA' a))
    {c' : G → ↥LA'.T ⧸ aT LA' a} (hc' : c' ∈ quotientCocycles LA' _ hI') :
    c' ∈ HfQ PD LA' _ hI' ↔ ∀ c ∈ HfQ PD LA _ hI, CobO PD L1 (cupQ LA LA' P a c c') := by
  have hz := io_Z1D LA' ha hI' hc'
  have key : ∀ d : ↥(latticeCocycles LA), CobO PD L1 (cupLD LA' P d (fun g => io LA' a (c' g))) ↔
      CobO PD L1 (cupQ LA LA' P a (redT LA _ d) c') := fun d =>
    cobO_congr PD L1 _ _ fun x => by
      rw [cupQ_red_left PD hd L1 hL1 ha]
      exact (congrFun (cup_eq_pairing PD hd L1 hL1 ⟨_, hz⟩ d) x).symm
  rw [mem_HfQ_iff_io PD LA' ha, (hB LL O hO L1 hL1 A A' LA LA' P hA hd).1 _ hz]
  constructor
  · intro h c hc
    obtain ⟨d, hd', rfl⟩ := (mem_HfQ PD LA _ hI c).1 hc
    exact (key d).1 (h _ hd')
  · intro h d hd'
    exact (key ⟨d, hd'.1⟩).2 (h _ ((mem_HfQ PD LA _ hI _).2 ⟨⟨d, hd'.1⟩, hd', rfl⟩))

theorem pair_locConst (hopen : IsOpen (Set.range (algebraMap O LL))) (c : ↥(divisibleCocycles LA'))
    (d : ↥(latticeCocycles LA)) : IsLocallyConstant
      (fun g => torsionPairing PD hd L1 hL1 ((c : G → A'.V ⧸ LA'.T) g) (evT LA g d)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  obtain ⟨U₂, hU₂, hh₀, hc⟩ := (IsLocallyConstant.iff_exists_open _).1 c.2.1 g₀
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ ((c : G → A'.V ⧸ LA'.T) g₀)
  have hcont : Continuous fun g : G => P.flip v ((d : G → A.V) g) :=
    (IsModuleTopology.continuous_of_linearMap (P.flip v)).comp d.2.1.1
  obtain ⟨U₁, hU₁, hg₀, hf⟩ := (IsLocallyConstant.iff_exists_open _).1
    (locConst_mk L1.T (integers_isOpen PD L1 hL1 hopen) _ hcont) g₀
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hg₀, hh₀⟩, ?_⟩
  rintro g ⟨hg, hh⟩
  rw [hc g hh, ← hv]
  exact hf g hg

include hd hL1 ha in

theorem cupQ_flip (hopen : IsOpen (Set.range (algebraMap O LL))) (hI : StableSub LA (aT LA a))
    {c : G → ↥LA.T ⧸ aT LA a} (hc : c ∈ quotientCocycles LA _ hI) (d' : ↥(latticeCocycles LA')) :
    CobO PD L1 (cupQ LA' LA P.flip a (redT LA' _ d') c) ↔
      CobO PD L1 (cupQ LA LA' P a c (redT LA' _ d')) := by
  have hz := io_Z1D LA ha hI hc
  have hfl := isDualLat1_flip PD hd
  have hsum : (fun x => (Submodule.Quotient.mk (cupQ LA' LA P.flip a (redT LA' _ d') c x) :
      LL ⧸ L1.T)) + (fun x => (Submodule.Quotient.mk (cupQ LA LA' P a c (redT LA' _ d') x) :
      LL ⧸ L1.T)) ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
    refine (Submodule.neg_mem_iff _).1
      ⟨_, ⟨pair_locConst PD hfl L1 hL1 hopen ⟨_, hz⟩ d', fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    obtain ⟨g, h⟩ := x
    have e1 : io LA a (c (g * h)) = io LA a (c g) + repD LA g (io LA a (c h)) := hz.2 g h
    show repD L1 g (torsionPairing PD hfl L1 hL1 (io LA a (c h)) (evT LA' h d'))
      - torsionPairing PD hfl L1 hL1 (io LA a (c (g * h))) (evT LA' (g * h) d')
      + torsionPairing PD hfl L1 hL1 (io LA a (c g)) (evT LA' g d') =
      -(Submodule.Quotient.mk (cupQ LA' LA P.flip a (redT LA' _ d') c (g, h)) +
        Submodule.Quotient.mk (cupQ LA LA' P a c (redT LA' _ d') (g, h)))
    rw [cupQ_red_left PD hfl L1 hL1 ha, cupQ_red_right PD hd L1 hL1 ha, ← torsionPairing_equivariant, e1,
      lattice_cocycle_mul]
    simp only [map_add, LinearMap.add_apply]
    abel
  unfold CobO
  constructor
  · intro h
    exact (Submodule.add_mem_iff_right _ h).1 hsum
  · intro h
    exact (Submodule.add_mem_iff_left _ h).1 hsum

end Generic

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem bkC_of_bkB (hB : bkBCore PD) (hD : drDualCore PD) : bkC PD := by
  intro LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' P hA hd ϖ hϖ r hI hI' cup
  obtain ⟨hdom, hdvr, hfr⟩ := hO.1
  haveI := hO.2.2.2.1
  have ha : ϖ ^ r ≠ 0 := pow_ne_zero r hϖ.ne_zero
  have hcup : ∀ c c', cup c c' = cupQ LA LA' P (ϖ ^ r) c c' := fun c c' => by
    funext x
    simp only [cup, cupQ, map_pow, inv_pow]
  simp only [hcup]
  refine ⟨fun c hc => ?_, fun c' hc' => right_half PD hd L1 hL1 ha hO hB hA hI hI' hc'⟩
  rw [right_half PD (isDualLat1_flip PD hd) L1 hL1 ha hO hB (hD LL O hO A A' P hA hd.1) hI' hI hc]
  refine forall₂_congr fun c' hc' => ?_
  obtain ⟨d', -, rfl⟩ := (mem_HfQ PD LA' _ hI' c').1 hc'
  exact cupQ_flip PD hd L1 hL1 ha hO.2.2.2.2 hI hc d'

end Main

theorem main : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), bkACore ((D.loc l).PD K) →
      bkBCore ((D.loc l).PD K) → LocalSituation.bkC ((D.loc l).PD K) :=
  fun _ _ D l _ K _ hB => bkC_of_bkB _ hB (GlobalTheory.TateDualFil.main D l K).1

end GlobalTheory.CompanionTheory.BKTorsion
