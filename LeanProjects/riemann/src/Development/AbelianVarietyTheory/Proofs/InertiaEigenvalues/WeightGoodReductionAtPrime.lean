import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLengthEqAndCardEqPowOfIsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthTorsionByQuotientDivisibleLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenerator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDRAndDdRLeFilZeroOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaTmulOneMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemGKChiPowNeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfLocallyConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroSmulMemOfSpanEqTop

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.TwistTors

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
  [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]

omit [TopologicalSpace Qp] in
theorem actD_mk (T : LocLat G Qp LL O) (g : G) (x : T.V) :
    actD T.L g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T.ρ g x) := rfl

omit [TopologicalSpace Qp] in

theorem lc_mk (T : LocLat G Qp LL O) (hT : IsOpen (T.L.T : Set T.V)) {f : G → T.V}
    (hf : Continuous f) :
    IsLocallyConstant fun g => (Submodule.Quotient.mk (f g) : T.V ⧸ T.L.T) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun h => f h + (-f g)) ⁻¹' (T.L.T : Set T.V),
    hT.preimage (hf.add continuous_const), by simp, fun h hh => ?_⟩
  rw [Submodule.Quotient.eq, sub_eq_add_neg]
  exact hh

omit [TopologicalSpace Qp] in
theorem lc_act (T : LocLat G Qp LL O) (hT : IsOpen (T.L.T : Set T.V)) (w : T.V ⧸ T.L.T) :
    IsLocallyConstant fun g => actD T.L g w := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact lc_mk T hT (T.cont x)

omit [TopologicalSpace Qp] in
theorem actD_one (T : LocLat G Qp LL O) (w : T.V ⧸ T.L.T) : actD T.L 1 w = w := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [actD_mk, map_one]; rfl

omit [TopologicalSpace Qp] in
theorem actD_mul (T : LocLat G Qp LL O) (g h : G) (w : T.V ⧸ T.L.T) :
    actD T.L (g * h) w = actD T.L g (actD T.L h w) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [actD_mk, actD_mk, actD_mk, map_mul]; rfl

omit [TopologicalSpace Qp] in
theorem mem_HfD (T : LocLat G Qp LL O) (c : G → T.V ⧸ T.L.T) :
    c ∈ HfD PD T.L ↔ ∃ z ∈ finiteCocycles PD T.ρ, ∃ x : T.V, ∀ g,
      c g = Submodule.Quotient.mk (z g + (T.ρ g x - x)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨z, hz, x, fun g => rfl⟩
  · rintro ⟨z, hz, x, hc⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk x, rfl⟩, ?_⟩
    funext g
    rw [hc g]; rfl

omit [TopologicalSpace Qp] in
theorem HfD_le (T : LocLat G Qp LL O) (hT : IsOpen (T.L.T : Set T.V)) :
    HfD PD T.L ≤ divisibleCocycles T.L := by
  intro c hc
  obtain ⟨z, hz, x, hc⟩ := (mem_HfD PD T c).1 hc
  obtain rfl : c = _ := funext hc
  refine ⟨lc_mk T hT (hz.1.1.add ?_), fun g h => ?_⟩
  · simp only [sub_eq_add_neg]
    exact (T.cont x).add continuous_const
  · beta_reduce
    rw [actD_mk, ← Submodule.Quotient.mk_add, hz.1.2, map_mul, map_add, map_sub,
      Module.End.mul_apply]
    congr 1
    abel

omit [TopologicalSpace Qp] in
theorem HfD_div [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O) {b : O} (hb : b ≠ 0)
    {c : G → T.V ⧸ T.L.T} (hc : c ∈ HfD PD T.L) : ∃ y ∈ HfD PD T.L, b • y = c := by
  obtain ⟨z, hz, x, hc⟩ := (mem_HfD PD T c).1 hc
  have hb' : algebraMap O LL b ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]
  refine ⟨fun g => Submodule.Quotient.mk (((algebraMap O LL b)⁻¹ • z) g +
    (T.ρ g ((algebraMap O LL b)⁻¹ • x) - (algebraMap O LL b)⁻¹ • x)),
    (mem_HfD PD T _).2 ⟨_, Submodule.smul_mem _ _ hz, _, fun g => rfl⟩, ?_⟩
  funext g
  rw [hc g, Pi.smul_apply, ← Submodule.Quotient.mk_smul, Pi.smul_apply, map_smul, ← smul_sub,
    ← smul_add, ← algebraMap_smul LL b, smul_smul, mul_inv_cancel₀ hb', one_smul]

omit [TopologicalSpace Qp] in
theorem quot_torsion [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O)
    (w : T.V ⧸ T.L.T) : ∃ b : O, b ≠ 0 ∧ b • w = 0 := by
  first
  | exact @_root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion
  | exact _root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion
  | (apply _root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion ..)

omit [TopologicalSpace Qp] in
theorem Z1D_torsion [CompactSpace G] [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O)
    {c : G → T.V ⧸ T.L.T} (hc : c ∈ divisibleCocycles T.L) : ∃ b : O, b ≠ 0 ∧ b • c = 0 := by
  classical
  choose b hb hw using quot_torsion T
  have hfin := hc.1.range_finite
  refine ⟨∏ w ∈ hfin.toFinset, b w, Finset.prod_ne_zero_iff.2 fun w _ => hb w, ?_⟩
  funext g
  obtain ⟨k, hk⟩ : b (c g) ∣ ∏ w ∈ hfin.toFinset, b w :=
    Finset.dvd_prod_of_mem _ (by simp)
  rw [Pi.smul_apply, hk, mul_comm, mul_smul, hw, smul_zero]; rfl

theorem length_le_of_card (O : Type) [CommRing O] [IsLocalRing O] (M N : Type) [AddCommGroup M]
    [Module O M] [Finite M] [AddCommGroup N] [Module O N] [Finite N] (k : ℕ)
    (h : Nat.card M ≤ Nat.card N ^ k) : Module.length O M ≤ (k : ℕ∞) * Module.length O N := by
  obtain ⟨m, hm, hM⟩ := GlobalTheory.exists_length_eq_and_card_eq_pow O M
  obtain ⟨n, hn, hN⟩ := GlobalTheory.exists_length_eq_and_card_eq_pow O N
  rw [hm, hn]
  norm_cast
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact Nat.zero_le _
  have hq0 : Nat.card (IsLocalRing.ResidueField O) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm0.ne'] at hM
    exact Nat.card_pos.ne' hM
  haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero hq0
  have hq : 1 < Nat.card (IsLocalRing.ResidueField O) := Finite.one_lt_card
  rw [hM, hN, ← pow_mul, mul_comm] at h
  exact (Nat.pow_le_pow_iff_right hq).1 h

omit [TopologicalSpace Qp] in

def actTors (T : LocLat G Qp LL O) (a : O) (g : G) :
    ↥(Submodule.torsionBy O (T.V ⧸ T.L.T) a) →+ ↥(Submodule.torsionBy O (T.V ⧸ T.L.T) a) where
  toFun m := ⟨actD T.L g m.1, by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, (Submodule.mem_torsionBy_iff _ _).1 m.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem lc_sub {X Y : Type} [TopologicalSpace X] {p : Y → Prop} {f : X → Subtype p}
    (hf : IsLocallyConstant fun x => (f x).1) : IsLocallyConstant f :=
  IsLocallyConstant.desc f Subtype.val hf Subtype.val_injective

omit [TopologicalSpace Qp] in

def toCoc (T : LocLat G Qp LL O) (a : O) (c : ↥(Submodule.torsionBy O ↥(divisibleCocycles T.L) a)) :
    ↥{c : G → ↥(Submodule.torsionBy O (T.V ⧸ T.L.T) a) |
      IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actTors T a g (c h)} :=
  ⟨fun g => ⟨c.1.1 g, congrFun (congrArg Subtype.val ((Submodule.mem_torsionBy_iff _ _).1 c.2)) g⟩,
    lc_sub c.1.2.1, fun g h => Subtype.ext (c.1.2.2 g h)⟩

omit [TopologicalSpace Qp] in
theorem toCoc_inj (T : LocLat G Qp LL O) (a : O) : Function.Injective (toCoc T a) := by
  intro c c' h
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  exact congrArg Subtype.val (congrFun (congrArg Subtype.val h) g)

theorem len_part [CompactSpace G] (hO : GoodO (Qp := Qp) LL O) (T : LocLat G Qp LL O)
    (h1 : Module.finrank LL T.V = 1) (p r d : ℕ) (ha : (p : O) ^ r ≠ 0)
    [Finite (O ⧸ Ideal.span {(p : O) ^ r})]
    (heul : ∀ (M : Type) [AddCommGroup M] [Finite M] (a : G → M →+ M), (∀ m, a 1 m = m) →
      (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, p ^ r • m = 0) →
      (∀ m, IsLocallyConstant fun g => a g m) →
      {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (d + 2))
    (hne : HfD PD T.L ≠ ⊥) :
    Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology T.L ⧸ divisibleFiniteCohomology PD T.L) ((p : O) ^ r)) ≤
      ((d + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {(p : O) ^ r}) := by
  have hT := GlobalTheory.Cyc.locLat_isOpen hO T
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨-, he⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L h1
  obtain ⟨e⟩ := he _ ha
  haveI : Finite ↥(Submodule.torsionBy O (T.V ⧸ T.L.T) ((p : O) ^ r)) :=
    Finite.of_equiv _ e.toEquiv.symm
  obtain ⟨hfin, hcard⟩ := heul _ (actTors T ((p : O) ^ r))
    (fun m => Subtype.ext (actD_one T m.1)) (fun g h m => Subtype.ext (actD_mul T g h m.1))
    (fun m => Subtype.ext (by
      have := (Submodule.mem_torsionBy_iff _ _).1 m.2
      change p ^ r • m.1 = 0
      rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
      exact this))
    (fun m => lc_sub (lc_act T hT m.1))
  haveI := hfin.to_subtype
  haveI : Finite ↥(Submodule.torsionBy O ↥(divisibleCocycles T.L) ((p : O) ^ r)) :=
    Finite.of_injective _ (toCoc_inj T _)
  let π : ↥(divisibleCocycles T.L) →ₗ[O] (DivisibleCohomology T.L ⧸ divisibleFiniteCohomology PD T.L) :=
    (divisibleFiniteCohomology PD T.L).mkQ ∘ₗ Submodule.mkQ _
  have hπ : ∀ c, π c = 0 ↔ c.1 ∈ HfD PD T.L := by
    intro c
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨c', hc', h⟩
      have h0 : c' - c ∈ (BD T.L).comap (divisibleCocycles T.L).subtype := (Submodule.Quotient.eq _).1 h
      have h2 : c'.1 - c.1 ∈ BD T.L := h0
      have h3 : c'.1 - c.1 ∈ HfD PD T.L := Submodule.mem_sup_right h2
      have := Submodule.sub_mem _ (show c'.1 ∈ HfD PD T.L from hc') h3
      rwa [sub_sub_cancel] at this
    · intro hc
      exact ⟨c, hc, rfl⟩
  refine GlobalTheory.length_torsionBy_quotient_divisible_le O _ _ π
    ((Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)) ?_ ?_ _ ha (d + 1) ?_
  · intro b hb x hx
    obtain ⟨y, hy, h⟩ := HfD_div PD T hb ((hπ x).1 hx)
    exact ⟨⟨y, HfD_le PD T hT hy⟩, (hπ _).2 hy, Subtype.ext h⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨b, hb, h⟩ := Z1D_torsion T (HfD_le PD T hT hx)
    exact ⟨⟨x, HfD_le PD T hT hx⟩, fun h0 => hx0 (congrArg Subtype.val h0), (hπ _).2 hx, b, hb,
      Subtype.ext h⟩
  · refine length_le_of_card O _ _ _ ?_
    rw [← Nat.card_congr e.toEquiv]
    exact (Nat.card_le_card_of_injective _ (toCoc_inj T _)).trans hcard

def toG (T : LocLat G Qp LL O) : GRep G Qp LL O where
  V := T.V
  ρ := T.ρ
  cont := T.cont

omit [TopologicalSpace Qp] in

theorem fixed_points_trivial_of_scalar_action_ne_one (T : LocLat G Qp LL O) (g : G) (u : LL) (hu : u ≠ 1)
    (hg : ∀ x, T.ρ g x = u • x) : H0V T.ρ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h := (Submodule.mem_iInf _).1 hx g
  rw [LinearMap.mem_ker, LinearMap.sub_apply, hg, LinearMap.id_apply] at h
  have h2 : (u - 1) • x = 0 := by rw [sub_smul, one_smul, h]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hu)

theorem BD_ne_bot (hO : GoodO (Qp := Qp) LL O) (T : LocLat G Qp LL O)
    (h1 : Module.finrank LL T.V = 1) (g : G) (u : LL) (hu : u ≠ 1)
    (hg : ∀ x, T.ρ g x = u • x) : BD T.L ≠ ⊥ := by
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ' : algebraMap O LL ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]; exact hϖ.ne_zero
  intro hb
  have hm : (LinearMap.pi fun g => actD T.L g - LinearMap.id)
      (Submodule.Quotient.mk (e ((u - 1)⁻¹ * (algebraMap O LL ϖ)⁻¹))) ∈ BD T.L := ⟨_, rfl⟩
  rw [hb, Submodule.mem_bot] at hm
  have h2 : (Submodule.Quotient.mk (T.ρ g (e ((u - 1)⁻¹ * (algebraMap O LL ϖ)⁻¹)) -
      e ((u - 1)⁻¹ * (algebraMap O LL ϖ)⁻¹)) : T.V ⧸ T.L.T) = 0 := congrFun hm g
  rw [Submodule.Quotient.mk_eq_zero, hg, ← map_smul, ← map_sub, he] at h2
  obtain ⟨a, ha⟩ := h2
  have hu' := sub_ne_zero.2 hu
  have h3 : algebraMap O LL (ϖ * a) = algebraMap O LL 1 := by
    rw [map_mul, ha, map_one, smul_eq_mul]; field_simp
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one a (IsFractionRing.injective O LL h3))

omit [TopologicalSpace Qp] in
theorem HfD_eq_BD (T : LocLat G Qp LL O) (h : finiteCocycles PD T.ρ ≤ B1 T.ρ) : HfD PD T.L = BD T.L := by
  refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨x, rfl⟩ := h hz
  exact ⟨Submodule.Quotient.mk x, rfl⟩

end Abstract

theorem tbe_of (S : Sit) [TopologicalSpace S.Qp] [CompactSpace S.G] [IsTopologicalGroup S.G]
    [IsTopologicalRing S.LL] (hO : GoodO (Qp := S.Qp) S.LL S.O)
    (hfin : ∀ n : ℕ, Finite (S.O ⧸ Ideal.span {((S.PD.p : ℕ) : S.O) ^ n}))
    (hp : ((S.PD.p : ℕ) : S.O) ≠ 0)
    (h5 : TateFilteredInvariants S.PD) (h7 : fontCore S.PD) (hbk : bkADim S.PD)
    (heul : ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : S.G → M →+ M), (∀ m, a 1 m = m) →
      (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, S.PD.p ^ r • m = 0) →
      (∀ m, IsLocallyConstant fun g => a g m) →
      {c : S.G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : S.G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (Module.finrank S.Qp S.K + 2))
    (hchi : ∀ e : ℕ, 0 < e → ∃ g : S.G, (S.PD.χ g : S.Qp) ^ e ≠ 1)
    (φ : S.G) (hφ : (Subgroup.zpowers φ ⊔ S.IK).topologicalClosure = ⊤)
    (δ : S.G → S.LL) (hδ : δ ∈ finiteCocycles S.PD (1 : Representation S.LL S.G S.LL))
    (hδI : ∀ g ∈ S.IK, δ g = 0) (hδ0 : δ ≠ 0) : TBeAt S := by
  intro e Ve h1 hχ
  obtain ⟨hDR, hFil⟩ := GlobalTheory.isDR_and_DdR_le_Fil_zero_of_twist S.PD Ve.ρ e hχ
  have hpos : 0 < e → HfD S.PD Ve.L = BD Ve.L ∧ BD Ve.L ≠ ⊥ := by
    intro he
    obtain ⟨g, hg1⟩ := hchi e he
    have hu : ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e ≠ 1 := by
      rw [inv_pow, Ne, inv_eq_one, ← map_pow, map_eq_one_iff _ (algebraMap S.Qp S.LL).injective]
      exact hg1
    exact ⟨HfD_eq_BD S.PD Ve (GlobalTheory.HfZero.z1f_le_b1 S.PD h5 h7 hO (toG Ve) hDR hFil
      (fixed_points_trivial_of_scalar_action_ne_one Ve _ _ hu (hχ _))), BD_ne_bot hO Ve h1 _ _ hu (hχ _)⟩
  have hzero : e = 0 → HfD S.PD Ve.L ≠ ⊥ ∧ ∀ c : S.G → Ve.V ⧸ Ve.L.T, c ∈ HfD S.PD Ve.L ↔
      (c ∈ divisibleCocycles Ve.L ∧ ∃ x, ∀ g ∈ S.IK, c g = actD Ve.L g x - x) := by
    rintro rfl
    simp only [pow_zero, one_smul] at hχ
    have htop : H0V Ve.ρ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine (Submodule.mem_iInf _).2 fun g => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hχ, LinearMap.id_apply, sub_self]
    have hdim : ((Module.finrank S.LL (FiniteCohomology S.PD Ve.ρ) : ℕ) : ℤ) =
        Module.finrank S.LL ↥(H0V Ve.ρ) + ((Module.finrank S.LL ↥(DdR S.PD Ve.ρ) : ℤ) -
          Module.finrank S.LL ↥(DdR S.PD Ve.ρ ⊓ FilV S.PD (LL := S.LL) (V := Ve.V) 0)) :=
      hbk _ _ hO (toG Ve) hDR
    rw [inf_eq_left.2 hFil, sub_self, add_zero, htop, finrank_top, h1] at hdim
    exact GlobalTheory.UnramifiedClasses.HfD_eq_unramified S.PD hO Ve h1 hχ (by exact_mod_cast hdim) S.IK φ hφ δ hδ hδI hδ0
  refine ⟨fun n => ?_, fun he => (hpos he).1, fun he => (hzero he).2⟩
  have hne : HfD S.PD Ve.L ≠ ⊥ := by
    rcases Nat.eq_zero_or_pos e with he | he
    · exact (hzero he).1
    · rw [(hpos he).1]; exact (hpos he).2
  haveI := hfin n
  haveI : IsDomain S.O := hO.1.1
  have key := len_part S.PD hO Ve h1 S.PD.p n (Module.finrank S.Qp S.K) (pow_ne_zero n hp)
    (heul n) hne
  have hord : Module.length S.O (S.O ⧸ Ideal.span {((S.PD.p : ℕ) : S.O) ^ n}) =
      n • Module.length S.O (S.O ⧸ Ideal.span {((S.PD.p : ℕ) : S.O)}) :=
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hp) n
  unfold lenOl
  rw [Nat.cast_mul, mul_assoc, ← nsmul_eq_mul n, ← hord]
  exact key

theorem exists_unr (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) :
    ∃ δ : ↥(GK K) → ↥LL.1,
    δ ∈ finiteCocycles ((D.loc l).PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) ∧ (∀ g ∈ IK K, δ g = 0) ∧
      δ ≠ 0 := by
  obtain ⟨δ, hδc, hδm, hδI, g₀, hg₀⟩ := GlobalTheory.UnramZl.exists_unramified_character l K
  have hcont : Continuous (algebraMap ℚ_[l] ↥LL.1) :=
    continuous_induced_rng.2 (continuous_algebraMap ℚ_[l] (Om l))
  refine ⟨fun g => algebraMap ℚ_[l] ↥LL.1 (δ g), GlobalTheory.UnramifiedCrys.unramified_mem_Z1f D l K LL _ ?_, ?_, ?_⟩
  · refine ⟨⟨hcont.comp hδc, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · beta_reduce
      rw [hδm, map_add]; rfl
    · beta_reduce
      rw [hδI g hg, map_zero, map_zero, sub_zero]
  · intro g hg
    beta_reduce
    rw [hδI g hg, map_zero]
  · intro h0
    exact hg₀ ((map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective).1 (congrFun h0 g₀))

theorem twist_torsion_facts : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBeAt S := by
  intro D HW F hA hB l _ K s LL h S E
  obtain ⟨-, hA2, -, hA4, hA5, -, hA7, -, -⟩ := hA
  obtain ⟨hO, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  haveI := K.2
  have hc : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  obtain ⟨φ, hφ⟩ := GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K
  obtain ⟨δ, hδ, hδI, hδ0⟩ := exists_unr D l K LL
  have hp : S.PD.p = l := (D.loc l).PD_p K
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  letI : TopologicalSpace S.Qp := (inferInstance : TopologicalSpace ℚ_[l])
  haveI : CompactSpace S.G := hc
  haveI : IsTopologicalGroup S.G := (inferInstance : IsTopologicalGroup ↥(GK K))
  haveI : IsTopologicalRing S.LL := hO.2.2.2.1
  refine tbe_of S hO ?_ ?_ (hA5 l K) (hA7 l K) (hB l K).2.1 ?_ ?_ φ hφ δ hδ hδI hδ0
  · rw [hp]; exact hfin
  · rw [hp]; exact hl0
  · rw [hp]; exact GlobalTheory.CocycleCount.cocycles_finite_ncard_le hA2 hA4 l K
  · intro e he
    obtain ⟨g, hg, hg1⟩ := GlobalTheory.Cyc.exists_mem_GK_chi_pow_ne_one l (D.loc l).χQ (D.loc l).χQ_cyc K e he
    refine ⟨⟨g, hg⟩, ?_⟩
    have := (D.loc l).PD_χ K ⟨g, hg⟩
    change (((D.loc l).PD K).χ ⟨g, hg⟩ : ℚ_[l]) ^ e ≠ 1
    rw [this]
    exact hg1

end GlobalTheory.TwistTors
