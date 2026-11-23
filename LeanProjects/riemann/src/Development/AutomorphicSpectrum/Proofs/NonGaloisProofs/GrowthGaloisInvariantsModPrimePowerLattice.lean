import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemBis
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthOfInvariants

theorem card_quot_pow {O : Type} [CommRing O] [IsDomain O] (ϖ : O) (hϖ : ϖ ≠ 0) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {ϖ ^ n}) = Nat.card (O ⧸ Ideal.span {ϖ}) ^ n := by
  have key : ∀ a : O, Nat.card (O ⧸ Ideal.span {a}) =
      (Submodule.toAddSubgroup (Ideal.span {a} : Ideal O)).index := fun a => rfl
  induction n with
  | zero =>
    have : Subsingleton (O ⧸ Ideal.span {ϖ ^ 0}) := by
      rw [pow_zero, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    simp [Nat.card_of_subsingleton (0 : O ⧸ Ideal.span {ϖ ^ 0})]
  | succ n ih =>
    let f : O →+ O := AddMonoidHom.mulLeft (ϖ ^ n)
    have hle : Submodule.toAddSubgroup (Ideal.span {ϖ ^ (n + 1)} : Ideal O) ≤
        Submodule.toAddSubgroup (Ideal.span {ϖ ^ n} : Ideal O) := by
      intro x hx
      have hx' : x ∈ (Ideal.span {ϖ ^ (n + 1)} : Ideal O) := hx
      change x ∈ (Ideal.span {ϖ ^ n} : Ideal O)
      rw [Ideal.mem_span_singleton] at hx' ⊢
      exact (pow_dvd_pow ϖ (Nat.le_succ n)).trans hx'
    have hrange : f.range = Submodule.toAddSubgroup (Ideal.span {ϖ ^ n} : Ideal O) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        change ϖ ^ n * y ∈ (Ideal.span {ϖ ^ n} : Ideal O)
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      · intro hx
        have hx' : x ∈ (Ideal.span {ϖ ^ n} : Ideal O) := hx
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx'
        exact ⟨y, rfl⟩
    have hcomap : (Submodule.toAddSubgroup (Ideal.span {ϖ ^ (n + 1)} : Ideal O)).comap f =
        Submodule.toAddSubgroup (Ideal.span {ϖ} : Ideal O) := by
      ext x
      change ϖ ^ n * x ∈ (Ideal.span {ϖ ^ (n + 1)} : Ideal O) ↔ x ∈ (Ideal.span {ϖ} : Ideal O)
      rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ]
      exact mul_dvd_mul_iff_left (pow_ne_zero n hϖ)
    have h1 := AddSubgroup.relIndex_mul_index hle
    rw [← hrange, ← AddSubgroup.index_comap, hcomap, hrange, ← key, ← key, ← key, ih] at h1
    rw [← h1, pow_succ, mul_comm]

theorem card_le_of_fibers {Q R E : Type} [AddCommGroup Q] [AddCommGroup E] [Finite R] [Finite E]
    (g : Q → R) (φ : E →+ Q) (hg : ∀ x y, g x = g y → ∃ e, x - y = φ e) :
    Nat.card Q ≤ Nat.card R * Nat.card E := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.range]
  have h2 : Nat.card (Q ⧸ φ.range) ≤ Nat.card R := by
    refine Nat.card_le_card_of_injective (fun u => g u.out) ?_
    intro u v h
    obtain ⟨e, he⟩ := hg _ _ h
    rw [← QuotientAddGroup.out_eq' u, ← QuotientAddGroup.out_eq' v]
    refine (QuotientAddGroup.eq.mpr ?_).symm
    have : -v.out + u.out = φ e := by rw [← he]; abel
    rw [this]
    exact ⟨e, rfl⟩
  have h3 : Nat.card φ.range ≤ Nat.card E :=
    Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact Nat.mul_le_mul h2 h3

theorem finite_quot_smul_top {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] (J : Ideal O) [Finite (O ⧸ J)] :
    Finite (M ⧸ (J • ⊤ : Submodule O M)) := by
  haveI : Module.Finite (O ⧸ J) (M ⧸ (J • ⊤ : Submodule O M)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact Module.finite_of_finite (O ⧸ J)

theorem card_quot_free {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {h : ℕ}
    (e : M ≃ₗ[O] (Fin h → O)) (a : O) :
    Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule O M)) = Nat.card (O ⧸ Ideal.span {a}) ^ h := by
  have hq : (Ideal.span {a} • ⊤ : Submodule O M).map (e : M →ₗ[O] (Fin h → O)) =
      Submodule.pi Set.univ (fun _ => (Ideal.span {a} : Submodule O O)) := by
    rw [Submodule.ideal_span_singleton_smul]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      intro i _
      simp only [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hx
      have hx' : ∀ i, ∃ y, x i = a * y := fun i =>
        Ideal.mem_span_singleton'.mp (hx i (Set.mem_univ i)) |>.imp fun y hy => by
          rw [← hy, mul_comm]
      choose y hy using hx'
      refine ⟨a • e.symm y, ?_, ?_⟩
      · exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨_, trivial, rfl⟩
      · ext i
        simp [hy]
  have e1 := Submodule.Quotient.equiv _ _ e hq
  have e2 := Submodule.quotientPi (fun _ : Fin h => (Ideal.span {a} : Submodule O O))
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]
  simp [Nat.card_pi]

theorem finite_quot_pow {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0)
    (hq : Finite (O ⧸ Ideal.span {ϖ})) (n : ℕ) : Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  have hpos : Nat.card (O ⧸ Ideal.span {ϖ}) ≠ 0 := Nat.card_pos.ne'
  exact Nat.finite_of_card_ne_zero (by rw [card_quot_pow ϖ hϖ n]; exact pow_ne_zero n hpos)

theorem finite_of_torsion {O H : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup H] [Module O H] [Module.Finite O H] {ϖ : O} (hϖ : Irreducible ϖ)
    (hq : Finite (O ⧸ Ideal.span {ϖ})) (R : Submodule O H)
    (hR : ∀ y ∈ R, ∃ a : O, a ≠ 0 ∧ a • y = 0) : Finite R := by
  have hfg : R.FG := IsNoetherian.noetherian R
  have hkill : (∀ y ∈ R, ∃ a : O, a ≠ 0 ∧ a • y = 0) → ∃ a : O, a ≠ 0 ∧ ∀ y ∈ R, a • y = 0 := by
    refine Submodule.fg_induction (motive := fun N _ =>
      (∀ y ∈ N, ∃ a : O, a ≠ 0 ∧ a • y = 0) → ∃ a : O, a ≠ 0 ∧ ∀ y ∈ N, a • y = 0) ?_ ?_ R hfg
    · intro x hx
      obtain ⟨a, ha, hax⟩ := hx x (Submodule.mem_span_singleton_self x)
      refine ⟨a, ha, fun y hy => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [smul_comm, hax, smul_zero]
    · intro N₁ N₂ _ _ h₁ h₂ h
      obtain ⟨a, ha, ha'⟩ := h₁ fun y hy => h y (Submodule.mem_sup_left hy)
      obtain ⟨b, hb, hb'⟩ := h₂ fun y hy => h y (Submodule.mem_sup_right hy)
      refine ⟨a * b, mul_ne_zero ha hb, fun y hy => ?_⟩
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [smul_add, mul_comm, mul_smul, ha' y₁ hy₁, smul_zero, mul_comm, mul_smul, hb' y₂ hy₂,
        smul_zero, add_zero]
  obtain ⟨a, ha, ha'⟩ := hkill hR
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have hJ : (Ideal.span {a} : Ideal O) = Ideal.span {ϖ ^ n} := Ideal.span_singleton_eq_span_singleton.mpr hn
  have hfin : Finite (O ⧸ (Ideal.span {a} : Ideal O)) := by
    rw [hJ]
    exact finite_quot_pow hϖ.ne_zero hq n
  haveI : Module.Finite O R := Module.Finite.iff_fg.mpr hfg
  have hfq := finite_quot_smul_top (M := R) (Ideal.span {a} : Ideal O)
  have hbot : (Ideal.span {a} • ⊤ : Submodule O R) = ⊥ := by
    rw [Submodule.ideal_span_singleton_smul, eq_bot_iff]
    intro y hy
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    simp only [Submodule.mem_bot]
    exact Subtype.ext (ha' z z.2)
  exact Finite.of_equiv _ (Submodule.quotEquivOfEqBot _ hbot).toEquiv

section Rep

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  (A : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ)

theorem smul_eq_zero_of_ne [IsDomain O] [IsFractionRing O LL] {s : O} (hs : s ≠ 0) {x : A.V}
    (h : s • x = 0) : x = 0 := by
  rw [← algebraMap_smul LL s x] at h
  exact (smul_eq_zero.mp h).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr hs)

theorem exists_smul_mem [IsDomain O] [IsFractionRing O LL] (v : A.V) :
    ∃ a : O, a ≠ 0 ∧ a • v ∈ LA.T :=
  by apply _root_.UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem <;> assumption

def fixT : Submodule O ↥LA.T := ((H0V A.ρ).restrictScalars O).comap LA.T.subtype

theorem mem_fixT {m : ↥LA.T} : m ∈ fixT A LA ↔ ∀ g, A.ρ g (m : A.V) = m := by
  change (m : A.V) ∈ H0V A.ρ ↔ _
  simp [H0V, Submodule.mem_iInf, sub_eq_zero]

theorem exists_equiv_fixT [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] :
    Nonempty (↥(fixT A LA) ≃ₗ[O] (Fin (finrank LL ↥(H0V A.ρ)) → O)) := by
  haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.mpr LA.fg
  haveI := LA.free
  obtain ⟨n, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Module.finBasis O ↥LA.T) (fixT A LA)
  let f : ↥(fixT A LA) →ₗ[O] A.V := LA.T.subtype ∘ₗ (fixT A LA).subtype
  let bv : Fin n → A.V := f ∘ b
  have hker : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.mpr (LA.T.injective_subtype.comp (fixT A LA).injective_subtype)
  have hli : LinearIndependent O bv := b.linearIndependent.map' f hker
  have hli' : LinearIndependent LL bv := (LinearIndependent.iff_fractionRing O LL).mp hli
  have hspan : Submodule.span LL (Set.range bv) = H0V A.ρ := by
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact (b i).2
    · intro v hv
      obtain ⟨a, ha, hav⟩ := exists_smul_mem A LA v
      have hm : (⟨a • v, hav⟩ : ↥LA.T) ∈ fixT A LA := ((H0V A.ρ).restrictScalars O).smul_mem a hv
      let m : ↥(fixT A LA) := ⟨⟨a • v, hav⟩, hm⟩
      have h1 : f m ∈ Submodule.span O (Set.range bv) := by
        have := Submodule.mem_map_of_mem (f := f)
          (show m ∈ Submodule.span O (Set.range b) by rw [b.span_eq]; trivial)
        rwa [Submodule.map_span, ← Set.range_comp] at this
      have h2 := Submodule.span_subset_span O LL (Set.range bv) h1
      have ha1 : algebraMap O LL a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr ha
      have h3 : v = (algebraMap O LL a)⁻¹ • f m := by
        change v = (algebraMap O LL a)⁻¹ • (a • v)
        rw [← algebraMap_smul LL a v, smul_smul, inv_mul_cancel₀ ha1, one_smul]
      rw [h3]
      exact Submodule.smul_mem _ _ h2
  have hn : finrank LL ↥(H0V A.ρ) = n := by
    rw [← hspan, finrank_span_eq_card hli', Fintype.card_fin]
  rw [hn]
  exact ⟨b.equivFun⟩

theorem cob_apply (v : A.V) (g : G) : cob A.ρ v g = A.ρ g v - v := rfl

def coW : Submodule O A.V where
  carrier := {v | ∀ g, A.ρ g v - v ∈ LA.T}
  zero_mem' := fun g => by simp
  add_mem' := by
    intro a b ha hb g
    have : A.ρ g (a + b) - (a + b) = (A.ρ g a - a) + (A.ρ g b - b) := by rw [map_add]; abel
    rw [this]
    exact LA.T.add_mem (ha g) (hb g)
  smul_mem' := by
    intro c a ha g
    have : A.ρ g (c • a) - c • a = c • (A.ρ g a - a) := by
      rw [(A.ρ g).map_smul_of_tower, smul_sub]
    rw [this]
    exact LA.T.smul_mem c (ha g)

theorem cob_mem_Z1T (v : A.V) (hv : v ∈ coW A LA) : cob A.ρ v ∈ latticeCocycles LA := by
  refine ⟨⟨?_, ?_⟩, fun g _ => hv g⟩
  · have h : cob A.ρ v = fun g => A.ρ g v + -v := funext fun g => sub_eq_add_neg _ _
    rw [h]
    exact (A.cont v).add continuous_const
  · intro g h
    simp only [cob_apply, map_mul, Module.End.mul_apply, map_sub]
    abel

def cobW : ↥(coW A LA) →ₗ[O] ↥(latticeCocycles LA) where
  toFun v := ⟨cob A.ρ v, cob_mem_Z1T A LA v v.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := by
    refine Subtype.ext (funext fun g => ?_)
    change A.ρ g (c • (a : A.V)) - c • (a : A.V) = c • (A.ρ g a - a)
    rw [(A.ρ g).map_smul_of_tower, smul_sub]

def connW : ↥(coW A LA) →ₗ[O] LatticeCohomology LA := Submodule.mkQ _ ∘ₗ cobW A LA

theorem connW_eq_zero_iff (v : ↥(coW A LA)) :
    connW A LA v = 0 ↔ ∃ u ∈ LA.T, cob A.ρ u = cob A.ρ (v : A.V) := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change cob A.ρ (v : A.V) ∈ latticeCoboundaries LA ↔ _
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, h⟩

theorem finite_range_connW [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (hfin : Module.Finite O (LatticeCohomology LA)) {ϖ : O} (hϖ : Irreducible ϖ)
    (hq : Finite (O ⧸ Ideal.span {ϖ})) : Finite ↥(LinearMap.range (connW A LA)) := by
  refine finite_of_torsion hϖ hq _ ?_
  rintro _ ⟨v, rfl⟩
  obtain ⟨a, ha, hav⟩ := exists_smul_mem A LA (v : A.V)
  refine ⟨a, ha, ?_⟩
  rw [← map_smul, connW_eq_zero_iff]
  exact ⟨_, hav, rfl⟩

theorem mem_span_smul_top {M : Type} [AddCommGroup M] [Module O M] {a : O} {x : M} :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O M) ↔ ∃ y, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro hx
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact ⟨z, rfl⟩
  · rintro ⟨y, rfl⟩
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, trivial, rfl⟩

def fixQ (I : Submodule O ↥LA.T) (hI : StableSub LA I) : Submodule O (↥LA.T ⧸ I) where
  carrier := {x | ∀ g, actQ LA I hI g x = x}
  zero_mem' := fun g => map_zero _
  add_mem' := by
    intro a b ha hb g
    rw [map_add, ha g, hb g]
  smul_mem' := by
    intro c a ha g
    rw [map_smul, ha g]

theorem actT_of_mem_fixT {m : ↥LA.T} (hm : m ∈ fixT A LA) (g : G) : actT LA g m = m :=
  Subtype.ext ((mem_fixT A LA).mp hm g)

def phi0 (I : Submodule O ↥LA.T) (hI : StableSub LA I) : ↥(fixT A LA) →ₗ[O] ↥(fixQ A LA I hI) :=
  LinearMap.codRestrict _ (I.mkQ ∘ₗ (fixT A LA).subtype) fun m g => by
    change I.mkQ (actT LA g m) = I.mkQ m
    rw [actT_of_mem_fixT A LA m.2 g]

theorem quotient_invariant_map_val (I : Submodule O ↥LA.T) (hI : StableSub LA I) (m : ↥(fixT A LA)) :
    ((phi0 A LA I hI m : ↥(fixQ A LA I hI)) : ↥LA.T ⧸ I) = I.mkQ (m : ↥LA.T) := rfl

def phi (a : O) (hI : StableSub LA (Ideal.span {a} • ⊤ : Submodule O ↥LA.T)) :
    (↥(fixT A LA) ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥(fixT A LA))) →ₗ[O] ↥(fixQ A LA _ hI) :=
  Submodule.liftQ _ (phi0 A LA _ hI) (by
    intro m hm
    obtain ⟨y, rfl⟩ := mem_span_smul_top.mp hm
    refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
    rw [quotient_invariant_map_val]
    refine (Submodule.Quotient.mk_eq_zero _).mpr (mem_span_smul_top.mpr ⟨(y : ↥LA.T), rfl⟩))

theorem phi_injective [IsDomain O] [IsFractionRing O LL] {a : O} (ha : a ≠ 0)
    (hI : StableSub LA (Ideal.span {a} • ⊤ : Submodule O ↥LA.T)) :
    Function.Injective (phi A LA a hI) := by
  refine LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ ?_)
  intro m hm
  have h0 : (Submodule.Quotient.mk (m : ↥LA.T) :
      ↥LA.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥LA.T)) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hm)
  obtain ⟨y, hy⟩ := mem_span_smul_top.mp ((Submodule.Quotient.mk_eq_zero _).mp h0)
  have hyf : y ∈ fixT A LA := by
    refine (mem_fixT A LA).mpr fun g => ?_
    have h1 := (mem_fixT A LA).mp m.2 g
    have h2 : ((m : ↥LA.T) : A.V) = a • (y : A.V) := congrArg Subtype.val hy
    rw [h2, (A.ρ g).map_smul_of_tower] at h1
    have h3 : a • (A.ρ g (y : A.V) - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (smul_eq_zero_of_ne A ha h3)
  exact mem_span_smul_top.mpr ⟨⟨y, hyf⟩, Subtype.ext hy⟩

theorem smul_inv_smul_tower [IsDomain O] [IsFractionRing O LL] {a : O} (ha : a ≠ 0) (v : A.V) :
    a • ((algebraMap O LL a)⁻¹ • v) = v := by
  have ha1 : algebraMap O LL a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr ha
  rw [← algebraMap_smul LL a, smul_smul, mul_inv_cancel₀ ha1, one_smul]

theorem inv_smul_smul_tower [IsDomain O] [IsFractionRing O LL] {a : O} (ha : a ≠ 0) (v : A.V) :
    (algebraMap O LL a)⁻¹ • (a • v) = v := by
  have ha1 : algebraMap O LL a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr ha
  rw [← algebraMap_smul LL a, smul_smul, inv_mul_cancel₀ ha1, one_smul]

theorem lift_mem_coW [IsDomain O] [IsFractionRing O LL] {a : O} (ha : a ≠ 0) (t : ↥LA.T)
    (ht : ∀ g, actT LA g t - t ∈ (Ideal.span {a} • ⊤ : Submodule O ↥LA.T)) :
    (algebraMap O LL a)⁻¹ • (t : A.V) ∈ coW A LA := by
  intro g
  obtain ⟨y, hy⟩ := mem_span_smul_top.mp (ht g)
  have h1 : A.ρ g (t : A.V) - t = a • (y : A.V) := congrArg Subtype.val hy
  rw [map_smul, ← smul_sub, h1, inv_smul_smul_tower A ha]
  exact y.2

theorem growth [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (hfin : Module.Finite O (LatticeCohomology LA)) {ϖ : O} (hϖ : Irreducible ϖ)
    (hq : Finite (O ⧸ Ideal.span {ϖ})) :
    ∃ C : ℕ, ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)),
      Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL ↥(H0V A.ρ)) ≤
        Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ∧
      Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ≤
        C * Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
  haveI hR := finite_range_connW A LA hfin hϖ hq
  refine ⟨Nat.card ↥(LinearMap.range (connW A LA)), fun r hI => ?_⟩
  have ha : ϖ ^ r ≠ 0 := pow_ne_zero r hϖ.ne_zero
  obtain ⟨e⟩ := exists_equiv_fixT A LA
  haveI : Finite (O ⧸ (Ideal.span {ϖ ^ r} : Ideal O)) := finite_quot_pow hϖ.ne_zero hq r
  haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.mpr LA.fg
  haveI : Module.Finite O ↥(fixT A LA) := Module.Finite.equiv e.symm
  haveI hTI := finite_quot_smul_top (M := ↥LA.T) (Ideal.span {ϖ ^ r} : Ideal O)
  haveI hE := finite_quot_smul_top (M := ↥(fixT A LA)) (Ideal.span {ϖ ^ r} : Ideal O)
  have hcE : Nat.card (↥(fixT A LA) ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥(fixT A LA))) =
      Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
    rw [card_quot_free e, card_quot_pow ϖ hϖ.ne_zero r, pow_mul]
  have hcQ : Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} =
      Nat.card ↥(fixQ A LA _ hI) := rfl
  rw [hcQ, ← hcE]
  constructor
  · exact Nat.card_le_card_of_injective _ (phi_injective A LA ha hI)
  · let I : Submodule O ↥LA.T := Ideal.span {ϖ ^ r} • ⊤
    let sec : (↥LA.T ⧸ I) → ↥LA.T := Function.surjInv (Submodule.mkQ_surjective I)
    have hsec : ∀ y, I.mkQ (sec y) = y := Function.surjInv_eq _
    have hlift : ∀ x : ↥(fixQ A LA I hI), ∀ g, actT LA g (sec x) - sec x ∈ I := by
      intro x g
      have h1 : actQ LA I hI g (x : ↥LA.T ⧸ I) = x := x.2 g
      have h2 : (Submodule.Quotient.mk (actT LA g (sec x)) : ↥LA.T ⧸ I) =
          Submodule.Quotient.mk (sec x) := by
        change actQ LA I hI g (I.mkQ (sec x)) = I.mkQ (sec x)
        rw [hsec]
        exact h1
      exact (Submodule.Quotient.eq I).mp h2
    let w : ↥(fixQ A LA I hI) → ↥(coW A LA) := fun x =>
      ⟨(algebraMap O LL (ϖ ^ r))⁻¹ • ((sec x : ↥LA.T) : A.V), lift_mem_coW A LA ha _ (hlift x)⟩
    refine card_le_of_fibers (fun x => (connW A LA).rangeRestrict (w x)) (phi A LA _ hI).toAddMonoidHom ?_
    intro x y hxy
    have h1 : connW A LA (w x - w y) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val hxy
    obtain ⟨u, hu, hcu⟩ := (connW_eq_zero_iff A LA _).mp h1
    let m0 : ↥LA.T := sec x - sec y - (ϖ ^ r) • (⟨u, hu⟩ : ↥LA.T)
    have hz : (m0 : A.V) = (ϖ ^ r) • (((w x : A.V) - (w y : A.V)) - u) := by
      change ((sec x : ↥LA.T) : A.V) - ((sec y : ↥LA.T) : A.V) - (ϖ ^ r) • u = _
      rw [smul_sub, smul_sub]
      change _ = (ϖ ^ r) • ((algebraMap O LL (ϖ ^ r))⁻¹ • ((sec x : ↥LA.T) : A.V)) -
        (ϖ ^ r) • ((algebraMap O LL (ϖ ^ r))⁻¹ • ((sec y : ↥LA.T) : A.V)) - _
      rw [smul_inv_smul_tower A ha, smul_inv_smul_tower A ha]
    have hm0 : m0 ∈ fixT A LA := by
      refine (mem_fixT A LA).mpr fun g => ?_
      have h2 : A.ρ g u - u = A.ρ g ((w x : A.V) - (w y : A.V)) - ((w x : A.V) - (w y : A.V)) :=
        congrFun hcu g
      have h3 : A.ρ g (((w x : A.V) - (w y : A.V)) - u) = ((w x : A.V) - (w y : A.V)) - u := by
        rw [sub_eq_sub_iff_add_eq_add] at h2
        rw [map_sub (A.ρ g), sub_eq_sub_iff_add_eq_add, ← h2, add_comm]
      rw [hz, (A.ρ g).map_smul_of_tower, h3]
    refine ⟨Submodule.Quotient.mk ⟨m0, hm0⟩, Subtype.ext ?_⟩
    change (x : ↥LA.T ⧸ I) - y = I.mkQ m0
    have h4 : I.mkQ ((ϖ ^ r) • (⟨u, hu⟩ : ↥LA.T)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (mem_span_smul_top.mpr ⟨_, rfl⟩)
    change _ = I.mkQ (sec x - sec y - (ϖ ^ r) • (⟨u, hu⟩ : ↥LA.T))
    rw [map_sub, map_sub, h4, hsec, hsec, sub_zero]

end Rep

theorem growth_galois_invariants_mod_prime_power_lattice_alt : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), TateFiniteness ((D.loc l).PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∃ C : ℕ, ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL ↥(H0V A.ρ)) ≤ Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ∧ Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ≤ C * Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
  intro D l _ K hcore LL _ _ _ O _ _ hG A LA ϖ hϖ
  obtain ⟨⟨hO, hD, hF⟩, -⟩ := id hG
  haveI := hO
  haveI := hD
  haveI := hF
  exact growth A LA (hcore LL O hG A LA) hϖ (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ).2.1

end GlobalTheory.CompanionTheory.GrowthOfInvariants
