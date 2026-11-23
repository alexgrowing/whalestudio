import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenerator

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.UnramifiedClasses

theorem eq_zero_of_locallyConstant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type} [AddCommGroup A] (I : Subgroup G) (φ : G)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤) (c : G → A)
    (hlc : IsLocallyConstant c) (hc : ∀ g h, c (g * h) = c g + c h) (hφ : c φ = 0)
    (hI : ∀ g ∈ I, c g = 0) (g : G) : c g = 0 := by
  have h1 : c 1 = 0 := by
    have := hc 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  let H : Subgroup G :=
    { carrier := {g | c g = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hc, ha, hb, add_zero]
      one_mem' := h1
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have := hc a a⁻¹
        rw [mul_inv_cancel, h1, ha, zero_add] at this
        exact this.symm }
  have hle : Subgroup.zpowers φ ⊔ I ≤ H :=
    sup_le ((Subgroup.zpowers_le (G := G)).mpr hφ) (fun g hg => hI g hg)
  have hcl : (Subgroup.zpowers φ ⊔ I).topologicalClosure ≤ H :=
    Subgroup.topologicalClosure_minimal _ hle (hlc.isClosed_fiber 0)
  rw [hgen] at hcl
  exact hcl (Subgroup.mem_top g)

theorem isLocallyConstant_mkQ {X : Type} [TopologicalSpace X] {O V : Type} [CommRing O]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [ContinuousAdd V] (T : Submodule O V)
    (hT : IsOpen (T : Set V)) (f : X → V) (hf : Continuous f) :
    IsLocallyConstant (fun x => T.mkQ (f x)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => f y + (-f x)) ⁻¹' (T : Set V),
    hT.preimage (hf.add continuous_const), by simp, fun y hy => ?_⟩
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, sub_eq_add_neg]
  exact hy

theorem exists_not_mem_range {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL] :
    ∃ y : LL, y ∉ Set.range (algebraMap O LL) := by
  by_contra h
  push Not at h
  apply IsDiscreteValuationRing.not_isField O
  exact (RingEquiv.ofBijective (algebraMap O LL)
    ⟨IsFractionRing.injective O LL, h⟩).toMulEquiv.isField (Field.toIsField LL)

theorem HfD_eq_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [IsTopologicalGroup G] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsTopologicalRing LL], GoodO (Qp := Qp) LL O → ∀ (T : LocLat G Qp LL O), Module.finrank LL T.V = 1 → (∀ g x, T.ρ g x = x) → Module.finrank LL (FiniteCohomology PD T.ρ) = 1 → ∀ (I : Subgroup G) (φ : G), (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤ → ∀ δ : G → LL, δ ∈ finiteCocycles PD (1 : Representation LL G LL) → (∀ g ∈ I, δ g = 0) → δ ≠ 0 → HfD PD T.L ≠ ⊥ ∧ ∀ c : G → T.V ⧸ T.L.T, c ∈ HfD PD T.L ↔ (c ∈ divisibleCocycles T.L ∧ ∃ x, ∀ g ∈ I, c g = actD T.L g x - x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ _ LL _ _ _ O _ _ _ hO T hV hρ
    hH I φ hgen δ hδ hδI hδ0
  have hopen := GlobalTheory.Cyc.locLat_isOpen hO T
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L hV
  obtain ⟨y₀, hy₀⟩ := exists_not_mem_range (O := O) (LL := LL)
  obtain ⟨⟨hδc, hδh⟩, x₀, hx₀⟩ := hδ
  have hδadd : ∀ g h, δ (g * h) = δ g + δ h := fun g h => by simpa using hδh g h
  have hact : ∀ g (x : T.V ⧸ T.L.T), actD T.L g x = x := by
    intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg (Submodule.Quotient.mk (p := T.L.T)) (hρ g x)
  have hBD : BD T.L = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [hact]
  have hB1 : B1 T.ρ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob, hρ]
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hc₀c : Continuous fun g => e (δ g) := by
    have : (fun g => e (δ g)) = fun g => δ g • e 1 := by
      funext g
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [this]
    exact hδc.smul continuous_const
  have hc₀ : (fun g => e (δ g)) ∈ finiteCocycles PD T.ρ := by
    let m := AlgebraTensorModule.map (e : LL →ₗ[LL] T.V) (LinearMap.id : B →ₗ[Qp] B)
    have hm : ∀ g y, m (actVB PD (1 : Representation LL G LL) g y) = actVB PD T.ρ g (m y) := by
      intro g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m, actVB, hρ]
      | add a b ha hb => simp only [map_add, ha, hb]
    refine ⟨⟨hc₀c, fun g h => by simp only [hδadd, map_add, hρ]⟩, m x₀, fun g => ?_⟩
    have := congrArg m (hx₀ g)
    simp only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this
    rw [← hm]
    exact this
  obtain ⟨g₀, hg₀⟩ : ∃ g, δ g ≠ 0 := Function.ne_iff.mp hδ0
  have hdim : Module.finrank LL ↥(finiteCocycles PD T.ρ) = 1 := by
    rw [← hH]
    refine (Submodule.quotEquivOfEqBot _ ?_).finrank_eq.symm
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  have hspan : ∀ z ∈ finiteCocycles PD T.ρ, ∃ a : LL, ∀ g, z g = e (a * δ g) := by
    intro z hz
    have hne : (⟨_, hc₀⟩ : ↥(finiteCocycles PD T.ρ)) ≠ 0 := by
      intro h
      have := congrFun (congrArg Subtype.val h) g₀
      exact hg₀ (by simpa using this)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hz⟩
    refine ⟨a, fun g => ?_⟩
    have := congrFun (congrArg Subtype.val ha) g
    rw [← smul_eq_mul, map_smul]
    exact this.symm

  let r : LL → G → T.V ⧸ T.L.T := fun a g => T.L.T.mkQ (e (a * δ g))
  have hHf : ∀ c, c ∈ HfD PD T.L ↔ ∃ a, c = r a := by
    intro c
    unfold HfD
    rw [hBD, sup_bot_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha⟩ := hspan z hz
      exact ⟨a, funext fun g => by simp [r, ha]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨a • fun g => e (δ g), (finiteCocycles PD T.ρ).smul_mem a hc₀, ?_⟩
      funext g
      simp [r, ← map_smul]
  have hrlc : ∀ a, IsLocallyConstant (r a) := fun a => by
    refine isLocallyConstant_mkQ T.L.T hopen (fun g => e (a * δ g)) ?_
    have : (fun g => e (a * δ g)) = fun g => a • e (δ g) := by
      funext g
      rw [← map_smul, smul_eq_mul]
    rw [this]
    exact hc₀c.const_smul a
  have hradd : ∀ a g h, r a (g * h) = r a g + r a h := fun a g h => by
    simp only [r, hδadd, mul_add, map_add]
  have hrI : ∀ a, ∀ g ∈ I, r a g = 0 := fun a g hg => by
    simp only [r, hδI g hg, mul_zero, map_zero]
  have hr₀ : r (y₀ / δ g₀) g₀ ≠ 0 := by
    intro h
    simp only [r, div_mul_cancel₀ _ hg₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact hy₀ ((he _).mp h)
  have hφ : δ φ ≠ 0 := by
    intro h
    exact hr₀ (eq_zero_of_locallyConstant I φ hgen _ (hrlc _) (hradd _)
      (by simp only [r, h, mul_zero, map_zero]) (hrI _) g₀)
  refine ⟨fun h => ?_, fun c => ?_⟩
  · have : r (y₀ / δ g₀) ∈ HfD PD T.L := (hHf _).mpr ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hr₀ (congrFun this g₀)
  · rw [hHf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨hrlc a, fun g h => by rw [hact, hradd]⟩, 0, fun g hg => by
        rw [hrI a g hg, hact, sub_zero]⟩
    · rintro ⟨⟨hlc, hcoc⟩, x, hx⟩
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (c φ)
      refine ⟨e.symm v / δ φ, funext fun g => sub_eq_zero.mp ?_⟩
      refine eq_zero_of_locallyConstant I φ hgen (fun g => c g - r (e.symm v / δ φ) g)
        (hlc.sub (hrlc _)) (fun g h => ?_) ?_ (fun g hg => ?_) g
      · simp only [hcoc, hact, hradd]
        abel
      · simp only [r, div_mul_cancel₀ _ hφ, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, hv,
          sub_self]
      · simp only [hx g hg, hact, hrI _ g hg, sub_self]

end GlobalTheory.UnramifiedClasses
