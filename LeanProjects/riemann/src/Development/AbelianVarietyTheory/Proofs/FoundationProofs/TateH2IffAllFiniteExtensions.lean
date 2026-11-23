import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TateLocalDualityTopDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow

noncomputable section

namespace GlobalTheory.TateTopCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo

section Transport

variable {O O' G M M' : Type} [CommRing O] [CommRing O'] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O' M']
  {σ : O →+* O'} {σ' : O' →+* O} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (π : Representation O G M) (ρ : Representation O' G M') (e : M ≃ₛₗ[σ] M')

def postEquiv (X : Type) : (X → M) ≃ₛₗ[σ] (X → M') where
  toFun c := fun x => e (c x)
  invFun c := fun x => e.symm (c x)
  map_add' a b := by funext x; simp
  map_smul' a c := by funext x; simp [LinearEquiv.map_smulₛₗ]
  left_inv c := by funext x; simp
  right_inv c := by funext x; simp

theorem locallyConstant_iff {X : Type} [TopologicalSpace X] (c : X → M) :
    IsLocallyConstant c ↔ Continuous (postEquiv e X c) := by
  rw [← IsLocallyConstant.iff_continuous]
  exact ⟨fun h => h.comp e, fun h => by
    simpa [postEquiv, Function.comp_def] using h.comp e.symm⟩

variable (he : ∀ g x, e (π g x) = ρ g (e x))
include he

theorem mem_Z2_iff (c : G × G → M) :
    c ∈ ReciprocityTheory.Def.Z2 π ⊤ ↔ postEquiv e (G × G) c ∈ ReciprocityTheory.Gal.Z2 ρ := by
  rw [ReciprocityTheory.Gal.mem_cocycles2, ← locallyConstant_iff]
  have key : ∀ g h k, ρ g (postEquiv e (G × G) c (h, k)) - postEquiv e (G × G) c (g * h, k) +
      postEquiv e (G × G) c (g, h * k) - postEquiv e (G × G) c (g, h) =
      e (ReciprocityTheory.Def.d2 π c (g, h, k)) := by
    intro g h k
    simp [postEquiv, ReciprocityTheory.Def.d2, he]
  simp only [key, e.map_eq_zero_iff]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, fun g h k => congrFun (LinearMap.mem_ker.1 h2) (g, h, k)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun _ => trivial⟩, LinearMap.mem_ker.2 (funext fun x => h2 x.1 x.2.1 x.2.2)⟩

omit [TopologicalSpace G] [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalAddGroup M']
  [ContinuousConstSMul O' M'] in
theorem post_equiv_coboundary_one (c : G → M) :
    postEquiv e (G × G) (ReciprocityTheory.Def.d1 π c) = ReciprocityTheory.Gal.d1 ρ (postEquiv e G c) := by
  funext x
  simp [postEquiv, ReciprocityTheory.Def.d1, ReciprocityTheory.Gal.d1, he]

theorem mem_B2_iff (c : G × G → M) :
    c ∈ ReciprocityTheory.Def.B2 π ⊤ ↔ postEquiv e (G × G) c ∈ ReciprocityTheory.Gal.B2 ρ := by
  rw [ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]
  constructor
  · rintro ⟨f, ⟨hf, -⟩, rfl⟩
    exact ⟨postEquiv e G f, (locallyConstant_iff e f).1 hf, (post_equiv_coboundary_one π ρ e he f).symm⟩
  · rintro ⟨f, hf, h⟩
    obtain ⟨f, rfl⟩ := (postEquiv e G).surjective f
    refine ⟨f, ⟨(locallyConstant_iff e f).2 hf, fun _ => trivial⟩, ?_⟩
    rw [← post_equiv_coboundary_one π ρ e he] at h
    exact (postEquiv e (G × G)).injective h

def twoCocycleMap : ↥(ReciprocityTheory.Def.Z2 π ⊤) →ₛₗ[σ] ↥(ReciprocityTheory.Gal.Z2 ρ) where
  toFun c := ⟨postEquiv e (G × G) c.1, (mem_Z2_iff π ρ e he c.1).1 c.2⟩
  map_add' a b := Subtype.ext (map_add (postEquiv e (G × G)) a.1 b.1)
  map_smul' a c := Subtype.ext ((postEquiv e (G × G)).map_smulₛₗ a c.1)

def h2CohomologyMap : ReciprocityTheory.Def.H2 π ⊤ →ₛₗ[σ] ReciprocityTheory.Gal.H2 ρ :=
  Submodule.mapQ _ _ (twoCocycleMap π ρ e he) fun c hc => (mem_B2_iff π ρ e he c.1).1 hc

theorem h2CohomologyMap_bijective : Function.Bijective (h2CohomologyMap π ρ e he) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.Quotient.mk_eq_zero]
    have h1 : (Submodule.Quotient.mk (twoCocycleMap π ρ e he c) : ReciprocityTheory.Gal.H2 ρ) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1
    exact (mem_B2_iff π ρ e he c.1).2 h1
  · intro y
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨c, rfl⟩ := (postEquiv e (G × G)).surjective c
    exact ⟨Submodule.Quotient.mk ⟨c, (mem_Z2_iff π ρ e he c).2 hc⟩, rfl⟩

def h2EquivOfOrderTwo : ReciprocityTheory.Def.H2 π ⊤ ≃ₛₗ[σ] ReciprocityTheory.Gal.H2 ρ :=
  LinearEquiv.ofBijective (h2CohomologyMap π ρ e he) (h2CohomologyMap_bijective π ρ e he)

theorem nonempty_iff :
    Nonempty (ReciprocityTheory.Def.H2 π ⊤ ≃ₗ[O] M) ↔ H2IsoCoefficients ρ := by
  haveI : RingHomCompTriple σ' σ (RingHom.id O') := ⟨RingHomInvPair.comp_eq₂⟩
  haveI : RingHomCompTriple σ σ' (RingHom.id O) := ⟨RingHomInvPair.comp_eq⟩
  constructor
  · rintro ⟨f⟩
    exact ⟨((h2EquivOfOrderTwo π ρ e he).symm.trans f).trans e⟩
  · rintro ⟨f⟩
    exact ⟨((h2EquivOfOrderTwo π ρ e he).trans f).trans e.symm⟩

end Transport

section Integers

variable {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [CommRing O] [Algebra O LL]

theorem mem_range_of_norm_le (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) (hx : ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1) :
    x ∈ Set.range (algebraMap O LL) := by
  obtain ⟨⟨hO, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := h
  obtain ⟨-, -, hmt', -, -⟩ := (GlobalTheory.LocalIntegers.good_integers l L').1
  have hcont : Continuous φ.symm :=
    IsModuleTopology.continuous_of_linearMap φ.symm.toLinearEquiv.toLinearMap
  have hU : IsOpen (φ.symm ⁻¹' Set.range (algebraMap O LL)) := hop.preimage hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 ⟨0, by simp⟩
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt ℚ_[l] hε
  have hc0' : c ≠ 0 := norm_pos_iff.1 hc0
  have hk : ∀ k : ℕ, ∃ b : O, algebraMap O LL b = algebraMap ℚ_[l] LL c * x ^ k := by
    intro k
    have : φ (algebraMap ℚ_[l] LL c * x ^ k) ∈ Metric.ball (0 : ↥L'.1) ε := by
      rw [mem_ball_zero_iff]
      change ‖((φ (algebraMap ℚ_[l] LL c * x ^ k) : ↥L'.1) : Om l)‖ < ε
      rw [map_mul, map_pow, AlgEquiv.commutes]
      push_cast
      rw [norm_mul, norm_pow]
      have h1 : ‖((algebraMap ℚ_[l] ↥L'.1 c : ↥L'.1) : Om l)‖ = ‖c‖ := PadicAlgCl.norm_extends l c
      calc _ ≤ ‖c‖ * 1 := by
            gcongr
            · exact h1.le
            · exact pow_le_one₀ (norm_nonneg _) hx
        _ < ε := by simpa using hc
    simpa using hball this
  rcases ValuationRing.isInteger_or_isInteger O x with h | ⟨y, hy⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  by_cases hu : IsUnit y
  · obtain ⟨z, hz⟩ := hu.exists_right_inv
    refine ⟨z, ?_⟩
    have := congrArg (algebraMap O LL) hz
    rw [map_mul, hy, map_one] at this
    field_simp at this
    exact this
  · exfalso
    obtain ⟨a, ha⟩ := hk 0
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hc0' (by simpa using ha.symm)
    obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hu ha0
    obtain ⟨b, hb⟩ := hk (n + 1)
    refine hn ⟨b, IsFractionRing.injective O LL ?_⟩
    rw [map_mul, map_pow, hy, hb, ha, inv_pow]
    field_simp

theorem mem_range_iff (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) :
    x ∈ Set.range (algebraMap O LL) ↔ φ x ∈ OL L' := by
  have hO : φ x ∈ OL L' ↔ ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1 := mem_integralClosure_padicInt_iff L'.1 _
  rw [hO]
  refine ⟨?_, mem_range_of_norm_le h L' φ x⟩
  rintro ⟨a, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  have hsurj : Function.Surjective (algebraMap O LL) := by
    intro w
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖((φ w : ↥L'.1) : Om l)‖ hlt
    have hpos : 0 < ‖((φ (algebraMap O LL a) : ↥L'.1) : Om l)‖ ^ k := by positivity
    have ha : algebraMap O LL a ≠ 0 := by
      intro h0
      rw [h0] at hlt
      norm_num at hlt
    obtain ⟨b, hb⟩ := mem_range_of_norm_le h L' φ (w / algebraMap O LL a ^ k) (by
      rw [map_div₀, map_pow]
      push_cast
      rw [norm_div, norm_pow, div_le_one hpos]
      exact hk.le)
    exact ⟨b * a ^ k, by rw [map_mul, map_pow, hb]; field_simp⟩
  obtain ⟨⟨hO, hdvr, hfr⟩, -⟩ := h
  exact IsDiscreteValuationRing.not_isField O
    ((RingEquiv.ofBijective (algebraMap O LL)
      ⟨IsFractionRing.injective O LL, hsurj⟩).toMulEquiv.isField (Field.toIsField LL))

theorem exists_finExt (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ L' : FinExt l, Nonempty (LL ≃ₐ[ℚ_[l]] ↥L'.1) := by
  let ψ : LL →ₐ[ℚ_[l]] Om l := IsAlgClosed.lift
  exact ⟨⟨ψ.fieldRange, (AlgEquiv.ofInjectiveField ψ).toLinearEquiv.finiteDimensional⟩,
    ⟨AlgEquiv.ofInjectiveField ψ⟩⟩

end Integers

section Quotients

variable {G LL O LL' O' M' : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O]
  [Algebra O LL] [Field LL'] [CommRing O'] [Algebra O' LL'] [AddCommGroup M'] [Module O' M']
  [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalAddGroup M']
  [ContinuousConstSMul O' M']

theorem nonempty_iff_of_ringEquiv (hinj : Function.Injective (algebraMap O LL))
    (hinj' : Function.Injective (algebraMap O' LL')) (φ : LL ≃+* LL')
    (hφ : ∀ x, x ∈ Set.range (algebraMap O LL) ↔ φ x ∈ Set.range (algebraMap O' LL'))
    (T : Submodule O LL) (hT : T = LinearMap.range (Algebra.linearMap O LL))
    (m : LL' →+ M') (hm : Function.Surjective m)
    (hker : ∀ y, m y = 0 ↔ y ∈ Set.range (algebraMap O' LL'))
    (hsmul : ∀ a y, m (algebraMap O' LL' a * y) = a • m y)
    (π : Representation O G (LL ⧸ T)) (ρ : Representation O' G M') (χ : G → LL)
    (hπ : ∀ g x, π g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (χ g * x))
    (hρ : ∀ g y, ρ g (m y) = m (φ (χ g) * y)) :
    Nonempty (ReciprocityTheory.Def.H2 π ⊤ ≃ₗ[O] (LL ⧸ T)) ↔ H2IsoCoefficients ρ := by
  let e₁ := RingEquiv.ofBijective (algebraMap O LL).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap O LL).rangeRestrict_surjective⟩
  let e₂ := RingEquiv.ofBijective (algebraMap O' LL').rangeRestrict
    ⟨fun a b h => hinj' (congrArg Subtype.val h), (algebraMap O' LL').rangeRestrict_surjective⟩
  let e₃ : ↥(algebraMap O LL).range ≃+* ↥(algebraMap O' LL').range :=
    φ.restrict _ _ fun x => hφ x
  let σ : O ≃+* O' := (e₁.trans e₃).trans e₂.symm
  have hσ : ∀ a, algebraMap O' LL' (σ a) = φ (algebraMap O LL a) := fun a =>
    congrArg Subtype.val (e₂.apply_symm_apply (e₃ (e₁ a)))
  clear_value σ
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let f : LL →ₛₗ[(σ : O →+* O')] M' :=
    { toFun := fun x => m (φ x)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun a x => by
        rw [Algebra.smul_def, map_mul, ← hσ, hsmul]
        rfl }
  have hmem : ∀ x, x ∈ T ↔ f x = 0 := fun x => by
    rw [hT]
    exact (hφ x).trans (hker _).symm
  let q : (LL ⧸ T) →ₛₗ[(σ : O →+* O')] M' := T.liftQ f fun x hx => (hmem x).1 hx
  have hq : ∀ x, q (Submodule.Quotient.mk x) = m (φ x) := fun _ => rfl
  have hqb : Function.Bijective q := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero, hmem]
      exact hx
    · intro y
      obtain ⟨y, rfl⟩ := hm y
      obtain ⟨y, rfl⟩ := φ.surjective y
      exact ⟨Submodule.Quotient.mk y, rfl⟩
  refine nonempty_iff π ρ (LinearEquiv.ofBijective q hqb) ?_
  intro g x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change q (π g (Submodule.Quotient.mk x)) = ρ g (q (Submodule.Quotient.mk x))
  rw [hπ, hq, hq, hρ, map_mul]

omit [TopologicalSpace G] in

def rangeLattice (hinj : Function.Injective (algebraMap O LL)) (χ : G →* LLˣ)
    (hχ : ∀ g, ((χ g : LLˣ) : LL) ∈ Set.range (algebraMap O LL)) :
    Lattice (O := O) (charRep χ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hχ g
    exact ⟨a * y, by simp [charRep, ha]⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have : (1 : LL) ∈ Submodule.span LL ((LinearMap.range (Algebra.linearMap O LL) :
        Submodule O LL) : Set LL) := Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x this

end Quotients

section Compare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

theorem clause_iff {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL]
    (hinj : Function.Injective (algebraMap O LL)) (L' : FinExt l) (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1)
    (hφ : ∀ x, x ∈ Set.range (algebraMap O LL) ↔ φ x ∈ OL L')
    (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)))
    (hL : L1.T = LinearMap.range (Algebra.linearMap O LL)) :
    Nonempty (ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] (LL ⧸ L1.T)) ↔ TateLocalDualityDegreeTwoAt P K L' := by
  refine nonempty_iff_of_ringEquiv (O' := ↥(OL L')) hinj Subtype.val_injective φ.toRingEquiv
    (fun x => (hφ x).trans ⟨fun h => ⟨⟨_, h⟩, rfl⟩, by rintro ⟨y, hy⟩; exact hy ▸ y.2⟩) L1.T hL
    (FracModInt.mk L').toAddMonoidHom (Submodule.Quotient.mk_surjective (intSub L'))
    (fun y => Submodule.Quotient.mk_eq_zero (intSub L'))
    (fun a y => (FracModInt.mk L').map_smul a y) (repD L1) (fracModIntTwist P K L')
    (fun g => ((cycLL (P.PD K) LL g : LLˣ) : LL)) (fun g x => rfl) fun g y => ?_
  refine (fracModIntTwist_mk P K L' g y).trans ?_
  exact congrArg (fun t => FracModInt.mk L' (t * y)) (φ.commutes _).symm

def Clause (LL O : Type) [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL] : Prop :=
  ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
      Nonempty (ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] (LL ⧸ L1.T))

theorem tate_h2_iff_clause : LocalTateTopDegree (P.PD K) ↔
    ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → Clause P K LL O := Iff.rfl

def CoreClause (LL : FinExt l) : Prop := Clause P K ↥LL.1 ↥(OL LL)

def intLattice (LL : FinExt l) :=
  rangeLattice (O := ↥(OL LL)) Subtype.val_injective (cycLL (P.PD K) ↥LL.1)
    fun g => ⟨algebraMap ℤ_[l] ↥(OL LL) (chiInt P K g), rfl⟩

theorem coreClause_iff (LL : FinExt l) : CoreClause P K LL ↔ TateLocalDualityDegreeTwoAt P K LL := by
  have h := clause_iff P K (O := ↥(OL LL)) Subtype.val_injective LL AlgEquiv.refl
    fun x => ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  exact ⟨fun H => (h _ rfl).1 (H (intLattice P K LL) rfl), fun H L1 hL => (h L1 hL).2 H⟩

theorem tate_h2_iff_finite_extensions : LocalTateTopDegree (P.PD K) ↔ ∀ LL : FinExt l, TateLocalDualityDegreeTwoAt P K LL := by
  constructor
  · intro h LL
    exact (coreClause_iff P K LL).1
      (h ↥LL.1 ↥(OL LL) (GlobalTheory.LocalIntegers.good_integers l LL).1)
  · intro h LL _ _ _ O _ _ hO L1 hL
    haveI := hO.2.1
    obtain ⟨L', ⟨φ⟩⟩ := exists_finExt (l := l) LL
    obtain ⟨_, -, hfr⟩ := hO.1
    exact (clause_iff P K (IsFractionRing.injective O LL) L' φ (mem_range_iff hO L' φ) L1 hL).2
      (h L')

end Compare

theorem tate_h2_iff_all_finite_extensions (D : D7) : Formalism.MainNotions.LocalSituation.adm3 D ↔ TateLocalDualityDegreeTwoAll D :=
  forall_congr' fun l => forall_congr' fun _ => forall_congr' fun K => tate_h2_iff_finite_extensions (D.loc l) K

theorem tateLocalDualityGood_iff_forall_coreClause (D : D7) : TateLocalDualityDegreeTwoGood D ↔
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL →
      CoreClause (D.loc l) K LL :=
  forall_congr' fun l => forall_congr' fun _ => forall_congr' fun K => forall_congr' fun _ =>
    forall_congr' fun LL => forall_congr' fun _ => (coreClause_iff (D.loc l) K LL).symm

theorem tateLocalDualityGood_of_adm3 {D : D7} (h : Formalism.MainNotions.LocalSituation.adm3 D) : TateLocalDualityDegreeTwoGood D :=
  ((tate_h2_iff_all_finite_extensions D).1 h).tateDualityTop_of_all

theorem compare (D : D7) :
    (Formalism.MainNotions.LocalSituation.adm3 D ↔ TateLocalDualityDegreeTwoAll D) ∧
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
      CoreClause (D.loc l) K LL ↔ TateLocalDualityDegreeTwoAt (D.loc l) K LL) ∧
    (TateLocalDualityDegreeTwoGood D ↔ ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL →
      CoreClause (D.loc l) K LL) ∧
    (Formalism.MainNotions.LocalSituation.adm3 D → TateLocalDualityDegreeTwoGood D) :=
  ⟨tate_h2_iff_all_finite_extensions D, fun l _ K LL => coreClause_iff (D.loc l) K LL, tateLocalDualityGood_iff_forall_coreClause D,
    tateLocalDualityGood_of_adm3⟩

end GlobalTheory.TateTopCompare
