import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteSpanAlgebraMapOfFreeFinite
import ReciprocityTheory.ClassFieldTheory.PadicCompatibleSequences.ExistsPadicIntOfCompatibleSeq
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.TdDualD

section Gen

variable {G : Type} [Group G] [TopologicalSpace G]
    {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

abbrev Ip (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (ϖ : O) (r : ℕ) : Submodule O ↥L.T :=
  (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)

theorem mem_Ip {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} {ϖ : O} {r : ℕ} {x : ↥L.T} :
    x ∈ Ip L ϖ r ↔ ∃ y : ↥L.T, x = ϖ ^ r • y := by
  rw [Ip, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, rfl⟩

theorem Ip_anti {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} {ϖ : O} {a b : ℕ} (h : a ≤ b) :
    Ip L ϖ b ≤ Ip L ϖ a := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_Ip.1 hx
  refine mem_Ip.2 ⟨ϖ ^ (b - a) • y, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]

theorem Ip_stable (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (ϖ : O) (r : ℕ) : StableSub L (Ip L ϖ r) := by
  intro g x hx
  obtain ⟨y, rfl⟩ := mem_Ip.1 hx
  exact mem_Ip.2 ⟨actT L g y, map_smul _ _ _⟩

def lq (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (I : Submodule O ↥L.T) (c : ↥L.T ⧸ I) : ↥L.T :=
  (Submodule.Quotient.mk_surjective I c).choose

theorem lq_mk (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (I : Submodule O ↥L.T) (c : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk (lq L I c) : ↥L.T ⧸ I) = c :=
  (Submodule.Quotient.mk_surjective I c).choose_spec

theorem liftQ_eq (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (I : Submodule O ↥L.T) (c : ↥L.T ⧸ I) :
    LocalSituation.liftQ L I c = (lq L I c : V) := rfl

theorem liftD_mk (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (e : V ⧸ L.T) :
    (Submodule.Quotient.mk (liftD L e) : V ⧸ L.T) = e :=
  (Submodule.Quotient.mk_surjective L.T e).choose_spec

theorem scale_cancel {ϖ : O} (hϖ : algebraMap O LL ϖ ≠ 0) (r : ℕ) (v : V) :
    ((algebraMap O LL ϖ)⁻¹ ^ r) • (ϖ ^ r • v) = v := by
  rw [← algebraMap_smul LL (ϖ ^ r) v, smul_smul, map_pow, ← mul_pow, inv_mul_cancel₀ hϖ, one_pow,
    one_smul]

theorem scale_cancel' {ϖ : O} (hϖ : algebraMap O LL ϖ ≠ 0) (r : ℕ) (v : V) :
    ϖ ^ r • (((algebraMap O LL ϖ)⁻¹ ^ r) • v) = v := by
  rw [← algebraMap_smul LL (ϖ ^ r), smul_smul, map_pow, ← mul_pow, mul_inv_cancel₀ hϖ, one_pow,
    one_smul]

def jr (L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ') {ϖ : O} (hϖ : algebraMap O LL ϖ ≠ 0) (r : ℕ) :
    (↥L'.T ⧸ Ip L' ϖ r) →ₗ[O] V' ⧸ L'.T :=
  (Ip L' ϖ r).liftQ
    (L'.T.mkQ ∘ₗ ((((algebraMap O LL ϖ)⁻¹ ^ r) • (LinearMap.id : V' →ₗ[LL] V')).restrictScalars O) ∘ₗ
      L'.T.subtype) (by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_Ip.1 hx
    rw [LinearMap.mem_ker]
    have : ((algebraMap O LL ϖ)⁻¹ ^ r) • (((ϖ ^ r • y : ↥L'.T)) : V') = (y : V') := by
      rw [Submodule.coe_smul]
      exact scale_cancel hϖ r _
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
      LinearMap.smul_apply, LinearMap.id_apply, this, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 y.2)

theorem jr_mk (L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ') {ϖ : O} (hϖ : algebraMap O LL ϖ ≠ 0) (r : ℕ)
    (t : ↥L'.T) :
    jr L' hϖ r (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (((algebraMap O LL ϖ)⁻¹ ^ r) • (t : V')) := rfl

theorem jr_inj (L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ') {ϖ : O} (hϖ : algebraMap O LL ϖ ≠ 0) (r : ℕ) :
    Function.Injective (jr L' hϖ r) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [jr_mk, Submodule.Quotient.mk_eq_zero] at hx
  refine (Submodule.Quotient.mk_eq_zero _).2 (mem_Ip.2 ⟨⟨_, hx⟩, ?_⟩)
  apply Subtype.ext
  rw [Submodule.coe_smul]
  exact (scale_cancel' hϖ r _).symm

theorem jr_surj (L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ') {ϖ : O} (hϖ : algebraMap O LL ϖ ≠ 0) (r : ℕ)
    (e : V' ⧸ L'.T) (he : ϖ ^ r • e = 0) : ∃ x, jr L' hϖ r x = e := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ e
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at he
  refine ⟨Submodule.Quotient.mk ⟨_, he⟩, ?_⟩
  rw [jr_mk]
  congr 1
  exact scale_cancel hϖ r v

theorem jr_act (L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ') {ϖ : O} (hϖ : algebraMap O LL ϖ ≠ 0) (r : ℕ)
    (g : G) (x : ↥L'.T ⧸ Ip L' ϖ r) :
    jr L' hϖ r (actQ L' _ (Ip_stable L' ϖ r) g x) = actD L' g (jr L' hϖ r x) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (((algebraMap O LL ϖ)⁻¹ ^ r) • ρ' g (t : V')) =
    Submodule.Quotient.mk (ρ' g (((algebraMap O LL ϖ)⁻¹ ^ r) • (t : V')))
  rw [map_smul]

theorem mem_Z1Q_of_jr (L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ') {ϖ : O} (hϖ : algebraMap O LL ϖ ≠ 0)
    (r : ℕ) (b : G → ↥L'.T ⧸ Ip L' ϖ r) (hb : (fun g => jr L' hϖ r (b g)) ∈ divisibleCocycles L') :
    b ∈ quotientCocycles L' _ (Ip_stable L' ϖ r) := by
  refine ⟨IsLocallyConstant.desc b (jr L' hϖ r) hb.1 (jr_inj L' hϖ r), fun g h => ?_⟩
  apply jr_inj L' hϖ r
  rw [map_add, jr_act]
  exact hb.2 g h

theorem cup_congr1 {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} {L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ'}
    {P : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, P x y = algebraMap O LL a) {ϖ : O} {r : ℕ}
    (d₁ d₂ : G → V) (e : G → V' ⧸ L'.T) (he : ∀ h, ϖ ^ r • e h = 0)
    (hd : ∀ g, ∃ t : ↥L.T, d₁ g - d₂ g = ϖ ^ r • (t : V)) (x : G × G) :
    ∃ a : O, cupLD L' P d₁ e x - cupLD L' P d₂ e x = algebraMap O LL a := by
  obtain ⟨t, ht⟩ := hd x.1
  have hw : ϖ ^ r • liftD L' (e x.2) ∈ L'.T := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, liftD_mk]
    exact he _
  obtain ⟨a, ha⟩ := hP t t.2 (ρ' x.1 (ϖ ^ r • liftD L' (e x.2))) (L'.stable _ _ hw)
  refine ⟨a, ?_⟩
  unfold cupLD
  rw [← LinearMap.sub_apply, ← map_sub, ht, ← ha, ← algebraMap_smul LL (ϖ ^ r) (t : V),
    ← algebraMap_smul LL (ϖ ^ r) (liftD L' (e x.2)), map_smul, map_smul, map_smul,
    LinearMap.smul_apply]

theorem cup_congr2 {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} {L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ'}
    {P : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, P x y = algebraMap O LL a) {ϖ : O}
    (hϖ : algebraMap O LL ϖ ≠ 0) {r : ℕ}
    (d : G → ↥L.T ⧸ Ip L ϖ r) (c' : G → ↥L'.T ⧸ Ip L' ϖ r) (x : G × G) :
    ∃ a : O, cupQ L L' P ϖ r d c' x -
      cupLD L' P (fun g => (lq L _ (d g) : V)) (fun g => jr L' hϖ r (c' g)) x =
        algebraMap O LL a := by
  set u : ↥L'.T := lq L' _ (c' x.2) with hu
  set w : V' := liftD L' (jr L' hϖ r (c' x.2)) with hw
  have hmem : ((algebraMap O LL ϖ)⁻¹ ^ r) • (u : V') - w ∈ L'.T := by
    rw [← Submodule.Quotient.eq]
    rw [hw, liftD_mk, ← jr_mk L' hϖ, hu, lq_mk]
  obtain ⟨a, ha⟩ := hP _ (lq L _ (d x.1)).2 _ (L'.stable x.1 _ hmem)
  refine ⟨a, ?_⟩
  unfold cupQ cupLD
  rw [← ha, map_sub, map_sub, map_smul, map_smul, smul_eq_mul, liftQ_eq, liftQ_eq]

def XX (Cob : (G × G → LL) → Prop) (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ)
    (L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O)
    (S : Submodule O (G → V' ⧸ L'.T)) (c : G → V' ⧸ L'.T) (r : ℕ) :
    Set (G → ↥L.T ⧸ Ip L ϖ r) :=
  {d | d ∈ quotientCocycles L _ (Ip_stable L ϖ r) ∧
    (∀ s ∈ S, (∀ h, ϖ ^ r • s h = 0) → Cob (cupLD L' P (fun g => (lq L _ (d g) : V)) s)) ∧
    ¬ Cob (cupLD L' P (fun g => (lq L _ (d g) : V)) c)}

theorem XX_nonempty {Cob : (G × G → LL) → Prop}
    (hCob : ∀ z z' : G × G → LL, (∀ x, ∃ a : O, z x - z' x = algebraMap O LL a) → (Cob z ↔ Cob z'))
    {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} {L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ'}
    {P : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, P x y = algebraMap O LL a) {ϖ : O}
    (hϖ : algebraMap O LL ϖ ≠ 0) (r : ℕ)
    (hdual : ∀ S', BQ L' _ (Ip_stable L' ϖ r) ≤ S' → S' ≤ quotientCocycles L' _ (Ip_stable L' ϖ r) →
      ∀ c' ∈ quotientCocycles L' _ (Ip_stable L' ϖ r),
      (∀ c ∈ quotientCocycles L _ (Ip_stable L ϖ r), (∀ s ∈ S', Cob (cupQ L L' P ϖ r c s)) →
        Cob (cupQ L L' P ϖ r c c')) → c' ∈ S')
    {S : Submodule O (G → V' ⧸ L'.T)} (hBS : BD L' ≤ S) (hSZ : S ≤ divisibleCocycles L')
    {c : G → V' ⧸ L'.T} (hc : c ∈ divisibleCocycles L') (hcS : c ∉ S) (hck : ∀ h, ϖ ^ r • c h = 0) :
    (XX Cob L L' P ϖ S c r).Nonempty := by
  let J : (G → ↥L'.T ⧸ Ip L' ϖ r) →ₗ[O] (G → V' ⧸ L'.T) := (jr L' hϖ r).compLeft G
  have hJ : ∀ b g, J b g = jr L' hϖ r (b g) := fun _ _ => rfl
  have hB : BQ L' _ (Ip_stable L' ϖ r) ≤ S.comap J := by
    rintro b ⟨x, rfl⟩
    refine hBS ⟨jr L' hϖ r x, ?_⟩
    funext g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, hJ, map_sub, jr_act]
  have hZ : S.comap J ≤ quotientCocycles L' _ (Ip_stable L' ϖ r) :=
    fun b hb => mem_Z1Q_of_jr L' hϖ r b (hSZ hb)
  choose c' hc' using fun h => jr_surj L' hϖ r (c h) (hck h)
  have hJc : J c' = c := funext hc'
  have hc'Z : c' ∈ quotientCocycles L' _ (Ip_stable L' ϖ r) :=
    mem_Z1Q_of_jr L' hϖ r c' (by
      have : (fun g => jr L' hϖ r (c' g)) = c := funext hc'
      rw [this]; exact hc)
  by_contra hne
  apply hcS
  rw [← hJc]
  refine hdual (S.comap J) hB hZ c' hc'Z (fun d hd hs => ?_)
  by_contra hnot
  refine hne ⟨d, hd, fun s hsS hsk => ?_, fun hcob => hnot ?_⟩
  · choose s' hs' using fun h => jr_surj L' hϖ r (s h) (hsk h)
    have hJs : J s' = s := funext hs'
    have h1 := hs s' (by rw [Submodule.mem_comap, hJs]; exact hsS)
    have h2 := (hCob _ _ (cup_congr2 hP hϖ d s')).1 h1
    have h3 : (fun g => jr L' hϖ r (s' g)) = s := funext hs'
    rwa [h3] at h2
  · refine (hCob _ _ (cup_congr2 hP hϖ d c')).2 ?_
    have h3 : (fun g => jr L' hϖ r (c' g)) = c := funext hc'
    rwa [h3]

def stp (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    (↥L.T ⧸ Ip L ϖ (r + 1)) →ₗ[O] (↥L.T ⧸ Ip L ϖ r) :=
  Submodule.mapQ _ _ LinearMap.id (fun _ hx => Ip_anti (Nat.le_succ r) hx)

theorem stp_mk (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (t : ↥L.T) :
    stp L ϖ r (Submodule.Quotient.mk t) = Submodule.Quotient.mk t := rfl

theorem stp_act (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (g : G)
    (x : ↥L.T ⧸ Ip L ϖ (r + 1)) :
    stp L ϖ r (actQ L _ (Ip_stable L ϖ (r + 1)) g x) =
      actQ L _ (Ip_stable L ϖ r) g (stp L ϖ r x) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show actQ L _ (Ip_stable L ϖ (r + 1)) g (Submodule.Quotient.mk t) =
    Submodule.Quotient.mk (actT L g t) from Submodule.mapQ_apply _ _ _ _, stp_mk, stp_mk]
  exact (Submodule.mapQ_apply _ _ _ _).symm

theorem lq_stp (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (y : ↥L.T ⧸ Ip L ϖ (r + 1)) :
    ∃ t : ↥L.T, (lq L _ (stp L ϖ r y) : V) - (lq L _ y : V) = ϖ ^ r • (t : V) := by
  have h : lq L _ (stp L ϖ r y) - lq L _ y ∈ Ip L ϖ r := by
    rw [← Submodule.Quotient.eq, lq_mk, ← stp_mk, lq_mk]
  obtain ⟨t, ht⟩ := mem_Ip.1 h
  exact ⟨t, by simpa using congrArg (Subtype.val) ht⟩

theorem XX_step {Cob : (G × G → LL) → Prop}
    (hCob : ∀ z z' : G × G → LL, (∀ x, ∃ a : O, z x - z' x = algebraMap O LL a) → (Cob z ↔ Cob z'))
    {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} {L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ'}
    {P : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, P x y = algebraMap O LL a) {ϖ : O} (r : ℕ)
    {S : Submodule O (G → V' ⧸ L'.T)} {c : G → V' ⧸ L'.T} (hck : ∀ h, ϖ ^ r • c h = 0)
    {d : G → ↥L.T ⧸ Ip L ϖ (r + 1)} (hd : d ∈ XX Cob L L' P ϖ S c (r + 1)) :
    (fun g => stp L ϖ r (d g)) ∈ XX Cob L L' P ϖ S c r := by
  have hlift : ∀ g, ∃ t : ↥L.T, (fun g => (lq L _ (stp L ϖ r (d g)) : V)) g -
      (fun g => (lq L _ (d g) : V)) g = ϖ ^ r • (t : V) := fun g => lq_stp L ϖ r (d g)
  refine ⟨⟨hd.1.1.comp _, fun g h => ?_⟩, fun s hs hk => ?_, fun hc => hd.2.2 ?_⟩
  · change stp L ϖ r (d (g * h)) = _
    rw [hd.1.2 g h, map_add, stp_act]
  · refine (hCob _ _ (cup_congr1 hP _ _ s hk hlift)).2 (hd.2.1 s hs fun h => ?_)
    rw [pow_succ', mul_smul, hk, smul_zero]
  · exact (hCob _ _ (cup_congr1 hP _ _ c hck hlift)).1 hc

theorem span_pow_smul (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (ϖ : O) (k : ℕ) :
    ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule O ↥L.T) = Ip L ϖ k := by
  rw [Ideal.span_singleton_pow]

theorem exists_limit (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) {ϖ : O}
    (hc : IsAdicComplete (Ideal.span {ϖ}) ↥L.T) (r₀ : ℕ) (x : ∀ n, ↥L.T ⧸ Ip L ϖ (r₀ + n))
    (hx : ∀ n, stp L ϖ (r₀ + n) (x (n + 1)) = x n) :
    ∃ t : ↥L.T, ∀ n, (Submodule.Quotient.mk t : ↥L.T ⧸ Ip L ϖ (r₀ + n)) = x n := by
  let u : ℕ → ↥L.T := fun n => lq L _ (x n)
  have hu : ∀ n, (Submodule.Quotient.mk (u n) : ↥L.T ⧸ Ip L ϖ (r₀ + n)) = x n :=
    fun n => lq_mk L _ (x n)
  have h1 : ∀ n, u (n + 1) - u n ∈ Ip L ϖ (r₀ + n) := by
    intro n
    rw [← Submodule.Quotient.eq, hu, ← hx n, ← hu (n + 1)]
    rfl
  have h2 : ∀ m n, m ≤ n → u n - u m ∈ Ip L ϖ (r₀ + m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem (Ip_anti (Nat.add_le_add_left hmn r₀) (h1 n)) ih
      simpa using this
  obtain ⟨t, ht⟩ := hc.toIsPrecomplete.prec (f := u) (fun {m n} hmn => by
    rw [SModEq.sub_mem, span_pow_smul, ← neg_sub, neg_mem_iff]
    exact Ip_anti (Nat.le_add_left m r₀) (h2 m n hmn))
  refine ⟨t, fun n => ?_⟩
  have a := ht (r₀ + n)
  rw [SModEq.sub_mem, span_pow_smul] at a
  have b := h2 n (r₀ + n) (Nat.le_add_left n r₀)
  rw [← hu n, eq_comm, Submodule.Quotient.eq]
  have := sub_mem a b
  simpa using this

theorem eq_zero_of_mem (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) {ϖ : O}
    (hc : IsAdicComplete (Ideal.span {ϖ}) ↥L.T) (w : ↥L.T) (h : ∀ n, w ∈ Ip L ϖ n) : w = 0 :=
  hc.toIsHausdorff.haus w fun n => by
    rw [SModEq.zero, span_pow_smul]
    exact h n

theorem core [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [CompactSpace G]
    {Cob : (G × G → LL) → Prop}
    (hCob : ∀ z z' : G × G → LL, (∀ x, ∃ a : O, z x - z' x = algebraMap O LL a) → (Cob z ↔ Cob z'))
    {L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ} {L' : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ'}
    {P : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, P x y = algebraMap O LL a) {ϖ : O}
    (hϖ : algebraMap O LL ϖ ≠ 0) (hadic : IsAdicComplete (Ideal.span {ϖ}) ↥L.T)
    (hbasis : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (htor : ∀ v : V', ∃ n : ℕ, ϖ ^ n • v ∈ L'.T)
    (hfin : ∀ r, Finite ↥(quotientCocycles L _ (Ip_stable L ϖ r)))
    (hdual : ∀ r, ∀ S', BQ L' _ (Ip_stable L' ϖ r) ≤ S' → S' ≤ quotientCocycles L' _ (Ip_stable L' ϖ r) →
      ∀ c' ∈ quotientCocycles L' _ (Ip_stable L' ϖ r),
      (∀ c ∈ quotientCocycles L _ (Ip_stable L ϖ r), (∀ s ∈ S', Cob (cupQ L L' P ϖ r c s)) →
        Cob (cupQ L L' P ϖ r c c')) → c' ∈ S')
    {S : Submodule O (G → V' ⧸ L'.T)} (hBS : BD L' ≤ S) (hSZ : S ≤ divisibleCocycles L')
    {c : G → V' ⧸ L'.T} (hc : c ∈ divisibleCocycles L')
    (H : ∀ d ∈ latticeCocycles L, (∀ s ∈ S, Cob (cupLD L' P d s)) → Cob (cupLD L' P d c)) : c ∈ S := by
  by_contra hcS
  have tor1 : ∀ e : V' ⧸ L'.T, ∃ n : ℕ, ϖ ^ n • e = 0 := by
    intro e
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ e
    obtain ⟨n, hn⟩ := htor v
    exact ⟨n, by rw [← Submodule.Quotient.mk_smul]; exact (Submodule.Quotient.mk_eq_zero _).2 hn⟩
  have kill : ∀ s ∈ divisibleCocycles L', ∃ N : ℕ, ∀ h, ϖ ^ N • s h = 0 := by
    intro s hs
    choose nn hnn using tor1
    have hf := hs.1.range_finite
    refine ⟨hf.toFinset.sup nn, fun h => ?_⟩
    have hle : nn (s h) ≤ hf.toFinset.sup nn := Finset.le_sup (by simp)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hnn, smul_zero]
  have mono : ∀ (e : V' ⧸ L'.T) (a b : ℕ), a ≤ b → ϖ ^ a • e = 0 → ϖ ^ b • e = 0 := by
    intro e a b hab he
    rw [← Nat.sub_add_cancel hab, pow_add, mul_smul, he, smul_zero]
  obtain ⟨r₀, hr₀⟩ := kill c hc
  have hck : ∀ n h, ϖ ^ (r₀ + n) • c h = 0 :=
    fun n h => mono _ _ _ (Nat.le_add_right r₀ n) (hr₀ h)
  obtain ⟨f, hfX, hf⟩ := ReciprocityTheory.DiscreteGroups.PeuVal.exists_compatible_seq
    (Y := fun n => G → ↥L.T ⧸ Ip L ϖ (r₀ + n))
    (fun n => XX Cob L L' P ϖ S c (r₀ + n))
    (fun n d g => stp L ϖ (r₀ + n) (d g))
    (fun n => XX_nonempty hCob hP hϖ (r₀ + n) (hdual (r₀ + n)) hBS hSZ hc hcS (hck n))
    (fun n => by
      haveI := hfin (r₀ + n)
      exact (Set.toFinite (quotientCocycles L _ (Ip_stable L ϖ (r₀ + n)) : Set _)).subset fun d hd => hd.1)
    (fun n d hd => XX_step hCob hP (r₀ + n) (hck n) hd)
  choose t ht using fun g => exists_limit L hadic r₀ (fun n => f n g) (fun n => congrFun (hf n) g)
  have hzero : ∀ w : ↥L.T, (∀ n, w ∈ Ip L ϖ (r₀ + n)) → w = 0 := fun w hw =>
    eq_zero_of_mem L hadic w fun n => Ip_anti (Nat.le_add_left n r₀) (hw n)
  have hcont : Continuous fun g => (t g : V) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    have hF : Filter.Tendsto (fun g => (t g : V) - (t g₀ : V)) (nhds g₀) (nhds 0) := by
      rw [hbasis.tendsto_right_iff]
      intro n _
      filter_upwards [(hfX n).1.1.eventually_eq g₀] with g hg
      have h1 : t g - t g₀ ∈ Ip L ϖ n := Ip_anti (Nat.le_add_left n r₀)
        ((Submodule.Quotient.eq _).1 (by rw [ht g n, ht g₀ n, hg]))
      obtain ⟨y, hy⟩ := mem_Ip.1 h1
      exact ⟨y, y.2, by simpa using (congrArg Subtype.val hy).symm⟩
    have h2 : Filter.Tendsto (fun g => ((t g : V) - (t g₀ : V)) + (t g₀ : V)) (nhds g₀)
        (nhds (0 + (t g₀ : V))) := hF.add tendsto_const_nhds
    simpa [ContinuousAt] using h2
  have hcoc : ∀ g h, (t (g * h) : V) = (t g : V) + ρ g (t h : V) := by
    intro g h
    have h0 : t (g * h) - (t g + actT L g (t h)) = 0 := by
      refine hzero _ fun n => ?_
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add,
        ht, ht, show (Submodule.Quotient.mk (actT L g (t h)) : ↥L.T ⧸ Ip L ϖ (r₀ + n)) =
          actQ L _ (Ip_stable L ϖ (r₀ + n)) g (Submodule.Quotient.mk (t h)) from
          (Submodule.mapQ_apply _ _ _ _).symm, ht, (hfX n).1.2 g h, sub_self]
    have h3 : (t (g * h) : V) = (t g : V) + ((actT L g (t h) : ↥L.T) : V) := by
      simpa using congrArg Subtype.val (sub_eq_zero.1 h0)
    exact h3
  have hdZ : (fun g => (t g : V)) ∈ latticeCocycles L :=
    ⟨⟨hcont, hcoc⟩, fun g _ => (t g).2⟩
  have hclose : ∀ n g, ∃ y : ↥L.T, (fun g => (t g : V)) g - (fun g => (lq L _ (f n g) : V)) g =
      ϖ ^ (r₀ + n) • (y : V) := by
    intro n g
    have h1 : t g - lq L _ (f n g) ∈ Ip L ϖ (r₀ + n) := by
      rw [← Submodule.Quotient.eq, ht, lq_mk]
    obtain ⟨y, hy⟩ := mem_Ip.1 h1
    exact ⟨y, by simpa using congrArg Subtype.val hy⟩
  refine (hfX 0).2.2 ((hCob _ _ (cup_congr1 hP _ _ c (hck 0) (hclose 0))).1
    (H _ hdZ fun s hs => ?_))
  obtain ⟨N, hN⟩ := kill s (hSZ hs)
  have hkill : ∀ h, ϖ ^ (r₀ + N) • s h = 0 := fun h => mono _ _ _ (Nat.le_add_left N r₀) (hN h)
  exact (hCob _ _ (cup_congr1 hP _ _ s hkill (hclose N))).2 ((hfX N).2.1 s hs hkill)

end Gen

open GlobalTheory.CompanionTheory.LocDual in

theorem dualD_of_dualQ : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), FinZQ ((D.loc l).PD K) →
    DualQ ((D.loc l).PD K) → DualD ((D.loc l).PD K) := by
  intro D l _ K hF hQ LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' P hP S hBS hSZ c hc H
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := id hG
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : algebraMap O LL ϖ ≠ 0 := fun h =>
    hϖ.ne_zero ((IsFractionRing.injective O LL) (by rw [h, map_zero]))
  obtain ⟨hO, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ
  obtain ⟨-, hb, -, -, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hG A LA ϖ hϖ
  obtain ⟨-, -, -, hbd', -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hG A' LA' ϖ hϖ
  haveI : CompactSpace ↥(GK K) :=
    haveI := K.2
    isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact
  haveI : Module.Free O ↥LA.T := LA.free
  haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  refine core (Cob := CobO ((D.loc l).PD K) L1) ?_ (fun x hx y hy => (hP.2 y).1 hy x hx) hne
    (GlobalTheory.CNorm.isAdicComplete_of_free_finite _ hO) hb ?_
    (fun r => hF LL O hG A LA ϖ hϖ r (Ip_stable LA ϖ r))
    (fun r => (hQ LL O hG L1 hL1 A A' LA LA' P hP ϖ hϖ r (Ip_stable LA ϖ r) (Ip_stable LA' ϖ r)).2)
    hBS hSZ hc H
  · intro z z' h
    have : (fun x => (Submodule.Quotient.mk (z x) : LL ⧸ L1.T)) =
        fun x => (Submodule.Quotient.mk (z' x) : LL ⧸ L1.T) := by
      funext x
      obtain ⟨a, ha⟩ := h x
      refine (Submodule.Quotient.eq _).2 ?_
      rw [ha, hL1]
      exact ⟨a, rfl⟩
    unfold CobO
    rw [this]
  · intro v
    obtain ⟨n, hn⟩ := hbd' (fun _ => v) continuous_const
    exact ⟨n, hn 1⟩

end GlobalTheory.CompanionTheory.TdDualD
