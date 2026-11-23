import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TateLocalDualityTopDegree
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotient
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasis
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCocycle
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCoboundaryStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicCupTwoCochainLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section
namespace GlobalTheory.CompanionTheory.LocDual.Q

theorem mem_smul_top {O T : Type} [CommRing O] [AddCommGroup T] [Module O T] (a : O) (x : T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O T) ↔ ∃ t : T, x = a • t := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, trivial, rfl⟩

theorem divisible {LL O V V' : Type} [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
    (T : Submodule O V) (T' : Submodule O V') (Q : V →ₗ[LL] V' →ₗ[LL] LL) (a : O) (ha : a ≠ 0)
    (hx : ∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ b : O, Q x y = algebraMap O LL b) (x : V)
    (h : ∀ y ∈ T', ∃ b : O, Q x y = algebraMap O LL (a * b)) : ∃ t : ↥T, x = a • (t : V) := by
  have h0 : algebraMap O LL a ≠ 0 := by
    simpa using (IsFractionRing.injective O LL).ne ha
  have hm : (algebraMap O LL a)⁻¹ • x ∈ T := by
    refine (hx _).2 fun y hy => ?_
    obtain ⟨b, hb⟩ := h y hy
    refine ⟨b, ?_⟩
    rw [map_smul, LinearMap.smul_apply, hb, map_mul, smul_eq_mul, inv_mul_cancel_left₀ h0]
  refine ⟨⟨_, hm⟩, ?_⟩
  change x = a • ((algebraMap O LL a)⁻¹ • x)
  rw [← algebraMap_smul LL a, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem pairing_exists : ∀ (LL O V V' : Type) [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
    (T : Submodule O V) (T' : Submodule O V') (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O), ϖ ≠ 0 → ∀ r : ℕ,
    (∀ y, y ∈ T' ↔ ∀ x ∈ T, ∃ a : O, P x y = algebraMap O LL a) →
    (∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ a : O, P x y = algebraMap O LL a) →
    ∃ pm : (↥T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥T)) →ₗ[O]
        (↥T' ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥T')) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ r}),
      (∀ (x : ↥T) (y : ↥T') (a : O), P x y = algebraMap O LL a →
        pm (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Ideal.Quotient.mk _ a) ∧
      (∀ w, (∀ w', pm w w' = 0) → w = 0) ∧ (∀ w', (∀ w, pm w w' = 0) → w' = 0) := by
  intro LL O V V' _ _ _ _ _ _ _ _ _ _ _ _ _ T T' P ϖ hϖ r hy hx
  have inj := IsFractionRing.injective O LL
  have hex : ∀ (x : ↥T) (y : ↥T'), ∃ a : O, P x y = algebraMap O LL a := fun x y => (hy y).1 y.2 x x.2
  choose pa hpa using hex
  have hsm : ∀ (c : O) (v : V), c • v = algebraMap O LL c • v := fun c v => (algebraMap_smul LL c v).symm
  have hsm' : ∀ (c : O) (v : V'), c • v = algebraMap O LL c • v := fun c v => (algebraMap_smul LL c v).symm
  let B : ↥T →ₗ[O] ↥T' →ₗ[O] O := LinearMap.mk₂ O pa
    (fun x x' y => inj (by simp only [map_add, ← hpa, Submodule.coe_add, LinearMap.add_apply]))
    (fun c x y => inj (by
      simp only [map_mul, ← hpa, Submodule.coe_smul, smul_eq_mul, hsm, map_smul, LinearMap.smul_apply]))
    (fun x y y' => inj (by simp only [map_add, ← hpa, Submodule.coe_add]))
    (fun c x y => inj (by
      simp only [map_mul, ← hpa, Submodule.coe_smul, smul_eq_mul, hsm', map_smul]))
  have hB : ∀ x y, B x y = pa x y := fun _ _ => rfl
  let C : ↥T →ₗ[O] ↥T' →ₗ[O] (O ⧸ Ideal.span {ϖ ^ r}) := B.compr₂ (Submodule.mkQ (Ideal.span {ϖ ^ r}))
  have hC : ∀ x y, C x y = Ideal.Quotient.mk _ (pa x y) := fun _ _ => rfl
  have hk1 : (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥T) ≤ LinearMap.ker C := by
    intro x hxm
    obtain ⟨t, rfl⟩ := (mem_smul_top _ _).1 hxm
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun y => ?_
    have h1 : C (ϖ ^ r • t) y = Ideal.Quotient.mk _ (ϖ ^ r * pa t y) := by
      rw [hC, ← hB, map_smul, LinearMap.smul_apply, hB, smul_eq_mul]
    rw [h1, LinearMap.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  let D := Submodule.liftQ _ C hk1
  have hk2 : (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥T') ≤ LinearMap.ker D.flip := by
    intro y hym
    obtain ⟨t, rfl⟩ := (mem_smul_top _ _).1 hym
    rw [LinearMap.mem_ker]
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    have h1 : C x (ϖ ^ r • t) = Ideal.Quotient.mk _ (ϖ ^ r * pa x t) := by
      rw [hC, ← hB, map_smul, hB, smul_eq_mul]
    change C x (ϖ ^ r • t) = 0
    rw [h1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  let F := Submodule.liftQ _ D.flip hk2
  have hF : ∀ (x : ↥T) (y : ↥T'), F.flip (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Ideal.Quotient.mk _ (pa x y) := fun _ _ => rfl
  have hy' : ∀ y, y ∈ T' ↔ ∀ x ∈ T, ∃ b : O, P.flip y x = algebraMap O LL b := fun y => by
    simpa using hy y
  have hx' : ∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ b : O, P.flip.flip x y = algebraMap O LL b := fun x => by
    simpa using hx x
  refine ⟨F.flip, ?_, ?_, ?_⟩
  · intro x y a ha
    rw [hF]
    congr 1
    apply inj
    rw [← hpa, ha]
  · intro w hw
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨t, ht⟩ := divisible T T' P (ϖ ^ r) (pow_ne_zero _ hϖ) hx x (fun y hym => by
      have h1 := hw (Submodule.Quotient.mk ⟨y, hym⟩)
      rw [hF] at h1
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
      exact ⟨b, by rw [← hb]; exact hpa x ⟨y, hym⟩⟩)
    rw [Submodule.Quotient.mk_eq_zero, mem_smul_top]
    exact ⟨t, Subtype.ext ht⟩
  · intro w hw
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨t, ht⟩ := divisible T' T P.flip (ϖ ^ r) (pow_ne_zero _ hϖ) hy' y (fun x hxm => by
      have h1 := hw (Submodule.Quotient.mk ⟨x, hxm⟩)
      rw [hF] at h1
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
      exact ⟨b, by rw [← hb]; exact hpa ⟨x, hxm⟩ y⟩)
    rw [Submodule.Quotient.mk_eq_zero, mem_smul_top]
    exact ⟨t, Subtype.ext ht⟩

theorem finite_quot : ∀ (O V : Type) [CommRing O] [AddCommGroup V] [Module O V] (T : Submodule O V) (ϖ : O) (r : ℕ),
    Finite (O ⧸ Ideal.span {ϖ}) → T.FG →
    Finite (O ⧸ Ideal.span {ϖ ^ r}) ∧ Finite (↥T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥T)) := by
  intro O V _ _ _ T ϖ r hF hT
  haveI := hF
  have h1 : Finite (O ⧸ Ideal.span {ϖ ^ r}) := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.finite_quotient_pow ⟨{ϖ}, by simp⟩ r
  refine ⟨h1, ?_⟩
  haveI : Module.Finite O ↥T := Module.Finite.iff_fg.2 hT
  haveI : Module.Finite (O ⧸ Ideal.span {ϖ ^ r}) (↥T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥T)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ r})

theorem cobO_iff : ∀ (G : Type) [Group G] [TopologicalSpace G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR), TopInj PD →
    ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
    ∀ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (u : G → O),
      (∀ g, algebraMap O LL (u g) = ((cycLL PD LL g : LLˣ) : LL)) →
    ∀ (z : G × G → LL) (zb : G × G → O ⧸ Ideal.span {ϖ ^ r}),
      (∀ x, ∃ a : O, algebraMap O LL a = algebraMap O LL ϖ ^ r * z x ∧ zb x = Ideal.Quotient.mk _ a) →
      (CobO PD L1 z ↔ ∃ f : G → O ⧸ Ideal.span {ϖ ^ r}, IsLocallyConstant f ∧
        ∀ g h, Ideal.Quotient.mk _ (u g) * f h - f (g * h) + f g = zb (g, h)) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD hTop LL _ _ _ O _ _ hG L1 hL1 ϖ hϖ r u hu z zb hz
  have hG0 : ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL := hG.1
  haveI hDom : IsDomain O := hG0.choose
  haveI hFrac : IsFractionRing O LL := hG0.choose_spec.2
  have inj := IsFractionRing.injective O LL
  have h0 : algebraMap O LL ϖ ≠ 0 := by
    simpa using inj.ne hϖ.ne_zero
  have h0r : algebraMap O LL ϖ ^ r ≠ 0 := pow_ne_zero _ h0
  have hmem : ∀ y : LL, y ∈ L1.T ↔ ∃ a : O, algebraMap O LL a = y := fun y => by
    rw [hL1]
    rfl
  constructor
  · intro hc
    have hzr : ∀ x, algebraMap O LL ϖ ^ r * z x ∈ L1.T := fun x => by
      obtain ⟨a, ha, -⟩ := hz x
      exact (hmem _).2 ⟨a, ha⟩
    obtain ⟨f, hf1, hf2, hf3⟩ := hTop LL O hG L1 hL1 ϖ hϖ r z hzr hc
    choose o ho using fun g => (hmem _).1 (hf1 g)
    refine ⟨fun g => Ideal.Quotient.mk _ (o g), ?_, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro g0
      filter_upwards [hf2.eventually_eq g0] with g hg
      obtain ⟨b, hb⟩ := (hmem _).1 ((Submodule.Quotient.eq _).1 hg)
      have h1 : o g - o g0 = ϖ ^ r * b := inj (by
        rw [map_sub, map_mul, map_pow, ho, ho, hb]
        ring)
      refine Ideal.Quotient.eq.2 ?_
      rw [h1]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro g h
      obtain ⟨a, ha, hza⟩ := hz (g, h)
      obtain ⟨b, hb⟩ := (hmem _).1 (hf3 (g, h))
      have hb' : algebraMap O LL b =
          ((cycLL PD LL g : LLˣ) : LL) * f h - f (g * h) + f g - z (g, h) := hb
      have h1 : u g * o h - o (g * h) + o g - a = ϖ ^ r * b := inj (by
        simp only [map_sub, map_add, map_mul, map_pow, ho, ha, hu, hb']
        ring)
      rw [hza, ← map_mul, ← map_sub, ← map_add]
      refine Ideal.Quotient.eq.2 ?_
      rw [h1]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨f, hf, hf2⟩
    choose o ho using fun g => Ideal.Quotient.mk_surjective (f g)
    have hF : ∀ g h b, o g - o h = ϖ ^ r * b → (algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o g) -
        (algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o h) = algebraMap O LL b := by
      intro g h b hb
      rw [← mul_sub, ← map_sub, hb, map_mul, map_pow, inv_pow, inv_mul_cancel_left₀ h0r]
    refine Submodule.mem_map.2 ⟨fun g => (Submodule.Quotient.mk
      ((algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o g)) : LL ⧸ L1.T), ⟨?_, fun _ => trivial⟩, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro g0
      filter_upwards [hf.eventually_eq g0] with g hg
      rw [← ho g, ← ho g0] at hg
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hg)
      exact (Submodule.Quotient.eq _).2 ((hmem _).2 ⟨b, (hF g g0 b hb).symm⟩)
    · funext x
      obtain ⟨g, h⟩ := x
      obtain ⟨a, ha, hza⟩ := hz (g, h)
      have h1 := hf2 g h
      rw [hza, ← ho, ← ho, ← ho, ← map_mul, ← map_sub, ← map_add] at h1
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
      have hb2 : algebraMap O LL b = ((cycLL PD LL g : LLˣ) : LL) * ((algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o h)) -
          (algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o (g * h)) +
          (algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o g) - z (g, h) := by
        have h2 := congrArg (algebraMap O LL) hb
        simp only [map_sub, map_add, map_mul, map_pow, ha, hu] at h2
        rw [inv_pow]
        field_simp
        linear_combination -h2
      change (Submodule.Quotient.mk (((cycLL PD LL g : LLˣ) : LL) * ((algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o h))) : LL ⧸ L1.T) -
        Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o (g * h))) +
        Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL (o g)) = Submodule.Quotient.mk (z (g, h))
      rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
      exact (Submodule.Quotient.eq _).2 ((hmem _).2 ⟨b, hb2⟩)

section Defs
variable (G : Type) [Group G] [TopologicalSpace G] (N : ℕ) (χ : G →* (ZMod N)ˣ)

def TopChars : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] (z : G × G → M), IsLocallyConstant z →
    (∀ g h k, (χ g : ZMod N) • z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
    (∀ ψ : M →+ ZMod N, ∃ f : G → ZMod N, IsLocallyConstant f ∧
      ∀ g h, (χ g : ZMod N) * f h - f (g * h) + f g = ψ (z (g, h))) →
    ∃ f : G → M, IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod N) • f h - f (g * h) + f g = z (g, h)

def PairLeft : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Finite W] (a : G → W →+ W), (∀ m, a 1 m = m) →
    (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m, IsLocallyConstant fun g => a g m) →
  ∀ (W' : Type) [AddCommGroup W'] [Finite W'] (a' : G → W' →+ W'), (∀ m, a' 1 m = m) →
    (∀ g h m, a' (g * h) m = a' g (a' h m)) → (∀ m, IsLocallyConstant fun g => a' g m) →
  ∀ P : W →+ W' →+ ZMod N, (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) →
    (∀ g x y, P (a g x) (a' g y) = (χ g : ZMod N) * P x y) →
  ∀ S : AddSubgroup (G → W), (∀ m : W, (fun g => a g m - m) ∈ S) →
    (∀ s ∈ S, (IsLocallyConstant s ∧ ∀ g h, s (g * h) = s g + a g (s h))) →
  ∀ c : G → W, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)) →
    (∀ c' : G → W', (IsLocallyConstant c' ∧ ∀ g h, c' (g * h) = c' g + a' g (c' h)) →
      (∀ s ∈ S, (∃ f : G → ZMod N, IsLocallyConstant f ∧
        ∀ g h, (χ g : ZMod N) * f h - f (g * h) + f g = P (s g) (a' g (c' h)))) →
      (∃ f : G → ZMod N, IsLocallyConstant f ∧
        ∀ g h, (χ g : ZMod N) * f h - f (g * h) + f g = P (c g) (a' g (c' h)))) → c ∈ S

def PairRight : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Finite W] (a : G → W →+ W), (∀ m, a 1 m = m) →
    (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m, IsLocallyConstant fun g => a g m) →
  ∀ (W' : Type) [AddCommGroup W'] [Finite W'] (a' : G → W' →+ W'), (∀ m, a' 1 m = m) →
    (∀ g h m, a' (g * h) m = a' g (a' h m)) → (∀ m, IsLocallyConstant fun g => a' g m) →
  ∀ P : W →+ W' →+ ZMod N, (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) →
    (∀ g x y, P (a g x) (a' g y) = (χ g : ZMod N) * P x y) →
  ∀ S : AddSubgroup (G → W'), (∀ m : W', (fun g => a' g m - m) ∈ S) →
    (∀ s ∈ S, (IsLocallyConstant s ∧ ∀ g h, s (g * h) = s g + a' g (s h))) →
  ∀ c' : G → W', (IsLocallyConstant c' ∧ ∀ g h, c' (g * h) = c' g + a' g (c' h)) →
    (∀ c : G → W, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)) →
      (∀ s ∈ S, (∃ f : G → ZMod N, IsLocallyConstant f ∧
        ∀ g h, (χ g : ZMod N) * f h - f (g * h) + f g = P (c g) (a' g (s h)))) →
      (∃ f : G → ZMod N, IsLocallyConstant f ∧
        ∀ g h, (χ g : ZMod N) * f h - f (g * h) + f g = P (c g) (a' g (c' h)))) → c' ∈ S

end Defs

theorem cob_of_chars {G : Type} [Group G] [TopologicalSpace G] {N : ℕ} {χ : G →* (ZMod N)ˣ}
    (hC : TopChars G N χ) {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)] (hN : (N : O) ∈ I) (u : G → O)
    (hu : ∀ g, ∃ k : ℕ, (k : ZMod N) = (χ g : ZMod N) ∧ (k : O) - u g ∈ I)
    (zb : G × G → O ⧸ I) (hlc : IsLocallyConstant zb)
    (hco : ∀ g h k, Ideal.Quotient.mk I (u g) * zb (h, k) - zb (g * h, k) + zb (g, h * k) - zb (g, h) = 0)
    (hch : ∀ ψ : (O ⧸ I) →+ ZMod N, ∃ f : G → ZMod N, IsLocallyConstant f ∧
      ∀ g h, (χ g : ZMod N) * f h - f (g * h) + f g = ψ (zb (g, h))) :
    ∃ f : G → O ⧸ I, IsLocallyConstant f ∧
      ∀ g h, Ideal.Quotient.mk I (u g) * f h - f (g * h) + f g = zb (g, h) := by
  have hNz : ∀ x : O ⧸ I, N • x = 0 := by
    intro x
    have : (N : O ⧸ I) = 0 := by
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hN
      simpa using this
    rw [nsmul_eq_mul, this, zero_mul]
  letI : Module (ZMod N) (O ⧸ I) := AddCommGroup.zmodModule hNz
  have hsm : ∀ g (x : O ⧸ I), (χ g : ZMod N) • x = Ideal.Quotient.mk I (u g) * x := by
    intro g x
    obtain ⟨k, hk, hkI⟩ := hu g
    rw [← hk, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    congr 1
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hkI
    rw [map_sub, sub_eq_zero] at this
    simpa using this
  obtain ⟨f, hf, hf2⟩ := hC (O ⧸ I) zb hlc (fun g h k => by rw [hsm]; exact hco g h k) hch
  exact ⟨f, hf, fun g h => by rw [← hsm]; exact hf2 g h⟩

theorem char_mul {N : ℕ} {O : Type} [CommRing O] (I : Ideal O) (ψ : (O ⧸ I) →+ ZMod N) (v : O)
    (c : ZMod N) (h : ∃ k : ℕ, (k : ZMod N) = c ∧ (k : O) - v ∈ I) (x : O ⧸ I) :
    ψ (Ideal.Quotient.mk I v * x) = c * ψ x := by
  obtain ⟨k, rfl, hk⟩ := h
  have h1 : Ideal.Quotient.mk I v = (k : O ⧸ I) := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hk
    rw [map_sub, sub_eq_zero] at this
    simpa using this.symm
  rw [h1, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

theorem exists_nat_rep {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [CommRing O]
    [Algebra O LL] (hinj : Function.Injective (algebraMap O LL))
    (hInt : ∀ u : ℤ_[l], algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ Set.range (algebraMap O LL))
    (I : Ideal O) (n : ℕ) (hN : ((l ^ n : ℕ) : O) ∈ I) (x : ℤ_[l]) (v : O)
    (hv : algebraMap O LL v = algebraMap ℚ_[l] LL (x : ℚ_[l])) :
    ∃ k : ℕ, (k : ZMod (l ^ n)) = PadicInt.toZModPow n x ∧ (k : O) - v ∈ I := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨(pow_pos hlp.pos n).ne'⟩
  refine ⟨(PadicInt.toZModPow n x).val, ZMod.natCast_zmod_val _, ?_⟩
  have h0 : (((PadicInt.toZModPow n x).val : ℕ) : ℤ_[l]) - x ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h0
  obtain ⟨t, ht⟩ := h0
  obtain ⟨o, ho⟩ := hInt t
  have h1 : ((((PadicInt.toZModPow n x).val : ℕ) : O)) - v = ((l ^ n : ℕ) : O) * o := by
    apply hinj
    have h2 := congrArg (fun y : ℤ_[l] => algebraMap ℚ_[l] LL (y : ℚ_[l])) ht
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, map_sub, map_mul, map_pow,
      map_natCast] at h2
    rw [map_sub, map_mul, map_natCast, map_natCast, hv, ho]
    push_cast
    exact h2
  rw [h1]
  exact Ideal.mul_mem_right _ _ hN

section Act
variable {G : Type} [Group G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
  [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_mk (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g : G) (x : ↥L.T) :
    actQ L I hI g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (actT L g x) := rfl

theorem actQ_one (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (m : ↥L.T ⧸ I) :
    actQ L I hI 1 m = m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [actQ_mk]
  congr 1
  apply Subtype.ext
  simp [actT]

theorem actQ_mul (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g h : G) (m : ↥L.T ⧸ I) :
    actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [actQ_mk, actQ_mk, actQ_mk]
  congr 1
  apply Subtype.ext
  simp [actT, Module.End.mul_apply]
  rfl

theorem liftQ_spec (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (w : ↥L.T ⧸ I) :
    ∃ t : ↥L.T, (t : V) = LocalSituation.liftQ L I w ∧ Submodule.Quotient.mk t = w :=
  ⟨_, rfl, (Submodule.Quotient.mk_surjective I w).choose_spec⟩

end Act

theorem smul_quot {O : Type} [CommRing O] (I : Ideal O) (o : O) (m : O ⧸ I) : o • m = Ideal.Quotient.mk I o * m := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
  rfl

theorem act_lc {G Qp LL O : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (A : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (hB : (nhds (0 : A.V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (LA.T : Set A.V)))
    (m : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) :
    IsLocallyConstant fun g => actQ LA _ hI g m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have hU := hB.mem_of_mem (i := r) trivial
  have hc : Filter.Tendsto (fun g => A.ρ g (x : A.V) + (-(A.ρ g0 (x : A.V)))) (nhds g0) (nhds 0) := by
    have h1 : Filter.Tendsto (fun g => A.ρ g (x : A.V) + (-(A.ρ g0 (x : A.V)))) (nhds g0)
        (nhds (A.ρ g0 (x : A.V) + (-(A.ρ g0 (x : A.V))))) :=
      ((A.cont (x : A.V)).add continuous_const).tendsto g0
    rwa [add_neg_cancel] at h1
  filter_upwards [hc hU] with g hg
  obtain ⟨t, ht, he⟩ := hg
  rw [actQ_mk, actQ_mk]
  refine (Submodule.Quotient.eq _).2 ((mem_smul_top _ _).2 ⟨⟨t, ht⟩, Subtype.ext ?_⟩)
  change A.ρ g (x : A.V) - A.ρ g0 (x : A.V) = ϖ ^ r • t
  rw [sub_eq_add_neg]
  exact he.symm

theorem act_locConst (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O)
    (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (hϖ : Irreducible ϖ) (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (m : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) :
    IsLocallyConstant fun g => actQ LA _ hI g m :=
  act_lc A LA ϖ r hI (GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hG A LA ϖ hϖ).2.1 m

section Core
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]

set_option maxHeartbeats 1000000 in

theorem dual_core (PD : PeriodData G Qp K₀ K B BdR) (hTop : TopInj PD)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] (hG : GoodO (Qp := Qp) LL O)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (A A' : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hdual : IsDualLat1 PD LA LA' P)
    (hdual' : ∀ x, x ∈ LA.T ↔ ∀ y ∈ LA'.T, ∃ a : O, P x y = algebraMap O LL a)
    (ϖ : O) (hϖ : Irreducible ϖ) (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T))
    (hFM : Finite (O ⧸ Ideal.span {ϖ ^ r}))
    (hFW : Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)))
    (hFW' : Finite (↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)))
    (N : ℕ) (hlO : (N : O) ∈ Ideal.span {ϖ ^ r}) (χ : G →* (ZMod N)ˣ)
    (ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) (hψ1 : ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0)
    (hψ2 : ∀ ψ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, ∃ o, ∀ x, ψ x = ψ₀ (o * x))
    (u : G → O) (hu : ∀ g, algebraMap O LL (u g) = ((cycLL PD LL g : LLˣ) : LL))
    (hk : ∀ g, ∃ k : ℕ, (k : ZMod N) = (χ g : ZMod N) ∧ (k : O) - u g ∈ Ideal.span {ϖ ^ r})
    (halc : ∀ m, IsLocallyConstant fun g => actQ LA _ hI g m)
    (halc' : ∀ m, IsLocallyConstant fun g => actQ LA' _ hI' g m)
    (hC : TopChars G N χ) (hL : PairLeft G N χ) (hR : PairRight G N χ) :
    (∀ S, BQ LA _ hI ≤ S → S ≤ quotientCocycles LA _ hI → ∀ c ∈ quotientCocycles LA _ hI,
      (∀ c' ∈ quotientCocycles LA' _ hI', (∀ s ∈ S, CobO PD L1 (cupQ LA LA' P ϖ r s c')) →
        CobO PD L1 (cupQ LA LA' P ϖ r c c')) → c ∈ S) ∧
    (∀ S', BQ LA' _ hI' ≤ S' → S' ≤ quotientCocycles LA' _ hI' → ∀ c' ∈ quotientCocycles LA' _ hI',
      (∀ c ∈ quotientCocycles LA _ hI, (∀ s ∈ S', CobO PD L1 (cupQ LA LA' P ϖ r c s)) →
        CobO PD L1 (cupQ LA LA' P ϖ r c c')) → c' ∈ S') := by
  obtain ⟨pm, hpm, hpl, hpr⟩ := pairing_exists LL O A.V A'.V LA.T LA'.T P ϖ hϖ.ne_zero r hdual.2 hdual'
  have hψu : ∀ g (x : O ⧸ Ideal.span {ϖ ^ r}), ψ₀ (Ideal.Quotient.mk _ (u g) * x) = (χ g : ZMod N) * ψ₀ x :=
    fun g x => char_mul _ ψ₀ (u g) _ (hk g) x
  have heq : ∀ g x y, pm (actQ LA _ hI g x) (actQ LA' _ hI' g y) = Ideal.Quotient.mk _ (u g) * pm x y := by
    intro g x y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨b, hb⟩ := (hdual.2 _).1 y.2 _ x.2
    rw [actQ_mk, actQ_mk, hpm x y b hb, ← map_mul]
    apply hpm
    change P (A.ρ g x) (A'.ρ g y) = _
    rw [hdual.1.1 g x y, hb, map_mul, hu g]
  let Pz : (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) →+
      (↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)) →+ ZMod N :=
    { toFun := fun x => ψ₀.comp (pm x).toAddMonoidHom
      map_zero' := AddMonoidHom.ext fun y => by simp
      map_add' := fun a b => AddMonoidHom.ext fun y => by simp }
  have hPz : ∀ x y, Pz x y = ψ₀ (pm x y) := fun _ _ => rfl
  have hPl : ∀ x, (∀ y, Pz x y = 0) → x = 0 := by
    intro x hx
    apply hpl
    intro y
    apply hψ1
    intro o
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [← smul_quot, ← map_smul]
    exact hx _
  have hPr : ∀ y, (∀ x, Pz x y = 0) → y = 0 := by
    intro y hy
    apply hpr
    intro x
    apply hψ1
    intro o
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [← smul_quot, ← LinearMap.smul_apply, ← map_smul]
    exact hy _
  have key : ∀ c ∈ quotientCocycles LA _ hI, ∀ c' ∈ quotientCocycles LA' _ hI', (CobO PD L1 (cupQ LA LA' P ϖ r c c') ↔
      ∀ o : O, ∃ f : G → ZMod N, IsLocallyConstant f ∧ ∀ g h,
        (χ g : ZMod N) * f h - f (g * h) + f g =
          ψ₀ (Ideal.Quotient.mk _ o * pm (c g) (actQ LA' _ hI' g (c' h)))) := by
    intro c hc c' hc'
    have hz : ∀ x : G × G, ∃ a : O, algebraMap O LL a =
        algebraMap O LL ϖ ^ r * cupQ LA LA' P ϖ r c c' x ∧
        pm (c x.1) (actQ LA' _ hI' x.1 (c' x.2)) = Ideal.Quotient.mk _ a := by
      intro x
      obtain ⟨xh, hx1, hx2⟩ := liftQ_spec LA _ (c x.1)
      obtain ⟨yh, hy1, hy2⟩ := liftQ_spec LA' _ (c' x.2)
      obtain ⟨b, hb⟩ := (hdual.2 _).1 (actT LA' x.1 yh).2 _ xh.2
      refine ⟨b, ?_, ?_⟩
      · have h0 : algebraMap O LL ϖ ≠ 0 := by
          simpa using (IsFractionRing.injective O LL).ne hϖ.ne_zero
        have h1 : cupQ LA LA' P ϖ r c c' x = (algebraMap O LL ϖ)⁻¹ ^ r * algebraMap O LL b := by
          rw [← hb]
          simp only [cupQ, ← hx1, ← hy1]
          rfl
        rw [h1, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero _ h0)]
      · rw [← hx2, ← hy2, actQ_mk]
        exact hpm _ _ _ hb
    refine (cobO_iff G Qp K₀ K B BdR PD hTop LL O hG L1 hL1 ϖ hϖ r u hu (cupQ LA LA' P ϖ r c c')
      (fun x => pm (c x.1) (actQ LA' _ hI' x.1 (c' x.2))) hz).trans ?_
    constructor
    · rintro ⟨f, hf, hf2⟩ o
      refine ⟨fun g => ψ₀ (Ideal.Quotient.mk _ o * f g), hf.comp (fun y => ψ₀ (Ideal.Quotient.mk _ o * y)), fun g h => ?_⟩
      have h1 := hf2 g h
      simp only at h1
      rw [← h1, ← hψu, ← map_sub, ← map_add]
      congr 1
      ring
    · intro hall
      refine cob_of_chars hC _ hlO u hk (fun x => pm (c x.1) (actQ LA' _ hI' x.1 (c' x.2))) ?_ ?_ ?_
      · rw [IsLocallyConstant.iff_eventually_eq]
        intro x
        have h1 := (continuous_fst.tendsto x).eventually (hc.1.eventually_eq x.1)
        have h2 := (continuous_fst.tendsto x).eventually ((halc' (c' x.2)).eventually_eq x.1)
        have h3 := (continuous_snd.tendsto x).eventually (hc'.1.eventually_eq x.2)
        filter_upwards [h1, h2, h3] with y a1 a2 a3
        simp only [a1, a3, a2]
      · intro g h k
        simp only
        rw [← heq, actQ_mul, hc.2 g h, hc'.2 h k, map_add, map_add, map_add, LinearMap.add_apply]
        ring
      · intro ψ
        obtain ⟨o, ho⟩ := hψ2 ψ
        obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
        obtain ⟨f, hf, hf2⟩ := hall o
        exact ⟨f, hf, fun g h => by rw [hf2, ho]⟩
  refine ⟨?_, ?_⟩
  · intro S hBS hSZ c hc hyp
    refine hL _ (fun g => (actQ LA _ hI g).toAddMonoidHom)
      (fun m => actQ_one LA _ hI m) (fun g h m => actQ_mul LA _ hI g h m) halc
      _ (fun g => (actQ LA' _ hI' g).toAddMonoidHom)
      (fun m => actQ_one LA' _ hI' m) (fun g h m => actQ_mul LA' _ hI' g h m) halc'
      Pz hPl hPr (fun g x y => ?_) S.toAddSubgroup ?_ (fun s hs => hSZ hs) c hc ?_
    · simp only [hPz, LinearMap.toAddMonoidHom_coe]
      rw [heq, hψu]
    · intro m
      exact hBS ⟨m, rfl⟩
    · intro c' hc' hs
      have hcob : CobO PD L1 (cupQ LA LA' P ϖ r c c') := by
        refine hyp c' hc' fun s hsS => (key s (hSZ hsS) c' hc').2 fun o => ?_
        obtain ⟨f, hf, hf2⟩ := hs (o • s) (S.smul_mem o hsS)
        refine ⟨f, hf, fun g h => ?_⟩
        rw [hf2, hPz, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_quot]
        rfl
      obtain ⟨f, hf, hf2⟩ := (key c hc c' hc').1 hcob 1
      refine ⟨f, hf, fun g h => ?_⟩
      rw [hf2, map_one, one_mul]
      rfl
  · intro S hBS hSZ c' hc' hyp
    refine hR _ (fun g => (actQ LA _ hI g).toAddMonoidHom)
      (fun m => actQ_one LA _ hI m) (fun g h m => actQ_mul LA _ hI g h m) halc
      _ (fun g => (actQ LA' _ hI' g).toAddMonoidHom)
      (fun m => actQ_one LA' _ hI' m) (fun g h m => actQ_mul LA' _ hI' g h m) halc'
      Pz hPl hPr (fun g x y => ?_) S.toAddSubgroup ?_ (fun s hs => hSZ hs) c' hc' ?_
    · simp only [hPz, LinearMap.toAddMonoidHom_coe]
      rw [heq, hψu]
    · intro m
      exact hBS ⟨m, rfl⟩
    · intro c hc hs
      have hcob : CobO PD L1 (cupQ LA LA' P ϖ r c c') := by
        refine hyp c hc fun s hsS => (key c hc s (hSZ hsS)).2 fun o => ?_
        obtain ⟨f, hf, hf2⟩ := hs (o • s) (S.smul_mem o hsS)
        refine ⟨f, hf, fun g h => ?_⟩
        rw [hf2, hPz]
        change ψ₀ (pm (c g) (actQ LA' _ hI' g (o • s h))) = _
        rw [map_smul, map_smul, smul_quot]
      obtain ⟨f, hf, hf2⟩ := (key c hc c' hc').1 hcob 1
      refine ⟨f, hf, fun g h => ?_⟩
      rw [hf2, map_one, one_mul]
      rfl

end Core

set_option maxHeartbeats 1000000 in

theorem dualQ_of_topInj : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l),
    TopInj ((D.loc l).PD K) → DualQ ((D.loc l).PD K) := by
  intro hT D l _ K hTop LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' P hdual ϖ hϖ r hI hI'
  have hG0 : ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL := hG.1
  haveI hDom : IsDomain O := hG0.choose
  haveI hDVR : IsDiscreteValuationRing O := hG0.choose_spec.1
  haveI hFrac : IsFractionRing O LL := hG0.choose_spec.2
  have h50 := GlobalTheory.CompanionTheory.GoodCoeff.goodO_structure l LL O hG ϖ hϖ
  have hFin := h50.2.1
  have hle : (l : O) ∈ Ideal.span {ϖ} := h50.2.2.2.1.choose_spec.1
  have hInt := h50.2.2.2.2.2
  have hdual' := (GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hG A LA ϖ hϖ).2.2.2.2 A' LA' P hdual
  have hF1 := finite_quot O A.V LA.T ϖ r hFin LA.fg
  have hF2 := finite_quot O A'.V LA'.T ϖ r hFin LA'.fg
  have hlp : l.Prime := Fact.out
  have hn : 0 < r + 1 := Nat.succ_pos r
  have hlO : ((l ^ (r + 1) : ℕ) : O) ∈ Ideal.span {ϖ ^ r} := by
    refine (Ideal.mem_span_singleton.1 hle).elim fun b hb => Ideal.mem_span_singleton.2 ?_
    rw [Nat.cast_pow, hb, mul_pow, pow_succ ϖ r]
    exact ⟨ϖ * b ^ (r + 1), by ring⟩
  let w : ↥(GK K) →* ℤ_[l] := GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo.chiInt (D.loc l) K
  let χ : ↥(GK K) →* (ZMod (l ^ (r + 1)))ˣ := ((PadicInt.toZModPow (r + 1)).toMonoidHom.comp w).toHomUnits
  have hcomp : ∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧
      PadicInt.toZModPow (r + 1) u = (χ g : ZMod (l ^ (r + 1))) := fun g => ⟨w g, rfl, rfl⟩
  have hu0 : ∀ g, ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (w g : ℚ_[l]) := fun g => hInt (w g)
  refine (GlobalTheory.CompanionTheory.LocDual.GenChar.exists_generating_character O ϖ hϖ r (l ^ (r + 1)) (pow_pos hlp.pos _) hF1.1 hlO).elim fun ψ₀ hψ => ?_
  exact dual_core ((D.loc l).PD K) hTop hG L1 hL1 A A' LA LA' P hdual (fun x => hdual'.2 x) ϖ hϖ r hI hI'
    hF1.1 hF1.2 hF2.2 (l ^ (r + 1)) hlO χ ψ₀ hψ.1 hψ.2 (fun g => (hu0 g).choose)
    (fun g => (hu0 g).choose_spec)
    (fun g => exists_nat_rep (IsFractionRing.injective O LL) hInt _ (r + 1) hlO (w g) _ (hu0 g).choose_spec)
    (act_locConst D l K LL O hG A LA ϖ hϖ r hI) (act_locConst D l K LL O hG A' LA' ϖ hϖ r hI')
    (GlobalTheory.CompanionTheory.LocDual.TopCoh.coboundary_of_characters_GK hT D l K (r + 1) χ hn hcomp) (GlobalTheory.CompanionTheory.LocDual.Pair.double_annihilator hT D l K (r + 1) χ hn hcomp)
    (GlobalTheory.T.cyclotomic_twist_finite_module_coboundary hT D l K (r + 1) χ hn hcomp)

end GlobalTheory.CompanionTheory.LocDual.Q
