import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties

noncomputable section

namespace GlobalTheory.TateFin

section Core

open GlobalTheory.TateTop GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift ReciprocityTheory.Gal ReciprocityTheory.Neutral.Bridge

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem cob_of_cob_ambient [CompactSpace G] {χ : G →* ℤ_[l]ˣ} {c : G × G → ℤ_[l]}
    (h : ∀ r, Gen χ r c) {D : Type} [AddCommGroup D] [Module ℤ_[l] D]
    (htor : ∀ a : D, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) (W : Submodule ℤ_[l] D) [Finite W] {n : ℕ}
    (hW : ∀ m : W, (l : ℤ_[l]) ^ n • m = 0) {z : G × G → W} (hz : IsCoc χ z) {b : G → D}
    (hb : IsLocallyConstant b) (hzb : ∀ p, (z p : D) = cob χ b p) :
    ∃ b' : G → W, IsLocallyConstant b' ∧ ∀ p, z p = cob χ b' p := by
  obtain ⟨x, b', hb', hx⟩ := (h n W hW).2.1 z hz
  have hb2 : IsLocallyConstant fun g => b g - (b' g : D) := hb.sub (hb'.comp _)
  obtain ⟨r, hf, hM⟩ := finite_span htor (hb2.range_finite.insert (x : D))
  have h3 := (h r _ hM).2.2 ⟨x, Submodule.subset_span (Set.mem_insert _ _)⟩
    (fun g => ⟨b g - (b' g : D), Submodule.subset_span (Set.mem_insert_of_mem _ ⟨g, rfl⟩)⟩)
    (IsLocallyConstant.desc _ Subtype.val hb2 Subtype.val_injective)
    fun p => Subtype.ext (by
      have e := congrArg Subtype.val (hx p)
      rw [hzb p] at e
      simp only [cob, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul] at e ⊢
      linear_combination (norm := module) -e)
  have h4 : x = 0 := Subtype.ext (by have h5 := congrArg Subtype.val h3; exact h5)
  exact ⟨b', hb', fun p => by rw [hx p, h4, smul_zero, zero_add]⟩

theorem nondeg_of_perfect {q : ℕ} [NeZero q] (χ : G →* (ZMod q)ˣ) {X N : Type} [AddCommGroup X]
    [AddCommGroup N] [Module (ZMod q) X] [Module (ZMod q) N] [Finite X] [Finite N]
    [TopologicalSpace N] [DiscreteTopology N] (a : G → X → X)
    (rho : Representation (ZMod q) G N) (hrho : ContAction rho) (hD : DualityFor χ rho hrho)
    (β : X →ₗ[ZMod q] N →ₗ[ZMod q] ZMod q)
    (he : ∀ g x y, β (a g x) (rho g y) = (χ g : ZMod q) * β x y)
    (h1 : Function.Injective β) (h2 : Function.Injective β.flip) :
    (∀ c : G → X, IsLocallyConstant c → (∀ g h, c (g * h) = c g + a g (c h)) →
      (∀ c' : G → N, IsLocallyConstant c' → (∀ g h, c' (g * h) = c' g + rho g (c' h)) →
        ∃ b : G → ZMod q, IsLocallyConstant b ∧
          ∀ g h, β (c g) (rho g (c' h)) = (χ g : ZMod q) * b h - b (g * h) + b g) →
      ∃ x, ∀ g, c g = a g x - x) ∧
    (∀ c' : G → N, IsLocallyConstant c' → (∀ g h, c' (g * h) = c' g + rho g (c' h)) →
      (∀ c : G → X, IsLocallyConstant c → (∀ g h, c (g * h) = c g + a g (c h)) →
        ∃ b : G → ZMod q, IsLocallyConstant b ∧
          ∀ g h, β (c g) (rho g (c' h)) = (χ g : ZMod q) * b h - b (g * h) + b g) →
      ∃ y, ∀ g, c' g = rho g y - y) := by
  have := finite_dual (n := q) (M := X)
  have := finite_dual (n := q) (M := N)
  have hbij : Function.Bijective β := h1.bijective_of_nat_card_le
    ((card_dual_le (n := q) (M := N)).trans ((Nat.card_le_card_of_injective _ h2).trans
      (card_dual_le (n := q) (M := X))))
  let e : X ≃ₗ[ZMod q] TDual (ZMod q) N := LinearEquiv.ofBijective β hbij
  have hea : ∀ g x, e (a g x) = twDual χ rho g (e x) := fun g x => TDual.ext fun m => by
    change β (a g x) m = (χ g : ZMod q) * β x (rho g⁻¹ m)
    rw [← he, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hcup : ∀ (y : Z1 ((twDual χ rho).comp (MonoidHom.id G))) (x : Z1 (rho.comp (MonoidHom.id G))),
      (∃ b : G → ZMod q, IsLocallyConstant b ∧
          ∀ g h, y.1 g (rho g (x.1 h)) = (χ g : ZMod q) * b h - b (g * h) + b g) →
      cupH1H1TwistedDual χ rho (MonoidHom.id G) (hrho.comp' continuous_id) (Submodule.Quotient.mk y)
        (Submodule.Quotient.mk x) = 0 := by
    rintro y x ⟨b, hb, hbe⟩
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨b, hb.continuous, ?_⟩
    funext p
    exact (hbe p.1 p.2).symm
  refine ⟨fun c hc hcc H => ?_, fun c' hc' hcc' H => ?_⟩
  · let y : Z1 ((twDual χ rho).comp (MonoidHom.id G)) := ⟨fun g => e (c g),
      (hc.comp e).continuous, fun g h => by
        beta_reduce
        rw [hcc, map_add, hea]; rfl⟩
    have h0 : (Submodule.Quotient.mk y : H1 ((twDual χ rho).comp (MonoidHom.id G))) = 0 := by
      apply hD.2.2.1.1
      rw [map_zero]
      refine LinearMap.ext fun x => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact hcup y x (H x.1 ((IsLocallyConstant.iff_continuous _).2 x.2.1) x.2.2)
    obtain ⟨φ, hφ⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    obtain ⟨x, rfl⟩ := e.surjective φ
    refine ⟨x, fun g => e.injective ?_⟩
    rw [map_sub, hea]
    exact hφ g
  · let x : Z1 (rho.comp (MonoidHom.id G)) := ⟨c', hc'.continuous, hcc'⟩
    have h0 : (Submodule.Quotient.mk x : H1 (rho.comp (MonoidHom.id G))) = 0 := by
      apply hD.2.2.2.1.1
      rw [map_zero]
      refine LinearMap.ext fun y => ?_
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      refine hcup y x ?_
      have hy : ∀ g, β (e.symm (y.1 g)) = y.1 g := fun g => e.apply_symm_apply (y.1 g)
      obtain ⟨b, hb, hbe⟩ := H (fun g => e.symm (y.1 g))
        (((IsLocallyConstant.iff_continuous _).2 y.2.1).comp e.symm) fun g h => e.injective (by
          rw [map_add, hea, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
          exact y.2.2 g h)
      refine ⟨b, hb, fun g h => ?_⟩
      rw [← hbe, hy]
      rfl
    have h3 := (Submodule.Quotient.mk_eq_zero _).1 h0
    exact (mem_coboundaries1 _ _).1 h3

theorem nondeg_torsion [CompactSpace G] [ContinuousMul G] {χ : G →* ℤ_[l]ˣ}
    (hχ : Continuous fun g => (χ g : ℤ_[l]))
    (hT : ∀ (k : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ (k + 1))) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ (k + 1))) G M)
      (hrho : ContAction rho), DualityFor (redChar χ (k + 1)) rho hrho)
    {X N D : Type} [AddCommGroup X] [AddCommGroup N] [AddCommGroup D] [Module ℤ_[l] D] [Finite X]
    [Finite N] (htor : ∀ a : D, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) {n : ℕ}
    (hX : ∀ x : X, l ^ n • x = 0) (hN : ∀ y : N, l ^ n • y = 0) (a : G → X → X) (a' : G → N →+ N)
    (h1 : ∀ y, a' 1 y = y) (hm : ∀ g h y, a' (g * h) y = a' g (a' h y))
    (hlc : ∀ y, IsLocallyConstant fun g => a' g y) (β : X →+ N →+ D)
    (he : ∀ g x y, β (a g x) (a' g y) = (χ g : ℤ_[l]) • β x y) {s : D} (hs : s ≠ 0)
    (hβ1 : ∀ x, x ≠ 0 → ∃ y, β x y = s) (hβ2 : ∀ y, y ≠ 0 → ∃ x, β x y = s) :
    (∀ c : G → X, IsLocallyConstant c → (∀ g h, c (g * h) = c g + a g (c h)) →
      (∀ c' : G → N, IsLocallyConstant c' → (∀ g h, c' (g * h) = c' g + a' g (c' h)) →
        ∃ b : G → D, IsLocallyConstant b ∧ ∀ p : G × G, β (c p.1) (a' p.1 (c' p.2)) = cob χ b p) →
      ∃ x, ∀ g, c g = a g x - x) ∧
    (∀ c' : G → N, IsLocallyConstant c' → (∀ g h, c' (g * h) = c' g + a' g (c' h)) →
      (∀ c : G → X, IsLocallyConstant c → (∀ g h, c (g * h) = c g + a g (c h)) →
        ∃ b : G → D, IsLocallyConstant b ∧ ∀ p : G × G, β (c p.1) (a' p.1 (c' p.2)) = cob χ b p) →
      ∃ y, ∀ g, c' g = a' g y - y) := by
  obtain ⟨c₀, hc₀⟩ := exists_gen_all hχ fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχ
      (hT r (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χ (r + 1)))
        (contAction_charRep _ ((continuous_toZModPow _).comp hχ))).1
      fun M _ _ _ _ _ rho hrho => (hT r M rho hrho).2.2.2.2
  obtain ⟨m, hWf, hWm⟩ := finite_span htor
    ((Set.finite_range fun p : X × N => β p.1 p.2).insert s)
  set W := Submodule.span ℤ_[l] (insert s (Set.range fun p : X × N => β p.1 p.2)) with hWdef
  have hsW : s ∈ W := Submodule.subset_span (Set.mem_insert _ _)
  have hβW : ∀ x y, β x y ∈ W := fun x y =>
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(x, y), rfl⟩)
  have hW : ∀ w : W, (l : ℤ_[l]) ^ (n + m + 1) • w = 0 := fun w => by
    rw [show n + m + 1 = (n + 1) + m by ring, pow_add, mul_smul, hWm, smul_zero]
  have : NeZero (l ^ (n + m + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ (n + m + 1))) X) := ⟨AddCommGroup.zmodModule fun x => by
    rw [show n + m + 1 = (m + 1) + n by ring, pow_add, mul_smul, hX, smul_zero]⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ (n + m + 1))) N) := ⟨AddCommGroup.zmodModule fun x => by
    rw [show n + m + 1 = (m + 1) + n by ring, pow_add, mul_smul, hN, smul_zero]⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ (n + m + 1))) W) := ⟨AddCommGroup.zmodModule fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow, hW]⟩
  obtain ⟨ψ, hψ⟩ := exists_dual_ne_zero (n := l ^ (n + m + 1)) (x := (⟨s, hsW⟩ : W))
    fun h => hs (congrArg Subtype.val h)
  have hψs : ∀ (u : ℤ_[l]) (w : W), ψ (u • w) = PadicInt.toZModPow (n + m + 1) u * ψ w := fun u w => by
    rw [smul_eq_val hW, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  let : TopologicalSpace N := ⊥
  have : DiscreteTopology N := ⟨rfl⟩
  let rho : Representation (ZMod (l ^ (n + m + 1))) G N :=
    { toFun := fun g => (a' g).toZModLinearMap _
      map_one' := LinearMap.ext h1
      map_mul' := fun g h => LinearMap.ext (hm g h) }
  have hcont : Continuous fun p : G × N => a' p.1 p.2 :=
    continuous_prod_of_discrete_right.2 fun y => (hlc y).continuous
  let β' : X →ₗ[ZMod (l ^ (n + m + 1))] N →ₗ[ZMod (l ^ (n + m + 1))] ZMod (l ^ (n + m + 1)) :=
    (AddMonoidHom.mk' (fun x => (AddMonoidHom.mk' (fun y => ψ ⟨β x y, hβW x y⟩) fun y y' => by
      rw [← map_add]; exact congrArg ψ (Subtype.ext (map_add _ _ _))).toZModLinearMap _)
      fun x x' => LinearMap.ext fun y => by
        change ψ ⟨β (x + x') y, _⟩ = ψ ⟨β x y, _⟩ + ψ ⟨β x' y, _⟩
        rw [← map_add]
        exact congrArg ψ (Subtype.ext (by simp))).toZModLinearMap _
  have hβ' : ∀ x y, β' x y = ψ ⟨β x y, hβW x y⟩ := fun _ _ => rfl
  have key : ∀ (c : G → X) (c' : G → N), IsLocallyConstant c → (∀ g h, c (g * h) = c g + a g (c h)) →
      IsLocallyConstant c' → (∀ g h, c' (g * h) = c' g + a' g (c' h)) →
      (∃ b : G → D, IsLocallyConstant b ∧ ∀ p : G × G, β (c p.1) (a' p.1 (c' p.2)) = cob χ b p) →
      ∃ b : G → ZMod (l ^ (n + m + 1)), IsLocallyConstant b ∧ ∀ g h, β' (c g) (rho g (c' h)) =
        (redChar χ (n + m + 1) g : ZMod (l ^ (n + m + 1))) * b h - b (g * h) + b g := by
    rintro c c' hc hcc hc' hcc' ⟨b, hb, hbe⟩
    have hl : IsLocallyConstant fun p : G × G => a' p.1 (c' p.2) :=
      (IsLocallyConstant.iff_continuous _).2
        (hcont.comp (continuous_fst.prodMk (hc'.continuous.comp continuous_snd)))
    obtain ⟨b', hb', hbe'⟩ := cob_of_cob_ambient hc₀ htor W hW
      (z := fun p => ⟨β (c p.1) (a' p.1 (c' p.2)), hβW _ _⟩)
      ⟨(hc.comp_continuous continuous_fst).comp₂ hl fun x y => (⟨β x y, hβW x y⟩ : W),
        fun g h k => Subtype.ext (by
          change (χ g : ℤ_[l]) • β (c h) (a' h (c' k)) - β (c (g * h)) (a' (g * h) (c' k)) +
            β (c g) (a' g (c' (h * k))) - β (c g) (a' g (c' h)) = 0
          rw [← he, hcc, hcc', hm]
          simp only [map_add, AddMonoidHom.add_apply]
          abel)⟩ hb hbe
    refine ⟨fun g => ψ (b' g), hb'.comp ψ, fun g h => ?_⟩
    have e := congrArg ψ (hbe' (g, h))
    rw [cob, map_add, map_sub, hψs] at e
    exact e
  obtain ⟨H1, H2⟩ := nondeg_of_perfect (redChar χ (n + m + 1)) a rho hcont (hT (n + m) N rho hcont) β'
    (fun g x y => by
      rw [hβ', hβ']
      exact (congrArg ψ (Subtype.ext (he g x y))).trans (hψs _ ⟨_, hβW x y⟩))
    ((injective_iff_map_eq_zero _).2 fun x hx => by
      by_contra h0
      obtain ⟨y, hy⟩ := hβ1 x h0
      have e := LinearMap.congr_fun hx y
      rw [hβ'] at e
      simp only [hy] at e
      exact hψ e)
    ((injective_iff_map_eq_zero _).2 fun y hy => by
      by_contra h0
      obtain ⟨x, hx⟩ := hβ2 y h0
      have e := LinearMap.congr_fun hy x
      rw [LinearMap.flip_apply, hβ'] at e
      simp only [hx] at e
      exact hψ e)
  exact ⟨fun c hc hcc H => H1 c hc hcc fun c' hc' hcc' => key c c' hc hcc hc' hcc' (H c' hc' hcc'),
    fun c' hc' hcc' H => H2 c' hc' hcc' fun c hc hcc => key c c' hc hcc hc' hcc' (H c hc hcc)⟩

end Core

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Lat

variable {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra O LL] [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']

omit [IsDiscreteValuationRing O] in
theorem mem_pow_smul_top (T : Submodule O V) {ϖ : O} (hϖ : ϖ ≠ 0) (r : ℕ) (t : T) :
    t ∈ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O T) ↔ (algebraMap O LL ϖ)⁻¹ ^ r • (t : V) ∈ T := by
  have hπ : algebraMap O LL ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 hϖ
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    rw [Submodule.coe_smul, ← algebraMap_smul LL (ϖ ^ r), smul_smul, map_pow, ← mul_pow, inv_mul_cancel₀ hπ,
      one_pow, one_smul]
    exact y.2
  · intro h
    refine ⟨⟨_, h⟩, trivial, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul LL, smul_smul, map_pow, ← mul_pow, mul_inv_cancel₀ hπ,
      one_pow, one_smul]

theorem exists_pair (T : Submodule O V) (T' : Submodule O V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : ∀ x, (∀ y ∈ T', ∃ a : O, m x y = algebraMap O LL a) → x ∈ T) {ϖ : O} (hϖ : Irreducible ϖ)
    (r : ℕ) (t : T) (ht : t ∉ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O T)) :
    ∃ y : T', (algebraMap O LL ϖ)⁻¹ ^ r * m t y = (algebraMap O LL ϖ)⁻¹ := by
  rw [mem_pow_smul_top (LL := LL) T hϖ.ne_zero] at ht
  have h1 := mt (h _) ht
  push_neg at h1
  obtain ⟨y, hy, hu⟩ := h1
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hu
  set u := (algebraMap O LL ϖ)⁻¹ ^ r * m t y with hudef
  have hu0 : u ≠ 0 := fun h0 => hu 0 (by rw [h0, map_zero])
  obtain ⟨w, hw⟩ := (ValuationRing.isInteger_or_isInteger O u).resolve_left fun ⟨b, hb⟩ => hu b hb.symm
  have hwu : ¬ IsUnit w := by
    rintro ⟨v, rfl⟩
    refine hu (↑v⁻¹) ?_
    rw [← inv_inv u, ← hw]
    exact (eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm
  have hd : ϖ ∣ w := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hwu
  obtain ⟨o, rfl⟩ := hd
  refine ⟨o • ⟨y, hy⟩, ?_⟩
  rw [Submodule.coe_smul, ← algebraMap_smul LL, map_smul, smul_eq_mul, mul_left_comm, ← hudef]
  rw [map_mul] at hw
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← mul_assoc, hw, inv_mul_cancel₀ hu0]

omit [IsDiscreteValuationRing O] in

theorem exists_quot_pairing (T : Submodule O V) (T' : Submodule O V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : ∀ x ∈ T, ∀ y ∈ T', ∃ a : O, m x y = algebraMap O LL a) {ϖ : O} (hϖ : ϖ ≠ 0) (r : ℕ)
    (S : Submodule O LL) (hS : S = LinearMap.range (Algebra.linearMap O LL)) :
    ∃ β : (T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O T)) →+
        (T' ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O T')) →+ LL ⧸ S,
      ∀ (t : T) (t' : T'), β (Submodule.Quotient.mk t) (Submodule.Quotient.mk t') =
        Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r * m t t') := by
  let B : T →ₗ[O] T' →ₗ[O] LL ⧸ S := LinearMap.mk₂ O
    (fun t t' => Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r * m t t'))
    (fun t u t' => by
      rw [Submodule.coe_add, map_add, LinearMap.add_apply, mul_add, Submodule.Quotient.mk_add])
    (fun c t t' => by
      rw [Submodule.coe_smul, ← algebraMap_smul LL c (t : V), map_smul, LinearMap.smul_apply,
        algebraMap_smul, mul_smul_comm, Submodule.Quotient.mk_smul])
    (fun t t' u' => by rw [Submodule.coe_add, map_add, mul_add, Submodule.Quotient.mk_add])
    (fun c t t' => by
      rw [Submodule.coe_smul, ← algebraMap_smul LL c (t' : V'), map_smul,
        algebraMap_smul, mul_smul_comm, Submodule.Quotient.mk_smul])
  let β := LinearMap.liftQ₂ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O T)
    (Ideal.span {ϖ ^ r} • ⊤ : Submodule O T') B
    (fun t ht => LinearMap.ext fun t' => by
      obtain ⟨a, ha⟩ := h _ ((mem_pow_smul_top (LL := LL) T hϖ r t).1 ht) t' t'.2
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at ha
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [hS, ha]
      exact ⟨a, rfl⟩)
    (fun t' ht' => LinearMap.ext fun t => by
      obtain ⟨a, ha⟩ := h t t.2 _ ((mem_pow_smul_top (LL := LL) T' hϖ r t').1 ht')
      rw [map_smul, smul_eq_mul] at ha
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [hS, ha]
      exact ⟨a, rfl⟩)
  exact ⟨AddMonoidHom.mk' (fun x => (β x).toAddMonoidHom) fun x y => by rw [map_add]; rfl,
    fun _ _ => rfl⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_quot (T : Submodule O V) (hT : T.FG) (J : Ideal O) [Finite (O ⧸ J)] :
    Finite (T ⧸ (J • ⊤ : Submodule O T)) := by
  have : Module.Finite O T := Module.Finite.iff_fg.2 hT
  have : Module.Finite (O ⧸ J) (T ⧸ (J • ⊤ : Submodule O T)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact Module.finite_of_finite (O ⧸ J)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in
theorem actQ_one {G : Type} [Group G] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (I : Submodule O L.T) (hI : StableSub L I) (y : L.T ⧸ I) : actQ L I hI 1 y = y := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have h : actT L 1 y = y := Subtype.ext (LinearMap.congr_fun (map_one ρ) (y : V))
  exact congrArg Submodule.Quotient.mk h

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in
theorem actQ_mul {G : Type} [Group G] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (I : Submodule O L.T) (hI : StableSub L I) (g h : G) (y : L.T ⧸ I) :
    actQ L I hI (g * h) y = actQ L I hI g (actQ L I hI h y) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have h : actT L (g * h) y = actT L g (actT L h y) :=
    Subtype.ext (LinearMap.congr_fun (map_mul ρ g h) (y : V))
  exact congrArg Submodule.Quotient.mk h

theorem actQ_locallyConstant {G Qp : Type} [Group G] [TopologicalSpace G] [Field Qp] [Algebra Qp LL]
    [TopologicalSpace LL] [IsTopologicalRing LL] (hopen : IsOpen (Set.range (algebraMap O LL)))
    (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ) {ϖ : O} (hϖ : ϖ ≠ 0) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O L.T))
    (y : L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O L.T)) :
    IsLocallyConstant fun g => actQ L _ hI g y := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  refine ⟨(fun g => (algebraMap O LL ϖ)⁻¹ ^ r • (A.ρ g y - A.ρ g₀ y)) ⁻¹' (L.T : Set A.V),
    (Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen L.T L.fg L.span).preimage
      (((A.cont _).sub continuous_const).const_smul _), by simp, fun g hg => ?_⟩
  exact (Submodule.Quotient.eq _).2
    ((mem_pow_smul_top (LL := LL) L.T hϖ r (actT L g y - actT L g₀ y)).2 hg)

end Lat

set_option maxHeartbeats 6400000 in
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop Formalism.MainNotions.BlochKatoDuality.Br in

theorem tate_pairing_nondegenerate : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ c ∈ quotientCocycles LA _ hI, (∀ c' ∈ quotientCocycles LA' _ hI', CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c ∈ BQ LA _ hI) ∧ (∀ c' ∈ quotientCocycles LA' _ hI', (∀ c ∈ quotientCocycles LA _ hI, CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c' ∈ BQ LA' _ hI') := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm ϖ hϖ r hI hI'
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  have hcpt : CompactSpace (GK K) := Φ.symm.surjective.compactSpace hΦ1
  let χ : ↥(GK K) →* ℤ_[l]ˣ := χZ.comp Φ.toMonoidHom
  let e : Formalism.GaloisCohomology.GK l K.1 ≃ₜ* ↥(GK K) :=
    { Φ.symm with continuous_toFun := hΦ1, continuous_invFun := hΦ2 }
  have hD : ∀ (k : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ (k + 1))) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M]
      (rho : Representation (ZMod (l ^ (k + 1))) ↥(GK K) M) (hrho : ReciprocityTheory.Gal.ContAction rho),
      ReciprocityTheory.Neutral.Bridge.DualityFor (redChar χ (k + 1)) rho hrho := by
    intro k M _ _ _ _ _ rho hrho
    refine ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp e _ hrho ?_
    have h1 : (redChar χ (k + 1)).comp (e : Formalism.GaloisCohomology.GK l K.1 →* ↥(GK K)) =
        Formalism.GaloisCohomology.cycK l K.1 (k + 1) :=
      MonoidHom.ext fun g => congrArg (Formalism.GaloisCohomology.cycK l K.1 (k + 1)) (Φ.apply_symm_apply g)
    rw [h1]
    exact hT l K.1 K.2 (k + 1) M _ (Nat.succ_pos _) (ReciprocityTheory.Neutral.Bridge.contAction_comp e hrho)
  obtain ⟨ι, hι⟩ := exists_ringHom hO
  let : Module ℤ_[l] (LL ⧸ L1.T) := Module.compHom _ ι
  have hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x) := fun a x => by
    rw [← hι, ← Algebra.smul_def]
    rfl
  have htor : ∀ x : LL ⧸ L1.T, ∃ n : ℕ, (l : ℤ_[l]) ^ n • x = 0 := fun x => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hO x
    refine ⟨n, ?_⟩
    rw [hs, Submodule.Quotient.mk_eq_zero, hL1]
    simpa using hn 1
  have hχL : ∀ g, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap ℚ_[l] LL (χ g : ℤ_[l]) := fun g => by
    have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    change algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) = _
    rw [← h1]
    rfl
  have hact : ∀ g (x : LL ⧸ L1.T), repD L1 g x = (χ g : ℤ_[l]) • x := fun g x => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hs, ← hχL]
    rfl
  obtain ⟨n, hn⟩ := exists_pow_smul_mem hO ((algebraMap O LL ϖ)⁻¹ ^ r)
  have hfin := (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO).2.2.1 n
  obtain ⟨⟨hDom, hDVR, hFr⟩, -, -, htr, hopen⟩ := hO
  have hinj := IsFractionRing.injective O LL
  have hπ : algebraMap O LL ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hln : ((l : ℕ) : O) ^ n ∈ Ideal.span {ϖ ^ r} := by
    obtain ⟨o, ho⟩ := hn 1
    refine Ideal.mem_span_singleton'.2 ⟨o, hinj ?_⟩
    rw [map_mul, ho, mul_assoc, map_pow (algebraMap O LL), ← mul_pow, inv_mul_cancel₀ hπ]
    simp
  have : Finite (O ⧸ Ideal.span {ϖ ^ r}) := Finite.of_surjective _
    (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).2 hln))
  have := finite_quot LA.T LA.fg (Ideal.span {ϖ ^ r})
  have := finite_quot LA'.T LA'.fg (Ideal.span {ϖ ^ r})
  have hkill : ∀ (B : GRep ↥(GK K) ℚ_[l] LL O) (L : Lattice (O := O) B.ρ)
      (x : L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O L.T)), l ^ n • x = 0 := fun B L x => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hln trivial
  obtain ⟨β, hβ⟩ := exists_quot_pairing LA.T LA'.T m (fun x hx y hy => (hm.2 y).1 hy x hx)
    hϖ.ne_zero r L1.T hL1
  have hcup : ∀ (g : ↥(GK K)) x y, (Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r *
      m (liftQ LA _ x) (A'.ρ g (liftQ LA' _ y))) : LL ⧸ L1.T) = β x (actQ LA' _ hI' g y) := by
    intro g x y
    conv_rhs => rw [← (Submodule.Quotient.mk_surjective _ x).choose_spec,
      ← (Submodule.Quotient.mk_surjective _ y).choose_spec]
    exact (hβ _ (actT LA' g _)).symm
  have hcob : ∀ (c : ↥(GK K) → _) (c' : ↥(GK K) → _), CobO (P.PD K) L1 (fun x =>
      (algebraMap O LL ϖ)⁻¹ ^ r * m (liftQ LA _ (c x.1)) (A'.ρ x.1 (liftQ LA' _ (c' x.2)))) →
      ∃ b : ↥(GK K) → LL ⧸ L1.T, IsLocallyConstant b ∧
        ∀ p : ↥(GK K) × ↥(GK K), β (c p.1) (actQ LA' _ hI' p.1 (c' p.2)) = GlobalTheory.TateTop.cob χ b p := by
    rintro c c' ⟨b, hb, hbe⟩
    refine ⟨b, hb.1, fun p => ?_⟩
    rw [← hcup, GlobalTheory.TateTop.cob, ← hact]
    exact (congrFun hbe p).symm
  have he : ∀ g x y, β (actQ LA _ hI g x) (actQ LA' _ hI' g y) = (χ g : ℤ_[l]) • β x y := by
    intro g x y
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨t', ht'⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← ht, ← ht']
    refine (hβ (actT LA g t) (actT LA' g t')).trans ?_
    rw [hβ, hs, ← hχL, mul_left_comm, ← hm.1.1]
    rfl
  have hs0 : (Submodule.Quotient.mk (algebraMap O LL ϖ)⁻¹ : LL ⧸ L1.T) ≠ 0 := fun h => by
    rw [Submodule.Quotient.mk_eq_zero, hL1] at h
    obtain ⟨o, ho⟩ := h
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one o (hinj ?_))
    rw [map_mul, map_one, show algebraMap O LL o = _ from ho, mul_inv_cancel₀ hπ]
  have hβ1 : ∀ x, x ≠ 0 → ∃ y, β x y = Submodule.Quotient.mk (algebraMap O LL ϖ)⁻¹ := fun x hx => by
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, hy⟩ := exists_pair LA.T LA'.T m
      (fun v hv => ((isDualLat1_flip (P.PD K) hm).2 v).2 hv) hϖ r t
      fun h => hx (ht.symm.trans ((Submodule.Quotient.mk_eq_zero _).2 h))
    exact ⟨Submodule.Quotient.mk y, by rw [← ht, hβ, hy]⟩
  have hβ2 : ∀ y, y ≠ 0 → ∃ x, β x y = Submodule.Quotient.mk (algebraMap O LL ϖ)⁻¹ := fun y hy => by
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, hx⟩ := exists_pair LA'.T LA.T m.flip (fun v hv => (hm.2 v).2 hv) hϖ r t
      fun h => hy (ht.symm.trans ((Submodule.Quotient.mk_eq_zero _).2 h))
    exact ⟨Submodule.Quotient.mk x, by rw [← ht, hβ]; exact congrArg _ hx⟩
  obtain ⟨H1, H2⟩ := @nondeg_torsion l _ (GK K) _ _ hcpt _ χ (hχc.comp hΦ2) hD _ _ _ _ _ _ _ _ _ htor n
    (hkill A LA) (hkill A' LA') (fun g => actQ LA _ hI g)
    (fun g => (actQ LA' _ hI' g).toAddMonoidHom) (actQ_one LA' _ hI') (actQ_mul LA' _ hI')
    (actQ_locallyConstant hopen A' LA' hϖ.ne_zero r hI') β he _ hs0 hβ1 hβ2
  refine ⟨fun c hc H => ?_, fun c' hc' H => ?_⟩
  · obtain ⟨x, hx⟩ := H1 c hc.1 hc.2 fun c' h1 h2 => hcob c c' (H c' ⟨h1, h2⟩)
    exact ⟨x, funext fun g => (hx g).symm⟩
  · obtain ⟨y, hy⟩ := H2 c' hc'.1 hc'.2 fun c h1 h2 => hcob c c' (H c ⟨h1, h2⟩)
    exact ⟨y, funext fun g => (hy g).symm⟩

end GlobalTheory.TateFin
