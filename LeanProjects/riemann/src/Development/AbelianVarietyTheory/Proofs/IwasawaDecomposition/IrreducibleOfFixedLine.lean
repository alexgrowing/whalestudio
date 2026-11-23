import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIntegralGLMulRightComplexProductSigma
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

open MeasureTheory Topology
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.SphCyclic

theorem irreducible_of_fixed_line {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : G →* (V ≃ₗᵢ[ℂ] V)) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (hsm : ∀ x, IsOpen {g | ρ g x = x}) (v : V) (hv : ∀ k ∈ K, ρ k v = v)
    (hcyc : Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤)
    (hline : ∀ x, (∀ k ∈ K, ρ k x = x) → ∃ c : ℂ, x = c • v)
    (W : Submodule ℂ V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  have hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by rw [map_mul]; rfl
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨w₀, hw₀, hw0⟩ := (Submodule.ne_bot_iff W).1 hne
  obtain ⟨g, hg⟩ : ∃ g, inner ℂ (ρ g v) w₀ ≠ 0 := by
    by_contra h
    push Not at h
    have : ∀ x ∈ Submodule.span ℂ (Set.range fun g => ρ g v), inner ℂ x w₀ = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact h g
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
    exact hw0 (inner_self_eq_zero.1 (this w₀ (hcyc ▸ Submodule.mem_top)))
  set w := ρ g⁻¹ w₀ with hw
  have hwW : w ∈ W := hW _ _ hw₀
  have hvw : inner ℂ v w ≠ 0 := by
    rw [← (ρ g).inner_map_map, hw, ← hmul, mul_inv_cancel, map_one]
    exact hg
  have hlc : IsLocallyConstant fun g : G => ρ g w := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun a => ?_
    have h1 : IsOpen {b : G | ρ (a⁻¹ * b) w = w} := (hsm w).preimage (continuous_const_mul a⁻¹)
    filter_upwards [h1.mem_nhds (show a ∈ {b : G | ρ (a⁻¹ * b) w = w} by simp)] with b hb
    rw [← mul_inv_cancel_left a b, hmul, hb]
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfin : (Set.range fun k : K => ρ k w).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  set u := ∑ y ∈ hfin.toFinset, y with hu
  have huW : u ∈ W := W.sum_mem fun y hy => by
    obtain ⟨k, rfl⟩ := hfin.mem_toFinset.1 hy
    exact hW _ _ hwW
  have hufix : ∀ k ∈ K, ρ k u = u := by
    intro k hk
    rw [hu, map_sum]
    refine Finset.sum_bij (fun y _ => ρ k y) ?_ ?_ ?_ fun _ _ => rfl
    · intro y hy
      obtain ⟨l, rfl⟩ := hfin.mem_toFinset.1 hy
      exact hfin.mem_toFinset.2 ⟨⟨k, hk⟩ * l, hmul _ _ _⟩
    · intro y _ z _ h
      exact (ρ k).injective h
    · intro y hy
      obtain ⟨l, rfl⟩ := hfin.mem_toFinset.1 hy
      refine ⟨_, hfin.mem_toFinset.2 ⟨⟨k, hk⟩⁻¹ * l, rfl⟩, ?_⟩
      show ρ k (ρ (k⁻¹ * l) w) = _
      rw [← hmul, mul_inv_cancel_left]
  have hvu : inner ℂ v u ≠ 0 := by
    rw [hu, inner_sum, Finset.sum_congr rfl (g := fun _ => inner ℂ v w), Finset.sum_const, nsmul_eq_mul]
    · refine mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, hfin.mem_toFinset.2 ⟨1, rfl⟩⟩)) hvw
    · intro y hy
      obtain ⟨l, rfl⟩ := hfin.mem_toFinset.1 hy
      conv_lhs => rw [← hv l l.2]
      exact (ρ l).inner_map_map _ _
  obtain ⟨c, hc⟩ := hline u hufix
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hvu (by rw [hc]; simp)
  have hvW : v ∈ W := (W.smul_mem_iff hc0).1 (hc ▸ huW)
  rw [eq_top_iff, ← hcyc, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact hW _ _ hvW

section Cyclic

variable {G : Type} [Group G]

def transl (φ : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun g x => φ (x * g))

theorem transl_mem {φ f : G → ℂ} (hf : f ∈ transl φ) (g : G) : (fun x => f (x * g)) ∈ transl φ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    exact Submodule.subset_span ⟨g * a, by simp only [mul_assoc]⟩
  | zero => exact zero_mem _
  | add f f' _ _ h h' => exact add_mem h h'
  | smul a f _ h => exact Submodule.smul_mem _ a h

def translEquiv (φ : G → ℂ) (g : G) : transl φ ≃ₗ[ℂ] transl φ where
  toFun f := ⟨fun x => f.1 (x * g), transl_mem f.2 g⟩
  invFun f := ⟨fun x => f.1 (x * g⁻¹), transl_mem f.2 g⁻¹⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (funext fun x => by simp)
  right_inv f := Subtype.ext (funext fun x => by simp)

theorem transl_law {φ f : G → ℂ} {p : G} {c : ℂ} (h : ∀ x, φ (p * x) = c * φ x) (hf : f ∈ transl φ) (x : G) :
    f (p * x) = c * f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    simp only [mul_assoc, h]
  | zero => simp
  | add f f' _ _ h h' => simp only [Pi.add_apply, h, h', mul_add]
  | smul a f _ h => simp only [Pi.smul_apply, h, smul_eq_mul]; ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem transl_smooth {φ f : G → ℂ} {K : Subgroup G} (hK : IsOpen (K : Set G))
    (h : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (hf : f ∈ transl φ) : ∀ᶠ g in 𝓝 (1 : G), ∀ x, f (x * g) = f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    have h1 : IsOpen {g : G | a⁻¹ * g * a ∈ K} := hK.preimage (by fun_prop)
    filter_upwards [h1.mem_nhds (show (1 : G) ∈ {g : G | a⁻¹ * g * a ∈ K} by simp)] with g hg x
    rw [← h (x * a) _ hg]
    congr 1
    group
  | zero => simp
  | add f f' _ _ h h' => filter_upwards [h, h'] with g h h' x; simp only [Pi.add_apply, h, h']
  | smul a f _ h => filter_upwards [h] with g h x; simp only [Pi.smul_apply, h]

theorem continuous_of_smooth {f : G → ℂ} (hf : ∀ᶠ g in 𝓝 (1 : G), ∀ x, f (x * g) = f x) : Continuous f := by
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun a => ?_).continuous
  have h1 : Filter.Tendsto (fun b : G => a⁻¹ * b) (𝓝 a) (𝓝 1) := by
    have := (continuous_const_mul a⁻¹).tendsto a
    rwa [inv_mul_cancel] at this
  filter_upwards [h1.eventually hf] with b hb
  rw [← hb a, mul_inv_cancel_left]

theorem exists_rep [MeasurableSpace G] [BorelSpace G] [T2Space G] (μ : Measure G) [μ.IsHaarMeasure]
    (K P : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hμ : μ K = 1)
    (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) (ψ : P → ℂ) (δ : P → ℂ) (hδ : ∀ p, conj (ψ p) * ψ p = δ p)
    (φ : G → ℂ) (hφP : ∀ (p : P) x, φ (p * x) = ψ p * φ x) (hφK : ∀ x, ∀ k ∈ K, φ (x * k) = φ x)
    (hφ1 : φ 1 = 1)
    (hinv : ∀ F : G → ℂ, Continuous F → (∀ (p : P) x, F (p * x) = δ p * F x) → ∀ g,
      ∫ x in (K : Set G), F (x * g) ∂μ = ∫ x in (K : Set G), F x ∂μ) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (ρ : G →* (V ≃ₗᵢ[ℂ] V)),
      (∀ x, IsOpen {g | ρ g x = x}) ∧
      (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∃ v : V, ‖v‖ = 1 ∧ (∀ k ∈ K, ρ k v = v) ∧ ∀ g, inner ℂ v (ρ g v) = ∫ k in (K : Set G), φ (k * g) ∂μ := by
  have hc : ∀ f : transl φ, Continuous f.1 := fun f => continuous_of_smooth (transl_smooth hKo hφK f.2)
  have hc2 : ∀ f f' : transl φ, Continuous fun x => conj (f.1 x) * f'.1 x := fun f f' =>
    (Complex.continuous_conj.comp (hc f)).mul (hc f')
  have hi : ∀ f f' : transl φ, IntegrableOn (fun x => conj (f.1 x) * f'.1 x) K μ := fun f f' =>
    (hc2 f f').continuousOn.integrableOn_compact hKc
  have hsq : ∀ f : transl φ, ∫ x in (K : Set G), conj (f.1 x) * f.1 x ∂μ =
      ((∫ x in (K : Set G), ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ) := fun f => by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.conj_mul']
    push_cast; rfl
  have hφk : ∀ k ∈ K, φ k = 1 := fun k hk => by rw [← one_mul k, hφK 1 k hk, hφ1]
  let core : InnerProductSpace.Core ℂ (transl φ) :=
    { inner := fun f f' => ∫ x in (K : Set G), conj (f.1 x) * f'.1 x ∂μ
      conj_inner_symm := fun f f' => by
        rw [← integral_conj]
        simp only [map_mul, Complex.conj_conj, mul_comm]
      re_inner_nonneg := fun f => by
        rw [hsq]
        exact integral_nonneg fun x => sq_nonneg _
      add_left := fun f f' f'' => by
        rw [← integral_add (hi f f'') (hi f' f'')]
        simp only [Submodule.coe_add, Pi.add_apply, map_add, add_mul]
      smul_left := fun f f' r => by
        rw [← integral_const_mul]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
      definite := fun f hf => by
        rw [hsq, Complex.ofReal_eq_zero] at hf
        have hn : Continuous fun x => ‖f.1 x‖ ^ 2 := (hc f).norm.pow 2
        have h1 := (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (hn.continuousOn.integrableOn_compact hKc)).1 hf
        have h2 := Measure.eqOn_open_of_ae_eq h1 hKo hn.continuousOn continuousOn_const
        refine Subtype.ext (funext fun g => ?_)
        obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
        have h3 : f.1 k = 0 := by simpa using h2 hk
        rw [transl_law (hφP ⟨p, hp⟩) f.2, h3, mul_zero]
        rfl }
  letI : NormedAddCommGroup (transl φ) := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ (transl φ) := InnerProductSpace.ofCore core.toCore
  have hin : ∀ f f' : transl φ, inner ℂ f f' = ∫ x in (K : Set G), conj (f.1 x) * f'.1 x ∂μ := fun _ _ => rfl
  have hunit : ∀ g (f f' : transl φ), inner ℂ (translEquiv φ g f) (translEquiv φ g f') = inner ℂ f f' := by
    intro g f f'
    refine hinv (fun x => conj (f.1 x) * f'.1 x) (hc2 f f') (fun p x => ?_) g
    simp only [transl_law (hφP p) f.2, transl_law (hφP p) f'.2, map_mul, ← hδ]
    ring
  let ρ : G →* (transl φ ≃ₗᵢ[ℂ] transl φ) := MonoidHom.mk'
    (fun g => (translEquiv φ g).isometryOfInner (hunit g)) fun g h =>
      LinearIsometryEquiv.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (mul_assoc x g h).symm)
  have hρ : ∀ g (f : transl φ) x, (ρ g f).1 x = f.1 (x * g) := fun _ _ _ => rfl
  let v : transl φ := ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩
  have hsm : ∀ x, IsOpen {g | ρ g x = x} := fun f => by
    let S : Subgroup G :=
      { carrier := {g | ρ g f = f}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          show ρ (a * b) f = f
          rw [map_mul]
          exact (congrArg (ρ a) hb).trans ha
        inv_mem' := fun {a} ha => by
          show ρ a⁻¹ f = f
          rw [map_inv]
          exact (ρ a).symm_apply_eq.2 ha.symm }
    refine S.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [transl_smooth hKo hφK f.2] with g hg
    exact Subtype.ext (funext hg)
  have hv : ∀ k ∈ K, ρ k v = v := fun k hk => Subtype.ext (funext fun x => hφK x k hk)
  have hcoef : ∀ g, inner ℂ v (ρ g v) = ∫ k in (K : Set G), φ (k * g) ∂μ := fun g => by
    rw [hin]
    refine setIntegral_congr_fun hKo.measurableSet fun k hk => ?_
    show conj (φ k) * φ (k * g) = _
    rw [hφk k hk, map_one, one_mul]
  refine ⟨transl φ, inferInstance, inferInstance, ρ, hsm, irreducible_of_fixed_line ρ K hKc hsm v hv ?_ ?_,
    v, ?_, hv, hcoef⟩
  · apply Submodule.map_injective_of_injective (transl φ).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    rfl
  · intro f hf
    refine ⟨f.1 1, Subtype.ext (funext fun g => ?_)⟩
    obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
    have h1 : f.1 k = f.1 1 := by rw [← one_mul k, ← hρ, hf k hk]
    show _ = f.1 1 * φ (p * k)
    rw [transl_law (hφP ⟨p, hp⟩) f.2, hφP ⟨p, hp⟩, h1, hφk k hk, mul_one, mul_comm]
  · have h1 := hcoef 1
    rw [map_one, setIntegral_congr_fun hKo.measurableSet (g := fun _ => (1 : ℂ))
      (fun k hk => by simpa using hφk k hk), setIntegral_const, Measure.real, hμ] at h1
    have h2 : inner ℂ v v = 1 := by simpa using h1
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : ‖v‖ ^ 2 = 1 := Complex.ofReal_eq_one.1 (by rw [Complex.ofReal_pow]; exact h2)
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

end Cyclic

end GlobalTheory.SphCyclic

namespace GlobalTheory.SphCyclic

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix ValuativeRel

theorem exists_sphFn {G : Type} [Group G] (K P : Subgroup G) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (ψ : P →* ℂˣ) (hψ : ∀ p : P, (p : G) ∈ K → ψ p = 1) :
    ∃ φ : G → ℂ, (∀ (p : P) x, φ (p * x) = ψ p * φ x) ∧ (∀ x, ∀ k ∈ K, φ (x * k) = φ x) ∧ φ 1 = 1 := by
  choose p hp u hu hpu using hPK
  have key : ∀ (q : P), ∀ k ∈ K, ψ ⟨p (q * k), hp _⟩ = ψ q := by
    intro q k hk
    have h1 : ((q⁻¹ * ⟨p (q * k), hp _⟩ : P) : G) = k * (u (q * k))⁻¹ := by
      show (q : G)⁻¹ * p (q * k) = _
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, ← hpu]
    have h2 := hψ _ (h1 ▸ mul_mem hk (inv_mem (hu _)))
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2.symm
  have key2 : ∀ (q : P) x, ∀ k ∈ K, ψ ⟨p (q * x * k), hp _⟩ = ψ q * ψ ⟨p x, hp _⟩ := by
    intro q x k hk
    have h1 : q * x * k = ((q * ⟨p x, hp x⟩ : P) : G) * (u x * k) := by
      conv_lhs => rw [hpu x]
      simp only [Subgroup.coe_mul, mul_assoc]
    have h2 := key (q * ⟨p x, hp x⟩) _ (mul_mem (hu x) hk)
    simp only [← h1] at h2
    rw [h2, map_mul]
  refine ⟨fun g => ψ ⟨p g, hp g⟩, fun q x => ?_, fun x k hk => ?_, ?_⟩
  · have := key2 q x 1 (one_mem _)
    simp only [mul_one] at this
    simp only [this, Units.val_mul]
  · have := key2 1 x k hk
    simp only [OneMemClass.coe_one, one_mul, map_one] at this
    simp only [this]
  · have := key 1 1 (one_mem _)
    simp only [OneMemClass.coe_one, one_mul, map_one] at this
    simp only [this, Units.val_one]

theorem exists_rep_blocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (GL n k)] [BorelSpace (GL n k)]
    (ν : α → kˣ →* ℂˣ) (hu : ∀ a x, ‖(ν a x : ℂ)‖ = 1) (hν : ∀ a, IsUnram (ν a))
    (H : Type) [Group H] [TopologicalSpace H] :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (ρ : H × GL n k →* (V ≃ₗᵢ[ℂ] V)),
      (∀ x, IsOpen {g | ρ g x = x}) ∧
      (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∃ v : V, ‖v‖ = 1 ∧ (∀ h, ∀ x ∈ KO k n, ρ (h, x) v = v) ∧
        ∃ (φ : GL n k → ℂ) (κ : Measure (GL n k)),
          (∀ (p : parab k e) x, φ (p * x) = (√(modulus k m (leviProj k e p)) : ℝ) *
            (∏ a, (ν a (GeneralLinearGroup.det (leviProj k e p a)) : ℂ)) * φ x) ∧
          (∀ x, ∀ y ∈ KO k n, φ (x * y) = φ x) ∧ φ 1 = 1 ∧ κ.IsHaarMeasure ∧ κ (KO k n) = 1 ∧
          ∀ g, inner ℂ v (ρ (1, g) v) = ∫ x in (KO k n : Set (GL n k)), φ (x * g) ∂κ := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨-, h2, h3, -, -, -, -, -, hPK⟩ := LeviInt.levi_integral_facts k α n m e
  let ψ : parab k e →* ℂˣ := (deltaHalf k m * ∏ a, ((ν a).comp GeneralLinearGroup.det).comp
    (Pi.evalMonoidHom (fun a => GL (m a) k) a)).comp (leviProj k e)
  have hψ : ∀ p, (ψ p : ℂ) = (√(modulus k m (leviProj k e p)) : ℝ) *
      (∏ a, (ν a (GeneralLinearGroup.det (leviProj k e p a)) : ℂ)) := fun p => by
    simp [ψ, val_deltaHalf, MonoidHom.finsetProd_apply]
  obtain ⟨φ, hφP, hφK, hφ1⟩ := exists_sphFn (KO k n) (parab k e) hPK ψ fun p hp => by
    ext
    rw [hψ, h3 _ (h2 p hp), Finset.prod_eq_one fun a _ => ?_]
    · simp
    · obtain ⟨g, hg⟩ := h2 p hp a
      rw [hν a, Units.val_one]
      rw [← hg]
      have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
          algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
        ((algebraMap 𝒪[k] k).map_det _).symm
      exact h1.symm ▸ (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  let K₀ : TopologicalSpace.PositiveCompacts (GL n k) :=
    ⟨⟨KO k n, SplitFlip.isCompact_KO⟩, by
      rw [SplitFlip.isOpen_KO.interior_eq]; exact ⟨1, one_mem _⟩⟩
  have hκ : Measure.haarMeasure K₀ (KO k n) = 1 := Measure.haarMeasure_self
  obtain ⟨V, _, _, ρ, hsm, hirr, v, hv1, hvK, hco⟩ := exists_rep (Measure.haarMeasure K₀) (KO k n) (parab k e)
    SplitFlip.isOpen_KO SplitFlip.isCompact_KO hκ hPK (fun p => ψ p)
    (fun p => (modulus k m (leviProj k e p) : ℂ)) (fun p => by
      rw [Complex.conj_mul', hψ, norm_mul, norm_prod, Finset.prod_eq_one fun a _ => hu a _, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← Complex.ofReal_pow,
        Real.sq_sqrt (modulus_pos k _).le]) φ hφP hφK hφ1
    (IndDual.integral_KO_mul_right k α n m e _)
  refine ⟨V, inferInstance, inferInstance, ρ.comp (MonoidHom.snd _ _), fun x => (hsm x).preimage continuous_snd,
    fun W hW => hirr W fun g => hW (1, g), v, hv1, fun _ => hvK, φ, _, fun p x => by rw [hφP, hψ], hφK, hφ1,
    inferInstance, hκ, hco⟩

end GlobalTheory.SphCyclic
