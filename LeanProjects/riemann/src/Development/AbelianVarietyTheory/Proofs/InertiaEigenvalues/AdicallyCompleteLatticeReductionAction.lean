import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.GaloisCohomology.LocalTateDualityK
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.CocycleLift

variable {O G T M : Type} [CommRing O] [Group G] [TopologicalSpace G] [ContinuousMul G]
  [AddCommGroup T] [Module O T] [AddCommGroup M] [Module O M]

theorem pow_smul_eq_zero (lam : O) (htf : ∀ t : T, lam • t = 0 → t = 0) (n : ℕ) (t : T)
    (h : lam ^ n • t = 0) : t = 0 := by
  induction n generalizing t with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    exact htf _ (ih _ h)

theorem smodeq_iff (lam : O) (n : ℕ) (x y : T) :
    x ≡ y [SMOD ((Ideal.span {lam}) ^ n • ⊤ : Submodule O T)] ↔ ∃ t, x - y = lam ^ n • t := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, hb⟩; exact ⟨b, hb.symm⟩
  · rintro ⟨b, hb⟩; exact ⟨b, trivial, hb.symm⟩

theorem step (lam : O) (π : Representation O G T) (π' : Representation O G M) (q : T →ₗ[O] M)
    (htf : ∀ t : T, lam • t = 0 → t = 0) (hq : Function.Surjective q)
    (hker : ∀ t, q t = 0 ↔ ∃ y, t = lam • y) (heq : ∀ g t, q (π g t) = π' g (q t))
    (hcont : ∀ (a : ℕ) (t : T) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, π g t - π g₀ t = lam ^ a • y)
    (hH : Subsingleton (ReciprocityTheory.Def.H2 π' ⊤)) (a : ℕ) (c : G → T) (hc : IsLocallyConstant c)
    (hd : ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c x = lam ^ (a + 1) • y) :
    ∃ c' : G → T, (IsLocallyConstant c' ∧ ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c' x = lam ^ (a + 1 + 1) • y) ∧
      ∀ g, ∃ y, c' g - c g = lam ^ (a + 1) • y := by
  choose w hw using hd
  have hw' : ∀ g h, π g (c h) - c (g * h) + c g = lam ^ (a + 1) • w (g, h) := fun g h => hw (g, h)
  have hlc : IsLocallyConstant (fun x => q (w x)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨g₀, h₀⟩
    have e1 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c x.1 = c g₀ :=
      (hc.comp_continuous continuous_fst).eventually_eq (g₀, h₀)
    have e2 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c x.2 = c h₀ :=
      (hc.comp_continuous continuous_snd).eventually_eq (g₀, h₀)
    have e3 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c (x.1 * x.2) = c (g₀ * h₀) :=
      (hc.comp_continuous continuous_mul).eventually_eq (g₀, h₀)
    have e4 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀),
        ∃ y, π x.1 (c h₀) - π g₀ (c h₀) = lam ^ (a + 1 + 1) • y :=
      (continuous_fst.tendsto (g₀, h₀)).eventually (hcont (a + 1 + 1) (c h₀) g₀)
    filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 ⟨y, h4⟩
    obtain ⟨g, h⟩ := x
    simp only at h1 h2 h3 h4
    rw [← sub_eq_zero, ← map_sub, hker]
    refine ⟨y, ?_⟩
    rw [← sub_eq_zero]
    apply pow_smul_eq_zero lam htf (a + 1)
    rw [smul_sub, smul_sub, ← hw', ← hw', h1, h2, h3, ← mul_smul, ← pow_succ, ← h4]
    abel
  have hcoc : ∀ g h l, π g (w (h, l)) - w (g * h, l) + w (g, h * l) - w (g, h) = 0 := by
    intro g h l
    apply pow_smul_eq_zero lam htf (a + 1)
    rw [smul_sub, smul_add, smul_sub, ← map_smul, ← hw', ← hw', ← hw', ← hw']
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
    abel
  have hZ : (fun x => q (w x)) ∈ ReciprocityTheory.Def.Z2 π' ⊤ := by
    refine ⟨⟨hlc, fun _ => trivial⟩, ?_⟩
    show ReciprocityTheory.Def.d2 π' _ = 0
    funext ⟨g, h, l⟩
    have := congrArg q (hcoc g h l)
    simp only [map_add, map_sub, heq, map_zero] at this
    exact this
  have h0 : (Submodule.Quotient.mk ⟨_, hZ⟩ : ReciprocityTheory.Def.H2 π' ⊤) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨b, ⟨hb, -⟩, hbd⟩ := h0
  have hbd' : ∀ g h, π' g (b h) - b (g * h) + b g = q (w (g, h)) := fun g h => congrFun hbd (g, h)
  choose s hs using hq
  refine ⟨fun g => c g - lam ^ (a + 1) • s (b g), ⟨?_, ?_⟩, fun g => ⟨- s (b g), by simp⟩⟩
  · exact hc.sub (hb.comp (fun m => lam ^ (a + 1) • s m))
  · rintro ⟨g, h⟩
    obtain ⟨y, hy⟩ := (hker (w (g, h) - (π g (s (b h)) - s (b (g * h)) + s (b g)))).1 (by
      simp only [map_add, map_sub, heq, hs, hbd', sub_self])
    refine ⟨y, ?_⟩
    show π g (c h - lam ^ (a + 1) • s (b h)) - (c (g * h) - lam ^ (a + 1) • s (b (g * h)))
      + (c g - lam ^ (a + 1) • s (b g)) = _
    rw [pow_succ lam (a + 1), mul_smul, ← hy, smul_sub, ← hw', map_sub, map_smul, smul_add, smul_sub]
    abel

theorem exists_lift : ∀ (O G T M : Type) [CommRing O] [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup T] [Module O T] [AddCommGroup M] [Module O M] (lam : O) (π : Representation O G T) (π' : Representation O G M) (q : T →ₗ[O] M), IsAdicComplete (Ideal.span {lam}) T → (∀ t : T, lam • t = 0 → t = 0) → Function.Surjective q → (∀ t, q t = 0 ↔ ∃ y, t = lam • y) → (∀ g t, q (π g t) = π' g (q t)) → (∀ (a : ℕ) (t : T) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, π g t - π g₀ t = lam ^ a • y) → Subsingleton (ReciprocityTheory.Def.H2 π' ⊤) → ∀ z ∈ ReciprocityTheory.Def.Z1 π' ⊤, ∃ c : G → T, (∀ g h, c (g * h) = c g + π g (c h)) ∧ (∀ g, q (c g) = z g) ∧ ∀ (a : ℕ) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, c g - c g₀ = lam ^ a • y := by
  intro O G T M _ _ _ _ _ _ _ _ lam π π' q hcomp htf hq hker heq hcont hH z hz
  have hst := step lam π π' q htf hq hker heq hcont hH
  obtain ⟨⟨hz1, -⟩, hz2⟩ := hz
  have hz3 : ∀ g h, π' g (z h) - z (g * h) + z g = 0 := fun g h => congrFun hz2 (g, h)
  choose s hs using hq
  let P : ℕ → (G → T) → Prop := fun a c =>
    IsLocallyConstant c ∧ ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c x = lam ^ (a + 1) • y
  have P0 : P 0 (fun g => s (z g)) := by
    refine ⟨hz1.comp s, ?_⟩
    rintro ⟨g, h⟩
    rw [zero_add, pow_one, ← hker]
    show q (π g (s (z h)) - s (z (g * h)) + s (z g)) = 0
    simp only [map_add, map_sub, heq, hs, hz3]
  have hst' : ∀ a (c : {c // P a c}), ∃ c' : {c // P (a + 1) c},
      ∀ g, ∃ y, c'.1 g - c.1 g = lam ^ (a + 1) • y := by
    intro a c
    obtain ⟨c', h1, h2⟩ := hst a c.1 c.2.1 c.2.2
    exact ⟨⟨c', h1⟩, h2⟩
  choose F hF using hst'
  let u : ∀ a, {c // P a c} := fun a => Nat.rec ⟨_, P0⟩ F a
  have hu : ∀ a g, ∃ y, (u (a + 1)).1 g - (u a).1 g = lam ^ (a + 1) • y := fun a => hF a (u a)
  have hcau : ∀ g m n, m ≤ n → ∃ y, (u n).1 g - (u m).1 g = lam ^ (m + 1) • y := by
    intro g m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ n hmn ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨y', hy'⟩ := hu n g
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨y + lam ^ k • y', ?_⟩
      rw [smul_add, ← mul_smul, ← pow_add, show m + 1 + k = m + k + 1 by ring, ← hy, ← hy']
      abel
  have hlim : ∀ g, ∃ L, ∀ n, ∃ y, (u n).1 g - L = lam ^ n • y := by
    intro g
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hcomp.toIsPrecomplete (f := fun n => (u n).1 g) (by
      intro m n hmn
      apply SModEq.symm
      rw [smodeq_iff]
      obtain ⟨y, hy⟩ := hcau g m n hmn
      exact ⟨lam • y, by rw [hy, pow_succ, mul_smul]⟩)
    exact ⟨L, fun n => (smodeq_iff lam n _ _).1 (hL n)⟩
  choose c hc using hlim
  refine ⟨c, fun g h => ?_, fun g => ?_, fun a g₀ => ?_⟩
  · rw [← sub_eq_zero]
    apply IsHausdorff.haus hcomp.toIsHausdorff
    intro n
    rw [smodeq_iff]
    obtain ⟨y1, h1⟩ := hc g n
    obtain ⟨y2, h2⟩ := hc h n
    obtain ⟨y3, h3⟩ := hc (g * h) n
    obtain ⟨y4, h4⟩ := (u n).2.2 (g, h)
    have h4' : π g ((u n).1 h) - (u n).1 (g * h) + (u n).1 g = lam ^ n • lam • y4 := by
      rw [← mul_smul, ← pow_succ]; exact h4
    refine ⟨y1 + π g y2 - y3 - lam • y4, ?_⟩
    rw [smul_sub, smul_sub, smul_add, ← map_smul, ← h1, ← h2, ← h3, ← h4', map_sub]
    abel
  · obtain ⟨y1, h1⟩ := hc g 1
    obtain ⟨y2, h2⟩ := hcau g 0 1 (by norm_num)
    have h0 : q ((u 0).1 g) = z g := hs _
    rw [← h0, ← sub_eq_zero, ← map_sub, hker]
    refine ⟨y2 - y1, ?_⟩
    rw [zero_add, pow_one] at h2
    rw [pow_one] at h1
    rw [smul_sub, ← h1, ← h2]
    abel
  · filter_upwards [(u a).2.1.eventually_eq g₀] with g hg
    obtain ⟨y1, h1⟩ := hc g a
    obtain ⟨y2, h2⟩ := hc g₀ a
    refine ⟨y2 - y1, ?_⟩
    rw [smul_sub, ← h1, ← h2, hg]
    abel

end GlobalTheory.CocycleLift
