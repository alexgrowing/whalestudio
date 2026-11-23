import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsPresOfRealD
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReduction

noncomputable section
namespace GlobalTheory.RankOneReduction
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

section Series
variable {k : Type} [Field k]

theorem coe_inj {a b : k⟦X⟧} (h : (a : k⸨X⸩) = (b : k⸨X⸩)) : a = b :=
  HahnSeries.ofPowerSeries_injective h

theorem eq_unit_mul_pow (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) {d : ℕ} (hd : 0 < d)
    (h1 : ∃ u : (k⟦X⟧)ˣ, ι (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ d)
    (h2 : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, ι (a : k⸨X⸩) = (b : k⸨X⸩)) (c w : k⟦X⟧) (hw : IsUnit w) (p : ℕ)
    (hc : ι (c : k⸨X⸩) = (((PowerSeries.X ^ d) ^ p * w : k⟦X⟧) : k⸨X⸩)) :
    ∃ u : (k⟦X⟧)ˣ, c = (u : k⟦X⟧) * PowerSeries.X ^ p := by
  obtain ⟨u₁, hu₁⟩ := h1
  obtain ⟨w, rfl⟩ := hw
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : (0 : k⟦X⟧) = (PowerSeries.X ^ d) ^ p * (w : k⟦X⟧) := coe_inj (by rw [← hc]; simp)
    exact (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ PowerSeries.X_ne_zero)) w.ne_zero) this.symm
  obtain ⟨r, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 (PowerSeries.X_irreducible (R := k))
  obtain ⟨b, hb⟩ := h2 (u : k⟦X⟧)
  obtain ⟨b', hb'⟩ := h2 ((u⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
  have hbb : b * b' = 1 := coe_inj (by
    rw [PowerSeries.coe_mul, ← hb, ← hb', ← map_mul, ← PowerSeries.coe_mul, Units.mul_inv]; simp)
  have hbu : IsUnit b := IsUnit.of_mul_eq_one _ hbb
  have key : ((hbu.unit * u₁ ^ r : (k⟦X⟧)ˣ) : k⟦X⟧) * (PowerSeries.X : k⟦X⟧) ^ (d * r) =
      (w : k⟦X⟧) * PowerSeries.X ^ (d * p) :=
    coe_inj (by
      rw [mul_comm (w : k⟦X⟧), pow_mul, pow_mul, ← hc, hu, PowerSeries.coe_mul, PowerSeries.coe_mul, map_mul, hb,
        PowerSeries.coe_pow, PowerSeries.coe_pow, PowerSeries.coe_pow, ← vv_eq_coe_X, map_pow, hu₁, mul_pow]
      simp [mul_assoc])
  have := IsDiscreteValuationRing.unit_mul_pow_congr_pow (PowerSeries.X_irreducible (R := k))
    (PowerSeries.X_irreducible (R := k)) _ _ _ _ key
  have hr : r = p := Nat.eq_of_mul_eq_mul_left hd this
  exact ⟨u, hr ▸ hu⟩

variable {m : ℕ}

theorem sh_span (a : ℤ) (x : Vc k m) :
    sh a (Submodule.span k⟦X⟧ {x}) = Submodule.span k⟦X⟧ {vv k ^ a • x} := by
  unfold sh
  rw [Submodule.map_span, Set.image_singleton]
  rfl

theorem pull_span {l : ℕ} (R : RingPG k l) (f : Vc k m →ₗ[k] Vc k m) (hf : Semi R.φ f) (x : Vc k m) :
    pull f (Submodule.span k⟦X⟧ {x}) = Submodule.span k⟦X⟧ {f x} := by
  unfold pull
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨b, hb⟩ := R.φ_int c
    refine Submodule.mem_span_singleton.mpr ⟨b, ?_⟩
    change (b : k⸨X⸩) • f x = f ((c : k⸨X⸩) • x)
    rw [hf, hb]
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨x, Submodule.mem_span_singleton_self x, rfl⟩)

theorem span_unit_pow (u : (k⟦X⟧)ˣ) (p : ℕ) (x : Vc k m) :
    Submodule.span k⟦X⟧ {((u : k⟦X⟧) * PowerSeries.X ^ p) • x} = Submodule.span k⟦X⟧ {vv k ^ (p : ℤ) • x} := by
  rw [mul_smul, Submodule.span_singleton_smul_eq u.isUnit]
  congr 2
  change (((PowerSeries.X : k⟦X⟧) ^ p : k⟦X⟧) : k⸨X⸩) • x = _
  rw [PowerSeries.coe_pow, ← vv_eq_coe_X, zpow_natCast]

end Series

section Rank

theorem free_rank_one {O k M : Type} [CommRing O] [Field k] [Algebra O k] [AddCommGroup M] [Module O M]
    [Module.Free O M] {lam : O} (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) {m : ℕ} (hm : m = 1) (q : M →ₗ[O] (Fin m → k))
    (hq : Function.Surjective q) (hker : KerIs lam q) :
    Module.finrank O M = 1 ∧ ∃ e : M, e ≠ 0 ∧ ∀ x, ∃ c : O, x = c • e := by
  subst hm
  have : Nontrivial O := (algebraMap O k).domain_nontrivial
  let b := Module.Free.chooseBasis O M
  have hli : LinearIndependent k (fun s => q (b s)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    choose g' hg' using fun i => hs (g i)
    have h0 : q (∑ j ∈ s, g' j • b j) = 0 := by
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← hg', algebraMap_smul]
    obtain ⟨y, hy⟩ := (hker _).mp h0
    have := congrArg (fun z => b.repr z i) hy
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul] at this
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (fun h => absurd hi h)] at this
    rw [← hg', hk]
    exact ⟨b.repr y i, by simpa using this⟩
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex O M) := by
    have := hli.cardinal_lift_le_rank
    simp only [rank_fun', Fintype.card_fin, Nat.cast_one, Cardinal.lift_id] at this
    exact Cardinal.le_one_iff_subsingleton.mp this
  have hne : Nonempty (Module.Free.ChooseBasisIndex O M) := by
    by_contra h
    rw [not_nonempty_iff] at h
    obtain ⟨x, hx⟩ := hq 1
    have : x = 0 := by rw [← b.repr.map_eq_zero_iff]; exact Subsingleton.elim _ _
    rw [this, map_zero] at hx
    exact zero_ne_one hx
  obtain ⟨s⟩ := hne
  have : Unique (Module.Free.ChooseBasisIndex O M) := uniqueOfSubsingleton s
  refine ⟨by rw [Module.finrank_eq_card_basis b]; simp, b default, b.ne_zero _, fun x => ⟨b.repr x default, ?_⟩⟩
  simpa using (b.sum_repr x).symm

end Rank

section Wach
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    {W : LocWach PD LL O v n₀} {k : Type} [Field k] [Algebra O k]

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n₀) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n₀) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem γA_apply (g : W.Gam) (a : LetA O n₀) (j : ZMod n₀) : W.γA g a j = W.γ₀ g (a j) := rfl

theorem γA_letE (g : W.Gam) (j : ZMod n₀) : W.γA g (letE j) = letE j := by
  funext i
  rw [γA_apply]
  by_cases h : i = j
  · subst h; simp [letE]
  · simp [letE, h]

theorem red_Q {l : ℕ} [Fact l.Prime] [CharP k l] (hp : PD.p = l) (hs : W.s = 1) (j : ZMod n₀) :
    PowerSeries.map (algebraMap O k) (W.Q j) = PowerSeries.X ^ (l - 1) := by
  have hQ : W.Q j = W.q₀ := by
    rw [LocWach.Q, hs]
    rfl
  have h := congrArg (PowerSeries.map (algebraMap O k)) W.q₀_def
  have : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X, hp] at h
  rw [add_pow_char, one_pow, add_sub_cancel_left] at h
  rw [hQ]
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := k))
  rw [h, ← pow_succ', Nat.sub_add_cancel (Fact.out : l.Prime).one_le]

variable {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam}

theorem j_rel (p : Pres W F ι τ γ)
    (hΔ : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) →
      ∃ c : k⟦X⟧, ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩))
    {T A q} (h : Onto T A q) (i : ZMod n) (x y : ↥(DΔ W T)) (g : LetA O n₀)
    (hxy : (letE (τ i) : LetA O n₀) • (y : W.DD T) = g • (letE (τ i) : LetA O n₀) • (x : W.DD T))
    (htf : ∀ c : LetA O n₀, c • (letE (τ i) : LetA O n₀) • (x : W.DD T) = 0 → c (τ i) = 0) :
    ∃ c : k⟦X⟧, ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (g (τ i)) : k⟦X⟧) : k⸨X⸩) ∧
      p.j T A q i y = c • p.j T A q i x := by
  have hy' : (letE (τ i) : LetA O n₀) • (y : W.DD T) ∈ DΔ W T := fun δ hδ => by
    rw [γD_smulA, γA_letE, y.2 δ hδ]
  have hinv : ∀ δ ∈ W.DelF, W.γ₀ δ (g (τ i)) = g (τ i) := fun δ hδ => by
    have h1 := hy' δ hδ
    rw [hxy, γD_smulA, γD_smulA, γA_letE, x.2 δ hδ, ← sub_eq_zero, ← sub_smul] at h1
    have := htf _ h1
    rwa [Pi.sub_apply, γA_apply, sub_eq_zero] at this
  obtain ⟨c, hc⟩ := hΔ _ hinv
  refine ⟨c, hc, ?_⟩
  have h1 : p.j T A q i ⟨_, hy'⟩ = p.j T A q i y := by
    rw [p.j_smul T A q h i (letE (τ i)) 1 y ⟨_, hy'⟩ (by simp [letE]) rfl, one_smul]
  rw [← h1]
  exact p.j_smul T A q h i (g * letE (τ i)) c x _ (by simpa [letE] using hc) (by rw [mul_smul]; exact hxy)

theorem main_gen [Fact l.Prime] [CharP k l] (hp : PD.p = l) (hs : W.s = 1) (p : Pres W F ι τ γ)
    (h1 : ∃ u : (k⟦X⟧)ˣ, ι (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l - 1))
    (h2 : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, ι (a : k⸨X⸩) = (b : k⸨X⸩))
    (hΔ : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) →
      ∃ c : k⟦X⟧, ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩))
    {T A q} (h : Onto T A q) (b : ↥(DΔ W T)) (hb : ∀ c : LetA O n₀, c • (b : W.DD T) = 0 → c = 0)
    (hN : W.N T = Submodule.span (LetA O n₀) {(b : W.DD T)}) (N : Lats k n A.m)
    (hNi : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (i : ZMod n) (a : ℤ)
    (hr1 : ∀ x ∈ W.φpull T, ∃ y ∈ W.N T,
      W.Q ^ (-a).toNat • (letE (τ i) : LetA O n₀) • x = W.Q ^ a.toNat • (letE (τ i) : LetA O n₀) • y)
    (hr2 : ∀ y ∈ W.N T, ∃ x ∈ W.φpull T,
      W.Q ^ (-a).toNat • (letE (τ i) : LetA O n₀) • x = W.Q ^ a.toNat • (letE (τ i) : LetA O n₀) • y) :
    pull ((F.D A).φ i) (N (i - 1)) = sh a (N i) := by
  have hd : 0 < l - 1 := Nat.sub_pos_of_lt (Fact.out : l.Prime).one_lt
  have hbN : (b : W.DD T) ∈ W.N T := by rw [hN]; exact Submodule.mem_span_singleton_self _
  have htf : ∀ (j : ZMod n₀) (c : LetA O n₀), c • (letE j : LetA O n₀) • (b : W.DD T) = 0 → c j = 0 := by
    intro j c hc
    rw [smul_smul] at hc
    simpa [letE] using congrFun (hb _ hc) j
  have hspan : ∀ i, N i = Submodule.span k⟦X⟧ {p.j T A q i b} := by
    intro i
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := (hNi i y).mp hy
      rw [hN] at hx
      obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨c, -, hc⟩ := j_rel p hΔ h i b x g (by rw [← hg, smul_comm]) (htf _)
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    · rw [Submodule.span_singleton_le_iff_mem, hNi]
      exact ⟨b, hbN, rfl⟩
  let fb : ↥(DΔ W T) := ⟨W.φD T b, φ_mem W T b⟩
  have hfb : p.j T A q i fb = (F.D A).φ i (p.j T A q (i - 1) b) := p.j_φ' h i b
  rw [hspan, hspan, pull_span R _ ((F.D A).φ_semi i), sh_span, ← hfb]
  have hpull : ∀ x ∈ W.φpull T, ∃ d : LetA O n₀, d • (fb : W.DD T) = x := by
    intro x hx
    rw [← Submodule.mem_span_singleton]
    refine (Submodule.span_le.mpr ?_ : W.φpull T ≤ _) hx
    rintro _ ⟨y, hy, rfl⟩
    rw [hN] at hy
    obtain ⟨g, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact Submodule.mem_span_singleton.mpr ⟨W.φA g, (φD_smulA T g _).symm⟩
  obtain ⟨y, hy, hc⟩ := hr1 (fb : W.DD T) (Submodule.subset_span ⟨b, hbN, rfl⟩)
  rw [hN] at hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨x, hx, hd'⟩ := hr2 _ hbN
  obtain ⟨d, rfl⟩ := hpull x hx
  set e : LetA O n₀ := letE (τ i) with he
  have hQ := red_Q (W := W) (k := k) hp hs (τ i)
  have hcd : PowerSeries.map (algebraMap O k) (c (τ i)) * PowerSeries.map (algebraMap O k) (d (τ i)) = 1 := by
    have h3 : (W.Q ^ a.toNat * (c * d) - W.Q ^ a.toNat) • e • (b : W.DD T) = 0 := by
      rw [sub_smul, ← hd', sub_eq_zero]
      calc (W.Q ^ a.toNat * (c * d)) • e • (b : W.DD T) = d • W.Q ^ a.toNat • e • c • (b : W.DD T) := by
            simp only [smul_smul]; congr 1; ring
        _ = d • W.Q ^ (-a).toNat • e • (fb : W.DD T) := by rw [hc]
        _ = _ := by simp only [smul_smul]; congr 1; ring
    have h4 := congrArg (PowerSeries.map (algebraMap O k)) (htf _ _ h3)
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, map_sub, map_mul, map_pow, map_zero, hQ] at h4
    apply mul_left_cancel₀ (pow_ne_zero a.toNat (pow_ne_zero (l - 1) (PowerSeries.X_ne_zero (R := k))))
    rw [mul_one]
    exact sub_eq_zero.mp h4
  rcases le_total 0 a with ha | ha
  · have h0 : (-a).toNat = 0 := by omega
    rw [h0, pow_zero, one_smul] at hc
    obtain ⟨c', hc', hj⟩ := j_rel p hΔ h i b fb (W.Q ^ a.toNat * c)
      (by rw [hc]; simp only [smul_smul]; congr 1; ring) (htf _)
    rw [Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, hQ] at hc'
    obtain ⟨u, hu⟩ := eq_unit_mul_pow ι hd h1 h2 c' _ (IsUnit.of_mul_eq_one _ hcd) _ hc'
    rw [hj, hu, span_unit_pow, Int.toNat_of_nonneg ha]
  · have h0 : a.toNat = 0 := by omega
    rw [h0, pow_zero, one_smul] at hd'
    obtain ⟨c', hc', hj⟩ := j_rel p hΔ h i fb b (W.Q ^ (-a).toNat * d)
      (by rw [← hd']; simp only [smul_smul]; congr 1; ring)
      (fun z hz => htf _ z (by
        rw [← hd']
        calc z • W.Q ^ (-a).toNat • e • d • (fb : W.DD T) = (W.Q ^ (-a).toNat * d) • z • e • (fb : W.DD T) := by
              simp only [smul_smul]; congr 1; ring
          _ = 0 := by rw [hz, smul_zero]))
    rw [Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, hQ] at hc'
    obtain ⟨u, hu⟩ := eq_unit_mul_pow ι hd h1 h2 c' _ (IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hcd)) _ hc'
    rw [← sh_span, hj, hu, span_unit_pow, sh_span, smul_smul, ← zpow_add₀ (vv_ne_zero k),
      Int.toNat_of_nonneg (by omega), add_neg_cancel, zpow_zero, one_smul]

theorem rank_one {lam : O} (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (T : LocLat G Qp LL O) {m : ℕ} (hm : m = 1)
    (q : ↥T.L.T →ₗ[O] (Fin m → k)) (hq : Function.Surjective q) (hker : KerIs lam q) :
    Module.finrank O ↥T.L.T = 1 ∧ Module.finrank LL T.V = 1 := by
  have := T.L.free
  obtain ⟨h1, e, he, hx⟩ := free_rank_one hs hk hm q hq hker
  refine ⟨h1, finrank_eq_one (R := LL) (e : T.V) (by simpa using he) fun w => ?_⟩
  rw [← Submodule.mem_span_singleton]
  have hw : w ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  refine Submodule.span_le.mpr ?_ hw
  intro x hx'
  obtain ⟨c, hc⟩ := hx ⟨x, hx'⟩
  exact Submodule.mem_span_singleton.mpr ⟨algebraMap O LL c, by
    rw [algebraMap_smul]; exact (congrArg Subtype.val hc).symm⟩

theorem exists_gen (hB : GlobalTheory.WachUse.InvBasis W) (T : LocLat G Qp LL O) (hc : IsCrys PD T.ρ)
    (h1 : Module.finrank O ↥T.L.T = 1) :
    ∃ b : ↥(DΔ W T), (∀ c : LetA O n₀, c • (b : W.DD T) = 0 → c = 0) ∧
      W.N T = Submodule.span (LetA O n₀) {(b : W.DD T)} := by
  have h := hB T hc
  rw [h1] at h
  obtain ⟨b, hb, hli, hN⟩ := h
  refine ⟨⟨b 0, (hb 0).2⟩, fun c hc => ?_, ?_⟩
  · exact (Fintype.linearIndependent_iff.mp hli) (fun _ => c) (by simpa using hc) 0
  · rw [Set.range_unique] at hN; exact hN

theorem main_QN [Fact l.Prime] [CharP k l] (hp : PD.p = l) (hs : W.s = 1) (p : Pres W F ι τ γ)
    (hcyc : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι)
    (e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1})
    (he : ∀ δ a, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 a) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) a))
    {lam : O} (hsurj : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x)
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} (hbij : Function.Bijective emb) (hτ : ∀ i, W.emb (τ i) = emb i)
    (hQN : GlobalTheory.WachUse.QN W) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (U : ZMod n → Multiset ℤ) (hon : Onto T A q) (hker : KerIs lam q) (hcr : CrysWith PD emb T.ρ U)
    (N : Lats k n A.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (a : ZMod n → ℤ)
    (hm : A.m = 1) (hU : ∀ i, U i = {a i}) (i : ZMod n) :
    pull ((F.D A).φ i) (N (i - 1)) = sh (a i) (N i) := by
  have hΔ : ∀ b : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ b = b) →
      ∃ c : k⟦X⟧, ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) b : k⟦X⟧) : k⸨X⸩) := by
    intro b hb
    refine (hcyc.2.2.1 _).mp fun z hz => ?_
    obtain ⟨δ, hδ⟩ := e.surjective ⟨z, hz⟩
    have h := he δ b
    rw [hδ, hb δ.1 δ.2] at h
    exact h.symm
  obtain ⟨h1, h2⟩ := rank_one hsurj hk T hm q hon.1 hker
  obtain ⟨b, hb, hNb⟩ := exists_gen hQN.1 T hcr.1 h1
  choose σ hσ using fun j => hbij.2 (W.emb j)
  have hστ : σ (τ i) = i := hbij.1 ((hσ _).trans (hτ i))
  have hcr' : CrysWith PD W.emb T.ρ (fun j => {a (σ j)}) :=
    ⟨hcr.1, fun j => by have h := hcr.2 (σ j); rw [hσ j, hU] at h; exact h⟩
  have hr := hQN.2.2.1 T (fun j => a (σ j)) hcr' h2 (τ i)
  have h := main_gen hp hs p hcyc.1 hcyc.2.1 hΔ hon b hb hNb N hN i (a (σ (τ i))) hr.1 hr.2
  rwa [hστ] at h

end Wach

theorem pull_eq_sh : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ a : ZMod S.n → ℤ, A.m = 1 → (∀ i, U i = {a i}) → ∀ i, pull ((F.D A).φ i) (N (i - 1)) = sh (a i) (N i) := by
  intro l _ P H S k _ _ _ hres R ι F τ γ p hcyc hτ _ hQN T A q U hon hker hcr N hN a hm hU i
  obtain ⟨-, e, he⟩ := GlobalTheory.RedAct.gamma_action_reduction H S k
  have hs : (S.W H).s = 1 := H.W_s S.K 1 S.LL _
  exact main_QN (W := S.W H) (P.PD_p S.K) hs p hcyc e he hres.1 hres.2 S.hyp.1.2.2.2.1 hτ hQN T A q U hon hker hcr
    N hN a hm hU i

end GlobalTheory.RankOneReduction
