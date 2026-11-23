import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallMemSupPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantTuplePrescribedMemberLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.ValuationRepresentative

theorem exists_dual_pos {M : Type} [AddCommGroup M] [Module.Finite ℤ M] {m : ℕ} (v : Fin m → M)
    (hv : LinearIndependent ℤ v) (k : Fin m) :
    ∃ f : M →ₗ[ℤ] ℤ, (∀ j, j ≠ k → f (v j) = 0) ∧ 0 < f (v k) := by
  classical
  let p : Submodule ℤ M := Submodule.span ℤ (v '' {j | j ≠ k})
  have hx : p.mkQ (v k) ∉ Submodule.torsion ℤ (M ⧸ p) := by
    intro h
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff _).1 h
    have h1 : a • v k ∈ p := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa using hax
    obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination ℤ).1 h1
    have h2 : Finsupp.linearCombination ℤ v (l - Finsupp.single k a) = 0 := by
      simp [map_sub, hle]
    have h3 := linearIndependent_iff.1 hv _ h2
    have h4 : l k = 0 := (Finsupp.mem_supported' ℤ l).1 hl k (by simp)
    have h5 := congrArg (fun f => f k) h3
    simp [h4] at h5
    exact nonZeroDivisors.ne_zero ha h5
  haveI : Module.IsTorsionFree ℤ ((M ⧸ p) ⧸ Submodule.torsion ℤ (M ⧸ p)) :=
    Submodule.isTorsionFree_iff_torsion_eq_bot.2 Submodule.QuotientTorsion.torsion_eq_bot
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  let g : M →ₗ[ℤ] ℤ := f ∘ₗ p.mkQ
  have hg : ∀ j, j ≠ k → g (v j) = 0 := fun j hj => by
    have : p.mkQ (v j) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    simp only [g, LinearMap.comp_apply, this, map_zero]
  have hgk : g (v k) ≠ 0 := hf
  rcases lt_or_gt_of_ne hgk with hn | hp
  · exact ⟨-g, fun j hj => by simp [hg j hj], by simp; omega⟩
  · exact ⟨g, hg, hp⟩

theorem sum_rep {R : Type} [AddCommMonoid R] {l n : ℕ} (f : Fin l → R) :
    ∑ i : Fin (l * n), f (finProdFinEquiv.symm i).1 = n • ∑ i, f i := by
  rw [finProdFinEquiv.symm.sum_comp (fun p : Fin l × Fin n => f p.1), Fintype.sum_prod_type]
  simp [Finset.smul_sum]

theorem prod_rep {R : Type} [CommMonoid R] {l n : ℕ} (f : Fin l → R) :
    ∏ i : Fin (l * n), f (finProdFinEquiv.symm i).1 = (∏ i, f i) ^ n := by
  rw [finProdFinEquiv.symm.prod_comp (fun p : Fin l × Fin n => f p.1), Fintype.prod_prod_type]
  simp [Finset.prod_pow]

theorem supports_rep {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {d : ℕ} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {r : ℕ} {ga : Fin r → LinearMap.BilinForm ℤ X} {m : ℕ} {a : Fin m → X}
    (h : Supports bar φ d ga a) (n : ℕ) (hn : 1 ≤ n) :
    Supports bar φ (d * n) ga (fun i : Fin (m * n) => a (finProdFinEquiv.symm i).1) := by
  have hs : ∀ β : LinearMap.BilinForm ℤ X, (∑ i : Fin (m * n), β (a (finProdFinEquiv.symm i).1)
      (a (finProdFinEquiv.symm i).1)) = n * ∑ i, β (a i) (a i) := fun β => by
    rw [sum_rep (fun j => β (a j) (a j)), nsmul_eq_mul]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩
  · rw [eq_top_iff, ← h.span]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨finProdFinEquiv (j, ⟨0, by omega⟩), by simp⟩
  · rw [hs, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    have := mul_le_mul_of_nonneg_left (h.le β hβ hp) hn'.le
    linarith
  · rw [hs, Int.cast_mul, Int.cast_natCast, ← h.eq j, Nat.cast_mul]; ring
  · rw [hs, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
    refine h.only β hβ hp ?_
    have : (n : ℝ) * (d * φ.evalZ β) = n * ((∑ i, β (a i) (a i) : ℤ) : ℝ) := by rw [← he]; ring
    exact mul_left_cancel₀ hn'.ne' this

theorem lin_smul {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X]
    (a : Fin l × Fin s → X) (M : ℤ) (δ : LinearMap.BilinForm ℤ X) : lin W a (M • δ) = M * lin W a δ := by
  simp only [lin, qW, LinearMap.smul_apply, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem prod_mono {s l m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X V : Type} [AddCommGroup X] [CommRing V] (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (h : ∀ i y, 0 ≤ qW W (δ i) y) (a : Fin l × Fin s → X) :
    ∏ i, mono W t δ (fun v => a (i, v)) = ∏ j, t j ^ (lin W a (δ j)).toNat := by
  simp only [mono]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have h0 : 0 ≤ lin W a (δ j) := Finset.sum_nonneg fun i _ => h j _
  apply Int.natCast_inj.1
  rw [Int.toNat_of_nonneg h0, lin, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h j _)

end GlobalTheory.Poinc.ValuationRepresentative

open GlobalTheory.Poinc.ValuationRepresentative in

theorem GlobalTheory.Poinc.Sep.values_of_elements : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → NoSelfInt bar q φ → ∀ d₀ d : ℕ, 1 ≤ d₀ → 1 ≤ d → HasSupports bar q φ d₀ → ∀ (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ), PosW W → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ (A : Type) [CommRing A] [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) (ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y)) (M : ℕ), 1 ≤ M → IsCone bar φ ga → (∀ k, Φ.δ y k = (M : ℤ) • ga k) → ∀ (K : Type) [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K), Elements Φ y φ d ga ev k₀ → Values Φ y ev k₀ := by
  classical
  intro O _ _ _ _ bar q φ hF hNS d₀ d hd₀ hd hSupp s W hW N₁ hN₁ A _ _ Φ y ga M hM hcone hδ K _ ev k₀ hE
  obtain ⟨O', g₀, b, hO', hb, ⟨w, hw⟩, happ⟩ := hE
  obtain ⟨m₀, a₀, hs₀⟩ := hSupp (Φ.X y) (Φ.rank_le y) _ ga hcone
  obtain ⟨m₁, a₁, hs₁⟩ : ∃ (m₁ : ℕ) (a₁ : Fin m₁ → Φ.X y), Supports bar φ (d₀ * d) ga a₁ :=
    ⟨_, _, supports_rep hs₀ d hd⟩
  have hφX : IsPolFanOn bar φ (Φ.X y) := hF (Φ.X y) (Φ.rank_le y)
  have hne : NoEquivRays O ga := hNS (Φ.X y) (Φ.rank_le y) _ ga hcone
  have hpos : ∀ x, x ≠ 0 → ∃ j, 0 < ga j x x := fun x hx => by
    obtain ⟨i, hi⟩ := Φ.pos y x hx
    refine ⟨i, ?_⟩
    rw [hδ i] at hi
    simp only [LinearMap.smul_apply, smul_eq_mul] at hi
    exact pos_of_mul_pos_right hi (by positivity)
  obtain ⟨cW, hcW0, hcW⟩ := GlobalTheory.T.weightedLatticeQuadraticSum_ge_diagonal (s + 1) W hW
  have hq : ∀ k mv, 0 ≤ qW W (Φ.δ y k) mv := fun k mv => by
    have h1 := hcW (Φ.X y) (Φ.δ y k) (Φ.bal y k).1 (Φ.nonneg y k) mv
    have h2 : (0 : ℝ) ≤ ((∑ u, Φ.δ y k (mv u) (mv u) : ℤ) : ℝ) := by
      exact_mod_cast Finset.sum_nonneg fun u _ => Φ.nonneg y k _
    exact_mod_cast (mul_nonneg hcW0.le h2).trans h1
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  haveI hp : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  have hOp : ∀ h ∈ O', h ∈ maximalIdeal (Φ.V y) → h ∈ RingHom.ker ev := fun h hh hm =>
    RingHom.mem_ker.2 ((hO' h hh).2 hm)
  have hg₀0 : g₀ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hw
    exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (Φ.t_mem y k).2) hw.symm
  have hI : Ideal.span (Set.range (Φ.t y)) ≤ maximalIdeal (Φ.V y) :=
    Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (Φ.t_mem y k).1)
  have hexp : ∀ (D : ℕ) k, (M : ℤ) * (D * ∑ i, ga k (a₁ i) (a₁ i)) = ((D * d₀ * b k : ℕ) : ℤ) := by
    intro D k
    have h1 : ((∑ i, ga k (a₁ i) (a₁ i) : ℤ) : ℝ) = d₀ * d * φ.evalZ (ga k) := by
      rw [← hs₁.eq k]; push_cast; ring
    have h2 : ((b k : ℕ) : ℝ) = d * (M * φ.evalZ (ga k)) := by
      rw [hb k, hδ k, hcone.evalZ_smul]
    have : ((M * (D * ∑ i, ga k (a₁ i) (a₁ i)) : ℤ) : ℝ) = ((D * d₀ * b k : ℕ) : ℝ) := by
      rw [Int.cast_mul, Int.cast_mul, h1, Nat.cast_mul, h2]; push_cast; ring
    exact_mod_cast this
  have key : ∀ lam : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (ga j)) → ∀ mv : Fin (s + 1) → Φ.X y,
      ∃ (D D' l : ℕ) (a : Fin l × Fin (s + 1) → Φ.X y) (i₀ : Fin l), 1 ≤ D ∧ 1 ≤ D' ∧ (∀ u, a (i₀, u) = mv u) ∧
        (∀ β ∈ balForms bar (Φ.X y), lin W a β = D * ∑ i, β (a₁ i) (a₁ i) + D' * lam β) ∧
        ∀ c : Fin l → Φ.Q,
          (IsUnit (Φ.coefT y a c) →
            (w : Φ.V y) ^ (D * d₀) * ∏ k, Φ.t y k ^ (M * D' * (lam (ga k)).toNat) ∈ maximalIdeal (Φ.V y) →
            (w : Φ.V y) ^ (D * d₀) * ∏ k, Φ.t y k ^ (M * D' * (lam (ga k)).toNat) ∈ RingHom.ker ev) ∧
          (Ideal.span (Set.range (Φ.t y)) ≤ RingHom.ker ev → ∃ h ∈ O',
            h - Φ.coefT y a c * ((w : Φ.V y) ^ (D * d₀) * ∏ k, Φ.t y k ^ (M * D' * (lam (ga k)).toNat)) ∈
              RingHom.ker ev) := by
    intro lam hlam mv
    obtain ⟨D, D', l, a, i₀, hD, hD', hmv, hdom, hlin⟩ :=
      GlobalTheory.T.exists_dominant_tuple_prescribed_member_linearForm O bar φ (d₀ * d) (Φ.X y) hφX (Φ.m y) m₁ ga a₁ hcone hne hpos hs₁ s W hW N₁ hN₁ lam hlam mv
    refine ⟨D, D', l, a, i₀, hD, hD', hmv, hlin, fun c => ?_⟩
    set T := (w : Φ.V y) ^ (D * d₀) * ∏ k, Φ.t y k ^ (M * D' * (lam (ga k)).toNat) with hT
    have hmono : Φ.monoT y a = T * g₀ ^ (D * d₀) := by
      have e1 : Φ.monoT y a = ∏ k, Φ.t y k ^ (D * d₀ * b k + M * D' * (lam (ga k)).toNat) := by
        show ∏ i, mono W (Φ.t y) (Φ.δ y) (fun v => a (i, v)) = _
        rw [prod_mono W _ _ hq a]
        refine Finset.prod_congr rfl fun k _ => congrArg _ ?_
        have : lin W a (Φ.δ y k) = ((D * d₀ * b k + M * D' * (lam (ga k)).toNat : ℕ) : ℤ) := by
          rw [hδ k, lin_smul, hlin _ (hcone.mem k)]
          push_cast
          rw [Int.toNat_of_nonneg (hlam k)]
          have h3 := hexp D k
          push_cast at h3
          linear_combination h3
        rw [this, Int.toNat_natCast]
      have e2 : ∀ k, Φ.t y k ^ (D * d₀ * b k + M * D' * (lam (ga k)).toNat) =
          (Φ.t y k ^ b k) ^ (D * d₀) * Φ.t y k ^ (M * D' * (lam (ga k)).toNat) := fun k => by
        rw [← pow_mul, pow_add, mul_comm (b k)]
      rw [e1, Finset.prod_congr rfl fun k _ => e2 k, Finset.prod_mul_distrib, Finset.prod_pow, ← hw, mul_pow, hT]
      ring
    have H : ∀ e : ℕ, ∃ h ∈ O', h * g₀ ^ (D * d₀) - Φ.coefT y a c * (T * g₀ ^ (D * d₀)) ∈
        Ideal.span {T * g₀ ^ (D * d₀)} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e := by
      intro e
      have hdom' : Dominant bar φ (D * d₀ * d) N₁ W ga a := by rwa [_root_.mul_assoc]
      obtain ⟨h, hh, hm⟩ := happ (D * d₀) l a hdom' c e
      exact ⟨h, hh, by rwa [hmono] at hm⟩
    exact GlobalTheory.Poinc.const_mod_prime_of_approx (Φ.V y) (RingHom.ker ev) O' hOp (g₀ ^ (D * d₀)) T _ _
      (pow_ne_zero _ hg₀0) hI H
  have hunit : ∀ {l : ℕ} (a : Fin l × Fin (s + 1) → Φ.X y),
      IsUnit (Φ.coefT y a fun i => (Φ.u_unit y (fun v => a (i, v))).choose) := fun a =>
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => (Φ.u_unit y _).choose_spec
  have hwne : ∀ n : ℕ, ev ((w : Φ.V y) ^ n) ≠ 0 := fun n => ((w.isUnit.pow n).map ev).ne_zero
  have ht : ∀ k, Φ.t y k ∈ RingHom.ker ev := by
    intro k
    obtain ⟨lam, hl0, hlk⟩ := exists_dual_pos ga hcone.linearIndependent k
    have hlam : ∀ j, 0 ≤ lam (ga j) := fun j => by
      by_cases hj : j = k
      · subst hj; exact hlk.le
      · rw [hl0 j hj]
    obtain ⟨D, D', l, a, i₀, hD, hD', -, -, hc⟩ := key lam hlam 0
    have hprod : ∏ j, Φ.t y j ^ (M * D' * (lam (ga j)).toNat) = Φ.t y k ^ (M * D' * (lam (ga k)).toNat) :=
      Fintype.prod_eq_single k fun j hj => by rw [hl0 j hj]; simp
    have hn : 0 < M * D' * (lam (ga k)).toNat := by
      have : 0 < (lam (ga k)).toNat := by omega
      positivity
    have hTm : (w : Φ.V y) ^ (D * d₀) * ∏ j, Φ.t y j ^ (M * D' * (lam (ga j)).toNat) ∈ maximalIdeal (Φ.V y) := by
      rw [hprod]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Φ.t_mem y k).1 _ hn)
    have h1 := (hc _).1 (hunit a) hTm
    rw [hprod] at h1
    have hw' : (w : Φ.V y) ^ (D * d₀) ∉ RingHom.ker ev := fun h => hwne _ (RingHom.mem_ker.1 h)
    exact hp.mem_of_pow_mem _ ((hp.mem_or_mem h1).resolve_left hw')
  have hIp : Ideal.span (Set.range (Φ.t y)) ≤ RingHom.ker ev :=
    Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact ht k)
  have hzero : ∀ D' : ℕ, ∏ k, Φ.t y k ^ (M * D' * ((0 : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ) (ga k)).toNat) = 1 :=
    fun D' => by simp
  refine ⟨fun k => RingHom.mem_ker.1 (ht k), fun mu c c' hc' => ?_, fun lam hlam => ?_⟩
  · obtain ⟨D, D', l, a, i₀, -, -, hmv, -, hc⟩ := key 0 (fun j => le_rfl) mu
    let c₀ : Fin l → Φ.Q := fun i => (Φ.u_unit y (fun v => a (i, v))).choose
    have hsplit : ∀ e : Φ.Q, Φ.coefT y a (Function.update c₀ i₀ e) =
        Φ.u y mu e * ∏ i ∈ Finset.univ.erase i₀, Φ.u y (fun v => a (i, v)) (c₀ i) := by
      intro e
      rw [VSys.coefT, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      congr 1
      · rw [Function.update_self]
        congr 1
        funext v
        exact hmv v
      · refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have hU : IsUnit (∏ i ∈ Finset.univ.erase i₀, Φ.u y (fun v => a (i, v)) (c₀ i)) :=
      Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => (Φ.u_unit y _).choose_spec
    obtain ⟨h, hh, hhp⟩ := (hc (Function.update c₀ i₀ c)).2 hIp
    obtain ⟨h', hh', hhp'⟩ := (hc (Function.update c₀ i₀ c')).2 hIp
    rw [hsplit, hzero, _root_.mul_one] at hhp hhp'
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hhp hhp'
    have hUe : ev (∏ i ∈ Finset.univ.erase i₀, Φ.u y (fun v => a (i, v)) (c₀ i)) ≠ 0 := (hU.map ev).ne_zero
    have hce : ev (Φ.u y mu c') ≠ 0 := (hc'.map ev).ne_zero
    refine ⟨ev h / ev h', div_mem (hO' h hh).1 (hO' h' hh').1, ?_⟩
    rw [hhp, hhp']
    simp only [map_mul]
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (mul_ne_zero hce hUe) (by simpa using hwne (D * d₀)))]
    ring
  · have hlam0 : ∀ j, lam (ga j) = 0 := fun j => by
      have := hlam j
      rw [hδ j, map_smul, smul_eq_mul] at this
      rcases mul_eq_zero.1 this with h | h
      · omega
      · exact h
    obtain ⟨D, D', l, a, -, -, hD', -, hlin, hc⟩ := key lam (fun j => (hlam0 j).ge) 0
    obtain ⟨E, E', l', a', -, hE, -, -, hlin', hc'⟩ := key 0 (fun j => le_rfl) 0
    obtain ⟨h, hh, hhp⟩ := (hc fun i => (Φ.u_unit y (fun v => a (i, v))).choose).2 hIp
    obtain ⟨h', hh', hhp'⟩ := (hc' fun i => (Φ.u_unit y (fun v => a' (i, v))).choose).2 hIp
    have hprod1 : ∏ k, Φ.t y k ^ (M * D' * (lam (ga k)).toNat) = 1 := by simp [hlam0]
    rw [hprod1, _root_.mul_one, RingHom.mem_ker, map_sub, sub_eq_zero] at hhp
    rw [hzero, _root_.mul_one, RingHom.mem_ker, map_sub, sub_eq_zero] at hhp'
    have hce' := ((hunit a').map ev).ne_zero
    have hrepc : ∀ {l n : ℕ} (a : Fin l × Fin (s + 1) → Φ.X y) (c : Fin l → Φ.Q),
        Φ.coefT y (fun p : Fin (l * n) × Fin (s + 1) => a ((finProdFinEquiv.symm p.1).1, p.2))
          (fun i => c (finProdFinEquiv.symm i).1) = Φ.coefT y a c ^ n := fun a c =>
      prod_rep (fun j => Φ.u y (fun v => a (j, v)) (c j))
    have hrepl : ∀ {l n : ℕ} (a : Fin l × Fin (s + 1) → Φ.X y) (β : LinearMap.BilinForm ℤ (Φ.X y)),
        lin W (fun p : Fin (l * n) × Fin (s + 1) => a ((finProdFinEquiv.symm p.1).1, p.2)) β = n * lin W a β :=
      fun a β => (sum_rep (fun j => qW W β fun u => a (j, u))).trans (nsmul_eq_mul _ _)
    refine ⟨l * E, l' * D, E * D', fun p => a ((finProdFinEquiv.symm p.1).1, p.2),
      fun p => a' ((finProdFinEquiv.symm p.1).1, p.2), fun i => (Φ.u_unit y (fun v => a ((finProdFinEquiv.symm i).1, v))).choose,
      fun i => (Φ.u_unit y (fun v => a' ((finProdFinEquiv.symm i).1, v))).choose, Nat.mul_le_mul hE hD', ?_⟩
    have eA : Φ.coefT y (fun p : Fin (l * E) × Fin (s + 1) => a ((finProdFinEquiv.symm p.1).1, p.2))
        (fun i => (Φ.u_unit y (fun v => a ((finProdFinEquiv.symm i).1, v))).choose) =
        Φ.coefT y a (fun i => (Φ.u_unit y (fun v => a (i, v))).choose) ^ E := hrepc (n := E) a (fun i => (Φ.u_unit y (fun v => a (i, v))).choose)
    have eA' : Φ.coefT y (fun p : Fin (l' * D) × Fin (s + 1) => a' ((finProdFinEquiv.symm p.1).1, p.2))
        (fun i => (Φ.u_unit y (fun v => a' ((finProdFinEquiv.symm i).1, v))).choose) =
        Φ.coefT y a' (fun i => (Φ.u_unit y (fun v => a' (i, v))).choose) ^ D := hrepc (n := D) a' (fun i => (Φ.u_unit y (fun v => a' (i, v))).choose)
    have hwe : ev (w : Φ.V y) ≠ 0 := by simpa using hwne 1
    refine ⟨?_, ?_, fun β hβ => ?_, ⟨ev h ^ E / ev h' ^ D, div_mem (pow_mem (hO' h hh).1 _) (pow_mem (hO' h' hh').1 _), ?_⟩⟩
    · rw [eA]; exact (hunit a).pow _
    · rw [eA']; exact (hunit a').pow _
    · rw [hrepl a β, hrepl a' β, hlin β hβ, hlin' β hβ, LinearMap.zero_apply]
      push_cast; ring
    · rw [eA, eA', map_pow, map_pow, hhp, hhp']
      simp only [map_mul, map_pow]
      rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ (mul_ne_zero hce' (pow_ne_zero _ hwe)))]
      ring
