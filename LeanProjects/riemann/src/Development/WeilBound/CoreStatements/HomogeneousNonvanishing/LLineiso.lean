import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

namespace PositivityTheory.UnitarySelfGeneration

set_option linter.unusedSectionVars false

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem ll_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem ll_C (n : ℤ) : IsMultiHomog (C n : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_C, if_neg (Ne.symm h)] at hm
    exact hm rfl
  simp [this]

theorem ll_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem ll_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem ll_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine ll_add hf fun m hm k => hg m (by simpa using hm) k

theorem ll_Xpow [DecidableEq K] (k : K) (i : ι k) (n : ℕ) :
    IsMultiHomog ((X ⟨k, i⟩ : MRing ι) ^ n) (Pi.single k n) := by
  classical
  intro m hm k'
  rw [X_pow_eq_monomial] at hm
  have hm' := support_monomial_subset hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [this, h]

noncomputable def llMon (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k

theorem ll_mon (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (llMon c d) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, Pi.single k (d k)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (ll_one (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact ll_mul (ll_Xpow k (c k) _) ih
  have := key Finset.univ
  rwa [Finset.univ_sum_single] at this

theorem ll_mon_notMem {W : Ideal (MRing ι)} (hW : W.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (d : K → ℕ) : llMon c d ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).mp h
  exact hc k (hW.mem_of_pow_mem _ hk)

theorem ll_aeval_mon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (llMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [llMon]

theorem ll_mon_add (c : ∀ k, ι k) (d d' : K → ℕ) : llMon c (d + d') = llMon c d * llMon c d' := by
  simp [llMon, pow_add, Finset.prod_mul_distrib]

theorem ll_mem_of_zero (y : (Σ k, ι k) → Ω) {F : MRing ι} {α : K → ℕ} (hF : IsMultiHomog F α)
    (h0 : aeval y F = 0) : F ∈ mCoordIdeal y := by
  classical
  have key : mConeMap y F = C (aeval y F) * ∏ k, (X k : MvPolynomial K Ω) ^ α k := by
    rw [mConeMap, aeval_def, aeval_def, eval₂_eq', eval₂_eq', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h1 : ∏ p : (Σ k, ι k), (X p.1 : MvPolynomial K Ω) ^ m p = ∏ k, (X k : MvPolynomial K Ω) ^ α k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← hF m hm k]
      exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i => m ⟨k, i⟩) (X k : MvPolynomial K Ω)
    simp only [mul_pow, Finset.prod_mul_distrib, h1, map_mul, map_prod, map_pow, eq_intCast, map_intCast,
      mul_assoc]
  show mConeMap y F = 0
  rw [key, h0, map_zero, zero_mul]

theorem ll_zero_of_mem (y : (Σ k, ι k) → Ω) {F : MRing ι} (hF : F ∈ mCoordIdeal y) : aeval y F = 0 := by
  have h : mConeMap y F = 0 := hF
  have h2 : ((MvPolynomial.eval fun _ : K => (1 : Ω)).comp (mConeMap y).toRingHom) =
      (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) fun p => ?_
    simp [mConeMap]
  have h3 := congrArg (fun φ : MRing ι →+* Ω => φ F) h2
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h, map_zero] at h3
  exact h3.symm

theorem ll_shift (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a a' : K → ℤ) :
    aeval y (llMon c fun k => (a k - a' k).toNat) * ∏ k, y ⟨k, c k⟩ ^ a' k =
      aeval y (llMon c fun k => (a' k - a k).toNat) * ∏ k, y ⟨k, c k⟩ ^ a k := by
  rw [ll_aeval_mon, ll_aeval_mon, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]
  congr 1
  omega

def LlRep (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (s : Ω) (F : MRing ι) (α : K → ℕ) : Prop :=
  IsMultiHomog F α ∧ aeval y F = s * aeval y (llMon c α)

theorem llRep_add {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {s t : Ω} {F G : MRing ι} {α β : K → ℕ}
    (h : LlRep y c s F α) (h' : LlRep y c t G β) :
    LlRep y c (s + t) (F * llMon c β + llMon c α * G) (α + β) := by
  refine ⟨ll_add (ll_mul h.1 (ll_mon c β)) (ll_mul (ll_mon c α) h'.1), ?_⟩
  rw [map_add, map_mul, map_mul, ll_mon_add, map_mul, h.2, h'.2]
  ring

theorem llRep_mul {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {s t : Ω} {F G : MRing ι} {α β : K → ℕ}
    (h : LlRep y c s F α) (h' : LlRep y c t G β) : LlRep y c (s * t) (F * G) (α + β) := by
  refine ⟨ll_mul h.1 h'.1, ?_⟩
  rw [map_mul, ll_mon_add, map_mul, h.2, h'.2]
  ring

theorem llRep_exists (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (s : Ω)
    (hs : s ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → ι k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) :
    ∃ F α, LlRep y c s F α := by
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨llMon j 1, 1, ll_mon j 1, ?_⟩
    have : ∏ k, y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
    simp only [ll_aeval_mon, Pi.one_apply, pow_one]
    field_simp
  | algebraMap r => exact ⟨C r, 0, ll_C r, by simp [llMon]⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, α, h⟩ := hx
    obtain ⟨G, β, h'⟩ := hy
    exact ⟨_, _, llRep_add h h'⟩
  | mul x y _ _ hx hy =>
    obtain ⟨F, α, h⟩ := hx
    obtain ⟨G, β, h'⟩ := hy
    exact ⟨_, _, llRep_mul h h'⟩

theorem llRep_indep {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {W : Ideal (MRing ι)} (hW : W.IsPrime)
    (hPW : mCoordIdeal y ≤ W) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) {s : Ω} {F G : MRing ι} {α β : K → ℕ}
    (h : LlRep y c s F α) (h' : LlRep y c s G β) (hF : F ∈ W) : G ∈ W := by
  have h1 : F * llMon c β - llMon c α * G ∈ W := by
    refine hPW (ll_mem_of_zero y (ll_sub (ll_mul h.1 (ll_mon c β)) (ll_mul (ll_mon c α) h'.1)) ?_)
    rw [map_sub, map_mul, map_mul, h.2, h'.2]
    ring
  have h2 : llMon c α * G ∈ W := by
    have := W.sub_mem (W.mul_mem_right (llMon c β) hF) h1
    simpa using this
  exact (hW.mem_or_mem h2).resolve_left (ll_mon_notMem hW c hc α)

theorem ll_prime (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {W : Ideal (MRing ι)}
    (hW : W.IsPrime) (hPW : mCoordIdeal y ≤ W) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) :
    ∃ I : Ideal (Algebra.adjoin ℤ
      (Set.range fun j : (k : K) → ι k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)), I.IsPrime ∧
      ∀ s, s ∉ I → ∃ F α, LlRep y c s.1 F α ∧ F ∉ W := by
  let I : Ideal (Algebra.adjoin ℤ
      (Set.range fun j : (k : K) → ι k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) :=
    { carrier := {s | ∃ F α, LlRep y c s.1 F α ∧ F ∈ W}
      add_mem' := by
        rintro s t ⟨F, α, h, hF⟩ ⟨G, β, h', hG⟩
        exact ⟨_, _, llRep_add h h', W.add_mem (W.mul_mem_right _ hF) (W.mul_mem_left _ hG)⟩
      zero_mem' := ⟨0, 0, ⟨fun m hm => by simp at hm, by simp⟩, W.zero_mem⟩
      smul_mem' := by
        rintro r s ⟨F, α, h, hF⟩
        obtain ⟨G, β, h'⟩ := llRep_exists y c hy r.1 r.2
        exact ⟨_, _, llRep_mul h' h, W.mul_mem_left _ hF⟩ }
  have hI : ∀ s, s ∈ I ↔ ∃ F α, LlRep y c s.1 F α ∧ F ∈ W := fun s => Iff.rfl
  refine ⟨I, ⟨?_, ?_⟩, ?_⟩
  · rw [Ideal.ne_top_iff_one, hI]
    rintro ⟨F, α, h, hF⟩
    have h1 : LlRep y c (1 : Ω) (llMon c 0) 0 := ⟨ll_mon c 0, by simp⟩
    exact ll_mon_notMem hW c hc 0 (llRep_indep hW hPW hc h h1 hF)
  · intro s t hst
    obtain ⟨H, γ, h, hH⟩ := (hI _).1 hst
    obtain ⟨F, α, h1⟩ := llRep_exists y c hy s.1 s.2
    obtain ⟨G, β, h2⟩ := llRep_exists y c hy t.1 t.2
    rcases hW.mem_or_mem (llRep_indep hW hPW hc h (llRep_mul h1 h2) hH) with h3 | h3
    · exact Or.inl ((hI _).2 ⟨F, α, h1, h3⟩)
    · exact Or.inr ((hI _).2 ⟨G, β, h2, h3⟩)
  · intro s hs
    obtain ⟨F, α, h1⟩ := llRep_exists y c hy s.1 s.2
    exact ⟨F, α, h1, fun hF => hs ((hI _).2 ⟨F, α, h1, hF⟩)⟩

theorem ll_ratio {E : Type} [AddCommGroup E] [Module Ω E] (A : Subring Ω) {e : E} (he : e ≠ 0) {s t : Ω}
    (hs : s ≠ 0) (h : Submodule.span A {t • e} ≤ Submodule.span A {s • e}) : t / s ∈ A := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (h (Submodule.mem_span_singleton_self _))
  have h1 : ((r : Ω) * s) • e = t • e := by
    rw [mul_smul]
    exact hr
  have h2 : (r : Ω) * s = t := smul_left_injective Ω he h1
  rw [← h2, mul_div_cancel_right₀ _ hs]
  exact r.2

end

theorem l_lineiso : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (a a' : K → ℤ) (e₀ : E) (ρ : Ω), CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) → Birational y → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → L.IsDegOn Set.univ y a e₀ → L.IsDegOn Set.univ y a' (ρ • e₀) → ∃ f g : MRing ι, IsLineIso (mCoordIdeal y) a a' f g ∧ aeval y f = ρ * aeval y g := by
  intro X Ω _ ξ K _ ι _ y E _ _ L a a' e₀ ρ htie hbir hy hL hL'
  have hρ : ρ ≠ 0 := by
    rintro rfl
    exact hL'.1 (zero_smul _ _)
  choose c₀ hc₀ using hy
  have hz : ∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ b : K → ℤ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun c hc b => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
  have hm : ∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ b : K → ℕ, aeval y (llMon c b) ≠ 0 :=
    fun c hc b => by
      rw [ll_aeval_mon]
      exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  obtain ⟨d, G, H, hG, hH, hH0, hGH⟩ :=
    hbir (ρ * (∏ k, y ⟨k, c₀ k⟩ ^ a' k) / ∏ k, y ⟨k, c₀ k⟩ ^ a k)
  set pos : K → ℕ := fun k => (a k - a' k).toNat with hpos
  set neg : K → ℕ := fun k => (a' k - a k).toNat with hneg
  have hf : IsMultiHomog (G * llMon c₀ pos) (d + pos) := ll_mul hG (ll_mon _ _)
  have hg : IsMultiHomog (H * llMon c₀ neg) (d + neg) := ll_mul hH (ll_mon _ _)
  have hfg : aeval y (G * llMon c₀ pos) = ρ * aeval y (H * llMon c₀ neg) := by
    have h1 := ll_shift y c₀ hc₀ a a'
    have h2 := hz c₀ hc₀ a
    rw [map_mul, map_mul, hGH]
    field_simp
    linear_combination h1
  have hg0 : aeval y (H * llMon c₀ neg) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hH0 (hm c₀ hc₀ _)
  refine ⟨G * llMon c₀ pos, H * llMon c₀ neg, ⟨⟨d + pos, d + neg, hf, hg, fun k => ?_⟩, fun h => ?_,
    fun h => hg0 (ll_zero_of_mem y h), fun W hW hPW hr => ?_⟩, hfg⟩
  · simp only [Pi.add_apply, hpos, hneg]
    omega
  · have := ll_zero_of_mem y h
    rw [hfg] at this
    exact mul_ne_zero hρ hg0 this
  generalize G * llMon c₀ pos = f at hf hfg ⊢
  generalize H * llMon c₀ neg = g at hg hfg ⊢
  choose c hc using hr
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    classical
    intro k h0
    refine hc k (hPW (ll_mem_of_zero y (α := Pi.single k 1) ?_ (by simpa using h0)))
    simpa using ll_Xpow k (c k) 1
  obtain ⟨I, hI, hIW⟩ := ll_prime y c hyc hW hPW hc
  have hxc : (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hyc k
  obtain ⟨p, ⟨hp, hpI⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ _ _ htie c hxc I hI
  have e1 := hL.2 p trivial c hp
  have e2 := hL'.2 p trivial c hp
  rw [smul_smul] at e2
  have hA := hz c hyc a
  have hA' := hz c hyc a'
  set w : Ω := ((∏ k, y ⟨k, c k⟩ ^ a' k) * ρ) / ∏ k, y ⟨k, c k⟩ ^ a k with hw
  have hw1 : w ∈ regAt ξ p := ll_ratio _ hL.1 hA (e2.symm.trans e1).le
  have hw2 : w⁻¹ ∈ regAt ξ p := by
    rw [hw, inv_div]
    exact ll_ratio _ hL.1 (mul_ne_zero hA' hρ) (e1.symm.trans e2).le
  have hw0 : w ≠ 0 := div_ne_zero (mul_ne_zero hA' hρ) hA
  obtain ⟨s, hs, hsu, hsw⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ htie c p hp w).1 hw1
  have htu : unitAt ξ p (s * w) := ⟨mul_ne_zero hsu.1 hw0, mul_mem hsu.2.1 hw1, by
    rw [mul_inv]
    exact mul_mem hsu.2.2 hw2⟩
  obtain ⟨S, α, hS, hSW⟩ := hIW ⟨s, hs⟩ ((hpI ⟨s, hs⟩).2 hsu)
  obtain ⟨T, β, hT, hTW⟩ := hIW ⟨s * w, hsw⟩ ((hpI ⟨s * w, hsw⟩).2 htu)
  refine ⟨S * llMon c (β + neg), T * llMon c (α + pos),
    fun h => (hW.mem_or_mem h).elim hSW (ll_mon_notMem hW c hc _),
    fun h => (hW.mem_or_mem h).elim hTW (ll_mon_notMem hW c hc _), ?_⟩
  have h1 := ll_mul (ll_mul hS.1 (ll_mon c (β + neg))) hf
  have h2 := ll_mul (ll_mul hT.1 (ll_mon c (α + pos))) hg
  have h3 : β + (α + pos) + (d + neg) = α + (β + neg) + (d + pos) := by abel
  rw [h3] at h2
  refine ll_mem_of_zero y (ll_sub h1 h2) ?_
  have h4 := ll_shift y c hyc a a'
  have h5 : w * aeval y (llMon c pos) = ρ * aeval y (llMon c neg) := by
    rw [hw]
    field_simp
    linear_combination h4
  have hS2 : aeval y S = s * aeval y (llMon c α) := hS.2
  have hT2 : aeval y T = s * w * aeval y (llMon c β) := hT.2
  simp only [map_sub, map_mul, ll_mon_add, hS2, hT2, hfg]
  linear_combination (-(s * aeval y (llMon c α) * aeval y (llMon c β) * aeval y g)) * h5

end PositivityTheory.UnitarySelfGeneration
