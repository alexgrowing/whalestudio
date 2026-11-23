import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RankinHecke

open Ad3 Ad3.R

theorem inv_mul_mem_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ϖ : Fˣ) (h1 : ord (ϖ : F) = 1) {y : F} (hy : y ≠ 0) : ((ϖ⁻¹ : Fˣ) : F) * y ∈ 𝒪[F] ↔ 1 ≤ ord y := by
  have hne : ((ϖ⁻¹ : Fˣ) : F) * y ≠ 0 := mul_ne_zero (Units.ne_zero _) hy
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hne, ord_mul (Units.ne_zero _) hy, ord_units_inv, h1]
  omega

theorem natCast_ne_zero (v : Pl) {n : ℕ} (hn : n ≠ 0) : (n : Qv v) ≠ 0 := by
  intro hz
  have h : algebraMap ℚ (Qv v) (n : ℚ) = 0 := by rw [map_natCast]; exact hz
  have := (algebraMap ℚ (Qv v)).injective (h.trans (map_zero _).symm)
  exact hn (by exact_mod_cast this)

theorem ord_sub_eq (hB0 : B0) (v : Pl) {a b : ℕ} (ha : a < pOf v) (hb : b < pOf v) (hab : a ≠ b) :
    ((a : Qv v) - (b : Qv v)) ≠ 0 ∧ ord ((a : Qv v) - (b : Qv v)) = 0 := by
  obtain ⟨hl, -⟩ := hB0
  obtain ⟨-, -, hp, hp1, hn, -, -⟩ := hl v
  have key : ∀ c d : ℕ, c < d → d < pOf v → ((d : Qv v) - (c : Qv v)) ≠ 0 ∧ ord ((d : Qv v) - (c : Qv v)) = 0 := by
    intro c d hcd hd
    have e : (d : Qv v) - (c : Qv v) = ((d - c : ℕ) : Qv v) := by
      rw [Nat.cast_sub hcd.le]
    have h0 : d - c ≠ 0 := by omega
    have hnd : ¬ pOf v ∣ d - c := fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    have ho := hn (d - c) h0
    rw [Nat.factorization_eq_zero_of_not_dvd hnd] at ho
    rw [e]
    exact ⟨natCast_ne_zero v h0, by simpa using ho⟩
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨h1, h2⟩ := key a b h hb
    have e : (a : Qv v) - (b : Qv v) = -((b : Qv v) - (a : Qv v)) := by ring
    refine ⟨by rw [e]; exact neg_ne_zero.2 h1, ?_⟩
    rw [e, ord, Valuation.map_neg, ← ord, h2]
  · exact key b a h ha

theorem reps_range (hB0 : B0) (hC1 : C1) (v : Pl) (ϖ : (Qv v)ˣ) (hϖ : (ϖ : Qv v) = (pOf v : ℕ)) :
    Reps ϖ ((Finset.range (pOf v)).image (fun b : ℕ => (b : Qv v))) ∧
      Set.InjOn (fun b : ℕ => (b : Qv v)) (Finset.range (pOf v) : Set ℕ) := by
  have hB0' := hB0
  obtain ⟨hl, -⟩ := hB0'
  obtain ⟨hstd, hres, hp, hp1, hn, -, -⟩ := hl v
  have hord : ord (ϖ : Qv v) = 1 := by rw [hϖ]; exact hp1
  obtain ⟨⟨ϖ₀, B₀, hR₀⟩, hcard, -⟩ := hC1 (Qv v) (localAdelicChar ℚ v) hstd
  have hord₀ : ord (ϖ₀ : Qv v) = 1 := hR₀.1
  have hc₀ : B₀.card = pOf v := by rw [hcard ϖ₀ B₀ hR₀, hres]
  have hinj : Set.InjOn (fun b : ℕ => (b : Qv v)) (Finset.range (pOf v) : Set ℕ) := by
    intro a ha b hb hab
    by_contra hne
    exact (ord_sub_eq hB0 v (by simpa using ha) (by simpa using hb) hne).1 (sub_eq_zero.2 hab)
  have hint : ∀ n : ℕ, (n : Qv v) ∈ 𝒪[Qv v] := fun n => natCast_mem _ n

  have hex := fun n : ℕ => hR₀.2.2 (n : Qv v) (hint n)
  choose r hr hru using hex
  have hrinj : Set.InjOn r (Finset.range (pOf v) : Set ℕ) := by
    intro a ha b hb hab
    by_contra hne
    obtain ⟨h1, h2⟩ := ord_sub_eq hB0 v (by simpa using ha) (by simpa using hb) hne
    have e : ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * ((a : Qv v) - b) =
        ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * ((a : Qv v) - r a) - ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * ((b : Qv v) - r b) := by
      rw [hab]; ring
    have hm : ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * ((a : Qv v) - b) ∈ 𝒪[Qv v] := by
      rw [e]; exact sub_mem (hr a).2 (hr b).2
    have := (inv_mul_mem_iff ϖ₀ hord₀ h1).1 hm
    omega
  have himg : (Finset.range (pOf v)).image r = B₀ := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
      exact (hr n).1
    · rw [Finset.card_image_of_injOn hrinj, Finset.card_range, hc₀]
  refine ⟨⟨hord, ?_, ?_⟩, hinj⟩
  · intro b hb
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hb
    exact hint n
  · intro x hx
    obtain ⟨b₀, ⟨hb₀, hb₀'⟩, -⟩ := hR₀.2.2 x hx
    rw [← himg] at hb₀
    obtain ⟨n, hnr, rfl⟩ := Finset.mem_image.1 hb₀
    have hdiff : ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * (x - n) ∈ 𝒪[Qv v] := by
      have e : ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * (x - n) =
          ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * (x - r n) - ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * ((n : Qv v) - r n) := by ring
      rw [e]; exact sub_mem hb₀' (hr n).2
    have hconv : ∀ y : Qv v, ((ϖ₀⁻¹ : (Qv v)ˣ) : Qv v) * y ∈ 𝒪[Qv v] → ((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * y ∈ 𝒪[Qv v] := by
      intro y hy
      by_cases h0 : y = 0
      · rw [h0, mul_zero]; exact zero_mem _
      · exact (inv_mul_mem_iff ϖ hord h0).2 ((inv_mul_mem_iff ϖ₀ hord₀ h0).1 hy)
    refine ⟨(n : Qv v), ⟨Finset.mem_image.2 ⟨n, hnr, rfl⟩, hconv _ hdiff⟩, ?_⟩
    rintro b ⟨hb, hb'⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hb
    by_contra hne
    have hmn : m ≠ n := fun h => hne (by simp [h])
    obtain ⟨h1, h2⟩ := ord_sub_eq hB0 v (by simpa using hm) (by simpa using hnr) hmn
    have e : ((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * ((m : Qv v) - n) =
        ((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * (x - n) - ((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * (x - m) := by ring
    have hm' : ((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * ((m : Qv v) - n) ∈ 𝒪[Qv v] := by
      rw [e]; exact sub_mem (hconv _ hdiff) hb'
    have := (inv_mul_mem_iff ϖ hord h1).1 hm'
    omega

theorem infAt_finEmb (y : AdelicGLn.FiniteAdelicGL ℚ 2) (w : InfinitePlace ℚ) : infAt w (finEmb ℚ 2 y) = 1 := by
  show (AdelicGLn.infiniteEquiv ℚ 2 (AdelicGLn.prodEquiv ℚ 2 (finEmb ℚ 2 y)).1) w = 1
  rw [prodEquiv_finEmb, map_one]
  rfl

theorem finAt_finEmb (y : AdelicGLn.FiniteAdelicGL ℚ 2) (v : Pl) :
    finAt v (finEmb ℚ 2 y) = AdelicGLn.finiteRestrictedEquiv ℚ 2 y v := by
  show (AdelicGLn.finiteRestrictedEquiv ℚ 2 (AdelicGLn.prodEquiv ℚ 2 (finEmb ℚ 2 y)).2) v = _
  rw [prodEquiv_finEmb]

theorem finAt_finEmb_mem {u : AdelicGLn.FiniteAdelicGL ℚ 2} (hu : u ∈ AdelicGLn.integralFiniteGL ℚ 2) (v : Pl) :
    finAt v (finEmb ℚ 2 u) ∈ integralGL (Qv v) 2 := by
  rw [finAt_finEmb]
  exact (AdelicGLn.mem_integralFiniteGL_iff_forall ℚ 2).1 hu v

theorem congruence_local_component_of_global (hB0 : B0) (N : ℕ) [NeZero N] {v : Pl} (hv : pOf v ∣ N) {u : AdelicGLn.FiniteAdelicGL ℚ 2}
    (hu : u ∈ Gamma0Level N) : ∃ d, GammaZeroLevelMembership (N.factorization (pOf v)) (finAt v (finEmb ℚ 2 u)) d := by
  obtain ⟨hl, -⟩ := hB0
  obtain ⟨hstd, hres, hp, hp1, hn, -, -⟩ := hl v
  have hN0 : N ≠ 0 := NeZero.ne N
  have hxK := finAt_finEmb_mem hu.1 v
  set x := finAt v (finEmb ℚ 2 u) with hx
  have hn1 : 1 ≤ N.factorization (pOf v) := (hp.dvd_iff_one_le_factorization hN0).1 hv
  obtain ⟨t, ht, hut⟩ := hu.2
  have hx10 : x 1 0 = (N : Qv v) * t v := by
    have e1 : x 1 0 = (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 v := by
      rw [hx, finAt_finEmb]; rfl
    rw [e1, hut]
    exact (map_mul (adeleAt v) _ _).trans (by rw [map_natCast]; rfl)
  have htv : t v ∈ 𝒪[Qv v] := (mem_valuationInteger_iff v _).2 (mem_integralFiniteAdeles.1 ht v)
  have hord : x 1 0 = 0 ∨ ((N.factorization (pOf v) : ℕ) : ℤ) ≤ ord (x 1 0) := by
    by_cases h0 : t v = 0
    · left; rw [hx10, h0, mul_zero]
    · right
      have hNc := natCast_ne_zero v hN0
      rw [hx10, ord_mul hNc h0, hn N hN0]
      have : 0 ≤ ord (t v) := (mem_valBall_iff_le_ord h0).1 (mem_valBall_zero_iff.2 htv)
      omega
  have hinv := ((GLnLocal.mem_integralGL_iff (Qv v) 2).1 hxK).2
  have h11 : x 1 1 ≠ 0 := by
    intro h0
    have e : (x.val * (x⁻¹ : GL (Fin 2) (Qv v)).val) 1 1 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]; simp
    rw [Matrix.mul_apply, Fin.sum_univ_two] at e
    have e' : x 1 0 * (x⁻¹ : GL (Fin 2) (Qv v)) 0 1 = 1 := by
      have h0' : x.val 1 1 = 0 := h0
      rw [h0', zero_mul, add_zero] at e
      exact e
    have ha : x 1 0 ≠ 0 := fun h => by rw [h, zero_mul] at e'; exact zero_ne_one e'
    have hb : (x⁻¹ : GL (Fin 2) (Qv v)) 0 1 ≠ 0 := fun h => by rw [h, mul_zero] at e'; exact zero_ne_one e'
    have h1 := ord_mul ha hb
    rw [e', ord_one] at h1
    have h2 : 0 ≤ ord ((x⁻¹ : GL (Fin 2) (Qv v)) 0 1) := (mem_valBall_iff_le_ord hb).1 (mem_valBall_zero_iff.2 (hinv 0 1))
    rcases hord with h | h
    · exact ha h
    · omega
  refine ⟨Units.mk0 _ h11, hxK, ?_, rfl⟩
  rcases hord with h | h
  · rw [h, mul_zero]; exact zero_mem _
  · by_cases h0 : x 1 0 = 0
    · rw [h0, mul_zero]; exact zero_mem _
    · have hu' : ((((unifUnit (Qv v))⁻¹ ^ (N.factorization (pOf v)) : (Qv v)ˣ)) : Qv v) ≠ 0 := Units.ne_zero _
      rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord (mul_ne_zero hu' h0), ord_mul hu' h0]
      have e : ord ((((unifUnit (Qv v))⁻¹ ^ (N.factorization (pOf v)) : (Qv v)ˣ)) : Qv v) = -((N.factorization (pOf v) : ℕ) : ℤ) := by
        rw [← zpow_natCast, ord_units_zpow, ord_units_inv, ord_unifUnit]; ring
      omega

theorem loc_mul {v : Pl} {x x' : GL (Fin 2) (Qv v)} {h h' : G2} (a : IsLoc2 v x h) (b : IsLoc2 v x' h') :
    IsLoc2 v (x * x') (h * h') :=
  ⟨by rw [Reduction.finAt_mul, a.1, b.1], fun v' hv => by rw [Reduction.finAt_mul, a.2.1 v' hv, b.2.1 v' hv, one_mul],
    fun w => by rw [Reduction.infAt_mul, a.2.2, b.2.2, one_mul]⟩

theorem loc_unique (hB0 : B0) {v : Pl} {x : GL (Fin 2) (Qv v)} {h h' : G2} (a : IsLoc2 v x h) (b : IsLoc2 v x h') : h = h' :=
  hB0.2.2.2.1 h h' (fun v' => by
    by_cases e : v' = v
    · subst e; rw [a.1, b.1]
    · rw [a.2.1 v' e, b.2.1 v' e]) (fun w => by rw [a.2.2, b.2.2])

theorem exists_loc (hB0 : B0) (v : Pl) (x : GL (Fin 2) (Qv v)) : ∃ h, IsLoc2 v x h := (hB0.1 v).2.2.2.2.2.1 x

theorem comm_loc (hB0 : B0) {v : Pl} {x : GL (Fin 2) (Qv v)} {h y : G2} (a : IsLoc2 v x h) (hy : finAt v y = 1) :
    y * h = h * y :=
  hB0.2.2.2.1 _ _ (fun v' => by
    rw [Reduction.finAt_mul, Reduction.finAt_mul]
    by_cases e : v' = v
    · subst e; rw [hy, one_mul, mul_one]
    · rw [a.2.1 v' e, one_mul, mul_one]) (fun w => by
    rw [Reduction.infAt_mul, Reduction.infAt_mul, a.2.2, one_mul, mul_one])

theorem locfn_mul {v : Pl} {φ : G2 → ℂ} {g : G2} {W : GL (Fin 2) (Qv v) → ℂ} (hW : LocFn v φ g W)
    {x x' : GL (Fin 2) (Qv v)} {h h' : G2} (a : IsLoc2 v x h) (b : IsLoc2 v x' h') : W (x * x') = φ (g * h * h') := by
  rw [hW _ _ (loc_mul a b), mul_assoc]

theorem exists_locfn (hB0 : B0) (v : Pl) (φ : G2 → ℂ) (g : G2) : ∃ W, LocFn v φ g W := by
  choose H hH using exists_loc hB0 v
  exact ⟨fun x => φ (g * H x), fun x h a => by show φ (g * H x) = _; rw [loc_unique hB0 (hH x) a]⟩

theorem scalar_of_level (hB0 : B0) (N : ℕ) [NeZero N] (ω : HeckeCharacter ℚ) (φ : G2 → ℂ)
    (hbad : ∀ v, pOf v ∣ N → ∀ x d, GammaZeroLevelMembership (N.factorization (pOf v)) x d → ∀ h, IsLoc2 v x h → ∀ g,
      φ (g * h) = (localChar ω v d : ℂ) * φ g)
    (hglob : ∀ κ : KA, (∀ w, infAt w κ.1 = 1) → (∀ v, pOf v ∣ N → finAt v κ.1 = 1) → ∀ g, φ (g * κ.1) = φ g)
    {u : AdelicGLn.FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) : ∃ c : ℂ, ∀ g, φ (g * finEmb ℚ 2 u) = c * φ g := by
  have hfin : {v : Pl | pOf v ∣ N}.Finite := by
    have hd : ((Nat.divisors N : Finset ℕ) : Set ℕ).Finite := (Nat.divisors N).finite_toSet
    refine (Set.Finite.preimage (f := pOf) (hB0.2.1.injOn) hd).subset fun v hv => ?_
    exact Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨hv, NeZero.ne N⟩)
  have key : ∀ S : Finset Pl, (∀ v ∈ S, pOf v ∣ N) → ∃ (h : G2) (c : ℂ), (∀ v ∈ S, finAt v h = finAt v (finEmb ℚ 2 u)) ∧
      (∀ v ∉ S, finAt v h = 1) ∧ (∀ w, infAt w h = 1) ∧ ∀ g, φ (g * h) = c * φ g := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => ⟨1, 1, by simp, by simp, by simp, by simp⟩
    | insert v S hvS ih =>
      intro hS
      obtain ⟨h₁, c₁, a₁, a₂, a₃, a₄⟩ := ih fun v' hv' => hS v' (Finset.mem_insert_of_mem hv')
      obtain ⟨hv, hl⟩ := exists_loc hB0 v (finAt v (finEmb ℚ 2 u))
      obtain ⟨d, hd⟩ := congruence_local_component_of_global hB0 N (hS v (Finset.mem_insert_self _ _)) hu
      refine ⟨h₁ * hv, (localChar ω v d : ℂ) * c₁, ?_, ?_, ?_, ?_⟩
      · intro v' hv'
        rw [Reduction.finAt_mul]
        by_cases e : v' = v
        · subst e; rw [a₂ _ hvS, hl.1, one_mul]
        · rw [hl.2.1 v' e, mul_one, a₁ v' ((Finset.mem_insert.1 hv').resolve_left e)]
      · intro v' hv'
        have e : v' ≠ v := fun e => hv' (e ▸ Finset.mem_insert_self _ _)
        rw [Reduction.finAt_mul, hl.2.1 v' e, a₂ v' fun h => hv' (Finset.mem_insert_of_mem h), one_mul]
      · intro w
        rw [Reduction.infAt_mul, a₃, hl.2.2, one_mul]
      · intro g
        rw [← mul_assoc, hbad v (hS v (Finset.mem_insert_self _ _)) _ d hd _ hl, a₄, mul_assoc]
  obtain ⟨h, c, a₁, a₂, a₃, a₄⟩ := key hfin.toFinset fun v hv => hfin.mem_toFinset.1 hv
  have hmem : h⁻¹ * finEmb ℚ 2 u ∈ (maxCompact : Subgroup G2) := by
    refine Reduction.mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩
    · rw [Reduction.infAt_mul, Reduction.infAt_inv, a₃, infAt_finEmb, inv_one, one_mul]
      exact one_mem _
    · rw [Reduction.finAt_mul, Reduction.finAt_inv]
      by_cases hv : v ∈ hfin.toFinset
      · rw [a₁ v hv, inv_mul_cancel]; exact one_mem _
      · rw [a₂ v hv, inv_one, one_mul]
        exact finAt_finEmb_mem hu.1 v
  refine ⟨c, fun g => ?_⟩
  have e := hglob ⟨_, hmem⟩ (fun w => by
    show infAt w (h⁻¹ * finEmb ℚ 2 u) = 1
    rw [Reduction.infAt_mul, Reduction.infAt_inv, a₃, infAt_finEmb, inv_one, one_mul]) (fun v hv => by
    show finAt v (h⁻¹ * finEmb ℚ 2 u) = 1
    rw [Reduction.finAt_mul, Reduction.finAt_inv, a₁ v (hfin.mem_toFinset.2 hv), inv_mul_cancel]) (g * h)
  have e' : g * h * (h⁻¹ * finEmb ℚ 2 u) = g * finEmb ℚ 2 u := by group
  simp only [e'] at e
  rw [e, a₄]

theorem move_past (hB0 : B0) {v : Pl} {φ : G2 → ℂ} {y h : G2} {c₀ c₁ : ℂ} (hc₁ : c₁ ≠ 0) {x₀ : GL (Fin 2) (Qv v)}
    (hl : IsLoc2 v x₀ h) (hfa : finAt v y = x₀) (h0 : ∀ g, φ (g * y) = c₀ * φ g) (h1 : ∀ g, φ (g * h) = c₁ * φ g)
    {x : GL (Fin 2) (Qv v)} {t : G2} (ht : IsLoc2 v x t) (g : G2) : φ (g * y * t) = c₀ * c₁⁻¹ * φ (g * h * t) := by
  have hinv : ∀ g', φ (g' * h⁻¹) = c₁⁻¹ * φ g' := fun g' => by
    have := h1 (g' * h⁻¹)
    rw [inv_mul_cancel_right] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hc₁, one_mul]
  have hy' : finAt v (h⁻¹ * y) = 1 := by
    rw [Reduction.finAt_mul, Reduction.finAt_inv, hl.1, hfa, inv_mul_cancel]
  have hc := comm_loc hB0 ht hy'
  have e : g * y * t = g * h * t * (h⁻¹ * y) := by
    calc g * y * t = g * h * ((h⁻¹ * y) * t) := by group
      _ = g * h * (t * (h⁻¹ * y)) := by rw [hc]
      _ = _ := by group
  have e2 : ∀ g', φ (g' * (h⁻¹ * y)) = c₀ * c₁⁻¹ * φ g' := fun g' => by
    rw [← mul_assoc, h0, hinv, mul_assoc]
  rw [e]
  exact e2 _

theorem W_bad (hB0 : B0) {v : Pl} {n : ℕ} {ω' : (Qv v)ˣ →* ℂˣ} {φ : G2 → ℂ} {g : G2} {W : GL (Fin 2) (Qv v) → ℂ}
    (hW : LocFn v φ g W)
    (hbad : ∀ x d, GammaZeroLevelMembership n x d → ∀ h, IsLoc2 v x h → ∀ g, φ (g * h) = (ω' d : ℂ) * φ g) :
    ∀ x d, GammaZeroLevelMembership n x d → ∀ g', W (g' * x) = ((ω' d : ℂˣ) : ℂ) * W g' := by
  intro x d hd g'
  obtain ⟨h', a⟩ := exists_loc hB0 v g'
  obtain ⟨h, b⟩ := exists_loc hB0 v x
  rw [locfn_mul hW a b, hbad x d hd h b, hW g' h' a]

theorem W_good (hB0 : B0) {v : Pl} {φ : G2 → ℂ} {g : G2} {W : GL (Fin 2) (Qv v) → ℂ} (hW : LocFn v φ g W)
    (hgood : ∀ x ∈ integralGL (Qv v) 2, ∀ h, IsLoc2 v x h → ∀ g, φ (g * h) = φ g) :
    ∀ x ∈ integralGL (Qv v) 2, ∀ g', W (g' * x) = W g' := by
  intro x hx g'
  obtain ⟨h', a⟩ := exists_loc hB0 v g'
  obtain ⟨h, b⟩ := exists_loc hB0 v x
  rw [locfn_mul hW a b, hgood x hx h b, hW g' h' a]

theorem sum_eq_sum_wPositions {v : Pl} {φ : G2 → ℂ} {g : G2} {W : GL (Fin 2) (Qv v) → ℂ} (hW : LocFn v φ g W) (ϖ : (Qv v)ˣ)
    {x : GL (Fin 2) (Qv v)} {h : G2} (a : IsLoc2 v x h) {t : ℕ → G2} (ht : ∀ b : ℕ, IsLoc2 v (upm ϖ b) (t b))
    (hinj : Set.InjOn (fun b : ℕ => (b : Qv v)) (Finset.range (pOf v) : Set ℕ)) :
    ∑ b ∈ (Finset.range (pOf v)).image (fun b : ℕ => (b : Qv v)), W (x * upm ϖ b) =
      ∑ b ∈ Finset.range (pOf v), φ (g * h * t b) := by
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun b _ => locfn_mul hW a (ht b)

theorem whittaker_hecke_coset_sum {v : Pl} {φ : G2 → ℂ} {g : G2} {W : GL (Fin 2) (Qv v) → ℂ} (hW : LocFn v φ g W) (ϖ : (Qv v)ˣ)
    {t : ℕ → G2} (ht : ∀ b : ℕ, IsLoc2 v (upm ϖ b) (t b))
    (hinj : Set.InjOn (fun b : ℕ => (b : Qv v)) (Finset.range (pOf v) : Set ℕ)) :
    ∑ b ∈ (Finset.range (pOf v)).image (fun b : ℕ => (b : Qv v)), W (upm ϖ b) =
      ∑ b ∈ Finset.range (pOf v), φ (g * t b) := by
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun b _ => hW _ _ (ht b)

theorem eq_of_decomposition (N : ℕ) [NeZero N] {φ T : G2 → ℂ} (lam : ℂ) (hφ : LInv φ) (hT : LInv T)
    (hreal : ∀ x : GL (Fin 2) ℝ, 0 < x.det.val → T (realEmb x) = lam * φ (realEmb x))
    (hc : ∀ u ∈ Gamma0Level N, ∃ c : ℂ, (∀ g, φ (g * finEmb ℚ 2 u) = c * φ g) ∧ ∀ g, T (g * finEmb ℚ 2 u) = c * T g)
    (g : G2) : T g = lam * φ g := by
  obtain ⟨γ, r, hr, u, hu, rfl⟩ := GL2Classical.exists_decomposition N g
  obtain ⟨c, h1, h2⟩ := hc u hu
  rw [h1, h2, hT γ, hφ γ, hreal r hr]
  ring

theorem filtration_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {χ : Fˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n) (h : quasiCharConductor χ = n) : unitFiltrationUnits F n ≤ χ.ker := by
  have hne : {m | unitFiltrationUnits F m ≤ χ.ker}.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have h0 : quasiCharConductor χ = 0 := by
      unfold quasiCharConductor
      rw [hc]
      simp
    omega
  have := Nat.sInf_mem hne
  rw [← h]
  exact this

theorem identity_mem_local_congruence (n : ℕ) (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    GammaZeroLevelMembership n (1 : GL (Fin 2) F) 1 :=
  ⟨one_mem _, by simp, by simp⟩

theorem hecke_std (hB0 : B0) (hC0 : C0) (hC1 : C1) (N : ℕ) [NeZero N] (ω : HeckeCharacter ℚ) (φ : G2 → ℂ) (lam : ℂ) (v : Pl)
    (hleft : LInv φ)
    (hgood : ∀ v, ¬ pOf v ∣ N → ∀ x ∈ integralGL (Qv v) 2, ∀ h, IsLoc2 v x h → ∀ g, φ (g * h) = φ g)
    (hbad : ∀ v, pOf v ∣ N → ∀ x d, GammaZeroLevelMembership (N.factorization (pOf v)) x d → ∀ h, IsLoc2 v x h → ∀ g,
      φ (g * h) = (localChar ω v d : ℂ) * φ g)
    (hglob : ∀ κ : KA, (∀ w, infAt w κ.1 = 1) → (∀ v, pOf v ∣ N → finAt v κ.1 = 1) → ∀ g, φ (g * κ.1) = φ g)
    (hcond : pOf v ∣ N → quasiCharConductor (localChar ω v) = N.factorization (pOf v))
    (ϖ : (Qv v)ˣ) (hϖ : (ϖ : Qv v) = (pOf v : ℕ)) (t : ℕ → G2) (t' : G2)
    (ht : ∀ b : ℕ, IsLoc2 v (upm ϖ b) (t b)) (ht' : IsLoc2 v (dg2 1 ϖ) t')
    (hreal : ∀ x : GL (Fin 2) ℝ, 0 < x.det.val →
      ∑ b ∈ Finset.range (pOf v), φ (realEmb x * t b) + (if pOf v ∣ N then 0 else φ (realEmb x * t')) = lam * φ (realEmb x))
    (g : G2) :
    ∑ b ∈ Finset.range (pOf v), φ (g * t b) + (if pOf v ∣ N then 0 else φ (g * t')) = lam * φ g := by
  obtain ⟨hR, hinj⟩ := reps_range hB0 hC1 v ϖ hϖ
  have hstd := (hB0.1 v).1
  have hp := (hB0.1 v).2.2.1
  refine eq_of_decomposition (T := fun g => ∑ b ∈ Finset.range (pOf v), φ (g * t b) + (if pOf v ∣ N then 0 else φ (g * t')))
    N lam hleft ?_ hreal ?_ g
  · intro γ g'
    simp only [mul_assoc, hleft γ]
  intro u hu
  obtain ⟨c₀, h0⟩ := scalar_of_level hB0 N ω φ (hbad) hglob hu
  refine ⟨c₀, h0, fun g' => ?_⟩
  obtain ⟨W, hW⟩ := exists_locfn hB0 v φ g'
  obtain ⟨h, hl⟩ := exists_loc hB0 v (finAt v (finEmb ℚ 2 u))
  by_cases hv : pOf v ∣ N
  · have hn1 : 1 ≤ N.factorization (pOf v) := (hp.dvd_iff_one_le_factorization (NeZero.ne N)).1 hv
    obtain ⟨d, hd⟩ := congruence_local_component_of_global hB0 N hv hu
    have hc₁ : ((localChar ω v d : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hm := fun b => move_past hB0 hc₁ hl rfl h0 (hbad v hv _ d hd h hl) (ht b) g'
    have hsum := (hC1 (Qv v) (localAdelicChar ℚ v) hstd).2.2 (localChar ω v) (N.factorization (pOf v)) W hn1
      (filtration_le hn1 (hcond hv)) (W_bad hB0 hW (hbad v hv)) ϖ _ ϖ _ hR hR _ d hd 1
    simp only [one_mul] at hsum
    rw [sum_eq_sum_wPositions hW ϖ hl ht hinj, whittaker_hecke_coset_sum hW ϖ ht hinj] at hsum
    simp only [if_pos hv, add_zero, hm, ← Finset.mul_sum, hsum]
    field_simp
  · have hK := finAt_finEmb_mem hu.1 v
    have hm := fun b => move_past (c₁ := 1) hB0 one_ne_zero hl rfl h0
      (fun g => by rw [one_mul]; exact hgood v hv _ hK h hl g) (ht b) g'
    have hm' := move_past (c₁ := 1) hB0 one_ne_zero hl rfl h0
      (fun g => by rw [one_mul]; exact hgood v hv _ hK h hl g) ht' g'
    have hsum := hC0 (Qv v) (localAdelicChar ℚ v) hstd W (W_good hB0 hW (hgood v hv)) ϖ _ ϖ _ hR hR _ hK 1
    simp only [one_mul] at hsum
    rw [sum_eq_sum_wPositions hW ϖ hl ht hinj, whittaker_hecke_coset_sum hW ϖ ht hinj, locfn_mul hW hl ht', hW _ _ ht'] at hsum
    simp only [if_neg hv, hm, hm', ← Finset.mul_sum, inv_one, mul_one]
    rw [← mul_add, hsum, mul_add]

theorem hecke_types_of_lift : B0 → C0 → C1 → F0b → F1 → AutomorphicLevelEquivariance → HeckeSumLocalTranslates → F3 := by
  intro hB0 hC0 hC1 hF0b hF1 hF1b hF3a k N _ hk χ hχ f a hf ha ω φ hω hL
  obtain ⟨hgood, hbad, hglob⟩ := hF1b k N hk χ hχ f a hf ha ω φ hω hL
  have hOm := hF0b k N χ hχ (hF1 k N χ f a hf ha.2.1 ω hω).1 ω hω
  have h3a := hF3a k N hk χ hχ f a hf ha ω φ hω hL
  have core : ∀ v, ∃ (ϖ : (Qv v)ˣ) (t : ℕ → G2) (t' : G2), (∀ b : ℕ, IsLoc2 v (upm ϖ b) (t b)) ∧ IsLoc2 v (dg2 1 ϖ) t' ∧
      Reps ϖ ((Finset.range (pOf v)).image (fun b : ℕ => (b : Qv v))) ∧
      Set.InjOn (fun b : ℕ => (b : Qv v)) (Finset.range (pOf v) : Set ℕ) ∧ ∀ g,
      ∑ b ∈ Finset.range (pOf v), φ (g * t b) + (if pOf v ∣ N then 0 else φ (g * t')) = lamOf k a v * φ g := by
    intro v
    have hp := (hB0.1 v).2.2.1
    let ϖ : (Qv v)ˣ := Units.mk0 ((pOf v : ℕ) : Qv v) (natCast_ne_zero v hp.ne_zero)
    have hϖ : (ϖ : Qv v) = (pOf v : ℕ) := rfl
    choose t ht using fun b : ℕ => exists_loc hB0 v (upm ϖ b)
    obtain ⟨t', ht'⟩ := exists_loc hB0 v (dg2 1 ϖ)
    obtain ⟨hR, hinj⟩ := reps_range hB0 hC1 v ϖ hϖ
    exact ⟨ϖ, t, t', ht, ht', hR, hinj, hecke_std hB0 hC0 hC1 N ω φ (lamOf k a v) v hL.left hgood hbad hglob (hOm.bad v) ϖ hϖ t t' ht ht'
      (h3a v ϖ hϖ t t' ht ht')⟩
  refine ⟨fun v hv g W hW => ⟨W_good hB0 hW (hgood v hv), fun ϖ' B' hR' g' => ?_⟩, fun v hv g W hW => ⟨W_bad hB0 hW (hbad v hv), fun ϖ' B' hR' g' => ?_⟩, hglob⟩
  · obtain ⟨ϖ, t, t', ht, ht', hR, hinj, hc⟩ := core v
    have hstd := (hB0.1 v).1
    obtain ⟨h', a'⟩ := exists_loc hB0 v g'
    have hsum := hC0 (Qv v) (localAdelicChar ℚ v) hstd W (W_good hB0 hW (hgood v hv)) ϖ' B' ϖ _ hR' hR 1 (one_mem _) g'
    simp only [mul_one] at hsum
    rw [hsum, sum_eq_sum_wPositions hW ϖ a' ht hinj, locfn_mul hW a' ht', hW _ _ a']
    have := hc (g * h')
    rwa [if_neg hv] at this
  · obtain ⟨ϖ, t, t', ht, ht', hR, hinj, hc⟩ := core v
    have hstd := (hB0.1 v).1
    have hp := (hB0.1 v).2.2.1
    have hn1 : 1 ≤ N.factorization (pOf v) := (hp.dvd_iff_one_le_factorization (NeZero.ne N)).1 hv
    obtain ⟨h', a'⟩ := exists_loc hB0 v g'
    have hsum := (hC1 (Qv v) (localAdelicChar ℚ v) hstd).2.2 (localChar ω v) (N.factorization (pOf v)) W hn1
      (filtration_le hn1 (hOm.bad v hv)) (W_bad hB0 hW (hbad v hv)) ϖ' B' ϖ _ hR' hR 1 1 (identity_mem_local_congruence _ _) g'
    simp only [mul_one, map_one, Units.val_one, one_mul] at hsum
    rw [hsum, sum_eq_sum_wPositions hW ϖ a' ht hinj, hW _ _ a']
    have := hc (g * h')
    rwa [if_pos hv, add_zero] at this

end GlobalTheory.CompanionTheory.RankinHecke
