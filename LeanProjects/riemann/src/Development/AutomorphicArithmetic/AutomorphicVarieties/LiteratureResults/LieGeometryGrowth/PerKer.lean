import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRhamInj
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Geo

section

variable {Γ M N : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

omit [Group Γ] [Module ℂ M] in
private theorem hd_cons (c : List Γ → M) (g : Γ) (x : List Γ) : hd c (g :: x) = c x - hd (fun y => c (g :: y)) x := by
  simp only [hd, List.length_cons, Finset.sum_range_succ', List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, pow_succ,
    mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, pow_zero, one_smul]
  abel

omit [Group Γ] [Module ℂ M] in
private theorem hd_congr {c c' : List Γ → M} {k : ℕ} (h : ∀ x : List Γ, x.length = k → c x = c' x) (x : List Γ)
    (hx : x.length = k + 1) : hd c x = hd c' x :=
  Finset.sum_congr rfl fun i hi => by
    rw [h _ (by rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi), hx]; rfl)]

omit [Group Γ] [Module ℂ M] in
private theorem hd_sub (c c' : List Γ → M) (x : List Γ) : hd (fun y => c y - c' y) x = hd c x - hd c' x := by
  simp only [hd, smul_sub, Finset.sum_sub_distrib]

omit [Group Γ] in
private theorem hd_map (f : M →ₗ[ℂ] N) (c : List Γ → M) (x : List Γ) : hd (fun y => f (c y)) x = f (hd c x) := by
  simp only [hd, map_sum, map_zsmul]

omit [Group Γ] [Module ℂ M] in
private theorem hd_hd (x : List Γ) : ∀ c : List Γ → M, hd (hd c) x = 0 := by
  induction x with
  | nil => intro c; simp [hd]
  | cons g x ih =>
    intro c
    rw [hd_cons]
    simp only [hd_cons]
    rw [hd_sub, ih]
    simp

private theorem hequiv_sub {ρ : Representation ℂ Γ M} {k : ℕ} {c c' : List Γ → M} (h : HEquiv ρ k c) (h' : HEquiv ρ k c') :
    HEquiv ρ k fun y => c y - c' y := fun γ x hx => by
  simp only [h γ x hx, h' γ x hx, map_sub]

private theorem contract {ρ : Representation ℂ Γ M} (hav : HasAverage ρ) {k : ℕ} {z : List Γ → M} (h : HEquiv ρ (k + 1) z)
    (hz : ∀ x : List Γ, x.length = k + 3 → hd z x = 0) :
    ∃ f, HEquiv ρ k f ∧ ∀ x : List Γ, x.length = k + 2 → z x = hd f x := by
  obtain ⟨P, h1, h2⟩ := hav
  refine ⟨fun x => P fun g => z (g :: x), fun γ x hx => ?_, fun x hx => ?_⟩
  · rw [h2]
    refine congrArg P (funext fun g => ?_)
    rw [← h γ _ (by simp [hx])]
    simp
  · rw [hd_map P (fun x g => z (g :: x)), ← h1 (z x)]
    congr 1
    funext g
    have := hz (g :: x) (by simp [hx])
    rw [hd_cons, sub_eq_zero] at this
    rw [this]
    simp [hd]

private theorem lift_ex {ρ : Representation ℂ Γ M} {σ : Representation ℂ Γ N} (f : M →ₗ[ℂ] N)
    (hf : ∀ γ m, f (ρ γ m) = σ γ (f m)) {k : ℕ} {e : List Γ → N} (h : HEquiv σ k e)
    (he : ∀ x : List Γ, x.length = k + 1 → ∃ m, f m = e x) :
    ∃ b, HEquiv ρ k b ∧ ∀ x : List Γ, x.length = k + 1 → f (b x) = e x := by
  classical
  choose! s hs using he
  refine ⟨fun x => ρ (x.headD 1) (s (x.map ((x.headD 1)⁻¹ * ·))), fun γ x hx => ?_, fun x hx => ?_⟩
  · cases x with
    | nil => simp at hx
    | cons g x =>
      have : ∀ y : Γ, (γ * g)⁻¹ * (γ * y) = g⁻¹ * y := fun y => by group
      simp only [List.map_cons, List.headD_cons, List.map_map, Function.comp_def, this, map_mul, Module.End.mul_apply]
  · rw [hf, hs _ (by simp [hx]), ← h _ _ (by simp [hx])]
    simp [Function.comp_def]

private theorem hequiv_hd {ρ : Representation ℂ Γ M} {k : ℕ} {c : List Γ → M} (h : HEquiv ρ k c) :
    HEquiv ρ (k + 1) (hd c) := fun γ x hx => by
  simp only [hd, map_sum, map_zsmul, List.length_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [List.eraseIdx_map, h γ _ (by rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi), hx]; rfl)]

end

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
  (G : Dr.Geo Γ V S d)

private theorem zig_pos (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (hav : ∀ q, HasAverage (G.act q))
    (c : List Γ → S → Fin d → ℂ) (n q : ℕ) : ∀ (k : ℕ) (u : List Γ → G.Om q), n = q + k → Zig G q (k + 1) u c →
    (HCob G.lev (n + 1) c ↔ ∃ e : List Γ → G.Om q, HEquiv (G.act q) k e ∧
      (∀ x : List Γ, x.length = k + 1 → G.dOm q (e x) = 0) ∧ ∀ x : List Γ, x.length = k + 2 → u x = hd e x) := by
  obtain ⟨a1, a2, a3⟩ := inclFacts Γ V S d G hc hn
  induction q with
  | zero =>
    intro k u hk hz
    obtain rfl : n = k := by omega
    constructor
    · rintro ⟨b, hb, hb'⟩
      refine ⟨fun x => G.incl (b x), fun γ x hx => ?_, fun x _ => a3.apply_apply_eq_zero _, fun x hx => ?_⟩
      · simp only [hb γ x hx, a1]
      · rw [hd_map, hz x hx, hb' x hx]
    · rintro ⟨e, h1, h2, h3⟩
      obtain ⟨b, hb, hb'⟩ := lift_ex G.incl a1 h1 fun x hx => (a3 _).1 (h2 x hx)
      refine ⟨b, hb, fun x hx => a2 ?_⟩
      rw [← hz x hx, h3 x hx, ← hd_map, hd_congr hb' x hx]
  | succ q ih =>
    rintro k u hk ⟨b, hb, hb', hz⟩
    rw [ih (k + 1) (hd b) (by omega) hz]
    constructor
    · rintro ⟨e, h1, h2, h3⟩
      obtain ⟨f, hf, hf'⟩ := contract (hav q) (hequiv_sub hb h1) fun x hx => by rw [hd_sub, h3 x hx, sub_self]
      refine ⟨fun x => G.dOm q (f x), fun γ x hx => ?_, fun x _ => (dExact Γ V S d G hc q).apply_apply_eq_zero _,
        fun x hx => ?_⟩
      · simp only [hf γ x hx, dEquiv Γ V S d G]
      · rw [hd_map, ← hf' x hx, map_sub, h2 x hx, hb' x hx, sub_zero]
    · rintro ⟨e, h1, h2, h3⟩
      obtain ⟨f, hf, hf'⟩ := lift_ex (G.dOm q) (dEquiv Γ V S d G q) h1 fun x hx =>
        (dExact Γ V S d G hc q _).1 (h2 x hx)
      refine ⟨fun x => b x - hd f x, hequiv_sub hb (hequiv_hd hf), fun x hx => ?_, fun x _ => ?_⟩
      · rw [map_sub, hb' x hx, h3 x hx, ← hd_map, hd_congr hf' x hx, sub_self]
      · rw [hd_sub, hd_hd, sub_zero]

private theorem zig_top (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (hav : ∀ q, HasAverage (G.act q))
    (c : List Γ → S → Fin d → ℂ) (q : ℕ) (w : G.Om q) (hz : Zig G q 0 (fun _ => w) c) :
    HCob G.lev q c ↔ InvExact (Ω := fun q => G.Om q) G.act G.dOm w := by
  obtain ⟨a1, a2, a3⟩ := inclFacts Γ V S d G hc hn
  have h2 : ∀ {M : Type} [AddCommGroup M] (e : List Γ → M) (g h : Γ), hd e [g, h] = e [h] - e [g] := fun e g h => by
    simp [hd, Finset.sum_range_succ, sub_eq_add_neg]
  cases q with
  | zero =>
    constructor
    · intro h
      have := hz [1] rfl
      rw [h [1] rfl, map_zero] at this
      exact this
    · intro h x hx
      have h0 : w = 0 := h
      exact a2 (by rw [← hz x hx, map_zero]; exact h0)
  | succ q =>
    obtain ⟨b, hb, hb', hz⟩ := hz
    rw [zig_pos G hc hn hav c q q 0 (hd b) rfl hz]
    constructor
    · rintro ⟨e, e1, e2, e3⟩
      refine ⟨b [1] - e [1], fun γ => ?_, ?_⟩
      · have := e3 [1, γ] rfl
        rw [h2, h2] at this
        have h4 := hequiv_sub hb e1 γ [1] rfl
        simp only [List.map_cons, List.map_nil, mul_one] at h4
        rw [← h4]
        exact sub_eq_sub_iff_sub_eq_sub.1 this
      · rw [map_sub, e2 [1] rfl, hb' [1] rfl, sub_zero]
    · rintro ⟨y, y1, y2⟩
      refine ⟨fun x => b x - y, hequiv_sub hb fun γ x _ => (y1 γ).symm, fun x hx => ?_, fun x hx => ?_⟩
      · rw [map_sub, hb' x hx, y2, sub_self]
      · obtain ⟨g, h, rfl⟩ := List.length_eq_two.1 hx
        rw [h2, h2]
        abel

end

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.perKer :
    PerKer := by
  rintro E _ _ _ a ha U hU Ξ q α c hα ⟨ho, w, hw, hz⟩
  obtain ⟨W, hW⟩ := window _ _ _ _ (geo ho U Ξ) (geoProper E a ho U Ξ hU)
  obtain ⟨u, hu⟩ := cutoff _ _ _ _ (geo ho U Ξ) W hW
  rw [← geo_lev ho U Ξ, zig_top (geo ho U Ξ) (coneConvex E a).1 ⟨_, hOne_mem_cone⟩ (average _ _ _ _ _ u hu) c q w hz]
  cases q with
  | zero =>
    constructor
    · intro h
      obtain rfl : w = 0 := h
      exact (corrUniq E a ho U Ξ 0).1 _ 0 _ hw (corr_zero U Ξ)
    · intro h
      obtain rfl : α = 0 := h
      exact (corrUniq E a ho U Ξ 0).2 0 _ 0 hw (corr_zero U Ξ)
  | succ q =>
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨l, hl⟩ := gauge E a ha ho U Ξ hU
      obtain ⟨y', i1, i2, i3⟩ := retract _ _ _ _ (geo ho U Ξ) (coneConvex E a).2 l hl q y hy
        ((corrBasic E a U Ξ _ _ _ hw).1 hα.basic)
      obtain ⟨η, hη⟩ := corrBwd E a ho U Ξ q y'
      have e : dCo (smLie Ξ) η = α := (corrUniq E a ho U Ξ (q + 1)).1 _ _ _ (i3 ▸ corrD E a ho U Ξ q _ _ hη) hw
      have b := (corrBasic E a U Ξ _ _ _ hη).2 i2
      obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hη
      exact ⟨η, ⟨c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hη).2 i1 X) (c2 X)
        (centralOf E a _ (smLie Ξ) q η b (e ▸ hα.basic) X)⟩, e⟩
    · rintro ⟨η, hη, rfl⟩
      have hv : ∀ X, LeftInv (η X) ∧ RightInv U (η X) := fun X => (levelVal E a U Ξ _).1 (hη.val X)
      obtain ⟨y, hy, h0⟩ := corrFwd E a U Ξ q η hη.equiv fun X => (hv X).2
      let y' : (geo ho U Ξ).Om q := ⟨y, fun s => ⟨corrSmooth E a U Ξ q _ y hy s, h0 s⟩⟩
      exact ⟨y', (corrInv E a ho U Ξ q _ y' hy).1 fun X => (hv X).1,
        (corrUniq E a ho U Ξ (q + 1)).2 _ _ _ (corrD E a ho U Ξ q _ y' hy) hw⟩
