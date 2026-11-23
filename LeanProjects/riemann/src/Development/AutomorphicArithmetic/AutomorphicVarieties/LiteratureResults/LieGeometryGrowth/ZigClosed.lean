import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DeRhamInjOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.InclFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ConeConvex
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrFwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Dr

section Hom

variable {Γ M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

omit [Module ℂ M] in
private theorem hd_cons (c : List Γ → M) (g : Γ) (t : List Γ) :
    hd c (g :: t) = c t - hd (fun s => c (g :: s)) t := by
  simp only [hd, List.length_cons, Finset.sum_range_succ', List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, pow_succ,
    pow_zero, one_smul, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  abel

omit [Module ℂ M] in
private theorem hd_sub (c c' : List Γ → M) (x : List Γ) : hd (fun s => c s - c' s) x = hd c x - hd c' x := by
  simp only [hd, smul_sub, Finset.sum_sub_distrib]

omit [Module ℂ M] in
private theorem hd_hd (x : List Γ) : ∀ c : List Γ → M, hd (hd c) x = 0 := by
  induction x with
  | nil => intro c; simp [hd]
  | cons g t ih =>
    intro c
    rw [hd_cons]
    simp only [hd_cons]
    rw [hd_sub, ih]
    simp

private theorem hd_lin (c c' : List Γ → M) (s t : ℂ) : hd (s • c + t • c') = s • hd c + t • hd c' := by
  funext x
  simp only [hd, Pi.add_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_comm s, smul_comm t]

private theorem map_hd (f : M →ₗ[ℂ] N) (c : List Γ → M) (c' : List Γ → N) (k : ℕ)
    (h : ∀ x : List Γ, x.length = k + 1 → f (c x) = c' x) (x : List Γ) (hx : x.length = k + 2) :
    f (hd c x) = hd c' x := by
  simp only [hd, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h]
  rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi), hx]; rfl

variable [Group Γ]

private theorem hequiv_hd (ρ : Representation ℂ Γ M) (k : ℕ) (c : List Γ → M) (h : HEquiv ρ k c) :
    HEquiv ρ (k + 1) (hd c) := fun γ x hx => by
  rw [map_hd (ρ γ) c (fun y => c (y.map (γ * ·))) k (fun y hy => (h γ y hy).symm) x hx]
  simp only [hd, List.length_map, List.eraseIdx_map]

private theorem lift_equiv (ρ : Representation ℂ Γ M) (ρ' : Representation ℂ Γ N) (f : M →ₗ[ℂ] N)
    (hf : ∀ γ m, f (ρ γ m) = ρ' γ (f m)) (k : ℕ) (u : List Γ → N) (hu : HEquiv ρ' k u)
    (h : ∀ x : List Γ, x.length = k + 1 → ∃ m, f m = u x) :
    ∃ b, HEquiv ρ k b ∧ ∀ x : List Γ, x.length = k + 1 → f (b x) = u x := by
  have h' : ∀ x : List Γ, ∃ m, x.length = k + 1 → f m = u x := fun x => by
    by_cases hx : x.length = k + 1
    · obtain ⟨m, hm⟩ := h x hx
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun e => absurd e hx⟩
  choose p hp using h'
  refine ⟨fun x => ρ (x.headD 1) (p (x.map ((x.headD 1)⁻¹ * ·))), fun γ x hx => ?_, fun x hx => ?_⟩
  · cases x with
    | nil => simp at hx
    | cons g t =>
      have e : (List.map (fun x => γ * x) (g :: t)).map ((γ * g)⁻¹ * ·) = (g :: t).map (g⁻¹ * ·) := by
        rw [List.map_map]
        congr 1
        funext y
        simp [mul_assoc]
      have e2 : (List.map (fun x => γ * x) (g :: t)).headD 1 = γ * g := rfl
      simp only [e2, e, List.headD_cons, map_mul, Module.End.mul_apply]
  · rw [hf, hp _ (by rw [List.length_map, hx]), hu _ _ hx, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]

end Hom

section Zig

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
  (G : Dr.Geo Γ V S d)

private theorem zig_ex (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (q : ℕ) : ∀ (k : ℕ) (u : List Γ → G.Om q),
    HEquiv (G.act q) k u → (∀ x : List Γ, x.length = k + 1 → G.dOm q (u x) = 0) →
    (∀ x : List Γ, x.length = k + 2 → hd u x = 0) → ∃ c, Zig G q k u c := by
  induction q with
  | zero =>
    intro k u h1 h2 _
    obtain ⟨a1, -, a3⟩ := inclFacts Γ V S d G hc hn
    obtain ⟨b, -, hb⟩ := lift_equiv G.lev (G.act 0) G.incl a1 k u h1 fun x hx => (a3 _).1 (h2 x hx)
    exact ⟨b, fun x hx => (hb x hx).symm⟩
  | succ q ih =>
    intro k u h1 h2 h3
    obtain ⟨b, hb1, hb⟩ := lift_equiv (G.act q) (G.act (q + 1)) (G.dOm q) (dEquiv Γ V S d G q) k u h1
      fun x hx => (dExact Γ V S d G hc q _).1 (h2 x hx)
    obtain ⟨c, hc⟩ := ih (k + 1) (hd b) (hequiv_hd _ _ _ hb1)
      (fun x hx => (map_hd _ _ _ k hb x hx).trans (h3 x hx)) fun x _ => hd_hd x b
    exact ⟨c, b, hb1, hb, hc⟩

private theorem zig_coc (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (q : ℕ) : ∀ (k n : ℕ) (u : List Γ → G.Om q) c,
    k + q = n → HEquiv (G.act q) k u → (∀ x : List Γ, x.length = k + 2 → hd u x = 0) → Zig G q k u c →
    HCoc G.lev n c := by
  induction q with
  | zero =>
    rintro k n u c rfl h1 h3 hz
    obtain ⟨a1, a2, -⟩ := inclFacts Γ V S d G hc hn
    refine ⟨fun γ x hx => a2 ?_, fun x hx => a2 ?_⟩
    · rw [a1, ← hz x hx, ← hz _ (by rw [List.length_map]; exact hx), h1 γ x hx]
    · rw [map_hd _ _ u k (fun y hy => (hz y hy).symm) x hx, h3 x hx, map_zero]
  | succ q ih =>
    rintro k n u c e - - ⟨b, hb1, -, hz⟩
    exact ih (k + 1) n (hd b) c (by omega) (hequiv_hd _ _ _ hb1) (fun x _ => hd_hd x b) hz

private theorem zig_closed (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (q k : ℕ) (u : List Γ → G.Om q) c
    (hz : Zig G q k u c) (x : List Γ) (hx : x.length = k + 1) : G.dOm q (u x) = 0 := by
  cases q with
  | zero => exact ((inclFacts Γ V S d G hc hn).2.2 _).2 ⟨_, (hz x hx).symm⟩
  | succ q =>
    obtain ⟨b, -, hb, -⟩ := hz
    exact (dExact Γ V S d G hc q _).2 ⟨_, hb x hx⟩

omit [FiniteDimensional ℝ V] in
private theorem zig_lin (s t : ℂ) (q : ℕ) : ∀ (k : ℕ) (u u' : List Γ → G.Om q) c c',
    Zig G q k u c → Zig G q k u' c' → Zig G q k (s • u + t • u') (s • c + t • c') := by
  induction q with
  | zero =>
    intro k u u' c c' h h' x hx
    simp only [Pi.add_apply, Pi.smul_apply, h x hx, h' x hx]
    rw [← map_smul, ← map_smul, ← map_add]
  | succ q ih =>
    rintro k u u' c c' ⟨b, h1, h2, h3⟩ ⟨b', h1', h2', h3'⟩
    refine ⟨s • b + t • b', fun γ x hx => ?_, fun x hx => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, h1 γ x hx, h1' γ x hx]
    · simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, h2 x hx, h2' x hx]
    · rw [hd_lin]
      exact ih _ _ _ _ _ h3 h3'

end Zig

private theorem hd_const {Γ M : Type} [AddCommGroup M] (w : M) (x : List Γ) (hx : x.length = 0 + 2) :
    hd (fun _ => w) x = 0 := by
  simp [hd, hx, Finset.sum_range_succ]

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Dr in
theorem UpperTheory.V.Lit.Geo.perEx :
    PerEx := by
  intro E _ _ _ a U Ξ q
  have hc := (coneConvex E a).1
  have hn : (cone E a).Nonempty := ⟨_, hOne_mem_cone⟩
  refine ⟨fun α hα h0 => ?_, ?_, ?_⟩
  · have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
      obtain ⟨τ, -, hτ⟩ := locSec E a p hp
      exact hτ.mono fun x hx => ⟨τ x, hx⟩
    have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, hw0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, hw0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [h0] at h
    obtain ⟨c, hz⟩ := zig_ex (geo ho U Ξ) hc hn q 0 (fun _ => w')
      (fun γ _ _ => ((corrInv E a ho U Ξ q _ _ hw').1 (fun X => (hv X).1) γ).symm)
      (fun _ _ => (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)) (hd_const w')
    exact ⟨c, ho, w', hw', hz⟩
  · rintro α c hα ⟨ho, w, hw, hz⟩
    have hv : ∀ X, LeftInv (α X) := fun X => ((levelVal E a U Ξ _).1 (hα.val X)).1
    constructor
    · have h := corrD E a ho U Ξ q _ _ hw
      rw [zig_closed (geo ho U Ξ) hc hn q 0 _ c hz [1] rfl] at h
      exact (corrUniq E a ho U Ξ (q + 1)).1 _ 0 _ h (corr_zero U Ξ)
    · rw [← geo_lev ho U Ξ]
      exact zig_coc (geo ho U Ξ) hc hn q 0 q _ c (zero_add q)
        (fun γ _ _ => ((corrInv E a ho U Ξ q _ _ hw).1 hv γ).symm) (hd_const w) hz
  · rintro α β c c' s t ⟨ho, w, hw, hz⟩ ⟨ho', w', hw', hz'⟩
    refine ⟨ho, s • w + t • w', ?_, zig_lin (geo ho U Ξ) s t q 0 _ _ _ _ hz hz'⟩
    have h := corr_sum U Ξ ![s, t] (α := ![α, β]) (w := ![w.1, w'.1]) (Fin.forall_fin_two.2 ⟨hw, hw'⟩)
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
    exact h
