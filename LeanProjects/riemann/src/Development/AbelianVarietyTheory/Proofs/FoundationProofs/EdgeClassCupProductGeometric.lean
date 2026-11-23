import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1CoboundaryStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EdgeAlg

open GlobalTheory.K5.Basic

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zcong (n : ℕ) (A B : ℤ) (h : (A : ZMod (p ^ n)) = B) : Cong p n (A : Ω) (B : Ω) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨((-k : ℤ) : Ω), isInt_intCast _, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hk
  push_cast at this ⊢
  linear_combination -this

theorem isInt_natCast (m : ℕ) : IsInt p (m : Ω) := by
  have := isInt_intCast (p := p) (Ω := Ω) (m : ℤ)
  simpa using this

theorem isInt_pow_p (c : ℕ) : IsInt p ((p : Ω) ^ c) := by
  have := isInt_natCast (p := p) (Ω := Ω) (p ^ c)
  simpa using this

theorem conj_invariant {G M : Type*} [Group G] [AddCommGroup M] (H : Subgroup G) (φ : G → M)
    (hφ : ∀ g ∈ H, ∀ h ∈ H, φ (g * h) = φ g + φ h) {σ h : G} (hσ : σ ∈ H) (hh : h ∈ H) :
    φ (σ * h * σ⁻¹) = φ h := by
  have h1 : φ 1 = 0 := by
    have e := hφ 1 H.one_mem 1 H.one_mem
    rw [mul_one] at e
    have e' : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero, ← e]
    exact add_left_cancel e'
  have h2 : φ σ + φ σ⁻¹ = 0 := by
    rw [← hφ σ hσ σ⁻¹ (H.inv_mem hσ), mul_inv_cancel, h1]
  rw [hφ _ (H.mul_mem hσ hh) _ (H.inv_mem hσ), hφ σ hσ h hh, add_right_comm, h2, zero_add]

theorem zeta_eq_pow (T : Tower p Ω) (m k : ℕ) : T.ζ m = T.ζ (m + k) ^ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    show _ = T.ζ (m + k + 1) ^ p ^ (k + 1)
    rw [ih, ← T.ζpow (m + k), ← pow_mul, ← pow_succ']

theorem gn_fix_zeta (T : Tower p Ω) {L n : ℕ} (hn : n ≤ L) {g : Gal p Ω} (hg : g ∈ Gn T L) :
    g (T.ζ n) = T.ζ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [zeta_eq_pow T n k, map_pow, ((mem_gn T _ g).1 hg).1]

theorem kum_add (T : Tower p Ω) {L n : ℕ} (hn : n ≤ L) {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T L) r a) : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, a (g * h) = a g + a h := by
  intro g hg h hh
  obtain ⟨χ, hχ⟩ := exists_isCyc T n
  have h1 : χ g = 1 := (isCyc_eq_one_iff hχ g).2 (gn_fix_zeta T hn hg)
  rw [isKum_mul hχ hr ha hg hh, h1, one_mul]

theorem isAlgZp_zeta (T : Tower p Ω) (m : ℕ) : IsAlgZp p (T.ζ m) := by
  refine ⟨Polynomial.X ^ (p ^ m) - Polynomial.C 1,
    Polynomial.X_pow_sub_C_ne_zero (pow_pos hp.out.pos m) 1, ?_⟩
  simp [(T.prim m).pow_eq_one]

theorem kum_geo_zero (T : Tower p Ω) {n m : ℕ} {H : Subgroup (Gal p Ω)} {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H (T.ζ m) a) {g : Gal p Ω} (hH : g ∈ H) (hg : g ∈ Ggeo p Ω) : a g = 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hg' : ∀ x : Ω, IsAlgZp p x → g x = x := hg
  have e := ha g hH
  rw [hg' _ (isAlgZp_zeta T m)] at e
  have hz : T.ζ m ≠ 0 := (T.prim m).ne_zero (pow_ne_zero _ hp.out.ne_zero)
  have e1 : T.ζ n ^ (a g).val = 1 := mul_right_cancel₀ hz (by rw [one_mul]; exact e.symm)
  have e2 : T.ζ n ^ (a g).val = T.ζ n ^ (0 : ℕ) := by rw [pow_zero]; exact e1
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e2
  simpa using e2

theorem conj_mem_ggeo {σ h : Gal p Ω} (hh : h ∈ Ggeo p Ω) : σ * h * σ⁻¹ ∈ Ggeo p Ω := by
  have hh' : ∀ x : Ω, IsAlgZp p x → h x = x := hh
  show ∀ x : Ω, IsAlgZp p x → (σ * h * σ⁻¹) x = x
  rintro x ⟨P, hP, hPx⟩
  have hx' : IsAlgZp p (σ⁻¹ x) := ⟨P, hP, by
    have := Polynomial.aeval_algHom_apply (σ⁻¹ : Gal p Ω).toAlgHom x (P.map (algebraMap ℤ_[p] (O0 p)))
    rw [hPx, map_zero] at this
    exact this⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh' _ hx', ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

end GlobalTheory.EdgeAlg

namespace GlobalTheory.EdgeAlg

open GlobalTheory.K5.Basic

theorem edge_class_cup : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c₁ : ℕ, ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ (x y lz lq η : Gal p Ω → ZMod (p ^ n)) (f : Ω),
  (∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h) →
  IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq → IsInt p f → (∀ g ∈ Gn T L, g f = f) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c₁ * (((x g).val : Ω) * ((y h).val : Ω)) + (p : Ω) ^ c₁ * f * (((lz g).val : Ω) * ((lq h).val : Ω))) →
  ∃ o : Ω, IsInt p o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L,
    Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun h => (p : Ω) ^ c * ((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : Ω) - (σ⁻¹ o - o - (p : Ω) ^ c * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)) := by
  classical
  intro p _ hp2 c₁
  obtain ⟨c', hc'⟩ := GlobalTheory.T.geometric_level_h1_coboundary p hp2
  refine ⟨c₁ + c', ?_⟩
  intro Ω _ _ hclo T L n hnL x y lz lq η f hxy hlz hlq hfi hff hη hηlc hcob
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨W, ⟨hWi, hWlc⟩, hW⟩ := hcob
  have hx_add : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h := fun g hg h hh => (hxy g hg h hh).1
  have hlq_add := kum_add T hnL (qq_ne_zero T (L + n)) hlq
  have hlz0 : ∀ g ∈ (Ggeo p Ω ⊓ Gn T L), lz g = 0 := fun g hg =>
    kum_geo_zero T hlz (Subgroup.mem_inf.1 hg).2 (Subgroup.mem_inf.1 hg).1
  have hlqΔ : IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq := fun g hg => hlq g (Subgroup.mem_inf.1 hg).2
  let a : Gal p Ω → Ω := fun g => (p : Ω) ^ c₁ * ((η g).val : Ω) - W g
  have haLC : IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a := by
    refine ⟨fun g _ => IsIntegral.sub (IsIntegral.mul (isInt_pow_p c₁) (isInt_natCast _)) (hWi g), fun g hg => ?_⟩
    obtain ⟨S1, hS1⟩ := hηlc g hg
    obtain ⟨S2, hS2⟩ := hWlc g
    refine ⟨S1 ∪ S2, fun h hh hS => ?_⟩
    have e1 := hS1 h hh (fun z hz => hS z (Finset.mem_union_left _ hz))
    have e2 := hS2 h (fun z hz => hS z (Finset.mem_union_right _ hz))
    simp only [a, e1]
    exact cong_sub (cong_refl _ _) e2
  have haCoc : ∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong p n (a (g * h)) (a g + g (a h)) := by
    intro g hg h hh
    have hgG := (Subgroup.mem_inf.1 hg).2
    have hhG := (Subgroup.mem_inf.1 hh).2
    obtain ⟨w, hw, ew⟩ := hW g hgG h hhG
    obtain ⟨u, hu, eu⟩ := zcong (p := p) (Ω := Ω) n (((x g).val : ℤ) * ((y h).val : ℤ))
      (((η h).val : ℤ) - ((η (g * h)).val : ℤ) + ((η g).val : ℤ)) (by
        simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
        exact hη g hg h hh)
    simp only [hlz0 g hg, ZMod.val_zero, Nat.cast_zero] at ew
    refine ⟨(p : Ω) ^ c₁ * u - w, IsIntegral.sub (IsIntegral.mul (isInt_pow_p c₁) hu) hw, ?_⟩
    simp only [a, map_sub, map_mul, map_pow, map_natCast]
    push_cast at eu
    linear_combination (p : Ω) ^ c₁ * eu - ew
  obtain ⟨o, hoi, hofix, z, hzi, hz⟩ := (hc' Ω hclo T L n hnL lq hlqΔ).1 a haLC haCoc
  refine ⟨o, hoi, hofix, fun σ hσ => ?_⟩
  have hsi : ∀ v : Ω, σ⁻¹ (σ v) = v := fun v => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hfs : σ⁻¹ f = f := hff _ ((Gn T L).inv_mem hσ)
  refine ⟨σ⁻¹ (z - σ z - (p : Ω) ^ c' * W σ),
    isInt_gal _ (IsIntegral.sub (IsIntegral.sub hzi (isInt_gal σ hzi)) (IsIntegral.mul (isInt_pow_p c') (hWi σ))),
    fun h hh => ?_⟩
  have hhG := (Subgroup.mem_inf.1 hh).2
  have hh2 : σ * h * σ⁻¹ ∈ (Ggeo p Ω ⊓ Gn T L) := Subgroup.mem_inf.2
    ⟨conj_mem_ggeo (Subgroup.mem_inf.1 hh).1, (Gn T L).mul_mem ((Gn T L).mul_mem hσ hhG) ((Gn T L).inv_mem hσ)⟩
  have hh2G := (Subgroup.mem_inf.1 hh2).2
  have hcomm : σ * h * σ⁻¹ * σ = σ * h := by group
  have hxh2 : x (σ * h * σ⁻¹) = x h := conj_invariant (Gn T L) x hx_add hσ hhG
  have hlqh2 : lq (σ * h * σ⁻¹) = lq h := conj_invariant (Gn T L) lq hlq_add hσ hhG
  have hlzh2 : lz (σ * h * σ⁻¹) = 0 := hlz0 _ hh2
  have hsh : σ (h z) = (σ * h * σ⁻¹) (σ z) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hsi]
  have hs2 : ∀ v : Ω, σ⁻¹ ((σ * h * σ⁻¹) v) = h (σ⁻¹ v) := fun v => by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hsi]
  obtain ⟨w1, hw1, e1⟩ := hW _ hh2G σ hσ
  obtain ⟨w2, hw2, e2⟩ := hW σ hσ h hhG
  obtain ⟨w3, hw3, e3⟩ := hz h hh
  obtain ⟨w4, hw4, e4⟩ := hz _ hh2
  obtain ⟨u0, hu0, e0⟩ := zcong (p := p) (Ω := Ω) n
    (((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : ℕ) : ℤ)
    (((η (σ * h * σ⁻¹)).val : ℤ) - ((η h).val : ℤ) - ((x h).val : ℤ) * ((y σ).val : ℤ) + ((x σ).val : ℤ) * ((y h).val : ℤ))
    (by simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val])
  push_cast at e0
  simp only [hxh2, hlzh2, hcomm, ZMod.val_zero, Nat.cast_zero] at e1
  simp only [a, hlqh2] at e3 e4
  have e3s := congrArg σ e3
  simp only [map_sub, map_mul, map_pow, map_natCast, hsh] at e3s
  have K : (p : Ω) ^ c₁ * (p : Ω) ^ c' * (((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : ℕ) : Ω)
      - (o - σ o - (p : Ω) ^ c₁ * (p : Ω) ^ c' * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)
      - (((σ * h * σ⁻¹) z - (σ * h * σ⁻¹) (σ z) - (p : Ω) ^ c' * (σ * h * σ⁻¹) (W σ)) - (z - σ z - (p : Ω) ^ c' * W σ))
      = (p : Ω) ^ n * ((p : Ω) ^ c₁ * (p : Ω) ^ c' * u0 - (p : Ω) ^ c' * w1 + (p : Ω) ^ c' * w2 + w4 - σ w3) := by
    linear_combination (p : Ω) ^ c₁ * (p : Ω) ^ c' * e0 - (p : Ω) ^ c' * e1 + (p : Ω) ^ c' * e2 + e4 - e3s
  refine ⟨σ⁻¹ ((p : Ω) ^ c₁ * (p : Ω) ^ c' * u0 - (p : Ω) ^ c' * w1 + (p : Ω) ^ c' * w2 + w4 - σ w3), isInt_gal _ ?_, ?_⟩
  · exact IsIntegral.sub (IsIntegral.add (IsIntegral.add (IsIntegral.sub
      (IsIntegral.mul (IsIntegral.mul (isInt_pow_p c₁) (isInt_pow_p c')) hu0)
      (IsIntegral.mul (isInt_pow_p c') hw1)) (IsIntegral.mul (isInt_pow_p c') hw2)) hw4) (isInt_gal σ hw3)
  · have KS := congrArg (⇑(σ⁻¹ : Gal p Ω)) K
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add, hs2, hsi, hfs] at KS
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add, hsi, pow_add]
    linear_combination KS

end GlobalTheory.EdgeAlg
