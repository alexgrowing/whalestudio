import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairValueLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootFlatPushforwardGeoFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishOfTrivialFlags
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntOfDenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDenBdd
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DefStab

variable {p : ℕ} [Fact p.Prime]

theorem psi_bound (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) : ∃ K : ℝ, ∀ y : GlobalTheory.LKCx.grp G B.β,
    ∀ (w : InfinitePlace G.F) (a b : Fin G.n), ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤
      K * Real.sqrt ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  let f : InfinitePlace G.F → (Fin G.n → ℂ) → ℝ := fun w x =>
    if sigPosH (G.gram_herm w) = 1 then (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re
    else -(star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re
  have hK : ∀ w, ∃ K : ℝ, ∀ (A : Matrix (Fin G.n) (Fin G.n) ℂ) (s : ℝ), 0 ≤ s →
      (∀ x, f w (A *ᵥ x) = s * f w x) → ∀ a b, ‖A a b‖ ≤ K * Real.sqrt s := by
    intro w
    apply GlobalTheory.LKCx.PsiBound.bound_of_form
    · by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; fun_prop
      · simp only [f, h, if_false]; fun_prop
    · intro t x
      by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; rw [GlobalTheory.LKCx.PsiBound.form_smul, Complex.re_ofReal_mul]
      · simp only [f, h, if_false]; rw [GlobalTheory.LKCx.PsiBound.form_smul, Complex.re_ofReal_mul]; ring
    · intro x hx
      have hp := B.posR w x hx
      by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; exact hp.1 h
      · have h2 : (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re < 0 := hp.2 h
        simp only [f, h, if_false]; linarith
  choose K hK using hK
  refine ⟨∑ w, |K w|, fun y w a b => ?_⟩
  set s : ℝ := ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast y.2.2
  set A := G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hA
  have hsim : ∀ x : Fin G.n → ℂ, star (A *ᵥ x) ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ (A *ᵥ x) =
      (s : ℂ) * (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x) := by
    intro x
    have h := GlobalTheory.LKCx.grp_similitude_herm p G w B.β y
    have h' : Aᴴ * GlobalTheory.LKCx.herm G w B.β * A =
        (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)) : ℂ) • GlobalTheory.LKCx.herm G w B.β := h
    rw [← GlobalTheory.LKCx.PsiBound.form_conj, h', smul_mulVec, dotProduct_smul, smul_eq_mul, hs, Complex.ofReal_ratCast]
  have hinv : ∀ x, f w (A *ᵥ x) = s * f w x := by
    intro x
    by_cases h : sigPosH (G.gram_herm w) = 1
    · simp only [f, h, if_true]; rw [hsim, Complex.re_ofReal_mul]
    · simp only [f, h, if_false]; rw [hsim, Complex.re_ofReal_mul]; ring
  calc ‖A a b‖ ≤ K w * Real.sqrt s := hK w A s hs0.le hinv a b
    _ ≤ |K w| * Real.sqrt s := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
    _ ≤ (∑ u, |K u|) * Real.sqrt s := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun u => |K u|) (fun u _ => abs_nonneg _) (Finset.mem_univ w))
        (Real.sqrt_nonneg _)

theorem isTest_indicator_comm (G : HTGroup p) (K' : Subgroup (Gr G 1))
    (hK : Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw)) :
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' (Set.indicator (K' : Set (Gr G 1)) 1) := by
  have hθ : ∀ g, sigG G 1 g = g := GlobalTheory.LKCx.sigG_one G
  refine ⟨hK, ?_, fun k hk g => ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩; rw [hθ]; exact hk
  · rw [hθ]
    by_cases hg : g ∈ K'
    · have h' : k⁻¹ * g * k ∈ K' := K'.mul_mem (K'.mul_mem (K'.inv_mem hk) hg) hk
      simp [Set.indicator_apply, hg, h']
    · have h' : k⁻¹ * g * k ∉ K' := fun h => hg (by
        have e : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
        rw [e]; exact K'.mul_mem (K'.mul_mem hk h) (K'.inv_mem hk))
      simp [Set.indicator_apply, hg, h']
  · set K₀ := KHT p G.m G.n 1 G.Fw
    haveI : (K₀.subgroupOf K').FiniteIndex := ⟨hK.2⟩
    haveI : Finite (K' ⧸ K₀.subgroupOf K') := Subgroup.finite_quotient_of_finiteIndex
    haveI : Fintype (K' ⧸ K₀.subgroupOf K') := Fintype.ofFinite _
    refine ⟨Finset.univ.image fun q : K' ⧸ K₀.subgroupOf K' => ((Quotient.out q : K') : Gr G 1), fun g hg => ?_⟩
    have hgK : g ∈ K' := by
      by_contra hn; exact hg (by simp [Set.indicator_apply, hn])
    set q : K' ⧸ K₀.subgroupOf K' := QuotientGroup.mk ⟨g, hgK⟩
    have hq : (Quotient.out q)⁻¹ * (⟨g, hgK⟩ : K') ∈ K₀.subgroupOf K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    rw [Subgroup.mem_subgroupOf] at hq
    refine ⟨((Quotient.out q : K') : Gr G 1), Finset.mem_image_of_mem _ (Finset.mem_univ _), 1, K₀.one_mem, _, hq,
      ?_⟩
    simp

theorem finite_locPart : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
    Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (B : GlobalTheory.LKDef.DForm G) (x : G.GAf × Gr G 1),
    Finite (GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x) := by
  intro p _ G _ L K' hK B x
  have hp : p.Prime := Fact.out
  obtain ⟨xx, tt, hx, heq⟩ : ∃ (xx : (AfP p ⊗[ℚ] G.C)ˣ) (tt : (AfP p)ˣ) (hx : Triv G (AfP p) B.β xx tt),
      B.emb = B.embAt xx tt hx := ⟨_, _, B.trivAf.choose_spec.choose_spec, rfl⟩
  set fK : G.GAf → ℂ := Set.indicator (L.K.toSubgroup : Set G.GAf) 1 with hfK
  set fK' : Gr G 1 → ℂ := Set.indicator (K' : Set (Gr G 1)) 1 with hfK'
  have hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup fK := isTest_indicator _ _ (by simp)
  have hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' fK' := isTest_indicator_comm G K' hK
  set S : Set (GlobalTheory.LKCx.grp G B.β) := {y | fK (x.1⁻¹ * GlobalTheory.LKCx.toAfF G B.β xx tt hx y * x.1) ≠ 0 ∧
    fK' (x.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * x.2) ≠ 0} with hS
  have hSfin : S.Finite := by
    obtain ⟨D, hD, hAf⟩ := GlobalTheory.LKCx.BoundedDen.main p G B.β xx tt hx L fK hf x.1
    obtain ⟨k, hP⟩ := GlobalTheory.AtP.main p G B.β K' fK' hf' x.2
    obtain ⟨R, hR⟩ := GlobalTheory.CoordArch.coord_bound p G
    obtain ⟨Kb, hKb⟩ := psi_bound G B
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = D * p ^ k := ⟨_, rfl⟩
    have hN : 0 < N := hNdef ▸ Nat.mul_pos hD (pow_pos hp.pos k)
    obtain ⟨R', hR'⟩ : ∃ R' : ℝ,
        R' = |R| * (Fintype.card (InfinitePlace G.F) * G.n * G.n * (max Kb 0 * Real.sqrt N)) := ⟨_, rfl⟩
    let φ : GlobalTheory.LKCx.grp G B.β → (Fin (Module.finrank ℚ G.C) → ℚ) :=
      fun y => (Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
    have hφ : Function.Injective φ := fun y y' h =>
      GlobalTheory.FinFix.grp_val_injective G B.β ((Module.finBasis ℚ G.C).repr.injective (Finsupp.ext fun i => congrFun h i))
    refine Set.Finite.subset
      (Set.Finite.preimage hφ.injOn (Set.Finite.pi fun _ => GlobalTheory.FinFix.finite_den_bdd N hN R')) ?_
    rintro y ⟨hf1, hf2⟩
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := GlobalTheory.FinFix.exists_int_of_den_le (p := p) D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [hNdef, ← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hN) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
      have h3 : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have := mul_le_mul_of_nonneg_right h2 hs.le
        rwa [one_mul, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one] at this
      exact_mod_cast h3
    intro i _
    obtain ⟨m2, hm2⟩ := GlobalTheory.FinFix.exists_int_of_den_le (p := p) D k hD (φ y i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    refine ⟨⟨m2, ?_⟩, ?_⟩
    · rw [hNdef, mul_comm]; exact hm2
    · show |((φ y i : ℚ) : ℝ)| ≤ R'
      refine (hR _ i).trans ?_
      have hb : ∀ w a b, ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤ max Kb 0 * Real.sqrt N := by
        intro w a b
        exact (hKb y w a b).trans
          (mul_le_mul (le_max_left _ _) (Real.sqrt_le_sqrt hsN) (Real.sqrt_nonneg _) (le_max_right _ _))
      have hsum : ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n,
          ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤
          Fintype.card (InfinitePlace G.F) * G.n * G.n * (max Kb 0 * Real.sqrt N) := by
        calc _ ≤ ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n, max Kb 0 * Real.sqrt N :=
              Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hb w a b
          _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
      have hnn : 0 ≤ ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n,
          ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ := by positivity
      rw [hR']
      calc R * _ ≤ |R| * _ := mul_le_mul_of_nonneg_right (le_abs_self R) hnn
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (abs_nonneg R)
  have hsub : ((GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x : Subgroup (G.GAf × Gr G 1)) :
      Set (G.GAf × Gr G 1)) ⊆ B.emb '' S := by
    intro e he
    rw [SetLike.mem_coe, GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map] at he
    obtain ⟨⟨y, rfl⟩, ⟨c, hc, hce⟩⟩ := he
    rw [Subgroup.mem_prod] at hc
    have hc' : x⁻¹ * B.emb y * x = c := by
      rw [← hce]; simp [MulAut.conj_apply, mul_assoc]
    have he1 : (B.emb y).1 = GlobalTheory.LKCx.toAfF G B.β xx tt hx y := by rw [heq]; rfl
    have he2 : (B.emb y).2 = GlobalTheory.LKCx.toP1 G B.β y := by rw [heq]; rfl
    have h1 : x.1⁻¹ * GlobalTheory.LKCx.toAfF G B.β xx tt hx y * x.1 = c.1 := by
      rw [← he1, ← hc']; rfl
    have h2 : x.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * x.2 = c.2 := by
      rw [← he2, ← hc']; rfl
    refine ⟨y, ⟨?_, ?_⟩, rfl⟩
    · rw [hfK, h1, Set.indicator_of_mem hc.1]; exact one_ne_zero
    · rw [hfK', h2, Set.indicator_of_mem hc.2]; exact one_ne_zero
  exact ((hSfin.image _).subset hsub).to_subtype

end GlobalTheory.DefStab
