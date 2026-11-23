import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.MemOfMulMem
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaElementsUnramifiedOrdinaryOfEulerSystemInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonvanishingTransferCharacterSumsPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientCharTrivialInertiaCyclotomicTowerStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.LocalUnitsRoots

variable {l : ℕ} [Fact l.Prime]

private theorem cg_symm {n : ℕ} {x y : Qbar l} (h : Cg n x y) : Cg n y x := by
  unfold Cg at *; rwa [norm_sub_rev]

private theorem cg_trans {n : ℕ} {x y w : Qbar l} (h₁ : Cg n x y) (h₂ : Cg n y w) : Cg n x w := by
  unfold Cg at *
  calc ‖x - w‖ = ‖(x - y) + (y - w)‖ := by ring_nf
    _ ≤ max ‖x - y‖ ‖y - w‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h₁ h₂

private theorem cg_mono {n n' : ℕ} (hn : n ≤ n') {x y : Qbar l} (h : Cg n' x y) : Cg n x y := by
  unfold Cg at *
  refine h.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ l) hn

private theorem cg_mul {n : ℕ} {t x y : Qbar l} (ht : ‖t‖ ≤ 1) (h : Cg n x y) : Cg n (t * x) (t * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖t‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h

private theorem norm_char_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (x : ZMod N) : ‖ψ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have h1 : (ψ (u : ZMod N)) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h2 : ‖ψ (u : ZMod N)‖ ^ (Fintype.card (ZMod N)ˣ) = 1 := by rw [← norm_pow, h1, norm_one]
    have hc : Fintype.card (ZMod N)ˣ ≠ 0 := Fintype.card_ne_zero
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hc).mp h2)
  · rw [MulChar.map_nonunit ψ hx, norm_zero]; exact zero_le_one

private theorem norm_factor_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (d : ℕ) :
    ‖(1 - (d : Qbar l) * ψ (d : ZMod N))‖ ≤ 1 := by
  have h1 := norm_char_le_one ψ (d : ZMod N)
  have h2 := IsUltrametricDist.norm_natCast_le_one (Qbar l) d
  calc _ ≤ max ‖(1 : Qbar l)‖ ‖(d : Qbar l) * ψ (d : ZMod N)‖ := by
        rw [sub_eq_add_neg, ← norm_neg ((d : Qbar l) * _)]; exact IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := by
      refine max_le (by rw [norm_one]) ?_
      rw [norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cycMod_eq_one {s : G ℚ Ω} (h : cycBar ℚ Ω l s = 1) (m : ℕ) : cycMod ℚ Ω l m s = 1 := by
  have h1 : cycZ ℚ Ω l s = 1 := by
    have h2 := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) h
    simp only [cycBar, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingHom.comp_apply, Units.val_one] at h2
    have h3 : PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = (1 : ℚ_[l]) :=
      (algebraMap ℚ_[l] (Qbar l)).injective (by rw [h2, map_one])
    exact Units.ext (Subtype.ext h3)
  simp only [cycMod, MonoidHom.comp_apply, h1, map_one]

private theorem roots_pow {ζ : ℕ → Ω} (h : Roots l ζ) (c m : ℕ) (hc : c ≤ m) : ζ m ^ l ^ c = ζ (m - c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hc
  rw [Nat.add_sub_cancel]
  clear hc
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ', pow_mul, ← add_assoc, (h (k + c)).2, ih]

private theorem conj_law {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {Z : Sy Ω l}
    (hIw : IwSys2 c A ν Z) (hν : ∀ s ∈ Ine (F := ℚ) A, ν s = 1) {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A)
    (hcy : cycBar ℚ Ω l σ = 1) (m : ℕ) {s : G ℚ Ω} (hs : s ∈ Hm l A m) :
    Z m (σ * s * σ⁻¹) 1 = (ν σ : Qbar l) * Z m s 1 := by
  obtain ⟨hsI, hsc⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hsc
  have hsD := Ine_le_Dec A hsI
  have hc := cycMod_eq_one hcy m
  have coc := (hIw.2.1 m).2
  have h0 : Z m 1 1 = 0 := by
    have := coc 1 (one_mem _) 1 (one_mem _) 1
    rw [hν 1 (one_mem _)] at this
    simpa using this
  have h1 := coc σ hσ σ⁻¹ (inv_mem hσ) 1
  have h2 := coc σ hσ s hsD 1
  have h3 := coc (σ * s) (mul_mem hσ hsD) σ⁻¹ (inv_mem hσ) 1
  rw [hIw.1 σ hσ s hsD, hν s hsI, map_mul, hc, hsc] at h3
  rw [mul_inv_cancel, h0, hc] at h1
  rw [hc] at h2
  simp only [inv_one, mul_one] at h1 h2 h3
  rw [h3, h2]
  linear_combination -h1

private theorem main
    (h48 : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Gs L : PowerSeries (Qbar l)) (a a' κ : Qbar l) (v v' : ℕ → Qbar l) (c₀ m₀ c₁ n₀ : ℕ) (φ : DirichletCharacter (Qbar l) l) (e : ℕ), l ≠ 2 → 1 ≤ e → 2 ≤ m₀ → (∀ n, Gs.coeff n ∈ c.O) → (∀ n, L.coeff n ∈ c.O) → ‖a‖ = 1 → ‖a'‖ = 1 → κ ≠ 0 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → 2 ≤ c₀ → ¬ l ∣ c₀ → (∀ m, m₀ ≤ m → ∃ z : Qbar l, IsPrimitiveRoot z (l ^ m) ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → Cg (m - c₁) ((1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ m))) * (v' m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) → (∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0) → ∃ n₁ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₁ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass Gs r ξ x) 0)
    (h50 : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1) :
    GlobalTheory.KZ.ZetaEulerSystemNonvanishing GlobalTheory.KZ.Pin7 := by
  intro l _ Ω _ _ _ ι e S A W g hN hS c y S' ν χ Z hSys hIw hSp hPin
  obtain ⟨a, a', κ, v', j, Rhs, L, φ, m₀, c₀, n₀, hInu, ⟨σ₀, hσ₀, hF₀, hν₀⟩, ha, ha', hv', hκ, hj, hL, ⟨ζ, hζ, hHT⟩,
    hRhs, hχ, hNZ⟩ := hPin
  have hl2 : l ≠ 2 := hN.l_odd
  have he : 1 ≤ e := hN.e_pos
  have hA : OverL l A := hN.atL
  have hl2' : ¬ l ∣ 2 := fun h => hl2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h)
  have hR : Roots l ζ := hζ
  by_contra hnz
  have hy : ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → y s 1 = 0 := by
    intro s hs hc
    by_contra h0
    exact hnz ⟨s, hs, hc, h50 l Ω ι e S A W g hN hS s hs hc, h0⟩
  have hSZ : SpZero A φ e Z := by
    intro n
    obtain ⟨r₀, hr₀⟩ := hSp n
    refine ⟨max r₀ 1, fun r hr s hs hc => ?_⟩
    have h1 := hr₀ r (le_trans (le_max_left _ _) hr) s hs hc
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have heq : (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) = eta φ e r := by
      funext x
      rw [hχ r hr1 x, mul_comm]
    rw [heq, hy s hs hc] at h1
    exact cg_symm h1
  have hI : IwI c A Z := by
    refine ⟨fun r s _ x => (hIw.2.1 r).1 s x, fun r s hs t ht x => ?_, fun r s _ x => hIw.2.2 r s x⟩
    rw [(hIw.2.1 r).2 s (Ine_le_Dec A hs) t (Ine_le_Dec A ht) x, hInu s hs, Units.val_one, one_mul]
  have hFr : ∀ σ ∈ Dec (F := ℚ) A, IsFrob A l σ → cycBar ℚ Ω l σ = 1 → ∀ m, ∀ s ∈ Hm l A m,
      Z m (σ * s * σ⁻¹) 1 = a * Z m s 1 := by
    intro σ hσ hF hc m s hs
    have h1 := (pFrobEx l hl2 Ω A hA).2.1 σ₀ hσ₀ σ hσ hF₀ hF
    have h2 := hIw.1 σ₀ hσ₀ _ (Ine_le_Dec A h1)
    rw [mul_inv_cancel_left, hInu _ h1, mul_one] at h2
    rw [conj_law hIw hInu hσ hc m hs, h2, hν₀]
  obtain ⟨Gs, v, c₁, m₁, hGs, hv, hrel, hint⟩ := pCore l hl2 Ω A hA c Z a j 2 c₀ (max m₀ c₀) ζ hI ha hFr hj hl2' hR (by
    intro m hm
    obtain ⟨κι, hfin, P, o, hP, -⟩ := hHT m (le_trans (le_max_left _ _) hm)
    refine ⟨κι, hfin, P, o, hP.2.1, hP.2.2.1, ?_⟩
    rw [← roots_pow hR c₀ m (le_trans (le_max_right _ _) hm)]
    exact hP.2.2.2.2)
  have hprim : ∀ m, IsPrimitiveRoot (j (ζ m)) (l ^ m) := fun m => (hζ m).1.map_of_injective j.injective
  obtain ⟨n₁, r₂, hG⟩ := h48 l c Gs L a a' κ v v' 2 (max (max m₀ c₀) (max m₁ 2)) (max c₀ c₁) n₀ φ e hl2 he
    (by omega) hGs hL ha ha' hκ hv hv' le_rfl hl2' (by
      intro m hm
      have hm0 : m₀ ≤ m := by omega
      obtain ⟨κι, hfin, P, o, hP, hlaw⟩ := hHT m hm0
      refine ⟨j (ζ m), hprim m, fun ψ hψ => ?_⟩
      have ht := norm_factor_le_one ψ⁻¹ 2
      have e1 := cg_mul ht (cg_symm (hRhs m hm0 ψ hψ _ (hprim m)))
      have e2 := cg_mul ht (cg_symm (hlaw ψ hψ))
      have e3 := hrel m (by omega) κι hfin P o hP.2.1 hP.2.2.1 (by
        rw [← roots_pow hR c₀ m (by omega)]
        exact hP.2.2.2.2) ψ
      exact cg_trans (cg_mono (by omega) (cg_trans e1 e2)) (cg_mono (by omega) e3)) hNZ
  obtain ⟨r₃, hr₃⟩ := hint φ e he hSZ n₁
  exact hG (max r₂ r₃) (le_max_left _ _) _ (hprim _) (hr₃ _ (le_max_right _ _) _ (hprim _))

end UpperTheory.Kd.C7.LocalUnitsRoots

theorem UpperTheory.Kd.C7.pLocu :
    GlobalTheory.KZ.ZetaEulerSystemNonvanishing GlobalTheory.KZ.Pin7 :=
  UpperTheory.Kd.C7.LocalUnitsRoots.main GlobalTheory.T.nonvanishing_transfer_characterSums_powerSeries GlobalTheory.T.quotient_char_trivial_inertia_cyclotomic_tower
