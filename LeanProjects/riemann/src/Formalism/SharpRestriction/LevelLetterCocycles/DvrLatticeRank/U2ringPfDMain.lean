import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffUniformiserZero

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2D

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

theorem u2ringPfD_main [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hK : W.gamK = W.gam)
    (he : e ≤ finrank K₀ K) (c : ZMod n) (a : O) (ha : IsUnit a) (r : Fin e → O)
    (hrm : ∀ j, r j ∈ IsLocalRing.maximalIdeal O)
    (hE : E c = Polynomial.C a * ∏ j, (Polynomial.X - Polynomial.C (r j)))
    (hnr : ∀ (j : Fin e) (w₀ : O), IsUnit w₀ → ∀ t : ℕ, 0 < t →
      (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) ^ t ≠ 1)
    (h' : ℕ) (hh' : 1 ≤ h') :
    SecondPropositionRingInput W π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c := by
  obtain ⟨ν, hνΔ, hνeq⟩ := u2ringPfC_nu W hR hs hK h'
  obtain ⟨hπΔ, hsub, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, ⟨w₂, hγ⟩, -⟩ := hR
  have hπ0 := constantCoeff_uniformiser_zero w hw hs
  have hHS : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  set ψ : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom (hHS c) with hψdef
  have hψ : ∀ F, ψ F = PowerSeries.subst (π' c) F := fun F => by
    rw [hψdef, PowerSeries.coe_substAlgHom]
  have hψX : ψ PowerSeries.X = π' c := by rw [hψ, PowerSeries.subst_X (hHS c)]
  have hψC : ∀ x : O, ψ (PowerSeries.C x) = PowerSeries.C x := fun x => by
    rw [hψ, PowerSeries.subst_C]; rfl
  have hψΔ : ∀ δ ∈ W.DelF, ∀ F, W.γ₀ δ (ψ F) = ψ F := fun δ hδ F => by
    rw [hψ]; exact u2ringPfC_subΔ W hπΔ hπ0 δ hδ c F
  have hψinj : ∀ F F', ψ F = ψ F' → F = F' := fun F F' h =>
    u2ringPfC_inj W hπΔ hsub hπ0 c F F' (by rwa [hψ, hψ] at h)
  have hpre : ∀ x, (∀ δ ∈ W.DelF, W.γ₀ δ x = x) → ∃ F, ψ F = x := fun x hx => by
    obtain ⟨F, hF⟩ := u2ringPfC_pre W hsub c x hx
    exact ⟨F, by rw [hψ]; exact hF⟩
  have hsingle : ∀ F, (Pi.single c (ψ F) : LetA O n) ∈ W.AΔ := fun F =>
    u2ringPfB_single_mem W c _ (fun δ hδ => hψΔ δ hδ F)
  have halg : ∀ x : O, (algebraMap O (LetA O n) x) c = PowerSeries.C x := fun x => by
    rw [Pi.algebraMap_apply, PowerSeries.algebraMap_apply]; rfl

  set EY : PowerSeries O := PowerSeries.C a * ∏ j, (PowerSeries.X - PowerSeries.C (r j)) with hEY
  have hÊc : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c = ψ EY := by
    show Polynomial.aeval (π' c) (E c) = ψ EY
    rw [hE, hEY, map_mul, map_prod, map_mul, map_prod, Polynomial.aeval_C, hψC]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hψX, hψC]
    rfl
  have hXC0 : ∀ y : O, (PowerSeries.X - PowerSeries.C y : PowerSeries O) ≠ 0 := fun y h => by
    have := congrArg (PowerSeries.coeff 1) h; simp at this
  have hEY0 : EY ≠ 0 := by
    rw [hEY]
    refine mul_ne_zero (fun h => ha.ne_zero ?_) (Finset.prod_ne_zero_iff.2 fun j _ => hXC0 _)
    simpa using congrArg PowerSeries.constantCoeff h
  have hψEY0 : ψ EY ≠ 0 := fun h => hEY0 (hψinj _ _ (by rw [h, map_zero]))
  have hπc0 : π' c ≠ 0 := by
    have : π' c = (w : LetA O n) c * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this]
    exact mul_ne_zero (w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)).ne_zero
      (pow_ne_zero _ PowerSeries.X_ne_zero)

  have hγc : W.γ₀ W.gam (π' c) = π' c + (w₂ : LetA O n) c * π' c * ψ EY := by
    have e1 : W.γ₀ W.gam (π' c) - π' c = (w₂ : LetA O n) c * π' c * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c :=
      congrFun hγ c
    rw [← hÊc, ← e1]; ring
  have hw2Δ : ∀ δ ∈ W.DelF, W.γ₀ δ ((w₂ : LetA O n) c) = (w₂ : LetA O n) c := by
    intro δ hδ
    have hπc : W.γ₀ δ (π' c) = π' c := congrFun (hπΔ δ hδ) c
    have h1 := congrArg (W.γ₀ δ) hγc
    rw [u2ringPfB_γ₀_comm, hπc, map_add, map_mul, map_mul, hπc, hψΔ δ hδ] at h1
    have h2 : (W.γ₀ δ ((w₂ : LetA O n) c) - (w₂ : LetA O n) c) * (π' c * ψ EY) = 0 := by
      linear_combination h1.symm.trans hγc
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero hπc0 hψEY0))
  obtain ⟨Ŵ, hŴ⟩ := hpre _ hw2Δ
  have hŴ0 : IsUnit (PowerSeries.constantCoeff Ŵ) := by
    have h1 : IsUnit ((w₂ : LetA O n) c) :=
      w₂.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
    rw [← hŴ, hψ, DualFramesAlt.EigenUniformiser.subst_eq_C_add (hπ0 c), PowerSeries.isUnit_iff_constantCoeff] at h1
    simpa [hπ0 c] using h1
  set Gt : PowerSeries O := 1 + Ŵ * EY with hGt
  set XG : PowerSeries O := PowerSeries.X * Gt with hXG
  have hXG0 : PowerSeries.constantCoeff XG = 0 := by
    rw [hXG, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hHSXG := PowerSeries.HasSubst.of_constantCoeff_zero' hXG0
  set Γ : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom hHSXG with hΓdef
  have hΓ : ∀ F, Γ F = PowerSeries.subst XG F := fun F => by rw [hΓdef, PowerSeries.coe_substAlgHom]
  have hΓX : Γ PowerSeries.X = XG := by rw [hΓ, PowerSeries.subst_X hHSXG]
  have hΓC : ∀ x : O, Γ (PowerSeries.C x) = PowerSeries.C x := fun x => by
    rw [hΓ, PowerSeries.subst_C]; rfl
  have hγπc : W.γ₀ W.gam (π' c) = ψ XG := by
    rw [hγc, hXG, hGt]
    simp only [map_mul, map_add, map_one, hψX, hŴ]
    ring
  have hγψ : ∀ F, W.γ₀ W.gam (ψ F) = ψ (Γ F) := by
    intro F
    rw [hψ F, DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ W.gam) (W.γ₀_X _).1 (hπ0 c), hγπc, hψ XG, hΓ F,
      hψ (PowerSeries.subst XG F), PowerSeries.subst_comp_subst_apply hHSXG (hHS c)]

  let θ : Fin e → PowerSeries O := fun j => 1 + PowerSeries.X * Ŵ * PowerSeries.C a *
      ∏ j' ∈ Finset.univ.erase j, (PowerSeries.X - PowerSeries.C (r j'))
  have hEYsplit : ∀ j, EY = (PowerSeries.X - PowerSeries.C (r j)) *
      (PowerSeries.C a * ∏ j' ∈ Finset.univ.erase j, (PowerSeries.X - PowerSeries.C (r j'))) := by
    intro j; rw [hEY, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]; ring
  have hΓlin : ∀ j, Γ (PowerSeries.X - PowerSeries.C (r j)) =
      (PowerSeries.X - PowerSeries.C (r j)) * θ j := by
    intro j
    rw [map_sub, hΓX, hΓC, hXG, hGt, hEYsplit j]
    ring
  have hΓEY : Γ EY = EY * ∏ j, θ j := by
    conv_lhs => rw [hEY]
    rw [map_mul, map_prod, hΓC, Finset.prod_congr rfl fun j _ => hΓlin j, Finset.prod_mul_distrib, hEY]
    ring

  obtain ⟨nh, hnh⟩ := hpre _ (u2ringPfB_letter_mem W hνΔ c)
  have hnθ : nh * (∏ j, θ j) ^ h' = 1 := by
    have h2 : ν c * W.γ₀ W.gamK (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c ^ h' :=
      congrFun hνeq c
    rw [hK, map_pow, hÊc, hγψ, ← hnh, ← map_pow ψ (Γ EY) h', ← map_pow ψ EY h', ← map_mul,
      hΓEY] at h2
    have h3 := hψinj _ _ h2
    have h4 : EY ^ h' * (nh * (∏ j, θ j) ^ h' - 1) = 0 := by linear_combination h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left (pow_ne_zero _ hEY0))

  have hm : 0 < 2 * h' := by omega
  set m := 2 * h' with hmdef
  set NR := m * e with hNR
  let rI : ℕ → O := fun k => if h : k < e then r ⟨k, h⟩ else 0
  have hrI : ∀ j : Fin e, rI j = r j := fun j => by simp [rI, j.2]
  have hdiv : ∀ k, k < NR → k / m < e := fun k hk => Nat.div_lt_of_lt_mul hk
  let root : ℕ → O := fun k => if k < NR then rI (k / m) else 0
  have hrootm : ∀ k, root k ∈ IsLocalRing.maximalIdeal O := by
    intro k
    simp only [root, rI]
    split_ifs
    · exact hrm _
    · exact Ideal.zero_mem _
    · exact Ideal.zero_mem _
  let φY : ℕ → PowerSeries O := fun k =>
    if k < NR then PowerSeries.X - PowerSeries.C (root k) else PowerSeries.C (a ^ m) * PowerSeries.X
  let θ' : ℕ → PowerSeries O := fun j => if h : j < e then θ ⟨j, h⟩ else 1
  let θY : ℕ → PowerSeries O := fun k => if k < NR then θ' (k / m) else Gt
  let f : ℕ → LetA O n := fun k =>
    if k < NR then π' - algebraMap O (LetA O n) (root k) else algebraMap O (LetA O n) (a ^ m) * π'
  have hfc : ∀ k, f k c = ψ (φY k) := by
    intro k
    simp only [f, φY]
    split_ifs
    · rw [Pi.sub_apply, halg, map_sub, hψX, hψC]
    · rw [Pi.mul_apply, halg, map_mul, hψX, hψC]
  have hfΔ : ∀ k, f k ∈ W.AΔ := by
    intro k
    simp only [f]
    split_ifs
    · exact W.AΔ.sub_mem hπΔ (W.AΔ.algebraMap_mem _)
    · exact W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) hπΔ
  have hφroot : ∀ k, ∃ u : PowerSeries O, PowerSeries.X - PowerSeries.C (root k) = φY k * u := by
    intro k
    by_cases hk : k < NR
    · exact ⟨1, by simp only [φY, if_pos hk, mul_one]⟩
    · refine ⟨PowerSeries.C (((ha.unit⁻¹ : Oˣ) : O) ^ m), ?_⟩
      simp only [φY, root, if_neg hk, map_zero, sub_zero]
      rw [mul_comm, ← mul_assoc, ← map_mul, ← mul_pow, ha.val_inv_mul, one_pow, map_one, one_mul]
  have hΓφ : ∀ k, Γ (φY k) = φY k * θY k := by
    intro k
    by_cases hk : k < NR
    · have hj := hdiv k hk
      simp only [φY, θY, θ', root, rI, if_pos hk, dif_pos hj]
      exact hΓlin ⟨k / m, hj⟩
    · simp only [φY, θY, if_neg hk]
      rw [map_mul, hΓC, hΓX, hXG]
      ring
  have hPY : ∀ k, (∏ j ∈ Finset.range k, f j) c = ψ (∏ j ∈ Finset.range k, φY j) := by
    intro k
    rw [Finset.prod_apply, map_prod]
    exact Finset.prod_congr rfl fun j _ => hfc j
  have hΓP : ∀ k, Γ (∏ j ∈ Finset.range k, φY j) =
      (∏ j ∈ Finset.range k, φY j) * ∏ j ∈ Finset.range k, θY j := by
    intro k
    rw [map_prod, Finset.prod_congr rfl fun j _ => hΓφ j, Finset.prod_mul_distrib]
  have hprod : ∏ k ∈ Finset.range (NR + 1), φY k = PowerSeries.X * EY ^ m := by
    have h0 : φY NR = PowerSeries.C (a ^ m) * PowerSeries.X := by
      simp only [φY, if_neg (lt_irrefl NR)]
    have h1 : ∏ k ∈ Finset.range NR, φY k =
        ∏ k ∈ Finset.range NR, (PowerSeries.X - PowerSeries.C (rI (k / m))) :=
      Finset.prod_congr rfl fun k hk => by simp only [φY, root, if_pos (Finset.mem_range.1 hk)]
    have h3 := DualFramesAlt.BlockProductRing.prod_div_block m hm (fun j => PowerSeries.X - PowerSeries.C (rI j)) e
    have h2 : ∏ j ∈ Finset.range e, (PowerSeries.X - PowerSeries.C (rI j)) =
        ∏ j, (PowerSeries.X - PowerSeries.C (r j)) := by
      rw [← Fin.prod_univ_eq_prod_range]
      exact Finset.prod_congr rfl fun j _ => by rw [hrI j]
    rw [Finset.prod_range_succ, h0, h1, hNR, h3, Finset.prod_pow,
      h2, hEY, mul_pow, map_pow]
    ring

  let ρ : ℕ → PowerSeries O := fun k => nh * ∏ i ∈ Finset.range k, θY i
  let cc : ℕ → O := fun k => Classical.choose (DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) (ρ k))
  have hcc : ∀ k, (mkI (root k)) (ρ k) = (mkI (root k)) (PowerSeries.C (cc k)) := fun k =>
    Classical.choose_spec (DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) (ρ k))
  have hmkΓ : ∀ k F, (mkI (root k)) (Γ F) = (mkI (root k)) F := by
    intro k F
    obtain ⟨c₀, hc₀⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) F
    have hXGr : (mkI (root k)) XG = (mkI (root k)) (PowerSeries.C (root k)) := by
      apply DualFramesAlt.BlockProductRing.mk_eq_of_mem
      by_cases hkN : k < NR
      · have hj := hdiv k hkN
        have hrk : root k = r ⟨k / m, hj⟩ := by simp [root, rI, hkN, hj]
        have key : XG - PowerSeries.C (root k) = (PowerSeries.X - PowerSeries.C (root k)) *
            (1 + PowerSeries.X * Ŵ * (PowerSeries.C a *
              ∏ j' ∈ Finset.univ.erase ⟨k / m, hj⟩, (PowerSeries.X - PowerSeries.C (r j')))) := by
          rw [hXG, hGt, hEYsplit ⟨k / m, hj⟩, hrk]; ring
        rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
      · have hrk : root k = 0 := by simp [root, hkN]
        have key : XG - PowerSeries.C (root k) = (PowerSeries.X - PowerSeries.C (root k)) * Gt := by
          rw [hXG, hrk, map_zero, sub_zero, sub_zero]
        rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
    rw [hΓ, DualFramesAlt.eigenRingInvariants.ev_subst hXG0 hXGr hc₀, hc₀]
  refine ⟨?_, ?_, ⟨1 + (w₂ : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π', ?_, ?_⟩, ν, hνΔ, hνeq, NR + 1, f, cc,
    hfΔ, ?_, ?_, ?_, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · have h1 := Formalism.MainNotions.LiftingTheory.liftb_q_unit W
    rw [hq, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  · exact gradNPf_fΔ W s' w π' _ hw hπΔ (by linear_combination hγ)
  · rw [hK]; linear_combination hγ
  · funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply]
      congr 1
      rw [hPY, hprod, map_mul, map_pow, hψX, ← hÊc]
      rfl
    · simp [letE, hi]
  · intro k hk x hx
    obtain ⟨F, hF⟩ := hpre _ (u2ringPfB_letter_mem W hx c)
    obtain ⟨a₀, ha₀⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) F
    obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq ha₀
    obtain ⟨u, hu⟩ := hφroot k
    refine ⟨a₀, Pi.single c (ψ (u * H)), hsingle _, ?_⟩
    funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply, Pi.add_apply, Pi.single_eq_same]
      congr 1
      rw [halg, hfc, ← hF, ← hψC, ← map_mul, ← map_add]
      congr 1
      linear_combination hH + H * hu
    · simp [letE, hi]
  · intro k hk x hx
    obtain ⟨F, hF⟩ := hpre _ (u2ringPfB_letter_mem W hx c)
    have hZ0 : (mkI (root k)) (ρ k * Γ F - PowerSeries.C (cc k) * F) =
        (mkI (root k)) (PowerSeries.C 0) := by
      rw [map_sub, map_mul (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (root k))) (ρ k) (Γ F),
        map_mul (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (root k))) (PowerSeries.C (cc k)) F, hcc k, hmkΓ,
        map_zero, sub_self, map_zero]
    obtain ⟨Z', hZ'⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hZ0
    rw [map_zero, sub_zero] at hZ'
    obtain ⟨u, hu⟩ := hφroot k
    refine ⟨Pi.single c (ψ (u * Z')), hsingle _, ?_⟩
    funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.single_eq_same]
      congr 1
      have hγA : ∀ (g : W.Gam) (y : LetA O n), (W.γA g y) c = W.γ₀ g (y c) := fun _ _ => rfl
      rw [hγA, Pi.mul_apply, hK, hPY, ← hF, ← map_mul, hγψ, ← hnh, halg, ← hψC, hPY (k + 1),
        ← map_mul, ← map_mul, ← map_mul, ← map_sub]
      congr 1
      rw [map_mul, hΓP, Finset.prod_range_succ]
      simp only [ρ] at hZ'
      linear_combination (∏ j ∈ Finset.range k, φY j) * hZ' + (∏ j ∈ Finset.range k, φY j) * Z' * hu
    · simp [letE, hi]
  · have hθother : ∀ j j' : Fin e, j ≠ j' → (mkI (r j)) (θ j') = 1 := by
      intro j j' hjj'
      rw [← map_one (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (r j)))]
      apply DualFramesAlt.BlockProductRing.mk_eq_of_mem
      have hjmem : j ∈ Finset.univ.erase j' := Finset.mem_erase.2 ⟨hjj', Finset.mem_univ j⟩
      have key : θ j' - 1 = (PowerSeries.X - PowerSeries.C (r j)) * (PowerSeries.X * Ŵ * PowerSeries.C a *
          ∏ i ∈ (Finset.univ.erase j').erase j, (PowerSeries.X - PowerSeries.C (r i))) := by
        simp only [θ]
        rw [← Finset.mul_prod_erase _ _ hjmem]; ring
      rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
    have hcval : ∀ j : Fin e, ∃ cj : O, IsUnit cj ∧ (∀ t : ℕ, 0 < t → cj ^ t ≠ 1) ∧
        (mkI (r j)) (θ j) = (mkI (r j)) (PowerSeries.C cj) := by
      intro j
      obtain ⟨wj, hwj⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrm j) Ŵ
      have hwju : IsUnit wj := by
        obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hwj
        have h0 := congrArg PowerSeries.constantCoeff hH
        simp only [map_sub, map_mul, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C,
          zero_sub] at h0
        by_contra hnu
        have hwm : wj ∈ IsLocalRing.maximalIdeal O :=
          (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
        have hŴm : PowerSeries.constantCoeff Ŵ ∈ IsLocalRing.maximalIdeal O := by
          have e0 : PowerSeries.constantCoeff Ŵ = wj + -r j * PowerSeries.constantCoeff H := by
            linear_combination h0
          rw [e0]
          exact Ideal.add_mem _ hwm (Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 (hrm j)))
        exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hŴm)) hŴ0
      refine ⟨1 + r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j'), ?_, hnr j wj hwju, ?_⟩
      · by_contra hnu
        have h1 : 1 + r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') ∈
            IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
        have h2 : r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') ∈
            IsLocalRing.maximalIdeal O :=
          Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hrm j)))
        have h3 := Ideal.sub_mem _ h1 h2
        rw [add_sub_cancel_right] at h3
        exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
      · simp only [θ, map_add, map_one, map_mul, map_prod, map_sub, DualFramesAlt.eigenRingInvariants.mk_X, hwj]
    have hcount : (Finset.range (NR + 1)).filter (fun k => cc k = 1) ⊆
        ((Finset.range e).image fun j => m * j + h') ∪ {NR} := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkN, hk1⟩ := hk
      rcases Nat.lt_or_ge k NR with hlt | hge
      · apply Finset.mem_union_left
        have hj := hdiv k hlt
        obtain ⟨cj, hcju, hcjt, hcjmk⟩ := hcval ⟨k / m, hj⟩
        have hrk : root k = r ⟨k / m, hj⟩ := by simp [root, rI, hlt, hj]
        have hθY : ∀ i ∈ Finset.range k, (mkI (r ⟨k / m, hj⟩)) (θY i) =
            if i / m = k / m then (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) else 1 := by
          intro i hi
          have hiN : i < NR := lt_trans (Finset.mem_range.1 hi) hlt
          have hij := hdiv i hiN
          simp only [θY, θ', if_pos hiN, dif_pos hij]
          split_ifs with hik
          · have e0 : (⟨i / m, hij⟩ : Fin e) = ⟨k / m, hj⟩ := Fin.ext hik
            rw [e0]; exact hcjmk
          · exact hθother _ _ (fun h => hik (congrArg Fin.val h).symm)
        have hprodθ : (mkI (r ⟨k / m, hj⟩)) (∏ j, θ j) = (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) := by
          rw [map_prod, Finset.prod_eq_single ⟨k / m, hj⟩
            (fun j' _ hne => hθother _ _ (Ne.symm hne)) (fun h => absurd (Finset.mem_univ _) h)]
          exact hcjmk
        have hn : (mkI (r ⟨k / m, hj⟩)) nh * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ h' = 1 := by
          have e0 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (r ⟨k / m, hj⟩))) hnθ
          rwa [map_mul, map_pow, hprodθ, map_one] at e0
        have hρ : (mkI (r ⟨k / m, hj⟩)) (ρ k) =
            (mkI (r ⟨k / m, hj⟩)) nh * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) := by
          rw [show ρ k = nh * ∏ i ∈ Finset.range k, θY i from rfl, map_mul, map_prod,
            Finset.prod_congr rfl hθY, DualFramesAlt.BlockProductRing.prod_ite_block m hm _ k]
        have hkey : cc k * cj ^ h' = cj ^ (k % m) := by
          apply DualFramesAlt.eigenRingInvariants.ev_inj (hrm ⟨k / m, hj⟩)
          have h1 := hcc k
          rw [hrk, hρ] at h1
          have e1 : (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cc k * cj ^ h')) =
              (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cc k)) * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ h' := by
            simp only [map_mul, map_pow]
          have e2 : (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cj ^ (k % m))) =
              (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) := by
            simp only [map_pow]
          rw [e1, e2, ← h1]
          linear_combination (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) * hn
        rw [hk1, one_mul] at hkey
        have ht : k % m = h' := by
          rcases lt_trichotomy (k % m) h' with h1 | h1 | h1
          · exfalso
            apply hcjt (h' - k % m) (by omega)
            have e0 : cj ^ (k % m) * (cj ^ (h' - k % m) - 1) = 0 := by
              rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h1.le, hkey, sub_self]
            exact sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left (pow_ne_zero _ hcju.ne_zero))
          · exact h1
          · exfalso
            apply hcjt (k % m - h') (by omega)
            have e0 : cj ^ h' * (cj ^ (k % m - h') - 1) = 0 := by
              rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h1.le, hkey, sub_self]
            exact sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left (pow_ne_zero _ hcju.ne_zero))
        rw [Finset.mem_image]
        refine ⟨k / m, Finset.mem_range.2 hj, ?_⟩
        have e0 := Nat.div_add_mod k m
        rw [ht] at e0; exact e0
      · have e0 : k = NR := by omega
        exact Finset.mem_union_right _ (Finset.mem_singleton.2 e0)
    calc ((Finset.range (NR + 1)).filter fun k => cc k = 1).card
        ≤ (((Finset.range e).image fun j => m * j + h') ∪ {NR}).card := Finset.card_le_card hcount
      _ ≤ ((Finset.range e).image fun j => m * j + h').card + ({NR} : Finset ℕ).card :=
          Finset.card_union_le _ _
      _ ≤ e + 1 := by
        rw [Finset.card_singleton]
        exact Nat.add_le_add_right (Finset.card_image_le.trans (by rw [Finset.card_range])) 1
      _ ≤ finrank K₀ K + 1 := by omega

end U2D

end Formalism.MainNotions.N.Ln34
