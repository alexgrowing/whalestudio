import Development.WeilBound.CoreStatements.BranchingTraces.CasimirDecomposition.ExtensionFixesSmoothVectors

open Matrix Finset
open scoped InnerProductSpace Classical

noncomputable section

namespace PositivityTheory.UnitaryDecomposition.DecB

open CompanionTheory.Zuck PositivityTheory.UnitaryDecomposition.DecA BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam IsCayleyU)
open Formalism.REAL (Jm UJ)

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem cas_dn {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} (hU : U.R.IsDS ε μ) {P : Mx k r} (hP : IsCayleyU k r ε P)
    (x : M (vr k r true, U)) : casT ε (fun g => U.R.σ (P⁻¹ * g * P)) (dn U P x) = dn U P (kOp U x) := by
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have hexp := (GlobalTheory.T.derivedAction_expand_matrixUnits CompanionTheory.D.gk.admitted.k_finite_smooth k r ε μ U.R hU 1 _ isUnit_one (GlobalTheory.CompanionTheory.CasimirDS.isE_one U)).2.1
  funext c
  show _ = ∑ a, P⁻¹ a c • (kOp U x a : U.R.H)
  have e1 : ∀ l, dn U P x l = ((∑ d, P⁻¹ d l • x d : U.R.smSub) : U.R.H) := fun l => by simp [dn]
  simp only [casT, (GlobalTheory.CayleyTransport.smooth_and_dsigC_transport k r ε U.R P hP).2, e1, hexp]
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one, map_sum, map_smul, kOp_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.smul_sum, smul_smul]
  have e2 : ∀ a b d, ∑ l, (P⁻¹ * Matrix.single c l (1 : ℂ) * P) a b * P⁻¹ d l = if b = d then P⁻¹ a c else 0 := fun a b d => by
    have h1 : ∀ l, (P⁻¹ * Matrix.single c l (1 : ℂ) * P) a b = P⁻¹ a c * P l b := fun l => by
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single c (fun j _ hj => by
        rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hj, mul_zero]) (by simp), Matrix.single_mul_apply_same, one_mul]
    have h2 := congrFun (congrFun (Matrix.nonsing_inv_mul P hPu) d) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    simp only [h1, mul_assoc, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun l _ => mul_comm (P l b) (P⁻¹ d l), h2]
    by_cases h : d = b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, e2]
  simp

theorem dec_U (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (U : URep k r) (π : Mx k r → (U.R.H →L[ℂ] U.R.H)) {P : Mx k r}
    (hP : IsCayleyU k r ε P) (hπe : (fun g => U.R.σ (P⁻¹ * g * P)) = π) (hU : U.R.IsDS ε lam)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) : Nonempty (Dec ε lam π) := by
  have S := zuckerman_ingredients
  have hl : IsHCParam lam := hU.1
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hth : thr _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < 200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by
    have h1 := thr_le (n := 2 * r + k + 1) (by omega) ε
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
    have h3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hn1
    rw [Nat.cast_add, Nat.cast_pow]
    push_cast at h1 h2 h3 ⊢
    linarith
  obtain ⟨T0, hT0, -, -⟩ := injV S zuckerman_library_bounds true hU hg (by linarith)
  let T : Fin (2 * r + k + 1) → URep k r := fun s => if h : IsHCParam (shift true lam s) then T0 ⟨s, h⟩ else U
  have hT : ∀ s : {s // IsHCParam (shift true lam s)}, (T s.1).R.IsDS ε (shift true lam s.1) := fun s => by
    simp only [T, dif_pos s.2]; exact hT0 s
  obtain ⟨io, pr, hD⟩ := decReg S zuckerman_library_bounds hk true hU hg hth (fun s => T s.1) hT
  have hsimp := S.schur S.infChar k r ε _ _ (fun s : {s // IsHCParam (shift true lam s)} => T s.1)
    ((shift_inj true lam).comp Subtype.val_injective) hT
  have hQ : ∀ s, ∃ Q : Mx k r, IsCayleyU k r ε Q ∧ (IsHCParam (shift true lam s) →
      PI.UpqRep.IsDS ε (shift true lam s) fun g => (T s).R.σ (Q⁻¹ * g * Q)) := fun s => by
    by_cases h : IsHCParam (shift true lam s)
    · obtain ⟨Q, h1, h2⟩ := (hT ⟨s, h⟩).2
      exact ⟨Q, h1, fun _ => h2⟩
    · exact ⟨P, hP, fun h' => absurd h' h⟩
  choose Q hQ1 hQ2 using hQ
  have sm_iff : ∀ v : U.R.H, v ∈ PI.PhMeasCore.smoothVecs (Jm ε) π ↔ v ∈ U.R.sm := fun v => by
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · have h1 := GlobalTheory.CayleyTransport.smoothOn_comp (H := Jm ε) (J := PI.UpqRep.Hpk k r) (A := P) (B := P⁻¹)
        (f := fun g => π g v) (fun g hg' => cay_mem' hP hg') hv
      have h2 : (fun g => π (P * g * P⁻¹) v) = fun g => U.R.σ g v := funext fun g => by
        rw [← hπe]
        show U.R.σ (P⁻¹ * (P * g * P⁻¹) * P) v = _
        rw [Matrix.mul_assoc P, Matrix.nonsing_inv_mul_cancel_left _ _ hPu, Matrix.nonsing_inv_mul_cancel_right _ _ hPu]
      rw [h2] at h1
      exact h1
    · have := (GlobalTheory.CayleyTransport.smooth_and_dsigC_transport k r ε U.R P hP).1 v hv
      rwa [hπe] at this
  let up : (Fin (2 * r + k + 1) → U.R.H) → M (vr k r true, U) := fun x =>
    if h : x ∈ SmT ε π then fun c => ∑ d, P d c • (⟨x d, (sm_iff _).1 (h d)⟩ : U.R.smSub) else 0
  have up_coe : ∀ x ∈ SmT ε π, ∀ c, (up x c : U.R.H) = ∑ d, P d c • x d := fun x hx c => by
    simp only [up, dif_pos hx]; simp
  have dn_up : ∀ x ∈ SmT ε π, dn U P (up x) = x := fun x hx => funext fun c => by
    show ∑ d, P⁻¹ d c • (up x d : U.R.H) = x c
    simp only [up_coe x hx]
    rw [sum_comp, Matrix.mul_nonsing_inv _ hPu, sum_one]
  have dn_sm : ∀ z, dn U P z ∈ SmT ε π := fun z c =>
    (sm_iff _).2 (show ∑ d, P⁻¹ d c • (z d : U.R.H) ∈ U.R.smSub from
      U.R.smSub.sum_mem fun d _ => U.R.smSub.smul_mem _ (z d).2)
  have up_dn : ∀ z, up (dn U P z) = z := fun z => funext fun c => Subtype.ext (by
    rw [up_coe _ (dn_sm z)]
    show ∑ d, P d c • ∑ e, P⁻¹ e d • (z e : U.R.H) = _
    rw [sum_comp, Matrix.nonsing_inv_mul _ hPu, sum_one])
  have mem : ∀ g : UJ ε, P⁻¹ * um g * P ∈ GG k r := fun g => cay_mem hP g.2
  have dn_act : ∀ (g : UJ ε) z, dn U P (CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) z) = actT π (um g) (dn U P z) := fun g z => by
    funext c
    show ∑ d, P⁻¹ d c • (CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) z d : U.R.H) = ∑ d, (um g)⁻¹ d c • π (um g) (∑ e, P⁻¹ e d • (z e : U.R.H))
    have e0 : U.R.σ (P⁻¹ * um g * P) = π (um g) := congrFun hπe _
    simp only [act_coe U (mem g), map_sum, map_smul, e0]
    rw [sum_comp, sum_comp, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hPu, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_right _ _ hPu]
  have up_act : ∀ (g : UJ ε), ∀ x ∈ SmT ε π, up (actT π (um g) x) = CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) (up x) :=
    fun g x hx => by rw [← up_dn (CompanionTheory.Zuck.act _ _ _), dn_act, dn_up x hx]
  have hform := fun s s' => invForm (U := U) hP (io s) (io s') (hD.io_hom s) (hD.io_hom s')
  choose cI hc using fun s => (CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense k r ε _ _ _ _ (hT s) (hT s)).1 _ (hform s s)
  have horth : ∀ s s', s ≠ s' → ∀ a b, formT ε (dn U P (io s' b)) (dn U P (io s a)) = 0 := fun s s' hs a b => by
    rcases (CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense k r ε _ _ _ _ (hT s) (hT s')).2 _ (hform s s') with h | h
    · have := h _ (a ()).2 _ (b ()).2
      simpa only [extension_one_coe] using this
    · obtain ⟨f, g, hf, -, hgf, -⟩ := S.uIso k r (triv k r) _ _ h
      have h0 := hsimp.2.2 s s' hs f hf
      obtain ⟨y, y', hy⟩ := hsimp.1 s
      have h1 : ∀ z, z = (g ∘ₗ f) z := fun z => by rw [hgf]; rfl
      exact absurd ((h1 y).trans (by rw [h1 y', h0]; simp)) hy
  have bmem : ∀ s, (Q s)⁻¹ * P ∈ GG k r := fun s => cay_two hP (hQ1 s)
  have sumS : ∀ f : {s // IsHCParam (shift true lam s)} → Fin (2 * r + k + 1) → U.R.H,
      ∑ s ∈ univ.filter (fun s => IsHCParam (shift true lam s)), (if h : IsHCParam (shift true lam s) then f ⟨s, h⟩ else 0) =
        ∑ s, f s := fun f => by
    rw [Finset.sum_subtype (p := fun s => IsHCParam (shift true lam s)) _ (by simp)]
    exact Finset.sum_congr rfl fun s _ => dif_pos s.2
  have hsum : ∀ z, ∑ s, io s (pr s z) = z := fun z => by
    have := LinearMap.congr_fun hD.sum z
    simpa [LinearMap.sum_apply] using this
  refine ⟨{ S := univ.filter fun s => IsHCParam (shift true lam s)
            Hs := fun s => (T s).R.H
            πs := fun s g => (T s).R.σ ((Q s)⁻¹ * g * Q s)
            ds := fun s hs => ⟨(mem_filter.1 hs).2, hQ2 s (mem_filter.1 hs).2⟩
            p := fun s x => if h : IsHCParam (shift true lam s) then dn U P (io ⟨s, h⟩ (pr ⟨s, h⟩ (up x))) else 0
            pr := fun s x => if h : IsHCParam (shift true lam s) then (T s).R.σ ((Q s)⁻¹ * P) (pr ⟨s, h⟩ (up x) ()) else 0
            c := fun s => if h : IsHCParam (shift true lam s) then cI ⟨s, h⟩ else 0
            κ := fun s => (lam s : ℂ) + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2
            p_sm := fun s hs x _ => by rw [dif_pos (mem_filter.1 hs).2]; exact dn_sm _
            sum := fun x hx => by rw [sumS fun s => dn U P (io s (pr s (up x))), ← map_sum, hsum, dn_up x hx]
            p_act := fun s hs g x hx => ?_
            pr_act := fun s hs g x hx => ?_
            form := fun s hs x hx y hy => ?_
            cas := fun s hs x hx => ?_
            κ_inj := fun s _ s' _ h => hl.1.injective (by exact_mod_cast add_right_cancel h) }⟩
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    rw [up_act g x hx, ← dn_act]
    congr 1
    exact LinearMap.congr_fun (((S.homCat k r).comp _ _ _ _ _ (hD.pr_hom ⟨s, h⟩) (hD.io_hom ⟨s, h⟩)).equiv _ (mem g)) (up x)
  · have h := (mem_filter.1 hs).2
    have hQu : IsUnit (Q s).det := (Matrix.isUnit_iff_isUnit_det _).1 (hQ1 s).1.1
    simp only [dif_pos h]
    have e := LinearMap.congr_fun ((hD.pr_hom ⟨s, h⟩).equiv _ (mem g)) (up x)
    simp only [LinearMap.comp_apply] at e
    rw [up_act g x hx, e, act_one_coe _ (mem g), ← (T s).repOn.apply_mul (bmem s) (mem g),
      ← (T s).repOn.apply_mul (cay_mem (hQ1 s) g.2) (bmem s)]
    congr 2
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.mul_nonsing_inv_cancel_left _ _ hQu]
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    have e := (LinearMap.norm_map_iff_inner_map_map ((T s).R.σ ((Q s)⁻¹ * P) : (T s).R.H →ₗ[ℂ] (T s).R.H)).1
      ((T s).rep.2.1 _ (bmem s)) (pr ⟨s, h⟩ (up y) ()) (pr ⟨s, h⟩ (up x) ())
    simp only [ContinuousLinearMap.coe_coe] at e
    rw [e, ← hc ⟨s, h⟩ _ (pr ⟨s, h⟩ (up x) ()).2 _ (pr ⟨s, h⟩ (up y) ()).2]
    simp only [extension_one_coe]
    conv_lhs => rw [← dn_up y hy, ← hsum (up y), map_sum]
    have e2 : ∀ (f : {s // IsHCParam (shift true lam s)} → Fin (2 * r + k + 1) → U.R.H) z,
        formT ε (∑ s', f s') z = ∑ s', formT ε (f s') z := fun f z => by
      simp only [formT, Finset.sum_apply, sum_inner, Finset.mul_sum]
      exact Finset.sum_comm
    rw [e2, Finset.sum_eq_single ⟨s, h⟩ (fun s' _ hs' => horth _ _ (Ne.symm hs') _ _) (by simp)]
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    have e := cas_dn hU hP (io ⟨s, h⟩ (pr ⟨s, h⟩ (up x)))
    rw [show (fun g => U.R.σ (P⁻¹ * g * P)) = π from hπe] at e
    rw [e, kOp_io hk hU s (hT ⟨s, h⟩) _ (hD.io_hom ⟨s, h⟩), map_smul]

theorem dec_hpk (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Mx k r → (H →L[ℂ] H)) {P : Mx k r} (hP : IsCayleyU k r ε P) (hl : IsHCParam lam) (hπ : Formalism.MainNotions.S.IsDS ε lam π)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) : Nonempty (Dec ε lam π) := by
  haveI : CompleteSpace H := hπ.1
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  let R : Rep k r := { H := H, σ := fun g => π (P * g * P⁻¹) }
  have hπe : (fun g => R.σ (P⁻¹ * g * P)) = π := funext fun g => by
    show π (P * (P⁻¹ * g * P) * P⁻¹) = π g
    rw [Matrix.mul_assoc P⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.mul_nonsing_inv_cancel_right _ _ hPu]
  have hR : R.IsDS ε lam := ⟨hl, P, hP, by rw [hπe]; exact hπ⟩
  exact dec_U hk lam (mkU R hR) π hP hπe hR hg

theorem unitary_decomposition_exists : DecEx := by
  intro m ε lam H _ _ π ⟨a, ha⟩ hle hl hπ hg
  have h1 : 1 ≤ (univ.filter fun a => ε a = false).card := Finset.card_pos.2 ⟨a, by simp [ha]⟩
  have h2 : (univ.filter fun a => ε a = true).card + (univ.filter fun a => ε a = false).card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) fun a => ε a = true
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r, (univ.filter fun a => ε a = false).card = r + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
  obtain ⟨k, hk⟩ : ∃ k, (univ.filter fun a => ε a = true).card = k + r := ⟨_, (Nat.sub_add_cancel (by omega)).symm⟩
  obtain rfl : m = 2 * r + k + 1 := by omega
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_of_card k r ε hk
  exact dec_hpk (by omega) lam H π (P := P) hP hl hπ hg

end PositivityTheory.UnitaryDecomposition.DecB
