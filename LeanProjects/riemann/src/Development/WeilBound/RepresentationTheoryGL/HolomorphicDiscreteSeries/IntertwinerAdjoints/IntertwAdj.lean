import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.OneLeDiff
import Development.WeilBound.CoreStatements.BranchingTraces.FormTSingle
import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.ColSq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.Sl

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition PI.DSInfCharCap CompanionTheory.D.DSIC Formalism.FourierDecayAlt.P.CapelliAbstractCharacter PositivityTheory.UnitaryDecomposition.Com

section Corner

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}
  {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)} {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

theorem corner_val {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} (hF : Fits ε ε' e) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (hm : Formalism.QuantumDeterminants.IsHCParam mu) (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ) (X : Dec ε lam π) (s : Fin (n + 1))
    (hs : s ∈ X.S) (hκ : X.κ s = (lam s : ℂ) + (((n + 1 : ℕ) : ℂ) - 1) / 2) (P : H →L[ℂ] H') (hP : Intertw ε' e π σ P)
    (η : H) (hη : η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π) :
    (∏ j ∈ univ.erase s, ((lam j - lam s : ℝ) : ℂ)) • P (X.p s (Pi.single (zi e) η) (zi e)) =
      (∏ j, ((mu j - lam s + 1 / 2 : ℝ) : ℂ)) • P η := by
  obtain ⟨S, E, hS⟩ := hSmMod (n + 1) ε H π hπ.2.2.1
  obtain ⟨S', E', hS'⟩ := hSmMod n ε' H' σ hσ.2.2.1
  set m : Fin (n + 1) → ℂ := fun j => (lam j : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2 with hmd
  have hq : ∀ u v, qdet E u v = (∏ j, (u + m j)) • v := cap_of hl hπ hS
  let co : (Fin (n + 1) → S) → Fin (n + 1) → H := fun x l => x l
  have hco : ∀ x, co x ∈ SmT ε π := fun x l => (hS.mem _).1 (x l).2
  let Y : (Fin (n + 1) → S) → X.S → Fin (n + 1) → S := fun x t c =>
    ⟨X.p t (co x) c, (hS.mem _).2 (X.p_sm t t.2 _ (hco x) c)⟩
  have hYe : ∀ x t, EE E (Y x t) = X.κ t • Y x t := fun x t => funext fun c => Subtype.ext (by
    have := congrFun (X.cas t t.2 _ (hco x)) c
    rw [EE_apply, Submodule.coe_sum]
    simp only [hS.act]
    exact this)
  have hYs : ∀ x, ∑ t, Y x t = x := fun x => funext fun c => Subtype.ext (by
    have := congrFun (X.sum _ (hco x)) c
    rw [Finset.sum_apply] at this
    rw [Finset.sum_apply, Submodule.coe_sum]
    exact (Finset.sum_coe_sort X.S fun t => X.p t (co x) c).trans this)
  have hsing : ∀ (l : Fin (n + 1)) (v : S), co (Pi.single l v) = Pi.single l (v : H) := fun l v => funext fun c => by
    by_cases h : c = l
    · subst h; simp [co]
    · simp [co, Pi.single_eq_of_ne h]
  have hi : X.κ s = (n : ℂ) + m s := by rw [hκ]; simp only [hmd]; push_cast; ring
  set d : ℂ := ∏ j ∈ univ.erase s, (-m s + m j) with hd
  have hd' : d = ∏ j ∈ univ.erase s, ((lam j - lam s : ℝ) : ℂ) :=
    Finset.prod_congr rfl fun j _ => by simp only [hmd]; push_cast; ring
  have key : ∀ l c (v : S), d • X.p s (Pi.single l (v : H)) c =
      ((-1 : ℂ) ^ ((l : ℕ) + (c : ℕ))) • ((qminor E l.succAbove c.succAbove (-m s) v : S) : H) := fun l c v => by
    have h := th_proj hS.gl hq univ (Y (Pi.single l v)) (fun t : X.S => X.κ t)
      (fun a _ b _ h => Subtype.ext (X.κ_inj a.2 b.2 h)) (fun t _ => hYe _ t) (mem_univ (⟨s, hs⟩ : X.S)) s hi
    rw [hYs] at h
    have h2 := congrArg Subtype.val (congrFun h c)
    rw [th_single] at h2
    rw [← hsing]
    exact h2.symm
  let f : S →ₗ[ℂ] S' := (P.toLinearMap ∘ₗ S.subtype).codRestrict S' fun x =>
    (hS'.mem _).2 (smooth_map hF hP ((hS.mem _).1 x.2))
  have hf : ∀ a b x, f (E (e (Sum.inl a)) (e (Sum.inl b)) x) = E' a b (f x) := fun a b x => Subtype.ext (by
    show P (E _ _ x : H) = _
    rw [hS.act, hS'.act, ← blk_single]
    exact dsigC_map hF hP (fun Z hZ => (hS.real Z hZ x).differentiableAt) _)
  let η' : S := ⟨η, (hS.mem _).2 hη⟩
  have h1 := key (zi e) (zi e) η'
  rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
    corner hS.gl (zi e) (fun a => e (Sum.inl a)) (e.injective.comp Sum.inl_injective)
      (fun a h => Sum.inl_ne_inr (e.injective h))] at h1
  have h2 := congrArg Subtype.val (qdet_int f hf (-m s) η')
  rw [cap_of hm hσ hS', Submodule.coe_smul] at h2
  have h3 : d • P (X.p s (Pi.single (zi e) η) (zi e)) = (∏ j, (-m s + ((mu j : ℂ) - ((n : ℂ) - 1) / 2))) • P η := by
    rw [← map_smul]
    exact (congrArg P h1).trans h2
  have e2 : ∏ j, (-m s + ((mu j : ℂ) - ((n : ℂ) - 1) / 2)) = ∏ j, ((mu j - lam s + 1 / 2 : ℝ) : ℂ) :=
    Finset.prod_congr rfl fun j _ => by simp only [hmd]; push_cast; ring
  rw [← hd', ← e2]
  exact h3

theorem intertw_adj {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} (hF : Fits ε ε' e) (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ)
    (i : H' →L[ℂ] H) (hn : ∀ x, ‖i x‖ = ‖x‖) (hi : IsHMap ε' e π σ i) :
    Intertw ε' e π σ (ContinuousLinearMap.adjoint i) := by
  have hρ := uRep_emb hF hπ.2.2.1
  have hs := uRep_self hσ.2.2.1
  have hPa : ∀ y x, ⟪y, ContinuousLinearMap.adjoint i x⟫_ℂ = ⟪i y, x⟫_ℂ := fun y x =>
    ContinuousLinearMap.adjoint_inner_right _ y x
  refine ⟨?_, fun h x => ext_inner_left ℂ fun y => ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact i.opNorm_le_bound zero_le_one fun y => by rw [hn, one_mul]
  · have a1 := hρ.adj h⁻¹ (i y) x
    have a2 := hs.adj h⁻¹ y (ContinuousLinearMap.adjoint i x)
    simp only [inv_inv] at a1 a2
    rw [hPa, ← a1, ← a2, hPa, hi]

theorem pt_id {lam : Fin (n + 1) → ℝ} (hF : Fits ε ε' e) (hπ : IsDS ε lam π) (X : Dec ε lam π) (s : Fin (n + 1))
    (hs : s ∈ X.S) (η : H) (hη : η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π) (h : UJ ε') :
    X.c s * ⟪X.pr s (Pi.single (zi e) η), X.πs s (emb e (um h)) (X.pr s (Pi.single (zi e) η))⟫_ℂ =
      ⟪η, π (emb e (um h)) (X.p s (Pi.single (zi e) η) (zi e))⟫_ℂ := by
  have hU := hπ.2.2.1
  have hx := smT_single hη (zi e)
  have e1 : π (emb e (um h)) (X.p s (Pi.single (zi e) η) (zi e)) =
      actT π (um (embU hF h)) (X.p s (Pi.single (zi e) η)) (zi e) := by
    unfold actT
    rw [← um_inv, Finset.sum_eq_single (zi e) (fun b _ hb => by
      rw [show um (embU hF h)⁻¹ b (zi e) = _ from emb_col _ b, if_neg hb, zero_smul]) (by simp),
      show um (embU hF h)⁻¹ (zi e) (zi e) = _ from emb_col _ (zi e), if_pos rfl, one_smul]
    rfl
  have e2 := X.form s hs _ (smT_act hU (embU hF h) hx) _ hx
  rw [formT_single, show ε (zi e) = true from hF.1, if_pos rfl, one_mul, X.pr_act s hs _ _ hx,
    X.p_act s hs _ _ hx] at e2
  rw [e1, e2]
  rfl

end Corner

theorem exists_ds (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (h : ℝ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : 8 * (m : ℝ) ^ 2 + 2 * m + 1 ≤ h) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)), IsDS ε lam σ := by
  refine ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap m ε lam hl h hg (Or.inr ?_)
  have hq : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ m :=
      (min_le_left _ _).trans (by unfold ReciprocityTheory.ChartRestriction.DS.pOf; exact (Finset.card_filter_le _ _).trans (by simp))
    exact_mod_cast this
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hq0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := Nat.cast_nonneg _
  refine max_lt (by nlinarith) ?_
  nlinarith [mul_le_mul_of_nonneg_left hq hm]

theorem stepL_of (hMo : Models) (hOI : OfInt) (hSe : Seed) (hD : DecEx2) : StepL := by
  intro n ε lam ε' mu e hG s hG' hne hocc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨H, i1, i2, π, hπ⟩ := exists_ds (n + 1) ε lam hG.hc _ (by push_cast; exact hG.gap) (by
    push_cast; nlinarith [pow_pos (show (0 : ℝ) < n + 1 by linarith) 2, pow_pos (show (0 : ℝ) < n + 1 by linarith) 3])
  obtain ⟨H', i3, i4, σ, hσ⟩ := exists_ds n ε' mu hG.hc' _ hG.gap' (by
    nlinarith [pow_pos (show (0 : ℝ) < n + 1 by linarith) 2, pow_pos (show (0 : ℝ) < n + 1 by linarith) 3])
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  obtain ⟨j, hj0, hj⟩ := hocc H H' π σ hπ hσ
  obtain ⟨-, -, w, hw, hw1⟩ := PositivityTheory.UnitaryDecomposition.X4.emb.2.2.2 ε' mu σ (muG ε') inferInstance hG.hc' hσ
  obtain ⟨κ, hκ⟩ := schur_haar hσ (muG ε')
  obtain ⟨-, i, η, hin, hiH, hη, hηw, hid⟩ := hSe n ε lam ε' mu e hG H H' π σ (muG ε') inferInstance hπ hσ
    ⟨j, hj0, hj⟩ κ hκ w hw hw1
  obtain ⟨X, hXS, hXκ⟩ := hD (n + 1) ε lam H π hG.neg ⟨zi e, hG.fits.1⟩ hG.hc hπ (by push_cast; exact hG.gap)
  have hs : s ∈ X.S := (hXS s).2 hG'.hc
  have hP := intertw_adj hG.fits hπ hσ i hin hiH
  have hcor := corner_val hG.fits hG.hc hG.hc' hπ hσ X s hs (hXκ s) _ hP η hη
  set dd : ℂ := ∏ j ∈ univ.erase s, ((lam j - lam s : ℝ) : ℂ) with hdd
  set γ : ℂ := ∏ j, ((mu j - lam s + 1 / 2 : ℝ) : ℂ) with hγd
  set b := X.pr s (Pi.single (zi e) η) with hb
  set y0 := X.p s (Pi.single (zi e) η) (zi e) with hy0d
  have hγ : γ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => Complex.ofReal_ne_zero.2 fun h0 => hne k (by linarith)
  have hw' : dd * ⟪i w, y0⟫_ℂ = γ * ⟪i w, η⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right i w y0, ← ContinuousLinearMap.adjoint_inner_right i w η,
      ← inner_smul_right, ← inner_smul_right, hcor]
  have hηw' : ⟪i w, η⟫_ℂ ≠ 0 := by
    rw [← inner_conj_symm]; exact (map_ne_zero (starRingEnd ℂ)).2 hηw
  have hy0 : ⟪i w, y0⟫_ℂ ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hw'
    exact mul_ne_zero hγ hηw' hw'.symm
  have hpt : ∀ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * ⟪b, X.πs s (emb e (um h)) b⟫_ℂ * X.c s =
      conj ⟪w, σ (um h) w⟫_ℂ * ⟪η, π (emb e (um h)) y0⟫_ℂ := fun h => by
    rw [mul_assoc, mul_comm _ (X.c s), pt_id hG.fits hπ X s hs η hη h]
  have hI : (∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * ⟪b, X.πs s (emb e (um h)) b⟫_ℂ ∂(muG ε')) * X.c s =
      κ * (⟪η, i w⟫_ℂ * ⟪i w, y0⟫_ℂ) := by
    rw [← integral_mul_const]
    exact (integral_congr_ae (.of_forall hpt)).trans (hid y0)
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.1.ne'
  have hI0 : (∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * ⟪b, X.πs s (emb e (um h)) b⟫_ℂ ∂(muG ε')) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hI
    exact mul_ne_zero hκ0 (mul_ne_zero hηw hy0) hI.symm
  obtain ⟨j', hj'0, hj'⟩ := hOI n ε (lam - Pi.single s 1) ε' mu e hG' (X.Hs s) H' (X.πs s) σ (muG ε') inferInstance
    (X.ds s hs).2 hσ w hw hw1 b b hI0
  exact (hMo n ε (lam - Pi.single s 1) ε' mu e hG').1 ⟨X.Hs s, H', inferInstance, inferInstance, inferInstance, inferInstance,
    X.πs s, σ, (X.ds s hs).2, hσ, j', hj'0, hj'⟩

end PositivityTheory.RgHe.Sl
