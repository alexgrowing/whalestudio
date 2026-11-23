import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.RootOfNe
import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.ContDiffEmb
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

noncomputable section

open Matrix Finset

namespace PositivityTheory.UnitaryDecomposition.Com

open Formalism.REAL PI.DSInfCharCap CompanionTheory.D.DSIC Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

theorem cap_of {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hπ : Formalism.MainNotions.S.IsDS ε lam π)
    {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S} (hS : IsSmMod ε π S E) (u : ℂ) (v : S) :
    qdet E u v = (∏ j, (u + ((lam j : ℂ) - ((m : ℂ) - 1) / 2))) • v := by
  have h := discrete_series_infinitesimal_character m ε lam H π hl hπ v ((hS.mem _).1 v.2) (u - ((m : ℂ) - 1) / 2)
  rw [sub_add_cancel, hActQ m ε H π S E hS] at h
  refine Subtype.ext (h.trans ?_)
  rw [Submodule.coe_smul, Formalism.QuantumDeterminants.capP]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by ring

theorem one_le_diff {m : ℕ} {lam : Fin m → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) {i j : Fin m} (h : j ≠ i) :
    1 ≤ |lam j - lam i| := by
  obtain ⟨a, ha⟩ := hl.2 i
  obtain ⟨b, hb⟩ := hl.2 j
  have e : lam j - lam i = ((b - a : ℤ) : ℝ) := by push_cast; linarith
  have h0 : b - a ≠ 0 := fun h0 => h (hl.1.injective (by rw [h0] at e; simpa [sub_eq_zero] using e))
  rw [e, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h0

theorem spread {n : ℕ} {lam : Fin (n + 1) → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) {B : ℝ} (hB : ∀ a, |lam a| ≤ B) :
    (n : ℝ) ≤ 2 * B := by
  have hA := hl.1
  have key : ∀ k : ℕ, ∀ hk : k ≤ n, (k : ℝ) ≤ lam 0 - lam ⟨k, by omega⟩ := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hlt : lam ⟨k + 1, by omega⟩ < lam ⟨k, by omega⟩ := hA (by simp [Fin.lt_def])
      have hne : (⟨k + 1, by omega⟩ : Fin (n + 1)) ≠ ⟨k, by omega⟩ := by simp [Fin.ext_iff]
      have h2 := one_le_diff hl hne
      rw [abs_of_neg (by linarith)] at h2
      push_cast
      linarith
  have h := key n le_rfl
  have h0 := (abs_le.mp (hB 0)).2
  have hn := (abs_le.mp (hB ⟨n, by omega⟩)).1
  linarith

private theorem exists_norm_le_one_p_eq_smul_Th {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → H →L[ℂ] H}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hπ : Formalism.MainNotions.S.IsDS ε lam π) {S : Submodule ℂ H}
    {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ S} (hS : IsSmMod ε π S E) (X : Dec ε lam π)
    {s : Fin (n + 1)} (hs : s ∈ X.S) :
    ∃ (i : Fin (n + 1)) (c0 : ℂ), ‖c0‖ ≤ 1 ∧ ∀ (x : Fin (n + 1) → S) (c : Fin (n + 1)),
      X.p s (fun l => (x l : H)) c =
        c0 • ((Th E (-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2)) x c : S) : H) := by
  classical
  set mm : Fin (n + 1) → ℂ := fun j => (lam j : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2 with hmm
  have hq : ∀ (u : ℂ) (v : S), qdet E u v = (∏ j, (u + mm j)) • v := fun u v => cap_of hl hπ hS u v
  have hgl : GlRel E := hS.gl
  have hxs : ∀ x : Fin (n + 1) → S, (fun l => (x l : H)) ∈ SmT ε π := fun x l => (hS.mem _).1 (x l).2
  let Y : (Fin (n + 1) → S) → Fin (n + 1) → Fin (n + 1) → S := fun x t c =>
    if ht : t ∈ X.S then ⟨X.p t (fun l => (x l : H)) c, (hS.mem _).2 (X.p_sm t ht _ (hxs x) c)⟩ else 0
  have hYs : ∀ x t, t ∈ X.S → ∀ c, ((Y x t c : S) : H) = X.p t (fun l => (x l : H)) c := by
    intro x t ht c
    simp [Y, ht]
  have hEig : ∀ x t, t ∈ X.S → EE E (Y x t) = X.κ t • Y x t := by
    intro x t ht
    funext c
    apply Subtype.ext
    rw [EE_apply]
    simp only [Submodule.coe_sum, hS.act, Pi.smul_apply, Submodule.coe_smul, hYs x t ht]
    have h2 := congrFun (X.cas t ht _ (hxs x)) c
    simpa [casT] using h2
  have hSum : ∀ x, ∑ t ∈ X.S, Y x t = x := by
    intro x
    funext c
    apply Subtype.ext
    rw [Finset.sum_apply, Submodule.coe_sum, Finset.sum_congr rfl fun t ht => hYs x t ht c,
      ← Finset.sum_apply, X.sum _ (hxs x)]
  by_cases h0 : ∀ x : Fin (n + 1) → S, Y x s = 0
  · refine ⟨0, 0, by simp, fun x c => ?_⟩
    rw [← hYs x s hs c, h0 x]
    simp
  · push_neg at h0
    obtain ⟨x0, hx0⟩ := h0
    obtain ⟨i, hi⟩ := root_of_ne hgl hq (hEig x0 s hs) hx0
    set D := ∏ j ∈ univ.erase i, (-mm i + mm j) with hD
    have hD1 : 1 ≤ ‖D‖ := by
      rw [hD, norm_prod]
      calc (1 : ℝ) = ∏ j ∈ univ.erase i, (1 : ℝ) := by simp
        _ ≤ ∏ j ∈ univ.erase i, ‖-mm i + mm j‖ := by
          apply Finset.prod_le_prod (fun _ _ => zero_le_one)
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          have he : -mm i + mm j = ((lam j - lam i : ℝ) : ℂ) := by
            simp only [hmm]
            push_cast
            ring
          rw [he, Complex.norm_real, Real.norm_eq_abs]
          exact one_le_diff hl hji
    have hDne : D ≠ 0 := by
      intro h
      rw [h, norm_zero] at hD1
      linarith
    refine ⟨i, D⁻¹, ?_, fun x c => ?_⟩
    · rw [norm_inv]
      exact inv_le_one_of_one_le₀ hD1
    · have hT := th_proj hgl hq X.S (Y x) X.κ X.κ_inj (fun t ht => hEig x t ht) hs i hi
      rw [hSum x] at hT
      rw [hT, Pi.smul_apply, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hDne, one_smul, hYs x s hs c]

private theorem list_prod_E_apply_eq_dsigCW {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin m) (Fin m) ℂ → H →L[ℂ] H} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S}
    (hS : IsSmMod ε π S E) (W : List (Fin m × Fin m)) (w : S) :
    (((W.map (fun p => E p.1 p.2)).prod w : S) : H) =
      dsigCW ε π (W.map (fun p => single p.1 p.2 (1 : ℂ))) (w : H) := by
  induction W with
  | nil => rfl
  | cons p W ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [hS.act, ih]
    rfl

private theorem hs_single_one_le_one {m : ℕ} (a b : Fin m) : hs (single a b (1 : ℂ)) ≤ 1 := by
  simp only [hs, Matrix.single_apply]
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem comat_of (hW : WordBd) : Comat := by
  unfold Comat ForPairs
  intro n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ X s hs
  obtain ⟨S, E, hS⟩ := hSmMod (n + 1) ε H π (show PI.UpqRep.IsDS ε lam π from hπ).2.2.1
  obtain ⟨S', E', hS'⟩ := hSmMod n ε' H' σ (show PI.UpqRep.IsDS ε' mu σ from hσ).2.2.1
  obtain ⟨i, c0, hc0, hform⟩ := exists_norm_le_one_p_eq_smul_Th hP.hc hπ hS X hs
  have hn2 := hP.two
  have hB : (n : ℝ) ≤ 2 * B := spread hP.hc hP.bd
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hB1 : 1 ≤ B := by linarith
  have hK1 : (1 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  refine ⟨?_, ?_⟩
  · intro v hv l c
    have hGap : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * ((n + 1 : ℕ) : ℝ) ^ 3) := by
      intro a b hab
      refine le_trans ?_ (hP.gap a b hab)
      have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
      push_cast
      linarith
    obtain ⟨hsm, hwb⟩ := hW (n + 1) ε lam B H π (by omega) hP.hc hπ hP.bd hGap v hv
    let vs : S := ⟨v, (hS.mem v).2 hsm⟩
    have hx : (fun l' => ((Pi.single l vs : Fin (n + 1) → S) l' : H)) = Pi.single l v := by
      funext l'
      by_cases h : l' = l
      · subst h
        simp [vs]
      · simp [h]
    have h1 := hform (Pi.single l vs) c
    rw [hx, th_single] at h1
    rw [h1, norm_smul, Submodule.coe_smul, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    set M : ℝ := 8 * √((n + 1 : ℕ) : ℝ) * (B + n) with hMdef
    have hM : ∀ W : List (Fin (n + 1) × Fin (n + 1)), W.length ≤ n →
        ‖(W.map (fun p => E p.1 p.2)).prod vs‖ ≤ M ^ W.length * ‖vs‖ := by
      intro W hWl
      have h3 := hwb n (W.map (fun p => single p.1 p.2 (1 : ℂ))) (by simpa using hWl)
        (by
          simp only [List.mem_map]
          rintro _ ⟨p, _, rfl⟩
          exact hs_single_one_le_one p.1 p.2)
      rw [List.length_map] at h3
      show ‖(((W.map (fun p => E p.1 p.2)).prod vs : S) : H)‖ ≤ M ^ W.length * ‖v‖
      rw [list_prod_E_apply_eq_dsigCW hS W vs]
      exact h3
    have hR : ∀ k : Fin n, ‖-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) - ((k : ℕ) : ℂ)‖ ≤ 4 * B := by
      intro k
      have he : -((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) - ((k : ℕ) : ℂ)
          = ((-lam i + (n : ℝ) / 2 - (k : ℕ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [he, Complex.norm_real, Real.norm_eq_abs]
      have hk : ((k : ℕ) : ℝ) ≤ n := by exact_mod_cast k.2.le
      have hk0 : (0 : ℝ) ≤ (k : ℕ) := by positivity
      have h2 := hP.bd i
      rw [abs_le] at h2 ⊢
      constructor <;> nlinarith
    have hq : ‖((qminor E l.succAbove c.succAbove (-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2)) vs : S) : H)‖
        ≤ (n.factorial : ℝ) * ((4 * B + M) ^ n * ‖v‖) :=
      qminor_bd (t := n) (by linarith) (by positivity) hM l.succAbove c.succAbove _ hR
    set K : ℝ := 8 * ((n : ℝ) + 1) * B with hKdef
    have hsq : √((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by push_cast; nlinarith⟩
    have hM3 : M ≤ 3 * K := by
      rw [hMdef, hKdef]
      have h0 : (0 : ℝ) ≤ B + n := by positivity
      have h5 : B + n ≤ 3 * B := by linarith
      calc 8 * √((n + 1 : ℕ) : ℝ) * (B + n) ≤ 8 * ((n : ℝ) + 1) * (3 * B) := by
            apply mul_le_mul (by linarith) h5 h0 (by positivity)
        _ = 3 * (8 * ((n : ℝ) + 1) * B) := by ring
    have hK24 : 24 * B ≤ K := by rw [hKdef]; nlinarith
    have h4 : 4 * B + M ≤ K ^ 2 := by nlinarith
    have hfact : (n.factorial : ℝ) ≤ K ^ n := by
      calc (n.factorial : ℝ) ≤ ((n ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow n
        _ = (n : ℝ) ^ n := by push_cast; ring
        _ ≤ K ^ n := pow_le_pow_left₀ (by positivity) (by nlinarith) n
    calc ‖c0‖ * _ ≤ 1 * ((n.factorial : ℝ) * ((4 * B + M) ^ n * ‖v‖)) :=
          mul_le_mul hc0 hq (norm_nonneg _) zero_le_one
      _ = ((n.factorial : ℝ) * (4 * B + M) ^ n) * ‖v‖ := by ring
      _ ≤ K ^ (4 * (n + 1)) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        have hM0 : 0 ≤ M := by positivity
        calc (n.factorial : ℝ) * (4 * B + M) ^ n ≤ K ^ n * (K ^ 2) ^ n :=
              mul_le_mul hfact (pow_le_pow_left₀ (by positivity) h4 n) (by positivity) (by positivity)
          _ = K ^ (3 * n) := by rw [← pow_mul, ← pow_add]; ring_nf
          _ ≤ K ^ (4 * (n + 1)) := pow_le_pow_right₀ hK1 (by omega)
  · refine ⟨c0 * ∏ j : Fin n, (-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) + ((mu j : ℂ) - ((n : ℂ) - 1) / 2)), ?_, ?_⟩
    · rw [norm_mul, norm_prod]
      have hprod : ∏ j : Fin n, ‖-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) + ((mu j : ℂ) - ((n : ℂ) - 1) / 2)‖
          ≤ (8 * ((n : ℝ) + 1) * B) ^ n := by
        calc _ ≤ ∏ j : Fin n, (8 * ((n : ℝ) + 1) * B) := by
              apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              intro j _
              have he : -((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2) + ((mu j : ℂ) - ((n : ℂ) - 1) / 2)
                  = ((mu j - lam i + 1 / 2 : ℝ) : ℂ) := by
                push_cast
                ring
              rw [he, Complex.norm_real, Real.norm_eq_abs]
              have h1 := hP.bd i
              have h2 := hP.bd' j
              rw [abs_le] at h1 h2 ⊢
              constructor <;> nlinarith
          _ = _ := by simp
      calc ‖c0‖ * _ ≤ 1 * (8 * ((n : ℝ) + 1) * B) ^ n :=
            mul_le_mul hc0 hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
        _ ≤ _ := by
          rw [one_mul]
          exact pow_le_pow_right₀ hK1 (Nat.le_succ n)
    · intro P hPI η hη
      have hηS : η ∈ S := (hS.mem η).2 hη
      let ηs : S := ⟨η, hηS⟩
      have hx : (fun l => ((Pi.single (zi e) ηs : Fin (n + 1) → S) l : H)) = Pi.single (zi e) η := by
        funext l
        by_cases h : l = zi e
        · subst h
          simp [ηs]
        · simp [h]
      have h1 := hform (Pi.single (zi e) ηs) (zi e)
      rw [hx, th_single] at h1
      rw [h1]
      have hpow : ((-1 : ℂ) ^ ((zi e : ℕ) + (zi e : ℕ))) = 1 := by
        rw [← two_mul, pow_mul]
        simp
      rw [hpow, one_smul]
      have hι : Function.Injective (fun a : Fin n => e (Sum.inl a)) :=
        fun a b h => Sum.inl_injective (e.injective h)
      have hιz : ∀ a : Fin n, e (Sum.inl a) ≠ zi e := fun a h => by
        have := e.injective h
        simp at this
      rw [corner hS.gl (zi e) _ hι hιz]
      have hPS : ∀ w : S, P w ∈ S' := fun w => (hS'.mem _).2 (smooth_map hF hPI ((hS.mem _).1 w.2))
      let f : S →ₗ[ℂ] S' := LinearMap.codRestrict S' (P.toLinearMap ∘ₗ S.subtype) hPS
      have hf : ∀ w : S, ((f w : S') : H') = P w := fun w => rfl
      have hcomm : ∀ (a b : Fin n) (w : S),
          f (E (e (Sum.inl a)) (e (Sum.inl b)) w) = E' a b (f w) := by
        intro a b w
        apply Subtype.ext
        rw [hf, hS'.act, hf, hS.act, ← blk_single]
        exact dsigC_map hF hPI (fun Xm hXm => (hS.real Xm hXm w).differentiableAt) (single a b 1)
      have hqi := qdet_int (E := fun a b => E (e (Sum.inl a)) (e (Sum.inl b))) f hcomm
        (-((lam i : ℂ) - (((n + 1 : ℕ) : ℂ) - 1) / 2)) ηs
      rw [cap_of hP.hc' hσ hS'] at hqi
      rw [map_smul, ← hf, hqi, Submodule.coe_smul, hf, smul_smul]

end PositivityTheory.UnitaryDecomposition.Com
