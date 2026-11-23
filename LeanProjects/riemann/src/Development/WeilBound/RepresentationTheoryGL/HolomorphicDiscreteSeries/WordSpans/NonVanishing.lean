import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.ExistsDs
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.QminorInt

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.WordSpanNonVanishing

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC PositivityTheory.UnitaryDecomposition.Com

theorem nonvan (hKey : KeyId) {N : ℕ} {ε : Fin (N + 2) → Bool} {ε' : Fin (N + 1) → Bool} {e : Fin (N + 1) ⊕ Unit ≃ Fin (N + 2)}
    {lam : Fin (N + 2) → ℝ} {mu : Fin (N + 1) → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → (H' →L[ℂ] H')} {S : Submodule ℂ H} {E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ S}
    {S' : Submodule ℂ H'} {E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ S'} {P : H →L[ℂ] H'} (hG : Gp ε lam ε' mu e)
    (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ) (hS : IsSmMod ε π S E) (hS' : IsSmMod ε' σ S' E') (hP : Intertw ε' e π σ P)
    (hP0 : P ≠ 0) (X : Dec ε' mu σ) (hκ : ∀ s, X.κ s = (mu s : ℂ) + (((N + 1 : ℕ) : ℂ) - 1) / 2) (j : Fin (N + 1))
    (hj : j ∈ X.S) (hwall : ∀ s, mu j - 1 / 2 ≠ lam s) : ∃ η ∈ S, X.p j (phi E e P η) ≠ 0 := by
  classical
  set ι : Fin (N + 1) → Fin (N + 2) := fun a => e (Sum.inl a) with hι
  set z : Fin (N + 2) := zi e with hz
  have hιinj : Function.Injective ι := fun a b h => Sum.inl_injective (e.injective h)
  have hιz : ∀ a, ι a ≠ z := by
    intro a h
    have := e.injective h
    simp at this
  have hPS : ∀ v : S, P v ∈ S' := fun v =>
    (hS'.mem _).2 (smooth_map hG.fits hP ((hS.mem _).1 v.2))
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun v => ⟨P v, hPS v⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  have hfv : ∀ v : S, ((f v : S') : H') = P v := fun v => rfl
  have hf : ∀ (a b : Fin (N + 1)) (x : S), f (E (ι a) (ι b) x) = E' a b (f x) := by
    intro a b x
    ext
    rw [hfv, hS.act, hS'.act, hfv, ← blk_single e a b]
    exact dsigC_map hG.fits hP (fun X hX => (hS.real X hX x).differentiableAt) (single a b 1)
  set mπ : Fin (N + 2) → ℂ := fun s => (lam s : ℂ) - (((N + 2 : ℕ) : ℂ) - 1) / 2 with hmπ
  set mσ : Fin (N + 1) → ℂ := fun s => (mu s : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2 with hmσ
  have hcapπ : ∀ (u : ℂ) (v : S), qdet E u v = (∏ s, (u + mπ s)) • v := cap_of hG.hc hπ hS
  have hcapσ : ∀ (u : ℂ) (v : S'), qdet E' u v = (∏ s, (u + mσ s)) • v := cap_of hG.hc' hσ hS'
  have hw0 : ∀ y : S', qdet E' (-mσ j) y = 0 := by
    intro y
    rw [hcapσ, Finset.prod_eq_zero (Finset.mem_univ j) (by ring), zero_smul]
  set cG : ℂ := ∏ s, (-mσ j + 1 + mπ s) with hcGdef
  have hcG : cG ≠ 0 := by
    rw [hcGdef, Finset.prod_ne_zero_iff]
    intro s _ h
    apply hwall s
    have h' : -((mu j : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2) + 1 + ((lam s : ℂ) - (((N + 2 : ℕ) : ℂ) - 1) / 2) = 0 := h
    push_cast at h'
    have h2 : ((mu j - 1 / 2 : ℝ) : ℂ) = (lam s : ℂ) := by
      push_cast
      linear_combination -h'
    exact_mod_cast h2
  have hK : ∀ v : S, cG • f v = -∑ c : Fin (N + 1),
      (Th E' (-mσ j)) (fun l => f ((E (ι l) z) ((E z (ι c)) v))) c :=
    fun v => hKey S S' N E E' ι z f hS.gl hιinj hιz hf (-mσ j) cG (fun x => hcapπ _ x) hw0 v
  by_contra hno
  push_neg at hno
  let lift : (Fin (N + 1) → H') → Fin (N + 1) → S' := fun y l =>
    if h : y l ∈ S' then ⟨y l, h⟩ else 0
  have hlift : ∀ y ∈ SmT ε' σ, ∀ l, ((lift y l : S') : H') = y l := by
    intro y hy l
    simp [lift, (hS'.mem _).2 (hy l)]
  have hT0 : ∀ u : S, (Th E' (-mσ j)) (fun l => f ((E (ι l) z) u)) = 0 := by
    intro u
    set x : Fin (N + 1) → H' := phi E e P (u : H) with hxdef
    have hxl : ∀ l, x l = P ((E (ι l) z) u) := by
      intro l
      simp [hxdef, phi, ap, u.2, hι, hz]
    have hx : x ∈ SmT ε' σ := by
      intro l
      rw [hxl]
      exact (hS'.mem _).1 (hPS _)
    have hsum : ∑ t ∈ X.S, lift (X.p t x) = fun l => f ((E (ι l) z) u) := by
      funext l
      apply Subtype.ext
      rw [Finset.sum_apply, Submodule.coe_sum]
      have : ∀ t ∈ X.S, ((lift (X.p t x) l : S') : H') = X.p t x l :=
        fun t ht => hlift _ (X.p_sm t ht x hx) l
      rw [Finset.sum_congr rfl this, ← Finset.sum_apply, X.sum x hx, hxl, hfv]
    have heig : ∀ t ∈ X.S, (EE E') (lift (X.p t x)) = X.κ t • lift (X.p t x) := by
      intro t ht
      have hsm := X.p_sm t ht x hx
      funext c
      apply Subtype.ext
      have hcas := congrFun (X.cas t ht x hx) c
      simp only [casT, Pi.smul_apply] at hcas
      simp only [EE, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.coe_proj, Function.eval, Pi.smul_apply, Submodule.coe_smul,
        Submodule.coe_sum]
      rw [hlift _ hsm c, ← hcas]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hS'.act, hlift _ hsm l]
    have hκj : X.κ j = (N : ℂ) + mσ j := by
      rw [hκ j, hmσ]
      push_cast
      ring
    have hproj := th_proj hS'.gl hcapσ X.S (fun t => lift (X.p t x)) X.κ X.κ_inj heig hj j hκj
    rw [hsum] at hproj
    rw [hproj]
    have hpj : lift (X.p j x) = 0 := by
      rw [hno _ u.2]
      funext l
      simp [lift]
    rw [hpj, smul_zero]
  have hPv : ∀ v : S, P v = 0 := by
    intro v
    have h1 := hK v
    simp only [hT0, Pi.zero_apply, Finset.sum_const_zero, neg_zero] at h1
    have h2 : f v = 0 := (smul_eq_zero.1 h1).resolve_left hcG
    have h3 := congrArg (fun y : S' => (y : H')) h2
    simpa [hfv] using h3
  have hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * ((N + 2 : ℕ) : ℝ) ^ 3) := by
    intro a b hab
    refine le_trans ?_ (hG.gap a b hab)
    push_cast
    have : (0 : ℝ) ≤ ((N : ℝ) + 2) ^ 3 := by positivity
    nlinarith
  have hdense : Dense (S : Set H) :=
    PositivityTheory.RgHe.SM.dense_sm (by omega) hG.hc hπ hgap hS
  apply hP0
  have heq := Continuous.ext_on hdense P.continuous (continuous_const (y := (0 : H')))
    (fun x hx => hPv ⟨x, hx⟩)
  ext x
  simpa using congrFun heq x

end PositivityTheory.RgHe.SM.WordSpanNonVanishing
