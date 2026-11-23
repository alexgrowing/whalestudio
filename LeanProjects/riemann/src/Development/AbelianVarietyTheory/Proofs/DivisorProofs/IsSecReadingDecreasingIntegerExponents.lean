import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedIsSecZeroKeySection

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlatTw.Hol

theorem isSec_of_local_quot {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (μ : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (h : ∀ x₀ ∈ X.dom, ∃ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P P' : Frame X.Ψ r → ℂ), X.IsSec (μ + la) P ∧
      X.IsSec la P' ∧ P' x₀ ≠ 0 ∧ ∀ x ∈ X.dom, Q x * P' x = P x) : X.IsSec μ Q := by
  refine ⟨?_, ?_, ?_⟩
  · intro x₀ hx₀
    obtain ⟨la, P, P', hP, hP', hne, hQ⟩ := h x₀ hx₀
    have hd : DifferentiableWithinAt ℂ (fun y => P y * (P' y)⁻¹) X.dom x₀ :=
      (hP.1 x₀ hx₀).mul ((hP'.1 x₀ hx₀).inv hne)
    have hc : ContinuousWithinAt P' X.dom x₀ := hP'.1.continuousOn x₀ hx₀
    have hev := Filter.Tendsto.eventually hc (eventually_ne_nhds hne)
    have hd' : DifferentiableWithinAt ℂ Q (X.dom ∩ {z | P' z ≠ 0}) x₀ := by
      refine (hd.mono Set.inter_subset_left).congr (fun z hz => ?_) ?_
      · exact (eq_mul_inv_iff_mul_eq₀ hz.2).2 (hQ z hz.1)
      · exact (eq_mul_inv_iff_mul_eq₀ hne).2 (hQ x₀ hx₀)
    exact (differentiableWithinAt_inter' hev).1 hd'
  · intro x hx b hb
    obtain ⟨la, P, P', hP, hP', hne, hQ⟩ := h x hx
    have hb' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
    have hdiag : ∀ (τ : X.Ψ) (i : Fin r), b τ i i ≠ 0 := by
      intro τ i
      have hbt : (mat b τ).BlockTriangular id := fun a c hac => (hb' τ).2 a c hac
      have hdet := (hb' τ).1
      rw [Matrix.det_of_upperTriangular hbt] at hdet
      exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
    have hcl : bchar la b ≠ 0 := by
      unfold bchar
      exact Finset.prod_ne_zero_iff.mpr fun τ _ =>
        Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hdiag τ i)
    have hsplit : bchar (μ + la) b = bchar μ b * bchar la b := by
      unfold bchar
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun τ _ => ?_)
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Pi.add_apply, Pi.add_apply, zpow_add₀ (hdiag τ i)]
    have h1 := hQ (rmul x b) (dom_rmul X hx hb)
    rw [hP.2.1 x hx b hb, hP'.2.1 x hx b hb, ← hQ x hx, hsplit] at h1
    apply mul_right_cancel₀ (mul_ne_zero hcl hne)
    calc Q (rmul x b) * (bchar la b * P' x) = bchar μ b * bchar la b * (Q x * P' x) := h1
      _ = bchar μ b * Q x * (bchar la b * P' x) := by ring
  · intro γ hγ x hx
    obtain ⟨la, P, P', hP, hP', hne, hQ⟩ := h x hx
    have hχ : X.χ la γ ≠ 0 := by
      obtain ⟨n, hn, hpow⟩ := X.χ_fin la
      intro h0
      have h2 := hpow γ hγ
      rw [h0, zero_pow hn.ne'] at h2
      exact zero_ne_one h2
    have h1 := hQ (lact γ x) (ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_dom X hγ hx)
    rw [hP.2.2 γ hγ x hx, hP'.2.2 γ hγ x hx, ← hQ x hx, X.χ_add μ la γ hγ] at h1
    apply mul_right_cancel₀ (mul_ne_zero hχ hne)
    calc Q (lact γ x) * (X.χ la γ * P' x) = X.χ μ γ * X.χ la γ * (Q x * P' x) := h1
      _ = X.χ μ γ * Q x * (X.χ la γ * P' x) := by ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem pow_succ_mem_secZ {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) (N : ℕ) :
    g ^ (N + 1) ∈ GlobalTheory.AllWt.secZ Xo c ((N + 1) • e) :=
  by
  induction N with
  | zero => simpa using hg
  | succ N ih =>
    rw [pow_succ, succ_nsmul]
    exact GlobalTheory.AllWt.mul_mem_secZ ih hg

theorem rdU_pow_succ_apply (U : Unf Xo c σ r) (g : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r) (N : ℕ) :
    rdU U (g ^ (N + 1)) k x = rdU U g k x ^ (N + 1) :=
  by
  induction N with
  | zero => simp only [zero_add, pow_one]
  | succ N ih =>
    calc rdU U (g ^ (N + 1 + 1)) k x = rdU U (g ^ (N + 1) * g) k x := by rw [pow_succ]
      _ = rdU U (g ^ (N + 1)) k x * rdU U g k x := by rw [GlobalTheory.AllWt.rdU_mul]; rfl
      _ = rdU U g k x ^ (N + 1 + 1) := by rw [ih, ← pow_succ]

theorem isSec_modelWt_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), Nonempty (KeySec Xo c) → GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ G : WTZ E, Even G.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) → ∀ f ∈ secZ Xo c (exZ Dw G), ∀ k, (U.X k).IsSec (modelWt U G k) (rdU U f k) := by
  intro E _ _ _ H Dw l Xo c σ r U hκ hσ hU hpq G hG hdec f hf k
  obtain ⟨κ⟩ := hκ
  have hU' := hU
  unfold IsUnf at hU'
  have hUsec := hU'.2.2.2.2.1
  have hsn : ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), secZ Xo c (exZ Dw (wtZ a n)) = sec Xo c a n :=
    fun a n => by rw [GlobalTheory.AllWt.exZ_wtZ]; exact GlobalTheory.AllWt.secZ_nat Xo c a n
  have hG2 := hG
  obtain ⟨g2, hg2⟩ := hG2
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = |G.2| := ⟨G.2.natAbs, Int.natCast_natAbs _⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), -(B : ℤ) ≤ G.1 (τ, j) := by
    refine ⟨∑ τ : E →+* ℂ, ∑ j : Fin (Dw.mult τ), (G.1 (τ, j)).natAbs, fun τ j => ?_⟩
    have h1 : (G.1 (τ, j)).natAbs ≤ ∑ j' : Fin (Dw.mult τ), (G.1 (τ, j')).natAbs :=
      Finset.single_le_sum (f := fun j' : Fin (Dw.mult τ) => (G.1 (τ, j')).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ j' : Fin (Dw.mult τ), (G.1 (τ, j')).natAbs ≤
        ∑ τ' : E →+* ℂ, ∑ j' : Fin (Dw.mult τ'), (G.1 (τ', j')).natAbs :=
      Finset.single_le_sum (f := fun τ' : E →+* ℂ => ∑ j' : Fin (Dw.mult τ'), (G.1 (τ', j')).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    have h3 : -((G.1 (τ, j)).natAbs : ℤ) ≤ G.1 (τ, j) := by
      rw [Int.natCast_natAbs]; exact neg_abs_le _
    have h4 : ((G.1 (τ, j)).natAbs : ℤ) ≤
        ((∑ τ' : E →+* ℂ, ∑ j' : Fin (Dw.mult τ'), (G.1 (τ', j')).natAbs : ℕ) : ℤ) := by
      exact_mod_cast h1.trans h2
    linarith
  apply isSec_of_local_quot (U.X k) (modelWt U G k) (rdU U f k)
  intro x₀ hx₀
  obtain ⟨m, f₀, hf₀, hne⟩ :=
    GlobalTheory.CuspFrom.KeyHol.exists_sec_rdU_ne_zero (Formalism.L2.PjFree.Unf.ofPj U) k x₀ hx₀
  have hne' : rdU U f₀ k x₀ ≠ 0 := hne
  obtain ⟨tg, htg⟩ : ∃ tg : ℕ, tg = (B + 1) * m + (N + 1) * (m + 1) := ⟨_, rfl⟩
  have htg1 : (N : ℤ) + 1 ≤ (tg : ℤ) := by
    rw [htg]; push_cast
    have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
    have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg N
    have hB0 : (0 : ℤ) ≤ B := Nat.cast_nonneg B
    nlinarith [mul_nonneg hB0 hm0, mul_nonneg hN0 hm0]
  have hnn : 0 ≤ g2 + (tg : ℤ) := by
    linarith [le_abs_self G.2, neg_le_abs G.2]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = g2 + tg := ⟨(g2 + tg).toNat, Int.toNat_of_nonneg hnn⟩
  obtain ⟨ag, hag⟩ : ∃ ag : (E →+* ℂ) × ℕ → ℕ, ∀ τ i, ag (τ, i) = if i < Dw.mult τ then B + 1 else 0 :=
    ⟨fun x => if x.2 < Dw.mult x.1 then B + 1 else 0, fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (E →+* ℂ) × ℕ → ℕ, ∀ τ i,
      (a (τ, i) : ℤ) = if i < Dw.mult τ then G.1 (τ, i) + ((B : ℤ) + 1) else 0 := by
    refine ⟨fun x => if x.2 < Dw.mult x.1 then (G.1 x + ((B : ℤ) + 1)).toNat else 0, fun τ i => ?_⟩
    dsimp only
    split_ifs with h
    · refine Int.toNat_of_nonneg ?_
      have h5 := hB τ ⟨i, h⟩
      simp only at h5
      linarith
    · simp

  have hf₀Z : f₀ ∈ secZ Xo c (exZ Dw (wtZ 0 (2 * (m + 1)))) := by rw [hsn]; exact hf₀
  have hgZ' : (κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1) ∈
      secZ Xo c ((fun i => ((B + 1 : ℕ) : ℤ) * keyEx Dw i) + (B + 1 + N + 1) • exZ Dw (wtZ 0 (2 * (m + 1)))) :=
    GlobalTheory.AllWt.mul_mem_secZ (κ.pow_mem (B + 1)) (pow_succ_mem_secZ hf₀Z (B + 1 + N))
  have hEg : exZ Dw (wtZ ag (2 * tg)) =
      (fun i => ((B + 1 : ℕ) : ℤ) * keyEx Dw i) + (B + 1 + N + 1) • exZ Dw (wtZ 0 (2 * (m + 1))) := by
    funext i
    rcases i with _ | ⟨τ, j⟩
    · simp [exZ, wtZ, keyEx, htg]
      ring
    · simp [exZ, wtZ, keyEx, hag]
  have hgZ : (κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1) ∈ secZ Xo c (exZ Dw (wtZ ag (2 * tg))) := by
    rw [hEg]; exact hgZ'
  have hgsec : (κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1) ∈ sec Xo c ag (2 * tg) := by
    rw [← hsn]; exact hgZ

  have hEa : exZ Dw (wtZ a (2 * t)) = exZ Dw G + exZ Dw (wtZ ag (2 * tg)) := by
    funext i
    rcases i with _ | ⟨τ, j⟩
    · simp [exZ, wtZ]
      linarith
    · simp [exZ, wtZ, hag]
      rw [ha τ j, if_pos j.isLt]
  have hfgsec : f * ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1)) ∈ sec Xo c a (2 * t) := by
    rw [← hsn, hEa]; exact GlobalTheory.AllWt.mul_mem_secZ hf hgZ

  have hDomG : Dom ag (2 * tg) := by
    refine ⟨fun τ i j hij => ?_, even_two_mul tg⟩
    show ag (τ, j) ≤ ag (τ, i)
    rw [hag, hag]
    split_ifs <;> omega
  have hDomA : Dom a (2 * t) := by
    refine ⟨fun τ i j hij => ?_, even_two_mul t⟩
    show a (τ, j) ≤ a (τ, i)
    have hi := ha τ i
    have hj := ha τ j
    by_cases hjm : j < Dw.mult τ
    · have him : i < Dw.mult τ := lt_of_le_of_lt hij hjm
      rw [if_pos hjm] at hj
      rw [if_pos him] at hi
      have hd := hdec τ i j hij hjm
      omega
    · rw [if_neg hjm] at hj
      omega

  have hWeven : Even (wtZ ag (2 * tg)).2 := ⟨(tg : ℤ), by simp [wtZ, two_mul]⟩
  have hEx : exZ Dw (wtZ a (2 * t)) = exZ Dw (G + wtZ ag (2 * tg)) := by
    rw [GlobalTheory.FlatTw.exZ_add_eq]; exact hEa
  have hwt : modelWt U G k + laU U ag (2 * tg) k = laU U a (2 * t) k := by
    rw [← GlobalTheory.AllWt.modelWt_wtZ U ag, ← GlobalTheory.AllWt.modelWt_wtZ U a, ← GlobalTheory.AllWt.modelWt_add U hG hWeven k, GlobalTheory.AllWt.modelWt_congr U hσ hU hEx]

  have h1ne : rdU U 1 k x₀ ≠ 0 := by
    intro h0
    apply hne'
    have h6 : rdU U (f₀ * 1) k x₀ = rdU U f₀ k x₀ * rdU U 1 k x₀ := by rw [GlobalTheory.AllWt.rdU_mul]; rfl
    rw [mul_one, h0, mul_zero] at h6
    exact h6
  have hρne : rdU U (κ.ρ : Rul Xo c) k x₀ ≠ 0 := by
    intro h0
    apply h1ne
    have h6 : rdU U ((κ.ρ : Rul Xo c) * ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)) k x₀ =
        rdU U (κ.ρ : Rul Xo c) k x₀ * rdU U ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) k x₀ := by rw [GlobalTheory.AllWt.rdU_mul]; rfl
    rw [Units.mul_inv, h0, zero_mul] at h6
    exact h6
  have hgx : rdU U ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1)) k x₀ =
      rdU U (κ.ρ : Rul Xo c) k x₀ ^ (B + 1) * rdU U f₀ k x₀ ^ (B + 1 + N + 1) := by
    rw [← rdU_pow_succ_apply U (κ.ρ : Rul Xo c) k x₀ B, ← rdU_pow_succ_apply U f₀ k x₀ (B + 1 + N), GlobalTheory.AllWt.rdU_mul]
    rfl
  refine ⟨laU U ag (2 * tg) k, rdU U (f * ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1))) k,
    rdU U ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1)) k, ?_, ?_, ?_, ?_⟩
  · rw [hwt]; exact hUsec a (2 * t) hDomA _ hfgsec k
  · exact hUsec ag (2 * tg) hDomG _ hgsec k
  · rw [hgx]; exact mul_ne_zero (pow_ne_zero _ hρne) (pow_ne_zero _ hne')
  · intro x _
    exact (congrFun (congrFun (GlobalTheory.AllWt.rdU_mul U f ((κ.ρ : Rul Xo c) ^ (B + 1) * f₀ ^ (B + 1 + N + 1))) k) x).symm

end GlobalTheory.FlatTw.Hol
