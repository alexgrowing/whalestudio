import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRdUFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerExponentSectionEqZeroOfIncreasingFlagStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_succ_mem_secZ {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e) (m : ℕ) :
    g ^ (m + 1) ∈ secZ Xo c ((m + 1) • e) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_secZ ih hg

theorem differentiableOn_rdU_of_antitone {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hU : IsUnf U)
    (hpq : 1 ≤ Dw.p + Dw.q) {e : Ix Dw → ℤ} (he0 : e none = 0)
    (hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩))
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (k : U.Comp) : DifferentiableOn ℂ (rdU U f k) (U.X k).dom := by
  intro x hx
  have ho : IsOpen (U.X k).dom := FourierCoefficientDomain.isOpen_dom _
  obtain ⟨n, hn, g, hg, hg0⟩ := GlobalTheory.TrueCx.FlatConst.exists_sec_four hpq (U.un k ⟨x, hx⟩)
  set M : ℕ := ∑ i : Ix Dw, (e i).natAbs with hMdef
  have hM : ∀ i, -(4 * ((M + 1 : ℕ) : ℤ)) ≤ e i := fun i => by
    have h1 : (e i).natAbs ≤ M := Finset.single_le_sum (f := fun i => (e i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    have h2 : -((e i).natAbs : ℤ) ≤ e i := by
      have := Int.natAbs_abs (e i); rw [← Int.abs_eq_natAbs]; exact neg_abs_le _
    have h3 : ((e i).natAbs : ℤ) ≤ M := by exact_mod_cast h1
    push_cast; linarith
  let a : (E →+* ℂ) × ℕ → ℕ := fun p =>
    if h : p.2 < Dw.mult p.1 then (4 * ((M + 1 : ℕ) : ℤ) + e (some ⟨p.1, ⟨p.2, h⟩⟩)).toNat else 0
  have hdom : Dom a ((M + 1) * n) := by
    refine ⟨fun τ i j hij => ?_, hn.mul_left _⟩
    show a (τ, j) ≤ a (τ, i)
    simp only [a]
    by_cases hj : j < Dw.mult τ
    · have hi : i < Dw.mult τ := lt_of_le_of_lt hij hj
      rw [dif_pos hj, dif_pos hi]
      exact Int.toNat_le_toNat (by linarith [hanti τ ⟨i, hi⟩ ⟨j, hj⟩ hij])
    · rw [dif_neg hj]; exact Nat.zero_le _
  have hgp := pow_succ_mem_secZ (Xo := Xo) (c := c) (by rw [secZ_nat]; exact hg) M
  have hgf : g ^ (M + 1) * f ∈ sec Xo c a ((M + 1) * n) := by
    rw [← secZ_nat]
    convert mul_mem_secZ hgp hf using 2
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp [ex, he0]
    · have hi := i.2
      rw [Pi.add_apply, Pi.smul_apply]
      simp only [ex, a, dif_pos hi, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (by linarith [hM (some ⟨τ, i⟩)])]
      push_cast
      ring
  have d1 := (hU.2.2.2.2.1 _ n ⟨fun _ _ _ _ => le_rfl, hn⟩ g hg k).1
  have d2 := (hU.2.2.2.2.1 _ _ hdom _ hgf k).1
  have hx0 : rdU U g k x ≠ 0 := by
    have : rdU U g k x = toC (evR Xo c g (U.un k ⟨x, hx⟩)) := dif_pos hx
    rwa [this]
  have a1 := d1.differentiableAt (ho.mem_nhds hx)
  have a2 := d2.differentiableAt (ho.mem_nhds hx)
  refine ((a2.mul ((a1.pow (M + 1)).inv (pow_ne_zero _ hx0))).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [a1.continuousAt.eventually_ne hx0] with y hy0
  have e1 : rdU U (g ^ (M + 1) * f) k y = rdU U g k y ^ (M + 1) * rdU U f k y := by
    rw [rdU_mul]
    have : ∀ m : ℕ, rdU U (g ^ (m + 1)) = rdU U g ^ (m + 1) := fun m => by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ g (m + 1), rdU_mul, ih, ← pow_succ]
    rw [this]; rfl
  rw [Pi.mul_apply, Pi.inv_apply, e1, Pi.pow_apply, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ hy0), one_mul]

end GlobalTheory.ReadCont

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem continuousOn_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (e : Ix Dw → ℤ), e none = 0 → ∀ s ∈ secZ Xo c e, ∀ σ, GoodEmb c σ → ∀ k, ContinuousOn (rdU (U σ) s k) ((U σ).X k).dom := by
  intro E _ _ _ H Dw l Xo c r U x hL e he0 s hs σ hσ k
  by_cases hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩)
  · exact (differentiableOn_rdU_of_antitone (hL.unf σ hσ) hL.pos he0 hanti hs k).continuousOn
  · push_neg at hanti
    obtain ⟨τ, i, j, hij, hlt⟩ := hanti
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    rw [GlobalTheory.T.integerExponentSection_eq_zero_of_increasing_flag E H Dw l Xo c e τ i j hij' hlt s hs, map_zero]
    exact continuousOn_const

end GlobalTheory.ReadCont
