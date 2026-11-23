import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps

noncomputable section

namespace RootFieldNumerics.Sq

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

theorem sum_fundOnRoot {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {A : Type} [AddCommGroup A] (a : Ψ × Fin N)
    (f : Ψ × Fin N → A) : ∑ r, fundOnRoot a r • f r = -∑ k ∈ Finset.Iic a.2, f (a.1, k) := by
  obtain ⟨x0, k0⟩ := a
  have h : ∀ r : Ψ × Fin N, fundOnRoot (x0, k0) r • f r = if r.1 = x0 ∧ r.2 ≤ k0 then -f r else 0 := by
    intro r
    simp only [fundOnRoot]
    split_ifs <;> simp_all
  simp only [h]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x0]
  · simp only [true_and, ← Finset.sum_filter, Finset.sum_neg_distrib]
    congr 2
    ext k
    simp
  · intro x _ hx
    simp [hx]
  · intro hx
    exact absurd (Finset.mem_univ x0) hx

theorem log_combLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J] (ℓ : J → HermLine ι)
    (n : J → ℤ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((Top.combLine ℓ n).h z) = ∑ j, n j • Real.log ((ℓ j).h z) := by
  have hpos : ∀ j, 0 < (ℓ j).h z := fun j => (ℓ j).pos z hz
  show Real.log (∏ j, (ℓ j).h z ^ n j) = _
  rw [Real.log_prod (fun j _ => (zpow_pos (hpos j) _).ne')]
  simp only [Real.log_zpow, zsmul_eq_mul]

theorem sum_root_fund {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (r : Ψ × Fin N) (f : Ψ × Fin N → ℝ) :
    ∑ a, rootOnFund r a • -∑ k ∈ Finset.Iic a.2, f (a.1, k) = f r := by
  obtain ⟨x0, k0⟩ := r
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x0]
  rotate_left
  · intro x _ hx
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [rootOnFund, hx]
  · intro h
    exact absurd (Finset.mem_univ x0) h
  have hterm : ∀ j : Fin N, rootOnFund (x0, k0) (x0, j) • -∑ k ∈ Finset.Iic j, f (x0, k) =
      (if j = k0 then ∑ k ∈ Finset.Iic j, f (x0, k) else 0) -
        (if (j : ℕ) + 1 = k0 then ∑ k ∈ Finset.Iic j, f (x0, k) else 0) := by
    intro j
    simp only [rootOnFund, if_true]
    split_ifs <;> simp
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases k0 with ⟨k, hk⟩
  cases k with
  | zero =>
    have hsum : ∑ j : Fin N, (if (j : ℕ) + 1 = (0 : ℕ) then ∑ k ∈ Finset.Iic j, f (x0, k) else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg (by omega)
    have hI : Finset.Iic (⟨0, hk⟩ : Fin N) = {⟨0, hk⟩} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    simp only [Fin.val_mk] at *
    rw [hsum, sub_zero, hI, Finset.sum_singleton]
  | succ k' =>
    have hk' : k' < N := by omega
    have hsum : ∑ j : Fin N, (if (j : ℕ) + 1 = k' + 1 then ∑ k ∈ Finset.Iic j, f (x0, k) else 0) =
        ∑ k ∈ Finset.Iic (⟨k', hk'⟩ : Fin N), f (x0, k) := by
      rw [Finset.sum_eq_single ⟨k', hk'⟩]
      · simp
      · intro j _ hj
        rw [if_neg]
        intro hj'
        apply hj
        ext
        simp only [Fin.val_mk]
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hI : Finset.Iic (⟨k' + 1, hk⟩ : Fin N) = insert ⟨k' + 1, hk⟩ (Finset.Iic ⟨k', hk'⟩) := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    have hnot : (⟨k' + 1, hk⟩ : Fin N) ∉ Finset.Iic (⟨k', hk'⟩ : Fin N) := by
      simp [Fin.le_def]
    simp only [Fin.val_mk] at *
    rw [hsum, hI, Finset.sum_insert hnot]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)} {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))}
  {Fx : FixedData Y Sys}

open Classical in

def tieOf (Or : RootOrigin Y S RM Fx) (h₀ : 0 < Sys.t₀) (hvb : Or.𝔐.OmVB)
    (hd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) (hA : AlgOver (Or.Re.comap some)) :
    HodgeTie Y S (Module.finrank ℚ c.F) RM where
  A := Or.𝔐
  Fl := Or.Fl
  e := Or.e
  roots := Or.lines
  sing := Or.sing
  sing_deg := Or.sing_deg
  hodge := Or.hodge
  Sy := Sys.comap some
  Re := Or.Re.comap some
  alg := hA
  ref_deg a := by
    refine (Or.fund_deg a.1 a.2).trans ?_
    show _ = ∑ j, _ • (Or.sing j).a
    rw [sum_fundOnRoot]
    simp only [Or.sing_deg]
  sing_eq a x hx := by
    refine Eq.trans ?_ (Or.fund_sing a.1 a.2 x hx).symm
    exact (log_combLine _ _ (Or.Re.R.mem x x (Or.Re.R.mem_U x)).1).trans (sum_fundOnRoot _ _)
  line_eq := by
    filter_upwards [Ioo_mem_nhdsGT h₀] with t ht r z hz
    refine Real.log_injOn_pos ((RM.x t r).pos z hz.1) (HermLine.pos _ z hz.1) ?_
    rw [log_combLine _ _ hz.1]
    refine Eq.trans (sum_root_fund r fun r' => Real.log ((RM.x t r').h z)).symm (Finset.sum_congr rfl fun a _ => ?_)
    exact congrArg _ (Or.fund_reg a.1 a.2 t ht.1 ht.2.le z hz).symm
  δ_eq := Or.δ_eq
  discr := hd
  ht_vb p hp := (hvb p hp).2

end RootFieldNumerics.Sq
