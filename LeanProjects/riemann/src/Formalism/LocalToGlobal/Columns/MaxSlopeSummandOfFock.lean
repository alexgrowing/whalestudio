import Mathlib
import Formalism.LocalToGlobal.Columns.MultiFactorialEqTripleProd
import Formalism.LocalToGlobal.Columns.BrpStarLatLattice
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PExtInvMuB
import Formalism.GL3MeanSquares.HookFormulaTorsion.ColumnParametrizationOffDiagonal

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

def TwistDeg (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)),
    0 < n → (∀ τ, Submodule.IsLattice K (M τ)) →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ (I : Submodule (𝓞 K) K) = twId lam M ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)) =
        ∑ τ, ((lam τ).detShift : ℝ) * ((n : ℝ) * (latK K (M τ)).mu)

def ShortBasis (E : Type) [Field E] [NumberField E] (n : ℕ) (Y : Submodule (𝓞 E) (Fin n → E)) (c : ℝ) : Prop :=
  ∃ y : Fin n → Fin n → E, (∀ i, y i ∈ Y) ∧ LinearIndependent E y ∧
    ∀ i, (∑ w : InfinitePlace E, ∑ a, (w (y i a)) ^ 2) / (nPl E : ℝ) ≤ c

section Places

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [IsTotallyComplex E] [IsTotallyComplex K]

theorem mean_over_places_comap (φ : E →+* K) (G : InfinitePlace E → ℝ) :
    (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, G (v.comap φ) = (∑ w, G w) / (nPl E : ℝ) := by
  classical
  let _ : Algebra E K := φ.toAlgebra
  have hc := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.card_fiber E K
  have hn := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.nPl_ext E K
  have hs : ∑ v : InfinitePlace K, G (v.comap φ) = (Module.finrank E K : ℝ) * ∑ w, G w := by
    rw [← Finset.sum_fiberwise Finset.univ (fun v : InfinitePlace K => v.comap φ) (fun v => G (v.comap φ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun v hv => congrArg G (Finset.mem_filter.1 hv).2), Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert hc w
    rfl
  have hK : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hE : (0 : ℝ) < (nPl E : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hn' : (nPl K : ℝ) = (Module.finrank E K : ℝ) * (nPl E : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Module.finrank E K : ℝ) := by
    by_contra h
    have h0 : (Module.finrank E K : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hn'
    exact hK.ne' hn'
  rw [hs, hn']
  field_simp

end Places

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def ShortC (u : Pr.Word) : Prop :=
  ∀ d : (colGSD W Ch u 0).D, ShortBasis X.E (R.N 0) (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh ((R.k : ℝ) ^ 2 * (2 * vC X) ^ 2)

theorem log_four_pow_identity (k v : ℝ) (hk : 0 < k) (hv : 0 < v) : Real.log k + Real.log (k ^ 3 * (2 * v) ^ 2) = Real.log (4 * k ^ 4 * v ^ 2) := by
  rw [← Real.log_mul hk.ne' (by positivity)]
  congr 1
  ring

theorem max_slope_summand_of_fock (hX : X.Ok) (hPr : Pr.Ok) (hv : 0 < vC X) (hS : FockSubNorm) (hC : HwNormBound) (hTw : TwistDeg X.K) (u : Pr.Word)
    (hT : ShortC W Ch u) : MaxSlopeSummandExplicitForm W Ch u := by
  intro d
  have := hX.cplxK
  have := hX.cplxE
  rw [colValH_eq_tenH]
  obtain ⟨y, hyL, hyli, hyb⟩ := hT d
  have hn0 : 0 < R.N 0 := R.N_pos 0
  have hdet : IsUnit (Matrix.of y).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of y)).1 hyli)
  have hdetτ : ∀ τ : X.Tau, IsUnit ((Matrix.of y).map (X.emb τ)).det := fun τ => by
    have : ((Matrix.of y).map (X.emb τ)).det = X.emb τ (Matrix.of y).det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact hdet.map _
  set g : X.Tau → GL (Fin (R.N 0)) X.K := fun τ => Matrix.nonsingInvUnit _ (hdetτ τ) with hgdef
  have hgc : ∀ τ c a, (g τ : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.K) c a = X.emb τ (y c a) := fun τ c a => rfl
  have hg : ∀ τ, ∀ x ∈ EEC W Ch u d τ, ∀ c, ((g τ : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.K) *ᵥ x) c ∈ (1 : Submodule (𝓞 X.K) X.K) := by
    intro τ x hx c
    have h1 := hx (fun a => X.emb τ (y c a)) (Submodule.subset_span ⟨y c, hyL c, rfl⟩)
    have e : ((g τ : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.K) *ᵥ x) c = x ⬝ᵥ fun a => X.emb τ (y c a) := by
      simp only [Matrix.mulVec, dotProduct, hgc]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [e]
    exact h1

  set hh : InfinitePlace X.E → Fin (R.N 0) → ℝ := fun w c => ∑ a, (w (y c a)) ^ 2 with hhdef
  have hhpos : ∀ w c, 0 < hh w c := by
    intro w c
    obtain ⟨a, ha⟩ := Function.ne_iff.1 (hyli.ne_zero c)
    refine Finset.sum_pos' (fun _ _ => by positivity) ⟨a, Finset.mem_univ _, ?_⟩
    have : 0 < w (y c a) := (InfinitePlace.pos_iff).2 ha
    positivity
  have hgN : ∀ v τ, gN X.K g v τ = ∑ c, hh (v.comap (X.emb τ)) c := by
    intro v τ
    unfold gN hsN
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.map_apply, Matrix.transpose_apply, hgc, InfinitePlace.comap_apply, ← InfinitePlace.norm_embedding_eq]
  have hpos : ∀ v τ, 0 < gN X.K g v τ := by
    intro v τ
    rw [hgN]
    exact Finset.sum_pos' (fun c _ => (hhpos _ c).le) ⟨⟨0, hn0⟩, Finset.mem_univ _, hhpos _ _⟩
  have hk : (R.N 0 : ℝ) = (R.k : ℝ) := by rw [brz_N_zero]
  have hk1 : (1 : ℝ) ≤ (R.k : ℝ) := by rw [← kap_cast]; have := (Nat.cast_nonneg (kap R) : (0 : ℝ) ≤ _); linarith
  have hmean : ∀ τ, (1 / (nPl X.K : ℝ)) * ∑ v, Real.log (gN X.K g v τ) ≤ Real.log ((R.k : ℝ) ^ 3 * (2 * vC X) ^ 2) := by
    intro τ
    simp only [hgN]
    rw [mean_over_places_comap X.E X.K (X.emb τ) fun w => Real.log (∑ c, hh w c)]
    let e : InfinitePlace X.E ≃ Fin (nPl X.E) := Fintype.equivFin _
    have hz := Formalism.HermitianLattices.ExplicitEstimates.mean_log_explicit (nPl X.E) (R.N 0) (fun i c => hh (e.symm i) c) (vC X)
      (Fintype.card_pos) hn0 hv (fun i c => hhpos _ c) (fun c => by
        rw [Equiv.sum_comp e.symm (fun w => hh w c), hk]
        exact hyb c)
    rw [Equiv.sum_comp e.symm (fun w => Real.log (∑ c, hh w c)), hk] at hz
    exact hz
  obtain ⟨I, hI0, hI, hN⟩ := hTw X.Tau (R.N 0) (W.lamTrue u 0) (EEC W Ch u d) hn0 (EEC_isLattice W Ch u d)
  have hmain := max_slope_twisted_general X.K hS hC (kap_succ R) (W.lamTrue u 0) (EEC W Ch u d) (EEC_isLattice W Ch u d) g hg hpos I hI0 hI
  have hee := eeSlope W Ch hX hPr u d
  rw [sub_eq_add_neg, hN, ← Finset.sum_add_distrib] at hmain
  refine hmain.trans (Finset.sum_le_sum fun τ _ => ?_)
  have hwp : (0 : ℝ) ≤ (wt (plus (lamZ W u τ)) : ℝ) := by
    unfold wt
    exact_mod_cast Finset.sum_nonneg fun i _ => brz_plus_nonneg _ (lamZ_anti W u τ) i
  have e1 : Real.log ((kap R : ℝ) + 1) + (1 / (nPl X.K : ℝ)) * ∑ v, Real.log (gN X.K g v τ) ≤
      Real.log (4 * (R.k : ℝ) ^ 4 * vC X ^ 2) := by
    rw [← log_four_pow_identity (R.k : ℝ) (vC X) (by linarith) hv, kap_cast]
    linarith [hmean τ]
  have e2 := mul_le_mul_of_nonneg_left e1 hwp
  have e3 : ((W.lamTrue u 0 τ).detShift : ℝ) * ((R.N 0 : ℝ) * (latK X.K (EEC W Ch u d τ)).mu) =
      -((lamZ W u τ (Fin.last (kap R)) : ℝ) * logTC Pr u) := by
    rw [hee τ, det_shift_eq_last_weight (kap_succ R), hk]
    show ((lamZ W u τ (Fin.last (kap R)) : ℤ) : ℝ) * _ = _
    field_simp
  rw [e3]
  have e4 : ((kap R : ℝ) + 1) * (kap R : ℝ) / 2 = (R.k : ℝ) * ((R.k : ℝ) - 1) / 2 := by rw [← kap_cast]; ring
  have e5 : (plus (castW (kap_succ R) (W.lamTrue u 0 τ)) 0 : ℝ) + (kap R : ℝ) + 1 = (plus (lamZ W u τ) 0 : ℝ) + (R.k : ℝ) := by
    rw [← kap_cast]
    show (plus (lamZ W u τ) 0 : ℝ) + (kap R : ℝ) + 1 = _
    ring
  rw [e4, e5]
  have e6 : (wt (plus (castW (kap_succ R) (W.lamTrue u 0 τ))) : ℝ) = (wt (plus (lamZ W u τ)) : ℝ) := rfl
  rw [e6]
  linarith

end Cols

end Formalism.L2.Col
