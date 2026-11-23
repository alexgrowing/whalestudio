import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mean4O.MetricSwap

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

theorem comp_swap_eq_cons {e : ℕ} (i : Fin (e + 1)) (W : Type) (x : Fin (e + 1) → W) (a : W) (hxa : x i = a) :
    x ∘ Equiv.swap 0 i = Fin.cons a (fun k => x (Equiv.swap 0 i k.succ)) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [hxa]
  · simp

theorem num_piece_eq {e : ℕ} {M : Man e} (K K' : Calc M) (v : K.V) (v' : K'.V) (g : M.Fun) (hg : M.Smooth g)
    (hv : ∀ σ, LeviEq (M.A σ) (K.c1 v σ) (K'.c1 v' σ)) (S : Finset (Fin (e + 1))) (i : Fin (e + 1)) (hi : i ∈ S) :
    K.num (S.piecewise (fun _ => K.ar g) (fun _ => v)) = K'.num (S.piecewise (fun _ => K'.ar g) (fun _ => v')) := by
  rw [← K.symm _ (Equiv.swap 0 i), ← K'.symm _ (Equiv.swap 0 i),
    comp_swap_eq_cons i _ _ (K.ar g) (Finset.piecewise_eq_of_mem _ _ _ hi),
    comp_swap_eq_cons i _ _ (K'.ar g) (Finset.piecewise_eq_of_mem _ _ _ hi), K.num_ar g hg, K'.num_ar g hg]
  unfold Man.int
  refine congrArg (M.κ * ·) (Finset.sum_congr rfl fun σ _ => ?_)
  refine (GlobalTheory.LeviOnly.mInt_eq_of_leviEq _ _ (M.A σ) _ _ (g σ) (fun k => K.firstChern_isPotential _ σ) (fun k => K'.firstChern_isPotential _ σ) ?_).1
  intro k j y hy w
  by_cases hk : Equiv.swap 0 i k.succ ∈ S
  · rw [Finset.piecewise_eq_of_mem _ _ _ hk, Finset.piecewise_eq_of_mem _ _ _ hk,
      K.c1_ar g hg σ j y hy w, K'.c1_ar g hg σ j y hy w]
  · rw [Finset.piecewise_eq_of_notMem _ _ _ hk, Finset.piecewise_eq_of_notMem _ _ _ hk]
    exact hv σ j y hy w

theorem top_add_sub {e : ℕ} {M : Man e} (K K' : Calc M) (v : K.V) (v' : K'.V) (g : M.Fun) (hg : M.Smooth g)
    (hv : ∀ σ, LeviEq (M.A σ) (K.c1 v σ) (K'.c1 v' σ)) :
    K.top (v + K.ar g) - K.top v = K'.top (v' + K'.ar g) - K'.top v' := by
  unfold Calc.top
  have e1 : (fun _ : Fin (e + 1) => v + K.ar g) = (fun _ => K.ar g) + (fun _ => v) := by
    funext k; exact add_comm _ _
  have e2 : (fun _ : Fin (e + 1) => v' + K'.ar g) = (fun _ => K'.ar g) + (fun _ => v') := by
    funext k; exact add_comm _ _
  rw [e1, e2, K.num.map_add_univ, K'.num.map_add_univ,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ ∅), ← Finset.add_sum_erase _ _ (Finset.mem_univ ∅),
    Finset.piecewise_empty, Finset.piecewise_empty]
  have hs : ∑ S ∈ (Finset.univ : Finset (Finset (Fin (e + 1)))).erase ∅, K.num (S.piecewise (fun _ => K.ar g) (fun _ => v)) =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin (e + 1)))).erase ∅, K'.num (S.piecewise (fun _ => K'.ar g) (fun _ => v')) := by
    refine Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS)
    exact num_piece_eq K K' v v' g hg hv S i hi
  rw [hs]
  ring

end GlobalTheory.Mean4O.MetricSwap

namespace GlobalTheory.Mean4O

theorem fR_sub_eq_top_sub : ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau) (T : Real0 Y) (B B' : ℝ) (c : Y.Comp) (u : GlobalTheory.Mean4.Wt Y) (s R : ℝ), (T.M c).Smooth ((T.F c).phR R u) → T.fR B c u s R - T.fR B' c u s R = (T.K B c).top (T.L B c u + s • T.a B c) - (T.K B' c).top (T.L B' c u + s • T.a B' c) := by
  intro D Y T B B' c u s R hg
  have hv : ∀ σ, LeviEq ((T.M c).A σ) ((T.K B c).c1 (T.L B c u + s • T.a B c) σ)
      ((T.K B' c).c1 (T.L B' c u + s • T.a B' c) σ) := by
    intro σ j y hy w
    rw [(T.K B c).isOneCochain_add _ _ σ j y hy w,
      Deg.leviAt_add _ ((T.K B c).firstChern_isPotential _ σ) ((T.K B c).firstChern_isPotential _ σ) j hy,
      (T.K B' c).isOneCochain_add _ _ σ j y hy w,
      Deg.leviAt_add _ ((T.K B' c).firstChern_isPotential _ σ) ((T.K B' c).firstChern_isPotential _ σ) j hy,
      T.c1_L B c u σ j y hy w, T.c1_L B' c u σ j y hy w,
      (T.K B c).firstChern_smul_leviEq _ _ σ j y hy w, (T.K B' c).firstChern_smul_leviEq _ _ σ j y hy w, Deg.leviAt_rsmul, Deg.leviAt_rsmul,
      T.firstChern_leviEq_constant B c σ j y hy w, T.firstChern_leviEq_constant B' c σ j y hy w]
  have key := MetricSwap.top_add_sub (T.K B c) (T.K B' c) _ _ _ hg hv
  unfold Real0.fR
  linarith

end GlobalTheory.Mean4O
