import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSize
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSixth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUniformFiniteBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspLiftFiniteSumApproximationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnCusp
variable {D : D7}

open GlobalTheory.Size in

theorem isCuspFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hU' : ∀ w, IsAutFun N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨(hx.aut w).toIsAutFun, hx.cusp w⟩
    | zero => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_zero _, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1 (hy w).1 (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_smul (hx w).1 c, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  suffices H : IsAutFun N.V ((PiTensorProduct.lift U) v) ∧ IsCuspFun N.V ((PiTensorProduct.lift U) v) from H.2
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.RowLift.isAutFun_smul (hU' f).1 r, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

end GlobalTheory.DnCusp

namespace GlobalTheory.DnCusp

theorem isCuspFun_lift_dn_of (s1 : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε) (s2 : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ hint
  obtain ⟨N₁, h1⟩ := s1 hP D hS G₀ Pl0 T A Ks R G hB hG i hi
  obtain ⟨N₂, h2⟩ := s2 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ
  have hdn := (hL D hS G₀ Pl0 T A Ks R G hB hG).dn i hi
  have haut := GlobalTheory.DnLiftAut.isAutFunSm_lift_dn hL hP D hS G₀ Pl0 T A Ks R G hB hG i hi Φ hΦ φ hφ hint
  set L : GA D (G.P i).V → ℂ := fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν with hLdef
  set N := max N₁ N₂
  have key : ∀ n : ℕ, ∃ ψ : GA D (G.P i).V → ℂ, (IsAutFun (G.P i).V ψ ∧ IsCuspFun (G.P i).V ψ) ∧
      GlobalTheory.Size.growthSize (G.P i).V N (ψ - L) ≤ ((n : ENNReal) + 1)⁻¹ := by
    intro n
    set ε : ENNReal := ((n : ENNReal) + 1)⁻¹ / 2 with hε
    have hε0 : 0 < ε := ENNReal.div_pos (ENNReal.inv_ne_zero.2 (by simp)) (by simp)
    obtain ⟨K, F, v, hF, hK⟩ := h2 Φ hΦ ε hε0
    obtain ⟨J, f, p, hf, hJ⟩ := h1 K F v hF Φ hΦ ε hε0
    have hF' : ∀ j ∈ J, ∀ k ∈ K, ∃ F' ∈ (G.P i).Cusp R.θ, ∀ h,
        (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) = F' ((G.dn i).It (p j) (v k)) h := by
      intro j hj k hk
      obtain ⟨F', hF'm, hF'e⟩ := hdn (f j) (hf j hj) (F k) (hF k hk)
      exact ⟨F', hF'm, fun h => (hF'e (p j) (v k) h).2⟩
    refine ⟨fun h => ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν, ?_, ?_⟩
    · have hterm : ∀ j ∈ J, ∀ k ∈ K, IsAutFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) ∧
          IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) := by
        intro j hj k hk
        obtain ⟨F', hF'm, hF'e⟩ := hF' j hj k hk
        have e : (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) = F' ((G.dn i).It (p j) (v k)) := funext hF'e
        rw [e]
        exact ⟨GlobalTheory.RowLift.isAutFun_of_mem_cusp _ _ hF'm _, isCuspFun_of_mem_cusp _ _ hF'm _⟩
      have h0 : IsCuspFun (G.P i).V (0 : GA D (G.P i).V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
      have hsum : ∀ (s : Finset ℕ) (u : ℕ → GA D (G.P i).V → ℂ), (∀ a ∈ s, IsAutFun (G.P i).V (u a) ∧ IsCuspFun (G.P i).V (u a)) →
          IsAutFun (G.P i).V (fun h => ∑ a ∈ s, u a h) ∧ IsCuspFun (G.P i).V (fun h => ∑ a ∈ s, u a h) := by
        intro s u hu
        have e : (fun h => ∑ a ∈ s, u a h) = ∑ a ∈ s, u a := by funext h; simp [Finset.sum_apply]
        rw [e]
        clear e
        induction s using Finset.induction_on with
        | empty => simpa using ⟨GlobalTheory.RowLift.isAutFun_zero _, h0⟩
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          have hA := hu a (Finset.mem_insert_self a s)
          have hB := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
          exact ⟨GlobalTheory.RowLift.isAutFun_add hA.1 hB.1, GlobalTheory.MultMem.isCuspFun_add hA.1 hB.1 hA.2 hB.2⟩
      exact hsum J _ fun j hj => hsum K _ fun k hk => hterm j hj k hk
    · set M : GA D (G.P i).V → ℂ := fun h => ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν
      set Ψ : GA D (G.P i).V → ℂ := fun h => ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν
      have e : Ψ - L = -((L - M) + (M - Ψ)) := by abel
      have e2 : GlobalTheory.Size.growthSize (G.P i).V N (Ψ - L) = GlobalTheory.Size.growthSize (G.P i).V N ((L - M) + (M - Ψ)) := by
        rw [e]; unfold GlobalTheory.Size.growthSize; congr 1; funext g; rw [Pi.neg_apply, norm_neg]
      rw [e2]
      refine (GlobalTheory.Size.growthSize_add_le).trans ?_
      have a1 : GlobalTheory.Size.growthSize (G.P i).V N (L - M) ≤ ε :=
        ((GlobalTheory.Size.growthSize_anti (le_max_right N₁ N₂)).trans hK.le)
      have a2 : GlobalTheory.Size.growthSize (G.P i).V N (M - Ψ) ≤ ε :=
        ((GlobalTheory.Size.growthSize_anti (le_max_left N₁ N₂)).trans hJ.le)
      refine (add_le_add a1 a2).trans (le_of_eq ?_)
      rw [hε, ENNReal.add_halves]
  choose ψ hψ hψb using key
  have ht : Filter.Tendsto (fun n => GlobalTheory.Size.growthSize (G.P i).V N (ψ n - L)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ENNReal) + 1)⁻¹) Filter.atTop (nhds 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => bot_le) hψb
  exact GlobalTheory.CuspLimit.isCuspFun_of_tendsto D (G.P i).V N ψ L
    (fun n => ⟨(hψ n).1.cont, (hψ n).1.left, (hψ n).2⟩) haut.cont haut.left ht

theorem isCuspFun_lift_dn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) :=
  isCuspFun_lift_dn_of GlobalTheory.T.theta_lift_uniform_finite_bound GlobalTheory.T.theta_lift_cusp_degree_bound

end GlobalTheory.DnCusp

end
