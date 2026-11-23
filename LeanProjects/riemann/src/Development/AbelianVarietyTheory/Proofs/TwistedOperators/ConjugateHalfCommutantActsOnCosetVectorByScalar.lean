import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneLeMulOfOneLt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodinger
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosScalar

variable {D : D7}

theorem smul_mem_hatMx_of_fr {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (Lev.EAf D)} {β' : GL (Fin m) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {z : Mx D m n}
    (hz : ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F 𝔪, s.1 = GlobalTheory.FunObj.Comparison₂.fr β' β (z.map (toEAf D)) i j) :
    a • z ∈ hatMx (𝔪 • homLat Λ Λ') := by
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪]
  refine ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul, map_mul, ha0, zero_mul], fun i j => ?_⟩
  obtain ⟨s, hs, hse⟩ := hz i j
  refine ⟨⟨toEAf D a, ha⟩ * s, Ideal.mul_mem_left _ _ hs, ?_⟩
  have e2 : GlobalTheory.FunObj.Comparison₂.fr β' β ((a • z).map (toEAf D)) i j = toEAf D a * GlobalTheory.FunObj.Comparison₂.fr β' β (z.map (toEAf D)) i j := by
    simp only [GlobalTheory.FunObj.Comparison₂.fr, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  exact (congrArg (toEAf D a * ·) hse).trans e2.symm

theorem exists_frames {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsLattice D.host.E Λ)
    (hΛ' : Submodule.IsLattice D.host.E Λ') :
    ∃ β : GL (Fin n) (Lev.EAf D), ∃ β' : GL (Fin m) (Lev.EAf D), Formalism.L2.DIV.IsFrame β Λ ∧ Formalism.L2.DIV.IsFrame β' Λ' := by
  obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ hΛ.fg hΛ.span_eq_top
  obtain ⟨β', hβ'⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ' hΛ'.fg hΛ'.span_eq_top
  exact ⟨β, β', hβ, hβ'⟩

theorem smul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsLattice D.host.E Λ)
    (hΛ' : Submodule.IsLattice D.host.E Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {z : Mx D m n}
    (hz : z ∈ hatMx (𝔪 • homLat Λ Λ')) : a • z ∈ hatMx (𝔪 • homLat Λ Λ') := by
  obtain ⟨β, β', hβ, hβ'⟩ := exists_frames hΛ hΛ'
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪] at hz
  exact smul_mem_hatMx_of_fr hβ hβ' 𝔪 ha0 ha hz.2

theorem smul_map_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsLattice D.host.E Λ)
    (hΛ' : Submodule.IsLattice D.host.E Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {y : Matrix (Fin m) (Fin n) D.host.E} (hy : y ∈ 𝔪 • homLat Λ Λ') :
    a • y.map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  obtain ⟨β, β', hβ, hβ'⟩ := exists_frames hΛ hΛ'
  exact smul_mem_hatMx_of_fr hβ hβ' 𝔪 ha0 ha (GlobalTheory.FunObj.Comparison₂.fr_mem_idS hβ hβ' hy)

theorem hatMx_smul_le {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (𝔪 : Ideal (𝓞 D.host.E)) :
    hatMx (𝔪 • homLat Λ Λ') ≤ hatMx (homLat Λ Λ') :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, x, hx, e⟩ => ⟨α, hα, x, Submodule.smul_le_right hx, e⟩

theorem sub_mem_of_cosSet {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsLattice D.host.E Λ)
    (hΛ' : Submodule.IsLattice D.host.E Λ') {𝔪 : Ideal (𝓞 D.host.E)} {e : AE D}
    (he0 : infPart D e = 0) (he : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {κ : Cos Λ Λ' 𝔪}
    {t t' : Mx D m n} (ht : t ∈ cosSet e κ) (ht' : t' ∈ cosSet e κ) : t - t' ∈ hatMx (𝔪 • homLat Λ Λ') := by
  obtain ⟨-, x₀, hx₀, hd⟩ := ht
  obtain ⟨-, x₁, hx₁, hd'⟩ := ht'
  have hy : x₀.1 - x₁.1 ∈ 𝔪 • homLat Λ Λ' := GlobalTheory.FunObj.Comparison₂.sub_mem_of_mk_eq (hx₀.trans hx₁.symm)
  have e1 : t - t' = (t - e • (↑x₀ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) -
      (t' - e • (↑x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) + e • (x₀.1 - x₁.1).map (incA D) := by
    rw [Matrix.map_sub _ (map_sub (incA D)), smul_sub]; abel
  rw [e1]
  exact add_mem (sub_mem hd hd') (smul_map_mem_hatMx hΛ hΛ' 𝔪 he0 he hy)

end GlobalTheory.CosScalar

set_option maxHeartbeats 2000000 in
open GlobalTheory.CosScalar in

theorem GlobalTheory.CosScalar.conjHalf_heisO_cosVec_smul : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → (∀ κ, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd e κ) (W.cosVec i κ)) → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∀ κ, ∃ c : ℂ, heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) (W.cosVec i κ) = c • W.cosVec i κ := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he hT w hw hinf κ
  have hsd := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hprops := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0 (fun _ => 0) he
  have he0 : infPart D e = 0 := hprops.1
  have heint := hprops.2.1
  obtain ⟨⟨es, hes, hesum⟩, -⟩ := id he
  have hee : e * e = e := by
    conv_lhs => rw [hesum, Finset.sum_mul]
    rw [hesum]
    exact Finset.sum_congr rfl fun P hP => GlobalTheory.IdemSumLoc.idem_mul_sum hes (hesum ▸ he.2) hP

  have hkey : ∀ u : WO (G.pS (.chi i 0)) (G.pT (.chi i 0)), IsHalf e u →
      u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) →
      W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w u) = 1 := by
    intro u hu hm
    have hlat : u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
        fun _ => True :=
      GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd.1 he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hQ hL G) hu (hatMx_smul_le _ _ _ hm)
    have hsplit : u = ∑ P ∈ G.pl.W0, es P • u := by
      rw [← Finset.sum_smul, ← hesum]
      ext a b
      rw [Matrix.smul_apply, smul_eq_mul, hu a b]
    have hsum : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (∑ P ∈ G.pl.W0, es P • u) =
        ∑ P ∈ G.pl.W0, symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (es P • u) :=
      map_sum (AddMonoidHom.mk' (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w)
        (GlobalTheory.Core.Rk.ThetaOf.symplO_add_right _ _ w)) _ _
    rw [hsplit, hsum]
    refine Finset.sum_induction _ (fun x => W.ψ x = 1) (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, one_mul])
      (AddChar.map_zero_eq_one _) fun P hP => ?_
    have hsp : IsSplitIdem D (es P) := (hes P hP).1
    have hPsum : IsIdemSum (es P) {P} :=
      ⟨⟨es, fun Q hQ => by rw [Finset.mem_singleton.1 hQ]; exact hes P hP, by rw [Finset.sum_singleton]⟩, hsp.2.1⟩
    have hPp := GlobalTheory.IdemSumIdeal.isIdemSum_props (es P) {P} (fun _ => 0) hPsum
    refine hw.2 (es P) hsp (es P • u) ⟨GlobalTheory.CosetRow.smul_mem_latO_idem _ _ hsp.1 hlat, fun e' he' => ?_⟩ fun a b => ?_
    · rw [smul_smul]
      have hp' := GlobalTheory.IdemSumIdeal.isIdemSum_props e' G.pl.W0 (fun _ => 0) he'
      exact smul_mem_hatMx hsd.1.1 hsd.2.1 _ (by rw [map_mul, hp'.1, zero_mul])
        (by rw [map_mul]; exact mul_mem hp'.2.1 hPp.2.1) hm
    · show es P * (es P * u a b) = es P * u a b
      rw [← mul_assoc, hsp.1]
  have hyH : IsHalf (cA D e) (cA D e • w) := fun a b => by
    show cA D e * (cA D e * w a b) = cA D e * w a b
    rw [← mul_assoc, ← map_mul, hee]
  have hconst : ∀ t ∈ cosSet e κ, ∀ t' ∈ cosSet e κ,
      W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t (cA D e • w)) =
        W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t' (cA D e • w)) := by
    intro t ht t' ht'
    have hu : IsHalf e (t - t') := fun a b => by
      show e * (t a b - t' a b) = t a b - t' a b
      rw [mul_sub, ht.1 a b, ht'.1 a b]
    have hm := sub_mem_of_cosSet hsd.1.1 hsd.2.1 he0 heint ht ht'
    have h1 : W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (t - t') (cA D e • w)) = 1 := by
      rw [GlobalTheory.BigDat.symplO_cA_smul, show e • (t - t') = t - t' from Matrix.ext fun a b => hu a b,
        GlobalTheory.Asc.psi_symplO_swap]
      exact hkey _ hu hm
    have e1 : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t (cA D e • w) =
        symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (t - t') (cA D e • w) +
          symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t' (cA D e • w) := by
      rw [← GlobalTheory.Core.Rk.ThetaOf.symplO_add_left, sub_add_cancel]
    rw [e1, AddChar.map_add_eq_mul, h1, one_mul]
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hT κ
  have hcv : W.cosVec i κ = Tm (cosInd e κ) := hall Tm hTm
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd hsd.1 hsd.2 (G.pl.modul_ne_bot sc) hee he0 κ
  have hmod := hTm.modul (cosInd e κ) hSB (cA D e • w) hyH
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (fun t => W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t (cA D e • w)) * cosInd e κ t) =
      c • cosInd e κ := by
    by_cases hne : (cosSet e κ).Nonempty
    · obtain ⟨t₀, ht₀⟩ := hne
      refine ⟨W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t₀ (cA D e • w)), funext fun t => ?_⟩
      by_cases ht : t ∈ cosSet e κ
      · have h1 : cosInd e κ t = 1 := by simp [cosInd, ht]
        rw [Pi.smul_apply, h1, hconst t ht t₀ ht₀, smul_eq_mul]
      · have h0 : cosInd e κ t = 0 := by simp [cosInd, ht]
        rw [Pi.smul_apply, h0, mul_zero, smul_zero]
    · refine ⟨0, funext fun t => ?_⟩
      have ht : t ∉ cosSet e κ := fun h => hne ⟨t, h⟩
      have h0 : cosInd e κ t = 0 := by simp [cosInd, ht]
      rw [Pi.smul_apply, h0, mul_zero, smul_zero]
  exact ⟨c, by rw [hcv, ← hmod, hc, map_smul]⟩
