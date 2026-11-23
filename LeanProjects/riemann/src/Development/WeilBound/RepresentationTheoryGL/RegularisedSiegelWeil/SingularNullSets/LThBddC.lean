import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D W.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem eval_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → schwartzA θ W.rank n) (X : Mx D W.rank n) :
    (∑ i ∈ s, c i • f i).1 X = ∑ i ∈ s, c i * (f i).1 X := by
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem omega_nb (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n)
    (Φ : schwartzA θ W.rank n) (X : Mx D W.rank n) : (ω (nb x) Φ).1 X = pch ψ x.1 (ip W X X) * Φ.1 X := by
  exact hω.unip (nb x) x.1 (hnb x) Φ X

theorem omega_cut (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (X : Mx D W.rank n) :
    (ω g Ψ').1 X = cutF ψ C (ip W X X) * (ω g Ψ).1 X := by
  subst hΨ'
  simp only [map_sum, map_smul]
  rw [eval_sum, show cutF ψ C (ip W X X) = ∑ x ∈ C.s, C.co x * pch ψ x.1 (ip W X X) from rfl,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hcomm : nb x * g = g * nb x :=
    PositivityTheory.Rg.Rsw.L.LThBdd.commute_of_atPts
      (PositivityTheory.Rg.Rsw.L.LThBdd.nb_mem_atPts hnb x (C.inf x hx) (C.off x hx)) hg
  rw [← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply,
    omega_nb hω hnb x, mul_assoc]

theorem pch_eq_one (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (Ψ : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (X : Mx D W.rank n) (hX : (ω g Ψ).1 X ≠ 0)
    (o : hermA D n) (ho : IntAt v o) : pch ψ o.1 (ip W X X) = 1 := by
  have hk := PositivityTheory.Rg.Rsw.L.LThBdd.nb_mem_KAt hnb o ho
  have hfix : ω (nb o) (ω g Ψ) = ω g Ψ := by
    rw [← Module.End.mul_apply, ← map_mul,
      PositivityTheory.Rg.Rsw.L.LThBdd.commute_of_atPts (Subgroup.mem_inf.mp hk).2 hg, map_mul,
      Module.End.mul_apply, hΨ _ hk]
  have h := omega_nb hω hnb o (ω g Ψ) X
  rw [hfix] at h
  exact mul_right_cancel₀ hX (h.symm.trans (one_mul _).symm)

theorem inner_rat' (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) :
    GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) = rat (gramQ W ξ) := by
  rw [show GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) =
      GlobalTheory.MixModel.adj (rat ξ) * (GlobalTheory.MixModel.rat (Formalism.BasicNotions.HSpace.gram W) * rat ξ) from rfl,
    ← GlobalTheory.MixModel.rat_conjTranspose, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul,
    ← GlobalTheory.MixModel.cT_sig]
  rfl

theorem ip_mt_rat (h : GA D W) (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ)) = rat (gramQ W ξ) := by
  calc ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))
      = GlobalTheory.MixModel.adj (mt W h⁻¹ * rat ξ) * (GlobalTheory.MixModel.gA W * (mt W h⁻¹ * rat ξ)) := rfl
    _ = GlobalTheory.MixModel.adj (rat ξ : Mx D W.rank n) *
          ((GlobalTheory.MixModel.adj (mt W h⁻¹) * (GlobalTheory.MixModel.gA W * mt W h⁻¹)) * rat ξ) := by
        rw [GlobalTheory.MixModel.adj_mul]
        simp only [Matrix.mul_assoc]
    _ = GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) := by
        rw [GlobalTheory.MixModel.mt_unitary]
        rfl
    _ = rat (gramQ W ξ) := inner_rat' ξ

theorem rank_gramQ_le (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) : (gramQ W ξ).rank ≤ ξ.rank := by
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _)

theorem term_zero (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n} (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1)
    (h : GA D W) (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) (hξ : ξ.rank ≠ W.rank) :
    (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) = 0 := by
  rw [omega_cut hω hnb C Ψ Ψ' hΨ' hg, ip_mt_rat]
  by_cases h0 : (ω g Ψ).1 (mm (mt W h⁻¹) (rat ξ)) = 0
  · rw [h0, mul_zero]
  · have hq : gramQ W ξ = ξᴴ * (Formalism.BasicNotions.HSpace.gram W * ξ) := by
      rw [← GlobalTheory.MixModel.cT_sig]
      rfl
    have hherm : ((gramQ W ξ).map ⇑(D.sp.cm.sig)).transpose = gramQ W ξ := by
      change Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (gramQ W ξ) = gramQ W ξ
      rw [GlobalTheory.MixModel.cT_sig, hq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose, Matrix.mul_assoc]
    have hlt : (gramQ W ξ).rank < W.rank :=
      (rank_gramQ_le ξ).trans_lt (lt_of_le_of_ne (Matrix.rank_le_height ξ) hξ)
    have hcut := hC (⟨gramQ W ξ, hherm⟩ : PositivityTheory.GramSchwartzFunctions.HermE D n) hlt (fun o ho => by
      have := pch_eq_one hω hnb Ψ hΨ hg _ h0 o ho
      rwa [ip_mt_rat] at this)
    rw [show cutF ψ C (rat (gramQ W ξ)) = 0 from hcut, zero_mul]

theorem theta_nb (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) (x : hermA D n) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (h : GA D W) :
    theta ω Ψ' (nb x * g) h =
      ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
        pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) * (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1)) := by
  have hfun : ∀ ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      ((ω (nb x * g)) Ψ').1 (mm (mt W h⁻¹) (rat ξ)) =
        pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
          (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := by
    intro ξ
    rw [map_mul, Module.End.mul_apply]
    exact omega_nb hω hnb x _ _
  have hsub : Function.support (fun ξ : Matrix (Fin W.rank) (Fin n) D.host.E =>
      pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
        (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ))) ⊆ {y | y.rank = W.rank} := by
    intro ξ hξ
    by_contra hne
    apply hξ
    show _ * _ = 0
    rw [term_zero hω hnb C hC Ψ Ψ' hΨ hΨ' hg h ξ hne, mul_zero]
  calc theta ω Ψ' (nb x * g) h
      = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, ((ω (nb x * g)) Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := rfl
    _ = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
          pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
            (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := tsum_congr hfun
    _ = _ := (tsum_subtype_eq_of_support_subset hsub).symm

theorem fix_open {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) (Ψ Ψ' : schwartzA θ W.rank n)
    (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ) (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {k : G D n}
    (hk : k ∈ Ucut nb v C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) : ω k Ψ' = Ψ' := by
  subst hΨ'
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hc := PositivityTheory.Rg.Rsw.L.LThBdd.conj_mem_KAt hnb C hk hkv hx
  congr 1
  calc ω k (ω (nb x) Ψ) = ω (nb x * ((nb x)⁻¹ * k * nb x)) Ψ := by
        rw [show nb x * ((nb x)⁻¹ * k * nb x) = k * nb x by group, map_mul, Module.End.mul_apply]
    _ = ω (nb x) (ω ((nb x)⁻¹ * k * nb x) Ψ) := by rw [map_mul, Module.End.mul_apply]
    _ = ω (nb x) Ψ := by rw [hΨ _ hc]

end PositivityTheory.Rg.Rsw.L.LThBdd

end
