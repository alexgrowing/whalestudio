import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

section StabNSec

open Matrix
open scoped TensorProduct

def StabLatC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 →
      Formalism.HermitianLatticesTheory.gmap σ ((Y.cs u').lamOf ρ') = (Y.cs u').lamOf ρ'

def StabFlagC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      ∀ j, ∀ x ∈ Xflag (lf D (X.Fu u')) (j + 1), σ x - x ∈ Xflag (lf D (X.Fu u')) j

def StabOrthC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 →
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), σ x - x ∈ Xsp (lf D (X.Fu u'))

theorem stabNC_of (hL : StabLatC) (hF : StabFlagC) (hO : StabOrthC) : StabNC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  exact ⟨⟨hσ, hL D X Y u u' hH ρ' s σ hs hσ hS hk⟩, hF D X Y u u' hH s σ hs hσ hS,
    hO D X Y u u' hH ρ' s σ hs hσ hS hk⟩

theorem lattice_stabilizer_holds : StabLatC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  obtain ⟨M, -, -, h2, h3⟩ := hs
  set a : X.B.I.Gf := ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u' with ha
  have hkK : a⁻¹ * s.2 * a ∈ X.B.I.Kset := hH.1.2.1 _ hk
  have hfm : ∀ x y : X.B.I.Gf, X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := by
    intro x y; simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : ∀ y : (VS D).V, σ y ∈ (Y.cs u').lamOf ρ' ↔ y ∈ (Y.cs u').lamOf ρ' := by
    intro y
    rw [(Y.cs u').lat_eq, (Y.cs u').lat_eq, h3, ← Formalism.L2.SG.Pf.Level.incl_mulVec X, ← h2]
    have e : X.B.I.fmat a⁻¹ *ᵥ (X.B.I.fmat s.2 *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd y)) =
        X.B.I.fmat (a⁻¹ * s.2 * a) *ᵥ (X.B.I.fmat a⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hfm, ← hfm]
      congr 2
      group
    rw [e]
    exact (hkK _).symm
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).2 hx
  · intro hy
    refine Submodule.mem_map.2 ⟨σ.symm y, (key _).1 (by simpa using hy), by simp⟩

def StabOrthDescC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (s : X.B.I.GA)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s.2 ∈ X.NfinU u' →
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), σ x - x ∈ Xsp (lf D (X.Fu u'))

theorem stab_nfin (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK)
    {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u' : D.what₂.Word) (hKL : X.LevelSubgroupNormalized)
    (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (hS : s ∈ Srat X u')
    (hk : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2) :
    s.2 ∈ X.NfinU u' := by
  have hK := Y.hK
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' s hS
  obtain ⟨ν, η, rfl, hνr, hν1, hν2, hη⟩ := Formalism.L2.SG.Pf.ratLevi_holds X u' _ (Subgroup.mem_inf.1 hS).1 h1 h2
  have hηp := Subgroup.mem_prod.1 (Subgroup.mem_inf.1 hη).2
  set hh : Hfin X u' := (Y.cs u').h ρ' with hhh
  have hn' : (hh : X.B.I.Gf)⁻¹ * ν.2 * hh ∈ X.NfinU u' := by
    have := (Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X u' hh⁻¹ ν.2 hν2).1
    simpa using this
  let g2 : Hfin X u' := hh⁻¹ * ⟨η.2, hηp.2⟩ * hh
  have hLD := Formalism.L2.SG.PoincareInHH.Cut.levelDec_of X u' hK (Formalism.L2.SG.Pf.ksetSplit_holds X u')
    (Formalism.L2.SG.Pf.unipotent_in_level X u') _ hn' g2 (by
      have e : (X.xu u')⁻¹ * ((hh : X.B.I.Gf)⁻¹ * ν.2 * hh * (g2 : X.B.I.Gf)) * X.xu u' =
          ((hh : X.B.I.Gf) * X.xu u')⁻¹ * (ν * η).2 * ((hh : X.B.I.Gf) * X.xu u') := by
        simp only [g2, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul]
        group
      rw [e]; exact hk)
  have hη1 : (⟨η, hη⟩ : Gam X u') = 1 := by
    refine hN D X Y u' hKL hh ⟨η, hη⟩ ?_
    show (X.xu u')⁻¹ * ((hh⁻¹ * Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u' ⟨η, hη⟩ * hh : Hfin X u') : X.B.I.Gf) *
      X.xu u' ∈ X.K2
    exact hLD.1
  have hη1' : η = 1 := congrArg Subtype.val hη1
  rw [hη1', mul_one]
  exact hν2

theorem stabOrthC_of (hD : StabOrthDescC)
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabOrthC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  exact hD D X u' s σ hs hσ (stab_nfin hN Y u' hH.1 ρ' s hS hk)

theorem incl_descent (I : Formalism.MainNotions.S.AutInst) [Nontrivial (Af I.F)] (S : Set (Fin I.n → I.E)) (w : Fin I.n → I.E)
    (hw : Formalism.L2.SG.HidaSetting.incl I w ∈
      Submodule.span (I.E ⊗[I.F] Af I.F) (Formalism.L2.SG.HidaSetting.incl I '' S)) :
    w ∈ Submodule.span I.E S := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap I.E (I.E ⊗[I.F] Af I.F)) (by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    exact Algebra.TensorProduct.includeLeft_injective (S := I.F) (algebraMap I.F (Af I.F)).injective h)
  have hgc : ∀ c : I.E, g (Formalism.UG.inclE (F := I.F) (Af I.F) c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (r : I.E ⊗[I.F] Af I.F) (c : I.E), g (r * Formalism.UG.inclE (F := I.F) (Af I.F) c) = c * g r := by
    intro r c
    have e : r * Formalism.UG.inclE (F := I.F) (Af I.F) c = c • r := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul]
  obtain ⟨m, f, t, hsum⟩ := Submodule.mem_span_set'.1 hw
  have ht : ∀ i, ∃ s ∈ S, Formalism.L2.SG.HidaSetting.incl I s = (t i : Formalism.L2.SG.HidaSetting.VA I) := fun i => (t i).2
  choose s hs hst using ht
  have e : w = ∑ i, g (f i) • s i := by
    funext k
    have hk := congrFun hsum k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hst] at hk ⊢
    have hk2 := congrArg g hk
    simp only [Formalism.L2.SG.HidaSetting.incl, map_sum, hgm, hgc] at hk2
    rw [← hk2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))

theorem crd_inj' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {y y' : (VS D).V} (h : X.crd y = X.crd y') : y = y' := by
  apply X.bas.repr.injective
  ext i
  have := congrFun h i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] at this
  exact X.ιE.symm.injective this

theorem crd_descent {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : (VS D).V)
    (hv : X.crd v ∈ Submodule.span X.B.I.E (Set.range X.eR)) :
    v ∈ Submodule.span D.host.E (Set.range X.eX) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun X.B.I.E).1 hv
  have e : v = ∑ a, X.ιE (c a) • X.eX a := by
    apply crd_inj' X
    rw [← hc]
    change _ = Formalism.L2.SG.Pf.Vanish2.crdHom X (∑ a, X.ιE (c a) • X.eX a)
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = X.crd (X.ιE (c a) • X.eX a)
    rw [Formalism.L2.SG.Pf.crd_smul X, RingEquiv.symm_apply_apply]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem orthogonal_stabilizer_descent : StabOrthDescC := by
  intro D X u' s σ hs hσ hn x hx
  obtain ⟨M, -, -, h2, h3⟩ := hs
  have : Nontrivial (Af X.B.I.F) := Formalism.L2.SG.Pf.Level.af_ntriv X.B.I.F
  have hx0 : ∀ a, Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a)) (Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd x)) = 0 := by
    intro a
    rw [Formalism.L2.SG.PoincareInHH.Cut.hA_incl X]
    have hmem : X.eX a ∈ Xsp (lf D (X.Fu u')) := by
      show X.eX a ∈ Submodule.span D.host.E (Set.range (X.Fu u').e)
      rw [X.Fu_e]
      exact Submodule.subset_span ⟨a, rfl⟩
    have h0 : (VS D).hT (X.eX a) x = 0 := (mem_orth_iff _ _).1 hx _ hmem
    have h1 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.crd x) = 0 := by
      apply X.ιE.injective
      rw [map_zero, show X.eR a = X.crd (X.eX a) from rfl, Formalism.L2.SG.PoincareInHH.Cut.hform_crd X]
      exact h0
    rw [h1, map_zero]
  have hmem := hn.2.2 _ hx0
  have e : (X.B.I.fmat s.2 - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd x) =
      Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd (σ x - x)) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h2, Formalism.L2.SG.Pf.Level.incl_mulVec X, ← h3,
      Formalism.L2.SG.Pf.Vanish2.crd_sub' X]
    funext i
    simp [Formalism.L2.SG.HidaSetting.incl]
  rw [e] at hmem
  have hd := incl_descent X.B.I (Set.range X.eR) _ (by rw [← Set.range_comp]; exact hmem)
  show σ x - x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e)
  rw [X.Fu_e]
  exact crd_descent X _ hd

theorem orthogonal_stabilizer_of_neat
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabOrthC :=
  stabOrthC_of orthogonal_stabilizer_descent hN

end StabNSec

end Formalism.L2.SG.Pf.RegroupPf
