import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem theta_Z_mem_range_iC {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) (t : A3.fam3.base3.Tup) :
    ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R t).ZHg A3.A.fam.X := hIB.1 t hz
  obtain ⟨x, hx⟩ := GlobalTheory.PrincipalRows.mem_range_toF_full (A3.A.fam.R t) A3.A.fam.X (X.zs.Z t) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ t (X.jR t y)) hx

set_option maxHeartbeats 1000000 in

theorem iC_range_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ t, LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) = ⊤ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F _hOk hC hUp hRT hIB t
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := GlobalTheory.PrincipalRows.theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT t
    (LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t))
    (theta_Z_mem_range_iC A3 (R.toCx3 F) hIB t)
  have hinj : Function.Injective (LinearMap.adjoint ((R.toCx3 F).Θ t)) := by
    show Function.Injective (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.Th t)))
    rw [Tw.adjoint_map]
    intro x y hxy
    exact hUp t hxy
  have hinj2 : Function.Injective ((R.toCx3 F).Θ t ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ t)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    have h0 : LinearMap.adjoint ((R.toCx3 F).Θ t) e = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_left]
      have : (R.toCx3 F).Θ t (LinearMap.adjoint ((R.toCx3 F).Θ t) e) = 0 := he
      rw [this, inner_zero_right]
    exact hinj (h0.trans (map_zero _).symm)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj2
  rw [eq_top_iff]
  intro e _
  obtain ⟨e', rfl⟩ := hsurj e
  exact hmem e'

end GlobalTheory.PrimIn
