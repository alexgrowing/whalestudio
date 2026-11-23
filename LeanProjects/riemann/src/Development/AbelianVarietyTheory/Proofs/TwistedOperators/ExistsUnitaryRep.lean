import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThLeSpanGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModel
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RangeAdjointRat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.RowsPosRed

theorem exists_unitary_rep {K G V H E : Type} [Field K] [StarRing K] [Group G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup E] [Module ℂ E] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    {ι : Type} (b : Module.Basis ι K V) (hli : LinearIndependent ℂ fun k => j (b k))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hiso : ∀ x y, ⟪j x, j y⟫_ℂ = σ (h x y)) (r : Representation K G V) (hr : ∀ g x y, h (r g x) (r g y) = h x y)
    (Θ : H →ₗ[ℂ] E) (π : Representation ℂ G E) (hΘ : ∀ g z, Θ (j (r g z)) = π g (Θ (j z))) :
    ∃ ρ : Representation ℂ G H, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, Θ (ρ g y) = π g (Θ y) := by
  let B : Module.Basis ι ℂ H := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = j (b k) := fun k => Module.Basis.mk_apply hli hsp.ge k
  let f : G → Module.End ℂ H := fun g => B.constr ℂ fun k => j (r g (b k))
  have hf : ∀ g z, f g (j z) = j (r g z) := by
    intro g z
    have : (f g).comp j = j.comp (r g) := b.ext fun k => by
      show f g (j (b k)) = j (r g (b k))
      rw [← hB]
      exact B.constr_basis ℂ _ k
    exact LinearMap.congr_fun this z
  let ρ : Representation ℂ G H :=
    { toFun := f
      map_one' := B.ext fun k => by
        show f 1 (B k) = B k
        rw [hB, hf, map_one, Module.End.one_apply]
      map_mul' := fun g g' => B.ext fun k => by
        show f (g * g') (B k) = f g (f g' (B k))
        rw [hB, hf, hf, hf, map_mul, Module.End.mul_apply] }
  have hρ : ∀ g z, ρ g (j z) = j (r g z) := hf
  have hin : ∀ g y y', ⟪ρ g y, ρ g y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
    intro g
    have h1 : ∀ k y', ⟪ρ g (B k), ρ g y'⟫_ℂ = ⟪B k, y'⟫_ℂ := by
      intro k
      have : (innerₛₗ ℂ (ρ g (B k))).comp (ρ g) = innerₛₗ ℂ (B k) := B.ext fun l => by
        show ⟪ρ g (B k), ρ g (B l)⟫_ℂ = ⟪B k, B l⟫_ℂ
        rw [hB, hB, hρ, hρ, hiso, hiso, hr]
      exact fun y' => LinearMap.congr_fun this y'
    intro y y'
    have : (innerₛₗ ℂ (ρ g y)).comp (ρ g) = innerₛₗ ℂ y := B.ext fun l => by
      show ⟪ρ g y, ρ g (B l)⟫_ℂ = ⟪y, B l⟫_ℂ
      rw [← inner_conj_symm, h1, inner_conj_symm]
    exact LinearMap.congr_fun this y'
  refine ⟨ρ, fun g z => (hρ g z).symm, fun g y => ?_, fun g => ?_⟩
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin]
  · have : Θ.comp (ρ g) = (π g).comp Θ := B.ext fun k => by
      show Θ (ρ g (B k)) = π g (Θ (B k))
      rw [hB, hρ, hΘ]
    exact fun y => LinearMap.congr_fun this y

end GlobalTheory.RowsPosRed

namespace GlobalTheory.RowsPosRed

open Formalism.IndefR.Cx.CxData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_idem_gEx (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) (x : (R.toCx3 F).EE) :
    ∑ g, A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x = x := by
  have h := GlobalTheory.AdjGood.proj_rows_core hC (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)
  have e : ∀ g, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
      (A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x) =
      D.what₂.embLL ((idemOf A3.A.X).coeff g) • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x) := by
    intro g
    have hc : cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) =
        D.what₂.embLL ((idemOf A3.A.X).coeff g) := by
      rw [R.emb0, cj_cj]
    exact congrArg (fun z : ℂ => z • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)) hc
  exact (Finset.sum_congr rfl fun g _ => e g).trans h

theorem range_le_span_rat {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    (X : CxData A) (cv : CrdV A) (hK : X.KFormR) (hJ : X.JIsoR cv) (hT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) :
    LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤
      Submodule.span ℂ (X.jR t '' {z | X.jR t z ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))}) := by
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  exact (Formalism.IndefR.Rat.range_adjoint_rat _ (X.jR t) (cv.hR t) (bR t) (hK t).1 (hK t).2 (hJ t) (X.Θ t) ψ hψ
    (fun i x => hr t i x)).ge

theorem exists_rho (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hM : R.toRealDat.IsModels)
    (hGE : R.PGEquiv F) :
    ∃ ρ : Representation ℂ G ((R.toCx3 F).FC A3.A.fam.μ0),
      (∀ g z, (R.toCx3 F).jR A3.A.fam.μ0 ((A3.A.fam.R A3.A.fam.μ0).r g z) = ρ g ((R.toCx3 F).jR A3.A.fam.μ0 z)) ∧
      (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, (R.toCx3 F).Θ A3.A.fam.μ0 (ρ g y) = R.gEx F g ((R.toCx3 F).Θ A3.A.fam.μ0 y) := by
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hM
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hM
  exact exists_unitary_rep (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (H := (R.toCx3 F).FC A3.A.fam.μ0)
    ((R.toCx3 F).jR A3.A.fam.μ0) (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (hKR A3.A.fam.μ0).1
    (hKR A3.A.fam.μ0).2 (F.cv.hR A3.A.fam.μ0) (hJR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r
    (fun g x y => (hOk.ok2.what₂ A3.A.fam.μ0).act.unitary g x y) ((R.toCx3 F).Θ A3.A.fam.μ0) (R.gEx F)
    (fun g z => hGE.1 A3.A.fam.μ0 g z)

theorem exists_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hM : R.toRealDat.IsModels) (hN : RowsNe R.toRealDat F.lv2)
    (b : Bool) : ∃ u : (R.toCx3 F).EE, u ≠ 0 ∧ u ∈ (R.toCx3 F).EEl b := by
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 (hN b)
  have hT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R.toRealDat _ hU
  obtain ⟨y, rfl⟩ : U ∈ LinearMap.range R.HE.e := hM.HE.2.1 ▸ hT
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) y, fun h0 => hU0 ?_, hU⟩
  have : y = 0 := h0
  rw [this, map_zero]

omit [Fintype G] in

theorem tw_eq_zero {s : Bool} {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (f : E →ₗ[ℂ] E')
    (hf : Function.Injective (LinearMap.adjoint f)) (v : Tw s E') (h1 : ∀ y : Tw s E, ⟪Tw.map s f y, v⟫_ℂ = 0) : v = 0 := by
  have h5 : LinearMap.adjoint f (Tw.out v) = 0 := by
    refine ext_inner_left ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    have h3 : cj s ⟪f y, Tw.out v⟫_ℂ = 0 := h1 (Tw.mk s y)
    have h4 := congrArg (cj s) h3
    rwa [cj_cj, map_zero] at h4
  exact hf (h5.trans (map_zero _).symm)

theorem surj_of_upInj (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hUp : UpInj R.toRealDat) (x : (R.toCx3 F).EE) :
    ∃ u, (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u) = x := by
  have hinj : ∀ v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v = 0 → v = 0 := by
    intro v hv
    have h1 : ∀ y : (R.toCx3 F).FC A3.A.fam.μ0, ⟪(R.toCx3 F).Θ A3.A.fam.μ0 y, v⟫_ℂ = 0 := fun y => by
      rw [← LinearMap.adjoint_inner_right, hv, inner_zero_right]
    exact tw_eq_zero (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.fam.μ0) (hUp A3.A.fam.μ0) v h1
  have h2 : Function.Injective ((R.toCx3 F).Θ A3.A.fam.μ0 ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h3 : ⟪LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      rw [LinearMap.comp_apply] at hv
      rw [hv, inner_zero_right]
    exact hinj v (inner_self_eq_zero.1 h3)
  exact LinearMap.injective_iff_surjective.1 h2 x

theorem dZ_pos_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F)
    (hEx : R.toRealDat.ExAt) (hUp : UpInj R.toRealDat) (hGE : R.PGEquiv F) (hRT : Formalism.IndefR.Rat.RowTest (R.toCx3 F))
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (u : (R.toCx3 F).EE) (hu0 : u ≠ 0)
    (hu : u ∈ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) :
    0 < (A3.A.fam.R A3.A.fam.μ0).dZ (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) := by
  have hM : R.toRealDat.IsModels := hC.base.models
  have hrat := range_le_span_rat (R.toCx3 F) F.cv (RealDat3.kFormR_of hM) (RealDat3.jIsoR_of hM) hRT A3.A.fam.μ0
  obtain ⟨ρ, hj, hρ, hΘ⟩ := exists_rho R F hOk hM hGE
  have hCore := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1
  have htype : ∀ h : P, R.gEx F (h : G) u = A3.A.fam.v0.embedding ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • u := by
    intro h
    have := (Submodule.mem_iInf _).1 hu h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨w, hw⟩ := surj_of_upInj R F hUp u
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.RowsNonzero.exists_rational ((R.toCx3 F).jR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r ρ
    (R.gEx F) ((R.toCx3 F).Θ A3.A.fam.μ0) hj hρ hΘ hrat (fun g => (idemOf A3.A.X).coeff g)
    (fun g => (lvlIdem P ψ).coeff g) hu0 hw (sum_idem_gEx R F hCore u)
    (GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) P ψ htype)
  exact GlobalTheory.RowsNonzero.dZ_pos (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) hz0 hz

end GlobalTheory.RowsPosRed

theorem GlobalTheory.RowsPosRed.pos_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInj R.toRealDat → RowsNe R.toRealDat F.lv2 → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp hNe hGE _ hRT b
  have hel := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.RowsPosRed.exists_row R F hC.base.models hNe b
  cases b
  · rw [hel.1] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P0 F.ψ0 u hu0 hu
  · rw [hel.2] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P1 F.ψ1 u hu0 hu
