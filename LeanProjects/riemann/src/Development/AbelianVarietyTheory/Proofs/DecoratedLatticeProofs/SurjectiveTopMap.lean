import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMemMultT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OnFrameOfSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopOnto

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ)))).mul (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  obtain ⟨u, rfl⟩ : IsUnit g := isUnit_of_mul_isUnit_right (hg'.symm ▸ hG : IsUnit (gᴴ * gramAt D V τ * g))
  exact Submodule.subset_span
    (Formalism.IndefR.SchurOrthogonalityAlt.smoothVec_rep M τ ⟨u, hg⟩ (Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_of_mem hw))

theorem real_induction (hθ : IsInfFam θ) (P : GA D V → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hat : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P (atTau θ V τ g)) : ∀ a ∈ GinfC V, P a := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have key : ∀ s : Finset D.what₂.Tau, ∀ a ∈ GinfC V, (∀ τ ∉ s, infMat D.sp.cm.sig V.gram (θ τ) a = 1) → P a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha h
      rw [R.2.2.1 a ha 1 (one_mem _) fun τ => by rw [h τ (Finset.notMem_empty τ), infMat_one]]
      exact h1
    | insert τ s hτ ih =>
      intro a ha h
      have hg := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
      have hb := atTau_spec hθ V τ hg
      have hi : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a))⁻¹ *
          infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) = 1 := fun ρ => by
        rw [← infMat_mul, inv_mul_cancel, infMat_one]
      rw [← mul_inv_cancel_left (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) a]
      refine hmul _ _ (hat τ _ hg) (ih _ (mul_mem (inv_mem hb.1) ha) fun ρ hρ => ?_)
      rw [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have := hi ρ
        rwa [hb.2.1] at this
      · have := hi ρ
        rw [hb.2.2 ρ c] at this
        rw [h ρ (by simp [c, hρ])]
        exact this
  exact fun a ha => key Finset.univ a ha fun τ h => absurd (Finset.mem_univ τ) h

theorem multT_rel {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (v v' : M.Vec) (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → m v' x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) :
    T (PiTensorProduct.tprod ℂ v') x' = c * T (PiTensorProduct.tprod ℂ v) x := by
  obtain ⟨m, hm, rfl⟩ := hT
  show PiTensorProduct.lift m _ x' = c * PiTensorProduct.lift m _ x
  rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
  induction hm using Submodule.span_induction with
  | mem m hm => exact h m hm
  | zero => simp
  | add a b _ _ ha hb => simp only [MultilinearMap.add_apply, Pi.add_apply, ha, hb, mul_add]
  | smul r a _ ha => simp only [MultilinearMap.smul_apply, Pi.smul_apply, ha, smul_eq_mul]; ring

theorem multT_rel' {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → ∀ v, m v x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) (v : SmT M) :
    T v x' = c * T v x := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, multT_rel v v x x' c (fun m hm => h m hm v) hT, smul_eq_mul, smul_eq_mul]
    ring
  | add a b ha hb => rw [map_add, Pi.add_apply, Pi.add_apply, ha, hb, mul_add]

theorem exists_ratPt (hθ : IsInfFam θ) {n : ℕ} (hn : V.rank = n) (δ : GL (Fin n) D.host.E)
    (hδ : δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))) :
    ∃ γ ∈ GQ V, finN V hn γ = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ ∧
      ∀ τ, (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) = (δ : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) := by
  subst hn
  have hm : Formalism.UG.bc (incA D) δ ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram :=
    unit_transfer (Equiv.refl _) (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig)
      (fun _ => rfl) V.gram _ (fun _ _ => rfl) δ.1 _ (fun _ _ => rfl) hδ
  refine ⟨⟨_, hm⟩, ⟨δ, hδ, rfl⟩, rfl, fun τ => ?_⟩
  exact Matrix.ext fun i j => (hθ τ).1 _

theorem infN_eq {n : ℕ} (hn : V.rank = n) (γ : GA D V) (τ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) =
      (infMat D.sp.cm.sig V.gram (θ τ) γ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

end General

section Law

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

set_option maxHeartbeats 1000000 in

theorem real_translate (hθ : IsInfFam θ) (hj : IsJ u M j) : ∀ a ∈ GinfC D.sp.X', ∀ v : SmT M, ∃ v' : SmT M,
    lT _ (infPt θ a) (j v') = j v ∧ ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine real_induction hθ _ (fun v => ⟨v, by rw [map_one, lT_one], fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, e1, f1⟩ := hb v
    obtain ⟨v₂, e2, f2⟩ := ha v₁
    refine ⟨v₂, by rw [map_mul (infPt θ), lT_mul, e2, e1], fun T hT h => ?_⟩
    rw [f2 T hT, f1 T hT, mul_assoc]
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), ?_, fun T hT h => ?_⟩
      · rw [map_smul, map_smul, map_smul]
        congr 1
        funext y
        refine hj.eqv τ g hg v w rfl _ y fun ρ => ?_
        refine (congrArg (· * y.1 ρ) (infN_atTau θ _ (rankP D) hθ τ hg ρ)).trans ?_
        by_cases c : ρ = τ
        · subst c
          simp only [Function.update_self]
        · simp only [Function.update_of_ne c, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      · rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
          multT_rel v (Function.update v τ w) (h * atTau θ _ τ g) h 1 (fun m hm => by
            rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', e1, f1⟩ := ha
      obtain ⟨b', e2, f2⟩ := hb
      refine ⟨a' + b', by rw [j.map_add, j.map_add, LinearMap.map_add, e1, e2], fun T hT h => ?_⟩
      rw [T.map_add, T.map_add, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]

theorem hasMat_finPt {h : GA D D.sp.X'} (hh : h ∈ GfC D.sp.X') : HasMat h (finPt h).1 :=
  ⟨hh, fun i j => (finN_apply D.sp.X' (rankP D) h (finCongr (rankP D) i) (finCongr (rankP D) j)).symm⟩

end Law

section Form

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

end Form

end GlobalTheory.Core.Rk.TopOnto

end
