import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocOpsW

theorem extend_hom {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) {G : Type} [Monoid G]
    (T : G →* Module.End ℂ S) : ∃ om' : G →* Module.End ℂ V, ∀ g (s : S), om' g s = (T g s : V) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  set P := S.linearProjOfIsCompl C hC with hPdef
  have hP : ∀ s : S, P s = s := fun s => Submodule.linearProjOfIsCompl_apply_left hC s
  let A : G → Module.End ℂ V := fun g => S.subtype ∘ₗ T g ∘ₗ P + (LinearMap.id - S.subtype ∘ₗ P)
  have hA : ∀ g w, A g w = (T g (P w) : V) + (w - (P w : V)) := fun g w => rfl
  refine ⟨{ toFun := A, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply LinearMap.ext; intro w
    rw [hA, map_one, Module.End.one_apply, Module.End.one_apply]; abel
  · intro x y; apply LinearMap.ext; intro w
    rw [Module.End.mul_apply, hA x, hA y, hA (x * y), map_mul, Module.End.mul_apply]
    have e : P ((T y (P w) : V) + (w - (P w : V))) = T y (P w) := by
      rw [map_add, map_sub, hP, hP, sub_self, add_zero]
    rw [e]; abel
  · intro g s
    show A g s = _
    rw [hA, hP, sub_self, add_zero]

end GlobalTheory.LocOpsW

namespace GlobalTheory.LocOpsW

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_uniq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ :=
  GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ φ₁ φ₂ hφ fun r hr => (h1 r hr).symm.trans (h2 r hr)

theorem loc_hom (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {G : Type} [Monoid G] (Ω : G →* Module.End ℂ ((κ → AF F) → ℂ))
    (hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, Ω x Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hex : ∀ x, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (Ω x) φ φ₁) :
    ∃ T : G →* Module.End ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)),
      ∀ x (φ : GlobalTheory.WeilM.SB (κ → Fv F v)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (Ω x) φ (T x φ) := by
  classical
  let S := GlobalTheory.WeilM.SB (κ → Fv F v)
  let t : G → S → S := fun x φ => ⟨Classical.choose (hex x φ φ.2), (Classical.choose_spec (hex x φ φ.2)).1⟩
  have ht : ∀ x (φ : S), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (Ω x) φ (t x φ) :=
    fun x φ => (Classical.choose_spec (hex x φ φ.2)).2
  have hu : ∀ x (φ ψ : S), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (Ω x) φ ψ → t x φ = ψ :=
    fun x φ ψ h => Subtype.ext (acts_uniq v _ φ.2 (ht x φ) h)
  let L : G → Module.End ℂ S := fun x =>
    { toFun := t x
      map_add' := fun φ ψ => hu x _ _ (by
        have := GlobalTheory.ThK.LocalOps.acts_lin v (Ω x) (hex x) φ.2 ψ.2 (ht x φ) (ht x ψ) 1 1
        simpa using this)
      map_smul' := fun a φ => hu x _ _ (by
        have := GlobalTheory.ThK.LocalOps.acts_lin v (Ω x) (hex x) φ.2 φ.2 (ht x φ) (ht x φ) a 0
        simpa using this) }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_ }, fun x φ => ht x φ⟩
  · apply LinearMap.ext; intro φ
    show t 1 φ = φ
    refine hu 1 φ φ ?_
    intro r _
    rw [map_one]; rfl
  · intro x y; apply LinearMap.ext; intro φ
    show t (x * y) φ = t x (t y φ)
    refine hu (x * y) φ _ ?_
    rw [map_mul]
    exact GlobalTheory.ThK.LocalOps.acts_mul v (hpres y) (ht y φ) (ht x (t y φ))

end GlobalTheory.LocOpsW

namespace GlobalTheory.LocOpsW

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W} {ψ : AddChar (AF F) ℂ} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W}
    (hW : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass F) ψ M.co (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)) om)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hx1 : x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)) (hx2 : x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := by
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2 - 1) = 0 := hx2 u hu
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 * (u • w) = u • w := by
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2)ᵀ = u • w := by
    have : (u • w) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2)ᵀ - u • w = w * (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

theorem acts_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W} {ψ : AddChar (AF F) ℂ} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W}
    (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (hW : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass F) ψ M.co (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)) om)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hx1 : x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)) (hx2 : x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ := by
  set T := om x with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres x Φ hΦ
  have hcomm := comm_off hW v x hx1 hx2
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ x Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin n × Fin d → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, GlobalTheory.ThK.LocalOps.schr_trans, GlobalTheory.ThK.LocalOps.schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  refine ⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.ThK.LocalOps.liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.LocOpsW

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweAdelic

namespace GlobalTheory.LocOpsW

theorem locRep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    ∃ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
      ∀ g h, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) ∧
        Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hstd hweil v
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hweil
  let ι : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* UA σ X.J × UA σ W.J :=
    (UAtGrp σ X (evFin F v)).subtype.prodMap (UAtGrp σ W (evFin F v)).subtype
  obtain ⟨T, hT⟩ := loc_hom v (om.comp ι) (fun x Φ hΦ => hW.pres (ι x) Φ hΦ)
    (fun x φ hφ => acts_exists hstd hW v (ι x) x.1.2 x.2.2 φ hφ)
  obtain ⟨om', hom'⟩ := extend_hom (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) T
  refine ⟨om', fun g h φ hφ => ?_⟩
  have e := hom' (g, h) ⟨φ, hφ⟩
  refine ⟨?_, ?_⟩
  · rw [show om' (g, h) φ = _ from e]; exact (T (g, h) ⟨φ, hφ⟩).2
  · rw [show om' (g, h) φ = _ from e]; exact hT (g, h) ⟨φ, hφ⟩

end GlobalTheory.LocOpsW
