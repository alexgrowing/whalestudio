import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlLoc
import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlDual
import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlBridge

noncomputable section

namespace PositivityTheory.ThKH.Evl

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.LatVac (liftV psiAt locCo evFin_liftV at_liftV)
open PositivityTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem psiAt_good {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (v : Pl F) :
    Continuous (psiAt ψ v) ∧ (∀ x, ‖psiAt ψ v x‖ = 1) ∧ psiAt ψ v ≠ 1 :=
  ⟨GlobalTheory.VacAny.continuous_psiV h.1 v, fun _ => GlobalTheory.StdCharFromIsStd.norm_psi h _, GlobalTheory.PsiNontriv.psiAt_ne_one ψ h v⟩

theorem evVac : PositivityTheory.ThK.EvVac := by
  rintro F E _ _ _ _ _ σ n d B X W M om hP v ⟨w₀, hw₀⟩ m Cy hL ⟨Cx, hLx, hsp⟩
  obtain ⟨hc, hn, h1⟩ := psiAt_good hP.base.std v
  obtain ⟨r, s, hX⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  obtain ⟨l, ⟨φ, hφ, hlφ⟩, hl⟩ := GlobalTheory.CompanionTheory.LagFun.exists_invariant_form (Fv F v) (Fin n × Fin d) (psiAt B.ψ v) hc h1
    (lagr M v Cy) (lagr_iso M hL)
  refine ⟨l, (isEvAt_iff M hL B.ψ l).2 hl, fun h0 => hlφ ?_⟩
  obtain ⟨hS, hne, θ, -, hvac⟩ := hP.good.vac v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  refine core hc hn h1 hS hne (lagr M v Cy) l hl (fun w => ?_) h0 φ hφ
  obtain ⟨u, rfl⟩ := exists_locCo M.co w
  obtain ⟨z, z', e⟩ := space_split hX.lat hW.lat hsp u
  refine ⟨_, ⟨z, rfl⟩, locCo M.co v (z' * Cxᵀ), by rw [e, map_add], ?_⟩
  by_cases hz : z' * Cxᵀ ∈ latAtV X W v
  · exact Or.inl ⟨_, ((acts_iff M.co B.ψ (hat _ hz) hS).1 (hvac _ hz)).symm⟩
  · right
    by_contra hcon
    refine hz (mem_latAtV_of_dual hP.base hX hW (hP.base.inert v w₀ hw₀).2.2 (at_mul hLx.supp z') fun γ hγ => ?_)
    obtain ⟨y, y', hy, rfl⟩ := lat_split hsp hγ
    rw [GlobalTheory.LatVacArith.symp_add_left, symp_lag hLx, add_zero, psi_form M.co B.ψ (hat _ hy)]
    by_contra hne'
    refine hcon ⟨_, ⟨y, rfl⟩, ?_, hne'⟩
    have h := (acts_iff M.co B.ψ (hat _ hy) hS).1 (hvac _ hy)
    rw [symp_lag hL, mul_zero, AddChar.map_zero_eq_one, one_smul] at h
    exact h.symm

end PositivityTheory.ThKH.Evl
