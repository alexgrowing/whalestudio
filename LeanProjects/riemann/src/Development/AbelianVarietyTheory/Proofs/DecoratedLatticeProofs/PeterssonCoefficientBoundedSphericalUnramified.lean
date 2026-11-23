import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.SphCoef

variable {D : D7}

theorem mem_l2_add {A : HSp D} {m : Measure (GA D A)} {φ ψ : GA D A → ℂ} (h : MemL2Quotient (GQ A) m φ)
    (h' : MemL2Quotient (GQ A) m ψ) : MemL2Quotient (GQ A) m (φ + ψ) :=
  ⟨fun γ hγ g => by simp only [Pi.add_apply, h.1 γ hγ g, h'.1 γ hγ g], h.2.add h'.2⟩

theorem mem_l2_smul {A : HSp D} {m : Measure (GA D A)} {φ : GA D A → ℂ} (c : ℂ) (h : MemL2Quotient (GQ A) m φ) :
    MemL2Quotient (GQ A) m (c • φ) :=
  ⟨fun γ hγ g => by simp only [Pi.smul_apply, h.1 γ hγ g], h.2.const_smul c⟩

theorem mem_l2_zero {A : HSp D} {m : Measure (GA D A)} : MemL2Quotient (GQ A) m (0 : GA D A → ℂ) :=
  ⟨fun _ _ _ => rfl, MemLp.zero⟩

theorem isSphCoef_rcoef : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (L : Lat A), IsInfFam θ → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)), ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u₁ par → SphFun A L Sf u₂ → ∀ v ∉ Sf, ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → IsSphCoef A L v par fun y => rcoef m u₁ u₂ (x * emb D.sp.cm.sig A.gram v y) := by
  intro hP D θ A cA L hθ m hm Sf u₁ hu₁ u₂ hu₂ par hpar hsph v hv x hx
  have : m.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A m hm
  have h1 : MemL2Quotient (GQ A) m u₁ := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu₁).1
  have h2 : MemL2Quotient (GQ A) m u₂ := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu₂).1
  have hR : ∀ g, MemL2Quotient (GQ A) m (rTr A g u₁) := fun g => h1.mul_right g
  let p : Submodule ℂ (GA D A → ℂ) :=
    { carrier := {F | MemL2Quotient (GQ A) m (rTr A x F)}
      zero_mem' := mem_l2_zero
      add_mem' := fun ha hb => mem_l2_add ha hb
      smul_mem' := fun c _ hF => mem_l2_smul c hF }
  let ℓ₀ : p →ₗ[ℂ] ℂ :=
    { toFun := fun F => petersson A m (rTr A x F) u₂
      map_add' := fun F G => petersson_add_left F.2 G.2 h2
      map_smul' := fun c F => petersson_smul_left c _ _ }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  let ρ : Representation ℂ (Gv A v) (GA D A → ℂ) :=
    (GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp (emb D.sp.cm.sig A.gram v)
  have hρ : ∀ y g, ρ y u₁ g = u₁ (g * emb D.sp.cm.sig A.gram v y) := fun _ _ => rfl
  have htr : ∀ y, rTr A x (ρ y u₁) = rTr A (x * emb D.sp.cm.sig A.gram v y) u₁ := fun y => funext fun g => by
    simp only [rTr, hρ, mul_assoc]
  have hmem : ∀ y, ρ y u₁ ∈ p := fun y => by
    show MemL2Quotient _ _ (rTr A x (ρ y u₁))
    rw [htr]; exact hR _
  have hval : ∀ y, ℓ (ρ y u₁) = petersson A m (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) u₂ := fun y => by
    have e := LinearMap.congr_fun hℓ ⟨_, hmem y⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e
    rw [e, ← htr]; rfl
  have hnorm : ∀ g, ‖(hR g).toL2‖ = ‖h1.toL2‖ := fun g => by
    have e1 := (hR g).inner_toL2_eq_theta_pairing (hR g)
    have e2 := h1.inner_toL2_eq_theta_pairing h1
    have e3 : pet (GQ A) m (rTr A g u₁) (rTr A g u₁) = pet (GQ A) m u₁ u₁ := by
      have := petersson_rTr (μ := m) h1 h1 g
      exact this
    rw [e3, ← e2, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e1
    have e4 : ‖(hR g).toL2‖ ^ 2 = ‖h1.toL2‖ ^ 2 := by exact_mod_cast e1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e4
  refine ⟨⟨‖h2.toL2‖ * ‖h1.toL2‖, fun y => ?_⟩, GA D A → ℂ, inferInstance, inferInstance, ρ, u₁, ℓ,
    fun w h => hpar v (by simpa using hv) w h, fun k hk y => ?_, fun y => (hval y).symm⟩
  · show ‖petersson A m (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) u₂‖ ≤ _
    rw [petersson, ← (hR _).inner_toL2_eq_theta_pairing h2, ← hnorm (x * emb D.sp.cm.sig A.gram v y)]
    exact norm_inner_le_norm _ _
  · rw [hval, hval, map_mul]
    have hc : emb D.sp.cm.sig A.gram v k * x = x * emb D.sp.cm.sig A.gram v k :=
      (GlobalTheory.AdelicU.commute_emb (σ := D.sp.cm.sig) (J := A.gram) k hx).eq
    have e1 : rTr A (x * (emb D.sp.cm.sig A.gram v k * emb D.sp.cm.sig A.gram v y)) u₁ =
        rTr A (emb D.sp.cm.sig A.gram v k) (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) := funext fun g => by
      simp only [rTr]
      rw [← mul_assoc x, ← hc]
      simp only [mul_assoc]
    have e2 : u₂ = rTr A (emb D.sp.cm.sig A.gram v k) u₂ := funext fun g => (hsph v hv k hk g).symm
    rw [e1]
    conv_lhs => rw [e2]
    exact petersson_rTr (hR _) h2 _

end GlobalTheory.Core.Rk.SphCoef

end
