import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupportedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeSplitPlaceEqAddComponentPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedOppositeLagrangianCoordinateStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacUniq

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem schr_schr {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  have key : (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) + ((x + w.1) ⬝ᵥ w'.2 + ⅟(2 : K) * (w'.1 ⬝ᵥ w'.2)) =
      ⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) +
        (x ⬝ᵥ (w + w').2 + ⅟(2 : K) * ((w + w').1 ⬝ᵥ (w + w').2)) := by
    have h2 : ⅟(2 : K) * 2 = 1 := invOf_mul_self 2
    simp only [Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2
  show ψ _ * (ψ _ * φ (x + w.1 + w'.1)) = ψ _ * (ψ _ * φ (x + (w + w').1))
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, Prod.fst_add, add_assoc]

theorem acts_unique {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) {x₀ : κ → AF F} (hx₀ : r x₀ ≠ 0)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i)) with hz
  have hza : At (evFin F v) z := GlobalTheory.VacAny.at_pi fun i => GlobalTheory.LatVac.at_liftV v _
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hza
  have hy : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [hz, Pi.add_apply, map_add, GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
  have e := congrFun ((h1 r hr).symm.trans (h2 r hr)) (x₀ + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hx₀ e

theorem phase {V : Type} [AddCommGroup V] [Module ℂ V] {φ ψ S : V} {c χ : ℂ} (hne : φ ≠ 0)
    (h1 : φ = (c * χ) • φ) (h2 : ψ = c • S) : S = χ • ψ := by
  have hcχ : c * χ = 1 := by
    by_contra hne'
    have h4 : (c * χ - 1) • φ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact hne ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne'))
  rw [h2, smul_smul, mul_comm, hcχ, one_smul]

theorem sa_bd_uniq : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq g hg hSa hBd
  have hψc : Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 Bs.v₁
  have hSB : ∀ γ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁),
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ ∈ GlobalTheory.WeilM.SB _ :=
    fun γ φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB _ _ hψc _ _ hφ
  have hat : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, At (evFin D.host.F Bs.v₁) γ :=
    (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1
  have hacts : ∀ γ, At (evFin D.host.F Bs.v₁) γ → ∀ φ, Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ
      (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) :=
    fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.T.exists_nonzero_complementary_adelicSchwartz_function Bs.v₁ φ₀ h0
  obtain ⟨χ, hχ⟩ : ∃ χ : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E) → ℂ, ∀ γ, χ γ =
      Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
        (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) := ⟨_, fun _ => rfl⟩
  have hφ₀ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ₀ = χ γ • φ₀ := by
    intro γ hγ
    rw [hχ]
    exact acts_unique Bs.v₁ hr hx₀ _ _ _ (hacts γ (hat γ hγ) φ₀) (hfix γ hγ)
  have hχ1 : ∀ u, At (evFin D.host.F Bs.v₁) u →
      (u.map (piW Bs.τ₁) = 0 ∨ u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) → χ u = 1 := by
    intro u hu h
    rw [hχ, GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hu h, mul_zero, AddChar.map_zero_eq_one]
  obtain ⟨ψ₀, hψ₀, hιψ₀⟩ := hι.bij.surjOn hg
  have hA : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, γ.map (piW Bs.τ₁) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    have ht : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) Y =
        ι ψ₀ (Y + GlobalTheory.VacShape.coBar Bs Γ γ) :=
      hι.trans γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) Y
    have hs : GlobalTheory.VacShape.coBar Bs Γ γ ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ := ⟨γ, hγ, h, rfl⟩
    rw [ht, hιψ₀]
    exact hSa _ hs Y
  have hB : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      γ.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_splitSupported_oppositeLagrangian_coordinate Bs Γ X om om' hTr Y
    have hm : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) (GlobalTheory.VacShape.coBar Bs Γ x) =
        Bs.ψ (symp (cA D.sp.cm.sig) (-1) (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) x γ) *
          ι ψ₀ (GlobalTheory.VacShape.coBar Bs Γ x) :=
      hι.mult γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) x hx hx0
    rw [hm, hιψ₀]
    by_cases hY : GlobalTheory.VacShape.coBar Bs Γ x ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂
    · rw [hY x hx hx0 rfl γ hγ h, one_mul]
    · rw [hBd _ hY, mul_zero]
  have hfixψ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
        (Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
          (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) • ψ₀) := by
    intro γ hγ
    rw [← hχ]
    obtain ⟨γA, hγA, γB, hγB, rfl, hA0, hB0⟩ := GlobalTheory.T.tensorLatticeSplitPlace_eq_add_componentParts Bs Γ X om om' hTr L₁ L₂ γ hγ
    have e0 : GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (γA + γB) =
        GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA + GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB := map_add _ _ _
    have hc := schr_schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA)
      (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB)
    have hφA : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA) φ₀ = φ₀ := by
      rw [hφ₀ γA hγA, hχ1 γA (hat γA hγA) (Or.inl hA0), one_smul]
    have hφB : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB) φ₀ = φ₀ := by
      rw [hφ₀ γB hγB, hχ1 γB (hat γB hγB) (Or.inr hB0), one_smul]
    have h1 := hc φ₀
    rw [hφB, hφA, ← e0, hφ₀ _ hγ, smul_smul] at h1
    have h2 := hc ψ₀
    rw [hB γB hγB hB0, hA γA hγA hA0, ← e0] at h2
    have key := phase hne h1 h2
    have := hacts _ (hat _ hγ) ψ₀
    rwa [key] at this
  obtain ⟨c, hc⟩ := huniq ψ₀ hψ₀ hfixψ
  exact ⟨c, by rw [← hιψ₀, hc, map_smul]⟩

end GlobalTheory.VacUniq

end
