import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

noncomputable section

namespace GlobalTheory.SquareAgree.CoinvPass

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

def relD (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Ψ | ∃ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Y (evFin F v₁), ∃ Ψ₀ ∈ algD M ψ emb, Ψ = om (g, 1) Ψ₀ - Ψ₀}

theorem tens_sub' (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a b : (Fin n × Fin d → Fv F v₁) → ℂ) (r : (Fin n × Fin d → AF F) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) (a - b) r =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) a r - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) b r := by
  funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.sub_apply]; ring

theorem tens_add' (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a b : (Fin n × Fin d → Fv F v₁) → ℂ) (r : (Fin n × Fin d → AF F) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) (a + b) r =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) a r + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) b r := by
  funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply]; ring

theorem tens_smul' (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (c : ℂ) (a : (Fin n × Fin d → Fv F v₁) → ℂ)
    (r : (Fin n × Fin d → AF F) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) (c • a) r = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) a r := by
  funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul]; ring

theorem tens_zero' (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (r : (Fin n × Fin d → AF F) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) (0 : (Fin n × Fin d → Fv F v₁) → ℂ) r = 0 := by
  funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.zero_apply, zero_mul]

theorem tens_mem_relD (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    {f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ emb)
    {φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hSB : ∀ v, φ v ∈ SB _)
    (hcof : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) {r : (Fin n × Fin d → AF F) → ℂ}
    (hr : ∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z → r (x + z) = r x)
    (hrt : ∀ ψ₀, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v₁ ψ₀)) :
    ∀ δ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v₁, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) δ r ∈ relD M om ψ emb v₁ := by
  have hφstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hstd] with v h1 h2
    rw [h1, h2]
  have hupd : ∀ φ₀ ∈ SB (Fin n × Fin d → Fv F v₁), ∀ w, Function.update φ v₁ φ₀ w ∈ SB _ := by
    intro φ₀ hφ₀ w
    by_cases hw : w = v₁
    · subst hw; rw [Function.update_self]; exact hφ₀
    · rw [Function.update_of_ne hw]; exact hSB w
  intro δ hδ
  induction hδ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, hg, φ₀, hφ₀, φ₁, hφ₁, hA, rfl⟩ := hz
    have hsch : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) φ₀ r ∈ schA F (Fin n × Fin d) := by
      rw [hrt]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd φ₀ hφ₀) (GlobalTheory.PureFactor.update_eventually φ v₁ φ₀ hφstd)
    have hact := hA r ⟨hr, hsch⟩
    have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) φ₀ r ∈ algD M ψ emb := by
      rw [hrt]
      refine Submodule.subset_span ⟨f, Function.update φ v₁ φ₀, hf, hupd φ₀ hφ₀, ?_, rfl⟩
      filter_upwards [hcof, Filter.eventually_cofinite_ne v₁] with w h1 hne
      rw [Function.update_of_ne hne]; exact h1
    rw [tens_sub']
    refine Submodule.subset_span ⟨g, hg, _, hmem, ?_⟩
    rw [hact]
  | zero => rw [tens_zero']; exact zero_mem _
  | add a b _ _ ha hb => rw [tens_add']; exact add_mem ha hb
  | smul c a _ ha => rw [tens_smul']; exact Submodule.smul_mem _ c ha

theorem exists_So (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v₁)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    {P : Type} [AddCommGroup P] [Module ℂ P] (p : ((Fin n × Fin d → Fv F v₁) → ℂ) →ₗ[ℂ] P)
    (hco : ∀ φ ∈ SB (Fin n × Fin d → Fv F v₁), p φ = 0 ↔ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v₁)
    (hex : ∀ ξ, ∃ φ ∈ M.SoLoc ψ t, p φ = ξ) :
    ∀ ΦD ∈ algD M ψ emb, ∃ Φ₀ ∈ algD M ψ emb, Φ₀ ∈ M.So ψ t ∧ ΦD - Φ₀ ∈ relD M om ψ emb v₁ := by
  intro ΦD hΦ
  induction hΦ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hz
    have hφstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hcof, hstd] with v h1 h2
      rw [h1, h2]
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v₁ f φ hφstd
    obtain ⟨φo, hφo, hp⟩ := hex (p (φ v₁))
    have hφoSB : φo ∈ SB _ := hφo.1
    have hδ : φ v₁ - φo ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v₁ :=
      (hco _ (sub_mem (hSB v₁) hφoSB)).1 (by rw [map_sub, hp, sub_self])
    have hupd : ∀ w, Function.update φ v₁ φo w ∈ SB _ := by
      intro w
      by_cases hw : w = v₁
      · subst hw; rw [Function.update_self]; exact hφoSB
      · rw [Function.update_of_ne hw]; exact hSB w
    have hcof' : ∀ᶠ w in Filter.cofinite, Function.update φ v₁ φo w = M.vac w := by
      filter_upwards [hcof, Filter.eventually_cofinite_ne v₁] with w h1 hne
      rw [Function.update_of_ne hne]; exact h1
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v₁ φo), ?_, ?_, ?_⟩
    · exact Submodule.subset_span ⟨f, _, hf, hupd, hcof', rfl⟩
    · exact Submodule.subset_span ⟨f, _, hupd, hcof', by rw [Function.update_self]; exact hφo, rfl⟩
    · have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) (φ v₁) r := by
        rw [hrt, Function.update_eq_self]
      rw [e1, ← hrt, ← tens_sub']
      exact tens_mem_relD M om ψ emb v₁ hstd hf hSB hcof hr hrt _ hδ
  | zero => exact ⟨0, zero_mem _, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨a₀, ha₀, ha₁, ha₂⟩ := ha
    obtain ⟨b₀, hb₀, hb₁, hb₂⟩ := hb
    refine ⟨a₀ + b₀, add_mem ha₀ hb₀, add_mem ha₁ hb₁, ?_⟩
    have e : a + b - (a₀ + b₀) = (a - a₀) + (b - b₀) := by abel
    rw [e]; exact add_mem ha₂ hb₂
  | smul c a _ ha =>
    obtain ⟨a₀, ha₀, ha₁, ha₂⟩ := ha
    refine ⟨c • a₀, Submodule.smul_mem _ c ha₀, Submodule.smul_mem _ c ha₁, ?_⟩
    rw [← smul_sub]; exact Submodule.smul_mem _ c ha₂

theorem rho_sub' (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))
    (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ u (Φ₁ - Φ₂) = M.co.rho ψ u Φ₁ - M.co.rho ψ u Φ₂ := by
  funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.sub_apply]; ring

theorem rho_add' (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))
    (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ u (Φ₁ + Φ₂) = M.co.rho ψ u Φ₁ + M.co.rho ψ u Φ₂ := by
  funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]; ring

theorem rho_smul' (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))
    (c : ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ u (c • Φ) = c • M.co.rho ψ u Φ := by
  funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]; ring

theorem rho_zero' (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :
    M.co.rho ψ u 0 = 0 := by
  funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.zero_apply, mul_zero]

theorem thetaSum_sub' {κ : Type} [Fintype κ] {A B : (κ → AF F) → ℂ} (hA : A ∈ schA F κ) (hB : B ∈ schA F κ) :
    thetaSum F (A - B) = thetaSum F A - thetaSum F B :=
  (summable_of_mem_schA F hA).tsum_sub (summable_of_mem_schA F hB)

variable {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd} {ψ : AddChar (AF F) ℂ} {Z : Type}
  {crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z}

theorem isDatum_sub (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ} {f₁ f₂ : Z → ℂ}
    (h₁ : IsDatum M ψ crd Φ₁ f₁) (h₂ : IsDatum M ψ crd Φ₂ f₂) : IsDatum M ψ crd (Φ₁ - Φ₂) (f₁ - f₂) := by
  refine ⟨sub_mem h₁.1 h₂.1, fun u => ?_⟩
  rw [rho_sub', thetaSum_sub' (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ₁ h₁.1) (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ₂ h₂.1),
    h₁.2 u, h₂.2 u]
  rfl

theorem isDatum_add (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ} {f₁ f₂ : Z → ℂ}
    (h₁ : IsDatum M ψ crd Φ₁ f₁) (h₂ : IsDatum M ψ crd Φ₂ f₂) : IsDatum M ψ crd (Φ₁ + Φ₂) (f₁ + f₂) := by
  refine ⟨add_mem h₁.1 h₂.1, fun u => ?_⟩
  rw [rho_add', thetaSum_add F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ₁ h₁.1) (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ₂ h₂.1),
    h₁.2 u, h₂.2 u]
  rfl

theorem isDatum_smul (c : ℂ) {Φ : (Fin n × Fin d → AF F) → ℂ} {f : Z → ℂ} (h : IsDatum M ψ crd Φ f) :
    IsDatum M ψ crd (c • Φ) (c • f) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun u => ?_⟩
  rw [rho_smul', thetaSum_smul, h.2 u]
  rfl

theorem isDatum_zero : IsDatum M ψ crd 0 (0 : Z → ℂ) := by
  refine ⟨zero_mem _, fun u => ?_⟩
  rw [rho_zero']
  simp [GlobalTheory.WeilM.thetaSum]

theorem isDatum_unique (hs : Function.Surjective crd) {Φ : (Fin n × Fin d → AF F) → ℂ} {f g : Z → ℂ}
    (hf : IsDatum M ψ crd Φ f) (hg : IsDatum M ψ crd Φ g) : f = g := by
  funext z
  obtain ⟨u, rfl⟩ := hs z
  rw [← hf.2 u, hg.2 u]

end Gen

set_option maxHeartbeats 1600000 in

theorem conjUInv_mem_GfC {D : D7} (V : HSp D) (Yp : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E V.rank) (c : D.host.E)
    (hc : c ≠ 0) (h : Yp.J = c • V.gram) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F) (x : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Yp.J)
    (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Yp (evFin D.host.F v)) :
    GlobalTheory.ConjUTransport.conjUInv V c hc h x ∈ GfC V := by
  set a : AF D.host.F := 1 - GlobalTheory.EmbChart.atPlace v 1 with ha
  have h0 : evFin D.host.F v a = 0 := by
    rw [ha, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h1 : fstA D.host.F a = 1 := by
    show (1 : Ainf D.host.F) - (0 : Ainf D.host.F) = 1
    exact sub_zero 1
  let f := Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
  have hf1 : f (sigR (AF D.host.F) D.sp.cm.sig (a ⊗ₜ[D.host.F] (1 : D.host.E))) = 1 := by
    simp only [f, sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one,
      AlgHom.coe_id, id_eq, h1]
    rfl
  have hz : ∀ i j, f (sigR (AF D.host.F) D.sp.cm.sig ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1) i j)) = 0 := by
    intro i j
    have k := congrFun (congrFun (hx a h0) i) j
    rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] at k
    have k2 := congrArg (fun w => f (sigR (AF D.host.F) D.sp.cm.sig w)) k
    simp only [map_mul, map_zero] at k2
    rw [hf1, one_mul] at k2
    exact k2
  rw [GfC, MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  show f (sigR (AF D.host.F) D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x i j)) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x i j = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [e, map_add, map_add, hz i j, zero_add]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq (α := AF D.host.F ⊗[D.host.F] D.host.E), map_one, map_one,
      Matrix.one_apply_eq (α := Ainf D.host.F ⊗[D.host.F] D.host.E)]
  · rw [Matrix.one_apply_ne (α := AF D.host.F ⊗[D.host.F] D.host.E) hij, map_zero, map_zero,
      Matrix.one_apply_ne (α := Ainf D.host.F ⊗[D.host.F] D.host.E) hij]

theorem coinv_passage : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Coinv Bs Γ Xc om om' Rf →
    ∀ Φ' ∈ algF ψ θ false A₁ B, ∃ Φ₀ ∈ algF ψ θ false A₁ B, Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) ∧
      ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ := by
  intro D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _hθ hO hT R Rf _hM hC Φ' hΦ'
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT.base.std
  have hstd := hT.geo.hM'.std
  obtain ⟨-, hco, hex, -⟩ := hC.1 Bs.v₁ hT.chars.good
  obtain ⟨ΦD, hΦD, hD⟩ := hO.algB Φ' hΦ'
  obtain ⟨Φ₀D, h0a, h0s, hdiff⟩ := exists_So Γ.M' om' Bs.ψ Bs.emb Bs.τ₁ hstd (Rf.p' Bs.v₁) hco (hex Bs.τ₁) ΦD hΦD
  obtain ⟨Φ₀, hΦ₀, hD0⟩ := hO.algB' Φ₀D h0a
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hk : kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [kapX]
  have key : ∀ Ψ ∈ relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁, ∃ Φ ∈ finRel ωB (algF ψ θ false A₁ B), IsDatum Γ.M' ψ cB Ψ Φ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, Ψ₀, hΨ₀, rfl⟩ := hz
      obtain ⟨Φ₁, hΦ₁, hD1⟩ := hO.algB' Ψ₀ hΨ₀
      have hgu : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ g) = g :=
        (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hO.JW₁).right_inv g
      have hW := hO.weilB Ψ₀ Φ₁ hD1 (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ g) 1
      rw [hgu, hk] at hW
      exact ⟨_, Submodule.subset_span ⟨_, conjUInv_mem_GfC W₁ Γ.V' (-1) hc hO.JW₁ Bs.v₁ g hg, Φ₁, hΦ₁, rfl⟩,
        isDatum_sub hψ hW hD1⟩
    | zero => exact ⟨0, zero_mem _, isDatum_zero⟩
    | add a b _ _ ha hb =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      obtain ⟨Φb, hb, hDb⟩ := hb
      exact ⟨Φa + Φb, add_mem ha hb, isDatum_add hψ hDa hDb⟩
    | smul c a _ ha =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      exact ⟨c • Φa, Submodule.smul_mem _ c ha, isDatum_smul c hDa⟩
  obtain ⟨Φ, hΦ, hDΦ⟩ := key _ hdiff
  have hsub := isDatum_sub hψ hD hD0
  have hEq : Φ' - Φ₀ = Φ := isDatum_unique cB.surjective hsub hDΦ
  exact ⟨Φ₀, hΦ₀, hEq ▸ hΦ, Φ₀D, hD0, h0s⟩

end GlobalTheory.SquareAgree.CoinvPass
