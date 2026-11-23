import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLieOp

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.RealLift

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem actsD_zero' (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

open scoped Classical in

theorem actsD_comb (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f + g) ⇑(c • f₁ + g₁) := by
  have e : ∀ (r : (κ → AF F) → ℂ) (φ ψ : SInf F κ),
      tens (evI F) ⇑(c • φ + ψ) r = c • tens (evI F) ⇑φ r + tens (evI F) ⇑ψ r := by
    intro r φ ψ; funext y; simp [tens]; ring
  have key : ∀ r, Rest (evI F) ⇑f r → Rest (evI F) ⇑g r → ∀ x,
      HasDerivAt (fun t => L t (tens (evI F) ⇑(c • f + g) r) x) (tens (evI F) ⇑(c • f₁ + g₁) r x) 0 := by
    intro r h1 h2 x
    rw [e, e]
    have h := ((hf r h1 x).const_mul c).add (hg r h2 x)
    have hfun : (fun t => L t (c • tens (evI F) ⇑f r + tens (evI F) ⇑g r) x) =
        (fun t => c * L t (tens (evI F) ⇑f r) x) + (fun t => L t (tens (evI F) ⇑g r) x) := by
      funext t; simp [map_add, map_smul]
    rw [hfun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h

  set g₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl
  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r₀ := fun φ =>
    ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨φ, g₀, hg₀, rfl⟩⟩
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  intro r hr x
  by_cases h0 : c • f + g = 0
  · have hz : c • f₁ + g₁ = 0 := by
      ext a
      have h := key r₀ (hrest₀ f) (hrest₀ g) (ptAt a 0)
      rw [h0, hzeroT] at h
      simp only [map_zero, Pi.zero_apply] at h
      have h' := h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      rw [htens₀, pureA_ptAt, hg₀0, mul_one] at h'
      simpa using h'
    rw [h0, hz, hzeroT]
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const _ _
  · have hR : (fun y => r (fun i => ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F), y i))) ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :=
      mem_SB_of_pureA_mem h0 (tens_eq_pureA _ hr.1 ▸ hr.2)
    have hrest : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r := fun φ =>
      ⟨hr.1, by rw [tens_eq_pureA _ hr.1]; exact Submodule.subset_span ⟨φ, _, hR, rfl⟩⟩
    exact key r (hrest f) (hrest g) x

theorem actsD_add (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(f + g) ⇑(f₁ + g₁) := by
  simpa only [one_smul] using actsD_comb L 1 hf hg

theorem actsD_smul (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f) ⇑(c • f₁) := by
  simpa only [add_zero] using actsD_comb L c hf (actsD_zero' L)

end GlobalTheory.RealLieOp

theorem GlobalTheory.RealLieOp.exists_realOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∃ T : Module.End ℂ R.Pi,
      (∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f₁ = T (R.p f)) ∧
      ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f' f₁' → R.p' f₁' = T (R.p' f') := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM γ hγ
  let L : ℝ → Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ) := fun t => om (1, γ (Multiplicative.ofAdd t))
  let L' : ℝ → Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) := fun t => om' (1, γ (Multiplicative.ofAdd t))
  let S : Set (R.Pi × R.Pi) :=
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ z = (R.p f, R.p f₁)} ∪
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')), f ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f ⇑f₁ ∧ z = (R.p' f, R.p' f₁)}
  have hspan : ∀ z ∈ Submodule.span ℂ S, ∃ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (f' f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f' ⇑f₁' ∧
      z = (R.p f + R.p' f', R.p f₁ + R.p' f₁') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨f, f₁, hf, h1, rfl⟩ | ⟨f, f₁, hf, h1, rfl⟩
      · exact ⟨f, f₁, 0, 0, hf, h1, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', by simp⟩
      · exact ⟨0, 0, f, f₁, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, hf, h1, by simp⟩
    | zero => exact ⟨0, 0, 0, 0, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', Prod.ext (by simp) (by simp)⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      obtain ⟨g, g₁, g', g₁', hg, h2, hg', h2', rfl⟩ := hy
      refine ⟨f + g, f₁ + g₁, f' + g', f₁' + g₁', add_mem hf hg, GlobalTheory.RealLieOp.actsD_add L h1 h2,
        add_mem hf' hg', GlobalTheory.RealLieOp.actsD_add L' h1' h2', ?_⟩
      simp only [map_add, Prod.mk_add_mk]
      abel_nf
    | smul c x _ hx =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      refine ⟨c • f, c • f₁, c • f', c • f₁', Submodule.smul_mem _ c hf, GlobalTheory.RealLieOp.actsD_smul L c h1,
        Submodule.smul_mem _ c hf', GlobalTheory.RealLieOp.actsD_smul L' c h1', ?_⟩
      simp only [map_smul, Prod.smul_mk, smul_add]
  have hgraph : ∀ z ∈ Submodule.span ℂ S, z.1 = 0 → z.2 = 0 := by
    intro z hz hz0
    obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hspan z hz
    have e : R.p f + R.p' f' = 0 := hz0
    have e2 : R.p f = R.p' (-f') := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left e
    have hn : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑(-f') ⇑(-f₁') := by
      simpa only [neg_one_smul] using GlobalTheory.RealLieOp.actsD_smul L' (-1) h1'
    have := hM.real.lie γ hγ f hf (-f') (neg_mem hf') f₁ (-f₁') h1 hn e2
    show R.p f₁ + R.p' f₁' = 0
    rw [this, map_neg, neg_add_cancel]
  obtain ⟨T, hT⟩ := LinearMap.exists_extend (Submodule.span ℂ S).toLinearPMap.toFun
  have hT' : ∀ z ∈ Submodule.span ℂ S, T z.1 = z.2 := by
    intro z hz
    have hz' : z ∈ (Submodule.span ℂ S).toLinearPMap.graph := by
      rw [Submodule.toLinearPMap_graph_eq _ hgraph]; exact hz
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hz'
    rw [← hy1, ← hy2]
    exact LinearMap.congr_fun hT y
  refine ⟨T, fun f hf f₁ h1 => ?_, fun f hf f₁ h1 => ?_⟩
  · exact (hT' (R.p f, R.p f₁) (Submodule.subset_span (Or.inl ⟨f, f₁, hf, h1, rfl⟩))).symm
  · exact (hT' (R.p' f, R.p' f₁) (Submodule.subset_span (Or.inr ⟨f, f₁, hf, h1, rfl⟩))).symm
