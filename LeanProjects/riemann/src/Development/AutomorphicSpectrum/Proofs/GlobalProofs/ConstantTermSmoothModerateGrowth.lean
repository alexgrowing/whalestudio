import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf

open MeasureTheory GlobalTheory.SiegelSet GlobalTheory.Mem.AutSpace GlobalTheory.SphSmooth

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def pairSpan (V : HSp D) (φ c : GA D V → ℂ) : Submodule ℂ ((GA D V → ℂ) × (GA D V → ℂ)) :=
  Submodule.span ℂ {p | ∃ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) ∧
    p = (l.foldr lineDer φ, l.foldr lineDer c)}

theorem pairSpan_le (φ c : GA D V → ℂ) : pairSpan V φ c ≤ (derSpan V φ).prod (derSpan V c) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩

theorem Rder_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {p : (GA D V → ℂ) × (GA D V → ℂ)}
    (hp : p ∈ pairSpan V φ c) : (Rder θ V τ X p.1, Rder θ V τ X p.2) ∈ pairSpan V φ c := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨oneP θ V τ X :: l, List.forall_mem_cons.2 ⟨isRealLine_oneP hθ V hX, hl⟩, rfl⟩
  | zero =>
    have := Rder_smul (θ := θ) 0 (0 : GA D V → ℂ) τ X
    rw [zero_smul, zero_smul] at this
    simp only [Prod.fst_zero, Prod.snd_zero, this]
    exact zero_mem (pairSpan V φ c)
  | add x y hx hy ihx ihy =>
    have h1 := pairSpan_le φ c hx
    have h2 := pairSpan_le φ c hy
    simp only [Prod.fst_add, Prod.snd_add]
    rw [Rder_add (derSpan_le hθ hφ h1.1) (derSpan_le hθ hφ h2.1) hX,
      Rder_add (derSpan_le hθ hc h1.2) (derSpan_le hθ hc h2.2) hX]
    exact add_mem ihx ihy
  | smul a x _ ih =>
    simp only [Prod.smul_fst, Prod.smul_snd, Rder_smul]
    exact Submodule.smul_mem _ a ih

theorem RderC_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) {p : (GA D V → ℂ) × (GA D V → ℂ)}
    (hp : p ∈ pairSpan V φ c) : (RderC θ V τ Z p.1, RderC θ V τ Z p.2) ∈ pairSpan V φ c := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  exact add_mem (Rder_mem_pairSpan hθ hφ hc h1 hp)
    (Submodule.smul_mem _ Complex.I (Rder_mem_pairSpan hθ hφ hc h2 hp))

theorem word_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (L : List ((GA D V → ℂ) → GA D V → ℂ)) (hL : ∀ A ∈ L, ∃ Z, A = RderC θ V τ Z) :
    (L.foldr (fun f acc => f acc) φ, L.foldr (fun f acc => f acc) c) ∈ pairSpan V φ c := by
  induction L with
  | nil => exact Submodule.subset_span ⟨[], by simp, rfl⟩
  | cons A L ih =>
    obtain ⟨Z, rfl⟩ := hL A List.mem_cons_self
    exact RderC_mem_pairSpan hθ hφ hc τ Z (ih fun B hB => hL B (List.mem_cons_of_mem _ hB))

theorem gelf_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (k : ℕ) : (gelf θ V τ k φ, gelf θ V τ k c) ∈ pairSpan V φ c := by
  have e : (gelf θ V τ k φ, gelf θ V τ k c) = ∑ idx : Fin (k + 1) → Fin V.rank,
      ((List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) φ,
        (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) c) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]; rfl
    · rw [Prod.snd_sum]; rfl
  rw [e]
  refine Submodule.sum_mem _ fun idx _ => word_mem_pairSpan hθ hφ hc τ _ fun A hA => ?_
  obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hA
  exact ⟨_, rfl⟩

variable {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}

theorem good_of_mem_pairSpan (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (T : Finset (Fin m)) {φ c : GA D V → ℂ}
    (hφ : IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ)
    (h : ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) →
      IsConstAlong D.sp.cm.sig V.gram X T (l.foldr lineDer φ) (l.foldr lineDer c))
    (μ : Measure (unip D.sp.cm.sig V.gram X T)) (𝓕 : Set (unip D.sp.cm.sig V.gram X T)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram).subgroupOf (unip D.sp.cm.sig V.gram X T)) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (g : GA D V) {p : (GA D V → ℂ) × (GA D V → ℂ)} (hp : p ∈ pairSpan V φ c) :
    IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => p.1 ((u : GA D V) * g)) 𝓕 μ ∧
      p.2 g = ∫ u in 𝓕, p.1 ((u : GA D V) * g) ∂μ := by
  have hJ : IsHermND D.sp.cm.sig V.gram :=
    ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero⟩
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine ⟨?_, h l hl μ 𝓕 hμ h𝓕 h1 g⟩
    obtain ⟨C, hC, hcov⟩ := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame _ _ _ (GlobalTheory.AdelicU.isCMExt_host D) _ _ hJ _ X Y hW T
    have hcont := GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic _ _ _ (GlobalTheory.AdelicU.isCMExt_host D) _ _ hJ φ hφ.level hφ.cont hφ.smooth l hl
    have hleft := GlobalTheory.UAut.ConstAut.leftInv_foldr
      (Γ := (GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V))) (φ := φ) (fun γ hγ x => hφ.left γ hγ x) l
    refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ _ C hC hcov μ hμ 𝓕 h𝓕 _
      (hcont.comp (continuous_subtype_val.mul continuous_const)) fun γ hγ u => ?_
    simp only [Subgroup.coe_mul, mul_assoc]
    exact hleft γ ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩ _
  | zero => exact ⟨integrableOn_zero, by simp⟩
  | add x y _ _ ihx ihy =>
    refine ⟨ihx.1.add ihy.1, ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [ihx.2, ihy.2]
    exact (integral_add ihx.1 ihy.1).symm
  | smul a x _ ih =>
    refine ⟨ih.1.const_mul a, ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [ih.2]
    exact (integral_const_mul a _).symm

theorem isConstAlong_gelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ → GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram c → (∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c)) → ∀ (τ : D.what₂.Tau) (k : ℕ), IsConstAlong D.sp.cm.sig V.gram X T (gelf θ V τ k φ) (gelf θ V τ k c) := by
  intro D θ hθ V m X Y hW T φ c hφ hc h τ k μ 𝓕 hμ h𝓕 h1 g
  have sφ : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram φ := hφ.smooth
  exact (good_of_mem_pairSpan hW T hφ h μ 𝓕 hμ h𝓕 h1 g
    (gelf_mem_pairSpan hθ (mem_smFun_of_isSm hθ sφ) (mem_smFun_of_isSm hθ hc) τ k)).2

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf

end
