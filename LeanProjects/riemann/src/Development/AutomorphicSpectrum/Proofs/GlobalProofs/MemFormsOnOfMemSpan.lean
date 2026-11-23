import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionSmoothBounded
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicColumnsExtendWitt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

variable {D : D7}

def leftSub (V : HSp D) {m : ℕ} (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (S : Finset (Fin m)) : Subgroup (GA D V) :=
  unip D.sp.cm.sig V.gram X S ⊔ (GQ V ⊓ levi D.sp.cm.sig V.gram X Y S)

def formsOn (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {m : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (S : Finset (Fin m)) (U : Subgroup (GA D V))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) : Set (GA D V → ℂ) :=
  {φ | IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ ∧ (∀ u ∈ U, u ∈ GfC V → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) ∧ ∀ τ k, gelf θ V τ k φ = c τ k • φ}

section Sub

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {m : ℕ}
  {X Y : Matrix (Fin V.rank) (Fin m) D.host.E} {S : Finset (Fin m)} {U : Subgroup (GA D V)}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
  {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)} {c : D.what₂.Tau → ℕ → ℂ}

theorem isSmModOn_add {Γ : Set (GA D V)} {f g : GA D V → ℂ} (hf : IsSmModOn D.sp.cm.sig V.gram Γ f)
    (hg : IsSmModOn D.sp.cm.sig V.gram Γ g) : IsSmModOn D.sp.cm.sig V.gram Γ (f + g) := by
  have sf : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f := hf.smooth
  have sg : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram g := hg.smooth
  refine ⟨fun γ hγ x => ?_, ?_, hf.cont.add hg.cont, GlobalTheory.UAut.isSm_add sf sg, ?_⟩
  · simp only [Pi.add_apply, hf.left γ hγ x, hg.left γ hγ x]
  · obtain ⟨A, hA, eA⟩ := hf.level
    obtain ⟨B, hB, eB⟩ := hg.level
    refine ⟨A ⊓ B, hA.inter hB, fun k hk hk' x => ?_⟩
    simp only [Pi.add_apply, eA k hk.1 hk' x, eB k hk.2 hk' x]
  · obtain ⟨N, hN⟩ := hf.growth
    obtain ⟨M, hM⟩ := hg.growth
    refine ⟨max N M, fun l hl => ?_⟩
    obtain ⟨A, hA⟩ := hN l hl
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max A 0 + max B 0, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) := by
      exact_mod_cast GlobalTheory.AdelicU.one_le_height D.sp.cm.sig V.gram x
    have p1 := pow_le_pow_right₀ h1 (le_max_left N M)
    have p2 := pow_le_pow_right₀ h1 (le_max_right N M)
    have p0 : (0 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) ^ N := by positivity
    have p0' : (0 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) ^ M := by positivity
    rw [GlobalTheory.UAut.foldr_add hl sf sg, Pi.add_apply, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hA x).trans ?_) ((hB x).trans ?_))
    · exact (mul_le_mul_of_nonneg_right (le_max_left A 0) p0).trans
        (mul_le_mul_of_nonneg_left p1 (le_max_right A 0))
    · exact (mul_le_mul_of_nonneg_right (le_max_left B 0) p0').trans
        (mul_le_mul_of_nonneg_left p2 (le_max_right B 0))

theorem isSmModOn_smul {Γ : Set (GA D V)} (a : ℂ) {f : GA D V → ℂ} (hf : IsSmModOn D.sp.cm.sig V.gram Γ f) :
    IsSmModOn D.sp.cm.sig V.gram Γ (a • f) := by
  have sf : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f := hf.smooth
  refine ⟨fun γ hγ x => ?_, ?_, hf.cont.const_smul a, GlobalTheory.UAut.isSm_smul a sf, ?_⟩
  · simp only [Pi.smul_apply, hf.left γ hγ x]
  · obtain ⟨A, hA, eA⟩ := hf.level
    exact ⟨A, hA, fun k hk hk' x => by simp only [Pi.smul_apply, eA k hk hk' x]⟩
  · obtain ⟨N, hN⟩ := hf.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨A, hA⟩ := hN l hl
    refine ⟨‖a‖ * A, fun x => ?_⟩
    rw [GlobalTheory.UAut.foldr_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA x) (norm_nonneg _)

theorem formsOn_add (hθ : IsInfFam θ) {f g : GA D V → ℂ} (hf : f ∈ formsOn θ V X Y S U ε fr ρ c)
    (hg : g ∈ formsOn θ V X Y S U ε fr ρ c) : f + g ∈ formsOn θ V X Y S U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨isSmModOn_add f1 g1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.add_apply, f2 u hu hu' x, g2 u hu hu' x]
  · exact (coeffSpan (ρ τ)).add_mem (f3 τ x) (g3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).add f (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ f1.smooth) g
      (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ g1.smooth), f4, g4, smul_add]

theorem formsOn_smul (a : ℂ) {f : GA D V → ℂ} (hf : f ∈ formsOn θ V X Y S U ε fr ρ c) :
    a • f ∈ formsOn θ V X Y S U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  refine ⟨isSmModOn_smul a f1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.smul_apply, f2 u hu hu' x]
  · exact (coeffSpan (ρ τ)).smul_mem a (f3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul, f4, smul_comm]

theorem zero_mem_formsOn : (0 : GA D V → ℂ) ∈ formsOn θ V X Y S U ε fr ρ c := by
  refine ⟨isSmModOn_const _ _ _ 0, fun _ _ _ _ => rfl, fun τ x => (coeffSpan (ρ τ)).zero_mem, fun τ k => ?_⟩
  have := (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 0
  simpa using this

theorem const_mem_formsOn (a : ℂ) :
    (fun _ => a) ∈ formsOn θ V X Y S U ε fr (fun τ => Representation.trivial ℂ (Formalism.REAL.KG (ε τ)) ℂ) (fun _ _ => 0) :=
  have h := const_mem_forms (θ := θ) (V := V) U ε fr a
  ⟨isSmModOn_const _ _ _ a, h.2.1, h.2.2.1, h.2.2.2⟩

theorem mem_formsOn_of_mem_span (hθ : IsInfFam θ) {f : GA D V → ℂ}
    (hf : f ∈ Submodule.span ℂ (formsOn θ V X Y S U ε fr ρ c)) : f ∈ formsOn θ V X Y S U ε fr ρ c := by
  induction hf using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact zero_mem_formsOn
  | add x y _ _ hx hy => exact formsOn_add hθ hx hy
  | smul a x _ hx => exact formsOn_smul a hx

end Sub

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
