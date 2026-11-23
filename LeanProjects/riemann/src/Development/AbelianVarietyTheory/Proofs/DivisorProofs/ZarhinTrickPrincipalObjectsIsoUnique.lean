import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationUnitKernelLeKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationKernelLeUnitKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickActionsIsomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickBundleUniqueOfOrderLinearIsoStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem actPB_of_zRel : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d _ _ _ hd _ jl n o κ S t c z₁ z₂ act₁ act₂ hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂ hZ₁ hZ₂
  obtain ⟨inc₁, pr₁, hi₁, hp₁, hip₁, hpi₁, hL₁, -, hz₁⟩ := hZ₁
  obtain ⟨inc₂, pr₂, hi₂, hp₂, hip₂, hpi₂, hL₂, -, hz₂⟩ := hZ₂
  have hker : ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔
      x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1 := fun T x =>
    ⟨fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x hx),
     fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x hx)⟩
  obtain ⟨e, he, hinc, hact⟩ := GlobalTheory.T.zarhinTrick_actions_isomorphic h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ pr₂ hdS hA₁ hA₂
    hi₁ hp₁ hip₁ hpi₁ hi₂ hp₂ hip₂ hpi₂ hker
  have hLB := GlobalTheory.T.zarhinTrick_bundle_unique_of_order_linear_iso h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ e hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂
    hi₁ hp₁ hip₁ hpi₁ hL₁ hL₂ he hinc hact
  haveI := he
  refine ⟨e.hom.left, (e.hom ⊗ₘ e.hom).left, isGrpPullback_of_iso e, ⟨?_, ?_⟩, hLB, fun a => ?_, fun o => ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  · rw [Category.id_comp, ← Over.comp_left, hz₁ a, hz₂ a]
    congr 1
    have key := map_list_prod (IsMonHom.monoidHom e.hom (𝟙_ (Over S)))
      (List.ofFn fun k => c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))
    refine key.trans ?_
    rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    show (c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)) ≫ e.hom = _
    rw [Category.assoc, Category.assoc, hact, ← Category.assoc inc₁, hinc]
  · rw [← Over.comp_left, ← Over.comp_left, hact o]

end GlobalTheory.ZarhinFam
