import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

namespace GlobalTheory.SiegLoc

theorem keepsRegular_siegPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ φs : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → AgreesPsd (Module.finrank ℚ E / 2 * (D.p + D.q)) φs φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) → IsSiegPull s j G e κ C π → BD.KeepsRegular π := by
  intro E _ _ _ H D l Xo c n R _ b ω φ φs F S s j _ G _ e BD d N κ C π _ hn3 _ _ hφ _ hω _ _ hS _ hP
  obtain ⟨-, -, -, -, -, -, -, -, hd, hch, -⟩ := hS
  obtain ⟨μ, y, α, α₂, -, -, -, hyj, -⟩ := hP
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hω
  letI : Algebra R c.F := ω.toAlgebra
  have hg := GlobalTheory.genericPart_dense_proOpen R c.F C.X (Xo.XF c) C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  haveI hdom : IsDominant (C.jQ ≫ pullback.fst C.s (spMap (algebraMap R c.F))) := hg.2.2.2.2.2.1
  refine GlobalTheory.EffCartierData.keepsRegular_of_dense BD π (fun z => (C.normal z).1) ?_
  refine (Scheme.Hom.denseRange (C.jQ ≫ pullback.fst C.s (spMap (algebraMap R c.F)))).mono ?_
  rintro _ ⟨w, rfl⟩
  show π (C.j w) ∉ _
  have e1 : π (C.j w) = j (y w) := by
    rw [← Scheme.Hom.comp_apply, ← hyj, Scheme.Hom.comp_apply]
  rw [e1]
  intro hmem
  exact (ReciprocityTheory.AnForm.R.mem_support_iff_stalkId _ _).1 hmem
    ((HasChart.idl_eq_top_iff hφ (by omega) (by omega) (hch (j (y w)))).2 ⟨y w, rfl⟩)

end GlobalTheory.SiegLoc
