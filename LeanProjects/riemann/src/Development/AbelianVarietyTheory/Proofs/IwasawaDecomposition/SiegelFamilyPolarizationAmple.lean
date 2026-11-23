import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyNormalCompactifyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilySemiabelianExtendsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

noncomputable section

namespace GlobalTheory.SiegLoc.PolPull

theorem evalZ_comb {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (a : ℕ)
    (ψ : InvFun O) (b : ℕ) (φ : InvFun O) (β : LinearMap.BilinForm ℤ X) :
    (comb a ψ b φ).evalZ β = a * ψ.evalZ β + b * φ.evalZ β := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  unfold InvFun.evalZ
  rw [(comb a ψ b φ).eval_eq hr, ψ.eval_eq hr, φ.eval_eq hr]
  rfl

theorem polRay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ φs : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → AgreesPsd (Module.finrank ℚ E / 2 * (D.p + D.q)) φs φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) → IsSiegPull s j G e κ C π → PolRay (comb 0 (resInt _ φs) 0 (resInt _ φs)) (resInt _ φs) 1 C := by
  intro E _ _ _ H D l Xo c n R _ b ω φ φs F S s j _ G _ e BD d N κ C π hpq h3 hodd hn hφ hφs hω hωb hloc hD hκ hC
  have h := GlobalTheory.T.siegel_family_normal_compactify E H D l Xo c n R b ω φ φs F S s j G e BD d N κ C π hpq h3 hodd hn hφ hφs hω hωb hloc hD hκ hC
  have hB := GlobalTheory.T.siegel_family_proper_extension E H D l Xo c n R b ω φ φs F S s j G e BD d N κ C π h hpq h3 hodd hn hφ hφs hω hωb hloc hD hκ hC
  obtain ⟨-, -, -, -, -, -, -, -, hd, -, hN, -, k₀, hk₀⟩ := id hD
  refine ⟨d, N, k₀, hd, hN, fun T hT => ⟨BD.pull π h, ?_, ?_⟩⟩
  · intro W _ _ _ hW ϖ hϖ χ t m P hgen be hbe hmon
    obtain ⟨k, hk, hI⟩ := hB W hW ϖ hϖ χ t m P hgen be hbe hmon
    refine ⟨k, ?_, hI⟩
    rw [hk, evalZ_comb, evalZ_comb, evalZ_comb]
    ring
  · rw [mul_one]
    exact GlobalTheory.T.siegel_family_semiabelian_extends E H D l Xo c n R b ω φ φs F S s j G e BD d N κ C π h (N * T) hpq h3 hodd hn hφ hφs hω hωb hloc hD
      hκ hC (hk₀ T hT)

end GlobalTheory.SiegLoc.PolPull
