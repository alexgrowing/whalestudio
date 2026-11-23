import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst

noncomputable section

namespace GlobalTheory.RecDict

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology

variable {D : D7}

def gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) : Matrix (Fin r) (Fin r) D.host.E :=
  -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} {r : ℕ}

def RecOK (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  GlobalTheory.FrameUnif.ModelBase M ∧ (∀ k, ModelW V hr (M.X k)) ∧ LatEmb V io ∧
    (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (gmW V hr) (io x ∘ Fin.cast hr.symm) (io y ∘ Fin.cast hr.symm))) ∧
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ ∀ k, IsOrthogonalFrame (M.X k) x₀

def MarkSpec (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : GA D V) (p : Σ k, Frame (M.X k).Ψ r) : Prop :=
  ∃ γ ∈ GQ V,
      ((M.X p.1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((M.φ p.1 (F.t p.1 a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (M.X p.1).Ψ, mat p.2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) (γ * h)) * x₀ τ.1

end GlobalTheory.RecDict
