import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.EtaTildeShift

theorem sh_half : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (t : D.what₂.Tau) (sh : ℂ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → ∃ z : ℤ, sh = (z : ℂ) + 1 / 2 := by
  intro D cf jE A t sh h
  have hE : (A.chr.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [A.chr.etaT]; exact cf.isEta.inf⟩
  have h2 := (A.chr.infG _ _ hE (D.eTau t)).1
  have h3 : D.naut.infG D.naut.etaT (embT D t) = {((1 / 2 : ℚ) : ℂ)} := h2
  rw [h3] at h
  have := (Multiset.singleton_inj.1 h).symm
  refine ⟨0, ?_⟩
  rw [this]; push_cast; ring

end GlobalTheory.EtaTildeShift
