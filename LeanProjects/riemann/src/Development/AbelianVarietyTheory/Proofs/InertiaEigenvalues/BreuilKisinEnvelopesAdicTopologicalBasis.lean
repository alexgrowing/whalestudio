import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisExistsCompStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envelopes_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X))
    (En₂ : Env bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)),
    Nonempty (TopBasis (BK.hf En.inl) bk.J (Digits l)) ∧
      ∃ ι : Type, Nonempty (TopBasis (BK.hf (En₂.inl.comp En.inl)) bk.J ι) := by
  intro l _ K bk En En₂
  have h1 : bk.J.map (BK.hf En.inl) =
      Ideal.span {(BK.hf En.inl) (l : bk.S)} ⊔ Ideal.span {(BK.hf En.inl) bk.E} := by
    simp only [BK.J, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have h2 : (BK.hf En.inl) (l : bk.S) = (l : En.Q.A) := map_natCast (BK.hf En.inl) l
  have h3 : En.Q.I = Ideal.span {(BK.hf En.inl) bk.E} := En.I_eq
  have hI : Ideal.span {(l : En.Q.A)} ⊔ En.Q.I = bk.J.map (BK.hf En.inl) :=
    (h1.trans (congrArg₂ (· ⊔ ·) (congrArg (fun x => Ideal.span {x}) h2) h3.symm)).symm
  have T₁ : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have T₂ : TopBasis En₂.inl.f (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) := En₂.tb
  have key := GlobalTheory.T.adicTopologicalBasis_exists_comp bk.S En.Q.A (BK.hf En.inl) bk.J (Digits l) T₁ En₂.Q.A En₂.inl.f
    (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) T₂ hI
  exact ⟨⟨T₁⟩, Digits l × Digits l, key.elim fun TC _ => ⟨TC⟩⟩

end GlobalTheory.BSP
