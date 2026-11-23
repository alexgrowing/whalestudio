import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.Height

theorem isDiscMap_comp' {l : ℕ} {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A'']
    {u : A} {u' : A'} {u'' : A''} {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {g : A' →+* A''}
    {F : Disc l u ρ →+* Disc l u' ρ'} {G : Disc l u' ρ' →+* Disc l u'' ρ''}
    (hF : IsDiscMap f F) (hG : IsDiscMap g G) : IsDiscMap (g.comp f) (G.comp F) :=
  ⟨fun a => by simp [hF.ext, hG.ext], fun x => (hG.norm_le _).trans (hF.norm_le x)⟩

theorem rel_map : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B B' : Obj l ↥(OL K)) (f₀ f g : Hom bk.prism B) (f₀' : Hom bk.prism B') (k : Hom B B') (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → (∃ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap k.f Fk) ∧ ∀ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap k.f Fk → ht.Rel (BK.hf f₀' X) (k.comp f) (k.comp g) (ε.map Fk) := by
  intro l _ K bk d ρ τ s ht B B' f₀ f g f₀' k ε hrel
  have hk : ‖toDisc l (BK.hf f₀' X) bk.ρ₀ (k.f (BK.hf f₀ X))‖ ≤ bk.ρ₀ :=
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B' f₀' (k.comp f₀)).1
  refine ⟨⟨Disc.map k.f hk, isDiscMap_map k.f hk⟩, ?_⟩
  intro Fk hFk Ff' Fg' hf' hg'
  have hff := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ f).1
  have hgg := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ g).1
  have h := congrArg (fun M => Matrix.map M Fk)
    (hrel _ _ (isDiscMap_map (BK.hf f) hff) (isDiscMap_map (BK.hf g) hgg))
  have e1 : Fk.comp (Disc.map (BK.hf f) hff) = Ff' :=
    (isDiscMap_comp' (isDiscMap_map (BK.hf f) hff) hFk).unique hf'
  have e2 : Fk.comp (Disc.map (BK.hf g) hgg) = Fg' :=
    (isDiscMap_comp' (isDiscMap_map (BK.hf g) hgg) hFk).unique hg'
  subst e1 e2
  ext i j
  have h2 := congrFun (congrFun h i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_mul, map_pow, map_sum, smul_eq_mul,
    hFk.ext, RingHom.comp_apply] at h2 ⊢
  exact h2

end GlobalTheory.BSP.Height
