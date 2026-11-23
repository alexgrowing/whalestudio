import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PerGam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma perFr_lact (X : Data E r) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = perFr X x v τ i := by
  have hm : ∀ t : X.Ψ, mat (lact γ x) t = (γ : Matrix (Fin r) (Fin r) E).map t.1 * mat x t := fun _ => rfl
  have hu : ∀ t : E →+* ℂ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map t).det := fun t =>
    (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map t.mapMatrix)
  unfold perFr
  simp only [hm, GlobalTheory.PerMove.emb_mulVec]
  split_ifs
  · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _),
      Matrix.mul_one]
  · rfl
  · rw [GlobalTheory.PerMove.col_mul, GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
  · rfl
  · rfl

omit [IsCMField E] in

lemma exists_equiv (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (hγ : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ) :
    ∃ f : Λ ≃ₗ[𝓞 E] Λ, ∀ a, (f a : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) := by
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨{ toFun := fun a => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E), (hγ _).1 a.2⟩
            invFun := fun a => ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E),
              (hγ _).2 (by rw [hri]; exact a.2)⟩
            map_add' := fun a b => Subtype.ext (by simp [Matrix.mulVec_add])
            map_smul' := fun s a => Subtype.ext (by simp [Matrix.mulVec_smul])
            left_inv := fun a => Subtype.ext (hli _)
            right_inv := fun a => Subtype.ext (hri _) }, fun _ => rfl⟩

end GlobalTheory.PerGam

namespace GlobalTheory

theorem per_gam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ γ ∈ (M.X k).Γ, ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La, ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) ∧ ∀ x ∈ (M.X k).dom, ∀ a, Pf (lact γ x) (gam a) = Pf x a := by
  intro E _ _ _ H Dw l Xo c σ g e F r M _ hB _ k Pf hP γ hγ
  obtain ⟨⟨hU, hS⟩, hM, hA⟩ := (hB.gam k γ).1 hγ
  obtain ⟨f, hf⟩ := PerGam.exists_equiv _ γ hS
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans (f.trans (M.φ k).symm)
  have hg : ∀ a, (M.φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
    intro a
    rw [← hf]
    simp [gam]
  have key : ∀ (n : ℕ) (a b : (F.Di k).La),
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + n • (M.φ k b : Fin r → E) → gam a = a + n • b := by
    intro n a b h
    apply (M.φ k).injective
    apply Subtype.ext
    rw [hg, h, map_add, map_nsmul]
    rfl
  refine ⟨gam, ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩, fun x _ a => ?_⟩
  · have h1 := hB.ef k (gam a) (gam b)
    rw [hg, hg, hU, ← hB.ef k a b] at h1
    exact_mod_cast h1
  · obtain ⟨b, hb⟩ := hM a ha
    exact ⟨b, key _ a b hb⟩
  · obtain ⟨b, hb⟩ := hA a
    exact ⟨b, key _ a b hb⟩
  · funext j
    rw [hP, hP, hg, PerGam.perFr_lact _ γ hU]

end GlobalTheory
