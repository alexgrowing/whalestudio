import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt

namespace GlobalTheory.PetAdd

theorem cnorm_add_le {ι : Type} [Fintype ι] (u w : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u + w) ≤ Formalism.HermitianLatticesTheory.cnorm u + Formalism.HermitianLatticesTheory.cnorm w := by
  have key : ∀ t : ι → ℂ, Formalism.HermitianLatticesTheory.cnorm t = ‖(WithLp.equiv 2 (ι → ℂ)).symm t‖ := fun t => by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [key, key, key]
  have e : (WithLp.equiv 2 (ι → ℂ)).symm (u + w) = (WithLp.equiv 2 (ι → ℂ)).symm u + (WithLp.equiv 2 (ι → ℂ)).symm w := by
    first | exact WithLp.equiv_symm_add 2 u w | rfl | simp
  rw [e]
  exact norm_add_le _ _

theorem IsGram.add_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {ι : Type} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (v : InfinitePlace K) (f g : V) :
    N v.embedding (f + g) ≤ N v.embedding f + N v.embedding g := by
  rw [← (h v).2, ← (h v).2, ← (h v).2]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  have : Formalism.HermitianLatticesTheory.vecAt b v (f + g) = Formalism.HermitianLatticesTheory.vecAt b v f + Formalism.HermitianLatticesTheory.vecAt b v g := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [this, Matrix.mulVec_add]
  exact cnorm_add_le _ _

end GlobalTheory.PetAdd

namespace GlobalTheory.PetAdd

theorem normOn_add_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), GoodOn U x V dict Z G → ∀ σ (f g : cuspOn U Z G), normOn U x V dict Z G σ (f + g) ≤ normOn U x V dict Z G σ f + normOn U x V dict Z G σ g := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G h σ f g
  obtain ⟨n, ⟨p, hp⟩⟩ := h.1
  have hconj : ∀ y, normOn U x V dict Z G ((starRingEnd ℂ).comp σ) y = normOn U x V dict Z G σ y :=
    fun y => GlobalTheory.CompHt.petOn_conj U x V dict Z G σ y
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    rwa [e] at this
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    have e' : (InfinitePlace.mk σ).embedding = (starRingEnd ℂ).comp σ := by
      rw [e]; ext a; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e', hconj, hconj, hconj] at this
    exact this

end GlobalTheory.PetAdd
