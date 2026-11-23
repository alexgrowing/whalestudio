import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

namespace GlobalTheory.LatConjSplit

open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

noncomputable section

theorem toMatrix'_mul_symm {R : Type} [CommRing R] (a : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.toMatrix' (a : (Fin n → R) →ₗ[R] (Fin n → R)) * LinearMap.toMatrix' (a.symm : (Fin n → R) →ₗ[R] (Fin n → R)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.toMatrix'_id]

theorem toMatrix'_symm_mul {R : Type} [CommRing R] (a : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.toMatrix' (a.symm : (Fin n → R) →ₗ[R] (Fin n → R)) * LinearMap.toMatrix' (a : (Fin n → R) →ₗ[R] (Fin n → R)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.toMatrix'_id]

def compAt (τ : E →ₐ[F] Fv F v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    GL (Fin n) (Fv F v) where
  val := (LinearMap.toMatrix' (a : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ)
  inv := (LinearMap.toMatrix' (a.symm : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ)
  val_inv := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, toMatrix'_mul_symm, map_one]
  inv_val := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, toMatrix'_symm_mul, map_one]

theorem compAt_val (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    (compAt τ a).1 = (LinearMap.toMatrix' (a : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ) := rfl

theorem compAt_inv_val (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    ((compAt τ a)⁻¹).1 = (LinearMap.toMatrix' (a.symm : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ) := rfl

theorem splitVec_apply_equiv (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (a y) = (compAt τ a).1 *ᵥ splitVec τ y := by
  rw [compAt_val, ← splitVec_mulVec, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

theorem splitVec_symm_apply_equiv (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (a.symm y) = (compAt τ a)⁻¹.1 *ᵥ splitVec τ y := by
  rw [compAt_inv_val, ← splitVec_mulVec, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

theorem splitHom_conj (hc : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {J J' : Matrix (Fin n) (Fin n) E}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h3 : ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)) (g : GLoc σ J v) :
    splitHom σ J' τ (j g) = compAt τ a * splitHom σ J τ g * (compAt τ a)⁻¹ := by
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun u => ?_))
  obtain ⟨y, rfl⟩ : ∃ y, splitVec τ y = u := ⟨splitIncl hc τ u, splitVec_splitIncl hc τ u⟩
  simp only [Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [← splitVec_matHom_mulVec, ← splitVec_symm_apply_equiv, ← splitVec_matHom_mulVec, ← splitVec_apply_equiv, ← h3,
    LinearEquiv.apply_symm_apply]

theorem conj_mem_stabLoc_iff {J J' : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h2 : ∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v)
    (h3 : ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)) (g : GLoc σ J v) :
    j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v := by
  rw [mem_stabLoc, mem_stabLoc]
  constructor
  · intro H y
    have := H (a y)
    rwa [h3, h2, h2] at this
  · intro H y'
    obtain ⟨y, rfl⟩ := a.surjective y'
    rw [h3, h2, h2]
    exact H y

theorem isSplitBasis_conj {L L' : Submodule (𝓞 E) (Fin n → E)}
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h2 : ∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v) (τ : E →ₐ[F] Fv F v) {β : GL (Fin n) (Fv F v)}
    (hβ : IsSplitBasis τ L β) : IsSplitBasis τ L' (compAt τ a * β) := by
  intro u
  rw [hβ u, Units.val_mul, ← Matrix.mulVec_mulVec]
  generalize β.1 *ᵥ u = z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a y, (h2 y).2 hy, splitVec_apply_equiv τ a y⟩
  · rintro ⟨y', hy', e⟩
    refine ⟨a.symm y', (h2 _).1 (by rwa [a.apply_symm_apply]), ?_⟩
    rw [splitVec_symm_apply_equiv, e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem split_conj {J J' : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (hj : IsLatticeConj L L' j) (hJ' : IsHermND σ J')
    (hL' : IsSelfDualAt σ J' L' v) :
    (∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) ∧ ∀ s : SplitAt σ J L v, ∃ s' : SplitAt σ J' L' v,
      (∀ g, s'.equiv (j g) = s.equiv g) ∧
      ∀ (k : stabLoc σ J L v) (k' : stabLoc σ J' L' v), (k' : GLoc σ J' v) = j k → s'.red k' = s.red k := by
  obtain ⟨a, -, h2, h3⟩ := hj
  refine ⟨conj_mem_stabLoc_iff j a h2 h3, fun s => ⟨⟨s.emb, compAt s.emb a * s.basis, s.cm, hJ', hL',
    isSplitBasis_conj a h2 s.emb s.isBasis⟩, ?_⟩⟩
  have he : ∀ g, splitEquivIn s.cm hJ' s.emb (compAt s.emb a * s.basis) (j g) = s.equiv g := fun g => by
    rw [splitEquivIn_apply, splitHom_conj s.cm s.emb j a h3, SplitAt.equiv, splitEquivIn_apply]
    group
  refine ⟨he, fun k k' hk => ?_⟩
  apply Units.ext
  simp only [SplitAt.red, splitRed_val]
  congr 1
  ext i l
  rw [coe_stabLocEquiv, coe_stabLocEquiv, hk]
  exact congrArg _ (congrArg (fun x => x.1 i l) (he k))

theorem split_conj_cast {n' : ℕ} (hr : n' = n) {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
    {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} (j : GLoc σ J v ≃ₜ* GLoc σ J' v)
    (hj : IsLatticeConj L L' j) (hJ' : IsHermND σ J') (hL' : IsSelfDualAt σ J' L' v) :
    (∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) ∧ ∀ s : SplitAt σ J L v, ∃ s' : SplitAt σ J' L' v,
      (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧
      ∀ (k : stabLoc σ J L v) (k' : stabLoc σ J' L' v), (k' : GLoc σ J' v) = j k →
        ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  subst hr
  obtain ⟨h1, h2⟩ := split_conj j hj hJ' hL'
  refine ⟨h1, fun s => ?_⟩
  obtain ⟨s', e1, e2⟩ := h2 s
  exact ⟨s', fun g a b => by rw [e1]; rfl, fun k k' hk a b => by rw [e2 k k' hk]; rfl⟩

end

end GlobalTheory.LatConjSplit

theorem GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj : ∀ (D : D7) (V V' : HSp D) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → (∀ g, j g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ s : SplitAt D.sp.cm.sig V.gram (frameLat V) v, ∃ s' : SplitAt D.sp.cm.sig V'.gram (frameLat V') v, (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧ ∀ (k : Kv V v) (k' : Kv V' v), (k' : GLoc D.sp.cm.sig V'.gram v) = j k → ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  intro D V V' hr v j hj
  exact GlobalTheory.LatConjSplit.split_conj_cast hr j hj (GlobalTheory.Orb.isHermND_gram V') (SelfDual.isSelfDualAt_frameLat D V' v)
