import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSectionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem existsUnique_comb_matrix {S N : Type} [CommRing S] [AddCommGroup N] [Module S N] {n : ℕ}
    (b : Fin n → N) (g : Matrix (Fin n) (Fin n) S) (hg : IsUnit g.det) (m : N)
    (h : ∃! a : Fin n → S, m = ∑ i, a i • b i) :
    ∃! a : Fin n → S, m = ∑ i, a i • ∑ j, g i j • b j := by
  have key : ∀ a : Fin n → S, ∑ i, a i • ∑ j, g i j • b j = ∑ j, (Matrix.vecMul a g) j • b j := by
    intro a
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
  obtain ⟨a, ha, hu⟩ := h
  refine ⟨Matrix.vecMul a g⁻¹, ?_, fun a' ha' => ?_⟩
  · show m = _
    rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hg, Matrix.vecMul_one]
    exact ha
  · have h1 := hu (Matrix.vecMul a' g) (Eq.trans ha' (key a'))
    rw [← h1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hg, Matrix.vecMul_one]

theorem existsUnique_frChg (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ)
    (hg : ∀ τ, IsUnit (g τ).det) : ∃! y' : FrPt Xo c S, FrChg g (a : S) y y' := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S y.x
  have hid : y.x = spMap (RingHom.id S) ≫ y.x := by
    have : spMap (RingHom.id S) = 𝟙 (Sp S) := by
      simp [spMap]
    rw [this, Category.id_comp]
  obtain ⟨-, hbc, -, hsc⟩ := GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x hid hid
  obtain ⟨s', hs', hs'u⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S S (RingHom.id S) (a : S) y.x y.x hid y.s
  have heig : ∀ τ m, IsEigAt c τ (v m) ↔ ∀ z : 𝓞 E, ρ z m = algebraMap c.F S (embK c τ z) • m := by
    intro τ m
    refine forall_congr' fun z => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  choose b hb using fun τ i => (htan (y.u τ i)).1 (y.tan τ i)
  have hbu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  have hs'f := (hbc (a : S) y.s s').1 hs'
  refine ⟨⟨y.x, y.x_over, fun τ i => v (∑ j, g τ i j • b τ j), fun τ i => (htan _).2 ⟨_, rfl⟩,
    fun τ i => ?_, fun τ w hw hwe => ?_, s', fun t => ?_⟩, ⟨rfl, fun τ i => ?_, hs'⟩, ?_⟩
  · rw [heig]
    intro z
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (heig τ (b τ j)).1 (by rw [hb]; exact y.eig τ j) z
    rw [map_smul, this, smul_comm]
  · have h := y.basis τ w hw hwe
    obtain ⟨m, rfl⟩ := (htan w).1 hw
    rw [hbu τ] at h
    simp only [hcomb, hinj.eq_iff] at h ⊢
    exact existsUnique_comb_matrix (b τ) (g τ) (hg τ) m h
  · obtain ⟨e, he, heu⟩ := y.gen t
    refine ⟨e * (a⁻¹ : Sˣ), fun i => ?_, fun e' he' => ?_⟩
    · rw [hs'f, ← _root_.mul_assoc, ← (hsc _ _ i).1, Units.inv_mul_cancel_right]
      exact he i
    · have := heu (e' * a) (fun i => by rw [(hsc _ _ i).1, _root_.mul_assoc, ← hs'f]; exact he' i)
      rw [← this, Units.mul_inv_cancel_right]
  · rw [hbu τ, hcomb]
  · rintro ⟨x', hx', u', ht', he', hb', t', hg'⟩ ⟨hx, hu, hs⟩
    dsimp only at hx hu hs
    subst hx
    have e1 : t' = s' := hs'u t' hs
    have e2 : u' = fun τ i => v (∑ j, g τ i j • b τ j) := by
      funext τ i
      have := hu τ i
      rw [hbu τ, hcomb] at this
      exact this
    subst e1 e2
    rfl

end GlobalTheory.Frames
