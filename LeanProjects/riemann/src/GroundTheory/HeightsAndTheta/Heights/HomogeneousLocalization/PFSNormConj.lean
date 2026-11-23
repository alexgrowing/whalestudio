import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma fibreEquivComplex_value_eq {X : Scheme.{u}} {L : X.Modules} {p : X}
    (φ : locRing X p →+* ℂ) {U V : X.Opens} (hpU : p ∈ U) (hpV : p ∈ V)
    {e : ((preMod X).obj L).obj (op V)} (he : IsBasisOn ((preMod X).obj L) V e)
    (s : ((preMod X).obj L).obj (op U)) (r : locRing X p) (hr : germM hpU s = r • germM hpV e) :
    fibreEquivComplex φ hpV he (value φ hpU s) = φ r := by
  change (Via.ofComplex φ).symm (fibreEquiv φ hpV he (fibreMk L φ 1 (germM hpU s))) = φ r
  rw [hr, fibreEquiv_fibreMk, mul_one, RingEquiv.symm_apply_apply]

theorem FSNormConj.proof (h : FSIndex.Statement.{u}) : FSNormConj.Statement.{u} := by
  intro A _ N n ρ U s x hx hx'
  obtain ⟨j, hj⟩ : ∃ j, x.1.rep j ≠ 0 := ⟨_, rep_chartIndex_ne_zero x.1⟩
  obtain ⟨c, hc⟩ := exists_rep_conj x.1
  have hcj : (CP.conj x.1).rep j = (c : ℂ) * starRingEnd ℂ (x.1.rep j) := by
    rw [hc, Pi.smul_apply, smul_eq_mul, CP.conjVec_apply]
  have hj' : ((self A N).conjPoint ρ x).1.rep j ≠ 0 := by
    change (CP.conj x.1).rep j ≠ 0
    rw [hcj]
    exact mul_ne_zero c.ne_zero ((map_ne_zero _).mpr hj)
  have hpj := point_mem_stdOpen x hj
  obtain ⟨r, hr⟩ := (bijective_smul_germ hpj (isBasisOn_frame (A := A) j n)).2 (germM hx s)
  obtain ⟨V, -, hpV, f, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (X := (self A N).X.toTopCat) (self A N).X.sheaf.obj r hx
  have key : ∀ (q : (self A N).X) (_ : q = (self A N).point x) (φ : locRing (self A N).X q →+* ℂ)
      (hqU : q ∈ U) (hqj : q ∈ ProjSpace.stdOpen A N j) (hqV : q ∈ V),
      fibreEquivComplex φ hqj (isBasisOn_frame (A := A) j n) (value φ hqU s) = φ (germR hqV f) := by
    intro q hq φ hqU hqj hqV
    subst hq
    exact fibreEquivComplex_value_eq φ hqU hqj _ s _ hr.symm
  have hV' : (self A N).point ((self A N).conjPoint ρ x) ∈ V := by
    rw [point_conjPoint]
    exact hpV
  have hj'' := point_mem_stdOpen _ hj'
  rw [h A N n _ _ j hj', h A N n ρ x j hj]
  unfold sectionValue
  rw [key _ (point_conjPoint _ x) _ hx' hj'' hV', key _ rfl _ hx hpj hpV,
    evalAtPoint_conjPoint_germ _ x hpV hV', Complex.norm_conj]
  have hn : norm2 (CP.conj x.1).rep = ‖(c : ℂ)‖ * norm2 x.1.rep := by
    rw [hc, euclideanNorm_smul]
    congr 1
    simp [norm2, normSq2, CP.conjVec_apply]
  have hc0 : 0 < ‖(c : ℂ)‖ := norm_pos_iff.mpr c.ne_zero
  change _ * ‖(CP.conj x.1).rep j‖ ^ n / norm2 (CP.conj x.1).rep ^ n = _
  rw [hn, hcj, norm_mul, Complex.norm_conj, mul_pow, mul_pow]
  field_simp

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
