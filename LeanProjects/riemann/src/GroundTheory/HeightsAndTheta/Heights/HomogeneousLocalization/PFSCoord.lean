import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

lemma X_pow_mem_grading (j : Fin (N + 1)) (n : ℕ) :
    (MvPolynomial.X j ^ n : MvPolynomial (Fin (N + 1)) A) ∈ ProjSpace.grading A N n := by
  simpa using SetLike.pow_mem_graded n (ProjSpace.X_mem (A := A) (n := N) j)

def fracOn {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ ProjSpace.grading A N n)
    (j : Fin (N + 1)) : ringOn (self A N).X (ProjSpace.stdOpen A N j) :=
  (Proj.awayToSection (ProjSpace.grading A N) (MvPolynomial.X j)).hom
    (HomogeneousLocalization.mk ⟨n, ⟨P, hP⟩, ⟨MvPolynomial.X j ^ n, X_pow_mem_grading j n⟩, ⟨n, rfl⟩⟩)

lemma resM_polySection {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ ProjSpace.grading A N n)
    (j : Fin (N + 1)) :
    resM ((preMod (self A N).X).obj (twistN A N n)) le_top
        (polySection hP : ((preMod (self A N).X).obj (twistN A N n)).obj (op ⊤)) =
      fracOn hP j • stdFrame A j n := by
  apply ProjTwist.ext (k := (n : ℤ)) (U := ProjSpace.stdOpen A N j)
  funext x
  change Localization.mk P 1 = ((fracOn hP j).1 x).val *
    ProjTwist.val (k := (n : ℤ)) (U := Proj.basicOpen (ProjSpace.grading A N) (MvPolynomial.X j))
      (ProjTwist.upow (ProjSpace.grading A N) (ProjSpace.X_mem j) (n : ℤ)) x
  erw [ProjTwist.val_upow]
  change Localization.mk P 1 = (HomogeneousLocalization.mk _).val * _
  rw [HomogeneousLocalization.val_mk]
  unfold ProjTwist.twistFrac
  rw [Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, Int.toNat_natCast]
  simp
  ring

lemma evalAtPoint_fracOn {ρ : A →+* ℂ} (x : (self A N).complexPoints ρ) {j : Fin (N + 1)}
    (hp : (self A N).point x ∈ ProjSpace.stdOpen A N j) {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) :
    (self A N).evalAtPoint x (germR (X := (self A N).X) hp (fracOn hP j)) = evalAt ρ x.1.rep P / x.1.rep j ^ n := by
  have e := Scheme.Hom.germ_stalkMap_apply (self A N).ι (ProjSpace.stdOpen A N j) ((self A N).point x)
    hp (fracOn hP j)
  have e2 : germR (X := (self A N).X) hp (fracOn hP j) = ((self A N).ι.stalkMap ((self A N).point x)).hom
      ((projectiveSpace A N).presheaf.germ (ProjSpace.stdOpen A N j)
        ((self A N).ι.base ((self A N).point x)) hp (fracOn hP j)) := by
    rw [e]
    rfl
  rw [e2]
  change (self A N).evalStalk ((self A N).isOver_point x) _ = _
  rw [evalStalk_stalkMap]
  unfold evalStalkProj
  rw [RingHom.comp_apply]
  have e1 : (Proj.stalkIso (ProjSpace.grading A N) _).hom.hom
      ((projectiveSpace A N).presheaf.germ (ProjSpace.stdOpen A N j)
        ((self A N).ι.base ((self A N).point x)) hp (fracOn hP j)) = (fracOn hP j).1 ⟨_, hp⟩ :=
    Proj.stalkIso'_germ _ _ _ hp _
  rw [e1]
  refine (evalAtPrime_mk _ _).trans ?_
  simp [evalAt]

lemma fibreEquivComplex_fibreMk {X : Scheme.{u}} {L : X.Modules} {p : X} {φ : locRing X p →+* ℂ}
    {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) (r : locRing X p) :
    fibreEquivComplex φ hp he (fibreMk L φ 1 (r • germM hp e)) = φ r := by
  have h := fibreEquiv_fibreMk (φ := φ) hp he 1 r
  rw [mul_one] at h
  exact (congrArg (Via.ofComplex φ).symm h).trans (RingEquiv.symm_apply_apply _ _)

theorem FSCoord.proof : FSCoord.Statement.{u} := by
  intro A _ N n ρ P hP x j hj
  have hp := point_mem_stdOpen x hj
  have hg := (germM_resM (X := (self A N).X) (le_top : ProjSpace.stdOpen A N j ≤ ⊤) hp
      (polySection hP : ((preMod (self A N).X).obj (twistN A N n)).obj (op ⊤))).symm.trans
    ((congrArg (germM (X := (self A N).X) hp) (resM_polySection hP j)).trans (germM_smul hp _ _))
  have hv : (self A N).evalGlobalSection (twistN A N n) x (polySection hP) =
      fibreMk _ ((self A N).evalAtPoint x) 1
        (germR (X := (self A N).X) hp (fracOn hP j) • germM (X := (self A N).X) hp (stdFrame A j n)) :=
    congrArg (fibreMk _ ((self A N).evalAtPoint x) 1) hg
  have key := (congrArg (fibreEquivComplex ((self A N).evalAtPoint x) hp
      (isBasisOn_frame (A := A) j n)) hv).trans
    ((fibreEquivComplex_fibreMk hp (isBasisOn_frame (A := A) j n) _).trans (evalAtPoint_fracOn x hp hP))
  exact (congrArg (· * x.1.rep j ^ n) key).trans (div_mul_cancel₀ _ (pow_ne_zero _ hj))

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
