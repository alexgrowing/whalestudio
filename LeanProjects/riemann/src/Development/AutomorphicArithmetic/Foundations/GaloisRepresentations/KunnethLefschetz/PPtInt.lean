import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pb_id' (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) : pb l (𝟙 X) n z = z := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem slice_gen {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (R : Ring l) {X : Scheme.{0}} {p : X ⟶ S k}
    (y : Pt p) {a b n : ℤ} (h : a + b = n) (u : V l X a) (v : V l X b) :
    pb l (slice y) n (ext2 l p h u v) = cupV l X h u (pb l p b (pb l y.1 b v)) := by
  simp only [ext2]
  rw [R.nat (slice y) a b n h]
  have e1 : pb l (slice y) a (pb l (pullback.fst p p) a u) = u := by
    rw [← LinearMap.comp_apply, ← pb_comp]
    simp only [slice, pullback.lift_fst]
    exact pb_id' l X a u
  have e2 : pb l (slice y) b (pb l (pullback.snd p p) b v) = pb l p b (pb l y.1 b v) := by
    rw [← LinearMap.comp_apply, ← pb_comp, ← LinearMap.comp_apply, ← pb_comp]
    simp only [slice, pullback.lift_snd]
  rw [e1, e2]

theorem ptInt_holds : PtInt := by
  intro l _ k _ _ hl d X p hSP R L K lam Λ hΛ y w
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunitS : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  have key : (pb l y.1 0) ∘ₗ Λ =
      (lam ∘ₗ pb l (slice y) (2 * d)).smulRight (oneV l (S k)) := by
    apply LinearMap.ext_on (K.span (2 * d))
    rintro _ ⟨a, b, hab, u, v, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.smulRight_apply]
    rw [slice_gen R y hab u v]
    by_cases hb : b = 0
    · subst hb
      have ha : a = 2 * d := by omega
      subst ha
      obtain ⟨r, hr, -⟩ := L.line (pb l y.1 0 v)
      rw [hΛ.1, map_smul, hr]
      simp only [map_smul, R.one_nat p hunitS, R.mul_one X hunitX, smul_smul, smul_eq_mul]
      rw [mul_comm]
    · have hz : pb l y.1 b v = 0 := by
        rcases lt_or_gt_of_ne hb with hneg | hpos
        · haveI := L.neg (S k) b hneg
          exact Subsingleton.elim _ _
        · haveI := L.pos b hpos
          exact Subsingleton.elim _ _
      rw [hΛ.2 a b hab hb u v, map_zero, hz, map_zero, map_zero, map_zero, zero_smul]
  exact LinearMap.congr_fun key w

end UpperTheory.Gal.KunnethLefschetz
