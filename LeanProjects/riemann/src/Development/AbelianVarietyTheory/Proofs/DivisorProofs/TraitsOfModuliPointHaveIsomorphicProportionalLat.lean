import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonSemiAbelianPullbackTwoUnitaryTraitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationsCharacterIsoAssociatedCoordStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitUniq

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {w : W} (hw : Irreducible w) {a b : ℕ}
    (h : Associated (w ^ a) (w ^ b)) : a = b := by
  have key : ∀ {a b : ℕ}, Associated (w ^ a) (w ^ b) → a ≤ b → a = b := by
    intro a b h hab
    by_contra hne
    have hlt : 0 < b - a := by omega
    have h1 : Associated (w ^ a * 1) (w ^ a * w ^ (b - a)) := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab]; exact h
    have h2 : Associated 1 (w ^ (b - a)) :=
      Associated.of_mul_left h1 (Associated.refl _) (pow_ne_zero _ hw.ne_zero)
    have h3 : IsUnit (w ^ (b - a)) := associated_one_iff_isUnit.1 h2.symm
    exact hw.not_isUnit ((isUnit_pow_iff hlt.ne').1 h3)
  rcases le_total a b with hab | hab
  · exact key h hab
  · exact (key h.symm hab).symm

theorem sq_associated {V W : Type} [CommRing V] [CommRing W] [IsDomain W] (f : V →+* W) (ϖ : V) (w : W) (m n : ℕ)
    (hm : Associated (f ϖ) (w ^ m)) (v : Wˣ) (u : Vˣ) :
    Associated ((v * f (u * ϖ ^ n)) ^ 2) (w ^ (2 * (m * n))) := by
  have hu : IsUnit (f (u : V)) := (Units.isUnit u).map f
  have e : (v * f (u * ϖ ^ n)) ^ 2 = (((v : W) * f u) ^ 2) * (f ϖ ^ n) ^ 2 := by
    rw [map_mul, map_pow]; ring
  rw [e]
  refine (associated_unit_mul_left _ _ ((v.isUnit.mul hu).pow 2)).trans ?_
  have eq : w ^ (2 * (m * n)) = ((w ^ m) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
  rw [eq]
  exact (hm.pow_pow (n := n)).pow_pow (n := 2)

end GlobalTheory.UPoinc.TraitUniq

open GlobalTheory.UPoinc.TraitUniq in

theorem GlobalTheory.UPoinc.uTraitUniqSt_holds : UTraitUniqSt := by
  intro E _ _ _ H Dw l Xo c T T' W _ _ _ f f' fK fK' hB hW hf hf' hfl hfl' hK hK' hy w m m' hw hm hm'
  obtain ⟨tW, ⟨φ⟩, ⟨φ'⟩⟩ := GlobalTheory.T.exists_common_semiAbelian_pullback_two_unitary_traits E H Dw l Xo c T T' W f f' fK fK' hB hW hf hf' hfl hfl' hK hK' hy
  obtain ⟨PW, e1, he1⟩ := GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr E H T.V T.cdvr T.t T.P W hB hW f hf hfl tW ⟨φ⟩
  obtain ⟨PW', e1', he1'⟩ := GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr E H T'.V T'.cdvr T'.t T'.P W hB hW f' hf' hfl' tW ⟨φ'⟩
  obtain ⟨e2, he2⟩ := GlobalTheory.T.linear_uniformisations_character_iso_associated_coords E H W hB tW PW PW'
  let e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X := e1.symm.trans (e2.trans e1')

  have diag : ∀ y, (m : ℤ) * T.be y y = m' * T'.be (e y) (e y) := by
    intro y
    obtain ⟨u, n, hn, hc⟩ := T.mono y
    obtain ⟨u', n', hn', hc'⟩ := T'.mono (e y)
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one] at hn hc hn' hc'
    have hc1 : PsiCoord T.P.D.toPre (e1 (e1.symm y)) (u * T.ϖ ^ n 0) := by
      rw [LinearEquiv.apply_symm_apply]; exact hc
    obtain ⟨v, hv⟩ := he1 _ _ hc1
    obtain ⟨v', hv'⟩ := he1' (e2 (e1.symm y)) _ hc'
    have ha := he2 _ _ _ hv hv'
    have h1 := sq_associated f T.ϖ w m (n 0) hm v u
    have h2 := sq_associated f' T'.ϖ w m' (n' 0) hm' v' u'
    have := pow_eq_of_associated hw (h1.symm.trans (ha.trans h2))
    rw [hn 0, hn' 0]
    have : ((2 * (m * n 0) : ℕ) : ℤ) = ((2 * (m' * n' 0) : ℕ) : ℤ) := by rw [this]
    push_cast at this
    linarith
  have hs : ∀ a b, T.be a b = T.be b a := fun a b => (mem_levelForms.1 T.lev).1 a b
  have hs' : ∀ a b, T'.be a b = T'.be b a := fun a b => (mem_levelForms.1 T'.lev).1 a b
  refine ⟨e, fun a b => ?_⟩
  have h := diag (a + b)
  simp only [map_add, LinearMap.add_apply] at h
  have ha := diag a
  have hb := diag b
  rw [hs b a, hs' (e b) (e a)] at h
  linarith
