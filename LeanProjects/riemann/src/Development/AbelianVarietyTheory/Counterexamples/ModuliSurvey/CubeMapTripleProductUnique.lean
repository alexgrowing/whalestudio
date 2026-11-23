import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

noncomputable section

namespace GlobalTheory.SemiAbelianTripleChecks

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}

theorem act_add (t : SAB H S) (a b : 𝓞 E) :
    t.act.act (a + b) = lift (t.act.act a) (t.act.act b) ≫ μ[t.G] := t.act.add a b

theorem psum_singleton (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (x : Fin 3 → (T ⟶ G)) (i : Fin 3) :
    psum G x {i} = x i := by
  have h : (List.finRange 3).filter (· ∈ ({i} : Finset (Fin 3))) = [i] := by
    fin_cases i <;> decide
  unfold psum
  rw [h]
  have : padd G (x i) (pzero G T) = x i * 1 := rfl
  simp only [List.foldr_cons, List.foldr_nil]
  rw [this, _root_.mul_one]

theorem cubeMap_tripleProduct_unique {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m m' : CubeMap G' G) (h : m.F = m'.F) : m.F3 = m'.F3 := by
  have key : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = m'.F3 ≫ (x3 G i).left := fun i => by
    have h1 := m.psum_comm {i}
    have h2 := m'.psum_comm {i}
    rw [psum_singleton, psum_singleton] at h1 h2
    rw [← h1, ← h2, h]
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  apply pullback.hom_ext
  · exact k0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact k1
    · rw [Category.assoc, Category.assoc]; exact k2

theorem sabMap_ext {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m m' : SABMap t' t f) (h : m.φ = m'.φ) :
    m = m' := by
  obtain ⟨⟨F, F3, e, he, hp⟩, c, b, a, l⟩ := m
  obtain ⟨⟨F', F3', e', he', hp'⟩, c', b', a', l'⟩ := m'
  have h3 : F3 = F3' := cubeMap_tripleProduct_unique ⟨F, F3, e, he, hp⟩ ⟨F', F3', e', he', hp'⟩ h
  have h1 : F = F' := h
  have h2 : e = e' := b.trans b'.symm
  subst h1 h2 h3
  rfl

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hd : (H.d : 𝓞 E) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h1] at h2
    have h3 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have h4 : (φ H.rt) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, h3]; simp
    have h5 : (φ H.rt).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h6 := congrArg Complex.re h4
    simp [pow_two, h5] at h6
    have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ H.rt).re]
  have hb : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact absurd h hne
    · exact h
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

end GlobalTheory.SemiAbelianTripleChecks
