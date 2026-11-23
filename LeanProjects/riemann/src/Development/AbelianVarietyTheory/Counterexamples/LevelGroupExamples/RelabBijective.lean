import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

noncomputable section

namespace GlobalTheory.UnifDataTest

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_bijective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Bijective (relab (E := E) c σ) := by
  refine Finite.injective_iff_bijective.1 fun τ τ' h => ?_
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

theorem relab_conj (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) :
    relab c σ (conjEmb τ) = conjEmb (relab c σ τ) := by
  ext a
  have h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm
  show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (relab c σ τ) a

theorem laU_upper (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) (τ : E →+* ℂ)
    (hτ : relab c σ τ ∈ (U.X k).Ψ) (i : ℕ) (hi : (U.X k).p0 + i < r) :
    laU U a n k ⟨_, hτ⟩ ⟨_, hi⟩ = (a (τ, i) : ℤ) + (n / 2 : ℕ) := by
  simp [laU, Function.leftInverse_invFun (relab_bijective c σ).1 τ]

theorem laU_lower (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) (τ : E →+* ℂ)
    (hτ : relab c σ τ ∈ (U.X k).Ψ) (i : ℕ) (hi : i < (U.X k).p0) (hr : (U.X k).p0 - 1 - i < r) :
    laU U a n k ⟨_, hτ⟩ ⟨_, hr⟩ = -(a (conjEmb τ, i) : ℤ) - (n / 2 : ℕ) := by
  have h1 : ¬ (U.X k).p0 ≤ (U.X k).p0 - 1 - i := by omega
  have h2 : (U.X k).p0 - 1 - ((U.X k).p0 - 1 - i) = i := by omega
  simp only [laU, h1, if_false, h2, ← relab_conj, Function.leftInverse_invFun (relab_bijective c σ).1 (conjEmb τ)]

theorem laU_antitone (U : Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) (k : U.Comp)
    (τ : (U.X k).Ψ) (j j' : Fin r) (hj : j ≤ j') (hb : (U.X k).p0 ≤ (j : ℕ) ∨ (j' : ℕ) < (U.X k).p0) :
    laU U a n k τ j' ≤ laU U a n k τ j := by
  have hjj : (j : ℕ) ≤ j' := hj
  rcases hb with hb | hb
  · have hb' : (U.X k).p0 ≤ (j' : ℕ) := hb.trans hjj
    have := hd.1 (Function.invFun (relab c σ) τ.1) (show (j : ℕ) - (U.X k).p0 ≤ (j' : ℕ) - (U.X k).p0 by omega)
    simp only [laU, hb, hb', if_true]
    simp only at this
    omega
  · have h1 : ¬ (U.X k).p0 ≤ (j' : ℕ) := by omega
    have h2 : ¬ (U.X k).p0 ≤ (j : ℕ) := by omega
    have := hd.1 (Function.invFun (relab c σ) (conjEmb τ.1))
      (show (U.X k).p0 - 1 - (j' : ℕ) ≤ (U.X k).p0 - 1 - (j : ℕ) by omega)
    simp only [laU, h1, h2, if_false]
    simp only at this
    omega

theorem laU_add_two (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    laU U a (n + 2) = laU U (fun x => a x + 1) n := by
  funext k τ j
  have : (n + 2) / 2 = n / 2 + 1 := by omega
  simp only [laU, this]
  split_ifs <;> push_cast <;> ring

theorem laU_odd (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) : laU U a (2 * m + 1) = laU U a (2 * m) := by
  funext k τ j
  have : (2 * m + 1) / 2 = 2 * m / 2 := by omega
  simp only [laU, this]

theorem conj_mem (X : Data E r) {τ : E →+* ℂ} (h : τ ∉ X.Ψ) : conjEmb τ ∈ X.Ψ := by
  by_contra h'
  exact h ((X.cmType τ).2 h')

theorem perFr_smul (X : Data E r) (x : Frame X.Ψ r) (b : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (b • v) τ i = τ b * perFr X x v τ i := by
  have e : ∀ ρ : E →+* ℂ, Data.emb ρ (b • v) = ρ b • Data.emb ρ v := fun ρ => by
    funext a; simp [Data.emb]
  unfold perFr
  split_ifs with h hi h' hj
  · rw [e, Matrix.mulVec_smul]; rfl
  · simp
  · rw [e]
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, conjEmb, RingHom.comp_apply,
      Complex.conj_conj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp
  · simp

theorem perFr_beyond (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) {τ : E →+* ℂ} (h : τ ∉ X.Ψ) (hr : 0 < r)
    {i : ℕ} (hi : X.p0 ≤ i + 1) :
    perFr X x v τ i =
      hermC (conjEmb τ) X.Gm (col (mat x ⟨conjEmb τ, conj_mem X h⟩) ⟨0, hr⟩) (Data.emb (conjEmb τ) v) := by
  have h0 : X.p0 - 1 - i = 0 := by omega
  unfold perFr
  rw [dif_neg h, dif_pos (conj_mem X h), dif_pos (h0 ▸ hr)]
  simp only [h0]

theorem rdU_mul (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  by_cases h : x ∈ (U.X k).dom
  · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply, h, dif_pos]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp [rdU, h]

theorem not_good_conj (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have : starRingEnd ℂ ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h'
    rwa [show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h] at this
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, him, Complex.neg_re, Complex.natCast_re] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.UnifDataTest
