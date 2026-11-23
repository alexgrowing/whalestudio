import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

section Sums

end Sums

section Tri

variable {n : ℕ}

end Tri

section Per

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Classical in

def Ablk (X : Data E r) (b : Frame X.Ψ r) (τ' : E →+* ℂ) (i l : ℕ) : ℂ :=
  if h : τ' ∈ X.Ψ then
    (if h2 : X.p0 + i < r ∧ X.p0 + l < r then (mat b ⟨τ', h⟩)⁻¹ ⟨X.p0 + i, h2.1⟩ ⟨X.p0 + l, h2.2⟩ else 0)
  else if h' : conjEmb τ' ∈ X.Ψ then
    (if h2 : X.p0 - 1 - l < r ∧ X.p0 - 1 - i < r then
      mat b ⟨conjEmb τ', h'⟩ ⟨X.p0 - 1 - l, h2.1⟩ ⟨X.p0 - 1 - i, h2.2⟩ else 0)
  else if i = l then 1 else 0

end Per

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}

variable (c σ) in

theorem relab_rt_iff (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  have hcoe : ∀ x : E, ((embF c τ' x : c.F) : ℂ) = τ' x := fun x => by
    first
      | rfl
      | simp [embF]
  have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have h1 : ((H.rt : E)) ^ 2 = -((H.d : ℕ) : E) := by
      have h2 := congrArg (fun y : 𝓞 E => (y : E)) H.rt_sq
      simpa using h2
    rw [h1]
    simp
  have hne : H.rt0 ≠ 0 := by
    intro h0
    have h3 := H.sqrt_neg_disc_sq
    rw [h0] at h3
    have hd := H.d_prime.pos
    have : ((H.d : ℕ) : ℂ) = 0 := by
      have h4 : (0 : ℂ) ^ 2 = -((H.d : ℕ) : ℂ) := h3
      simpa using h4.symm
    exact hd.ne' (by exact_mod_cast this)
  have hσρ : σ ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ = H.rt0 := hσ
  unfold relab
  simp only [RingHom.comp_apply]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · have e : embF c τ' (H.rt : E) = ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ :=
      Subtype.ext (by rw [hcoe, h])
    rw [e, hσρ]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · have e : embF c τ' (H.rt : E) = -⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ :=
      Subtype.ext (by rw [hcoe, h]; rfl)
    rw [e, map_neg, hσρ, h]

theorem conjEmb_eq' (τ : E →+* ℂ) : conjEmb τ = NumberField.ComplexEmbedding.conjugate τ := by
  ext x
  simp [conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]

variable (M) in

def AM (k : Fin F.n) (b : Frame (M.X k).Ψ r) : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
  fun τ i l => Ablk (M.X k) b (relab c σ τ) i l

theorem bor_diag_ne (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ' : X.Ψ) (j : Fin r) :
    b τ' j j ≠ 0 := by
  have h1 := (hb τ').1
  have ht : (mat b τ').BlockTriangular id := fun a c hca => (hb τ').2 a c hca
  rw [Matrix.det_of_upperTriangular ht] at h1
  exact (Finset.prod_ne_zero_iff.1 h1) j (Finset.mem_univ _)

end Main

end Formalism.L2.Pj
