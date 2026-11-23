import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def PiHalf (l : Level H) (D : DepData E) : Prop := Ideal.span {D.pi 0 * D.pi 1} = l.Mb

theorem PiHalf.coprime {l : Level H} {D : DepData E} (h : PiHalf l D) (i k : Fin 2) :
    IsCoprime (D.pi i) (H.bar (D.pi k)) := by
  have hd : ∀ j : Fin 2, D.pi j ∣ D.pi 0 * D.pi 1 := fun j =>
    match j with
    | 0 => dvd_mul_right _ _
    | 1 => dvd_mul_left _ _
  have h1 : l.Mb ≤ Ideal.span {D.pi i} := by
    rw [← h]; exact Ideal.span_singleton_le_span_singleton.2 (hd i)
  have h2 : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ Ideal.span {H.bar (D.pi k)} := by
    rw [← h, Ideal.map_span, Set.image_singleton]
    exact Ideal.span_singleton_le_span_singleton.2 (map_dvd (H.bar : 𝓞 E →+* 𝓞 E) (hd k))
  have htop : Ideal.span {D.pi i} ⊔ Ideal.span {H.bar (D.pi k)} = ⊤ := by
    rw [eq_top_iff, ← l.coprime]; exact sup_le_sup h1 h2
  exact (Ideal.isCoprime_span_singleton_iff _ _).1 (Ideal.isCoprime_iff_sup_eq.2 htop)

theorem zeta_mem_of_dvd {l : Level H} (c : Coeff l) {g : ℕ} (hg : g ∣ l.M') (h0 : l.M' ≠ 0) : zeta g ∈ c.F := by
  obtain ⟨k, hk⟩ := hg
  have hg0 : (g : ℂ) ≠ 0 := by
    rintro h'; apply h0; rw [hk, Nat.cast_eq_zero.1 h', zero_mul]
  have hk0 : (k : ℂ) ≠ 0 := by
    rintro h'; apply h0; rw [hk, Nat.cast_eq_zero.1 h', mul_zero]
  have e : zeta g = zeta l.M' ^ k := by
    unfold zeta
    rw [← Complex.exp_nat_mul, hk]
    congr 1
    push_cast
    field_simp
  rw [e]
  exact pow_mem c.zeta_mem k

end Formalism.L2.Pj
