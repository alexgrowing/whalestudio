import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLoc

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def gen (Qq : Type) [Field Qq] (p : ℕ) (a : ℤ) : Fin 1 → Qq := fun _ => (p : Qq) ^ a

theorem gen_mem (a : ℤ) : gen Qq p a ∈ line W (Qq := Qq) p a := Submodule.mem_span_singleton_self _

theorem p_smul_gen (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : (p : W) • gen Qq p a = gen Qq p (a + 1) := by
  funext i
  simp only [gen, Pi.smul_apply, Algebra.smul_def, map_natCast]
  rw [zpow_add₀ (p_ne h), zpow_one, mul_comm]

theorem line_succ_le (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : line W (Qq := Qq) p (a + 1) ≤ line W p a := by
  unfold line
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have := p_smul_gen (W := W) h a
  unfold gen at this
  rw [← this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem p_smul_line (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) (x : Fin 1 → Qq) (hx : x ∈ line W (Qq := Qq) p a) :
    (p : W) • x ∈ line W (Qq := Qq) p (a + 1) := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [smul_comm]
  have := p_smul_gen (W := W) h a
  unfold gen at this
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

def toQuot (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) :
    W →ₗ[W] (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) :=
  (Submodule.mkQ _).comp (LinearMap.toSpanSingleton W _ ⟨gen Qq p a, Submodule.mem_span_singleton_self _⟩)

theorem toQuot_surj (a : ℤ) : Function.Surjective (toQuot W (Qq := Qq) p a) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  exact ⟨c, rfl⟩

theorem toQuot_ker (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) :
    LinearMap.ker (toQuot W (Qq := Qq) p a) = Ideal.span {(p : W)} := by
  have := h.frac_alt
  ext c
  rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
  show Submodule.mkQ _ (c • (⟨gen Qq p a, gen_mem a⟩ : ↥(line W (Qq := Qq) p a))) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show c • gen Qq p a ∈ line W p (a + 1) ↔ _
  constructor
  · intro hc
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hc
    have hd' : d • gen Qq p (a + 1) = c • gen Qq p a := hd
    rw [← p_smul_gen (W := W) h a, smul_smul] at hd'
    have h0 := congrFun hd' 0
    simp only [gen, Pi.smul_apply, Algebra.smul_def] at h0
    have h1 := mul_right_cancel₀ (zpow_ne_zero a (p_ne h)) h0
    have h2 : d * (p : W) = c := IsFractionRing.injective W Qq h1
    exact ⟨d, by rw [← h2, mul_comm]⟩
  · rintro ⟨d, rfl⟩
    rw [mul_comm, mul_smul, p_smul_gen h]
    exact Submodule.smul_mem _ _ (gen_mem _)

theorem card_line_quot (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) :
    Nat.card (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) =
      p ^ n' := by
  rw [← h.res_card, ← toQuot_ker (Qq := Qq) h a]
  exact Nat.card_congr ((toQuot W (Qq := Qq) p a).quotKerEquivOfSurjective (toQuot_surj a)).symm.toEquiv

def edge1 (W : Type) (Qq : Type) [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) : Edge W Qq 1 :=
  ⟨line W p (a + 1), line W p a⟩

theorem line_lattice_isEdge (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : IsEdge p n' 1 (edge1 W Qq p a) :=
  ⟨line_isLattice h _, line_isLattice h _, line_succ_le h a, p_smul_line h a, by
    rw [mul_one]; exact card_line_quot h a⟩

theorem edge_eq (h : HidaSetting p n' W Qq O Kf ι σ j w) (e : Edge W Qq 1) (he : IsEdge p n' 1 e) :
    ∃ a : ℤ, e = edge1 W Qq p a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := he
  obtain ⟨s, t⟩ := e
  obtain ⟨b, rfl⟩ := lat1 h s h1
  obtain ⟨a, rfl⟩ := lat1 h t h2
  have hab : a ≤ b := le_of_mem h (h3 (gen_mem b))
  have hba : b ≤ a + 1 := by
    have := h4 _ (gen_mem a)
    rw [p_smul_gen h] at this
    exact le_of_mem h this
  refine ⟨a, ?_⟩
  rcases (by omega : b = a + 1 ∨ b = a) with rfl | rfl
  · rfl
  · exfalso
    have htop : Submodule.comap (line W (Qq := Qq) p b).subtype (line W p b) = ⊤ := Submodule.comap_subtype_self _
    have h5' : Nat.card (↥(line W (Qq := Qq) p b) ⧸ Submodule.comap (line W (Qq := Qq) p b).subtype (line W p b)) =
      p ^ (n' * 1) := h5
    rw [htop] at h5'
    have h6 : Nat.card (↥(line W (Qq := Qq) p b) ⧸ (⊤ : Submodule W ↥(line W (Qq := Qq) p b))) = 1 :=
      Nat.card_unique
    rw [h6] at h5'
    have h7 : 1 < p ^ (n' * 1) := Nat.one_lt_pow (by have := h.two_le; omega) (by have := h.five_le; omega)
    omega

end Formalism.MainNotions.G.Inhab

end
