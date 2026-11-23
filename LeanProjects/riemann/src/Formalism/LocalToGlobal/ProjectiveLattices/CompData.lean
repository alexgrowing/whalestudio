import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

abbrev WTZ (E : Type) [Field E] : Type := ((E →+* ℂ) × ℕ → ℤ) × ℤ

def wtZ {E : Type} [Field E] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : WTZ E := (fun x => (a x : ℤ), (n : ℤ))

theorem wtZ_add {E : Type} [Field E] (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    wtZ (a + a') (n + n') = wtZ a n + wtZ a' n' := by
  unfold wtZ
  ext <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev AC (Z : Comp Xo c) : Type := AddMonoidAlgebra (Om Z) (WTZ E)

example (Z : Comp Xo c) : Algebra (𝓞 c.F) (AC Z) := inferInstance

example (Z : Comp Xo c) : IsScalarTower (𝓞 c.F) c.F (AC Z) := inferInstance

instance towKAC (Z : Comp Xo c) : IsScalarTower c.F (Om Z) (AC Z) := inferInstance

def AG (Z : Comp Xo c) (G : WTZ E) : Submodule (Om Z) (AC Z) :=
  Submodule.span (Om Z) {AddMonoidAlgebra.single G 1}

theorem mem_AG {Z : Comp Xo c} {G : WTZ E} {f : AC Z} : f ∈ AG Z G ↔ ∃ r : Om Z, f = AddMonoidAlgebra.single G r := by
  unfold AG
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AddMonoidAlgebra.smul_single', mul_one]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AddMonoidAlgebra.smul_single', mul_one]⟩

instance gradedAG (Z : Comp Xo c) : SetLike.GradedMonoid (AG Z) where
  one_mem := mem_AG.2 ⟨1, rfl⟩
  mul_mem := by
    intro G G' f g hf hg
    obtain ⟨r, rfl⟩ := mem_AG.1 hf
    obtain ⟨s, rfl⟩ := mem_AG.1 hg
    exact mem_AG.2 ⟨r * s, by rw [AddMonoidAlgebra.single_mul_single]⟩

theorem finrank_AG (Z : Comp Xo c) (G : WTZ E) : Module.finrank (Om Z) (AG Z G) = 1 :=
  finrank_span_singleton (by simp)

theorem mul_ne_zero_AG {Z : Comp Xo c} {G G' : WTZ E} {f g : AC Z} (hf : f ∈ AG Z G) (hg : g ∈ AG Z G')
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) : f * g ≠ 0 := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := by
    rintro rfl
    exact hf0 (by simp)
  have hs : s ≠ 0 := by
    rintro rfl
    exact hg0 (by simp)
  rw [AddMonoidAlgebra.single_mul_single]
  simp [hr, hs]

def valC (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ∀ Z : Comp Xo c, AC Z :=
  fun Z => AddMonoidAlgebra.single (wtZ a n) (evC h Z f)

theorem valC_mem (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h a n f Z ∈ AG Z (wtZ a n) := mem_AG.2 ⟨_, rfl⟩

end Formalism.L2.Pj
