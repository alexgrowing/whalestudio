import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TriComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLimit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem twoIrr_entry {K : Type} [Field K] (t : Kˣ × Kˣ) (X : M4 K) (i j : Fin 4) :
    tconj t X i j = 0 ↔ X i j = 0 := by
  show (wv t (wt i j) : K) * X i j = 0 ↔ _
  rw [mul_eq_zero, or_iff_right (Units.ne_zero _)]

private theorem twoIrr_ge {H K : Type} [Group H] [Field K] (t : Kˣ × Kˣ) (r r' : H →* M4 K)
    (h : ∀ g, r g = tconj t (r' g)) (i j : Fin 4) : Ge r i j ↔ Ge r' i j := by
  unfold Ge
  refine exists_congr fun g => ?_
  rw [h g, Ne, Ne, twoIrr_entry]

private theorem twoIrr_irr {H K : Type} [Group H] [Field K] (t : Kˣ × Kˣ) (r r' : H →* M4 K)
    (h : ∀ g, r g = tconj t (r' g)) (hr : Irr r) : Irr r' := by
  let L : M4 K →ₗ[K] M4 K :=
    { toFun := fun X => Matrix.of fun i j => (((wv t (wt i j))⁻¹ : Kˣ) : K) * X i j
      map_add' := fun X Y => by ext i j; simp [mul_add]
      map_smul' := fun a X => by ext i j; simp [mul_left_comm] }
  have hL : ∀ X, L (tconj t X) = X := fun X => by
    ext i j
    show (((wv t (wt i j))⁻¹ : Kˣ) : K) * ((wv t (wt i j) : K) * X i j) = X i j
    rw [Units.inv_mul_cancel_left]
  unfold Irr at *
  rw [eq_top_iff]
  intro X _
  have h1 : tconj t X ∈ Submodule.span K (Set.range r) := by rw [hr]; trivial
  have h2 := Submodule.mem_map_of_mem (f := L) h1
  rw [hL, Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, by rw [h g, hL]⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.twoIrr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], Loc.LocalPublishedTheorems → SoV Ω l → D.Fin0 → D.NoEnd → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, TwoSigned M.gr (ξ.comp M.toSS) → Irr (M.rep ξ) := by
  intro Ω _ _ _ l _ c D hD M _ hP hSo hF hNE ξ h2
  obtain ⟨t, r, hr, hrt⟩ := ptScale D hD M hF ξ
  have hge := twoIrr_ge t r _ hrt
  obtain ⟨hn, hp, -⟩ := signs D hD M hF ξ
  rcases tri D hD hP r hr with h | h | ⟨h02, h20, h⟩
  · exact twoIrr_irr t r _ hrt h
  · exfalso
    rcases diagCases D hD hSo r hr h with ⟨-, h⟩ | ⟨-, h⟩
    · exact h2.1 (hn fun i j hij hg => h i j hij ((hge i j).2 hg))
    · exact h2.2 (hp fun i j hij hg => h i j hij ((hge i j).2 hg))
  · exfalso
    obtain ⟨ξ₀, h₀⟩ := ptLimit D hD M hF ξ (h.imp (fun h i j hij hg => h i j hij ((hge i j).2 hg))
      (fun h i j hij hg => h i j hij ((hge i j).2 hg)))
    obtain ⟨t₀, r₀, hr₀, hrt₀⟩ := ptScale D hD M hF ξ₀
    have hge₀ := twoIrr_ge t₀ r₀ _ hrt₀
    obtain ⟨hm, -, -, -, -, he, -⟩ := ptIn D hD (PadicAlgCl l) r₀ hr₀
    obtain ⟨-, -, -, -, -, h6⟩ := geAlg (PadicAlgCl l) r₀ _ hm he
    have hb : ∀ g, IsBlock (r₀ g) := fun g i j hij => by
      rw [hrt₀, twoIrr_entry, h₀, if_neg hij]
    have key : ∀ i j, lamW i = lamW j → Ge r i j → Ge r₀ i j := fun i j hij hg => by
      obtain ⟨g, hg⟩ := (hge i j).1 hg
      exact (hge₀ i j).2 ⟨g, by rw [h₀, if_pos hij]; exact hg⟩
    exact hNE r₀ hr₀ hb (h6 (key 0 2 (by decide) h02) (key 2 0 (by decide) h20) hb)
