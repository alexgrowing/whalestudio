import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubMemIdS
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem idS_smul_latS (I : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Fin n → E)) {t : Formalism.L2.Herm.intAf F E}
    (ht : t ∈ idS F I) {u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hu : u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N) :
    t • u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N) := by
  have hA : ∀ p ∈ I, ∀ u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N,
      oToS F E p • u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N) := by
    intro p hp u hu
    refine Submodule.span_induction (p := fun u _ => oToS F E p • u ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N)) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨m, hm, rfl⟩
      refine Submodule.subset_span ⟨p • m, Submodule.smul_mem_smul hp hm, ?_⟩
      funext i
      show iA F E ((p • m) i) = (oToS F E p : E ⊗[F] Formalism.L2.Herm.Af F) * iA F E (m i)
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      rfl
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [smul_comm]; exact Submodule.smul_mem _ c ha
  have hmap : idS F I = Ideal.span (oToS F E '' I) := rfl
  rw [hmap] at ht
  refine Submodule.span_induction (p := fun t _ => t • u ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N)) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨p, hp, rfl⟩
    exact hA p hp u hu
  · rw [zero_smul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [add_smul]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c ha

theorem inv_mul_int_away {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (Q : Pl E) (ε : E ⊗[F] Formalism.L2.Herm.Af F) (h : IdemOf F Q ε) (m : ℕ)
    (y y' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hle : (Q.asIdeal ^ m) • Formalism.UG.CS.globLat y (stdLat E n) ≤ Formalism.UG.CS.globLat y' (stdLat E n)) :
    ∀ i j, (1 - ε) * (y'⁻¹ * y).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  intro i j
  have hfin := Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg
  have hspan := (stdLat_lattice (E := E) (n := n)).span_eq_top
  have hSR := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n) hfin hspan
  have hcol : (y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.UG.CS.globLat y (stdLat E n)) := by
    refine (hSR _ _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, mem_latS_std]
    intro k
    by_cases hkj : k = j
    · subst hkj; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hkj]; exact Subring.zero_mem _
  have h1 := idS_smul_latS (Q.asIdeal ^ m) _ (h.one_sub_mem_idS m) hcol
  have h2 := Submodule.span_mono (Set.image_mono hle) h1
  have h3 := ((mem_latS_std _).1 ((hSR y' _).1 h2)) i
  convert h3 using 1
  have e : ((⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) •
      ((y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) =
      (1 - ε) • ((y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := rfl
  rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one, Pi.smul_apply,
    smul_eq_mul]
  rfl

end GlobalTheory.InertNbr
