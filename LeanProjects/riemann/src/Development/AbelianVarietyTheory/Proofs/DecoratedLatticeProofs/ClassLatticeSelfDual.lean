import Mathlib
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStepG
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.ClassLatticeSelfDual

section General

open Formalism.UG Formalism.UG.P
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

omit [NumberField F] [DecidableEq n] [Fintype n] in

theorem mem_span_of_mem_latS (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] (S : Subring (E ⊗[F] R))
    (L : Submodule (𝓞 E) (n → E)) (x : n → E)
    (hx : (fun i => inclE (F := F) R (x i)) ∈ latS (F := F) R S L) :
    x ∈ Submodule.span E (L : Set (n → E)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R →ₗ[F] F, φ 1 = 1 := Module.Projective.exists_dual_eq_one F one_ne_zero
  let π : E ⊗[F] R →ₗ[E] E :=
    (TensorProduct.AlgebraTensorModule.rid F E E).toLinearMap ∘ₗ (φ.baseChange E)
  have hπ : ∀ (s : E ⊗[F] R) (a : E), π (s * inclE (F := F) R a) = π s * a := by
    intro s a
    have : s * inclE (F := F) R a = a • s := by
      rw [mul_comm, Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have hπ1 : π 1 = 1 := by
    simp [π, Algebra.TensorProduct.one_def, hφ]
  have key : ∀ u ∈ latS (F := F) R S L, ∀ s : E ⊗[F] R,
      (fun i => π (s * u i)) ∈ Submodule.span E (L : Set (n → E)) := by
    intro u hu
    unfold latS at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      intro s
      have : (fun i => π (s * inclE (F := F) R (y i))) = π s • y := by
        funext i; rw [hπ]; rfl
      exact this ▸ Submodule.smul_mem _ _ (Submodule.subset_span hy)
    | zero =>
      intro s
      have : (fun i => π (s * (0 : n → E ⊗[F] R) i)) = 0 := by funext i; simp
      exact this ▸ zero_mem _
    | add u u' _ _ h h' =>
      intro s
      have : (fun i => π (s * (u + u') i)) = (fun i => π (s * u i)) + fun i => π (s * u' i) := by
        funext i; simp [mul_add]
      exact this ▸ add_mem (h s) (h' s)
    | smul r u _ h =>
      intro s
      have : (fun i => π (s * (r • u) i)) = fun i => π ((s * (r : E ⊗[F] R)) * u i) := by
        funext i; rw [mul_assoc]; rfl
      exact this ▸ h _
  have h := key _ hx 1
  have e : (fun i => π (1 * inclE (F := F) R (x i))) = x := by
    funext i; rw [hπ, hπ1, one_mul]
  rwa [e] at h

theorem eq_globLat (Λ L : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (hL : Module.Finite (𝓞 E) L)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : ∀ x : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (g⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) :
    L = CS.globLat g Λ := by
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨p, hp⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨p, hp.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h1 : (0 : FiniteAdeleRing (𝓞 F) F) v = (1 : FiniteAdeleRing (𝓞 F) F) v := by rw [h]
    exact (zero_ne_one : (0 : v.adicCompletion F) ≠ 1) h1
  have hG := csGlob_lattice (F := F) Λ hfin hspan g
  have hLs : Submodule.span E (L : Set (n → E)) = ⊤ := by
    rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
    intro x hx
    exact mem_span_of_mem_latS (F := F) _ _ L x ((h _).2 hx)
  ext x
  conv_lhs => rw [← global_lattice_one_holds F E n L hL hLs]
  refine Iff.trans ?_ (h _)
  show ((1⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔ _
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

end General

theorem classLattice_selfDual : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (c : (D.fm u).clsP), Submodule.IsLattice D.host.E (K.lat c) ∧ ∀ y, y ∈ K.lat c ↔ ∀ x ∈ K.lat c, Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro D u K c
  have e := eq_globLat (F := D.host.F) K.lev.Lb (K.lat c) K.lev.Lb_fin K.lev.Lb_span (K.lat_fin c) (K.y c).1 (K.y_lat c)
  have hdual : ∀ x, x ∈ K.lev.Lb ↔ ∀ y ∈ K.lev.Lb,
      Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro x
    refine ⟨fun hx => K.lev.Lb_int x hx, fun hx => ?_⟩
    have := K.lev.Lb_dual x hx
    rwa [Nat.cast_one, one_smul] at this
  rw [e]
  exact ⟨Formalism.UG.P.csGlob_lattice (F := D.host.F) _ K.lev.Lb_fin K.lev.Lb_span _,
    fun y => GlobalTheory.PointLattice.globLat_selfDual (sigD D) (gramP D) _ hdual K.lev.Lb_fin K.lev.Lb_span _ (K.y c).2 y⟩

end GlobalTheory.ClassLatticeSelfDual
