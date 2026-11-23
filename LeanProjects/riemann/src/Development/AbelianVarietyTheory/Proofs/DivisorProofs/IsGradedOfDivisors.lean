import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo

namespace GlobalTheory.ChernWeilLine

variable {F : Type} [Field F] {X : Var F} {ι : Type} [Finite ι]

def ofDivisors (Δ : ι → X.Dv) : Fr (ratOf X) (fun _ : ι => 1) 0 where
  S z := {A | ∀ i, (Δ i).GeneratesAt z (A i 0 0)}
  loc z := by
    have := Fintype.ofFinite ι
    choose U hz g hg using fun i => (Δ i).exists_isEqn_nhds z
    let W : X.X.Opens := ⨅ i, U i
    have hW : z ∈ W := by
      show z ∈ ((⨅ i, U i : X.X.Opens) : Set X.X)
      rw [TopologicalSpace.Opens.coe_iInf]; exact Set.mem_iInter.2 hz
    refine ⟨W, fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹, hW, fun _ => by simp, fun z' hz' A => ?_⟩
    have hz'' (i : ι) : z' ∈ U i := by
      have : z' ∈ ((⨅ i, U i : X.X.Opens) : Set X.X) := hz'
      rw [TopologicalSpace.Opens.coe_iInf] at this; exact Set.mem_iInter.1 this i
    have e (i : ι) (a b : Fin 1) : (A * (fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹ :
        Mat (fun _ : ι => 1) X.Fn)⁻¹) i a b = A i 0 0 * g i := by
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp [Matrix.mul_apply, Matrix.inv_def]
    refine ⟨fun h i => ?_, fun h i => ?_⟩
    · have h' := ((hg i z' (hz'' i)).generatesAt_iff).1 (h i)
      refine ⟨fun a b => ?_, ?_, ?_, fun a b ha => absurd ha (by simp)⟩
      · rw [e]; exact mem_O_ratOf.2 h'.regAt
      · rw [Matrix.det_unique, e]; exact h'.ne_zero
      · rw [Matrix.det_unique, e]; exact mem_O_ratOf.2 h'.inv.regAt
    · obtain ⟨h1, h2, h3, -⟩ := h i
      rw [Matrix.det_unique, e] at h2 h3
      exact ((hg i z' (hz'' i)).generatesAt_iff).2
        ((unitAt_iff h2).2 ⟨mem_O_ratOf.1 (e i 0 0 ▸ h1 0 0), mem_O_ratOf.1 h3⟩)

theorem isGraded_ofDivisors (Δ : ι → X.Dv) : IsGraded (lineFlag (ofDivisors Δ)) fun x => Δ x.1 := by
  refine ⟨1, fun i => ⟨1, (Δ i).isEqn_genericPoint 1, by simpa using unitAt_one _⟩, fun y x => ?_⟩
  choose g hg using fun i => (Δ i).exists_isEqn y
  refine ⟨fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹,
    fun i => CartierDiv.isEqn_iff_generatesAt_inv.1 (hg i), g x.1, ?_, hg x.1⟩
  obtain ⟨i, a⟩ := x
  rw [Subsingleton.elim a 0]
  simp [Matrix.inv_def]

end GlobalTheory.ChernWeilLine

namespace GlobalTheory.ChernWeilLine

variable {F : Type} [Field F] [NumberField F] {ι : Type}

def lineGram {Y : Var F} {σ : F →+* ℂ} {Δ : ι → Y.Dv} (C : CxSt F) (m : ∀ i, C.Met Y σ (Δ i)) :
    Mat (fun _ : ι => 1) Y.Fn → Pts Y σ → Mat (fun _ : ι => 1) ℂ :=
  fun A y i => Matrix.of fun _ _ => ((C.pn Y σ (Δ i) (m i) (C.cx Y σ (A i 0 0)) y : ℝ) : ℂ)

end GlobalTheory.ChernWeilLine
