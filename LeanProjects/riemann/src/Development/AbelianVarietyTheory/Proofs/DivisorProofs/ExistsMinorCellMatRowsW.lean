import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagZ.StepDet

open GlobalTheory.FlagZ.TautCell

variable {ι : Type} [Fintype ι] {N : ℕ}

def rowsW (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : Fin (N + 1)) : Rows N l :=
  ⟨Finset.univ.filter fun i => ((w τ i : Fin N) : ℕ) < l, by
    change (Finset.univ.filter fun i => ((w τ i : Fin N) : ℕ) < l).card = l
    rw [← Finset.card_map (w τ).toEmbedding, Finset.map_filter, Finset.map_univ_equiv]
    simpa [min_eq_right (Nat.lt_succ_iff.1 l.2)] using Fin.card_filter_val_lt (n := N) (m := l)⟩

def colP (w : ι → Equiv.Perm (Fin N)) (τ : ι) (j : Fin N) :
    Γ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N), cellU w) :=
  ∑ i, (cellMat w τ).1 i j • QCoh.pullbackSections (flStr ι N) (Taut.stdE N) (by simp)
    (VB.freeFrame (Sp ℤ) (Fin N) i)

def matAt (w : ι → Equiv.Perm (Fin N)) (τ : ι) {σ : ℤ →+* ℂ} (y : CxPts (flStr ι N) σ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => CxPts.ev (flStr ι N) σ (cellU w) ((cellMat w τ).1 i j) y

theorem exists_minor_cellGL_rowsW (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : Fin (N + 1)) :
    ∃ ε : ℤˣ, minor (cellGL (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w τ).1 l (rowsW w τ l) = ((ε : ℤ) : R ι N) := by
  have hm (i : Fin l) : ((w τ (subsetEnum (rowsW w τ l) i) : Fin N) : ℕ) < l := by
    have : subsetEnum (rowsW w τ l) i ∈ (rowsW w τ l).1 := Finset.orderEmbOfFin_mem _ _ _
    exact (Finset.mem_filter.1 this).2
  let f : Fin l → Fin l := fun i => ⟨_, hm i⟩
  have hf : Function.Injective f := fun i j h => by
    have h1 : w τ (subsetEnum (rowsW w τ l) i) = w τ (subsetEnum (rowsW w τ l) j) := Fin.ext (congrArg (fun x : Fin l => x.val) h)
    exact (Finset.orderEmbOfFin _ _).injective ((w τ).injective h1)
  let π : Equiv.Perm (Fin l) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  let M : Matrix (Fin l) (Fin l) (R ι N) :=
    (lowMat (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd τ).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)
  have h {i j : Fin N} (hij : i ≤ j) :
      lowMat (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd τ i j = (1 : Matrix _ _ _) i j :=
    dif_neg fun ⟨_, _, h₁, h₂⟩ => (h₁.trans_le h₂).not_ge hij
  have ht : M.BlockTriangular OrderDual.toDual := fun i j hij =>
    (h (le_of_lt (show i < j from hij))).trans (Matrix.one_apply_ne (ne_of_lt (show i < j from hij)))
  have hM : M.det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ ht]
    simp [M, h le_rfl]
  refine ⟨Equiv.Perm.sign π, ?_⟩
  have e : minor (cellGL (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w τ).1 l (rowsW w τ l) =
      (M.submatrix π id).det := rfl
  rw [e, Matrix.det_permute, hM, mul_one]

theorem exists_minor_cellMat_rowsW (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : Fin (N + 1)) :
    ∃ ε : ℤˣ, minor (cellMat w τ).1 l (rowsW w τ l) = ((ε : ℤ) : Γ(Fl ι N, cellU w)) := by
  obtain ⟨ε, h⟩ := exists_minor_cellGL_rowsW w τ l
  refine ⟨ε, (minor_map (cellHom w) _ l _).trans ?_⟩
  rw [h, map_intCast]

theorem cellU_le_chart (a : ι) (l : Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) :
    cellU w ≤ (flDet a l).dual.B.U (frameIdx Prod.fst Prod.snd (a, l) (rowsW w a l)) := by
  rintro _ ⟨z, -, rfl⟩
  refine mem_pull.2 ?_
  obtain ⟨ε, h⟩ := exists_minor_cellGL_rowsW w a l
  have hu : IsUnit (plVec (cellGL (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w a).1 l (rowsEquiv N l (rowsW w a l))) := by
    rw [plVec_rowsEquiv, h]
    exact ε.isUnit.map (Int.castRingHom _)
  have := (GlobalTheory.Points.le_pt_preimage_chart_iff (Int.castRingHom _) _ (span_plVec _ _) _).2 hu (Set.mem_univ z)
  rw [← plPt_π Prod.fst Prod.snd (cellGL (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) (a, l),
    ← flagPt_plEmb_assoc] at this
  exact this

theorem eq_flagPt_of_le {A : Type} [CommRing A] (w : ι → Equiv.Perm (Fin N)) (x : Sp A ⟶ Fl ι N)
    (h : ⊤ ≤ x ⁻¹ᵁ cellU w) :
    x = flagPt Prod.fst Prod.snd fun τ =>
      Matrix.GeneralLinearGroup.map (Points.valMap x (cellU w) h).hom (cellMat w τ) := by
  have hr : Set.range x ⊆ Set.range (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, -, hy⟩ := h (Set.mem_univ z)
    exact ⟨y, hy⟩
  obtain ⟨t, rfl⟩ : ∃ t, t ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w = x :=
    ⟨_, IsOpenImmersion.lift_fac _ x hr⟩
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
  have e : (Points.valMap (Spec.map ψ ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) (cellU w) h).hom.comp
      (cellHom w) = ψ.hom := by
    have e₁ : (Scheme.ΓSpecIso (CommRingCat.of (R ι N))).inv ≫
        ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).inv ≫
        Points.valMap (Spec.map ψ ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) (cellU w) h = ψ := by
      rw [Points.valMap, ← Scheme.Hom.appLE_comp_appLE (Spec.map ψ) _ (cellU w) ⊤ ⊤ (by simp [cellU]) le_rfl,
        Category.assoc]
      erw [Scheme.Hom.appIso_inv_appLE_assoc]
      have e₂ : (Spec.map ψ).appLE ⊤ ⊤ le_rfl = (Spec.map ψ).appTop := (Scheme.Hom.app_eq_appLE _).symm
      rw [e₂]
      simp [← Scheme.ΓSpecIso_inv_naturality_assoc]
    exact congrArg CommRingCat.Hom.hom e₁
  refine (spMap_flagPt _ _ ψ.hom _).trans ?_
  congr 1
  funext τ
  rw [← e]
  rfl

end GlobalTheory.FlagZ.StepDet
