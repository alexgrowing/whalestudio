import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

theorem Spans.exists_basis {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V : X.Opens}
    {v : Fin m → Γ(F, V)} (h : Spans fl V v) :
    ∃ b : Module.Basis (Fin m) Γ(X, V) Γ(F, V), ∀ j, b j = v j := by
  obtain ⟨s, hs, e⟩ := h (Fin.last m)
  have hf := hs.map_iso (fl.ι (Fin.last m))
  refine ⟨hf.basis le_rfl, fun j => ?_⟩
  refine (hf.basis_apply le_rfl j).trans ((GlobalTheory.Twist.resM_self _ _).trans ((e j).trans ?_))
  rfl

theorem Spans.mem_span {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V : X.Opens}
    {v v' : Fin m → Γ(F, V)} (h : Spans fl V v) (h' : Spans fl V v') (j : Fin m) :
    v' j ∈ Submodule.span Γ(X, V) (v '' {k | k ≤ j}) := by
  obtain ⟨s, hs, e⟩ := h j.succ
  obtain ⟨s', -, e'⟩ := h' j.succ
  let i : Fin (j.succ : ℕ) := ⟨j, by simp⟩
  have hj : v' j = GlobalTheory.QCoh.appLinear (fl.ι j.succ) V (s' i) := (e' i).symm
  rw [hj, ← (hs.basis le_rfl).sum_repr (s' i), map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE j.succ.is_le k, ?_, ?_⟩)
  · have := k.2
    simp only [Fin.val_succ] at this
    change (k : ℕ) ≤ j
    omega
  · rw [hs.basis_apply, GlobalTheory.Twist.resM_self]
    exact (e k).symm

theorem spans_change : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl : Vert.Flag F m) (V : X.Opens) (v v' : Fin m → Γ(F, V)), Spans fl V v → Spans fl V v' → ∃ M : Matrix (Fin m) (Fin m) Γ(X, V), M.BlockTriangular id ∧ IsUnit M.det ∧ ∀ j, v' j = ∑ k, M k j • v k := by
  intro X F m fl V v v' h h'
  obtain ⟨b, hb⟩ := h.exists_basis
  obtain ⟨b', hb'⟩ := h'.exists_basis
  have e : ⇑b = v := funext hb
  have e' : ⇑b' = v' := funext hb'
  refine ⟨b.toMatrix v', fun i j hij => ?_, ?_, fun j => ?_⟩
  · have hm := h.mem_span h' j
    rw [← e, Module.Basis.mem_span_image] at hm
    rw [Module.Basis.toMatrix_apply]
    by_contra hne
    exact absurd (hm (Finsupp.mem_support_iff.2 hne)) (not_le.2 hij)
  · rw [← e']
    exact b.isUnit_det b'
  · rw [← e]
    exact (b.sum_toMatrix_smul_self v' j).symm

end GlobalTheory.FlagCell
