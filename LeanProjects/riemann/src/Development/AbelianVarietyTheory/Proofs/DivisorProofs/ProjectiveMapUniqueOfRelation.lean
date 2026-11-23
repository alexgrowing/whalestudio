import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.LineQuot

theorem isUnit_pullRatio_of_frame {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {i j : Fin (N + 1)}
    (hi : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N i) (hb : Function.Bijective ((s j).app V))
    {e : Fin 1 → Γ(Q, V)} (he : IsFrame e) : IsUnit (ProjSpace.pullRatio χ V i hi j) := by
  set b := he.basis (le_refl V)
  obtain ⟨t, ht⟩ := hb.2 (b 0)
  set c := b.repr ((s i).app V t) 0
  have hc : (s i).app V t = c • b 0 := by
    conv_lhs => rw [← b.sum_repr ((s i).app V t)]
    simp [Fin.sum_univ_one, c]
  have h1 := hχ i j V hi t
  rw [ht, hc, smul_smul] at h1
  have h2 := congrArg (fun x => b.repr x 0) h1
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] at h2
  exact .of_mul_eq_one _ h2.symm

theorem pullRatio_smul_eq {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {j : Fin (N + 1)}
    (hj : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N j) (t : Γ(L, V)) (m : Fin (N + 1)) :
    (s m).app V t = ProjSpace.pullRatio χ V j hj m • (s j).app V t :=
  hχ j m V hj t

theorem le_preimage_chart {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} {L Q : T.Modules}
    {s : Fin (N + 1) → (L ⟶ Q)} {χ : T ⟶ PSpace k N} (hχ : Rel χ s) {V : T.Opens} {i j : Fin (N + 1)}
    (hi : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N i) (hb : Function.Bijective ((s j).app V))
    {e : Fin 1 → Γ(Q, V)} (he : IsFrame e) : V ≤ χ ⁻¹ᵁ ProjSpace.chart k N j := by
  have h := ProjSpace.basicOpen_pullRatio (φ := χ) (W := V) (i := i) (hi := hi) (j := j)
  rw [T.basicOpen_of_isUnit (isUnit_pullRatio_of_frame hχ hi hb he)] at h
  exact h.le.trans inf_le_right

theorem exists_mem_preimage_chart {k : Type} [CommRing k] {N : ℕ} {T : Scheme.{0}} (χ : T ⟶ PSpace k N)
    (y : T) : ∃ i, y ∈ χ ⁻¹ᵁ ProjSpace.chart k N i := by
  have : χ y ∈ (⨆ i, ProjSpace.chart k N i : (PSpace k N).Opens) := by
    rw [ProjSpace.iSup_chart]; trivial
  exact (TopologicalSpace.Opens.mem_iSup (s := fun i => ProjSpace.chart k N i)).1 this

theorem eq_of_rel : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q : T.Modules)
    (s : Fin (N + 1) → (L ⟶ Q)) (φ ψ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Gen s →
    φ ≫ PSpace.str k N = ψ ≫ PSpace.str k N → Rel φ s → Rel ψ s → φ = ψ := by
  intro k _ N T L Q s φ ψ _ hQ hG hstr hφ hψ
  refine ProjSpace.hom_ext hstr fun y => ?_
  obtain ⟨j, W, hyW, hbij⟩ := hG y
  obtain ⟨i, hi⟩ := exists_mem_preimage_chart φ y
  obtain ⟨l, hl⟩ := exists_mem_preimage_chart ψ y
  obtain ⟨V, e, -, hyV, hV, he⟩ := hQ.exists_affine
    (V := W ⊓ φ ⁻¹ᵁ ProjSpace.chart k N i ⊓ ψ ⁻¹ᵁ ProjSpace.chart k N l) ⟨⟨hyW, hi⟩, hl⟩
  have hb := hbij V (hV.trans (inf_le_left.trans inf_le_left))
  have hjφ := le_preimage_chart hφ (hV.trans (inf_le_left.trans inf_le_right)) hb he
  have hjψ := le_preimage_chart hψ (hV.trans inf_le_right) hb he
  refine ⟨V, hyV, j, hjφ, hjψ, fun m => ?_⟩
  set b := he.basis (le_refl V)
  obtain ⟨t, ht⟩ := hb.2 (b 0)
  have h := (pullRatio_smul_eq hφ hjφ t m).symm.trans (pullRatio_smul_eq hψ hjψ t m)
  rw [ht] at h
  have h2 := congrArg (fun x => b.repr x 0) h
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] using h2

end GlobalTheory.LineQuot
