import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMemSpanField

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.SeamSelfDual

theorem mem_range_iff {E : Type} [Field E] (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem mem_one_iff {E : Type} [Field E] (x : E) :
    x ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one, ← mem_range_iff]
  rfl

theorem isIntegral_map {E E' : Type} [Field E] [Field E'] (f : E →+* E') {x : E}
    (h : IsIntegral ℤ x) : IsIntegral ℤ (f x) :=
  h.map f.toIntAlgHom

theorem isSDLat_pi (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    IsSDLat E n (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  classical
  have hm : ∀ x : Fin n → E, x ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
      ∀ i, IsIntegral ℤ (x i) := by
    intro x
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, mem_one_iff]
  have hs : ∀ i : Fin n, (Pi.single i 1 : Fin n → E) ∈
      (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
    intro i
    rw [hm]
    intro j
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun hy => ?_⟩⟩
  · rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact hs i
  · rw [mem_range_iff]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => (isIntegral_map (starRingEnd E) (hx i)).mul (hy i)
  · rw [hm]
    intro i
    have := hy _ (hs i)
    rw [mem_range_iff] at this
    have e : stdH E n (Pi.single i 1) y = y i := by
      unfold stdH
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    rwa [e] at this

section Transport

variable {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}

theorem isSDLat_image [NumberField E] [NumberField E'] [StarRing E] [StarRing E']
    (hf : ∀ x, f (star x) = star (f x)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSDLat E n L) :
    IsSDLat E' n (Submodule.span (𝓞 E')
      ((fun (x : Fin n → E) (i : Fin n) => f (x i)) '' (L : Set (Fin n → E)))) := by
  first
  | exact @_root_.GlobalTheory.StandardLatticeSpan.isSDLat_map
  | exact _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map
  | (apply _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map ..)

end Transport

theorem isSDLat_of_isSdLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) : IsSDLat E n L := by
  obtain ⟨h1, h2⟩ := hL
  refine ⟨h1.fg, h1.span_eq_top, fun y => ?_⟩
  have h3 : y ∈ L ↔ y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
    rw [show Formalism.HermitianLatticesTheory.dual (hStd E n) L = L from h2]
  rw [h3]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, mem_one_iff, mem_range_iff]
  rfl

theorem seam_selfDual : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → ∀ (n : ℕ), StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat L → StandardLatticesGL3.SD D (s.lat L) := by
  intro D X s hs n
  letI := D.host.cmStar
  refine ⟨isSDLat_pi D.host.E n, fun L hL => ?_⟩
  exact isSDLat_image s.iE (fun x => (hs.2 x).trans (bridge_star_holds D.R D.host _).symm) L
    (isSDLat_of_isSdLat L hL)

end GlobalTheory.SeamSelfDual
