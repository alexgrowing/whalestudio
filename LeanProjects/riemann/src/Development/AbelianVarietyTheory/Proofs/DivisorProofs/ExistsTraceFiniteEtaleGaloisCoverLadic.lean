import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.E5
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceOfFiniteEtaleDegree

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TrGal

open GlobalTheory.EtC.Tr GlobalTheory.EtC.TrDeg

variable (R : Type) [CommRing R]

theorem splitBy_of_equiv {Y X V : Scheme.{0}} (f : Y ⟶ X) (y : V ⟶ X) {G : Type} {m : ℕ} (e : Fin m ≃ G)
    (a : G → (V ⟶ Y)) (ha : ∀ g, a g ≫ f = y)
    (h : IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 V) (by rw [ha g, Category.id_comp])) :
      ∐ (fun _ : G => V) ⟶ pullback f y)) : SplitBy f y (fun j => a (e j)) := by
  refine ⟨fun j => ha _, ?_⟩
  let w : ∐ (fun _ : Fin m => V) ≅ ∐ (fun _ : G => V) := Sigma.reindex e (fun _ : G => V)
  have hw : ∀ j, Sigma.ι (fun _ : Fin m => V) j ≫ w.hom = Sigma.ι (fun _ : G => V) (e j) := fun j =>
    Sigma.ι_reindex_hom e (fun _ : G => V) j
  convert (inferInstance : IsIso (w.hom ≫ (Sigma.desc (fun g => pullback.lift (a g) (𝟙 V) (by rw [ha g, Category.id_comp])) :
      ∐ (fun _ : G => V) ⟶ pullback f y)))
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_desc, reassoc_of% (hw j), Sigma.ι_desc]

theorem along_sum {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) {ι : Type} (s : Finset ι) (t : ι → (freeSch R X ⟶ freeSch R Y))
    (x : H R (sch.obj Y) F n) : along R F n (∑ j ∈ s, t j) x = ∑ j ∈ s, along R F n (t j) x :=
  map_sum (AddMonoidHom.mk' (fun u : freeSch R X ⟶ freeSch R Y => along R F n u x) (fun u v => along_add R F n u v x)) t s

theorem pull_trH {Y X V : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Y)} (hs : SplitBy f y s) (F : Shv R) (n : ℤ) (x : H R (sch.obj Y) F n) :
    pull R (sch.map y) F n (trH R f F n x) = ∑ j, pull R (sch.map (s j)) F n x := by
  rw [trH, ← along_free, ← along_comp,
    (transfer_spec R (existsUnique_isTransfer R f).exists).apply_of_splitBy R hs, along_sum]
  simp only [along_free]

theorem exists_trace_galois : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, ∃ tr : Hl l (sch.obj Y) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i,
  (∀ x, tr (pullHl l (sch.map f) n i x) = Fintype.card G • x) ∧ ∀ y, pullHl l (sch.map f) n i (tr y) = ∑ g, pullHl l (sch.map (a g)) n i y := by
  intro l _ Y X f _ _ _ G _ a ha hiso n i
  have hs := splitBy_of_equiv f f (Fintype.equivFin G).symm a ha hiso
  have h := trHl_spec l (redCompat_of_finite_etale l f (fun R _ => existsUnique_isTransfer R f) n i)
  refine ⟨trHl l f n i, fun x => Subtype.ext (funext fun k => ?_), fun y => Subtype.ext (funext fun k => ?_)⟩
  · exact (h _ k).trans (trH_pull (ZMod (l ^ k)) f hs (tw (l ^ k) i) n (x.1 k))
  · rw [← Equiv.sum_comp (Fintype.equivFin G).symm, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    exact (congrArg (pull (ZMod (l ^ k)) (sch.map f) (tw (l ^ k) i) n) (h y k)).trans
      (pull_trH (ZMod (l ^ k)) f hs (tw (l ^ k) i) n (y.1 k))

end GlobalTheory.EtC.TrGal

end
