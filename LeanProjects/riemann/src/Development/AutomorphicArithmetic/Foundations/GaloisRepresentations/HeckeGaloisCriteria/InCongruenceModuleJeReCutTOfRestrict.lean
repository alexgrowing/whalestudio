import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ActEqZeroOfQK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement

noncomputable section

namespace UpperTheory.GalC

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices Formalism Formalism.BasicNotions Formalism.MainNotions.N UpperTheory.GalC.Alg

variable {A X Γ : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Group Γ] {n r : ℕ}
  {T : Subalgebra A (X → A)} (S : Set X) {rep : X → (Γ →* GL (Fin n) A)}

theorem mem_cutT {f : X → A} (hf : f ∈ T) : (fun y : S => f y.1) ∈ cutT T S := ⟨f, hf, rfl⟩

theorem inRing_cut {a : X → Matrix (Fin n) (Fin n) A} (h : InRing T rep a) :
    InRing (cutT T S) (fun y : S => rep y.1) (fun y => a y.1) := by
  obtain ⟨m, f, g, hf, rfl⟩ := h
  refine ⟨m, fun k y => f k y.1, g, fun k => mem_cutT S (hf k), ?_⟩
  funext y
  simp [Finset.sum_apply]

theorem inCongruenceModuleJeRe_cutT_of_restrict {π : S} {e s : X → Matrix (Fin n) (Fin n) A} (h : InMatrixCongruenceModule T rep π.1 e s) :
    InMatrixCongruenceModule (cutT T S) (fun y : S => rep y.1) π (fun y => e y.1) (fun y => s y.1) := by
  obtain ⟨m, j, a, hj, rfl⟩ := h
  refine ⟨m, fun k y => j k y.1, fun k y => a k y.1, fun k => ⟨mem_cutT S (hj k).1, (hj k).2.1, inRing_cut S (hj k).2.2⟩, ?_⟩
  funext y
  simp [Finset.sum_apply]

theorem setting_cut [Nonempty S] {t : ℕ} {Z : Finset X} {Z' : Finset S} (hZ : ∀ y ∈ Z', y.1 ∈ Z)
    {ρ : X → (Γ →* GL (Fin r) A)} {χ : ℕ → (Γ →* Aˣ)} (h : HidaSetting t T Z rep ρ χ) :
    HidaSetting t (cutT T S) Z' (fun y : S => rep y.1) (fun y => ρ y.1) χ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  haveI := h1
  refine ⟨cutT_local T S, fun x y hxy => ?_, fun x => h3 x.1, fun g d => mem_cutT S (h4 g d), fun x => h5 x.1,
    fun x y g => h6 x.1 y.1 g, fun x hx => h7 x.1 (hZ x hx), fun x hx => h8 x.1 (hZ x hx)⟩
  obtain ⟨f, hf, hne⟩ := h2 x.1 y.1 fun e => hxy (Subtype.ext e)
  exact ⟨_, mem_cutT S hf, hne⟩

theorem isChoice_cut {t : ℕ} {ρ : X → (Γ →* GL (Fin r) A)} {χ : ℕ → (Γ →* Aˣ)} {π : S} {g0 : Γ} {L : ℕ}
    {eB e1 X0 : X → Matrix (Fin n) (Fin n) A} (h : IsChoice t T rep ρ χ π.1 g0 L eB e1 X0) :
    IsChoice t (cutT T S) (fun y : S => rep y.1) (fun y => ρ y.1) χ π g0 L (fun y => eB y.1) (fun y => e1 y.1)
      (fun y => X0 y.1) := by
  obtain ⟨⟨hB, h1, hBB, h11, hB1, h1B⟩, hdec, ⟨ϖ, s, hϖ, hs, rfl⟩, hroot⟩ := h
  refine ⟨⟨inRing_cut S hB, inRing_cut S h1, ?_, ?_, ?_, ?_⟩, hdec, ⟨ϖ, fun y => s y.1, hϖ, inCongruenceModuleJeRe_cutT_of_restrict S hs, rfl⟩,
    fun y => hroot y.1⟩
  · funext y; exact congrFun hBB y.1
  · funext y; exact congrFun h11 y.1
  · funext y; exact congrFun hB1 y.1
  · funext y; exact congrFun h1B y.1

theorem span_cut {O : Type} [CommRing O] [IsDomain O] [Algebra A O] {TO : Subalgebra O (X → O)}
    (h : Subalgebra.toSubmodule TO = Submodule.span O ((fun f : X → A => fun x => algebraMap A O (f x)) '' (T : Set _))) :
    Subalgebra.toSubmodule (cutT TO S) =
      Submodule.span O ((fun f : S → A => fun x => algebraMap A O (f x)) '' (cutT T S : Set _)) := by
  have e1 : Subalgebra.toSubmodule (cutT TO S) = (Subalgebra.toSubmodule TO).map (resA O S).toLinearMap :=
    Subalgebra.map_toSubmodule
  rw [e1, h, Submodule.map_span, cutT, Subalgebra.coe_map, ← Set.image_comp, ← Set.image_comp]
  rfl

end UpperTheory.GalC
