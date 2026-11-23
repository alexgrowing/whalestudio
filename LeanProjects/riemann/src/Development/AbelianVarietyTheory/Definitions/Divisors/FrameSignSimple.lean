import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj.SumModel

open GlobalTheory.ChiGrid Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem frameSign_simple {R : Type} [CommRing R] (n n' : Matrix (Fin 5) (Fin 5) R)
    (hn : ∀ i j, j ≤ i → n i j = if i = j then 1 else 0) (hn' : ∀ i j, j ≤ i → n' i j = if i = j then 1 else 0)
    (h : n'ᵀ * antiDiagonalSignGramMatrix 5 (-1 : R) * n = antiDiagonalSignGramMatrix 5 (-1 : R)) :
    (n 0 1 - n' 0 1) + (n 1 2 - n' 1 2) =
      ∑ p : Fin 4, frameSign R 5 p.castSucc * n p.castSucc p.succ * frameSign R 5 p.succ := by
  have h1 := congrFun (congrFun h 1) 4
  have h2 := congrFun (congrFun h 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_five, antiDiagonalSignGramMatrix, hn, hn'] at h1 h2
  simp [Fin.sum_univ_four, frameSign]
  linear_combination (-1 : R) * h1 - h2

theorem readOK {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) : ReadOK σ := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ Φ fun F => (h F _).2 rfl

theorem covOf_funOf {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) (F : VV ℂ σ) : covOf σ (funOf σ F) = F := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  have h1 := (h _ _).1 ((readOK σ).1 F)
  have h2 := (h _ _).1 ((readOK σ).2 (funOf σ F))
  exact Φ.injective (h2.symm.trans h1)

theorem funOf_rhoV {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (σ : ι → DomWeight n)
    (γ : GL (Fin n) E) (F : VV ℂ σ) :
    funOf σ (rhoK σ (embGL emb γ) F) = rhoK (fun τ => (σ τ).dual) (invTrK (embGL emb γ)) (funOf σ F) := by
  obtain ⟨Φ, h, h', -⟩ := funForm (K := ℂ) σ
  rw [(h _ _).1 ((readOK σ).1 F), (h _ _).1 ((readOK σ).1 _), h']

theorem finEmb_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) (x : GfC B)
    (h : EmbRel B A d.ι x.1 y.1) : finEmb d y = x :=
  Subtype.ext ((GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom y.1).unique (finEmb_rel d y) h)

theorem finEmb_mul {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y y' : GfC A) :
    finEmb d (y * y') = finEmb d y * finEmb d y' := by
  refine finEmb_eq d _ _ ⟨?_, fun v hv => ?_⟩
  · have h1 := (finEmb_rel d y).1
    have h2 := (finEmb_rel d y').1
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  · have h1 := (finEmb_rel d y).2 v hv
    have h2 := (finEmb_rel d y').2 v hv
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, h2, h1]

theorem exists_places : ∃ PA : Finset (Pl D.host.E),
    (∀ w ∈ PA, FractionalIdeal.count D.host.E w D.host.AA ≠ 0 ∨ FractionalIdeal.count D.host.E w D.host.AAbar ≠ 0) ∧
    ∀ w, FractionalIdeal.count D.host.E w D.host.AA ≠ 0 → ∃! w', w' ∈ PA ∧ w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  classical
  have hf : {w : Pl D.host.E | FractionalIdeal.count D.host.E w D.host.AA ≠ 0}.Finite :=
    Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors D.host.AA)
  let p : Pl D.host.F → Pl D.host.E → Prop := fun v w => FractionalIdeal.count D.host.E w D.host.AA ≠ 0 ∧ w.under (𝓞 D.host.F) = v
  let f : ∀ w : Pl D.host.E, FractionalIdeal.count D.host.E w D.host.AA ≠ 0 → Pl D.host.E := fun w h =>
    (⟨w, h, rfl⟩ : ∃ w', p (w.under (𝓞 D.host.F)) w').choose
  have hp : ∀ w h, p (w.under (𝓞 D.host.F)) (f w h) := fun w h => Exists.choose_spec _
  have hc : ∀ w h w' h', w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → f w h = f w' h' := fun w h w' h' e => by
    simp only [f, e]
  refine ⟨hf.toFinset.attach.image fun w => f w.1 (hf.mem_toFinset.1 w.2), fun w hw => ?_, fun w h => ⟨f w h, ⟨?_, (hp w h).2⟩, ?_⟩⟩
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hw
    exact Or.inl (hp _ (hf.mem_toFinset.1 a.2)).1
  · exact Finset.mem_image.2 ⟨⟨w, hf.mem_toFinset.2 h⟩, Finset.mem_attach _ _, rfl⟩
  · rintro w' ⟨hw, e⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hw
    exact hc _ (hf.mem_toFinset.1 a.2) _ h ((hp _ (hf.mem_toFinset.1 a.2)).2.symm.trans e)

theorem nonempty_empty {G : GridData L sc} (W : G.Weil) (N : Std G (∅ : Set T)) (Z : Normal W N) : Nonempty (GridChoice W ∅) := by
  obtain ⟨PA, h1, h2⟩ := exists_places (D := D)
  have h : ∀ j, ∃ β : GL (Fin (G.V (.top j)).rank) (Lev.EAf D), j ≤ D.R.m → IsFrame β (G.Λ (.top j)) := fun j => by
    by_cases hj : j ≤ D.R.m
    · have hl := (G.isV (X := .top j) hj fun _ e => by cases e).sd.1
      obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ hl.fg hl.span_eq_top
      exact ⟨β, fun _ => hβ⟩
    · exact ⟨1, fun a => absurd a hj⟩
  choose β hβ using h
  exact ⟨⟨Classical.arbitrary _, β, hβ, fun _ h => h.elim, fun _ h => h.elim, N, Z, PA, h1, h2⟩⟩

end GlobalTheory.FunObj.SumModel

end
