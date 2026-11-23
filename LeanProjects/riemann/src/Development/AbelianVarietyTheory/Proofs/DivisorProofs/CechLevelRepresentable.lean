import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

def IsPow (n : ℕ) (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)) : Prop :=
  (∀ i, p i ≫ f = p 0 ≫ f) ∧ ∀ (U : Scheme.{0}) (y : Fin (n + 1) → (U ⟶ V)), (∀ i, y i ≫ f = y 0 ≫ f) →
    ∃! g : U ⟶ Z, ∀ i, g ≫ p i = y i

theorem exists_pow (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    (hf : P f) (n : ℕ) : ∃ (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)), IsPow f n Z p ∧ P (p 0) := by
  induction n with
  | zero =>
    refine ⟨V, fun _ => 𝟙 V, ⟨fun _ => rfl, fun U y _ => ⟨y 0, fun i => ?_, fun g hg => ?_⟩⟩, P.id_mem V⟩
    · rw [Fin.fin_one_eq_zero i]; simp
    · simpa using hg 0
  | succ n ih =>
    obtain ⟨Z, p, ⟨hc, hu⟩, hP⟩ := ih
    let q : Fin (n + 2) → (pullback (p 0 ≫ f) f ⟶ V) :=
      Fin.snoc (α := fun _ => pullback (p 0 ≫ f) f ⟶ V) (fun j => pullback.fst _ _ ≫ p j) (pullback.snd _ _)
    have qc : ∀ j : Fin (n + 1), q j.castSucc = pullback.fst _ _ ≫ p j := fun j => by simp [q]
    have ql : q (Fin.last _) = pullback.snd _ _ := by simp [q]
    have hz : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 2)) = 0 := rfl
    have q0 : q 0 = pullback.fst _ _ ≫ p 0 := qc 0
    refine ⟨pullback (p 0 ≫ f) f, q, ⟨fun i => ?_, fun U y hy => ?_⟩, ?_⟩
    · rw [q0]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [ql, ← pullback.condition, Category.assoc]
      · rw [qc, Category.assoc, Category.assoc, hc j]
    · have h' : ∀ j : Fin (n + 1), y j.castSucc ≫ f = y (Fin.castSucc 0) ≫ f := fun j => by
        rw [hy, hz, hy]
      obtain ⟨g0, hg0, hg0u⟩ := hu U (fun j => y j.castSucc) h'
      have hw : g0 ≫ p 0 ≫ f = y (Fin.last _) ≫ f := by
        rw [← Category.assoc, hg0 0, hy (Fin.last _), hz]
      refine ⟨pullback.lift g0 (y (Fin.last _)) hw, fun i => ?_, fun g hg => ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [ql, pullback.lift_snd]
        · rw [qc, pullback.lift_fst_assoc, hg0 j]
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine hg0u _ (fun j => ?_)
          rw [Category.assoc, ← qc, hg]
        · rw [pullback.lift_snd, ← ql, hg]
    · rw [q0]
      exact P.comp_mem _ _ (P.pullback_fst _ _ hf) hP

end GlobalTheory.EtC.CechRep

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

noncomputable section

def isLimitPow {n : ℕ} {Z : Scheme.{0}} {p : Fin (n + 1) → (Z ⟶ V)} (h : IsPow f n Z p) :
    IsLimit (WidePullbackShape.mkCone (F := WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f))
      (p 0 ≫ f) p (fun j => h.1 j)) := by
  have hs : ∀ s : Cone (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f)),
      ∀ j, s.π.app (some j) ≫ f = s.π.app (some 0) ≫ f := fun s j => by
    have a : s.π.app (some j) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term j)
    have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
    rw [a, b]
  refine IsLimit.mk (fun s => (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose) (fun s j => ?_)
    (fun s m hm => ?_)
  · have hl := (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec
    cases j with
    | none =>
      have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
      change (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose ≫ (p 0 ≫ f) = s.π.app none
      rw [← Category.assoc, hl 0]
      exact b
    | some j =>
      exact hl j
  · exact (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).unique (fun j => hm (some j))
      (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec

end

end GlobalTheory.EtC.CechRep

theorem GlobalTheory.EtC.cech_level_representable : ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] (V W : Scheme.{0}) (f : V ⟶ W), P f → ∀ k : SimplexCategoryᵒᵖ, ∃ (Z : Scheme.{0}) (π : Z ⟶ V) (e : yoneda.obj Z ≅ (cech f).obj k), P π ∧ e.hom ≫ (cechAug f).app k = yoneda.map (π ≫ f) := by
  intro P _ _ V W f hf k
  obtain ⟨Z, p, h, hP⟩ := GlobalTheory.EtC.CechRep.exists_pow f P hf k.unop.len
  have hY := isLimitOfPreserves yoneda (GlobalTheory.EtC.CechRep.isLimitPow f h)
  let D := WidePullbackShape.wideCospan (yoneda.obj W) (fun _ : Fin (k.unop.len + 1) => yoneda.obj V)
    (fun _ => yoneda.map f)
  let iso : WidePullbackShape.wideCospan W (fun _ : Fin (k.unop.len + 1) => V) (fun _ => f) ⋙ yoneda ≅ D :=
    WidePullbackShape.diagramIsoWideCospan _
  have hL := (IsLimit.postcomposeHomEquiv iso _).symm hY
  refine ⟨Z, p 0, IsLimit.conePointUniqueUpToIso hL (limit.isLimit D), hP, ?_⟩
  have := IsLimit.conePointUniqueUpToIso_hom_comp hL (limit.isLimit D) none
  change _ ≫ limit.π D none = _
  refine this.trans ?_
  change yoneda.map (p 0 ≫ f) ≫ iso.hom.app none = _
  simp [iso, WidePullbackShape.diagramIsoWideCospan]
  first | exact Category.comp_id _ | rfl | (erw [eqToHom_refl, Category.comp_id])
