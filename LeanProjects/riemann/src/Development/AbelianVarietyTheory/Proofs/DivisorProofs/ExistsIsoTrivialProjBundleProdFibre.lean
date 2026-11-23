import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem comp_trivV (N : ℕ) {E E' : Spc} (f : E' ⟶ E) : f ≫ trivV N E = trivV N E' := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

theorem hom_ext_invertibleLocus (q : ℕ) {E : Spc} (f g : E ⟶ disc.obj (invP q)) : f = g := by
  ext n U x
  exact Subsingleton.elim (α := PLift _) _ _

def toInvP (q : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) : disc.obj F ⟶ disc.obj (invP q) :=
  disc.map
    { app := fun U => TypeCat.ofHom fun x => ⟨hF U.unop ⟨x⟩⟩
      naturality := fun _ _ _ => by ext x; rfl }

def fibQ.snd (q N : ℕ) : fibQ q N ⟶ PGL N := pullback.snd _ _

theorem fibQ.cond (q N : ℕ) : trivV N (fibQ q N) = fibQ.snd q N ≫ PGL.pr N := by
  show trivV N (pullback (trivV N (disc.obj (invP q))) (PGL.pr N)) = pullback.snd _ _ ≫ PGL.pr N
  rw [← comp_trivV N (pullback.fst (trivV N (disc.obj (invP q))) (PGL.pr N))]
  exact pullback.condition

def fibQ.lift {q N : ℕ} {X : Spc} (a : X ⟶ disc.obj (invP q)) (b : X ⟶ PGL N) (h : trivV N X = b ≫ PGL.pr N) :
    X ⟶ fibQ q N :=
  pullback.lift a b (by rw [comp_trivV]; exact h)

@[simp] theorem fibQ.lift_snd {q N : ℕ} {X : Spc} (a : X ⟶ disc.obj (invP q)) (b : X ⟶ PGL N)
    (h : trivV N X = b ≫ PGL.pr N) : fibQ.lift a b h ≫ fibQ.snd q N = b :=
  pullback.lift_snd _ _ _

theorem fibQ.hom_ext {q N : ℕ} {X : Spc} {f g : X ⟶ fibQ q N} (h : f ≫ fibQ.snd q N = g ≫ fibQ.snd q N) : f = g :=
  pullback.hom_ext (hom_ext_invertibleLocus q _ _) h

theorem trivProj_iso (q N : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) :
    ∃ θ : disc.obj F ⨯ fibQ q N ≅ pullback (trivV N (disc.obj F)) (PGL.pr N),
      θ.hom ≫ pullback.fst _ _ = prod.fst ∧ θ.hom ≫ pullback.snd _ _ ≫ PGL.line N = prod.snd ≫ lineQ q N := by
  have h1 : prod.fst ≫ trivV N (disc.obj F) = (prod.snd ≫ fibQ.snd q N) ≫ PGL.pr N := by
    rw [comp_trivV, Category.assoc, ← fibQ.cond, comp_trivV]
  have h2 : trivV N (pullback (trivV N (disc.obj F)) (PGL.pr N)) = pullback.snd _ _ ≫ PGL.pr N := by
    rw [← comp_trivV N (pullback.fst (trivV N (disc.obj F)) (PGL.pr N))]
    exact pullback.condition
  let hom : disc.obj F ⨯ fibQ q N ⟶ pullback (trivV N (disc.obj F)) (PGL.pr N) :=
    pullback.lift prod.fst (prod.snd ≫ fibQ.snd q N) h1
  let inv : pullback (trivV N (disc.obj F)) (PGL.pr N) ⟶ disc.obj F ⨯ fibQ q N :=
    prod.lift (pullback.fst _ _) (fibQ.lift (pullback.fst _ _ ≫ toInvP q F hF) (pullback.snd _ _) h2)
  refine ⟨{ hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_, ?_⟩
  · apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, pullback.lift_fst, Category.id_comp]
    · apply fibQ.hom_ext
      rw [Category.assoc, Category.assoc, ← Category.assoc inv, prod.lift_snd, fibQ.lift_snd, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, prod.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, prod.lift_snd, fibQ.lift_snd, Category.id_comp]
  · exact pullback.lift_fst _ _ _
  · rw [← Category.assoc, pullback.lift_snd, Category.assoc]
    rfl

end GlobalTheory.EtC

end
