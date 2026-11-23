import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagIdPf

theorem par_self {A : Type} [CommRing A] {P : LateralTheory.E.PartDiagCut.Part A} (h : P ≤ P) (e : P.1) : par h e = e := by
  apply Subtype.ext
  by_contra hne
  have h1 := par_spec h e
  have h2 := P.orth e.1 e.2 (par h e).1 (par h e).2 (fun h' => hne h'.symm)
  exact (P.idem e.1 e.2).2 (h1.symm.trans h2)

theorem aux {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P) (e0 e : P.1) (hee : e0 = e)
    (hle : S I e0.1 ≤ (S I e.1).comap (RingHom.id B)) :
    IsLocalization.map (M := S I e0.1) (T := S I e.1) (Localization (S I e.1)) (RingHom.id B) hle (x e0) = x e := by
  subst hee
  exact IsLocalization.map_id _ _

theorem DiagId_of : LateralTheory.E.PartDiagCut.DiagId := by
  intro B _ I P h
  refine RingHom.ext fun x => funext fun e => ?_
  simp only [stageMap, RingHom.pi_apply, RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.id_apply]
  exact aux I P x (par h e) e (par_self h e) _

end LateralTheory.E.DiagIdPf
