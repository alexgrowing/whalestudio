import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHEqvPf
open LateralTheory.E.t_E3Cut

def SecBij : Prop := SHSection → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) →
  SH A → SH B → Function.Bijective (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s)

def SecPre : Prop := SHSection → ∀ (q : ℕ) (i : ℤ) (A : CommRingCat.{0}), SH A →
  Function.Bijective (ofRings.sec (twF q i) (Spec A))

def TwFBij : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B →
  Function.Bijective ((twF q i).map (Spec.map f).appTop).hom

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (j : V ⟶ U)
    (m : M.obj Γ(U, ⊤)) : Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op
  have h2 := congrArg (fun φ => φ.hom m) h
  exact h2.symm

theorem SecBij_of (hP : SecPre) (hT : TwFBij) : SecBij := by
  intro hSec q _ i A B f hq hA hB
  have key : (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s) =
      ofRings.sec (twF q i) (Spec B) ∘ ((twF q i).map (Spec.map f).appTop).hom ∘
        (Equiv.ofBijective _ (hP hSec q i A hA)).symm := by
    funext s
    obtain ⟨m, rfl⟩ := (hP hSec q i A hA).2 s
    simp only [Function.comp]
    rw [Equiv.ofBijective_symm_apply_apply]
    exact sec_res _ _ _
  rw [key]
  exact (hP hSec q i B hB).comp ((hT q i f hq hA hB).comp (Equiv.bijective (Equiv.ofBijective _ (hP hSec q i A hA)).symm))

theorem bij_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (g : M →+ N) : Function.Bijective g :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

theorem SHEqv_of_secBij (hSec : SHSection) (hB : SecBij) : SHEqv := by
  intro hyp q _ i A B f hq hA hBs n
  obtain ⟨_, _, _, _, _, hA9, _, hB2, _⟩ := hyp
  obtain ⟨hneg, e, he, -⟩ := hA9 (ZMod q) (tw q i)
  rcases lt_trichotomy n 0 with h | h | h
  · haveI := hneg (sch.obj (Spec A)) n h
    haveI := hneg (sch.obj (Spec B)) n h
    exact bij_of_subsingleton _
  · subst h
    have key : ⇑(pull (ZMod q) (sch.map (Spec.map f)) (tw q i) 0) =
        (e (Spec B)) ∘ (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s) ∘ (e (Spec A)).symm := by
      funext x
      simp only [Function.comp]
      rw [← he]
      simp
    show Function.Bijective (pull (ZMod q) (sch.map (Spec.map f)) (tw q i) 0)
    rw [key]
    exact (e _).bijective.comp ((hB hSec q i f hq hA hBs).comp (e _).symm.bijective)
  · haveI := hB2 (ZMod q) A hA (tw q i) n h
    haveI := hB2 (ZMod q) B hBs (tw q i) n h
    exact bij_of_subsingleton _

end LateralTheory.E.SHEqvPf
