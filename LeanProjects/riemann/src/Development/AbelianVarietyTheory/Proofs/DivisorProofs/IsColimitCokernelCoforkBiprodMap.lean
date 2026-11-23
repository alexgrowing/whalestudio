import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Vert.Flag

variable {X : Scheme.{0}} {E E₁ E₂ : X.Modules} {N r s : ℕ}

theorem biprodMap_comp_biprodMap_π {A B C D : X.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    biprod.map f g ≫ biprod.map (cokernel.π f) (cokernel.π g) = 0 := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

def cokernelCoforkBiprodMap {A B C D : X.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    CokernelCofork (biprod.map f g) :=
  CokernelCofork.ofπ (biprod.map (cokernel.π f) (cokernel.π g)) (biprodMap_comp_biprodMap_π f g)

def isColimitCokernelCoforkBiprodMap {A B C D : X.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    IsColimit (cokernelCoforkBiprodMap f g) :=
  CokernelCofork.IsColimit.ofπ _ (biprodMap_comp_biprodMap_π f g)
    (fun k hk => biprod.desc
      (cokernel.desc f (biprod.inl ≫ k) (by
        have := congrArg (biprod.inl ≫ ·) hk
        simpa using this))
      (cokernel.desc g (biprod.inr ≫ k) (by
        have := congrArg (biprod.inr ≫ ·) hk
        simpa using this)))
    (fun k hk => by
      refine biprod.hom_ext' _ _ ?_ ?_ <;> simp)
    (fun k hk m hm => by
      apply biprod.hom_ext'
      · refine (cancel_epi (cokernel.π f)).1 ?_
        have := congrArg (biprod.inl ≫ ·) hm
        simpa [cokernelCoforkBiprodMap] using this
      · refine (cancel_epi (cokernel.π g)).1 ?_
        have := congrArg (biprod.inr ≫ ·) hm
        simpa [cokernelCoforkBiprodMap] using this)

theorem isSubbundle_biprodMap {A B C D : X.Modules} {f : A ⟶ B} {g : C ⟶ D}
    (hf : VB.IsSubbundle f) (hg : VB.IsSubbundle g) : VB.IsSubbundle (biprod.map f g) := by
  obtain ⟨_, m, hm⟩ := hf
  obtain ⟨_, n, hn⟩ := hg
  exact ⟨inferInstance, m + n, (hm.biprod hn).of_iso
    ((isColimitCokernelCoforkBiprodMap f g).coconePointUniqueUpToIso (colimit.isColimit _))⟩

variable (fl : Flag E N)

@[reassoc (attr := simp)]
theorem eqToHom_ι {a b : Fin (N + 1)} (e : a = b) : eqToHom (congrArg fl.F e) ≫ fl.ι b = fl.ι a := by
  subst e; simp

def incl (a b : Fin (N + 1)) (h : (b : ℕ) = a ∨ (b : ℕ) = a + 1) : fl.F a ⟶ fl.F b :=
  if h' : (b : ℕ) = a then eqToHom (congrArg fl.F (Fin.ext h'.symm)) else
    eqToHom (congrArg fl.F (Fin.ext rfl : a = (⟨a, by omega⟩ : Fin N).castSucc)) ≫
      fl.step ⟨a, by omega⟩ ≫
      eqToHom (congrArg fl.F (Fin.ext (by simp; omega) : (⟨a, by omega⟩ : Fin N).succ = b))

@[reassoc (attr := simp)]
theorem incl_ι (a b : Fin (N + 1)) (h : (b : ℕ) = a ∨ (b : ℕ) = a + 1) :
    fl.incl a b h ≫ fl.ι b = fl.ι a := by
  unfold incl
  split_ifs with h'
  · exact fl.eqToHom_ι (Fin.ext h'.symm)
  · rw [Category.assoc, Category.assoc, fl.eqToHom_ι, fl.step_ι, fl.eqToHom_ι]
    all_goals ext; simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

theorem isIso_ι_of_eq {a : Fin (N + 1)} (e : a = Fin.last N) : IsIso (fl.ι a) := by
  subst e; infer_instance

def fstIdx (r s : ℕ) (i : Fin (r + s + 1)) : Fin (r + 1) := ⟨min (i : ℕ) r, by omega⟩

def sndIdx (r s : ℕ) (i : Fin (r + s + 1)) : Fin (s + 1) := ⟨(i : ℕ) - r, by omega⟩

theorem fstIdx_step (i : Fin (r + s)) : (fstIdx r s i.succ : ℕ) = fstIdx r s i.castSucc ∨
    (fstIdx r s i.succ : ℕ) = fstIdx r s i.castSucc + 1 := by
  simp only [fstIdx, Fin.val_succ, Fin.val_castSucc]; omega

theorem sndIdx_step (i : Fin (r + s)) : (sndIdx r s i.succ : ℕ) = sndIdx r s i.castSucc ∨
    (sndIdx r s i.succ : ℕ) = sndIdx r s i.castSucc + 1 := by
  simp only [sndIdx, Fin.val_succ, Fin.val_castSucc]; omega

def biprod (fl₁ : Flag E₁ r) (fl₂ : Flag E₂ s) : Flag (E₁ ⊞ E₂) (r + s) where
  F i := fl₁.F (fstIdx r s i) ⊞ fl₂.F (sndIdx r s i)
  ι i := biprod.map (fl₁.ι _) (fl₂.ι _)
  isSubbundle i := isSubbundle_biprodMap (fl₁.isSubbundle _) (fl₂.isSubbundle _)
  isVB i := by
    have h := (fl₁.isVB (fstIdx r s i)).biprod (fl₂.isVB (sndIdx r s i))
    have e : ((fstIdx r s i : ℕ) + (sndIdx r s i : ℕ)) = i := by
      simp only [fstIdx, sndIdx]; omega
    rwa [e] at h
  step i := biprod.map (fl₁.incl _ _ (fstIdx_step i)) (fl₂.incl _ _ (sndIdx_step i))
  step_ι i := by refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  isIso_last := by
    have := fl₁.isIso_ι_of_eq (a := fstIdx r s (Fin.last (r + s)))
      (Fin.ext (by simp [fstIdx]))
    have := fl₂.isIso_ι_of_eq (a := sndIdx r s (Fin.last (r + s)))
      (Fin.ext (by simp [sndIdx]))
    exact inferInstanceAs (IsIso (biprod.mapIso (asIso (fl₁.ι _)) (asIso (fl₂.ι _))).hom)

theorem biprod_ι (fl₁ : Flag E₁ r) (fl₂ : Flag E₂ s) (i : Fin (r + s + 1)) :
    (fl₁.biprod fl₂).ι i = biprod.map (fl₁.ι (fstIdx r s i)) (fl₂.ι (sndIdx r s i)) := rfl

end GlobalTheory.Vert.Flag
