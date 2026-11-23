import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.InputsGenus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem castGL_bc {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {m n : ℕ} (h : m = n) (x : GL (Fin m) A) :
    castGL h (Formalism.UG.bc f x) = Formalism.UG.bc f (castGL h x) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc, Matrix.reindexAlgEquiv_apply]

theorem castGL_symm_castGL' {A : Type} [CommRing A] {m n : ℕ} (h : m = n) (x : GL (Fin m) A) :
    castGL h.symm (castGL h x) = x := by
  subst h
  ext i j
  simp [castGL, Matrix.reindexAlgEquiv_apply]

theorem castGL_mem_UJ_one {A : Type} [CommRing A] (σ : A →+* A) {m n : ℕ} (h : m = n) (x : GL (Fin m) A)
    (hx : x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin m) (Fin m) A)) : castGL h x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
  subst h
  have e : castGL (rfl : m = m) x = x := by
    ext i j
    simp [castGL, Matrix.reindexAlgEquiv_apply]
  rwa [e]

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) {m : ℕ} :
    Function.Injective (Formalism.UG.bc (n := Fin m) f) := by
  intro x y hxy
  ext i j
  exact hf (congrArg (fun z : GL (Fin m) B => (z : Matrix (Fin m) (Fin m) B) i j) hxy)

def phiG (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Bridge.Gf (Vc X.toD7 i) →* Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV where
  toFun g := ⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) g.1), by
    obtain ⟨k, hk⟩ := g.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) g.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hk]
      exact GlobalTheory.LevSplit.finE_mem_UA _ k
    rw [hg] at h1
    exact castGL_mem_UA_std _ _ _ h1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem phiG_val (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (g : Bridge.Gf (Vc X.toD7 i)) :
    (phiG X i hg g : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) g.1) := rfl

theorem phiG_injective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Injective (phiG X i hg) := by
  intro a b hab
  have h1 := congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) hab
  simp only [phiG_val] at h1
  have h2 := (castGL (rkEq X i).symm).injective h1
  exact Subtype.ext (bc_injective _ (Algebra.TensorProduct.comm _ _ _).injective h2)

theorem phiG_surjective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Surjective (phiG X i hg) := by
  intro x
  have hy : castGL (rkEq X i) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    rw [hg]
    exact castGL_mem_UA_std _ _ _ x.2
  refine ⟨⟨finHom (Vc X.toD7 i) (GlobalTheory.StdFrameExist.liftF (Vc X.toD7 i) _ hy), _, rfl⟩, Subtype.ext ?_⟩
  rw [phiG_val]
  have e := GlobalTheory.StdFrameExist.finE_liftF (Vc X.toD7 i) _ hy
  change castGL (rkEq X i).symm (finE (Vc X.toD7 i) (GlobalTheory.StdFrameExist.liftF (Vc X.toD7 i) _ hy)) = _
  rw [e, castGL_symm_castGL']

end GlobalTheory.Mem.R3.LiftBrg.StdGroups

namespace GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem bc_inclR_mem_HR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (γ : GL (Fin m) E) (hγ : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (inclR (F := F) R) γ ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin m) (Fin m) E) * J * γ = J := hγ
  show Formalism.UG.cT (sigR R σ) ((γ : Matrix (Fin m) (Fin m) E).map (inclR R)) * J.map (inclR R) *
    (γ : Matrix (Fin m) (Fin m) E).map (inclR R) = J.map (inclR R)
  have h2 : Formalism.UG.cT (sigR R σ) ((γ : Matrix (Fin m) (Fin m) E).map (inclR R)) =
      (Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin m) (Fin m) E)).map (inclR (F := F) R) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR]
  rw [h2, ← Matrix.map_mul, ← Matrix.map_mul, h]

def psiQ (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV →* GQ (Vc X.toD7 i) where
  toFun γ :=
    have hm : castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E) ∈
        Formalism.UG.UJ (X.toD7.sp.cm.sig : X.toD7.host.E →+* X.toD7.host.E) (Vc X.toD7 i).gram := by
      rw [hg]
      exact castGL_mem_UJ_one _ _ _ γ.2
    ⟨(show GA X.toD7 (Vc X.toD7 i) from
        (⟨Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F)) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)),
          bc_inclR_mem_HR _ _ _ _ hm⟩ : HR (AF X.toD7.host.F) X.toD7.sp.cm.sig (Vc X.toD7 i).gram)),
      Subgroup.mem_subgroupOf.2 ⟨_, hm, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_one]; rfl) | (simp <;> rfl)))
  map_mul' a b := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_mul]; rfl) | (simp <;> rfl)))

theorem psiQ_mat (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) :
    matHom (Vc X.toD7 i) (psiQ X i hg γ : GA X.toD7 (Vc X.toD7 i)) =
      Formalism.UG.bc (incA X.toD7) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := rfl

theorem phiG_ratF_psiQ (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) :
    phiG X i hg (Bridge.ratF (Vc X.toD7 i) (psiQ X i hg γ)) = Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ := by
  apply Subtype.ext
  rw [phiG_val, Formalism.L2.Col.ratIn_val]
  have e1 : ((Bridge.ratF (Vc X.toD7 i) (psiQ X i hg γ)) : GL (Fin (Vc X.toD7 i).rank) _) =
      Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F)) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := by
    change finHom (Vc X.toD7 i) _ = _
    rw [finHom, MonoidHom.comp_apply, Subgroup.coe_subtype, psiQ_mat]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  rw [e1]
  have e2 : Formalism.UG.bc (swapAE X.toD7) (Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
      (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) =
      Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := by
    ext a b
    simp [Formalism.UG.bc, swapAE, inclR, Formalism.UG.inclE]
  rw [e2, ← castGL_bc, castGL_symm_castGL']

theorem psiQ_injective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Injective (psiQ X i hg) := by
  intro a b hab
  have h1 : Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV a = Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV b := by
    rw [← phiG_ratF_psiQ X i hg a, ← phiG_ratF_psiQ X i hg b, hab]
  have h2 := congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) h1
  simp only [Formalism.L2.Col.ratIn_val] at h2
  exact Subtype.ext (Formalism.L2.DIV.incl_inj _ _ _ h2)

theorem psiQ_surjective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Surjective (psiQ X i hg) := by
  intro δ
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 δ.2
  have hγ : castGL (rkEq X i).symm γE ∈ Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV := by
    rw [hg] at hγE
    exact castGL_mem_UJ_one _ _ _ hγE
  refine ⟨⟨_, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
  change Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F)) (castGL (rkEq X i) (castGL (rkEq X i).symm γE)) = _
  rw [castGL_symm_castGL' (rkEq X i).symm γE]
  exact e

theorem stdGroups_equiv : ∀ (X : Stages) (i : Fin X.toD7.R.m), (Vc X.toD7 i).gram = 1 →
    ∃ (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
      (eΓ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV ≃* GQ (Vc X.toD7 i)),
      (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∧
      (∀ γ, Bridge.ratF (Vc X.toD7 i) (eΓ γ) = eG (Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ)) ∧
      (∀ γ, Bridge.IsRatMat (Vc X.toD7 i) (eΓ γ) (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) := by
  intro X i hg
  let eG0 := MulEquiv.ofBijective (phiG X i hg) ⟨phiG_injective X i hg, phiG_surjective X i hg⟩
  let eQ := MulEquiv.ofBijective (psiQ X i hg) ⟨psiQ_injective X i hg, psiQ_surjective X i hg⟩
  refine ⟨eG0.symm, eQ, fun x => ?_, fun γ => ?_, fun γ => ?_⟩
  · have h := eG0.apply_symm_apply x
    exact congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) h
  · rw [MulEquiv.eq_symm_apply]
    exact phiG_ratF_psiQ X i hg γ
  · exact psiQ_mat X i hg γ

end GlobalTheory.Mem.R3.LiftBrg.StdGroups
