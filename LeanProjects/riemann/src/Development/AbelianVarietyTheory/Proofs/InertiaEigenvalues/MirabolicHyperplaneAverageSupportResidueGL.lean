import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

section Reindex
variable {n K L : Type} [Fintype n] [CommRing K] [CommRing L]

theorem map_symm_mulVec_comp (ρ : K ≃+* L) (M : Matrix n n L) (x : n → L) :
    (M.map ρ.symm) *ᵥ (fun j => ρ.symm (x j)) = fun j => ρ.symm ((M *ᵥ x) j) := by
  funext j
  exact (RingHom.map_mulVec ρ.symm.toRingHom M x j).symm

theorem fix_hyperplane_map_iff (ρ : K ≃+* L) (M : Matrix n n L) (a : n → K) :
    (∀ x, (fun j => ρ (a j)) ⬝ᵥ x = 0 → M *ᵥ x = x) ↔ ∀ w, a ⬝ᵥ w = 0 → (M.map ρ.symm) *ᵥ w = w := by
  constructor
  · intro h w hw
    have hd : (fun j => ρ (a j)) ⬝ᵥ (fun j => ρ (w j)) = 0 := by
      have := (RingHom.map_dotProduct ρ.toRingHom a w).symm
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hw, map_zero] at this
      exact this
    have h1 := h _ hd
    have h2 := map_symm_mulVec_comp ρ M (fun j => ρ (w j))
    rw [h1] at h2
    simpa only [RingEquiv.symm_apply_apply] using h2
  · intro h x hx
    have hd : a ⬝ᵥ (fun j => ρ.symm (x j)) = 0 := by
      have := (RingHom.map_dotProduct ρ.symm.toRingHom (fun j => ρ (a j)) x).symm
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx, map_zero] at this
      simpa only [Function.comp_def, RingEquiv.symm_apply_apply] using this
    have h1 := h _ hd
    rw [map_symm_mulVec_comp] at h1
    funext j
    have := congrArg ρ (congrFun h1 j)
    simpa only [RingEquiv.apply_symm_apply] using this

end Reindex

theorem mirC_hyperplane_reindex : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (v : FinPl D) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP) (a : Fin D.R.r → IsLocalRing.ResidueField (OI v)) (F : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ), (∑ᶠ g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0}, F (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) = ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, F g := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R i PP hPP v ρk a F
  set P : R.Pg := ⟨PP, hPP⟩ with hP
  have key : ∀ g : G, ((∀ x, (fun j => ρk (a j)) ⬝ᵥ x = 0 →
      ((R.eG g P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) *ᵥ x = x) ↔
      ∀ w, a ⬝ᵥ w = 0 → ((Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ w = w) :=
    fun g => fix_hyperplane_map_iff ρk _ a
  have hset : {g : G | mirC R i P (fun j => ρk (a j)) false 1 g ≠ 0} =
      {g : G | (∀ PP', PP' ≠ P → R.eG g PP' = 1) ∧ ∀ w, a ⬝ᵥ w = 0 →
        ((Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ w = w} := by
    ext g
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← key g]
    simp only [mirC, Bool.false_eq_true, ↓reduceIte, zpow_one]
    split_ifs with hc
    · simp only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]
      exact hc
    · simp only [ne_eq, not_true_eq_false, false_iff]
      exact hc
  rw [hset]
  apply finsum_mem_eq_of_bijOn (fun g => Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P))
  · refine ⟨?_, ?_, ?_⟩
    · rintro g ⟨_, hg⟩
      exact hg
    · rintro g₁ ⟨h1, _⟩ g₂ ⟨h2, _⟩ he
      apply R.eG.injective
      funext PP'
      by_cases hq : PP' = P
      · rw [hq]
        have he' : ((R.eG g₁ P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).map ρk.symm =
            ((R.eG g₂ P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).map ρk.symm :=
          congrArg Units.val he
        exact Units.ext (Matrix.map_injective ρk.symm.injective he')
      · rw [h1 PP' hq, h2 PP' hq]
    · intro g₀ hg₀
      have hcomp : Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (Matrix.GeneralLinearGroup.map ρk.toRingHom g₀) = g₀ := by
        ext j k
        simp
      refine ⟨R.eG.symm (Pi.mulSingle P (Matrix.GeneralLinearGroup.map ρk.toRingHom g₀)), ⟨?_, ?_⟩, ?_⟩
      · intro PP' hq
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_of_ne hq]
      · rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, hcomp]
        exact hg₀
      · show Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG (R.eG.symm _) P) = g₀
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, hcomp]
  · intro g _
    rfl

end GlobalTheory.DownLift.GenSplit

end
