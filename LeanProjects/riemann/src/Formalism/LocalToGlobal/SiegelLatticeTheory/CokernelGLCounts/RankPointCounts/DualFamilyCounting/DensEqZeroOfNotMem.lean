import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensCut

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem algebraMap_mem_LO (c : F) (hc : c ∈ 𝒪[F]) : algebraMap F E c ∈ M.L.O := by
  rw [M.L.O_def]
  have h := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨c, hc⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h
  exact h

theorem dens_eq_zero_of_not_mem (H : Loc.HermSp M V) (ϖ : 𝒪[F]) {abelian₂ : Submodule M.L.O V} (hSD : H.IsSelfDual abelian₂)
    {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) (a b : ι) (hab : G₀ a b ∉ M.L.O) : H.dens ϖ abelian₂ G₀ = 0 := by
  unfold Loc.HermSp.dens
  have hE : IsEmpty {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} := by
    refine ⟨fun v => hab ?_⟩
    obtain ⟨hP, hG⟩ := v.2
    have h1 : H.h (v.1 b) (v.1 a) ∈ M.L.O := (hSD.2.2 (v.1 b)).1 (hP.1 b) (v.1 a) (hP.1 a)
    have h2 := hG a b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
    have hϖ : algebraMap F E (ϖ : F) ∈ M.L.O := algebraMap_mem_LO _ ϖ.2
    have h3 : H.h (v.1 b) (v.1 a) - G₀ a b ∈ M.L.O := by
      rw [← hc]
      exact M.L.O.mul_mem c.2 hϖ
    have h4 : G₀ a b = H.h (v.1 b) (v.1 a) - (H.h (v.1 b) (v.1 a) - G₀ a b) := by ring
    rw [h4]
    exact M.L.O.sub_mem h1 h3
  have h0 : Set.range (fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
        fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)) = ∅ :=
    Set.range_eq_empty _
  rw [h0]
  simp

end Local

def GaPlusIntMM : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (∀ (p : PlF D) (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)),
          GaPlus M δ p (Tn u) (Tn u') Z a b ∈ (M p).L.O) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')

theorem notIntDens_of (h1 : LocSelfDual) (hG : GaPlusIntMM) : NotIntDens := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  by_contra hall
  push_neg at hall
  apply hI
  refine hG D δ M hA L u u' hT F0 what₂ hR Z F' hz hZ hP fun p a b => ?_
  by_contra hab
  exact hall p (dens_eq_zero_of_not_mem (L.H p) (ϖ p) (h1 D δ M hA L p) _ a b hab)

end Formalism.L2.SG.Pf.Cnt
