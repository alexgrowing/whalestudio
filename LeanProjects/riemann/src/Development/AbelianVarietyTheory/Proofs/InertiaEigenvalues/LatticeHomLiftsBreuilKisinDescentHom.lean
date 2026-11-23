import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphism
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirectStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PackMap

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {G : Type} [Group G] [TopologicalSpace G]

theorem latW_TWact {T T' : LocLat G ℚ_[l] K O} (f : LatHom T.L T'.L) (s : GQ l) (g : G)
    (y : TW (OW l O) T) :
    latW f (TWact (galOW O s) T g y) = TWact (galOW O s) T' g (latW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x =>
    simp only [latW, TWact, TensorProduct.map_tmul]
    congr 1
    exact Subtype.ext (f.equiv g x)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem homW_act {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat G ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {f : LatHom T.L T'.L} {F : BK.Hom P Q}
    (h : IsMapOf I I' f F) (s : GQ l) (g : G) (v : ι → OW l O) :
    homW t ϖ F (I.act s g v) = I'.act s g (homW t ϖ F v) :=
  I'.j.injective (by rw [h, I.j_act, latW_TWact, I'.j_act, h])

variable [TameDescentExponentData K l e a]

theorem app_act_of_cover {s : G →* GQ l} {η H η' H' : ℕ} {D₁ : BKDat O K l e a ι η H}
    {D₂ : BKDat O K l e a κ η' H'} {T₁ T₂ : LocLat G ℚ_[l] K O} (R₁ : GalDat t ϖ s D₁ T₁)
    (R₂ : GalDat t ϖ s D₂ T₂) {f : LatHom T₁.L T₂.L} {F : BK.Hom D₁.toPhiMod D₂.toPhiMod}
    (hF : IsMapOf R₁.I R₂.I f F) (hcov : ∀ γ : TameGal K l e a, ∃ g : G, Covers K t ϖ (s g) γ)
    (γ : TameGal K l e a) (v : Vec K a ι) :
    F.app (D₁.desc.act γ v) = D₂.desc.act γ (F.app v) := by
  have hb : ∀ i : ι, F.app (D₁.desc.act γ (bas i)) = D₂.desc.act γ (F.app (bas i)) := by
    intro i
    obtain ⟨g, hg⟩ := hcov γ
    have m0 : (bas i : Vec K a ι) ∈ D₁.M := PhiMod.bas_mem_M _ i
    have m1 : D₁.desc.act γ (bas i) ∈ D₁.M := D₁.desc.act_mem_M γ _ m0
    have m2 : F.app (bas i) ∈ D₂.M := F.app_mem_M m0
    have m3 : D₂.desc.act γ (F.app (bas i)) ∈ D₂.M := D₂.desc.act_mem_M γ _ m2
    have m4 : F.app (D₁.desc.act γ (bas i)) ∈ D₂.M := F.app_mem_M m1
    have e1 := R₁.desc g γ hg ⟨_, mem_ME_of_mem_M m0⟩ ⟨_, mem_ME_of_mem_M m1⟩ rfl
    have e2 := R₂.desc g γ hg ⟨_, mem_ME_of_mem_M m2⟩ ⟨_, mem_ME_of_mem_M m3⟩ rfl
    have h1 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m1⟩
    have h2 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m0⟩
    have key : toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩ =
        toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ :=
      calc toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩
          = homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m1⟩) := h1.symm
        _ = homW t ϖ F (R₁.I.act (s g) g (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) := by rw [e1]
        _ = R₂.I.act (s g) g (homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) :=
          homW_act hF _ _ _
        _ = R₂.I.act (s g) g (toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m2⟩) := by rw [h2]
        _ = toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ := e2
    exact congrArg Subtype.val (toW_injective t ϖ _ key)
  rw [eq_sum_bas v, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D₁.desc.act_smul_tot, F.app_smul_tot, F.app_smul_tot, D₂.desc.act_smul_tot, hb]

end General

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T₁ T₂ : QLat LL)
    (P₁ : Pack a ϖ η H T₁) (P₂ : Pack a ϖ η H T₂) (f : LatHom T₁.L T₂.L),
    ∃ F : BKHom P₁.D P₂.D, IsMapOf P₁.R.I P₂.R.I f F.toHom := by
  intro BS l _ a e _ _ ϖ LL _ _ η H T₁ T₂ P₁ P₂ f
  let f' : LatHom (resF T₁ (ϖ.field a)).L (resF T₂ (ϖ.field a)).L :=
    ⟨f.f, fun _ x => f.equiv _ x, f.cont, f.T_le⟩
  obtain ⟨F, hF⟩ := GlobalTheory.BKReal.Full.main BS l a e _ _ (thetaW a LL) ϖ _ _ P₁.D.toPhiMod P₂.D.toPhiMod
    (resF T₁ (ϖ.field a)) (resF T₂ (ϖ.field a))
    (P₁.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
    (P₂.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) P₁.isBK P₂.isBK f'
  have hF' : IsMapOf P₁.R.I P₂.R.I f F := hF
  have hcov : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ := fun γ => by
    obtain ⟨k, -, hc⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).2.2.1 γ
    refine ⟨⟨k, ?_⟩, hc⟩
    show k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  exact ⟨⟨F, app_act_of_cover P₁.R P₂.R hF' hcov⟩, hF'⟩

end GlobalTheory.BKGal.PackMap
