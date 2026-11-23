import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

theorem ext_of_liftSemi_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) {e e' : M' →ₗ[C] C} (h : ∀ c, e (P c) = e' (P c)) : e = e' := by
  refine LinearMap.ext fun c' ↦ ?_
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | tmul r c => rw [liftSemi_tmul, map_smul, map_smul, h c]

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  (A₀ : Over (Sp k)) [GrpObj A₀]

def fstC : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀ →+ HdR A₀ where
  toFun e :=
    { toFun c := (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)).fst
      map_add' c c' := by rw [map_add, map_add, TrivSqZeroExt.fst_add]
      map_smul' r c := by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, TrivSqZeroExt.algebraMap_eq_inl,
          TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, smul_eq_mul] }
  map_zero' := by ext c; rfl
  map_add' e e' := by ext c; rfl

def sndC : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀ →+
    (primDR A₀ →ₗ[k] V) where
  toFun e :=
    { toFun c := (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)).snd
      map_add' c c' := by rw [map_add, map_add, TrivSqZeroExt.snd_add]
      map_smul' r c := by
        rw [LinearMap.map_smulₛₗ, map_smul, algebraMap_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
  map_zero' := by ext c; rfl
  map_add' e e' := by ext c; rfl

variable {A₀}

theorem fstC_apply (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) : fstC A₀ e c = (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)).fst := rfl

theorem sndC_apply (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) : sndC A₀ e c = (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)).snd := rfl

theorem eval_eq (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) : e ((GlobalTheory.FODef.constMorV k V A₀).pull c) =
      TrivSqZeroExt.inl (fstC A₀ e c) + TrivSqZeroExt.inr (sndC A₀ e c) := by
  ext
  · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]; rfl
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]; rfl

theorem fstC_smul (r : k) (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    fstC A₀ (algebraMap k (TrivSqZeroExt k V) r • e) = r • fstC A₀ e := by
  ext c
  rw [LinearMap.smul_apply, fstC_apply, fstC_apply, LinearMap.smul_apply, smul_eq_mul,
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, smul_eq_mul]

theorem sndC_smul (r : k) (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    sndC A₀ (algebraMap k (TrivSqZeroExt k V) r • e) = r • sndC A₀ e := by
  ext c
  rw [LinearMap.smul_apply, sndC_apply, sndC_apply, LinearMap.smul_apply, algebraMap_smul, TrivSqZeroExt.snd_smul]

theorem fstC_push (g : A₀ ⟶ A₀) [IsMonHom g]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    fstC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e) =
      push (dp0 k) (𝟙 _) g (fstC A₀ e) := by
  ext c; rw [fstC_apply, push_apply, GlobalTheory.HTGlue.primPull_constMorV_pull, push_apply, fstC_apply]

theorem sndC_push (g : A₀ ⟶ A₀) [IsMonHom g]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    sndC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e) =
      sndC A₀ e ∘ₗ primPull (dp0 k) (𝟙 _) g := by
  ext c; rw [sndC_apply, push_apply, GlobalTheory.HTGlue.primPull_constMorV_pull, LinearMap.comp_apply, sndC_apply]

theorem ext_coords (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀}
    (h1 : fstC A₀ e = fstC A₀ e') (h2 : sndC A₀ e = sndC A₀ e') : e = e' := by
  refine ext_of_liftSemi_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
    (GlobalTheory.FODef.constMorV k V A₀)).2 fun c ↦ ?_
  rw [eval_eq, eval_eq, h1, h2]

theorem exists_of_coords (hA : IsAbelianScheme A₀) (x : HdR A₀) (y : primDR A₀ →ₗ[k] V) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀,
      fstC A₀ e = x ∧ sndC A₀ e = y := by
  obtain ⟨e, he⟩ := GlobalTheory.HTGlue.exists_coords V A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k V)) ∘ₗ x + (TrivSqZeroExt.inrHom k V) ∘ₗ y)
  refine ⟨e, ?_, ?_⟩ <;> ext c
  · rw [fstC_apply, he c]; simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [sndC_apply, he c]; simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem red_pull_constMorV_pull (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem corr_iff_fstC (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) (y : HdR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y ↔
      fstC A₀ e = y := by
  constructor
  · intro h
    ext c
    have h1 := h ((GlobalTheory.FODef.constMorV k V A₀).pull c)
    rw [red_pull_constMorV_pull] at h1
    rw [h1, fstC_apply]
    rfl
  · rintro rfl
    exact GlobalTheory.HTGlue.eq_of_liftSemi_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
      (GlobalTheory.FODef.constMorV k V A₀)).2 _ _ e (fstC A₀ e) red_pull_constMorV_pull (fun c ↦ rfl)

theorem mem_glueFil_iff {d : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    e ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔ fstC A₀ e ∈ Fil A₀ ∧
      ∀ j, LinearMap.proj j ∘ₗ sndC A₀ e - f j (fstC A₀ e) ∈ Fil A₀ := by
  constructor
  · rintro ⟨x, hx, z, hz, he⟩
    have h1 : fstC A₀ e = x := by ext c; rw [fstC_apply, he c]; simp
    refine ⟨h1 ▸ hx, fun j ↦ ?_⟩
    have h2 : LinearMap.proj j ∘ₗ sndC A₀ e = f j x + z j := by
      ext c; rw [LinearMap.comp_apply, sndC_apply, he c]; simp
    rw [h1, h2, add_sub_cancel_left]; exact hz j
  · rintro ⟨h1, h2⟩
    refine ⟨fstC A₀ e, h1, fun j ↦ LinearMap.proj j ∘ₗ sndC A₀ e - f j (fstC A₀ e), h2, fun c ↦ ?_⟩
    rw [eval_eq]
    congr 2
    funext j
    simp [sndC_apply]

end GlobalTheory.HTGlueLie
