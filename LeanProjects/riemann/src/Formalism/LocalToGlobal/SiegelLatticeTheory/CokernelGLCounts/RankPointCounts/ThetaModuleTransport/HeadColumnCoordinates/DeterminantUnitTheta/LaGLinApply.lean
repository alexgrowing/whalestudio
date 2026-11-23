import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.FirstQuotientEqZeroIff

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def laGLin (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Fin (r + 1) → M.R) →ₗ[M.R] E :=
  (LinearMap.proj (Fin.last r)) ∘ₗ (Zm⁻¹.mulVecLin.restrictScalars M.R) ∘ₗ
    (LinearMap.compLeft (Algebra.linearMap M.R E) (Fin (r + 1)))

theorem laGLin_apply (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (l : Fin (r + 1) → M.R) :
    laGLin Zm l = laG Zm l := rfl

theorem laG_headCols (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit (ZZm g Zh T T').det)
    {l : Fin (r + 1) → M.R} (hl : l ∈ headCols Z.Z) : laG (ZZm g Zh T T') l = 0 := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff Z.Z l).1 hl
  rw [laG_mulVec Zh T T' Z hZ hu, hw]
  simp

def laM (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit (ZZm g Zh T T').det) :
    MbMod Z.Z →ₗ[M.R] E :=
  (headCols Z.Z).liftQ (laGLin (ZZm g Zh T T')) (fun l hl => by
    rw [LinearMap.mem_ker, laGLin_apply]; exact laG_headCols Zh T T' Z hZ hu hl)

theorem laM_mk (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit (ZZm g Zh T T').det)
    (l : Fin (r + 1) → M.R) : laM Zh T T' Z hZ hu (Submodule.Quotient.mk l) = laG (ZZm g Zh T T') l := rfl

theorem kap_common (hs : M.split = some g) (T T' : F) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hu₁ : IsUnit Zh₁.det) (hu₂ : IsUnit Zh₂.det) (hK : KapEq Zh₁ Zh₂) :
    kapR (ZZm g Zh₁ T T') = kapR (ZZm g Zh₂ T T') := by
  have h1 := ((isUnit_iff_ph (g := g) _).1 hu₁)
  have h2 := ((isUnit_iff_ph (g := g) _).1 hu₂)
  have k1 := congrArg (ph1 g) hK
  have k2 := congrArg (ph2 g) hK
  simp only [map_mul] at k1 k2
  rw [eq_iff_ph (g := g), cornerRatio_firstProj hs Zh₁ T T' hu₁, cornerRatio_firstProj hs Zh₂ T T' hu₂, cornerRatio_secondProj hs Zh₁ T T' hu₁,
    cornerRatio_secondProj hs Zh₂ T T' hu₂]
  constructor
  · field_simp [h1.1, h2.1]
    first | linear_combination (g.q : F) * k1 | linear_combination -(g.q : F) * k1
  · field_simp [h1.2, h2.2]
    first | linear_combination (g.q : F) * k2 | linear_combination -(g.q : F) * k2

theorem laG_b (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit (ZZm g Zh T T').det) :
    laG (ZZm g Zh T T') (Z.Z.mulVec (eV r)) = 1 - tau0 g T T' * kapR (ZZm g Zh T T') := by
  rw [laG_mulVec Zh T T' Z hZ hu]
  simp [eV]

theorem laM_equiv (hs : M.split = some g) (T T' : F) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (Z₁ Z₂ : M.Mat (r + 1)) (hZ₁ : Z₁.Z.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T')
    (hZ₂ : Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T') (hu₁ : IsUnit Zh₁.det) (hu₂ : IsUnit Zh₂.det)
    (hK : KapEq Zh₁ Zh₂) (γ : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (hb : γ (bCls Z₁.Z) = bCls Z₂.Z)
    (m : MbMod Z₁.Z) :
    laM Zh₂ T T' Z₂ hZ₂ (unit_zzm hs Zh₂ T T' hu₂) (γ m) = laM Zh₁ T T' Z₁ hZ₁ (unit_zzm hs Zh₁ T T' hu₁) m := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hb' : ∀ (Z : M.Mat (r + 1)) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
      (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit Zh.det),
      laM Zh T T' Z hZ (unit_zzm hs Zh T T' hu) (bCls Z.Z) = 1 - tau0 g T T' * kapR (ZZm g Zh T T') := by
    intro Z Zh hZ hu
    rw [bCls, col_eq_mulVec, laM_mk, laG_b Zh T T' Z hZ (unit_zzm hs Zh T T' hu)]
  apply (det_unit Z₁).mul_left_cancel
  have e1 := congrArg (laM Zh₂ T T' Z₂ hZ₂ (unit_zzm hs Zh₂ T T' hu₂)) (congrArg γ (det_smul_mk Z₁ v))
  have e2 := congrArg (laM Zh₁ T T' Z₁ hZ₁ (unit_zzm hs Zh₁ T T' hu₁)) (det_smul_mk Z₁ v)
  rw [map_smul, map_smul, map_smul, hb, map_smul, hb' Z₂ Zh₂ hZ₂ hu₂, Subring.smul_def, Subring.smul_def,
    smul_eq_mul, smul_eq_mul] at e1
  rw [map_smul, map_smul, hb' Z₁ Zh₁ hZ₁ hu₁, Subring.smul_def, Subring.smul_def, smul_eq_mul,
    smul_eq_mul] at e2
  rw [e1, e2, kap_common hs T T' Zh₁ Zh₂ hu₁ hu₂ hK]

theorem LL_dg_smul (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (c : 𝒪[F])
    {l : Fin (r + 1) → M.R} (hl : l ∈ LL hs Z TT) : dgR hs c • l ∈ LL hs Z TT := by
  obtain ⟨m, rfl⟩ := hl
  refine ⟨dgR hs c • m, ?_⟩
  show Z.Z.mulVec (dgR hs c • m) - (TT * dgR hs (trO hs ((dgR hs c • m) (Fin.last r)))) • eV r =
    dgR hs c • (Z.Z.mulVec m - (TT * dgR hs (trO hs (m (Fin.last r)))) • eV r)
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, trO_dgR_mul, map_mul, smul_sub, smul_smul]
  congr 2
  ring

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
