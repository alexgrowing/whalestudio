import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem rp_exists_unique {I : Type} {Gv Hv : I → Type} [∀ v, Group (Gv v)] [∀ v, Group (Hv v)]
    (K : ∀ v, Subgroup (Gv v)) (S : Finset I) (e : ∀ v, v ∈ S → (Gv v →* Hv v))
    (he : ∀ v h, Function.Bijective (e v h)) (w : ∀ v, Hv v) :
    ∃! g : RP Gv K, (∀ v (h : v ∈ S), e v h (g.1 v) = w v) ∧ ∀ v, v ∉ S → g.1 v = 1 := by
  classical
  let x : ∀ v, Gv v := fun v => if h : v ∈ S then Function.surjInv (he v h).2 (w v) else 1
  have hx : x ∈ RP Gv K := by
    show ∀ᶠ v in Filter.cofinite, x v ∈ K v
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    rw [Finset.mem_coe] at h
    exact hv (by simp [x, h, one_mem])
  refine ⟨⟨x, hx⟩, ⟨fun v h => ?_, fun v h => ?_⟩, ?_⟩
  · show e v h (x v) = w v
    simp only [x, dif_pos h]
    exact Function.surjInv_eq _ _
  · show x v = 1
    simp [x, h]
  · rintro g ⟨h1, h2⟩
    apply Subtype.ext
    funext v
    by_cases h : v ∈ S
    · apply (he v h).1
      rw [h1 v h]
      show w v = e v h (x v)
      simp only [x, dif_pos h]
      exact (Function.surjInv_eq _ _).symm
    · rw [h2 v h]
      show 1 = x v
      simp [x, h]

private theorem det_dg_inv {k : Type} [Field k] (t : kˣ) :
    ((dg ![t, t⁻¹] : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1 := by
  simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]

end UpperTheory.V.Z.Sym.So

private theorem mem_su_of_det_eq_one {K : Type} [Field K] {D : K} (x : DX D) (hx : (Glob.mt x).det = 1) :
    x ∈ SU D := by
  rw [SU, MonoidHom.mem_ker]
  refine Units.ext ?_
  rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact hx

theorem UpperTheory.V.Z.Sym.So.elEx :
    UpperTheory.V.Z.Sym.So.ElEx := by
  intro F _ _ Δ A hA
  have loc := fun v (h : v ∈ A.Sg) => (datOk F Δ A hA).2.2.1 v h
  have bU : ∀ v (h : v ∈ A.Sg), Function.Bijective (eU (A.hs v h)) := fun v h =>
    (eU_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h) (loc v h).2.2.1).1
  have bD : ∀ v (h : v ∈ A.Sg), Function.Bijective (eD (A.hs v h)) := fun v h =>
    (eD_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h) (loc v h).2.2.1).1
  refine ⟨fun d => ?_, fun d => ?_, ?_, ?_, ?_⟩
  · exact rp_exists_unique (Hv := fun v => GL (Fin 3) (Kv v)) _ A.Sg (fun v h => eU (A.hs v h)) bU
      (fun v => dg (d v))
  · exact rp_exists_unique (Hv := fun v => GL (Fin 2) (Kv v)) _ A.Sg (fun v h => eD (A.hs v h)) bD
      (fun v => dg (d v))
  · rintro g g' d d' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show eU (A.hs v h) (g.1 v * g'.1 v) = dg (d v * d' v)
      rw [map_mul, hg1 v h, hg1' v h]
      exact (map_mul (diagT (Kv v) (Fin 3)) _ _).symm
    · show g.1 v * g'.1 v = 1
      rw [hg2 v h, hg2' v h, mul_one]
  · rintro g g' d d' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show eD (A.hs v h) (g.1 v * g'.1 v) = dg (d v * d' v)
      rw [map_mul, hg1 v h, hg1' v h]
      exact (map_mul (diagT (Kv v) (Fin 2)) _ _).symm
    · show g.1 v * g'.1 v = 1
      rw [hg2 v h, hg2' v h, mul_one]
  · rintro g t ⟨hg1, hg2⟩
    simp only [SA, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show g.1 v ∈ SU (cv v Δ)
    by_cases h : v ∈ A.Sg
    · have hfac := (eD_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h)
        (loc v h).2.2.1).2.2.2.2.1 (g.1 v)
      have hd := hg1 v h
      have h2 : ((dg (SD.dS t v) : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)).det = 1 :=
        det_dg_inv (t v)
      refine mem_su_of_det_eq_one _ ?_
      rw [hfac.1, hd, h2, map_one]
    · exact (hg2 v h).symm ▸ one_mem _

end
