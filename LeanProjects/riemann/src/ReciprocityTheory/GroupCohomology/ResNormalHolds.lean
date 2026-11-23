import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.HomogExistsStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.HomogIso
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
import ReciprocityTheory.GroupCohomology.InnerHolds
import ReciprocityTheory.GroupCohomology.PartialProdCoe

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function CohomologyFunctoriality₂

universe u

theorem cor_holds : CorStatement.{u} := by
  intro R _ G _ _ _ M U _ hU
  obtain ⟨A, eA, hA⟩ := homogExists_holds R U (M.resSub U) G
  obtain ⟨eG, hG, hG1, hG2⟩ := homogIso_holds R G M
  obtain ⟨eU, hU0, hU1, hU2⟩ := homogIso_holds R U (M.resSub U)
  have P1 := prism_holds R U (M.resSub U) G U A (M.resSub U).coch eA eU hA hU0
  obtain ⟨φr, hφr⟩ := P1.1 (retr U) (continuous_retr U hU) (fun g x => retr_mul U g x)
  have P2 := prism_holds R U (M.resSub U) G G A A eA eA hA hA
  have ha : Continuous fun g : G => (retr U g : G) := continuous_subtype_val.comp (continuous_retr U hU)
  have hae : ∀ (g : U) (x : G), (retr U (g • x) : G) = g • (retr U x : G) := fun g x => by
    show (retr U ((g : G) * x) : G) = (g : G) * (retr U x : G)
    rw [retr_mul]; rfl
  obtain ⟨T, hT⟩ := P2.1 _ ha hae
  have hTid : ∀ n, T.H n = (Hom.id A).H n :=
    P2.2 _ id T (Hom.id A) ha continuous_id hae (fun _ _ => rfl) hT (fun _ _ _ => rfl)
  set N := normCx A eA hA eG hG
  set ι := inclCx A eA hA eG hG
  refine ⟨N.comp φr, ?_, ?_⟩
  · intro n f
    funext g
    rw [hG2 n _ g]
    show (eG n (N.f n (φr.f n f))).1 _ = _
    rw [normCx_spec]
    unfold normF corFun
    refine finsum_congr fun c => ?_
    congr 1
    rw [hφr, hU1]
    simp only [Fin.partialProd_zero, mul_one, retr_out, map_one, Module.End.one_apply]
    rfl
  · have hcomp : ∀ n f, (N.comp φr).f n ((Pair.res M U.subtype continuous_subtype_val).hom.f n f) =
        (N.comp (T.comp ι)).f n f := by
      intro n f
      apply (eG n).injective
      apply Subtype.ext
      show (eG n (N.f n _)).1 = (eG n (N.f n _)).1
      rw [normCx_spec, normCx_spec]
      funext x
      unfold normF
      refine finsum_congr fun c => ?_
      congr 1
      show (eA n (φr.f n _)).1 _ = (eA n (T.f n (ι.f n f))).1 _
      rw [hφr, hT, inclCx_spec, hU1, hG1]
      rfl
    have hNι : ∀ n f, (N.comp ι).f n f = U.index • f := by
      intro n f
      classical
      haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
      apply (eG n).injective
      apply Subtype.ext
      rw [map_nsmul]
      show (eG n (N.f n (ι.f n f))).1 = _
      rw [normCx_spec]
      funext x
      refine (normF_eq M U n _ x).trans ?_
      have h1 : ∀ c : Quotient (QuotientGroup.rightRel U),
          M.rho c.out⁻¹ ((eA n (ι.f n f)).1 fun i => c.out * x i) = (eG n f).1 x := by
        intro c
        rw [inclCx_spec]
        have := (eG n f).2.2 c.out x
        simp only [smul_eq_mul] at this
        rw [this, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      simp only [h1, Finset.sum_const, Finset.card_univ, card_rightRel]
      rfl
    intro n x
    calc (N.comp φr).H n ((Pair.res M U.subtype continuous_subtype_val).hom.H n x)
        = ((N.comp φr).comp (Pair.res M U.subtype continuous_subtype_val).hom).H n x :=
          (Hom.H_comp _ _ n x).symm
      _ = (N.comp (T.comp ι)).H n x := by
          rw [Hom.H_congr _ _ (fun n f => hcomp n f)]
      _ = N.H n (T.H n (ι.H n x)) := by rw [Hom.H_comp, Hom.H_comp]
      _ = N.H n (ι.H n x) := by rw [hTid, Hom.H_id]
      _ = (N.comp ι).H n x := (Hom.H_comp _ _ n x).symm
      _ = U.index • x := Hom.H_nsmul _ _ n (hNι n) x

theorem resInj_holds : ResInjStatement.{u} := by
  intro R _ G _ _ _ M U _ hU hunit n x y hxy
  obtain ⟨cor, -, hcor⟩ := cor_holds R G M U hU
  have h1 := hcor n x
  have h2 := hcor n y
  rw [hxy, h2] at h1
  have h3 : (U.index : R) • x = (U.index : R) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h1.symm
  exact (hunit.smul_left_cancel).1 h3

theorem resNormal_holds : ResNormalStatement.{u} := by
  intro R _ G _ _ _ M N _ _ hN hunit n x hx
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel N)) := Fintype.ofFinite _
  obtain ⟨cor, hcor, -⟩ := cor_holds R G M N hN
  set res := (Pair.res M N.subtype continuous_subtype_val).hom
  have key : ∀ f, (res.comp cor).f n f = ∑ c : Quotient (QuotientGroup.rightRel N),
      (conjPrime₂ M N c.out⁻¹).hom.f n f := by
    intro f
    apply Subtype.ext
    funext g
    show (cor.f n f).1 (fun i => (g i : G)) = _
    rw [hcor]
    erw [Submodule.coe_sum]
    rw [Finset.sum_apply]
    unfold corFun
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = M.rho c.out⁻¹ (f.1 fun i => conjHom N c.out⁻¹ (g i))
    refine congrArg (M.rho c.out⁻¹) (congrArg f.1 (funext fun i => ?_))
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [retr_conj N _ _ (by rw [partialProd_coe]; exact SetLike.coe_mem _),
      retr_conj N _ _ (by rw [partialProd_coe]; exact SetLike.coe_mem _), rep_out,
      Fin.partialProd_succ]
    show _ = (c.out⁻¹)⁻¹ * (g i : G) * c.out⁻¹
    group
  have hrc : res.H n (cor.H n x) = N.index • x := by
    rw [← Hom.H_comp, Hom.H_sum _ _ _ n key]
    rw [Finset.sum_congr rfl fun c _ => hx c.out⁻¹ (conjPrime₂ M N c.out⁻¹) (fun _ => rfl) (fun _ => rfl)]
    rw [Finset.sum_const, Finset.card_univ, card_rightRel]
  refine ⟨cor.H n (((hunit.unit⁻¹ : Rˣ) : R) • x), ?_⟩
  rw [map_smul, map_smul, hrc, ← Nat.cast_smul_eq_nsmul R, smul_smul, hunit.val_inv_mul, one_smul]

end ReciprocityTheory.Coh
