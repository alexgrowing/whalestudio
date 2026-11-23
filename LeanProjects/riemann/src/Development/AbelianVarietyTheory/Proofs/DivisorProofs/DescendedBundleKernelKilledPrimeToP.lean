import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfPowEqOneOfGeometric
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.KerPowDescent

theorem pow_eq_one_of_lift {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S} [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A')
    [IsMonHom ψ] (m : ℕ) {P' : LB (G2 A').left} (hP' : P'.IsLB)
    (hiso : LBIso (Hecke.lbPow o.P m) (P'.pull (sq2 ψ))) {e₀ : ℕ}
    (hker : ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e₀ = 1)
    {T T' : Over S} (π' : T' ⟶ T) (y : T' ⟶ o.A) (x : T ⟶ A') (hy : y ≫ ψ = π' ≫ x)
    (h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0) : y ^ (m * e₀) = 1 := by
  have hP := o.isLB
  have hPm : (Hecke.lbPow o.P m).IsLB := LB.isLB_linComb hP _ _
  have hc : GlobalTheory.CechPic.cls _ hPm = m • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1) hPm).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hc' : GlobalTheory.CechPic.cls _ hPm = GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP') :=
    (GlobalTheory.CechPic.cls_eq_iff hPm (pull_isLB hP' _)).2 hiso
  have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst o.A T' ≫ ψ) (snd o.A T' ≫ π')).left) h0
  rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst, Category.assoc, ← hy] at h1
  have e2 : GlobalTheory.AbDual.evc hP' (snd o.A T' ≫ y ≫ ψ) (fst o.A T' ≫ ψ) =
      GlobalTheory.CechPic.pull (lift (snd o.A T' ≫ y) (fst o.A T')).left
        (GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP')) := by
    rw [← GlobalTheory.CechPic.pull_comp, GlobalTheory.AbDual.evc, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc,
      Category.assoc]
  rw [e2, ← hc', hc, map_nsmul] at h1
  have h3 : GlobalTheory.AbDual.evc hP (snd o.A T' ≫ y ^ m) (fst o.A T') = 0 := by
    rw [comp_pow, Hecke.evc_pow_left o.ab hP o.rig₁ o.rig₂]
    exact h1
  have h4 := hker T' (y ^ m) ((GlobalTheory.AbDual.triv_ev_iff hP _ _).2 h3)
  rwa [← pow_mul] at h4

theorem kernel_primePower_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro p _ D R _ b N S s o c hc hpu H A' _ _ ψ hA' hψ hG hH P' hP' r₁ r₂ hiso
  haveI := hψ
  obtain ⟨e₀, he₀, hker⟩ := o.kerP
  obtain ⟨e, rfl⟩ := hc
  refine ⟨e₀, he₀, ?_⟩
  intro T x hx
  have h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0 := (GlobalTheory.AbDual.triv_ev_iff hP' _ _).1 hx
  have := hG.etale
  have := hG.fin
  have := hG.onto

  have hxc : x ^ (p ^ e * e₀) = 1 := by
    let T' : Over S := Over.mk (pullback.fst x.left ψ.left ≫ T.hom)
    let π' : T' ⟶ T := Over.homMk (pullback.fst x.left ψ.left) rfl
    let y : T' ⟶ o.A := Over.homMk (pullback.snd x.left ψ.left) (by
      show pullback.snd x.left ψ.left ≫ o.A.hom = pullback.fst x.left ψ.left ≫ T.hom
      rw [← Over.w ψ, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x])
    have hy : y ≫ ψ = π' ≫ x := Over.OverMorphism.ext (by
      show pullback.snd x.left ψ.left ≫ ψ.left = pullback.fst x.left ψ.left ≫ x.left
      exact pullback.condition.symm)
    have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker π' y x hy h0
    have h5 : π' ≫ x ^ (p ^ e * e₀) = π' ≫ 1 := by
      rw [comp_pow, ← hy, ← GlobalTheory.SS.FrobTorsion.pow_comp' ψ y, h4, MonObj.one_comp, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h6 := congrArg (fun f => f.left) h5
    simp only [Over.comp_left] at h6
    exact (cancel_epi (pullback.fst x.left ψ.left)).1 h6
  have hu : IsUnit (((p ^ e : ℕ) : Γ(S, ⊤))) := by
    have := (hpu.pow e).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  refine GlobalTheory.TorsionRigid.eq_one_of_pow_eq_one_of_geometric S A' hA' (p ^ e)
    (pow_pos (Fact.out : p.Prime).pos e) hu T (x ^ e₀) (by rw [← pow_mul, mul_comm]; exact hxc) ?_
  intro κ _ _ q
  let Tq : Over S := Over.mk (q ≫ T.hom)
  let πq : Tq ⟶ T := Over.homMk q rfl
  obtain ⟨pt, hpt⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left (q ≫ x.left)
  let y : Tq ⟶ o.A := Over.homMk pt (by
    show pt ≫ o.A.hom = q ≫ T.hom
    rw [← Over.w ψ, ← Category.assoc, ← hpt, Category.assoc, Over.w x])
  have hy : y ≫ ψ = πq ≫ x := Over.OverMorphism.ext (by
    show pt ≫ ψ.left = q ≫ x.left
    exact hpt.symm)
  have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker πq y x hy h0
  have hg : (y ^ e₀) ^ (p ^ e) = 1 := by rw [← pow_mul, mul_comm]; exact h4
  have hgψ : (y ^ e₀) ≫ ψ = (πq ≫ x) ^ e₀ := by rw [GlobalTheory.SS.FrobTorsion.pow_comp', hy]

  have hz : GlobalTheory.AbDual.evc hP' (snd A' Tq ≫ (y ^ e₀) ≫ ψ) (fst A' Tq) = 0 := by
    have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst A' Tq) (snd A' Tq ≫ πq)).left) h0
    rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst] at h1
    simp only [Category.assoc] at h1
    rw [hgψ, comp_pow, Hecke.evc_pow_left hA' hP' r₁ r₂, h1, smul_zero]
  have hG0 := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 A') := AbelianSchemeGerms.isAbelianScheme_tensor A' A' hA' hA'
  have hAo2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have s₁ : GlobalTheory.CechPic.pull (lift (1 : A' ⟶ A') (𝟙 A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₁
  have s₂ : GlobalTheory.CechPic.pull (lift (𝟙 A') (1 : A' ⟶ A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₂
  have hK : GlobalTheory.MemKL (G2 A') P' (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') :=
    GlobalTheory.DualCon.TwistDescent.memKL_of_lam_eq_zero hP' _
      (GlobalTheory.KernelPointPairing.lam_eq_zero hP' hA' s₁ s₂ ((y ^ e₀) ≫ ψ) hz)
  have w₀ : Out.WeilIs (G2 A') P' 1 (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') 1 1 :=
    GlobalTheory.DescendedPrincipal.weilIs_one_right hG0 hA2 hP' fun pp => by
      obtain ⟨V, hV, c, hc⟩ := hK pp
      exact ⟨V, hV, GlobalTheory.DescendedPrincipal.exists_theta_of_translDiff hP' _ V c hc⟩
  have hPc : (Hecke.lbPow o.P (p ^ e)).IsLB := LB.isLB_linComb o.isLB _ _
  let ψ2 : G2 o.A ⟶ G2 A' := lift (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
  haveI : IsMonHom ψ2 := inferInstance
  have hw : LBIso (Geo.Tor.lbPow (Hecke.lbPow o.P (p ^ e)) 1) (P'.pull ψ2.left) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hPc 1) hPc (pull_isLB hP' _) (GlobalTheory.lbIso_lbPow_one hPc) hiso
  have hHψ : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hG.inv ⟨h, hh⟩)
  obtain ⟨h, hh, hgh⟩ := hH κ (q ≫ T.hom) (y ^ e₀) hg fun h hh => by
    have e1 : (lift (y ^ e₀) 1 : Tq ⟶ G2 o.A) ≫ ψ2 = lift ((y ^ e₀) ≫ ψ) 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
    have e2 : (lift 1 (toUnit Tq ≫ h) : Tq ⟶ G2 o.A) ≫ ψ2 = 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, Category.assoc, hHψ h hh, MonObj.comp_one]
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG0 hAo2 hPc hP' ψ2 hw (n := 1) (x := lift (y ^ e₀) 1)
      (y := lift 1 (toUnit Tq ≫ h)) (c := 1) (by rw [e1, e2]; exact w₀)
    simpa using this
  show πq ≫ x ^ e₀ = 1
  rw [comp_pow, ← hgψ, hgh, Category.assoc, hHψ h hh, MonObj.comp_one]

end GlobalTheory.UPel.HT.ES.KerPowDescent
