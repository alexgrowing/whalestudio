import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentEndomorphismQuotientGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsOfHeckeLbPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermSystemHeightFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeQuotientByPGroupSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBimultiplicativeWeilPairingTorsionAxesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTorsionAndDescentAbelianVarietyAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.PQuot

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}

theorem sections_triv {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ^ c = 1) :
    (∃ t : ((Hecke.lbPow o.P c).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧
    (∃ t : ((Hecke.lbPow o.P c).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  have hP := o.isLB
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb hP _ _
  have clsPow : GlobalTheory.CechPic.cls (Hecke.lbPow o.P c) hQ = c • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin c) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = c • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow, map_nsmul]
  have hQth : GlobalTheory.AbDual.evc hQ (toUnit o.A ≫ h) (𝟙 o.A) = 0 := by
    rw [evcQ, ← evc_pow_left o.ab hP o.rig₁ o.rig₂, ← MonObj.comp_pow, hh, MonObj.comp_one]
    exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

theorem exists_quot {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : ∃ e : ℕ, c = p ^ e) (hp : IsUnit ((p : ℕ) : R))
    (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (hfin : Finite H)
    (hfree : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A), h ∈ H →
      toUnit (Over.mk x) ≫ h = 1 → h = 1)
    (stab : ∀ c' : D.O, ∀ h ∈ H, h ≫ o.act.act c' ∈ H) (hpow : ∀ h ∈ H, h ^ c = 1)
    (hiso : ∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1)
    (hmax : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 →
      (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A)
        (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) :
    ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧
      ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A),
        g ≫ ψ = 1 ↔ ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h := by
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.T.exists_abelianScheme_quotient_by_finite_translations S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
    H o.ab (pull_isLB o.isLB _) o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hgal.inv ⟨h, hh⟩)
  choose actf hactf using fun c' : D.O => GlobalTheory.T.exists_descent_endomorphism_quotient_group_scheme S o.A A' H ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ c H
    (fun h hh => (sections_triv o c h (hpow h hh)).1) (fun h hh => (sections_triv o c h (hpow h hh)).2) hiso
  have hGC := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S o.A A' H ψ hψ hgal
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ (sq2 ψ) _ _
    (Hecke.lbPow o.P c) hGC (DVR.linComb_isLB _ o.isLB _ _) u hu hcoc
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b N S s o A' ψ hψ _ P₀ hP₀ w₀
  have hc1 : 1 ≤ c := by
    obtain ⟨e, rfl⟩ := hc
    exact pow_pos (Fact.out : p.Prime).pos e
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.T.harrisTaylor_lie_conditions_of_etale_galois_quotient p D R b N S s o A' act' ψ _ _ hA' hψ hgal hcomp
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := GlobalTheory.T.descended_birigidified_bundle_symmetric p D R b N S s o A' ψ _ hA' hψ hgal _ P' hP' w r1 r2
      ample := GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover p D R b N S s o A' ψ _ hA' hψ hgal _ hc1 P' hP' w
      kerP := GlobalTheory.T.descendedBundle_kernel_killed_primeToP p D R b N S s o c hc hp H A' ψ hA' hψ hgal hmax P' hP' r1 r2 w
      rosati := GlobalTheory.T.rosati_involution_of_galois_isogeny_descent p D R b N S s o A' act' ψ _ hA' hψ hgal hcomp _ P' hP' w r1 r2
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta x ≫ ψ
      eta_add := fun x y => by rw [o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (c' • x) ≫ ψ = (o.eta x ≫ ψ) ≫ act'.act c'
        rw [o.eta_lin, Category.assoc, hcomp, Category.assoc]
      eta_ker := fun x => by rw [o.eta_ker, one_comp]
      geom := GlobalTheory.T.exists_tateSimilitude_quotient_by_pGroup_sections p D R b N S s o c hc H A' ψ hA' hψ hgal hpow act' hcomp P' hP' r1 r2 w }
  have hmk : IsMonHom (𝟙 o.A ^ c) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_mulA c
  obtain ⟨ψ', hψ'h, hψ'⟩ := GlobalTheory.T.exists_descent_hom_quotient_galois_group_scheme S o.A A' o.A H ψ hψ hgal (𝟙 o.A ^ c) hmk
    (fun h hh => by rw [MonObj.comp_pow, Category.comp_id, hpow h hh])
  refine ⟨o', ψ, ⟨hc, hψ, hcomp, fun x => rfl, ⟨w⟩, ψ', hψ'h, hψ', ?_⟩, fun κ _ _ x t => ⟨fun ht => ?_, ?_⟩⟩
  · show ψ' ≫ ψ = 𝟙 A' ^ c
    rw [← cancel_epi ψ, ← Category.assoc, hψ', MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have ht' : t ≫ ψ = (1 : Over.mk x ⟶ A') := ht
    have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
      rw [← Over.comp_left, ← Over.comp_left, ht', MonObj.one_comp]
    obtain ⟨h, hh, -⟩ := hgal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
    refine ⟨h.1, h.2, ?_⟩
    have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
    rw [e2, TateTransl.one_comp_transl_pt]
  · rintro ⟨h, hh, rfl⟩
    show (toUnit (Over.mk x) ≫ h) ≫ ψ = (1 : Over.mk x ⟶ A')
    rw [Category.assoc, kill h hh, MonObj.comp_one]

theorem exists_pairing {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : ∃ e : ℕ, c = p ^ e)
    (κ : Type) [Field κ] [IsAlgClosed κ] (hp : ((p : ℕ) : κ) ≠ 0) (x : Sp κ ⟶ S) :
    ∃ e : (Over.mk x ⟶ o.A) → (Over.mk x ⟶ o.A) → κˣ,
      (∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ,
        Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 g') u ↔
          u = unitOn (e g g')) ∧
      (∀ g₁ g₂ g' : Over.mk x ⟶ o.A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧
      (∀ g g₁ g₂ : Over.mk x ⟶ o.A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) ∧
      (∀ (a : D.O) (g g' : Over.mk x ⟶ o.A), g ^ c = 1 → g' ^ c = 1 →
        e (g ≫ o.act.act a) g' = e g (g' ≫ o.act.act (D.star a).unop)) ∧
      (∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → e g g' * e g' g = 1) ∧
      (∀ g : Over.mk x ⟶ o.A, g ^ c = 1 → (∀ g' : Over.mk x ⟶ o.A, g' ^ c = 1 → e g g' = 1) → g = 1) := by
  have hcκ : (c : κ) ≠ 0 := by
    obtain ⟨e, rfl⟩ := hc
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hp
  obtain ⟨e, he, hl, hr⟩ := GlobalTheory.T.exists_bimultiplicative_weilPairing_torsion_axes S o.A o.P o.ab o.isLB κ x c hcκ
  have hG2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hinj : Function.Injective (unitOn (R := κ)) := by
    refine Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom.toMonoidHom) ?_
    exact (Scheme.ΓSpecIso (CommRingCat.of κ)).symm.commRingCatIsoToRingEquiv.injective
  have hmul : ∀ u v : κˣ, unitOn (u * v) = unitOn u * unitOn v := fun u v => map_mul (Units.map _) u v
  have hone : unitOn (1 : κˣ) = 1 := map_one (Units.map _)
  have hval : ∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 →
      Out.WeilIs (G2 o.A) o.P c (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 g') (unitOn (e g g')) :=
    fun g g' hg hg' => GlobalTheory.BiextPairing.weilIs_of_hecke_lbPow hG2 o.isLB c ((he g g' hg hg' _).2 rfl)
  have hact : ∀ (a : D.O) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (g ≫ o.act.act a) ^ c = 1 := fun a g hg => by
    haveI := o.act.hom a
    rw [← MonObj.pow_comp, hg, MonObj.one_comp]
  refine ⟨e, he, hl, hr, fun a g g' hg hg' => hinj ?_, fun g g' hg hg' => hinj ?_, fun g hg h => ?_⟩
  · exact GlobalTheory.T.commutatorPairing_adjoint_eq_of_pullback_iso S o.A o.P o.ab o.isLB _ _ (o.act.hom a) (o.act.hom _) (o.rosati a) c _ g g' _ _
      (hval _ _ (hact a g hg) hg') (hval _ _ hg (hact _ g' hg'))
  · have h1 := GlobalTheory.CommPairing.weilIs_symm o.isLB (hval g' g hg' hg)
    have h2 := GlobalTheory.SwapPairing.weilIs_swap_eq S o.A o.P o.ab o.isLB o.symm c _ g g' _ _ h1 (hval g g' hg hg')
    rw [hmul, hone, ← h2]
    exact inv_mul_cancel _
  · obtain ⟨e₀, he₀, hker⟩ := o.kerP
    have h1 := hker _ g (GlobalTheory.T.lineBundle_slice_trivial_of_weilPairing_one_torsion S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ κ x c hcκ g hg (fun g' hg' => by
      have := hval g g' hg hg'
      rwa [h g' hg', hone] at this))
    have hco : e₀.Coprime c := by
      obtain ⟨e, rfl⟩ := hc
      exact he₀.pow_right e
    exact (pow_eq_one_iff_of_coprime hco).1 ⟨h1, hg⟩

theorem max_geom {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : (c : k) ≠ 0)
    (H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A)) (hpow : ∀ h ∈ H, h ^ c = 1)
    (hmax : ∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) 1) → g ∈ H)
    (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ o.A) (hg : g ^ c = 1)
    (ho : ∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A)
        (lift 1 (toUnit (Over.mk x) ≫ h)) 1) : ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h := by
  obtain ⟨g₀, hg₀, rfl⟩ := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hc).2 κ x g hg
  refine ⟨g₀, hmax g₀ hg₀ fun h hh => ?_, rfl⟩
  obtain ⟨e, he, -, -⟩ := GlobalTheory.T.exists_bimultiplicative_weilPairing_torsion_axes (Sp k) o.A o.P o.ab o.isLB k (𝟙 _) c hc
  have hG2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  obtain ⟨u, hu⟩ : ∃ u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift g₀ 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) u := ⟨_, (he g₀ h hg₀ (hpow h hh) _).2 rfl⟩
  have h1 := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hG2 hQ (toUnit (Over.mk x)) hu
  rw [comp_lift, comp_lift, MonObj.comp_one] at h1
  have h2 := GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds hG2 hQ h1 (ho h hh)
  have hinj : Function.Injective (toUnit (Over.mk x)).left.appTop.hom := by
    have e1 : (toUnit (Over.mk x)).left = x := by simp
    rw [e1]
    haveI : Nontrivial Γ(Sp κ, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of κ)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    letI : Field Γ(Sp k, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)).toField
    exact RingHom.injective x.appTop.hom
  have hu1 : u = 1 := Units.map_injective (f := (toUnit (Over.mk x)).left.appTop.hom.toMonoidHom) hinj
    (h2.trans (map_one _).symm)
  rwa [hu1] at hu

end GlobalTheory.UPel.HT.ES.PQuot
