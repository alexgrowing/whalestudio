import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfRankAtStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPerf

theorem bijective_deRham (HR : GlobalTheory.Published.AbelianDeRham) (HD : GlobalTheory.Published.AbelianDualCrystal) {K : Type} [CommRing K]
    [IsNoetherianRing K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (g : ℕ)
    (hg : SmoothOfRelativeDimension g A.hom) (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hsym : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    (amp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : K))
    (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (hψ : IsCorrForm (dp0 K) (𝟙 _) A A P ψ) : Function.Bijective ψ := by

  have hsw : (swap P).IsLB := pull_isLB hP _
  have ec : cls P hP = cls _ hsw := (cls_eq_iff hP hsw).2 hsym
  have key : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = evc hP b a := fun Y a b ↦ by
    rw [← evc_swap hP hsw a b]
    show CechPic.pull _ (cls P hP) = CechPic.pull _ (cls _ hsw)
    rw [ec]

  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD.1 (Sp K) A hA
  have hBg := hBg _ hg
  haveI : IsCommMonObj B := hB.comm

  have hL := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  obtain ⟨H, hH, hamp⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL amp hL amp
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH hamp hP r₁ r₂
  obtain ⟨lam, hlam, hcls⟩ := GlobalTheory.BirigidLift.exists_hom hd hd'.additive hP a₁ a₂

  have hkerl : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ lam = 1 → x ^ e = 1 := by
    intro T x hx
    have tr : Triv (ev P (fst A T) (snd A T ≫ x)) := by
      rw [triv_ev_iff hP, GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP hcls, Category.assoc, hx, comp_one]
      exact evc_one_right hd.isLB hd.zero _
    refine hker T x ((triv_ev_iff hP _ _).2 ?_)
    rw [key]
    exact (triv_ev_iff hP _ _).1 tr
  obtain ⟨μ', hμ', e₁, e₂⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A B g hA hB hg hBg lam hlam e he0 hkerl
  haveI := hlam
  haveI := hμ'
  have hpush := GlobalTheory.PolPrimeTo.bijective_push (dp0 K) (𝟙 _) lam μ' e he e₁ e₂

  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := GlobalTheory.Published.AbelianDualCrystal.duality HR hA hg hB hBg (hd.isPerfect hd')
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)
  have e' : LBIso (ev Q (fst A A) (snd A A ≫ lam)) (ev P (fst A A ≫ 𝟙 A) (snd A A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB hP _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev hP, GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP hcls, Category.comp_id]
  have hadj : ∀ x y, φ x (push (dp0 K) (𝟙 _) lam y) = ψ x y := fun x y ↦ by
    have k := IsCorrForm.adjoint C hd.isLB hP hφ hψ (𝟙 A) lam e' x y
    rwa [push_id] at k
  haveI := (hperf φ hφ).1
  have hφb : Function.Bijective φ := LinearMap.IsPerfPair.bijective_left φ
  let E := LinearEquiv.ofBijective _ hpush
  have : ⇑ψ = ⇑E.dualMap ∘ ⇑φ := by
    funext x
    refine LinearMap.ext fun y ↦ ?_
    rw [Function.comp_apply, LinearEquiv.dualMap_apply, ← hadj]
    rfl
  rw [this]
  exact E.dualMap.bijective.comp hφb

end GlobalTheory.HTPerf

namespace GlobalTheory.HTPerf

open GlobalTheory.Published.GrothendieckMessing IsLocalRing

set_option maxHeartbeats 1600000 in

theorem skew_bijective : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → (∀ x y, φ x y = -φ y x) ∧ Function.Bijective φ := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ φ hφ
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  haveI : IsNoetherianRing C₀ := isNoetherianRing_of_surjective C C₀ π hπ
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  have hA₀ := o₀.ab
  have hP₀ := o₀.isLB
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A hA₀
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have Cs := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'

  have hsw : (swap o₀.P).IsLB := pull_isLB hP₀ _
  have hs : LBIso (swap o₀.P) o₀.P := (cls_eq_iff hsw hP₀).1 ((cls_eq_iff hP₀ hsw).2 o₀.symm).symm
  have skew : ∀ x y, φ x y = -φ y x := GlobalTheory.SymmPoincare.skew_of_symm Cs hP₀ hs hφ
  refine ⟨skew, ?_⟩

  have HC := (GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1
  obtain ⟨bij, -, -⟩ := HC g o₀.A A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra C C₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 C A' g hA' hg C₀ o₀.A i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  haveI : Module.Finite C (Crys κ (spMap π) o₀.A) := Module.Finite.equiv e.symm
  haveI : Module.Projective C (Crys κ (spMap π) o₀.A) := Module.Projective.of_equiv e.symm

  let red : Crys κ (spMap π) o₀.A →ₛₗ[π] HdR o₀.A := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl o₀.A).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) hP₀).1
      (by rw [GlobalTheory.CechPic.cls_pull hP₀, Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ.pull hP₀ (crysRedMor κ rfl o₀.A) (crysRedMor κ rfl o₀.A)
    (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) hP₀ iso
  have hrel : ∀ x y, φ' (red x) (red y) = π (φ x y) := fun x y ↦ e' x (red x) y (red y) (hm x) (hm y)
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[C] C₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) o₀.A)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this

  obtain ⟨k, hkp, hkerP⟩ := o₀.kerP
  have hk0 : 0 < k := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    rw [h0, Nat.coprime_zero_left] at hkp
    exact (Fact.out : p.Prime).one_lt.ne' hkp
  have hku : IsUnit (k : C₀) := by
    have := (b.unit k hkp).map (π.comp tR)
    rwa [map_natCast] at this
  have hψb : Function.Bijective φ' :=
    bijective_deRham ADR ADC o₀.A hA₀ g₀ hg₀ o₀.P hP₀ o₀.rig₁ o₀.rig₂ o₀.symm o₀.ample k hk0 hku hkerP φ' hφ'
  have skew' : ∀ u v, φ' u v = -φ' v u := fun u v ↦ by
    obtain ⟨x, rfl⟩ := hred u
    obtain ⟨y, rfl⟩ := hred v
    rw [hrel, hrel, skew, map_neg]
  have hψf : Function.Surjective φ'.flip := fun l ↦ by
    obtain ⟨x, hx⟩ := hψb.2 (-l)
    exact ⟨x, LinearMap.ext fun y ↦ by rw [LinearMap.flip_apply, skew', hx, LinearMap.neg_apply, neg_neg]⟩
  have hperf := GlobalTheory.BirigLift.exists_perfect_mod π red φ φ' hπ hψf hred hker hrel

  have htop : (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ LinearMap.range φ.flip ⊔ RingHom.ker π • ⊤ := fun l _ ↦ by
    obtain ⟨z, hz⟩ := hperf l
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (l - φ.flip z) fun c ↦ by
      simpa only [LinearMap.sub_apply, LinearMap.flip_apply] using hz c
    exact Submodule.mem_sup.2 ⟨φ.flip z, ⟨z, rfl⟩, l - φ.flip z, hmem, add_sub_cancel _ _⟩
  have hIle : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ LinearMap.range φ.flip := by
    calc RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ RingHom.ker π • (LinearMap.range φ.flip ⊔ RingHom.ker π • ⊤) :=
          Submodule.smul_mono le_rfl htop
      _ = RingHom.ker π • LinearMap.range φ.flip ⊔ RingHom.ker π • RingHom.ker π • ⊤ := Submodule.smul_sup _ _ _
      _ ≤ LinearMap.range φ.flip := by
          refine sup_le Submodule.smul_le_right ?_
          rw [← Submodule.mul_smul, ← pow_two, hI2, Submodule.bot_smul]
          exact bot_le
  have hsurj : Function.Surjective φ.flip :=
    LinearMap.range_eq_top.1 (top_le_iff.1 (htop.trans (sup_le le_rfl hIle)))
  haveI : Module.Free C (Crys (divided₂ hsq) (spMap π) o₀.A) := Module.free_of_flat_of_isLocalRing
  let bs := Module.finBasis C (Crys (divided₂ hsq) (spMap π) o₀.A)
  have hinj : Function.Injective φ.flip := by
    have hs' : Function.Surjective (bs.toDualEquiv.symm.toLinearMap ∘ₗ φ.flip) :=
      bs.toDualEquiv.symm.surjective.comp hsurj
    have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs'
    exact fun x y hxy ↦ hi (by simp only [LinearMap.coe_comp, Function.comp_apply, hxy])
  have hneg : ∀ x, φ x = -φ.flip x := fun x ↦
    LinearMap.ext fun y ↦ by rw [LinearMap.neg_apply, LinearMap.flip_apply, skew]
  refine ⟨fun x x' hxx ↦ hinj (neg_injective ?_), fun l ↦ ?_⟩
  · rw [← hneg, ← hneg, hxx]
  · obtain ⟨z, hz⟩ := hsurj (-l)
    exact ⟨z, by rw [hneg, hz, neg_neg]⟩

end GlobalTheory.HTPerf
