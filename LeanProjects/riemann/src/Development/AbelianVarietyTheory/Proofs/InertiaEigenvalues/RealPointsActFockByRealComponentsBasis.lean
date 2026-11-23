import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.RealPtsFock

open GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.RealFockAction GlobalTheory.VacuumCharacter

variable {D : D7}

section Gen

variable {S T : HSp D}

theorem om_vac_of {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hF : B.F.Good)
    (hsig : ∀ τ, (B.w.p τ, B.w.q τ) = T.sig (tauE D τ)) (hsigOK : T.SigOK) (heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta)
    (hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2))
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S) :
    ω (u, 1) f = (((detFam B.w.c (realGL B.F.θ S u))⁻¹ : ℂˣ) : ℂ) • f := by
  have hθ := hF.vac.2.inf
  have hS := fun τ => GlobalTheory.FockBasis.isCartanInv_one (onb_posDef (hF.onbS τ))
  have hT := hF.cartT
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have hpq : ∀ τ, B.w.p τ + B.w.q τ = T.rank := fun τ => by
    obtain ⟨e, -⟩ := hsigOK (tauE D τ)
    rw [← hsig τ] at e
    simpa using (Fintype.card_congr e).symm
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (B.F.sT τ) (hT τ).1
  have ep : ∀ τ, p τ = B.w.p τ := fun τ => by
    have h1 := hF.onbT τ
    rw [← hsig τ] at h1
    have h2 := (onb_laws h1 (hpq τ ▸ Nat.le_add_right _ _)).2
    rw [hp] at h2
    have h3 : (p τ : ℂ) = B.w.p τ := by linear_combination h2 / 2
    exact_mod_cast h3
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D B.F.ψ hω.std S T B.F.θ hθ _ _ ω B.eta heta hω (fun _ => 1) B.F.sT hS hT u hu 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (B.mu * ψ.chi * B.eta⁻¹ * (B.eta ^ T.rank)⁻¹) τ ((B.w.c τ - p τ : ℤ) : ℚ) := fun τ => by
    have h1 := hasInfExp_twist (hasInfExp_twist (hinf τ) (heta.2.2.2 τ) 1) (heta.2.2.2 τ) T.rank
    rw [pow_one] at h1
    convert h1 using 1
    rw [← hpq τ, ep]
    push_cast
    ring
  rw [MonoidHom.map_one, mul_one, Circle.coe_inv, hxv _ _ hexp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    Units.val_inv_eq_inv_val]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := B.F.θ) τ u)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [one, (hd τ _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, mul_one, ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_one, one_pow,
    one_mul, show (realGL B.F.θ S u τ).val = compAt B.F.θ τ (Formalism.L2.Theta.mt S u) from rfl, zpow_sub₀ g0, zpow_natCast,
    inv_pow]
  have := pow_ne_zero (p τ) g0
  have := zpow_ne_zero (B.w.c τ) g0
  field_simp

theorem om_fock_of {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hF : B.F.Good)
    (hsig : ∀ τ, (B.w.p τ, B.w.q τ) = T.sig (tauE D τ)) (hsigOK : T.SigOK) (heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta)
    (hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2))
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hF.vac.2.inf
  have hBS := fun τ => onb_posDef (hF.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hsigOK (tauE D τ)
    rw [← hsig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, om_vac_of hF hsig hsigOK heta hinf hω hf hv hu,
    GlobalTheory.FiniteFock.pureTensorO_smul,
    pureTensorO_subst (p := B.w.p) hF.vac.1 hθ
      (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hF.cartT
      (fun τ => (onb_laws (by have := hF.onbT τ; rwa [← hsig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

theorem mem_UH_of_conj {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hB : IsUnit B.det)
    (hg : B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ) : g ∈ Formalism.QuantumDeterminants.UH G := by
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have h3 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hU : (B⁻¹ * g * B)ᴴ * (B⁻¹ * g * B) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hg
    rwa [Matrix.star_eq_conjTranspose] at this
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  have hgB : g = B * (B⁻¹ * g * B) * B⁻¹ := by
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  show gᴴ * G * g = G
  calc gᴴ * G * g = (B⁻¹)ᴴ * ((B⁻¹ * g * B)ᴴ * (Bᴴ * (B⁻¹)ᴴ) * (B⁻¹ * B) * (B⁻¹ * g * B)) * B⁻¹ := by
        conv_lhs => rw [hgB, hG]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h3, h2, Matrix.mul_one, Matrix.mul_one, hU, Matrix.mul_one, ← hG]

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}

theorem om_ptP (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) {ψ : Twist D Circle} {t : T0}
    (ht : IsTupOf R B ψ t) {u : GA D (Vc D i)} (hu : u ∈ GinfC (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (B.act u P) := by
  have hL := hC.lev
  have hW := hC.thP.ωP i A.μ0
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hω := h.isWeil hC.thP.ωP ht
  have hpt : ∀ P, R.ptP i t P = B.F.fock (R.vP i t) P := fun P => by rw [h.fock_eq]; rfl
  have hf' : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (R.vP i t) := by rw [h.ψ]; exact hf
  have hv' : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D i) (Wc D i)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP i t) := by
    rw [h.ψ, h.θ, h.sT]; exact hv
  have hsig : ∀ τ, (B.w.p τ, B.w.q τ) = (Wc D i).sig (tauE D τ) := fun τ => by rw [h.p, h.q]
  have heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta := by
    rw [h.eta]
    exact GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT
      (hev.add_odd (rW ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  have hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) := fun τ => by
    rw [h.mu_mul ht, h.exponent]
    exact (GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 hL i t τ).mu
  rw [hpt, hpt]
  exact om_fock_of (GlobalTheory.ConjTwist.Test.frame_good hC h) hsig (D.sp.W_sig _) heta hinf hω hf' hv' hu P

theorem real_points_fock : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∃ (w : GlobalTheory.ExportSeries.Weight D (Vc D i).rank) (BS : GlobalTheory.ExportSeries.GLR D (Vc D i).rank) (r : ↥(GinfC (Vc D i)) →* GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ (u : ↥(GinfC (Vc D i))) (P : PolF D (Wc D i).rank (Vc D i).rank), R.ωP i t ((u : GA D (Vc D i)), 1) (R.ptP i t P) = R.ptP i t (GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r u) P)) ∧ (∀ (u : ↥(GinfC (Vc D i))) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r u) τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ (∀ g : GlobalTheory.ExportSeries.GLR D (Vc D i).rank, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) → ∃ u, r u = g) ∧ (∀ (τ : D.what₂.Tau) (j : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε τ j = decide ((j : ℕ) < w.p τ)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t
  have hC := hG.core
  obtain ⟨B, hb, ht, rfl⟩ : ∃ B : Base (Vc D i) (Wc D i), BaseOf R i B ∧ IsTupOf R B (tupTwist R t) t ∧
      B = baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩ :=
    ⟨_, baseOf_baseAt R hC.models.BV _ _, isTupOf_tupTwist R hC.models.BV t _, rfl⟩
  have hF := GlobalTheory.ConjTwist.Test.frame_good hC hb
  have hθ : IsInfFam R.θ := hF.vac.2.inf
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_posDef (hC.models.BV i τ)
  have eu : ∀ (g : GLR D (Vc D i).rank) τ,
      (inBasis (baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩).F.BS g τ).val = (R.BV i τ)⁻¹ * (g τ).val * R.BV i τ :=
    fun g τ => by
      rw [← hb.BS τ, ← Matrix.coe_units_inv]
      rfl
  refine ⟨liftWeight D i, (baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩).F.BS,
    (realGL R.θ (Vc D i)).comp (GinfC (Vc D i)).subtype, fun u P => om_ptP hC hb ht u.2 P, fun u τ => ?_, fun g hg => ?_,
    fun τ j => hC.models.order i τ j⟩
  · rw [eu]
    exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ (u : GA D (Vc D i)) τ)
  · have hU : ∀ τ, (g τ).val ∈ Formalism.QuantumDeterminants.UH (gramAt D (Vc D i) τ) := fun τ => by
      refine mem_UH_of_conj (hBS τ) ?_ (by rw [← eu]; exact hg τ)
      rw [← hb.BS τ]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    refine ⟨⟨GlobalTheory.AdelicScalar.realElt R.θ (Vc D i) (fun τ => (g τ).val), list_prod_mem fun x hx => ?_⟩, ?_⟩
    · obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
      exact GlobalTheory.PointAtPlaceHom.atTau_mem _ τ _
    · funext ρ
      refine Units.ext ?_
      change infMat D.sp.cm.sig (Vc D i).gram (R.θ ρ) (GlobalTheory.AdelicScalar.realElt R.θ (Vc D i) fun τ => (g τ).val) = (g ρ).val
      rw [GlobalTheory.AdelicScalar.realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ _ hU ρ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]

end GlobalTheory.RealPtsFock

end
