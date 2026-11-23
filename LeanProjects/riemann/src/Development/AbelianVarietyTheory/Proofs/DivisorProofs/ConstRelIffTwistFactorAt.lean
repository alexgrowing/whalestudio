import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorCompare

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

theorem eq_one_of_chrEq_one {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem weilTwist_iff :
    WeilTwistColumns.WeilTwist R i ↔ (R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ t, FrameConstantVectors.WeilTwist R i t) := Iff.rfl

def ConstRel (cx : T0 → GA D (Wc D i) → ℂ) : Prop :=
  ∀ t : T0, ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ FrameConstantVectors.ConstTwist R i t (D.what₂.embLL ζ) (cx t)

def FrameRel (cx : T0 → GA D (Wc D i) → ℂ) : Prop :=
  ∀ t : T0, ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ ∀ h,
    cx A.μ0 h • FrameConstantVectors.frameVec (R.ωP i t) (R.vacP i) h =
      (D.what₂.embLL ζ * cx t h) • FrameConstantVectors.frameVec (R.ωP i A.μ0) (R.vacP i) h

def BaseIn {X : Type} (f : X → ℂ) : Prop :=
  ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ ∀ h, f h = D.what₂.embLL ζ

theorem root_mul_inv {K : Type} [Field K] {a b : K} (ha : ∃ m : ℕ, 0 < m ∧ a ^ m = 1) (hb : ∃ m : ℕ, 0 < m ∧ b ^ m = 1) :
    b ≠ 0 ∧ ∃ m : ℕ, 0 < m ∧ (a * b⁻¹) ^ m = 1 := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨fun h => by simp [h, hn.ne'] at hb, m * n, mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul, ha, one_pow, inv_pow, mul_comm m, pow_mul, hb, one_pow, inv_one, one_mul]

variable {R i}

theorem vac_theta (hv : R.thP_vP) (i : Fin D.R.m) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ R.vacP i ≠ 0 := by
  obtain ⟨-, h⟩ := (hv i A.μ0).1
  refine ⟨h.theta, fun h0 => ?_⟩
  obtain ⟨p, hp⟩ := h.norm.1
  have := h.norm.2 p hp
  simp [nrm2, h0] at this

theorem constTwist_iff (hv : R.thP_vP) (t : T0) (z : ℂ) (f : GA D (Wc D i) → ℂ) :
    FrameConstantVectors.ConstTwist R i t z f ↔ ∀ h, FrameConstantVectors.frameVec (R.ωP i t) (R.vacP i) h =
      (z * f h) • FrameConstantVectors.frameVec (R.ωP i A.μ0) (R.vacP i) h :=
  forall_congr' fun h => FrameConstantVectors.const_iff_frame _ _ (vac_theta hv i).2 h z (f h)

theorem base_eq_one (hv : R.thP_vP) {z : ℂ} {f : GA D (Wc D i) → ℂ} (H : FrameConstantVectors.ConstTwist R i A.μ0 z f)
    (h : GA D (Wc D i)) : z * f h = 1 :=
  smul_left_injective ℂ (FrameConstantVectors.frameVec_ne_zero _ (vac_theta hv i).2 h)
    (((constTwist_iff hv _ z f).1 H h).symm.trans (one_smul ℂ _).symm)

theorem constRel_iff (hv : R.thP_vP) (cx : T0 → GA D (Wc D i) → ℂ) :
    ConstRel R i cx ↔ FrameRel R i cx ∧ BaseIn (D := D) (cx A.μ0) := by
  have one : ∃ m : ℕ, 0 < m ∧ (1 : D.what₂.LL) ^ m = 1 := ⟨1, one_pos, one_pow _⟩
  constructor
  · intro H
    obtain ⟨z, hz, Hz⟩ := H A.μ0
    have hz0 : D.what₂.embLL z ≠ 0 := (map_ne_zero _).2 (root_mul_inv one hz).1
    have hb : ∀ h, cx A.μ0 h = (D.what₂.embLL z)⁻¹ := fun h => eq_inv_of_mul_eq_one_right (base_eq_one hv Hz h)
    refine ⟨fun t => ?_, 1 * z⁻¹, (root_mul_inv one hz).2, fun h => by rw [hb, one_mul, map_inv₀]⟩
    obtain ⟨ζ, hζ, Hζ⟩ := H t
    refine ⟨ζ * z⁻¹, (root_mul_inv hζ hz).2, fun h => ?_⟩
    rw [(constTwist_iff hv _ _ _).1 Hζ h, smul_smul, hb, map_mul, map_inv₀]
    congr 1
    ring
  · rintro ⟨H, z, hz, hb⟩ t
    obtain ⟨ζ, hζ, Hζ⟩ := H t
    have hz0 : D.what₂.embLL z ≠ 0 := (map_ne_zero _).2 (root_mul_inv one hz).1
    refine ⟨ζ * z⁻¹, (root_mul_inv hζ hz).2, (constTwist_iff hv _ _ _).2 fun h => ?_⟩
    rw [← inv_smul_smul₀ hz0 (FrameConstantVectors.frameVec (R.ωP i t) (R.vacP i) h), ← hb h, Hζ h, smul_smul, hb, map_mul, map_inv₀]
    congr 1
    ring

theorem frameRel_of_free (hv : R.thP_vP) {cx : T0 → GA D (Wc D i) → ℂ} {κ : ℂ}
    (H : ∀ t, FrameConstantVectors.ConstTwist R i t κ (cx t)) : FrameRel R i cx := fun t =>
  ⟨1, ⟨1, one_pos, one_pow _⟩, fun h => by
    rw [(constTwist_iff hv _ _ _).1 (H t) h, smul_smul, ← mul_assoc, mul_comm (cx A.μ0 h), base_eq_one hv (H A.μ0) h,
      map_one]⟩

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ D.R.r} {dict : GA D (Wc D i) → Σ k, Frame (U.X k).Ψ D.R.r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} {g : ℕ}
  {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
  {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {dδ : T0 → DeltaDat Xo c (Vc D i).rank}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) D.R.r}
  {dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r}
  {xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}

theorem cXi_eq (t : T0) :
    WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t) = FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t) := rfl

theorem ties_iff {Fc : Face D A} (hR : R.Char Fc) :
    WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi ↔
      (VStd D i ∧ (∀ k, ModelW (Wc D i) (rank_Wc i) (U.X k)) ∧
        (∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) ∧
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) x₀ ∧
        DictLat U (Wc D i) (rank_Wc i) dict ι e F ik φ th x₀) ∧
      CovPin Xo c dδ ∧ LatEmb (Wc D i) ι ∧ (∀ t, XiIs R i t (xi t)) ∧
        CXiVal (Wc D i) (rank_Wc i) σ dδ U₂ dict₂ ι x₀ xi :=
  ⟨fun ⟨_, _, _, a, b, c, d, e, f, g, h, k, m⟩ => ⟨⟨a, b, c, d, e, g⟩, h, f, k, m⟩,
    fun ⟨⟨a, b, c, d, e, g⟩, h, f, k, m⟩ => ⟨hR.lev, hR.thP.ωP, hR.thP.vP, a, b, c, d, e, f, g, h, k, m⟩⟩

theorem frame_iff_constOf (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) {t t' : T0}
    {cst cst' : GA D (Wc D i) → ℂ} (hc : WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t cst)
    (hc' : WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t' cst') (h : GA D (Wc D i)) (a b : ℂ) :
    a • FrameConstantVectors.frameVec (R.ωP i t') (R.vacP i) h = b • FrameConstantVectors.frameVec (R.ωP i t) (R.vacP i) h ↔
      a * cst' h = b * cst h := by
  obtain ⟨-, hω, hv, -, -, hΨ, hth, -⟩ := hT
  exact frame_iff_const (fun k => ⟨_, (hΨ k _).2 ⟨D.eTau.symm 1, rfl⟩⟩) hth (hω i t) (hω i t')
    (vac_theta hv i).1 (vac_theta hv i).2 hc hc' h a b

theorem cXi_ne_zero (hC : CXiVal (Wc D i) (rank_Wc i) σ dδ U₂ dict₂ ι x₀ xi) (t : T0) (h : GA D (Wc D i)) :
    WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t) h ≠ 0 := by
  obtain ⟨c0, hc, H⟩ := cXi_value hC
  obtain ⟨γ, -, e⟩ := H t h
  rw [e]
  exact mul_ne_zero (root_mul_inv hc hc).1 (Units.ne_zero _)

theorem twistFactorAt_of_frameRel
    (H : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi →
      FrameRel R i fun t => WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t)) :
    WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi := by
  intro hT c0 cb h0 hb t ct ht
  obtain ⟨ζ, hζ, Hζ⟩ := H hT t
  refine ⟨ζ, hζ, fun h => mul_left_cancel₀ (cXi_ne_zero hT.2.2.2.2.2.2.2.2.2.2.2.2 A.μ0 h) ?_⟩
  rw [(frame_iff_constOf hT h0 ht h _ _).1 (Hζ h), hb]
  ring

theorem frameRel_of_twistFactorAt (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi)
    (hex : ∀ t, ∃ ct, WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t ct)
    (H : WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) :
    FrameRel R i fun t => WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t) := by
  intro t
  obtain ⟨c0, h0⟩ := hex A.μ0
  obtain ⟨ct, ht⟩ := hex t
  have hne := cXi_ne_zero hT.2.2.2.2.2.2.2.2.2.2.2.2 A.μ0
  obtain ⟨ζ, hζ, Hζ⟩ := H hT c0 (fun h => c0 h / WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h) h0
    (fun h => (div_mul_cancel₀ _ (hne h)).symm) t ct ht
  refine ⟨ζ, hζ, fun h => (frame_iff_constOf hT h0 ht h _ _).2 ?_⟩
  have := hne h
  rw [Hζ h]
  field_simp

theorem baseIn_iff (hL : R.toLevCh.Is A.μ0) (hX : XiIs R i A.μ0 (xi A.μ0))
    (hC : CXiVal (Wc D i) (rank_Wc i) σ dδ U₂ dict₂ ι x₀ xi) :
    BaseIn (D := D) (WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0)) ↔
      ∀ h, ∃ a : D.what₂.LL, WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = D.what₂.embLL a := by
  refine ⟨fun ⟨z, _, hz⟩ h => ⟨z, hz h⟩, fun hv => ?_⟩
  obtain ⟨c0, ⟨m, hm, hc⟩, H⟩ := cXi_value hC
  have hb : ∀ h, WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = c0 := fun h => by
    obtain ⟨γ, -, e⟩ := H A.μ0 h
    obtain ⟨x, hx⟩ := RecDict.exists_isDetRoot D (Wc D i) (γ * h)
    rw [e, hX _ x hx, eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x, Circle.coe_one, mul_one]
  obtain ⟨a, ha⟩ := hv 1
  rw [hb] at ha
  exact ⟨a, ⟨m, hm, D.what₂.embLL.injective (by rw [map_pow, ← ha, hc, map_one])⟩, fun h => (hb h).trans ha⟩

theorem constRel_iff_twistFactorAt (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi)
    (hex : ∀ t, ∃ ct, WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t ct) :
    ConstRel R i (fun t => FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t)) ↔
      WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi ∧
        ∀ h, ∃ a : D.what₂.LL, FrameConstantVectors.cXi (Wc D i) σ (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = D.what₂.embLL a :=
  (constRel_iff hT.2.2.1 _).trans (and_congr
    ⟨fun h => twistFactorAt_of_frameRel fun _ => h, frameRel_of_twistFactorAt hT hex⟩
    (baseIn_iff hT.1 (hT.2.2.2.2.2.2.2.2.2.2.2.1 A.μ0) hT.2.2.2.2.2.2.2.2.2.2.2.2))

theorem constRel_iff_norm (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi)
    (hex : ∀ t, ∃ ct, WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t ct)
    (h1 : ∀ h, WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = 1) :
    (ConstRel R i (fun t => FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t)) ↔
      WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) ∧
    (WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi ↔
      WeilTwistColumns.TwistFactorNormAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) :=
  ⟨(constRel_iff_twistFactorAt hT hex).trans (and_iff_left fun h => ⟨1, (h1 h).trans (map_one _).symm⟩),
    fun H => H.norm, fun H _ c0 cb h0 hb t ct ht => by
      obtain rfl : c0 = cb := funext fun h => by rw [hb, h1, mul_one]
      exact H hT h1 c0 h0 t ct ht⟩

theorem twistFactorAt_of_closed (H : FrameConstantVectors.TwistFactor) {Fc : Face D A} (hR : R.Char Fc) (jL : D.what₂.LL →+* c.F)
    (hj : σ.comp jL = D.what₂.embLL) (hI : LatIsom (Wc D i) Dw.EF ι)
    (hv : ∀ t h, ∃ a : D.what₂.LL, FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t) h = D.what₂.embLL a) :
    WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi :=
  twistFactorAt_of_frameRel fun ⟨_, _, hvP, _, _, _, _, _, a, _, b, d, f⟩ => ((constRel_iff hvP _).1
    (H D G Pl0 T0 A Ks R Fc i _ Dw l Xo c σ jL _ (rank_Wc i) dδ U₂ dict₂ ι x₀ xi hR hj b a hI d f hv)).1

theorem twistFactor_of_free (H : FrameConstantVectors.TwistFactorFree) {Fc : Face D A} (hR : R.Char Fc) : WeilTwistColumns.TwistFactor R :=
  fun i H' Dw l Xo c σ _ _ ι _ _ _ _ _ _ x₀ dδ U₂ dict₂ xi =>
    twistFactorAt_of_frameRel fun ⟨_, _, hvP, _, _, _, _, _, _, _, _, d, f⟩ =>
      frameRel_of_free hvP
        (H D G Pl0 T0 A Ks R Fc i H' Dw l Xo c σ _ (rank_Wc i) dδ U₂ dict₂ ι x₀ xi hR d f).choose_spec.2

theorem constRel_of_twistFactor (H : WeilTwistColumns.TwistFactor R)
    (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi)
    (hex : ∀ t, ∃ ct, WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t ct)
    (hv : ∀ t h, ∃ a : D.what₂.LL, FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t) h = D.what₂.embLL a) :
    ConstRel R i fun t => FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t) :=
  (constRel_iff_twistFactorAt hT hex).2 ⟨H i _ Dw l Xo c σ U dict ι g e F ik φ th x₀ dδ U₂ dict₂ xi, hv A.μ0⟩

end Row

end GlobalTheory.TwistFactorCompare

end
