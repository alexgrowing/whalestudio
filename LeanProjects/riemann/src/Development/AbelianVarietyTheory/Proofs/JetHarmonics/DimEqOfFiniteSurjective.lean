import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.CMObjBundlePull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsPolFibreOfKeyPB
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingHomExtRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.BarEqOfLamEqMultiplier
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrime
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommonDenominatorOfValuationLeOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LeftEqOfIsLieCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtDvrAndLaws

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.LamCM Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTan
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

namespace GlobalTheory.CMClaims

theorem laws : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
theorem secTwist : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
theorem homExt : CM.HomExtDvr := fun T K _ _ _ _ _ _ G G' _ _ hG hG' φ hφ =>
  GlobalTheory.existsUnique_hom_extension_semiAbelian T K G G' hG hG' φ hφ

section Vec

variable {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {G : Over (Sp R)} {G' : Over (Sp R')} [GrpObj G]
  [GrpObj G'] {φ : G'.left ⟶ G.left}

def push (h : IsGrpPullback G' G (spMap f) φ) (w : epsR R' ⟶ G') : epsAt (spMap f) ⟶ G :=
  Over.homMk (w.left ≫ φ) (by
    change (w.left ≫ φ) ≫ G.hom = (epsR R').hom ≫ spMap f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w w])

variable (h : IsGrpPullback G' G (spMap f) φ)

variable [IsCommMonObj G'] {n : ℕ} {v : Fin n → (epsR R' ⟶ G')} (hv : IsLieBasis v)

def comb (c : Fin n → R') : epsR R' ⟶ G' := ((LieComb.lieComb_algebra R' G' n v hv.1).1 c).exists.choose

theorem isLieComb_iff (c : Fin n → R') (w : epsR R' ⟶ G') : IsLieComb c v w ↔ w = comb hv c :=
  have a := ((LieComb.lieComb_algebra R' G' n v hv.1).1 c).exists.choose_spec
  ⟨fun b => ((LieComb.lieComb_algebra R' G' n v hv.1).1 c).unique b a, fun b => b ▸ a⟩

theorem isLieComb_comb (c : Fin n → R') : IsLieComb c v (comb hv c) := (isLieComb_iff hv c _).2 rfl

theorem isTangent_iff (w : epsR R' ⟶ G') : IsTangent w ↔ ∃ c, comb hv c = w :=
  ⟨fun a => (hv.2 w a).exists.imp fun c b => ((isLieComb_iff hv c w).1 b).symm,
    fun ⟨c, a⟩ => a ▸ (LieComb.lieComb_algebra R' G' n v hv.1).2.1 _ _ (isLieComb_comb hv c)⟩

theorem comb_injective : Function.Injective (comb hv) := fun a b e =>
  (hv.2 _ ((isTangent_iff hv _).2 ⟨a, rfl⟩)).unique (isLieComb_comb hv a) (e ▸ isLieComb_comb hv b)

def vecOf (c : Fin n → R') : epsAt (spMap f) ⟶ G := push h (comb hv c)

end Vec

section Pair

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E}

end Pair

section Isog

theorem card_torsion_eq {M N : Type} [CommGroup M] [CommGroup N] (F : M →* N) (hF : Function.Surjective F) (m : ℕ)
    (hm : ∀ x, F x = 1 → x ^ (m + 1) = 1) :
    Nat.card {x : M // x ^ (m + 2) = 1} = Nat.card {y : N // y ^ (m + 2) = 1} := by
  refine Nat.card_eq_of_bijective (fun x => ⟨F x.1, by rw [← map_pow, x.2, map_one]⟩) ⟨fun a b e => ?_, fun y => ?_⟩
  · have e₁ : F (a.1 / b.1) = 1 := by rw [map_div, div_eq_one]; exact congrArg Subtype.val e
    have e₂ : (a.1 / b.1) ^ (m + 2) = 1 := by rw [div_pow, a.2, b.2, div_one]
    rw [pow_succ, hm _ e₁, _root_.one_mul, div_eq_one] at e₂
    exact Subtype.ext e₂
  · obtain ⟨x, hx⟩ := hF y.1
    have e₁ : (x ^ (m + 2)) ^ (m + 1) = 1 := hm _ (by rw [map_pow, hx, y.2])
    refine ⟨⟨x ^ ((m + 1) * (m + 1)), ?_⟩, Subtype.ext ?_⟩
    · rw [← pow_mul, show (m + 1) * (m + 1) * (m + 2) = (m + 2) * (m + 1) * (m + 1) by ring, pow_mul, pow_mul, e₁, one_pow]
    · change F _ = y.1
      rw [map_pow, hx, show (m + 1) * (m + 1) = (m + 2) * m + 1 by ring, pow_succ, pow_mul, y.2, one_pow, _root_.one_mul]

variable {K : Type} [Field K] [NumberField K]

theorem onto_points {R k : Type} [CommRing R] [Field k] [IsAlgClosed k] {P Q : Over (Sp R)} (Φ : P ⟶ Q)
    [IsFinite Φ.left] [Surjective Φ.left] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ Q) : ∃ x : Over.mk t ⟶ P, y = x ≫ Φ := by
  obtain ⟨p, hp⟩ := GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y

end Isog

section Sum

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l} {p q : ℕ}

end Sum

section Types

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

def vec (hf : abelian₂.IsFibreOf A x (abelian₂.gmap K) φ) (i : Fin x.P.g) : epsAt (genPt K) ⟶ A.A := push hf.1 (x.v i)

variable {E : Type} [Field E] [NumberField E]

def resLab (lab : (E →+* ℂ) → (E →+* K)) (t : E →+* ℂ) : 𝓞 E →+* K := (lab t).comp (algebraMap (𝓞 E) E)

end Types

section Lines

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

end Lines

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def conjType (H : Host E) : {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0} ≃ psiBar H :=
  Equiv.subtypeEquivRight (LamF.host_mem_compl_psiSet H)

variable [StarRing (𝓞 E)] {l : Level H} {c : Coeff l} {p q : ℕ}

def Readable (o : abelian₂.LamObj c p q) : Prop :=
  abelian₂.IsFibreOf o.AΨ o.xΨ (abelian₂.gmap o.K₁) o.φΨg ∧ abelian₂.IsFibreOf o.A' o.x' (abelian₂.gmap o.K₁) o.φ'g ∧
    (∀ i, IsMonHom (o.φΨ i)) ∧ (∀ i, IsMonHom (o.φ' i)) ∧
    (∀ i (a : 𝓞 E), o.oaΨ.act a ≫ o.φΨ i = o.φΨ i ≫ o.oa.act a) ∧
    ∀ i (a : 𝓞 E), o.oa'.act a ≫ o.φ' i = o.φ' i ≫ o.oa.act a

theorem Readable.fibP {o : abelian₂.LamObj c p q} (h : Readable o) : abelian₂.IsFibreOf o.AΨ o.xΨ (abelian₂.gmap o.K₁) o.φΨg := h.1
theorem Readable.fibC {o : abelian₂.LamObj c p q} (h : Readable o) : abelian₂.IsFibreOf o.A' o.x' (abelian₂.gmap o.K₁) o.φ'g := h.2.1
theorem Readable.homP {o : abelian₂.LamObj c p q} (h : Readable o) (i : Fin p) : IsMonHom (o.φΨ i) := h.2.2.1 i
theorem Readable.homC {o : abelian₂.LamObj c p q} (h : Readable o) (i : Fin q) : IsMonHom (o.φ' i) := h.2.2.2.1 i
theorem Readable.linP {o : abelian₂.LamObj c p q} (h : Readable o) (i : Fin p) (a : 𝓞 E) :
    o.oaΨ.act a ≫ o.φΨ i = o.φΨ i ≫ o.oa.act a := h.2.2.2.2.1 i a
theorem Readable.linC {o : abelian₂.LamObj c p q} (h : Readable o) (i : Fin q) (a : 𝓞 E) :
    o.oa'.act a ≫ o.φ' i = o.φ' i ≫ o.oa.act a := h.2.2.2.2.2 i a

def TargetLines (o : abelian₂.LamObj c p q) : Prop :=
  abelian₂.IsFibreOf o.B o.xB (abelian₂.gmap o.K₁) o.φB ∧ o.Tl.Good ∧ o.LamL.Good ∧ (∀ v, KeyLocAt o.xB o.Tl o.LamL v) ∧
    (∀ σ, KeyArchAt o.xB o.Tl o.LamL σ) ∧ ∀ v, ∃ M, abelian₂.IsModelAt o.B o.xB o.φB v M ∧ IsLocGen v M.det o.LamL.I

def toCM (o : abelian₂.LamObj c p q) (h : Readable o) : CMObj c p q where
  K := o.K₁
  B := o.B
  AP := o.AΨ
  AC := o.A'
  ιB := o.oa.toRingAct
  ιP := o.oaΨ.toRingAct
  ιC := o.oa'.toRingAct
  φP := o.φΨ
  φP_hom := h.homP
  φP_lin := h.linP
  φC := o.φ'
  φC_hom := h.homC
  φC_lin := h.linC
  hP := o.hΨ
  hC := o.h'
  ηP t := vec h.fibP (o.τΨ.symm t)
  ηC t := vec h.fibC ((o.τ'.trans (conjType H)).symm t)
  ℓP t := o.ℓΨ (o.τΨ.symm t)
  ℓC t := o.ℓ' ((o.τ'.trans (conjType H)).symm t)

variable (hs : ∀ a : 𝓞 E, star a = H.bar a) (o : abelian₂.LamObj c p q) (h : Readable o)

end Main

end GlobalTheory.CMClaims
