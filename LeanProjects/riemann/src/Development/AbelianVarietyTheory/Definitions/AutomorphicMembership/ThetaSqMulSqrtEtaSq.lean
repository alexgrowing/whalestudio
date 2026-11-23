import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ChiGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorial
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamHomogOfHomog
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorialStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaPowAndDegree
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaAndKeyCore

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyPow GlobalTheory.KeyCl

noncomputable section
namespace GlobalTheory.LocM

structure NgC (g : ℕ) : Type where

  τ : Matrix (Fin g) (Fin g) ℂ
  symm : τ.IsSymm
  pos : (τ.map Complex.im).PosDef

  a : Fin g → ℂ

  b : Fin g → ℂ
  half : charHalf g a b

namespace NgC

variable {g : ℕ}

def base (g : ℕ) (a b : Fin g → ℂ) (h : charHalf g a b) : NgC g :=
  ⟨_, (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).1,
    (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).2, a, b, h⟩

instance (g : ℕ) : Nonempty (NgC g) := ⟨base g 0 0 ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩⟩

def Y (z : NgC g) : Matrix (Fin g) (Fin g) ℝ := z.τ.map Complex.im

def Frame (z : NgC g) (x : KeyIn ℂ) : Prop :=
  ∃ h : x.P.g = g, NormalAt x (z.τ.submatrix (Fin.cast h) (Fin.cast h)) 1
    (fun i => z.a (i.cast h)) (fun i => z.b (i.cast h)) 1

def Lies (z : NgC g) (x : KeyIn ℂ) : Prop := KeyEq.Nrm x z.τ z.a z.b

theorem Frame.lies {z : NgC g} {x : KeyIn ℂ} (h : z.Frame x) : z.Lies x := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, 1, 1, one_ne_zero, h⟩

theorem exists_frame (hg : 1 ≤ g) (z : NgC g) : ∃ x : KeyIn ℂ, z.Frame x :=
  KeyOfPeriod.exists_keyIn_normalAt thetaUnifAV_all torusAlgebraic_holds g z.τ z.a z.b hg z.symm z.pos z.half

theorem exists_of_keyIn (x : KeyIn ℂ) : ∃ z : NgC x.P.g, z.Lies x := by
  obtain ⟨⟨τ, M, a, b, c, hab, hc, -, hN⟩, -⟩ := KeyNormalExists.exists_normalAt thetaUnifAV_all x
  exact ⟨⟨τ, hN.mem_siegelH.1, hN.mem_siegelH.2, a, b, hab⟩, rfl, M, c, hc, hN⟩

def cubSq (z : NgC g) (w : Fin g → ℂ) : ℝ :=
  ‖thetaChar z.τ z.a z.b w‖ ^ 2 *
    Real.exp (-2 * Real.pi * ((fun i => (w i).im) ⬝ᵥ (z.Y)⁻¹.mulVec fun i => (w i).im))

def thetaSq (z : NgC g) : ℝ :=
  ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
    z.cubSq ((fun i => (p (.inl i) : ℂ)) + z.τ.mulVec (fun i => (p (.inr i) : ℂ)))

def lieGram (z : NgC g) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => Real.pi * hermForm ((z.Y)⁻¹.map fun x : ℝ => (x : ℂ))
    (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (Pi.single j (2 * Real.pi * Complex.I)⁻¹)

def etaSq (z : NgC g) : ℝ := (z.lieGram.det.re)⁻¹

theorem det_Y_pos (z : NgC g) : 0 < z.Y.det := z.pos.det_pos

theorem thetaSq_eq (z : NgC g) : z.thetaSq = (Real.sqrt (2 ^ g * z.Y.det))⁻¹ := by
  have ha : z.a = fun i => (((z.a i).re : ℝ) : ℂ) := (TorusAlg.ofRealVec_re z.half.1).symm
  have hb : z.b = fun i => (((z.b i).re : ℝ) : ℂ) := (TorusAlg.ofRealVec_re z.half.2).symm
  refine Eq.trans ?_ (ThetaNorm.integral_norm_sq_thetaChar g z.τ (fun i => (z.a i).re) (fun i => (z.b i).re)
    z.symm z.pos)
  rw [← ha, ← hb, thetaSq]
  congr 1
  funext p
  have e : (fun i => (((fun i => (p (.inl i) : ℂ)) + z.τ.mulVec (fun i => (p (.inr i) : ℂ))) i).im) =
      z.Y.mulVec fun i => p (.inr i) := by
    funext i
    simp [Y, Matrix.mulVec, dotProduct]
  rw [cubSq, e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ z.det_Y_pos.ne'.isUnit, Matrix.one_mulVec,
    dotProduct_comm]
  rfl

theorem lieGram_eq (z : NgC g) :
    z.lieGram = (((4 * Real.pi)⁻¹ • (z.Y)⁻¹ : Matrix (Fin g) (Fin g) ℝ)).map fun x : ℝ => (x : ℂ) := by
  ext i j
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : star (Pi.single j (2 * Real.pi * Complex.I : ℂ)⁻¹ : Fin g → ℂ) =
      Pi.single j (-(2 * Real.pi * Complex.I : ℂ)⁻¹) := by
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  simp only [lieGram, Matrix.of_apply, hermForm, e, single_dotProduct, Matrix.mulVec_single, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp
  field_simp
  simp
  ring

theorem etaSq_eq (z : NgC g) : z.etaSq = (4 * Real.pi) ^ g * z.Y.det := by
  have e : z.lieGram.det = ((((4 * Real.pi)⁻¹ • (z.Y)⁻¹ : Matrix (Fin g) (Fin g) ℝ)).det : ℝ) := by
    rw [lieGram_eq]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  rw [etaSq, e, Complex.ofReal_re, Matrix.det_smul, Matrix.det_nonsing_inv, Fintype.card_fin, Ring.inverse_eq_inv',
    mul_inv, inv_inv, inv_pow, inv_inv]

theorem thetaSq_pos (z : NgC g) : 0 < z.thetaSq := by
  have := z.det_Y_pos
  rw [thetaSq_eq]; positivity

theorem etaSq_pos (z : NgC g) : 0 < z.etaSq := by
  have := z.det_Y_pos
  have := Real.pi_pos
  rw [etaSq_eq]; positivity

theorem thetaSq_mul_sqrt_etaSq (z : NgC g) : z.thetaSq * Real.sqrt z.etaSq = Real.sqrt ((2 * Real.pi) ^ g) := by
  have := z.det_Y_pos
  have := Real.pi_pos
  rw [thetaSq_eq, etaSq_eq, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [show (4 * Real.pi) ^ g = 2 ^ g * (2 * Real.pi) ^ g by rw [← mul_pow]; congr 1; ring]
  field_simp

end NgC

structure IsKF (g c : ℕ) (κ : Rule) : Prop where
  homog : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
    (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
    (∀ i, IsLieComb (M i) v (v' i)) →
    a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩
  funct : Funct κ
  unitSp : UnitSp κ
  off : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), x.P.g ≠ g → κ K x = 1

namespace IsKF

variable {g c : ℕ} {κ κ' : Rule}

theorem famUnit (h : IsKF g c κ) : FamUnit κ := KeyFamUnit.famUnit κ h.funct h.unitSp

theorem valUnit (h : IsKF g c κ) : ValUnit κ := KeyValUnit.valUnit κ h.funct h.unitSp

theorem famHomog (h : IsKF g c κ) (S : Type) [CommRing S] [IsDomain S] [CharZero S] (P : Out.PolAV (Sp S))
    (hg rig hr th hth v hv th' hth' v' hv') (a : S) (M : Matrix (Fin P.g) (Fin P.g) S) (u u' : S) (hP : P.g = g)
    (ha : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) (hM : ∀ i, IsLieComb (M i) v (v' i))
    (hu : IsValue κ ⟨P, hg, rig, hr, th, hth, v, hv⟩ u) (hu' : IsValue κ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ u') :
    a ^ (2 * c) * u' = M.det ^ c * u := by
  obtain ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁, th₁', hth₁', v₁', hv₁', M₁, h₁, h₂, ha₁, hN, hd⟩ :=
    KeyGalDesc.exists_keyPB_pair (algebraMap S (FractionRing S)) P hg rig hr th hth v hv th' hth' v' hv' a M ha hM
  have e := h.homog _ Q hg₁ rig₁ hr₁ th₁ hth₁ v₁ hv₁ th₁' hth₁' v₁' hv₁' _ M₁ ((KeyGalDesc.g_eq h₁).trans hP) ha₁ hN
  rw [hu _ _ _ h₁, hu' _ _ _ h₂, hd] at e
  apply IsFractionRing.injective S (FractionRing S)
  simpa only [map_mul, map_pow] using e

theorem value_normalAt (h : IsKF g c κ) (x : KeyIn ℂ) (hx : x.P.g = g) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hc : c₀ ≠ 0) (hM : M.det ≠ 0) (hN : NormalAt x τ M a b c₀) (t : ℂ)
    (ht : ∀ (y : KeyIn ℂ) (e : y.P.g = x.P.g), NormalAt y (τ.submatrix (Fin.cast e) (Fin.cast e)) 1
      (fun i => a (i.cast e)) (fun i => b (i.cast e)) 1 → (κ ℂ y : ℂ) = t) :
    c₀ ^ (2 * c) * (κ ℂ x : ℂ) = M.det ^ c * t := by
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := KeyConst.exists_rescale P hg rig hr th hth v hv τ M _ _ c₀ hc hM hN
  rw [← ht ⟨P, hg, rig, hr, th₀, hth₀, v₀, hv₀⟩ rfl hN₀]
  exact h.homog ℂ P hg rig hr _ hth₀ v₀ hv₀ th hth v hv c₀ M hx e₁ hMv

theorem ext (h : IsKF g c κ) (h' : IsKF g c κ') (f : NgC g → ℂˣ)
    (hf : ∀ (z : NgC g) x, z.Frame x → κ ℂ x = f z) (hf' : ∀ (z : NgC g) x, z.Frame x → κ' ℂ x = f z) : κ = κ' := by
  funext K _ _ x
  by_cases hx : x.P.g = g
  swap
  · rw [h.off K x hx, h'.off K x hx]
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := (KeyCountableDescent.keyIn_descends_countable firstFiveLaws.1).2 K x
  obtain ⟨σ⟩ := KeyRuleUnique.nonempty_ringHom_complex K₀
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ σ
  have hyg : y.P.g = g := (KeyGalDesc.g_eq hy).trans ((KeyGalDesc.g_eq hx₀).symm.trans hx)
  subst hyg
  obtain ⟨⟨τ, M, a, b, c₀, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt thetaUnifAV_all y
  let z : NgC y.P.g := ⟨τ, hN.mem_siegelH.1, hN.mem_siegelH.2, a, b, hab⟩
  have e : (κ ℂ y : ℂ) = κ' ℂ y := by
    refine mul_left_cancel₀ (pow_ne_zero (2 * c) hc) ?_
    rw [h.value_normalAt y rfl hc hM hN (f z) fun w e hw => congrArg Units.val (hf z w ⟨e, hw⟩),
      h'.value_normalAt y rfl hc hM hN (f z) fun w e hw => congrArg Units.val (hf' z w ⟨e, hw⟩)]
  rw [h.funct K₀ ℂ σ x₀ y hy, h'.funct K₀ ℂ σ x₀ y hy] at e
  apply Units.ext
  rw [h.funct K₀ K _ x₀ x hx₀, h'.funct K₀ K _ x₀ x hx₀, σ.injective e]

theorem not_one (hg : 1 ≤ g) (hc : 1 ≤ c) : ¬ IsKF g c (fun _ _ _ _ => 1) := fun h => by
  obtain ⟨z⟩ : Nonempty (NgC g) := inferInstance
  obtain ⟨x, hx, -⟩ := z.exists_frame hg
  choose M hM using fun i => (x.basis.2 (x.v i) (x.basis.1 i)).exists
  obtain ⟨t, -, e, hle⟩ := exists_sec_div x.P.A.hom (mul_inv_cancel₀ (two_ne_zero (α := ℂ))) x.th
  have e₁ := h.homog ℂ x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne x.v x.basis 1 (Matrix.of M) hx
    (fun i => by rw [constFn_one, _root_.one_mul]) hM
  have e₂ := h.homog ℂ x.P x.g_pos x.rig x.rig_gen t (fun s => (x.th_ne s).imp fun y hy => ⟨hy.1, hle hy.2⟩) x.v x.basis
    x.th x.th_ne x.v x.basis 2 (Matrix.of M) hx e hM
  rw [← e₁, _root_.one_pow] at e₂
  have e₃ : (2 : ℂ) ^ (2 * c) = 1 := by simpa using e₂
  have e₄ : (2 : ℕ) ^ (2 * c) = 1 := by exact_mod_cast e₃
  rw [Nat.pow_eq_one] at e₄
  omega

end IsKF

open Classical in

def cutRule (g : ℕ) (s : ℤˣ) (κ : Rule) : Rule := fun K _ _ x =>
  if x.P.g = g then Units.map (Int.castRingHom K).toMonoidHom s * κ K x else 1

theorem isKF_cutRule {g c : ℕ} (s : ℤˣ) {κ : Rule}
    (hH : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩)
    (hF : Funct κ) (hU : UnitSp κ) : IsKF g c (cutRule g s κ) where
  homog K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂ := by
    simp only [cutRule, if_pos hP, Units.val_mul]
    rw [mul_left_comm, hH K P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂, mul_left_comm]
  funct K K' _ _ _ _ f x x' h := by
    simp only [cutRule, KeyGalDesc.g_eq h]
    split_ifs
    · simp [hF K K' f x x' h]
    · simp
  unitSp R K _ _ _ _ _ _ _ x xK h := by
    by_cases hx : x.P.g = g
    · obtain ⟨u, hu, hk⟩ := hU R K x xK h
      refine ⟨Units.map (Int.castRingHom R).toMonoidHom s * u, ?_, fun k _ _ r xk hr hxk => ?_⟩
      · simp [cutRule, KeyGalDesc.g_eq h, hx, hu]
      · simp [cutRule, KeyGalDesc.g_eq hxk, hx, hk k r xk hr hxk]
    · exact ⟨1, by simp [cutRule, KeyGalDesc.g_eq h, hx],
        fun k _ _ r xk hr hxk => by simp [cutRule, KeyGalDesc.g_eq hxk, hx]⟩
  off K _ _ x hx := if_neg hx

structure KF (g c : ℕ) : Type where

  val : NgC g → ℂˣ
  ex : ∃ κ : Rule, IsKF g c κ ∧ ∀ (z : NgC g) (x : KeyIn ℂ), z.Frame x → κ ℂ x = (val z)⁻¹
  zero : g = 0 → ∀ z, val z = 1 ∨ val z = -1

namespace KF

variable {g c : ℕ} (kf : KF g c)

def rule : Rule := kf.ex.choose

theorem isKF : IsKF g c kf.rule := kf.ex.choose_spec.1

theorem rule_frame {z : NgC g} {x : KeyIn ℂ} (h : z.Frame x) : kf.rule ℂ x = (kf.val z)⁻¹ :=
  kf.ex.choose_spec.2 z x h

theorem rule_unique {κ : Rule} (h : IsKF g c κ) (hv : ∀ (z : NgC g) (x : KeyIn ℂ), z.Frame x → κ ℂ x = (kf.val z)⁻¹) :
    κ = kf.rule :=
  h.ext kf.isKF _ hv fun _ _ => kf.rule_frame

@[ext] theorem ext {kf kf' : KF g c} (h : kf.val = kf'.val) : kf = kf' := by
  cases kf; cases kf'; cases h; rfl

theorem rule_injective (hg : 1 ≤ g) : Function.Injective (rule : KF g c → Rule) := fun kf kf' h =>
  ext (funext fun z => by
    obtain ⟨x, hx⟩ := z.exists_frame hg
    exact inv_injective ((kf.rule_frame hx).symm.trans (h ▸ kf'.rule_frame hx)))

def coef (K : Type) [Field K] [CharZero K] (x : KeyIn K) : Kˣ := (kf.rule K x)⁻¹

theorem coef_frame {z : NgC g} {x : KeyIn ℂ} (h : z.Frame x) : kf.coef ℂ x = kf.val z := by
  rw [coef, kf.rule_frame h, inv_inv]

theorem coef_homog (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv')
    (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (hP : P.g = g)
    (ha : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) (hM : ∀ i, IsLieComb (M i) v (v' i)) :
    M.det ^ c * (kf.coef K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) =
      a ^ (2 * c) * kf.coef K ⟨P, hg, rig, hr, th, hth, v, hv⟩ := by
  have e := kf.isKF.homog K P hg rig hr th hth v hv th' hth' v' hv' a M hP ha hM
  simp only [coef, Units.val_inv_eq_inv_val]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), e]

theorem coef_funct {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') {x : KeyIn K}
    {x' : KeyIn K'} (h : KeyPB x' x f) : (kf.coef K' x' : K') = f (kf.coef K x) := by
  simp only [coef, Units.val_inv_eq_inv_val, map_inv₀, kf.isKF.funct K K' f x x' h]

theorem exists_unit_coef (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [CharZero S]
    (y : KeyIn S) : ∃ u : Sˣ, IsValue kf.coef y (u : S) := by
  obtain ⟨u, hu⟩ := kf.isKF.famUnit S y
  refine ⟨u⁻¹, fun K _ _ f x hx => ?_⟩
  rw [coef, Units.val_inv_eq_inv_val, hu K f x hx]
  exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])

theorem valUnit_coef : ValUnit kf.coef := fun S V K _ _ _ _ _ _ _ _ _ f y x hx => by
  obtain ⟨u, hu⟩ := kf.isKF.valUnit S V K f y x hx
  refine ⟨u⁻¹, ?_⟩
  rw [coef, Units.val_inv_eq_inv_val, hu]
  exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])

def norm (z : NgC g) : ℝ := ‖(kf.val z : ℂ)‖ / (z.thetaSq ^ c * Real.sqrt z.etaSq ^ c)

theorem norm_pos (z : NgC g) : 0 < kf.norm z := by
  have := z.thetaSq_pos
  have := z.etaSq_pos
  exact div_pos (norm_pos_iff.2 (kf.val z).ne_zero) (by positivity)

theorem norm_eq_div (z : NgC g) : kf.norm z = ‖(kf.val z : ℂ)‖ / Real.sqrt ((2 * Real.pi) ^ g) ^ c := by
  rw [norm, ← mul_pow, z.thetaSq_mul_sqrt_etaSq]

theorem norm_eq (z : NgC g) :
    kf.norm z = ‖(kf.val z : ℂ)‖ * Real.exp (c * g * (-(1 / 2) * Real.log (2 * Real.pi))) := by
  have hp : 0 < 2 * Real.pi := by have := Real.pi_pos; positivity
  rw [norm_eq_div, div_eq_mul_inv]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_mul hp.le,
    ← Real.rpow_neg hp.le, Real.rpow_def_of_pos hp]
  congr 1
  ring

theorem norm_eq_of_isArchNorm {z : NgC g} {x : KeyIn ℂ} (hz : z.Lies x) {nth nη : ℝ} (hn : IsArchNorm x nth nη) :
    kf.norm z = ‖(kf.coef ℂ x : ℂ)‖ / (nth ^ c * Real.sqrt nη ^ c) := by
  obtain ⟨hx, M, c₀, hc, hN⟩ := hz
  subst hx
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hn
  obtain ⟨u', τ', M', a', b', c', k₁, k₂, ha, hb, k₃, k₄, hc', k₅, hM', k₆, e⟩ :=
    keyIn_normal_form_and_archimedean_constant thetaUnifAV_all x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have p₁ : 0 ≤ nth := h₆ ▸ div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
  have p₂ : 0 ≤ nη := h₇ ▸ by positivity
  have hv : M.det ^ 4 / c₀ ^ 8 = M'.det ^ 4 / c' ^ 8 :=
    NormalUnique.thetaFrame_value_unique thetaUnifAV_all ThetaInversion.inversion x _ _
      ⟨z.τ, M, z.a, z.b, c₀, z.half, hc, hN, rfl⟩ ⟨τ', M', a', b', c', ⟨ha, hb⟩, hc', ⟨u', k₁, k₂, k₃, k₄, k₅, k₆⟩, rfl⟩
  have hM : M.det ≠ 0 := fun h0 => by
    rw [h0] at hv
    exact div_ne_zero (pow_ne_zero 4 hM') (pow_ne_zero 8 hc') (by rw [← hv]; simp)
  have hκ := kf.isKF.value_normalAt x rfl hc hM hN ((kf.val z)⁻¹ : ℂˣ)
    fun w e hw => congrArg Units.val (kf.rule_frame ⟨e, hw⟩)
  rw [← hv, norm_div, norm_pow, norm_pow] at e
  have q₁ : 0 < ‖M.det‖ := norm_pos_iff.2 hM
  have q₂ : 0 < ‖c₀‖ := norm_pos_iff.2 hc
  have hp := Real.pi_pos
  have e' : ‖M.det‖ / ‖c₀‖ ^ 2 * (nth * Real.sqrt nη) = Real.sqrt ((2 * Real.pi) ^ x.P.g) := by
    refine (pow_left_inj₀ (by positivity) (by positivity) (show 4 ≠ 0 by norm_num)).1 ?_
    have s : ∀ t : ℝ, 0 ≤ t → Real.sqrt t ^ 4 = t ^ 2 := fun t ht => by
      rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ht]
    rw [mul_pow, mul_pow, s _ p₂, s _ (by positivity), ← pow_mul, mul_comm x.P.g 2, ← e, div_pow, ← pow_mul,
      _root_.mul_assoc]
  have hκ' := congrArg (‖·‖) hκ
  simp only [norm_mul, norm_pow, Units.val_inv_eq_inv_val, norm_inv] at hκ'
  have q₃ : 0 < ‖(kf.val z : ℂ)‖ := norm_pos_iff.2 (kf.val z).ne_zero
  have q₄ : 0 < ‖(kf.rule ℂ x : ℂ)‖ := norm_pos_iff.2 (kf.rule ℂ x).ne_zero
  have e₂ : ‖(kf.coef ℂ x : ℂ)‖ = ‖(kf.val z : ℂ)‖ / (‖M.det‖ / ‖c₀‖ ^ 2) ^ c := by
    rw [coef, Units.val_inv_eq_inv_val, norm_inv, div_pow, ← pow_mul]
    field_simp at hκ' ⊢
    linarith
  rw [norm_eq_div, ← e', e₂, div_div, ← mul_pow, ← mul_pow]

def sign (s : ℤˣ) : KF g c where
  val z := Units.map (Int.castRingHom ℂ).toMonoidHom s * kf.val z
  ex := ⟨cutRule g s kf.rule, isKF_cutRule s kf.isKF.homog kf.isKF.funct kf.isKF.unitSp, fun z x h => by
    rw [cutRule, if_pos h.1, kf.rule_frame h]
    rcases Int.units_eq_one_or s with rfl | rfl <;> ext <;> simp⟩
  zero h z := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases kf.zero h z with e | e <;> rw [e] <;>
      [left; right; right; left] <;> ext <;> simp

theorem sign_neg_one_ne : kf.sign (-1) ≠ kf := fun h => by
  obtain ⟨z⟩ : Nonempty (NgC g) := inferInstance
  have e : (-1 : ℂ) * kf.val z = kf.val z := by simpa [sign] using congrArg (fun k : KF g c => (k.val z : ℂ)) h
  exact (kf.val z).ne_zero (by linear_combination (-1 / 2 : ℂ) * e)

def ofRule (N : ℕ → ℕ) (κ : Rule) (hH : Homog N κ) (hF : Funct κ) (hU : UnitSp κ) (hT : ThetaOne κ) (g : ℕ) :
    KF g (4 * N g) where
  val _ := 1
  ex := ⟨cutRule g 1 κ, isKF_cutRule 1 (fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂ => by
      subst hP
      rw [show 2 * (4 * N P.g) = 8 * N P.g by ring]
      exact hH K P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂) hF hU, fun z x h => by
    obtain ⟨e, h⟩ := h
    obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (normalAt_one_iff x _ _ _).1 h
    rw [cutRule, if_pos e, hT x u _ _ _ h₁ h₂ (fun i => z.half.1 _) (fun i => z.half.2 _) h₃ h₄ h₅ h₆]
    simp⟩
  zero _ _ := Or.inl rfl

theorem exists_rule_eq (hg : 1 ≤ g)
    (H : ∀ (z : NgC g) (x x' : KeyIn ℂ), z.Frame x → z.Frame x' → KeyPB x' x (RingHom.id ℂ))
    {κ : Rule} (h : IsKF g c κ) : ∃ kf : KF g c, kf.rule = κ := by
  choose x hx using fun z : NgC g => z.exists_frame hg
  have hv : ∀ (z : NgC g) (y : KeyIn ℂ), z.Frame y → κ ℂ y = ((κ ℂ (x z))⁻¹)⁻¹ := fun z y hy => by
    rw [inv_inv]
    exact Units.ext (h.funct ℂ ℂ _ _ _ (H z _ _ (hx z) hy))
  exact ⟨⟨fun z => (κ ℂ (x z))⁻¹, ⟨κ, h, hv⟩, fun h0 => by omega⟩, (rule_unique _ h hv).symm⟩

end KF

def ngTrue : Formalism.L2.Geo.NgPkg where
  NgC := NgC
  NgC_ne _ := inferInstance
  KF := KF
  kfNorm kf z := kf.norm z

theorem ngTrue_NgC (g : ℕ) : ngTrue.NgC g = NgC g := rfl

theorem ngTrue_KF (g c : ℕ) : ngTrue.KF g c = KF g c := rfl

theorem ngTrue_kfNorm {g c : ℕ} (kf : KF g c) (z : NgC g) : ngTrue.kfNorm (g := g) (c := c) kf z = kf.norm z := rfl

theorem exists_kf_four (g : ℕ) : ∃ kf : KF g 4, ∀ z, kf.val z = 1 := by
  obtain ⟨κ, h₁, h₂, h₃, h₄, -⟩ := keyFormula_iff.1 keyFormula_and_keyCore.1
  exact ⟨KF.ofRule (fun _ => 1) κ h₁ h₂ h₃ h₄ g, fun _ => rfl⟩

theorem ngTrue_keyFormula (g : ℕ) : ∃ c : ℕ, 1 ≤ c ∧ 4 ∣ c ∧ ∃ kf : ngTrue.KF g c,
    ∀ z, ngTrue.kfNorm kf z = Real.exp (c * g * (-(1 / 2) * Real.log (2 * Real.pi))) := by
  obtain ⟨kf, h⟩ := exists_kf_four g
  refine ⟨4, by norm_num, dvd_rfl, kf, fun z => (kf.norm_eq z).trans ?_⟩
  rw [h z, Units.val_one, norm_one, _root_.one_mul]

example : NgC.base 1 0 0 ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩ ≠
    NgC.base 1 (fun _ => 1 / 2) (fun _ => 1 / 2) ⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl⟩ := fun h => by
  simpa [NgC.base] using congrFun (congrArg NgC.a h) 0

example (a b : Fin 1 → ℂ) (h : charHalf 1 a b) : (NgC.base 1 a b h).etaSq = 4 * Real.pi := by
  simp [NgC.etaSq_eq, NgC.Y, NgC.base]

example (g : ℕ) : ∃ kf kf' : KF g 4, kf ≠ kf' ∧ ∀ z, kf.norm z = ((2 * Real.pi) ^ (2 * g))⁻¹ := by
  obtain ⟨kf, h⟩ := exists_kf_four g
  refine ⟨kf, kf.sign (-1), kf.sign_neg_one_ne.symm, fun z => ?_⟩
  have := Real.pi_pos
  rw [kf.norm_eq_div, h z, Units.val_one, norm_one, one_div, show 4 = 2 * 2 from rfl, pow_mul,
    Real.sq_sqrt (by positivity), ← pow_mul, mul_comm g 2]

end GlobalTheory.LocM
end
