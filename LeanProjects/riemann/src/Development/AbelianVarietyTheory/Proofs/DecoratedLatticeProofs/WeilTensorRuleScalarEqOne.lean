import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepOrthogonalSumEqUnitSmulProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionalInvarianceProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.TensorScalarOne
variable {D : D7}

theorem exists_theta_ne_zero_at_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) :
    ∃ f, IsThetaFunO ψ S T f ∧ f 0 ≠ 0 := by
  obtain ⟨f, hf, hf0⟩ := ((GlobalTheory.ThetaAllChar.thetaFacts D).std hψ S T).2.2.2
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hf0
  refine ⟨heisO ψ S T w f, (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 w f hf, ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero.heisO_apply_zero]; exact hw

theorem om_inv_apply {S T : HSp D} (om : Om S T) (p : GA D S × GA D T) (f : WO S T → ℂ) : om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

def ProdLaw (ψ : AddChar (AF D.host.F) ℂ) {S A B T : HSp D} (o : OrthDec S A B) (omS : Om S T) (omA : Om A T)
    (omB : Om B T) (a : GA D A) (b : GA D B) (h : GA D T) (c : ℂ) : Prop :=
  ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB →
    omS (o.emb (a, b), h) (o.boxS T fA fB) = c • o.boxS T (omA (a, h) fA) (omB (b, h) fB)

variable {ψ : AddChar (AF D.host.F) ℂ} {S A B T : HSp D} (o : OrthDec S A B) (omS : Om S T) (omA : Om A T)
    (omB : Om B T)

theorem boxS_resS_symm (fA : WO A T → ℂ) (fB : WO B T → ℂ) (u : WO A T) (v : WO B T) :
    o.boxS T fA fB ((o.resS T).symm (u, v)) = fA u * fB v := by
  simp only [OrthDec.boxS, AddEquiv.apply_symm_apply]

theorem prodLaw_of (a : GA D A) (b : GA D B) (h : GA D T) (c : ℂ)
    (H : ∀ f, IsThetaFunO ψ S T f → ∀ u v, omS (o.emb (a, b), h) f ((o.resS T).symm (u, v)) =
      c * omA (a, h) (fun u' => omB (b, h) (fun v' => f ((o.resS T).symm (u', v'))) v) u) :
    ProdLaw ψ o omS omA omB a b h c := by
  intro fA fB hA hB
  funext w
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective w
  rw [H _ (o.isThetaFunO_boxS hA hB) u v]
  have e1 : ∀ u', (fun v' => o.boxS T fA fB ((o.resS T).symm (u', v'))) = fA u' • fB := by
    intro u'; funext v'; simp [boxS_resS_symm]
  simp_rw [e1, LinearMap.map_smul]
  have e2 : (fun u' => (fA u' • omB (b, h) fB) v) = (omB (b, h) fB v) • fA := by
    funext u'; simp [mul_comm]
  rw [e2, LinearMap.map_smul]
  simp only [Pi.smul_apply, boxS_resS_symm, smul_eq_mul]; ring

end GlobalTheory.TensorScalarOne

namespace GlobalTheory.TensorScalarOne
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S A B T : HSp D} {o : OrthDec S A B} {omS : Om S T} {omA : Om A T}
    {omB : Om B T} {χA χB χT : (AE D)ˣ →* Circle}

theorem prodLaw_unique (hψ : IsStdChar D ψ (-1)) (hA : IsWeilDatumO ψ A T χA χT omA)
    (hB : IsWeilDatumO ψ B T χB χT omB) {a : GA D A} {b : GA D B} {h : GA D T} {c c' : ℂ}
    (h1 : ProdLaw ψ o omS omA omB a b h c) (h2 : ProdLaw ψ o omS omA omB a b h c') : c = c' := by
  obtain ⟨fA, hfA, hfA0⟩ := exists_theta_ne_zero_at_zero hψ A T
  obtain ⟨fB, hfB, hfB0⟩ := exists_theta_ne_zero_at_zero hψ B T
  have tA := hA.om_pres (a, h)⁻¹ fA hfA
  have tB := hB.om_pres (b, h)⁻¹ fB hfB
  have e := congrFun ((h1 _ _ tA tB).symm.trans (h2 _ _ tA tB)) 0
  simp only [Pi.smul_apply, om_inv_apply, OrthDec.boxS_zero, smul_eq_mul] at e
  exact mul_right_cancel₀ (mul_ne_zero hfA0 hfB0) e

theorem prodLaw_mul (hA : IsWeilDatumO ψ A T χA χT omA) (hB : IsWeilDatumO ψ B T χB χT omB)
    {a a' : GA D A} {b b' : GA D B} {h h' : GA D T} {c c' : ℂ}
    (h1 : ProdLaw ψ o omS omA omB a b h c) (h2 : ProdLaw ψ o omS omA omB a' b' h' c') :
    ProdLaw ψ o omS omA omB (a * a') (b * b') (h * h') (c * c') := by
  intro fA fB hfA hfB
  have eS : ((o.emb (a * a', b * b'), h * h') : GA D S × GA D T) = (o.emb (a, b), h) * (o.emb (a', b'), h') := by
    rw [Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk]
  have eA : ((a * a', h * h') : GA D A × GA D T) = (a, h) * (a', h') := rfl
  have eB : ((b * b', h * h') : GA D B × GA D T) = (b, h) * (b', h') := rfl
  rw [eS, eA, eB, map_mul omS, map_mul omA, map_mul omB, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.mul_apply, h2 fA fB hfA hfB, LinearMap.map_smul, h1 _ _ (hA.om_pres _ fA hfA) (hB.om_pres _ fB hfB),
    smul_smul, mul_comm c' c]

theorem prodLaw_rat (hψ : IsStdChar D ψ (-1)) (hS : IsWeilDatumO ψ S T (χA * χB) χT omS)
    (hA : IsWeilDatumO ψ A T χA χT omA) (hB : IsWeilDatumO ψ B T χB χT omB) {a : GA D A} {b : GA D B} {h : GA D T}
    (ha : a ∈ GQ A) (hb : b ∈ GQ B) (hh : h ∈ GQ T) {c : ℂ} (H : ProdLaw ψ o omS omA omB a b h c) : c = 1 := by
  obtain ⟨fA, hfA, hfA0⟩ := exists_theta_ne_zero_at_zero hψ A T
  obtain ⟨fB, hfB, hfB0⟩ := exists_theta_ne_zero_at_zero hψ B T
  have e := congrFun (H fA fB hfA hfB) 0
  rw [hS.om_aut _ (o.emb_mem_GQ ha hb) h hh _ (o.isThetaFunO_boxS hfA hfB)] at e
  simp only [Pi.smul_apply, OrthDec.boxS_zero, smul_eq_mul, hA.om_aut a ha h hh fA hfA,
    hB.om_aut b hb h hh fB hfB] at e
  have e' : (1 : ℂ) * (fA 0 * fB 0) = c * (fA 0 * fB 0) := by rw [one_mul]; exact e
  exact (mul_right_cancel₀ (mul_ne_zero hfA0 hfB0) e').symm

theorem prodLaw_cont (hψ : IsStdChar D ψ (-1)) (hS : IsWeilDatumO ψ S T (χA * χB) χT omS)
    (hA : IsWeilDatumO ψ A T χA χT omA) (hB : IsWeilDatumO ψ B T χB χT omB) (c : GA D A × GA D B × GA D T → ℂ)
    (hc : ∀ a b h, ProdLaw ψ o omS omA omB a b h (c (a, b, h))) : Continuous c := by
  obtain ⟨fA, hfA, hfA0⟩ := exists_theta_ne_zero_at_zero hψ A T
  obtain ⟨fB, hfB, hfB0⟩ := exists_theta_ne_zero_at_zero hψ B T
  rw [continuous_iff_continuousAt]
  rintro ⟨a₀, b₀, h₀⟩
  set gA := omA (a₀, h₀)⁻¹ fA with hgA
  set gB := omB (b₀, h₀)⁻¹ fB with hgB
  have tA : IsThetaFunO ψ A T gA := hA.om_pres _ fA hfA
  have tB : IsThetaFunO ψ B T gB := hB.om_pres _ fB hfB
  let den : GA D A × GA D B × GA D T → ℂ := fun p => omA (p.1, p.2.2) gA 0 * omB (p.2.1, p.2.2) gB 0
  let num : GA D A × GA D B × GA D T → ℂ := fun p => omS (o.emb (p.1, p.2.1), p.2.2) (o.boxS T gA gB) 0
  have hden : Continuous den :=
    ((hA.om_cont gA tA 0).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).mul
      ((hB.om_cont gB tB 0).comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))
  have hnum : Continuous num :=
    (hS.om_cont _ (o.isThetaFunO_boxS tA tB) 0).comp
      ((o.continuous_emb.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))
  have hd0 : den (a₀, b₀, h₀) ≠ 0 := by
    simp only [den, hgA, hgB, om_inv_apply]; exact mul_ne_zero hfA0 hfB0
  have hnd : ∀ p, num p = c p * den p := by
    rintro ⟨a, b, h⟩
    have := congrFun (hc a b h gA gB tA tB) 0
    simp only [Pi.smul_apply, OrthDec.boxS_zero, smul_eq_mul] at this
    exact this
  have hev : (fun p => num p / den p) =ᶠ[nhds (a₀, b₀, h₀)] c := by
    filter_upwards [hden.continuousAt.eventually_ne hd0] with p hp
    rw [hnd p]; field_simp
  exact (hnum.continuousAt.div hden.continuousAt hd0).congr hev

theorem circ_cont {X : Type*} [TopologicalSpace X] {f : X → Circle} (hf : Continuous fun x => (f x : ℂ)) :
    Continuous f := by
  first
  | exact continuous_induced_rng.2 hf
  | exact Circle.isEmbedding_coe.continuous_iff.2 hf

end GlobalTheory.TensorScalarOne

namespace GlobalTheory.TensorScalarOne

theorem det_emb {D : D7} {S A B : HSp D} (o : OrthDec S A B) (a : GA D A) (b : GA D B) :
    (Formalism.L2.Theta.mt S (o.emb (a, b))).det = (Formalism.L2.Theta.mt A a).det * (Formalism.L2.Theta.mt B b).det := by
  have hPQ : Matrix.fromCols o.jA o.jB ⬝ Matrix.fromRows o.pA o.pB = 1 := by
    rw [Matrix.fromCols_mul_fromRows]; exact o.sum_eq_one
  have hQP : Matrix.fromRows o.pA o.pB ⬝ Matrix.fromCols o.jA o.jB = 1 := by
    rw [Matrix.fromRows_mul_fromCols, o.pA_jA, o.pA_jB, o.pB_jA, o.pB_jB, Matrix.fromBlocks_one]
  have key : Matrix.fromRows o.pA o.pB ⬝ (Formalism.L2.Theta.mt S (o.emb (a, b)) ⬝ Matrix.fromCols o.jA o.jB) =
      Matrix.fromBlocks (Formalism.L2.Theta.mt A a) 0 0 (Formalism.L2.Theta.mt B b) := by
    rw [← Matrix.mul_assoc, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, o.pA_emb, o.pB_emb,
      Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, o.pA_jA, o.pA_jB, o.pB_jA, o.pB_jB]
    simp
  have h := Matrix.det_comm' hQP hPQ (N := Formalism.L2.Theta.mt S (o.emb (a, b)) ⬝ Matrix.fromCols o.jA o.jB)
  rw [key, Matrix.mul_assoc, hPQ, Matrix.mul_one, Matrix.det_fromBlocks_zero₂₁] at h
  exact h.symm

theorem suppAt_emb {D : D7} {S A B : HSp D} (o : OrthDec S A B) (e : AE D) {a : GA D A} {b : GA D B}
    (ha : SuppAt e A a) (hb : SuppAt e B b) : SuppAt e S (o.emb (a, b)) := by
  have key : ∀ {n : ℕ} (N : Matrix (Fin n) (Fin n) (AE D)),
      (∀ i j, (e + cA D e) * N i j = N i j) ↔ (e + cA D e) • N = N := by
    intro n N; constructor
    · intro h; ext i j; rw [Matrix.smul_apply, smul_eq_mul, h]
    · intro h i j; have := congrFun (congrFun h i) j; rwa [Matrix.smul_apply, smul_eq_mul] at this
  have hM : Formalism.L2.Theta.mt S (o.emb (a, b)) - 1 =
      o.jA ⬝ (Formalism.L2.Theta.mt A a - 1) ⬝ o.pA + o.jB ⬝ (Formalism.L2.Theta.mt B b - 1) ⬝ o.pB := by
    rw [o.mt_emb]
    conv_lhs => rw [← o.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  unfold SuppAt at ha hb ⊢
  rw [key] at ha hb ⊢
  rw [hM, smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, ha, ← Matrix.smul_mul, ← Matrix.mul_smul, hb]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S A B T : HSp D} {o : OrthDec S A B} {omS : Om S T} {omA : Om A T}
    {omB : Om B T} {χA χB χT : (AE D)ˣ →* Circle}

theorem prodLaw_split (hS : IsWeilDatumO ψ S T (χA * χB) χT omS)
    (hA : IsWeilDatumO ψ A T χA χT omA) (hB : IsWeilDatumO ψ B T χB χT omB) (e : AE D) (he : IsSplitIdem D e)
    {a : GA D A} {b : GA D B} {h : GA D T} (ha : SuppAt e A a) (hb : SuppAt e B b) (hh : SuppAt e T h) {c : ℂ}
    (hc1 : ‖c‖ = 1) (H : ProdLaw ψ o omS omA omB a b h c) : c = 1 := by
  have hψ := hS.std
  have he1 : e * e = e := he.1
  obtain ⟨ℓA, hℓA, fA, hfA, hℓfA⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ hψ A T e he
  obtain ⟨ℓB, hℓB, fB, hfB, hℓfB⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ hψ B T e he
  obtain ⟨ℓ, hℓ, hbox⟩ := GlobalTheory.T.theta_functional_invariance_product D ψ hψ S A B T o e he ℓA ℓB hℓA hℓB
  have dA := GlobalTheory.VecInv.isDetAt_detAt e he1 A a
  have dB := GlobalTheory.VecInv.isDetAt_detAt e he1 B b
  have dT := GlobalTheory.VecInv.isDetAt_detAt e he1 T h
  set xA := GlobalTheory.VecInv.detAt e he1 A a
  set xB := GlobalTheory.VecInv.detAt e he1 B b
  set y := GlobalTheory.VecInv.detAt e he1 T h
  have dS : IsDetAt e S (o.emb (a, b)) (xA * xB) := by
    unfold IsDetAt at dA dB ⊢
    rw [Units.val_mul, dA, dB, det_emb]
    linear_combination ((Formalism.L2.Theta.mt A a).det * (Formalism.L2.Theta.mt B b).det - (Formalism.L2.Theta.mt A a).det
      - (Formalism.L2.Theta.mt B b).det + 1) * he1
  obtain ⟨rS, hrS, HS⟩ := hS.om_split e he (o.emb (a, b)) h (suppAt_emb o e ha hb) hh (xA * xB) y dS dT
  obtain ⟨rA, hrA, HA⟩ := hA.om_split e he a h ha hh xA y dA dT
  obtain ⟨rB, hrB, HB⟩ := hB.om_split e he b h hb hh xB y dB dT
  have k1 := HS ℓ hℓ _ (o.isThetaFunO_boxS hfA hfB)
  rw [H fA fB hfA hfB, LinearMap.map_smul, hbox _ _ (hA.om_pres _ _ hfA) (hB.om_pres _ _ hfB),
    HA ℓA hℓA fA hfA, HB ℓB hℓB fB hfB, hbox fA fB hfA hfB, smul_eq_mul] at k1
  have hfac : splitFacO (χA * χB) χT (xA * xB) y = splitFacO χA χT xA y * splitFacO χB χT xB y := by
    simp only [splitFacO, map_mul, MonoidHom.mul_apply, mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  rw [hfac, Circle.coe_mul] at k1
  have hZ : (splitFacO χA χT xA y : ℂ) * (splitFacO χB χT xB y : ℂ) * (ℓA fA * ℓB fB) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)) (mul_ne_zero hℓfA hℓfB)
  have key : c * ((rA : ℂ) * rB) = rS := by
    apply mul_right_cancel₀ hZ
    linear_combination k1
  have hrA0 : (rA : ℂ) ≠ 0 := by exact_mod_cast hrA.ne'
  have hrB0 : (rB : ℂ) ≠ 0 := by exact_mod_cast hrB.ne'
  have hc' : c = ((rS / (rA * rB) : ℝ) : ℂ) := by
    push_cast; field_simp; linear_combination key
  rw [hc'] at hc1 ⊢
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hc1
  rw [hc1]; simp

end GlobalTheory.TensorScalarOne

namespace GlobalTheory.TensorScalarOne

theorem suppAt_one {D : D7} (U : HSp D) (e : AE D) : SuppAt e U (1 : GA D U) := by
  intro i j; simp [GlobalTheory.AdelicLatMove.mt_one]

theorem tensor_scalar_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χA χB χT : (AE D)ˣ →* Circle) (omS : Om S T) (omA : Om A T) (omB : Om B T), IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB → ∀ a b h f, IsThetaFunO ψ S T f → ∀ u v, omS (o.emb (a, b), h) f ((o.resS T).symm (u, v)) = omA (a, h) (fun u' => omB (b, h) (fun v' => f ((o.resS T).symm (u', v'))) v) u := by
  intro D ψ S A B T o χA χB χT omS omA omB hS hA hB
  have hψ := hS.std
  choose C hC using GlobalTheory.T.weilRep_orthogonal_sum_eq_unit_smul_product D ψ S A B T o χA χB χT omS omA omB hS hA hB
  have law : ∀ a b h, ProdLaw ψ o omS omA omB a b h (C a b h) := fun a b h =>
    prodLaw_of o omS omA omB a b h _ (hC a b h)
  have cmul : ∀ a a' b b' h h', (C (a * a') (b * b') (h * h') : ℂ) = C a b h * C a' b' h' := fun a a' b b' h h' =>
    prodLaw_unique hψ hA hB (law _ _ _) (prodLaw_mul hA hB (law a b h) (law a' b' h'))
  have ccont : Continuous fun p : GA D A × GA D B × GA D T => (C p.1 p.2.1 p.2.2 : ℂ) :=
    prodLaw_cont hψ hS hA hB _ fun a b h => law a b h
  have crat : ∀ a ∈ GQ A, ∀ b ∈ GQ B, ∀ h ∈ GQ T, C a b h = 1 := fun a ha b hb h hh =>
    Circle.ext (by rw [Circle.coe_one]; exact prodLaw_rat hψ hS hA hB ha hb hh (law a b h))
  have csplit : ∀ e, IsSplitIdem D e → ∀ a b h, SuppAt e A a → SuppAt e B b → SuppAt e T h → C a b h = 1 :=
    fun e he a b h ha hb hh => Circle.ext (by
      rw [Circle.coe_one]; exact prodLaw_split hS hA hB e he ha hb hh (Circle.norm_coe _) (law a b h))
  have c1 : C 1 1 1 = 1 := crat 1 (one_mem _) 1 (one_mem _) 1 (one_mem _)
  let νA : GA D A →* Circle :=
    { toFun := fun a => C a 1 1, map_one' := c1,
      map_mul' := fun a a' => Circle.ext (by simpa using cmul a a' 1 1 1 1) }
  let νB : GA D B →* Circle :=
    { toFun := fun b => C 1 b 1, map_one' := c1,
      map_mul' := fun b b' => Circle.ext (by simpa using cmul 1 1 b b' 1 1) }
  let νT : GA D T →* Circle :=
    { toFun := fun h => C 1 1 h, map_one' := c1,
      map_mul' := fun h h' => Circle.ext (by simpa using cmul 1 1 1 1 h h') }
  have hνA : ∀ a, C a 1 1 = 1 := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D A νA
    (circ_cont (f := νA) (by exact ccont.comp (continuous_id.prodMk (continuous_const (y := ((1 : GA D B), (1 : GA D T)))))))
    (fun γ hγ => crat γ hγ 1 (one_mem _) 1 (one_mem _))
    (fun e he g hg => csplit e he g 1 1 hg (suppAt_one B e) (suppAt_one T e))
  have hνB : ∀ b, C 1 b 1 = 1 := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D B νB
    (circ_cont (f := νB) (by exact ccont.comp ((continuous_const (y := (1 : GA D A))).prodMk (continuous_id.prodMk (continuous_const (y := (1 : GA D T)))))))
    (fun γ hγ => crat 1 (one_mem _) γ hγ 1 (one_mem _))
    (fun e he g hg => csplit e he 1 g 1 (suppAt_one A e) hg (suppAt_one T e))
  have hνT : ∀ h, C 1 1 h = 1 := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D T νT
    (circ_cont (f := νT) (by exact ccont.comp ((continuous_const (y := (1 : GA D A))).prodMk ((continuous_const (y := (1 : GA D B))).prodMk continuous_id))))
    (fun γ hγ => crat 1 (one_mem _) 1 (one_mem _) γ hγ)
    (fun e he g hg => csplit e he 1 1 g (suppAt_one A e) (suppAt_one B e) hg)
  have hall : ∀ a b h, (C a b h : ℂ) = 1 := by
    intro a b h
    have e1 := cmul a 1 1 b 1 1
    have e2 := cmul a 1 b 1 1 h
    simp only [mul_one, one_mul] at e1 e2
    rw [e2, e1, hνA, hνB, hνT]; simp
  intro a b h f hf u v
  rw [hC a b h f hf u v, hall, one_mul]

end GlobalTheory.TensorScalarOne

end
