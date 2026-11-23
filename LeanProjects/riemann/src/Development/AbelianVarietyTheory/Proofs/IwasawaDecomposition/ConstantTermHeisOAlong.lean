import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetIntegralMulLeft
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantForStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.OneAddPowOfSq

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift GlobalTheory.OrientedHeis GlobalTheory.HolDict.TransvGroup

namespace GlobalTheory.TransvConst

variable {D : D7} {S T : HSp D} {ξ : Fin T.rank → D.host.E} {ψ : AddChar (AF D.host.F) ℂ}

def row (S T : HSp D) (ξ : Fin T.rank → D.host.E) (y : WO S T) : Fin S.rank → AE D :=
  fun j => ∑ c, ∑ d, incA D (star (ξ c) * T.gram c d) * y d j

theorem along_add (a b : Fin S.rank → AE D) : along S T ξ (a + b) = along S T ξ a + along S T ξ b :=
  Matrix.ext fun _ _ => mul_add _ _ _

theorem along_zero : along S T ξ 0 = 0 := Matrix.ext fun _ _ => mul_zero _

theorem row_along (h : IsoVec T ξ) (a : Fin S.rank → AE D) : row S T ξ (along S T ξ a) = 0 := by
  funext j
  have h1 : ∑ c, ∑ d, star (ξ c) * T.gram c d * ξ d = 0 := by
    rw [← h.2]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rfl
  have h2 := congrArg (fun x => incA D x * a j) h1
  simp only [map_sum, Finset.sum_mul, map_zero, zero_mul] at h2
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_) h2
  rw [RingHom.map_mul _ _ (ξ d), mul_assoc]
  rfl

theorem hO_along (a : Fin S.rank → AE D) (y : WO S T) :
    hO S T (along S T ξ a) y = ∑ i, ∑ j, incA D (S.gram⁻¹ i j) * cA D (row S T ξ y j) * a i := by
  unfold hO row
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [RingHom.map_mul (cA D), GlobalTheory.DualPairCheck.cA_incA, star_mul', star_star, GlobalTheory.DualPairCheck.gram_star, RingHom.map_mul]
  change _ * (incA D (ξ c) * a i) = _
  ring

theorem symplO_along {y : WO S T} (h : row S T ξ y = 0) (a : Fin S.rank → AE D) : symplO S T (along S T ξ a) y = 0 := by
  simp only [symplO, hO_along, h, Pi.zero_apply, RingHom.map_zero, mul_zero, zero_mul, Finset.sum_const_zero, map_zero]

theorem symplOH_along (h : IsoVec T ξ) (a b : Fin S.rank → AE D) :
    symplOH S T (along S T ξ a) (along S T ξ b) = 0 := by
  rw [symplOH, symplO_along (row_along h b), mul_zero]

theorem actO_transv {z : GA D T} {t : AE D} (hz : (matHom T z).1 = 1 + t • (nilM T ξ).map (incA D)) (y : WO S T) :
    actO S T 1 z y = along S T ξ (t • row S T ξ y) + y := by
  have e : actO S T 1 z y = HMul.hMul (matHom T z).1 y := by
    unfold actO
    rw [inv_one]
    exact Matrix.mul_one _
  rw [e, hz, Matrix.add_mul, Matrix.one_mul, add_comm, Matrix.smul_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  change t * ∑ d, incA D (ξ i * ∑ c, star (ξ c) * T.gram c d) * y d j = incA D (ξ i) * (t * row S T ξ y j)
  rw [row, Finset.sum_comm, mul_left_comm, Finset.mul_sum]
  simp only [RingHom.map_mul _ (ξ i), map_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]

theorem actO_along (h : IsoVec T ξ) {z : GA D T} (hz : z ∈ ZI T ξ) (a : Fin S.rank → AE D) :
    actO S T 1 z (along S T ξ a) = along S T ξ a := by
  obtain ⟨t, -, e⟩ := exists_skew h hz
  rw [actO_transv e, row_along h, smul_zero, along_zero, zero_add]

theorem norm_ne_zero (hS : ∀ τ, (gramAt D S τ).PosDef) {m : Fin S.rank → D.host.E} (hm : m ≠ 0) :
    ∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i ≠ 0 := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hinv : (gramAt D S τ)⁻¹ = (S.gram⁻¹).map (tauE D τ) := Matrix.inv_eq_right_inv (by
    rw [gramAt, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)])
  have hs : ∀ x, tauE D τ (star x) = star (tauE D τ x) := GlobalTheory.FockCompare.tauE_star τ
  have h := (hS τ).inv.dotProduct_mulVec_pos (x := fun i => tauE D τ (star (m i))) fun h0 => hm (funext fun i => by
    have := congrFun h0 i
    simpa using this)
  intro h0
  refine h.ne' ?_
  rw [← (tauE D τ).map_zero, ← h0, hinv]
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, Pi.star_apply, star_star, Matrix.map_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem trace_three (s : AF D.host.F) (a b c : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D a * ((s ⊗ₜ[D.host.F] b : AE D) * incA D c)) =
      s * algebraMap _ _ (Algebra.trace D.host.F D.host.E (a * (b * c))) := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [h2, h2, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, GlobalTheory.LatVac.trace_tmul]

theorem cancel_two {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] (p : R) {q : F} (hq : q ≠ 0) :
    algebraMap F R (1 / 2) * (p * algebraMap F R q⁻¹ * algebraMap F R (2 • q)) = p := by
  rw [mul_left_comm, mul_assoc, ← map_mul, ← map_mul,
    show q⁻¹ * (1 / 2 * (2 • q)) = 1 by rw [nsmul_eq_mul]; push_cast; field_simp, map_one, mul_one]

set_option maxHeartbeats 800000 in

theorem exists_transv (hψ : IsStdChar D ψ (-1)) (hS : ∀ τ, (gramAt D S τ).PosDef) (h : IsoVec T ξ)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hx : row S T ξ (ratW T S x) ≠ 0) :
    ∃ e, IsSplitIdem D e ∧ ∃ z ∈ ZI T ξ, Formalism.L2.Theta.SuppAt e T z ∧ ∃ b, actO S T 1 z (ratW T S x) = along S T ξ b + ratW T S x ∧
      ψ (symplOH S T (along S T ξ b) (ratW T S x)) ≠ 1 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨m, hm⟩ : ∃ m : Fin S.rank → D.host.E, ∀ j, row S T ξ (ratW T S x) j = incA D (m j) :=
    ⟨fun j => ∑ c, ∑ d, star (ξ c) * T.gram c d * x d j, fun j => by
      simp only [map_sum, RingHom.map_mul _ _ (x _ _)]
      rfl⟩
  have hm0 : m ≠ 0 := fun h0 => hx (funext fun j => by rw [hm, h0, Pi.zero_apply, RingHom.map_zero]; rfl)
  have hN := norm_ne_zero hS hm0
  have hNs : star (∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i) = ∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i := by
    simp only [star_sum, star_mul', star_star, gramInv_star]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hh : ∀ t : AE D, hO S T (along S T ξ (t • row S T ξ (ratW T S x))) (ratW T S x) =
      t * incA D (∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i) := fun t => by
    simp only [hO_along, Pi.smul_apply, hm, GlobalTheory.DualPairCheck.cA_incA, map_sum, RingHom.map_mul, Finset.mul_sum, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  generalize ∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i = N at hN hNs hh
  have hx0 := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  obtain ⟨q, hq⟩ := (D.sp.cm.fixed (D.host.xi0 * (D.host.xi0 * N))).1 (by
    rw [star_mul', star_mul', hx0, hNs, neg_mul, neg_mul, mul_neg, neg_neg])
  have hq0 : q ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hq
    exact mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) hN) hq.symm
  obtain ⟨v, hv⟩ := Formalism.L2.G.Triv.exists_place (F := D.host.F) 2 Nat.prime_two
  obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v (by exact_mod_cast hv)
  obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v
  obtain ⟨s, hs1, hs2⟩ : ∃ s : AF D.host.F, pairA D.host.F 0 (singleV D.host.F v 1) * s = s ∧
      ψ (algebraMap D.host.F _ (1 / 2) * (s * algebraMap D.host.F _ (2 • q))) ≠ 1 :=
    ⟨GlobalTheory.SplitIdem.placeHom D.host.F v y * algebraMap D.host.F _ q⁻¹, (mul_assoc _ _ _).symm.trans (congrArg (· * _)
      (((GlobalTheory.SplitIdem.placeHom D.host.F v).map_mul' 1 y).symm.trans (congrArg _ (one_mul y)))),
      by rw [cancel_two _ hq0]; exact hy⟩
  obtain ⟨z, hz⟩ : ∃ z : GA D T, (matHom T z).1 = 1 + (s ⊗ₜ[D.host.F] D.host.xi0 : AE D) • (nilM T ξ).map (incA D) :=
    ⟨tv (AF D.host.F) D.sp.cm.sig (nilM_sq h) (nilM_adj T ξ) _ (skew_tmul _ _ hx0 s), rfl⟩
  refine ⟨e, ⟨e1, e2, v, _, ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ v 1,
    fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ v 1 hw⟩, e3⟩, z,
    Subgroup.subset_closure ⟨_, by rw [hz, add_sub_cancel_left]⟩, fun i j => ?_, _, actO_transv hz _, ?_⟩
  · rw [Formalism.L2.Theta.mt, hz, add_sub_cancel_left, e3, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    congr 1
    change (pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hs1]
  · rw [symplOH, symplO, hh, trace_three,
      ← hq, Algebra.trace_algebraMap, D.sp.cm.deg2]
    exact hs2

theorem heisO_at_zero (w : WO S T) (g : WO S T → ℂ) : heisO ψ S T w g 0 = g w := by
  have h : symplOH S T 0 w = 0 := by
    have := symplOH_add_left (S := S) (T := T) 0 0 w
    rw [add_zero] at this
    exact left_eq_add.1 this
  rw [heisO, h, ψ.map_zero_eq_one, one_mul, zero_add]

theorem heisO_rat {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T) :
    heisO ψ S T (ratW T S x) g w = ψ (symplO S T w (ratW T S x)) * g w := by
  rw [heisO, add_comm, hg.quasi, ← mul_assoc, ← ψ.map_add_eq_mul, symplOH, symplOH, symplO_skew w, mul_neg, neg_neg, ← add_mul,
    ← map_add, add_halves, map_one, one_mul]

theorem symplO_eq_add (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  rw [symplOH, ← add_mul, ← map_add, add_halves, map_one, one_mul]

def alongHom (S T : HSp D) (ξ : Fin T.rank → D.host.E) : (Fin S.rank → AE D) →+ WO S T :=
  AddMonoidHom.mk' (along S T ξ) along_add

theorem continuous_along : Continuous (along S T ξ) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact continuous_pi fun i => continuous_pi fun j => continuous_const.mul (continuous_apply j)

theorem along_injective (h : ξ ≠ 0) : Function.Injective (along S T ξ) := fun a b e => funext fun j => by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have h1 : incA D (ξ i) * a j = incA D (ξ i) * b j := congrFun (congrFun e i) j
  exact ((Ne.isUnit hi).map (incA D)).mul_left_cancel h1

theorem periodic (h : IsoVec T ξ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) {γ : Fin S.rank → AE D}
    (hγ : γ ∈ (ratL T S).comap (alongHom S T ξ)) (y : Fin S.rank → AE D) :
    g (along S T ξ (γ + y)) = g (along S T ξ y) := by
  obtain ⟨x, hx⟩ := hγ
  have hx' : ratW T S x = along S T ξ γ := hx
  have := hg.quasi x (along S T ξ y)
  rwa [hx', symplOH_along h, neg_zero, ψ.map_zero_eq_one, one_mul, ← along_add] at this

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_along (hW : IsWeilDatumO ψ S T χS χT om) (h : IsoVec T ξ) {z : GA D T} (hz : z ∈ ZI T ξ) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) (a : Fin S.rank → AE D) :
    om (1, z) (heisO ψ S T (along S T ξ a) g) 0 = om (1, z) g (along S T ξ a) := by
  rw [hW.om_heis _ _ _ _ hg, actO_along h hz, heisO_at_zero]

theorem om_mul (z z' : GA D T) (g : WO S T → ℂ) : om (1, z * z') g = om (1, z) (om (1, z') g) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

theorem om_rat_along (hW : IsWeilDatumO ψ S T χS χT om) (h : IsoVec T ξ) {γ : GA D T} (hz : γ ∈ ZI T ξ) (hγ : γ ∈ GQ T)
    (z : GA D T) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (a : Fin S.rank → AE D) :
    om (1, γ * z) g (along S T ξ a) = om (1, z) g (along S T ξ a) := by
  have hg' := hW.om_pres (1, z) g hg
  rw [om_mul, ← om_along hW h hz hg', hW.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hg' _),
    heisO_at_zero]

theorem exists_bound (hW : IsWeilDatumO ψ S T χS χT om) (h : IsoVec T ξ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ z : ZI T ξ, ∀ a, ‖om (1, (z : GA D T)) f (along S T ξ a)‖ ≤ C := by
  obtain ⟨θ, hθ⟩ := hW.std.2.1
  obtain ⟨⟨e, he⟩, -⟩ := transvection_group D θ T hθ ξ h
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F
  obtain ⟨C, hC⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hW f hf
    ((fun a => ((1 : GA D S), (e (Multiplicative.ofAdd a) : GA D T))) '' K)
    (hK.image (continuous_const.prodMk (continuous_subtype_val.comp (e.continuous.comp continuous_ofAdd))))
  refine ⟨C, fun z a => ?_⟩
  obtain ⟨s, rfl⟩ := e.surjective z
  obtain ⟨x, hx⟩ := hKx s.toAdd
  have e1 : e s = e (Multiplicative.ofAdd (algebraMap _ _ x)) * e (Multiplicative.ofAdd (s.toAdd - algebraMap _ _ x)) := by
    rw [← map_mul, ← ofAdd_add, add_sub_cancel, ofAdd_toAdd]
  rw [e1, Subgroup.coe_mul, om_rat_along hW h (SetLike.coe_mem _) ((he (Multiplicative.ofAdd (algebraMap _ _ x))).2 ⟨x, rfl⟩) _ hf]
  exact hC _ ⟨_, hx, rfl⟩ _

theorem exists_eigen (hW : IsWeilDatumO ψ S T χS χT om) (hS : ∀ τ, (gramAt D S τ).PosDef) (h : IsoVec T ξ)
    (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (hℓ : ∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hx : row S T ξ (ratW T S x) ≠ 0) :
    ∃ z ∈ ZI T ξ, ∃ c : ℂ, c ≠ 1 ∧ ∀ g, IsThetaFunO ψ S T g →
      ℓ (heisO ψ S T (ratW T S x) (om (1, z) g)) = c * ℓ (heisO ψ S T (ratW T S x) g) := by
  obtain ⟨e, he, z, hz, hs, b, hb, hu⟩ := exists_transv hW.std hS h x hx
  obtain ⟨r, hr, H⟩ := GlobalTheory.T.splitPlaceTransvection_acts_positively_invariant_forms D ψ S T χS χT om hW ξ h e he z hz hs
  refine ⟨z, hz, ψ (symplOH S T (along S T ξ b) (ratW T S x)) * r, fun h1 => hu ?_, fun g hg => ?_⟩
  · have h2 := congrArg norm h1
    rw [norm_mul, hW.std.1.2.1, one_mul, norm_one, Complex.norm_real, Real.norm_of_nonneg hr.le] at h2
    rwa [h2, Complex.ofReal_one, mul_one] at h1
  · rw [mul_assoc, ← H ℓ hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hg _), hW.om_heis _ _ _ _ hg, hb,
      ← hℓ b _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std (hW.om_pres _ _ hg) _), heisO_heisO, map_smul, smul_eq_mul]

set_option maxHeartbeats 800000 in

theorem constantTerm_heisO_along : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ ξ, IsoVec T ξ → ∀ (μ : Measure (ZI T ξ)) (𝓕 : Set (ZI T ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ T).subgroupOf (ZI T ξ)) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ a, ∫ z in 𝓕, om (1, (z : GA D T)) (heisO ψ S T (along S T ξ a) f) 0 ∂μ = ∫ z in 𝓕, om (1, (z : GA D T)) f 0 ∂μ := by
  intro D ψ S T χS χT om hW hS ξ h μ 𝓕 hμ h𝓕 f hf a
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have : BorelSpace (ZI T ξ) := Subtype.borelSpace (ZI T ξ : Set (GA D T))
  have : Countable ((GQ T).subgroupOf (ZI T ξ)) :=
    Function.Injective.countable (f := fun γ : (GQ T).subgroupOf (ZI T ξ) => (⟨γ.1.1, γ.2⟩ : GQ T))
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ T => (x : GA D T)) h))
  obtain ⟨⟨ε, -⟩, -⟩ := transvection_group D θ T hθ ξ h
  have hfin := ((GlobalTheory.TransvMeasure.transvection_measure D θ T hθ ξ h).2.1 μ 𝓕 hμ h𝓕).2
  have hc : ∀ a b : ZI T ξ, a * b = b * a := fun a b => by
    obtain ⟨a, rfl⟩ := ε.surjective a
    obtain ⟨b, rfl⟩ := ε.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  have : LocallyCompactSpace (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : LocallyCompactSpace (AE D) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE D) := e.secondCountableTopology
  have : T2Space (AE D) := e.isEmbedding.t2Space
  letI : MeasurableSpace (Fin S.rank → AE D) := borel _
  have : BorelSpace (Fin S.rank → AE D) := ⟨rfl⟩
  let Γ := (ratL T S).comap (alongHom S T ξ)
  have : DiscreteTopology (ratL T S) := (GlobalTheory.AdelicMatrixLattice.lattice D T S).2.2.2.2.1
  have : DiscreteTopology Γ := DiscreteTopology.of_continuous_injective (β := ratL T S) (f := fun γ => ⟨along S T ξ γ.1, γ.2⟩)
    ((continuous_along.comp continuous_subtype_val).subtype_mk _)
    fun a b e => Subtype.ext (along_injective h.1 (congrArg Subtype.val e))
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F)
  choose c hcK using hx
  have hK' : IsCompact (Set.univ.pi fun _ : Fin S.rank => K) := isCompact_univ_pi fun _ => hK
  have hcov : ∀ y : Fin S.rank → AE D, ∃ γ ∈ Γ, γ + y ∈ Set.univ.pi fun _ : Fin S.rank => K := fun y =>
    ⟨fun j => incA D (c (y j)), ⟨vecMulVec ξ fun j => c (y j), Matrix.ext fun _ _ => RingHom.map_mul (incA D) _ _⟩,
      fun j _ => hcK (y j)⟩
  have : Countable Γ := GlobalTheory.countable_of_discrete_addSubgroup Γ
  obtain ⟨G, -, -, hG⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup Γ
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Fin S.rank → AE D), ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have : IsFiniteMeasure (ν.restrict G) :=
    isFiniteMeasure_restrict.2 (measure_addFundamentalDomain_lt_top_of_cocompact Γ hK' hcov ν (hG ν)).ne
  have hint : ∀ g, IsThetaFunO ψ S T g → Integrable (fun y => g (along S T ξ y)) (ν.restrict G) := fun g hg => by
    obtain ⟨B, hB⟩ := theta_bounded hψ hg
    exact Integrable.of_bound (hg.cont.comp continuous_along).aestronglyMeasurable B (.of_forall fun _ => hB _)
  let N : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := theta_add
      zero_mem' := theta_zero
      smul_mem' := fun a _ hg => theta_smul a hg }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend (p := N) (V' := ℂ)
    { toFun := fun g => ∫ y in G, g.1 (along S T ξ y) ∂ν
      map_add' := fun p q => integral_add (hint _ p.2) (hint _ q.2)
      map_smul' := fun c p => integral_smul c fun y => p.1 (along S T ξ y) }
  replace hℓ : ∀ g, IsThetaFunO ψ S T g → ℓ g = ∫ y in G, g (along S T ξ y) ∂ν := fun g hg =>
    LinearMap.congr_fun hℓ ⟨g, hg⟩
  have hinv : ∀ b g, IsThetaFunO ψ S T g → ℓ (heisO ψ S T (along S T ξ b) g) = ℓ g := fun b g hg => by
    rw [hℓ _ hg, hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg _),
      ← GlobalTheory.AverageConst.setIntegral_add_left add_comm Γ ν (hG ν) (fun y => g (along S T ξ y))
        (fun γ hγ y => periodic h hg hγ y) b]
    refine integral_congr_ae (.of_forall fun y => ?_)
    change ψ (symplOH S T (along S T ξ y) (along S T ξ b)) * g (along S T ξ y + along S T ξ b) = g (along S T ξ (b + y))
    rw [symplOH_along h, ψ.map_zero_eq_one, one_mul, ← along_add, add_comm y]
  obtain ⟨C, hC⟩ := exists_bound hW h hf
  have key := GlobalTheory.AverageConst.average_const Γ hK' hcov
    (fun (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) y => ψ (symplO S T (along S T ξ y) (ratW T S x)))
    (fun x => by
      simp only [symplO_eq_add]
      exact hψ.1.1.comp ((continuous_symplOH continuous_along continuous_const).add
        (continuous_symplOH continuous_along continuous_const)))
    (fun x y y' => by rw [← ψ.map_add_eq_mul, along_add, symplO_eq_add, symplO_eq_add, symplO_eq_add, symplOH_add_left, add_add_add_comm])
    (fun x x' y => by
      rw [← ψ.map_add_eq_mul, show ratW T S (x + x') = ratW T S x + ratW T S x' from Matrix.map_add _ (incA D).map_add _ _,
        symplO_eq_add, symplO_eq_add, symplO_eq_add, symplOH_add_right, add_add_add_comm])
    (fun y => by
      rw [symplO_along (funext fun j => by simp [row, ratW]), ψ.map_zero_eq_one])
    (fun _ _ => hψ.1.2.1 _)
    (fun y => (Iff.intro (fun H _ ⟨x, e⟩ => e ▸ H x) fun H x => H _ ⟨x, rfl⟩).trans
      (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T _))
    ν (hG ν) hc _ μ h𝓕 hfin (fun z y => om (1, (z : GA D T)) f (along S T ξ y))
    (fun y => (hW.om_cont f hf _).comp (continuous_const.prodMk continuous_subtype_val))
    (fun z => (hW.om_pres _ f hf).cont.comp continuous_along) hC
    (fun γ hγ z y => om_rat_along hW h γ.2 hγ _ hf y)
    (fun γ hγ z y => periodic h (hW.om_pres _ f hf) hγ y)
    (fun x => by
      by_cases hx : row S T ξ (ratW T S x) = 0
      · exact Or.inl fun y => by rw [symplO_along hx, ψ.map_zero_eq_one]
      obtain ⟨z₁, hz, c, hc1, H⟩ := exists_eigen hW hS h ℓ hinv x hx
      refine Or.inr ⟨⟨z₁, hz⟩, c, hc1, fun z => ?_⟩
      have h1 := hW.om_pres (1, (z : GA D T)) f hf
      have h2 := hW.om_pres (1, z₁) _ h1
      have := H _ h1
      rw [hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ h1 _), hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ h2 _)] at this
      simpa only [heisO_rat h1, heisO_rat h2, Subgroup.coe_mul, om_mul] using this) a
  simp only [along_zero] at key
  rw [← key]
  exact integral_congr_ae (.of_forall fun z => om_along hW h z.2 hf a)

end GlobalTheory.TransvConst

end
