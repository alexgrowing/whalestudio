import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RatMove

variable {D : D7}

theorem exists_unitary (V : HSp D) (hV : V.gram = 1) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ U : Matrix.unitaryGroup (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = U.1.map (incA D) := by
  obtain ⟨γ', h1, h2⟩ := hγ
  have h3 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ'.1 * V.gram * γ'.1 = V.gram := h1
  rw [hV, Matrix.mul_one] at h3
  exact ⟨⟨γ'.1, Matrix.mem_unitaryGroup_iff'.2 h3⟩, congrArg Units.val h2.symm⟩

def finG (V : HSp D) : GA D V →* GL (Fin V.rank) (EAf D) := (bc (toEAf D)).comp (matHom V)

theorem moves_iff (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    Moves V rfl g N ↔ N = GlobalTheory.NormSum.AdLattice.lat (finG V g) := by
  rw [Submodule.ext_iff]
  refine forall_congr' fun x => iff_congr Iff.rfl ?_
  rw [GlobalTheory.NormSum.AdLattice.mem_lat, ← map_inv]
  rfl

theorem finG_congr (V : HSp D) {g g' : GA D V} (h : finHom V g = finHom V g') : finG V g = finG V g' := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun x : GL (Fin V.rank) _ =>
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (x.1 i j)) h

theorem toEAf_cA (a : AE D) : toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul y e => rfl

theorem sd_lat (V : HSp D) (hV : V.gram = 1) (g : GA D V) :
    Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.NormSum.AdLattice.lat (finG V g)) := by
  have hL := GlobalTheory.NormSum.AdLattice.lat_isLattice (finG V g)
  refine ⟨hL.fg, hL.span_eq_top, GlobalTheory.NormSum.AdLattice.lat_selfDual D.sp.cm.sig _ ?_⟩
  have h : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
  have h2 := congrArg (fun M => M.map (toEAf D)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero (toEAf D)) (map_one _)] at h2
  change cT _ (finG V g).1 * (1 : Matrix _ _ D.host.E).map _ * (finG V g).1 = (1 : Matrix _ _ D.host.E).map _
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, ← h2]
  congr 1
  ext i j
  exact (toEAf_cA _).symm

theorem lat_rat (V : HSp D) {γ : GA D V} (U : Matrix.unitaryGroup (Fin V.rank) D.host.E)
    (hU : Formalism.L2.Theta.mt V γ = U.1.map (incA D)) (g : GA D V) :
    GlobalTheory.NormSum.AdLattice.lat (finG V (γ * g)) = SDLat.smulLat U.1 (GlobalTheory.NormSum.AdLattice.lat (finG V g)) := by
  have key := GlobalTheory.NormSum.AdLattice.mem_lat_rat (finG V γ) (finG V g) U.1 (by
    change (Formalism.L2.Theta.mt V γ).map (toEAf D) = _
    rw [hU]; rfl)
  rw [map_mul]
  ext x
  constructor
  · intro hx
    have e : U.1 *ᵥ (star U.1 *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec]
    exact ⟨_, (key _).2 (e.symm ▸ hx), e⟩
  · rintro ⟨y, hy, rfl⟩
    exact (key y).1 hy

theorem realPt_spec {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    (realPt θ z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (realPt θ z) = z τ := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  refine Classical.epsilon_spec (p := fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ)
    ⟨Matrix.of fun i j => σ fun τ => z τ i j, ?_, fun τ => ?_⟩
  · ext i j; exact hσ.fin _
  · ext i j; exact hσ.comp _ _

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {m n k : ℕ} (x : Mx D m n) (y : Mx D n k) :
    compAt θ τ (HMul.hMul x y : Mx D m k) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (U : Matrix (Fin m) (Fin n) D.host.E) :
    compAt θ τ (U.map (incA D)) = U.map (tauE D τ) := by
  ext i j; exact (hθ τ).1 _

theorem map_unitary (τ : D.what₂.Tau) {n : ℕ} (U : Matrix.unitaryGroup (Fin n) D.host.E) :
    U.1.map (tauE D τ) * (U.1.map (tauE D τ))ᴴ = 1 := by
  have h := congrArg (fun M => M.map (tauE D τ)) U.2.2
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero (tauE D τ)) (map_one _)] at h
  rw [← h]
  congr 1
  ext i j
  exact (GlobalTheory.FockCompare.tauE_star τ _).symm

theorem root_eq {V : HSp D} {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D V} {x x' : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hx' : IsDetRoot V g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem gramAt_one {V : HSp D} (hV : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [hV]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem rat_data {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : V.gram = 1) {r : GA D V} (hr : IsRatFin V r)
    {g : GA D V} (hg : g ∈ GfC V) :
    ∃ γ ∈ GQ V, ∃ k ∈ GinfC V, ∃ U : Matrix.unitaryGroup (Fin V.rank) D.host.E,
      Formalism.L2.Theta.mt V γ = U.1.map (incA D) ∧ γ * g = r * g * k ∧
      (∀ τ, compAt θ τ (Formalism.L2.Theta.mt V k) = U.1.map (tauE D τ)) ∧
      GlobalTheory.NormSum.AdLattice.lat (finG V (r * g)) = SDLat.smulLat U.1 (GlobalTheory.NormSum.AdLattice.lat (finG V g)) ∧
      ∀ (μ : (AE D)ˣ →* Circle) (n : ℕ) (e : D.what₂.Tau → ℤ), IsHeckeChar D μ → ResEta D μ n → Even n →
        (∀ τ, HasInfExp D μ τ (e τ)) → ∀ x x₀, IsDetRoot V (r * g) x → IsDetRoot V g x₀ →
          (μ x₀ : ℂ) = μ x * ∏ τ, tauE D τ U.1.det ^ e τ := by
  obtain ⟨hr, γ, hγ, hf⟩ := hr
  obtain ⟨U, hU⟩ := exists_unitary V hV hγ
  have hk : r⁻¹ * γ ∈ GinfC V := by
    change finHom V _ = 1
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  have e1 : γ * g = r * g * (r⁻¹ * γ) := by
    have := (GlobalTheory.AutMult.commute_inf_fin ⟨_, hk⟩ ⟨_, hg⟩).eq
    dsimp only at this
    rw [mul_assoc r g, ← this, ← mul_assoc, mul_inv_cancel_left]
  have e2 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt V (r⁻¹ * γ)) = U.1.map (tauE D τ) := fun τ => by
    have h1 : infHom V (r⁻¹ * γ) = infHom V γ := by
      rw [map_mul, map_inv, show infHom V r = 1 from hr, inv_one, one_mul]
    rw [← compAt_rat hθ, ← hU]
    exact congrArg (fun x : GL (Fin V.rank) _ => x.1.map (θ τ)) h1
  refine ⟨γ, hγ, _, hk, U, hU, e1, e2, ?_, fun μ n e h1 h2 h3 h4 x x₀ hx hx₀ => ?_⟩
  · rw [← lat_rat V U hU, finG_congr V (g := r * g) (g' := γ * g) (by rw [map_mul, map_mul, hf])]
  · obtain ⟨b, hb⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.2.1 γ hγ
    obtain ⟨y, hy, hv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ V (fun τ => by rw [gramAt_one hV]; simp) _ hk
    have r1 := GlobalTheory.Member.isDetRoot_mul V _ _ _ _ hb hx₀
    have r2 := GlobalTheory.Member.isDetRoot_mul V _ _ _ _ hx hy
    rw [← e1] at r2
    have r3 := root_eq h2 h3 r2 r1
    rw [map_mul, map_mul, h1.2, one_mul] at r3
    rw [r3, Circle.coe_mul, hv μ e h4]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [e2, RingHom.map_det]; rfl

theorem xiN_rat {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om) (δ : ℂ) (sc : ℝ) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T}
    (hγ' : γ' ∈ GQ T) (U : Matrix.unitaryGroup (Fin S.rank) D.host.E) (U' : Matrix.unitaryGroup (Fin T.rank) D.host.E)
    (hU : Formalism.L2.Theta.mt S γ = U.1.map (incA D)) (hU' : Formalism.L2.Theta.mt T γ' = U'.1.map (incA D))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (z : VCx D.what₂.Tau S.rank T.rank) :
    xiN θ S T rfl rfl δ sc (om (γ, γ') f) z = xiN θ S T rfl rfl δ sc f
      fun τ => ((U'.1.map (tauE D τ))ᴴ * Matrix.of (z τ) * U.1.map (tauE D τ) : Matrix _ _ ℂ) := by
  have hrat : ∀ w, om (γ, γ') f (actO S T γ γ' w) = f w := fun w => by
    have h1 := hom.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf w)
    rw [hom.om_heis _ _ _ _ hf] at h1
    simpa [heisO, symplOH, symplO, hO] using h1
  have hi : Formalism.L2.Theta.mt S γ⁻¹ = (star U.1).map (incA D) := by
    have : Formalism.L2.Theta.mt S γ⁻¹ = ((matHom S γ)⁻¹).1 := congrArg Units.val (map_inv (matHom S) γ)
    rw [this]
    refine Units.inv_eq_of_mul_eq_one_left ?_
    change _ * Formalism.L2.Theta.mt S γ = 1
    rw [hU, ← Matrix.map_mul, U.2.1, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  unfold xiN
  congr 1
  · congr 2
    have key : ∀ {m n : ℕ} (y : Matrix (Fin m) (Fin n) ℂ), ∑ i, ∑ j, y i j * starRingEnd ℂ (y i j) = (y * yᴴ).trace :=
      fun y => by simp [Matrix.trace, Matrix.mul_apply]
    change (sc : ℂ) * ∑ τ, _ = (sc : ℂ) * ∑ τ, _
    refine congrArg _ (Finset.sum_congr rfl fun τ _ => ?_)
    refine (key (Matrix.of (z τ))).trans (Eq.trans ?_ (key _).symm)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (U.1.map _), map_unitary, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm _ (U'.1.map _),
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, map_unitary, Matrix.one_mul]
  · rw [← hrat]
    refine congrArg (om (γ, γ') f) ?_
    have s1 := realPt_spec hθ fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast rfl i) (Fin.cast rfl j))
    have s2 := realPt_spec hθ fun τ => Matrix.of fun i j => -(δ⁻¹ *
      ((U'.1.map (tauE D τ))ᴴ * Matrix.of (z τ) * U.1.map (tauE D τ) : Matrix _ _ ℂ) (Fin.cast rfl i) (Fin.cast rfl j))
    generalize realPt θ _ = w₁ at s1 ⊢
    generalize realPt θ _ = w₂ at s2 ⊢
    have t1 : (actO S T γ γ' w₂).map (finPart D) = 0 := by
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, s2.1, Matrix.mul_zero, Matrix.zero_mul]
    have t2 : ∀ τ, compAt θ τ (actO S T γ γ' w₂) = compAt θ τ w₁ := fun τ => by
      unfold actO
      rw [compAt_mul, compAt_mul, s1.2, s2.2, hi, hU', compAt_rat hθ, compAt_rat hθ]
      have a1 : (star U.1).map (tauE D τ) = (U.1.map (tauE D τ))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.tauE_star τ _
      have a2 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ,
          (Matrix.of fun i j => -(δ⁻¹ * y (Fin.cast rfl i) (Fin.cast rfl j))) = (-δ⁻¹) • y := fun y => by
        ext i j; simp
      rw [a1, a2]
      refine Eq.trans ?_ (a2 (Matrix.of (z τ))).symm
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, map_unitary, Matrix.one_mul,
        Matrix.mul_assoc, map_unitary, Matrix.mul_one]
    refine Matrix.ext fun i j => ?_
    exact GlobalTheory.VacuumCharacter.adele_ext hθ
      ((congrFun (congrFun s1.1 i) j).trans (congrFun (congrFun t1 i) j).symm)
      fun τ => (congrFun (congrFun (t2 τ) i) j).symm

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.NatEqui in

theorem thMoved_rat {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (hc : IsCurveIdeal D cc)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {n n' : ℕ} (hn : Even n) (hn' : Even n') {L L'} (hL : SD D L) (hL' : SD D L')
    (U : Matrix.unitaryGroup (Fin n) D.host.E) (U' : Matrix.unitaryGroup (Fin n') D.host.E) (z : VCx D.what₂.Tau n n') :
    B.thMoved n n' L L' (fun τ => ((U'.1.map (tauE D τ))ᴴ * Matrix.of (z τ) * U.1.map (tauE D τ) : Matrix _ _ ℂ)) =
      (∏ τ, tauE D τ U.1.det ^ (-((n' / 2 : ℕ) : ℤ)) * tauE D τ U'.1.det ^ ((n / 2 : ℕ) : ℤ)) *
        B.thMoved n n' (SDLat.smulLat U.1 L) (SDLat.smulLat U'.1 L') z := by
  obtain ⟨κ, k1, k2, -⟩ := GlobalTheory.TrueTheta.exists_kappa D
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.TrueTheta.exists_chi D κ k1 k2
  have h := congrFun ((eqP D cc δ B χ hc hδ hχ).1 n n' ⟨L, hL⟩ ⟨L', hL'⟩ hn hn' U U') z
  have h0 := chiFac_ne_zero hχ hL hL'
  refine mul_left_cancel₀ h0 (Eq.trans h ?_)
  change Formalism.L2.Ker.Base.chiFac χ n n' (SDLat.smulLat U.1 L) (SDLat.smulLat U'.1 L') * _ = _
  rw [← mul_assoc]
  congr 1
  unfold Formalism.L2.Ker.Base.chiFac
  rw [chi_smulLat hχ hL, chi_smulLat hχ hL', mul_zpow, mul_zpow, ← Finset.prod_zpow, ← Finset.prod_zpow,
    Finset.prod_mul_distrib]
  simp only [_root_.inv_zpow', neg_neg]
  change (∏ τ, tauE D τ U.1.det ^ _) * _ * ((∏ τ, tauE D τ U'.1.det ^ _) * _) = _
  ring

open scoped ComplexOrder in

theorem move_rat {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    {δ : ℂ} {sc : ℝ} (hp : StdPair θ S T δ sc ψ) {μ : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T μ μ om)
    (e : D.what₂.Tau → ℤ) (he : ∀ τ, HasInfExp D μ τ (e τ)) {f : WO S T → ℂ} (hf : IsHol θ S T ψ f)
    {cc : Ideal (𝓞 D.host.K)} {δ' : ℂ} (B : Formalism.L2.Ker.Base D cc δ') (hc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ') (c₀ : ℂ) {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T)
    (H : ∀ N N', Moves S hS g N → Moves T hT h N' → ∀ x y, IsDetRoot S g x → IsDetRoot T h y →
      xiN θ S T hS hT δ sc (om (g, h) f) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * B.thMoved a b N N' z)
    {r : GA D S} {r' : GA D T} (hr : IsRatFin S r) (hr' : IsRatFin T r') :
    ∀ N N', Moves S hS (r * g) N → Moves T hT (r' * h) N' → ∀ x y, IsDetRoot S (r * g) x → IsDetRoot T (r' * h) y →
      xiN θ S T hS hT δ sc (om (r * g, r' * h) f) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * B.thMoved a b N N' z := by
  subst hS hT
  intro N N' hN hN' x y hx hy
  obtain ⟨-, -, evS, evT⟩ := hp.rk
  obtain ⟨γ, hγ, k, hk, U, hU, e1, c1, l1, v1⟩ := rat_data hp.inf S hp.gS hr hg
  obtain ⟨γ', hγ', k', hk', U', hU', e2, c2, l2, v2⟩ := rat_data hp.inf T hp.gT hr' hh
  obtain ⟨x₀, hx₀⟩ := (GlobalTheory.Member.isDetRoot_laws D S).1 g
  obtain ⟨y₀, hy₀⟩ := (GlobalTheory.Member.isDetRoot_laws D T).1 h
  replace v1 := v1 μ _ e hom.hecS hom.resS evS he x x₀ hx hx₀
  replace v2 := v2 μ _ e hom.hecS hom.resS evS he y y₀ hy hy₀
  replace H := H _ _ ((moves_iff S g _).2 rfl) ((moves_iff T h _).2 rfl) x₀ y₀ hx₀ hy₀
  rw [(moves_iff _ _ _).1 hN, (moves_iff _ _ _).1 hN', l1, l2]
  have hcart : ∀ V : HSp D, V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    rw [gramAt_one hV]
    exact ⟨one_mul _, by simp, by rw [one_mul]; exact Matrix.PosDef.one⟩
  have hvac := GlobalTheory.VacuumCharacter.vacuum_character D ψ θ S T μ μ om hom hp.inf hp.sigS hp.sigT (fun _ => 1)
    (hcart S hp.gS) (hcart T hp.gT) _ _ he he (fun τ => e τ + (S.rank / 2 : ℕ)) (fun τ => e τ - (S.rank / 2 : ℕ))
    (fun τ => -((T.rank / 2 : ℕ) + e τ))
    (fun τ => by obtain ⟨m, hm⟩ := evS; rw [hm, show (m + m) / 2 = m by omega]; push_cast; ring)
    (fun τ => by obtain ⟨m, hm⟩ := evS; rw [hm, show (m + m) / 2 = m by omega]; push_cast; ring)
    (fun τ => by
      obtain ⟨m, hm⟩ := evT
      rw [Matrix.trace_one, Fintype.card_fin, hm, show (m + m) / 2 = m by omega]; push_cast; ring)
    f hf.1 hf.2 k hk k' hk' (fun τ => by rw [one_mul, mul_one])
  have h2 : (1 / 2 : ℂ) • (1 + 1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) = 1 := by module
  have hd : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) τ, (M.map (tauE D τ)).det = tauE D τ M.det :=
    fun M τ => (RingHom.map_det _ _).symm
  simp only [h2, sub_self, smul_zero, one_mul, add_zero, zero_mul, zero_add, Matrix.det_one, _root_.one_zpow, mul_one, c1, c2,
    hd] at hvac
  have hmul : om (γ, γ') (om (g, h) f) = om (r * g, r' * h) (om (k, k') f) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, e1, e2]
  rw [hvac, map_smul] at hmul
  funext z
  have key := xiN_rat hp.inf hom δ sc hγ hγ' U U' hU hU' (hom.om_pres (g, h) f hf.1) z
  rw [hmul, H] at key
  beta_reduce at key
  rw [thMoved_rat B hc hδ evS evT (sd_lat S hp.gS g) (sd_lat T hp.gT h), v1, v2] at key
  have hne : ∀ {n : ℕ} (U : Matrix.unitaryGroup (Fin n) D.host.E) τ, tauE D τ U.1.det ≠ 0 := fun U τ =>
    (_root_.map_ne_zero _).2 (Unitary.isUnit_coe (U := ⟨_, Matrix.det_of_mem_unitary U.2⟩)).ne_zero
  have hs : ∀ (c : ℂ) F, xiN θ S T rfl rfl δ sc (c • F) z = c * xiN θ S T rfl rfl δ sc F z := fun c F => by
    simp only [xiN, Pi.smul_apply, smul_eq_mul]; ring
  rw [hs] at key
  refine mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun τ _ =>
    mul_ne_zero (zpow_ne_zero _ (hne U' τ)) (zpow_ne_zero _ (hne U τ))) (key.trans ?_)
  simp only [neg_add, zpow_add₀ (hne _ _), Finset.prod_mul_distrib, mul_inv, ← Finset.prod_inv_distrib, ← _root_.zpow_neg]
  ring

theorem curveIdeal_top (D : D7) : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D ⊤ :=
  ⟨top_ne_bot, by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _⟩

theorem moveAt_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → A.MoveAt θ i hi c₀ g h → ∀ r r', IsRatFin _ r → IsRatFin _ r' → A.MoveAt θ i hi c₀ (r * g) (r' * h) := by
  intro B X I l Z w u A ψ θ hA i hi c₀ g h hg hh H r r' hr hr'
  have hp := (GlobalTheory.T.standard_pair_along_chain I l Z w u A ψ θ hA i hi).1
  choose e he using fun τ => (B.hc τ).e_int ⟨i, hi⟩
  have hexp := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ (I.rec7 l Z) _ _ _ (hA.chr ⟨i, hi⟩)).2 (I.C.isMu0 ⟨i, hi⟩).inf
  have hv := (hA.vac i hi).2
  exact move_rat _ _ hp (hA.om i hi) (fun τ => -e τ) (fun τ => by
      have e1 : ((-e τ : ℤ) : ℚ) = -(B.hc τ).e ⟨i, hi⟩ := by rw [Int.cast_neg, ← he τ]
      exact e1 ▸ hexp τ) ⟨hv.theta, hv.fock⟩ (Th.VacIn.toRec (D := I.rec7 l Z) I.J.V)
    (curveIdeal_top _) w.ok.amb_ok.delta c₀ hg hh H hr hr'

end GlobalTheory.AdForm.RatMove
