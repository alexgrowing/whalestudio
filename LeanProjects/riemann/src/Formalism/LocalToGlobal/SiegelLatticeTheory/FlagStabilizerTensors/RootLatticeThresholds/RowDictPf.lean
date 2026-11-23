import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GoodRecipPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionConjugacy
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RConvFExistsPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Closed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.CoefLocG
import Formalism.LocalRingCardinality.DataTies
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace TensorProduct ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.RowDictPf

open Formalism.L2.SG.RowDict

variable {D : D7} (X : HidaSetting D)

theorem finiteDimensional_HHX_of (hHC : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hF : ∀ v, IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)))
    (hint : ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v))) :
    FiniteDimensional ℂ (HHX X) :=
  hHC X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re X.B.e_adm.1 X.B.e_adm.2.2.2.2.1 X.B.Re_spec
    X.B.H X.B.σ (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.w
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1) hF (fun v => (X.low v).1) hint X.Rph X.Rph_spec

theorem f_eq : X.B.I.f = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  unfold AutInst.f
  omega

theorem rd_eq : X.B.I.rd = D.host.rdE := by
  have hd : discr X.B.I.E = discr D.host.E := NumberField.discr_eq_discr_of_algEquiv X.B.I.E X.ιE.toRatAlgEquiv
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : (Module.finrank ℚ D.host.E : ℝ) = 2 * (X.B.I.f : ℝ) := by
    unfold AutInst.f
    have : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ X.B.I.F := by rw [← e1, ← e2, e3, mul_comm]
    rw [this]; push_cast; ring
  unfold AutInst.rd Host.rdE
  rw [hd, e4]

section Real

open Formalism.L2.SG.Pf Formalism.MainNotions.LeviCoordinates

theorem rp_fin (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulRightInvariant] (g : I.Gf) :
    RPres (I.muA μf) ((1, g) : I.GA) := by
  have h1 : MeasurePreserving (fun x : I.Gf => x * g) μf μf := measurePreserving_mul_right μf g
  have h2 := (MeasurePreserving.id (Measure.pi fun v => Formalism.REAL.muG (I.ε v))).prod h1
  unfold RPres AutInst.muA
  convert h2 using 1
  funext x
  exact Prod.ext (mul_one _) rfl

theorem R_star (g : X.B.I.Gf) (φ : L2X X) : X.B.R (1, g) (star φ) = star (X.B.R (1, g) φ) := by
  have : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have hP : RPres (X.B.I.muA X.B.μf) ((1, g) : X.B.I.GA) := rp_fin X.B.I X.B.μf g
  have hPi : RPres (X.B.I.muA X.B.μf) (((1, g) : X.B.I.GA)⁻¹) := by
    have : ((1, g) : X.B.I.GA)⁻¹ = (1, g⁻¹) := Prod.ext inv_one rfl
    rw [this]; exact rp_fin X.B.I X.B.μf g⁻¹
  obtain ⟨h1, h2⟩ := rp_map (rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) hP hPi
  have e1 := X.B.R_spec (1, g) (star φ)
  have e2 := X.B.R_spec (1, g) φ
  have e3 : ∀ᵐ x ∂(muX X), ((star φ : L2X X) : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, g))) =
      star ((φ : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, g)))) := by
    refine ae_of_ae_map (p := fun y => ((star φ : L2X X) : X.B.I.GA → ℂ) y = star ((φ : X.B.I.GA → ℂ) y)) h1 ?_
    rw [h2]
    filter_upwards [Lp.coeFn_star φ] with y hy
    rw [hy]
    rfl
  apply Lp.ext
  filter_upwards [e1, e2, e3, Lp.coeFn_star (X.B.R (1, g) φ)] with x a1 a2 a3 a4
  rw [a1, a4, Pi.star_apply, a2]
  exact a3

end Real

section Red

open Formalism.MainNotions.BridgeLemma

def wB (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv X.ιE)
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv X.ιE).surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

theorem wLat_eq (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) : wLat X w = wLat0 X.B.I (wB X w) := by
  unfold wLat wLat0
  congr 1
  ext z
  constructor
  · rintro ⟨a, ⟨b, hb, hab⟩, y, hy, rfl⟩
    refine ⟨a, ?_, y, hy, rfl⟩
    show RingOfIntegers.mapRingEquiv X.ιE a ∈ w.asIdeal
    have : RingOfIntegers.mapRingEquiv X.ιE a = b := RingOfIntegers.ext (by simpa using hab)
    rw [this]
    exact hb
  · rintro ⟨a, ha, y, hy, rfl⟩
    exact ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, by simp⟩, y, hy, rfl⟩

theorem card_res_host (k : Fin 2) (v : D.nd.PlG k) :
    Nat.card (𝓞 D.host.E ⧸ (D.naut.plGw k v).asIdeal) = D.host.g k := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl : SplitsCompl D.host.E (D.host.g k) := by
    apply splitsCompl_of_ncard _ _ hp
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k
  obtain ⟨hN, -⟩ := hspl _ ((D.naut.plGw k v).isPrime.isMaximal (D.naut.plGw k v).ne_bot) (D.naut.plGw_over k v)
  rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem card_wB (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) :
    Nat.card (𝓞 X.B.I.E ⧸ (wB X w).asIdeal) = Nat.card (𝓞 D.host.E ⧸ w.asIdeal) :=
  Nat.card_congr (Ideal.quotientEquiv (wB X w).asIdeal w.asIdeal (RingOfIntegers.mapRingEquiv X.ιE)
    (Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv X.ιE).surjective w.asIdeal).symm).toEquiv

theorem redMat_iff (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (p : ℕ) (x : X.B.I.Gf)
    (M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)) : RedMat X w p x M ↔ RedMat0 X.B.I (wB X w) p x M := by
  unfold RedMat RedMat0 IsRedBasis IsRedBasis0 wLf
  rw [wLat_eq X w]
  exact Iff.rfl

theorem coeff_conj_of_central {G : Type*} [Group G] {z : MonoidAlgebra ℂ G} (hz : ∀ a, z * a = a * z)
    (g h : G) : z.coeff (h⁻¹ * g * h) = z.coeff g := by
  have e := congrArg (fun t : MonoidAlgebra ℂ G => t.coeff (g * h)) (hz (MonoidAlgebra.single h 1))
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    mul_inv_cancel_right] at e
  rw [mul_assoc, ← e]

theorem goodProjector_coeff_classFunction (γ P : G0g D.nd) : D.ntypes.e0.coeff (P⁻¹ * γ * P) = D.ntypes.e0.coeff γ := by
  unfold NTypes.e0
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · refine Finset.prod_congr rfl fun kv _ => ?_
    exact coeff_conj_of_central (D.ntypes.eSer_central kv.1 _) (γ kv) (P kv)
  · rfl

theorem egWellDef_of (hC : RedConj0) : EgWellDef X := by
  intro x γ γ' h h'
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      γ' kv = P⁻¹ * γ kv * P := by
    intro kv
    exact hC X.B.I (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1) (D.host.g_prime kv.1)
      (by rw [card_wB, card_res_host]) D.R.r X.n_eq.symm x (γ kv) (γ' kv)
      ((redMat_iff X _ _ x _).1 (h kv)) ((redMat_iff X _ _ x _).1 (h' kv))
  choose P hP using hP
  have e : γ' = (P : G0g D.nd)⁻¹ * γ * P := funext fun kv => hP kv
  rw [e, goodProjector_coeff_classFunction]

theorem redExists_of (hR : RedExists0) : RedExists X := by
  intro x hx
  have : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ M : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      RedMat0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1) x
        (M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := fun kv =>
    hR X.B.I _ _ (D.host.g_prime kv.1) (by rw [card_wB, card_res_host]) D.R.r X.n_eq.symm x hx
  choose M hM using this
  exact ⟨M, fun kv => (redMat_iff X _ _ x _).2 (hM kv)⟩

end Red

section E0

open Polynomial

theorem coeff_monicOf {K : Type} [Field K] {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (Formalism.CyclotomicNorms.monicOf a).coeff i = a i := by
  classical
  unfold Formalism.CyclotomicNorms.monicOf
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt), zero_add, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h).symm
  · simp

theorem monicOf_monic {K : Type} [Field K] {N : ℕ} (a : Fin N → K) :
    (Formalism.CyclotomicNorms.monicOf a).Monic ∧ (Formalism.CyclotomicNorms.monicOf a).natDegree = N := by
  have hd : degree (∑ i : Fin N, C (a i) * X ^ (i : ℕ)) < N := degree_sum_fin_lt a
  refine ⟨monic_X_pow_add hd, ?_⟩
  unfold Formalism.CyclotomicNorms.monicOf
  rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]

theorem monicOf_coeff {K : Type} [Field K] {N : ℕ} {h : K[X]} (hm : h.Monic) (hd : h.natDegree = N) :
    Formalism.CyclotomicNorms.monicOf (fun i : Fin N => h.coeff i) = h := by
  ext j
  rcases lt_trichotomy j N with hj | rfl | hj
  · exact coeff_monicOf _ ⟨j, hj⟩
  · have h1 := (monicOf_monic (fun i : Fin j => h.coeff i)).1.coeff_natDegree
    rw [(monicOf_monic (fun i : Fin j => h.coeff i)).2] at h1
    rw [h1, ← hd, hm.coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [(monicOf_monic _).2]; exact hj),
      coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hj)]

section Recip

variable {g : ℕ} [Fact g.Prime] {f : (ZMod g)[X]}

end Recip

end E0

section GoodOpEx

open Formalism.L2.SG.Pf.unitaryCongruence

theorem choose_congr {α : Sort*} {p q : α → Prop} (h : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    Classical.choose hp = Classical.choose hq := by
  subst h
  rfl

theorem incl_mem_Lf {y : Fin X.B.I.n → X.B.I.E} (hy : y ∈ X.B.I.L) : incl X.B.I y ∈ X.B.I.Lf :=
  Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem smul_Lf_wLf (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {y : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hy : y ∈ X.B.I.Lf) : (g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y ∈ wLf X w := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    have hm : (g : X.B.I.E) • l ∈ wLat X w :=
      Submodule.subset_span ⟨(g : 𝓞 X.B.I.E), ⟨(g : 𝓞 D.host.E), hg, by simp⟩, l, hl, by simp⟩
    have e : (g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (l i)) =
        fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((g : X.B.I.E) • l) i) := by
      funext i
      simp [map_natCast]
    rw [e]
    exact Submodule.subset_span ⟨⟨_, hm⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem level_mem (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
  have hgk : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
  have hdvd : D.host.g kv.1 ∣ X.B.g := by
    rw [X.g_eq]
    rcases kv with ⟨k, v⟩
    fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hgk

theorem goodAt_mul {x k : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hk : k ∈ X.B.I.Kg X.B.g) (γ : G0g D.nd) :
    GoodAt X (x * k) γ ↔ GoodAt X x γ := by
  have key : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∀ y ∈ X.B.I.L,
      X.B.I.fmat (x * k) *ᵥ incl X.B.I y - X.B.I.fmat x *ᵥ incl X.B.I y ∈ wLf X (D.naut.plGw kv.1 kv.2) := by
    intro kv y hy
    obtain ⟨z, hz, hkz⟩ := hk.2 _ (incl_mem_Lf X hy)
    have e1 : X.B.I.fmat k *ᵥ incl X.B.I y - incl X.B.I y = (X.B.I.fmat k - 1) *ᵥ incl X.B.I y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have e : X.B.I.fmat (x * k) *ᵥ incl X.B.I y - X.B.I.fmat x *ᵥ incl X.B.I y =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat x *ᵥ z) := by
      rw [fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, e1, hkz, Matrix.mulVec_smul]
    rw [e]
    exact smul_Lf_wLf X _ _ (level_mem X kv) (K_mv _ hx hz)
  have split : ∀ a c d : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, a - d = (a - c) + (c - d) := by
    intros; abel
  simp only [GoodAt, RedMat]
  refine forall_congr' fun kv => exists_congr fun b => and_congr_right fun hb => forall_congr' fun i => ?_
  rw [split _ (X.B.I.fmat x *ᵥ incl X.B.I (b i))]
  exact Submodule.add_mem_iff_right _ (key kv (b i) (hb.1 i))

theorem eg_mul (x : X.B.I.Gf) {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kg X.B.g) : eg X (x * k) = eg X x := by
  unfold eg
  by_cases hx : x ∈ X.B.I.Kset
  · have hxk : x * k ∈ X.B.I.Kset := K_mul _ hx hk.1
    have hpred : (fun γ => GoodAt X (x * k) γ) = (fun γ => GoodAt X x γ) :=
      funext fun γ => propext (goodAt_mul X hx hk γ)
    by_cases hE : ∃ γ, GoodAt X x γ
    · have hE' : ∃ γ, GoodAt X (x * k) γ := by rw [hpred]; exact hE
      rw [dif_pos ⟨hxk, hE'⟩, dif_pos ⟨hx, hE⟩, choose_congr hpred hE' hE]
    · have hE' : ¬ ∃ γ, GoodAt X (x * k) γ := by rw [hpred]; exact hE
      rw [dif_neg (fun h => hE' h.2), dif_neg (fun h => hE h.2)]
  · have hxk : x * k ∉ X.B.I.Kset := by
      intro h
      apply hx
      have := K_mul _ h (K_inv _ hk.1)
      rwa [mul_inv_cancel_right] at this
    rw [dif_neg (fun h => hxk h.1), dif_neg (fun h => hx h.1)]

theorem level_ne_zero : X.B.g ≠ 0 := by
  rw [X.g_eq]
  exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem isLocallyConstant_eg : IsLocallyConstant (eg X) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen (X.B.I.Kg X.B.g) := X.B.I.topf_open X.B.g (Nat.one_le_iff_ne_zero.2 (level_ne_zero X))
  have h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g :=
    ⟨K_one _, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩
  have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' X.B.I.Kg X.B.g) := hopen.preimage (continuous_const.mul continuous_id)
  have hmem : x ∈ (fun y => x⁻¹ * y) ⁻¹' X.B.I.Kg X.B.g := by
    show x⁻¹ * x ∈ X.B.I.Kg X.B.g
    rw [inv_mul_cancel]; exact h1
  filter_upwards [hop.mem_nhds hmem] with y hy
  have := eg_mul X x hy
  rwa [mul_inv_cancel_left] at this

theorem isOpen_Kset : IsOpen X.B.I.Kset := by
  have h := X.B.I.topf_open 1 le_rfl
  convert h using 1
  ext x
  constructor
  · intro hx
    exact ⟨hx, fun y hy => ⟨_, K_sub_mv _ hx hy, by simp⟩⟩
  · intro hx
    exact hx.1

theorem integrable_eg : Integrable (eg X) X.B.μf := by
  have hc : Continuous (eg X) := (isLocallyConstant_eg X).continuous
  have hK : IsCompact X.B.I.Kset := Formalism.L2.SG.Closed.AutKCompact_holds X.B.I
  have hon : IntegrableOn (eg X) X.B.I.Kset X.B.μf :=
    hc.continuousOn.integrableOn_compact' hK (isOpen_Kset X).measurableSet
  refine hon.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  unfold eg
  rw [dif_neg (fun h => hx h.1)]

theorem goodOp_exists (hR : RConvFExists) : Nonempty (GoodOp X) := by
  have hFR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  obtain ⟨T, hT⟩ := hR X.B.I X.B.μf (Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf) hFR.2.1 hFR.2.2.2.1 X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec (eg X) (integrable_eg X)
  exact ⟨⟨T, hT⟩⟩

end GoodOpEx

section Dstar

def DstarIdx : Prop :=
  (X.B.μf X.B.I.Kset).toReal / X.volK2 = Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1)

def DstarVol : Prop :=
  (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
    Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ

theorem chi2_apply_one : X.chi2 1 = 1 := by
  obtain ⟨h1, hmul, -, hχ, hn⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have e := hχ 1 h1 1 h1
  rw [one_mul] at e
  have hne : X.chi2 1 ≠ 0 := by
    intro h0
    have := hn 1 h1
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have : X.chi2 1 * (X.chi2 1 - 1) = 0 := by rw [mul_sub, mul_one, ← e, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hne
  · exact sub_eq_zero.1 h

theorem e_one : X.B.e 1 = 1 / (X.volK2 : ℂ) := by
  have h1 := (Formalism.L2.SG.Closed.level_subgroup_is_group X).1
  rw [X.e_eq 1, if_pos (show (1 : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw from h1)]
  change star (X.chi2 1) / (X.volK2 : ℂ) = _
  rw [chi2_apply_one, star_one]

end Dstar

section Schur

open Formalism.MainNotions.S

def DSSchurOrth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Nontrivial H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    IsSqIntOn ε σ → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d

theorem fdegOf_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (h : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : w ≠ 0) :
    fdegOf (Formalism.REAL.muG ε) σ w = d := by
  obtain ⟨hd, hS⟩ := h
  obtain ⟨-, hI⟩ := hS w w w w
  have e1 : ∀ g : Formalism.REAL.UJ ε, coefOn (ε := ε) σ w w g * star (coefOn (ε := ε) σ w w g) =
      ((‖coefOn (ε := ε) σ w w g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [← starRingEnd_apply, RCLike.mul_conj]
    push_cast
    rfl
  simp_rw [e1] at hI
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hI
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hR : ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖w‖ ^ 4 / d := by
    have h2 : ((∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [hI]
      change ((‖w‖ : ℂ)) ^ 2 * ((‖w‖ : ℂ)) ^ 2 / (d : ℂ) = _
      push_cast
      ring
    exact_mod_cast h2
  unfold fdegOf
  rw [hR]
  field_simp

theorem fdeg_of_schur (hS : DSSchurOrth) (v : InfinitePlace X.B.I.F) :
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) := by
  obtain ⟨hC, hN, hU, hIrr, hSq, -⟩ := X.ds v
  obtain ⟨d, hd⟩ := hS _ _ (X.B.H v) (X.B.σ v) hN hU hIrr hSq
  have hw : X.B.w v ≠ 0 := by
    intro h0
    have := (X.low v).1
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [fdegOf_eq hd hw]
  exact hd

theorem finiteDimensional_HHX_of_hypotheses (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hS : DSSchurOrth)
    (hint : ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v))) :
    FiniteDimensional ℂ (HHX X) :=
  finiteDimensional_HHX_of X hHC (fdeg_of_schur X hS) hint

end Schur

end Formalism.L2.SG.Pf.RowDictPf

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict

variable {D : D7} (X : HidaSetting D)

theorem rowDictEgWellDef_holds : EgWellDef X :=
  RowDictPf.egWellDef_of X RedConj0Pf.reduction_conjugacy

theorem rowDictGoodOp_exists : Nonempty (GoodOp X) :=
  RowDictPf.goodOp_exists X RConvFExistsPf.convergent_reduction_exists

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.RowDictPf

open Formalism.MainNotions.S

theorem schur_orthogonality_discrete_series : DSSchurOrth := by
  intro n ε H _ _ _ σ hN hU hI hS
  exact PIW.HCFdeg.formal_degree_abstract_form n ε H σ hU hI hS

variable {D : D7} (X : HidaSetting D)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem hint_of_gap (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (v : InfinitePlace X.B.I.F) :
    Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
    (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X Formalism.MainNotions.BesselDiscreteSeries.coefWeightedLoc_of_fact hG) v
  have h2 : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp h
  exact h2.const_mul _

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem finiteDimensional_HHX_of_gap (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    FiniteDimensional ℂ (HHX X) :=
  finiteDimensional_HHX_of_hypotheses X hHC schur_orthogonality_discrete_series (hint_of_gap X hG)

theorem isFdeg_smul {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Measure (Formalism.REAL.UJ ε)} {d : ℝ} {c : NNReal} (hc : 0 < c)
    (h : IsFdeg μ σ d) : IsFdeg ((c : ENNReal) • μ) σ (d / c) := by
  obtain ⟨hd, hS⟩ := h
  refine ⟨div_pos hd (by exact_mod_cast hc), fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := hS v w v' w'
  refine ⟨hi.smul_measure ENNReal.coe_ne_top, ?_⟩
  rw [integral_smul_measure, he, ENNReal.coe_toReal, Complex.real_smul]
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hc)
  have hd0 : d ≠ 0 := hd.ne'
  push_cast
  field_simp

theorem fdeg_tie (hT : Formalism.BasicNotions.dsigTie D) (τ : D.what₂.Tau) {n : ℕ} (e : n = 2 * D.R.rS + D.R.k + 1)
    {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hε : ∀ i, ε i = epsSH D.R (Fin.cast e i)) (hl : ∀ i, lam i = lamSH D.R (D.hc τ) (Fin.cast e i))
    (hds : IsDS ε lam σ) (hd : IsFdeg (Formalism.REAL.muG ε) σ d) :
    d = (D.s.cdScale _ (epsSH D.R) : ℝ) * D.dsig τ := by
  subst e
  have hε' : ε = epsSH D.R := funext fun i => by rw [hε i]; rfl
  have hl' : lam = lamSH D.R (D.hc τ) := funext fun i => by rw [hl i]; rfl
  subst hε' hl'
  have h2 := isFdeg_smul (D.s.cdScale_pos _ (epsSH D.R)) hd
  have h3 := hT τ H σ (d / D.s.cdScale _ (epsSH D.R)) hds h2
  have hc0 : (D.s.cdScale _ (epsSH D.R) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D.s.cdScale_pos _ _)
  rw [← h3]
  field_simp

theorem dv_eq (hT : Formalism.BasicNotions.dsigTie D) (v : InfinitePlace X.B.I.F) :
    X.dv v = (D.s.cdScale _ (epsSH D.R) : ℝ) * D.dsig (X.pl v) :=
  fdeg_tie hT (X.pl v) (Formalism.L2.SG.Pf.WuDec.hdim X) (fun i => by rw [X.eps_eq]; rfl)
    (fun i => by rw [X.lam_eq]; rfl) (X.ds v) (fdeg_of_schur X schur_orthogonality_discrete_series v)

def DstarVolV : Prop :=
  X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal *
      ∏ _v : InfinitePlace X.B.I.F, (D.s.cdScale _ (epsSH D.R) : ℝ) = Formalism.MainNotions.StandardLattice.volY0 D

def DstarVolCore : Prop :=
  ∀ (D : D7) (X : HidaSetting D), Formalism.MainNotions.StandardLattice.VolTie D → Formalism.BasicNotions.cdScaleTie D → DstarVolV X

theorem dstarVol_of (hT : Formalism.BasicNotions.dsigTie D) (hV : DstarVolV X) : DstarVol X := by
  unfold DstarVol
  unfold DstarVolV at hV
  have hd : ∀ v, X.dv v = (D.s.cdScale _ (epsSH D.R) : ℝ) * D.dsig (X.pl v) := dv_eq X hT
  simp_rw [hd]
  rw [Finset.prod_mul_distrib]
  have hp : ∏ v, D.dsig (X.pl v) = ∏ ρ, D.dsig ρ := Fintype.prod_equiv X.pl _ _ (fun _ => rfl)
  rw [hp, ← hV]
  ring

end Formalism.L2.SG.Pf.RowDictPf
