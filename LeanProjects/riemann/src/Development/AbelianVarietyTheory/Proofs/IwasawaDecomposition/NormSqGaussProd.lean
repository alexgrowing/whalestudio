import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateModelSameThetaFunctions
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaInnerProductEqRealTorusMean
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeVacuaTensorCorrespondLine
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NsmulMemHatA

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.VacUnit

section Mean
open MeasureTheory Measure
open scoped ENNReal Pointwise

theorem lintegral_sub {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] {μ : Measure V}
    [μ.IsAddLeftInvariant] {Γ B : AddSubgroup V} [Countable B] (h : Γ ≤ B) {Fd F : Set V}
    (hFd : IsAddFundamentalDomain Γ Fd μ) (hF : IsAddFundamentalDomain B F μ) (Φ : V → ℝ≥0∞)
    (hΦ : ∀ b ∈ B, ∀ v, Φ (b + v) = Φ v) :
    ∫⁻ v in Fd, Φ v ∂μ = ∑' _ : B ⧸ Γ.addSubgroupOf B, ∫⁻ v in F, Φ v ∂μ := by
  have : Countable Γ := (AddSubgroup.inclusion_injective h).countable
  have hb : Function.Bijective fun p : (B ⧸ Γ.addSubgroupOf B) × Γ => p.1.out + AddSubgroup.inclusion h p.2 := by
    have hm : ∀ (b : B) (γ : Γ), ((b + AddSubgroup.inclusion h γ : B) : B ⧸ Γ.addSubgroupOf B) = b := fun b γ =>
      QuotientAddGroup.mk_add_of_mem b γ.2
    constructor
    · rintro ⟨q, γ⟩ ⟨q', γ'⟩ e
      have e' := congrArg (fun b : B => (b : B ⧸ Γ.addSubgroupOf B)) e
      simp only [hm, QuotientAddGroup.out_eq'] at e'
      subst e'
      exact Prod.ext rfl (AddSubgroup.inclusion_injective h (add_left_cancel e))
    · intro b
      obtain ⟨γ, hγ⟩ := QuotientAddGroup.mk_out_eq_add (Γ.addSubgroupOf B) b
      refine ⟨(b, -⟨γ.1, γ.2⟩), ?_⟩
      simp only [hγ, map_neg]
      exact add_neg_cancel_right _ _
  rw [hF.setLIntegral_eq_tsum, ← (Equiv.ofBijective _ hb).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun q => ?_
  rw [hF.setLIntegral_eq (hF.vadd_of_comm q.out) Φ (fun b v => hΦ b b.2 v), hFd.setLIntegral_eq_tsum']
  refine tsum_congr fun γ => ?_
  have e : (γ +ᵥ (q.out +ᵥ F)) = (q.out + AddSubgroup.inclusion h γ) +ᵥ F := by
    rw [add_comm, add_vadd]; rfl
  rw [Set.inter_comm, e]
  exact lintegral_congr fun v => (hΦ _ (h (-γ).2) v).symm

theorem isFD_pi {Y : Type} [AddCommGroup Y] [MeasureSpace Y] [SigmaFinite (volume : Measure Y)] {A : AddSubgroup Y}
    {F : Set Y} (hF : IsAddFundamentalDomain A F volume) (n : ℕ) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : Fin n => A) (Set.univ.pi fun _ : Fin n => F) volume := by
  have hq (i : Fin n) := quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure Y)) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (volume : Measure (Fin n → Y)))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

theorem integral_prod_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {g n : ℕ}
    (e : V ≃L[ℝ] (Fin n → Fin g → ℂ)) {A : AddSubgroup (Fin g → ℂ)} [Countable A] {F : Set (Fin g → ℂ)}
    (hF : IsAddFundamentalDomain A F volume) {φ : (Fin g → ℂ) → ℝ} (hc : Continuous φ) (h0 : ∀ z, 0 ≤ φ z)
    (hp : ∀ a ∈ A, ∀ z, φ (a + z) = φ z) (hm : (∫ z in F, φ z) / (volume F).toReal = 1)
    {Γ : AddSubgroup V} (hΓ : ∀ v ∈ Γ, ∀ b, e v b ∈ A) {Fd : Set V} (hFd : IsAddFundamentalDomain Γ Fd μ) :
    ∫ v in Fd, ∏ b, φ (e v b) ∂μ = (μ Fd).toReal := by
  have hV : (volume F).toReal ≠ 0 := fun h => by simp [h] at hm
  rw [div_eq_one_iff_eq hV] at hm
  have hi : Integrable φ (volume.restrict F) := Integrable.of_integral_ne_zero (hm ▸ hV)
  set P : Set (Fin n → Fin g → ℂ) := Set.univ.pi fun _ : Fin n => F with hP
  let Φ : (Fin n → Fin g → ℂ) → ℝ := fun z => ∏ b, φ (z b)
  have hΦc : Continuous Φ := continuous_finset_prod _ fun b _ => hc.comp (continuous_apply b)
  have hΦ0 : ∀ z, 0 ≤ Φ z := fun z => Finset.prod_nonneg fun b _ => h0 _
  have h1 : ∫⁻ z in P, ENNReal.ofReal (Φ z) = volume P := by
    have e1 : volume.restrict P = Measure.pi fun _ : Fin n => volume.restrict F := restrict_pi_pi _ _
    have e2 : volume P = volume F ^ n := by
      rw [hP, volume_pi_pi]; simp
    rw [← ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall hΦ0), e1, e2]
    · rw [integral_fintype_prod_eq_pow, hm, Fintype.card_fin, ← ENNReal.toReal_pow, ENNReal.ofReal_toReal]
      exact ENNReal.pow_ne_top fun h => hV (by simp [h])
    · rw [e1]; exact Integrable.fintype_prod fun _ => hi
  have hH := e.isAddHaarMeasure_map μ
  have : (volume : Measure (Fin g → ℂ)).IsAddHaarMeasure := pi.isAddHaarMeasure _
  have : (volume : Measure (Fin n → Fin g → ℂ)).IsAddHaarMeasure := pi.isAddHaarMeasure _
  obtain ⟨c, hc'⟩ : ∃ c : NNReal, μ.map e = c • volume := ⟨_, isAddLeftInvariant_eq_smul _ _⟩
  have hme := e.toHomeomorph.measurableEmbedding
  have hq : QuasiMeasurePreserving e μ volume := ⟨e.continuous.measurable, by
    rw [hc']; exact smul_absolutelyContinuous⟩
  let Bn := AddSubgroup.pi Set.univ fun _ : Fin n => A
  let B : AddSubgroup V := Bn.comap e.toLinearEquiv.toAddEquiv.toAddMonoidHom
  let k : B ≃ Bn := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  have : Countable Bn := Function.Injective.countable (f := fun (a : Bn) (i : Fin n) => (⟨a.1 i, a.2 i trivial⟩ : A))
    fun a b h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  have : Countable B := k.injective.countable
  have hB : IsAddFundamentalDomain B (e ⁻¹' P) μ :=
    (isFD_pi hF n).preimage_of_equiv hq k.symm.bijective fun a v => by
      change e (e.symm a + v) = a + e v
      simp
  have hle : Γ ≤ B := fun v hv i _ => hΓ v hv i
  have h2 := lintegral_sub hle hFd hB (fun v => ENNReal.ofReal (Φ (e v))) fun b hb v => by
    simp only [Φ, map_add, Pi.add_apply]
    exact congrArg _ (Finset.prod_congr rfl fun i _ => hp _ (hb i trivial) _)
  have h3 := lintegral_sub hle hFd hB (fun _ => 1) fun _ _ _ => rfl
  have h4 : ∀ Ψ : (Fin n → Fin g → ℂ) → ℝ≥0∞, ∫⁻ v in e ⁻¹' P, Ψ (e v) ∂μ = c * ∫⁻ z in P, Ψ z := fun Ψ => by
    have := hme.lintegral_map (μ := μ.restrict (e ⁻¹' P)) Ψ
    have e3 := hme.restrict_map μ P
    simp only [ContinuousLinearEquiv.coe_toHomeomorph] at this e3
    rw [← this, ← e3, hc', restrict_smul, lintegral_smul_measure]
    rfl
  rw [h4 fun z => ENNReal.ofReal (Φ z), h1] at h2
  rw [h4 fun _ => 1, setLIntegral_one, setLIntegral_one, ← h2] at h3
  rw [h3]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun v => hΦ0 _)
    (hΦc.comp e.continuous).aestronglyMeasurable

end Mean

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r}

theorem norm_periodic (hs : IsSympl X bas) (hx' : x ∈ X.dom) {w : E} {L : Lt E r} {th : (Fin g → ℂ) → ℂ}
    (h : IsTheta1 X bas idx w x L th) {u : Fin r → E} (hu : u ∈ L) (z : Fin g → ℂ) :
    ‖th (pv X idx x u + z)‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x (pv X idx x u + z) (pv X idx x u + z)).re) =
      ‖th z‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x z z).re) := by
  have hc := (hx_laws E r X g bas idx 0 hs Even.zero x hx').1
  have hp : _ = th z := congrFun (h.2 u hu) z
  have hε : ‖eps1 X w u‖ = 1 := by
    rw [eps1, Complex.norm_exp]
    simp
  generalize pv X idx x u = p at hp
  simp only [Pi.smul_apply, smul_eq_mul, fock] at hp
  rw [← hp, add_comm p z, norm_mul, norm_mul, hε, _root_.one_mul, mul_pow, Complex.norm_exp,
    ← Real.exp_nat_mul, mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
  congr 2
  have e1 : (hx X bas idx x (z + p) (z + p)).re =
      (hx X bas idx x z z).re + 2 * (hx X bas idx x z p).re + (hx X bas idx x p p).re := by
    have := congrArg Complex.re (hc z p)
    rw [Complex.conj_re] at this
    simp only [hx, mulVec_add, star_add, add_dotProduct, dotProduct_add, Complex.add_re] at this ⊢
    linarith
  have e2 : hx X bas idx x (z + (1 / 2 : ℂ) • p) p = hx X bas idx x z p + (1 / 2 : ℝ) * hx X bas idx x p p := by
    simp only [hx, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
    push_cast; ring
  rw [e1, e2]
  simp only [Nat.cast_one, _root_.one_mul, Complex.neg_re, Complex.re_ofReal_mul, Complex.add_re]
  push_cast; ring

theorem norm_sq_gauss_prod (th : (Fin g → ℂ) → ℂ) (z : Fin n → Fin g → ℂ) :
    ‖Ker.gaussR X bas idx x z * ∏ b, th (z b)‖ ^ 2 =
      ∏ b, ‖th (z b)‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x (z b) (z b)).re) := by
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, norm_mul, mul_pow, norm_prod, Finset.prod_pow, mul_comm, Ker.gaussR,
    Complex.norm_exp, ← Real.exp_nat_mul, ← Finset.mul_sum]
  congr 2
  have : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.neg_re, Complex.re_ofReal_mul, Complex.re_sum]
  push_cast; ring

theorem exists_nsmul_mem {Λ L : Lt E r} (hΛ : Λ.FG) (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ Λ, N • v ∈ L := by
  obtain ⟨s, rfl⟩ := hΛ
  choose k hk hk' using GlobalTheory.LatFin.exists_int_smul_mem L hL
  refine ⟨(∏ v ∈ s, k v).natAbs, Int.natAbs_pos.2 (Finset.prod_ne_zero_iff.2 fun v _ => hk v), fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨c, hc⟩ := Int.dvd_natAbs.2 (Finset.dvd_prod_of_mem k hv)
    rw [← natCast_zsmul, hc, mul_comm, mul_smul]
    exact zsmul_mem (hk' v) c
  | zero => simp
  | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
  | smul a u _ hu => rw [smul_comm]; exact L.smul_mem a hu

end Classical

theorem frOf_mem_dom {D : D7} {T : HSp D} {X : Data D.host.E T.rank} {eT : D.what₂.Tau ≃ X.Ψ} (hm : ModelW T rfl X)
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) {Z : Fam T} (hZ : IsONeg T X.p0 Z) : frOf rfl eT Z ∈ X.dom := by
  refine Ker.ONBasis.mem_dom X fun σ => ?_
  obtain ⟨ρ, rfl⟩ := eT.surjective σ
  ext a b
  have h := congrFun (congrFun (hZ ρ) b) a
  have hs : sgnM X a b = -negM T X.p0 b a := by
    simp only [sgnM, negM, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  rw [hs, ← h]
  simp only [FD.gram, Matrix.of_apply, hermC, FD.col, FD.mat, frOf, Equiv.symm_apply_apply, he, hm.1,
    Matrix.mul_apply, Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, Fin.cast_eq_self, finCongr_refl,
    Matrix.reindex_refl_refl, Matrix.neg_apply, map_neg, ← Finset.sum_neg_distrib,
    Matrix.transpose_apply, Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

def conjPt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X X' : Data E r} (e : X.Ψ ≃ X'.Ψ) (n : ℕ) :
    Ker.WR X' n ≃ₗ[ℝ] Ker.WR X n where
  toFun v τ k a := conj (v (e τ) k a)
  invFun v σ k a := conj (v (e.symm σ) k a)
  map_add' _ _ := by funext τ k a; simp
  map_smul' _ _ := by funext τ k a; simp
  left_inv _ := by funext τ k a; simp
  right_inv _ := by funext τ k a; simp

theorem vac_eq_unit_mul : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → GlobalTheory.Ker.IdemTwo w → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ (LT : Lt D.host.E T.rank) (L : Lt D.host.E r), SelfD X L → GlobalTheory.Ker.IsAA (latW hr L) LT → ∀ f, IsVacO ψ θ S T (fun _ => 1) (cartZ T X.p0 Z) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) f → ∀ th : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w (frOf hr eT Z) L th → MeanOne X bas idx (frOf hr eT Z) L th → ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ p : WO S T, GlobalTheory.Ker.IsRealPt p → f p = a * (GlobalTheory.Ker.gaussR X bas idx (frOf hr eT Z) (GlobalTheory.Ker.zR X idx (frOf hr eT Z) (rePt θ hr eT p)) * ∏ b, th (GlobalTheory.Ker.zR X idx (frOf hr eT Z) (rePt θ hr eT p) b)) := by
  intro D S T r g hr ψ θ X eT bas idx hS w hw hw' hw2 Z hZ LT L hL hA f hf th hth hmean
  subst hr
  obtain ⟨X', m, hq', bas', idx', hs, π, hΛ, hEF, hhe, H⟩ :=
    GlobalTheory.OneMapRef.Flip.exists_flip_model D S T _ g rfl ψ θ X eT bas idx hS (T.rank - X.p0) (Nat.add_sub_cancel' X.p0_le)
  obtain ⟨hB, H⟩ := H Z
  obtain ⟨hsB, hZak, -⟩ := H hZ
  replace hB := hB.1 hZ
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  set B : C.Bas := fun ρ => (Z ρ).submatrix id π with hBd
  have hsym := hS.2.2.2.2.2.2.2
  have hev := hS.2.2.2.1
  replace hEF : ∀ u v, EF X' u v = EF X u v := hEF
  replace hΛ : X'.Λ = X.Λ := hΛ.trans (Submodule.comap_id _)
  replace hA : Ker.IsAA L LT := hA
  replace hhe : ∀ y φ, heisG X' bas' y φ = heisG X bas y φ := hhe
  have hL' : SelfD X' L := ⟨hL.1, by simpa only [hEF] using hL.2⟩
  have hx' := frOf_mem_dom hS.2.2.2.2.1 hS.2.2.2.2.2.2.1 hZ
  set x := frOf rfl eT Z with hxd
  obtain ⟨-, hv⟩ := hf
  have hstar : ∀ v : Fin S.rank → D.host.E, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank := by
    have : ∀ v : Fin S.rank → D.host.E, v ∈ stdL D.host.E S.rank → star v ∈ stdL D.host.E S.rank := fun v hv =>
      (SW.Base.mem_stdL _).2 fun a => SW.Base.isIntegral_cc ((SW.Base.mem_stdL _).1 hv a)
    exact fun v => ⟨this v, fun h => by simpa using this _ h⟩
  have hV := SW.Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  obtain ⟨v, hvac⟩ := (TensVac.vacua _ _ X g bas idx S.rank hsym hev w hw hw' L hL 1 _ hV).1
  have hvac' : IsVac X' bas' w (tens (stdL D.host.E S.rank) L) v :=
    ⟨hvac.1, hvac.2.1, fun y hy => by simpa only [SW.epsW, hEF, hhe] using hvac.2.2 y hy⟩
  obtain ⟨t, ht⟩ := (Ker.latVac_th_line D S T C w hw hw' hw2 1 _ hV L hL').2 B hB v hvac' f hv.theta
    (fun τ => by rw [hsB]; exact hv.fock τ) (by rw [← Ker.LatTens.latO_eq_hatA D S T C _ _ LT _ hstar hA]; exact hv.lat)
  have hz := ((hZak v _).1 (Ker.ZakEx.isZak_Th D S T C _ (Ker.ONBasis.mem_dom _ (Ker.ONBasis.isONFr_xB C hB)) v
    hvac.1).1).2
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA _ _ X g bas idx S.rank hsym hev w hw hw' L hL v hvac x hx' th hth
  obtain ⟨A, F, hAm, hF, hm⟩ := hmean
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ : ∃ z, th z ≠ 0 := by
      by_contra! h0
      simp [h0] at hm
    exact Finset.prod_ne_zero_iff.2 (fun _ _ => hz) ((hκ fun _ => z).trans (zero_mul _))
  have hfp : ∀ p : WO S T, Ker.IsRealPt p → f p = t / κ * (Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ rfl eT p)) *
      ∏ b, th (Ker.zR X idx x (rePt θ rfl eT p) b)) := fun p hp => by
    rw [ht, Pi.smul_apply, hz p hp, hκ, Ker.thR, smul_eq_mul]
    field_simp
  refine ⟨t / κ, ?_, hfp⟩
  generalize t / κ = a at hfp
  obtain ⟨⟨⟨μ, 𝓕⟩, hμ⟩, hn⟩ := hv.norm
  have h1 : nrm2 μ 𝓕 f = 1 := hn _ hμ
  obtain ⟨N₀, hN₀, hN⟩ := Ker.TorusMean.ipO_eq_mean D S T C μ 𝓕 hμ f f hv.theta hv.theta
  obtain ⟨N₁, hN₁, hN'⟩ := exists_nsmul_mem X.Λ_fg (TensLat.span_of_selfD X hL)
  obtain ⟨⟨Fd, hFd⟩, hN⟩ := hN (N₀ * N₁) (Nat.mul_pos hN₀ hN₁) (Dvd.intro _ rfl)
  obtain ⟨⟨e₀, he₀⟩, -⟩ := Ker.zR_laws _ _ X g _ (Nat.add_sub_cancel' X.p0_le) bas idx S.rank hsym hev x hx'
  let J := conjPt (eT.symm.trans m.e) S.rank
  let e := J.toContinuousLinearEquiv.trans e₀
  have hJ : ∀ p : WO S T, e (C.realPt p) = Ker.zR X idx x (rePt θ rfl eT p) := fun p => by
    rw [← he₀]
    refine congrArg e₀ ?_
    funext τ k a
    change conj (conj (compAt θ (m.e.symm (m.e (eT.symm τ))) p a k)) = _
    rw [Complex.conj_conj, Equiv.symm_apply_apply]
    rfl
  have hJ' : ∀ y, e (Ker.embR X' y) = Ker.zR X idx x (Ker.embR X y) := fun y => by
    rw [← he₀]
    refine congrArg e₀ ?_
    funext τ k a
    obtain ⟨ρ, rfl⟩ := eT.surjective τ
    change conj ((m.e (eT.symm (eT ρ))).1 (y k a)) = (eT ρ).1 (y k a)
    rw [Equiv.symm_apply_apply, m.e_emb, hS.2.2.2.2.2.2.1, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  let φ : (Fin g → ℂ) → ℝ := fun z => ‖th z‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x z z).re)
  have hφ : Continuous φ := by
    have := hth.1.continuous
    simp only [φ, hx]
    fun_prop
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable A := by
    have : (A : Set (Fin g → ℂ)) ⊆ Set.range (pv X idx x) := fun z hz => by
      obtain ⟨u, -, rfl⟩ := (hAm z).1 hz
      exact ⟨u, rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : (volume : Measure (Fin T.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin S.rank → Fin T.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Ker.WR X' S.rank)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h2 := integral_prod_eq (volume : Measure (Ker.WR X' S.rank)) e hF hφ (fun z => by positivity)
    (fun p hp z => by
      obtain ⟨u, hu, rfl⟩ := (hAm p).1 hp
      exact norm_periodic hsym hx' hth hu z) hm (Γ := Ker.latR X' S.rank (N₀ * N₁)) (fun u hu => by
      induction hu using AddSubgroup.closure_induction with
      | mem u hu =>
        obtain ⟨y, hy, rfl⟩ := hu
        intro b
        have e1 : (N₀ * N₁) • Ker.embR X' y = Ker.embR X' ((N₀ * N₁) • y) := by
          funext τ k a
          simp [Ker.embR]
        rw [e1, hJ', hAm]
        refine ⟨(N₀ * N₁) • y b, ?_, rfl⟩
        rw [mul_smul]
        exact nsmul_mem (hN' _ (hΛ ▸ hy b)) _
      | zero => simp
      | add u u' _ _ hu hu' => exact fun b => by rw [map_add]; exact add_mem (hu b) (hu' b)
      | neg u _ hu => exact fun b => by rw [map_neg]; exact neg_mem (hu b)) hFd
  have h3 := hN Fd hFd (fun u => ((‖a‖ ^ 2 * ∏ b, φ (e u b) : ℝ) : ℂ)) fun p hp => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hfp p hp, norm_mul, mul_pow, norm_sq_gauss_prod, hJ]
  have h4 : Ker.ipO μ 𝓕 f f = 1 := by
    simp only [Ker.ipO, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_complex_ofReal]
    exact_mod_cast h1
  rw [h4, integral_complex_ofReal, integral_const_mul] at h3
  erw [h2] at h3
  have h5 : (1 : ℝ) = (volume Fd).toReal⁻¹ * (‖a‖ ^ 2 * (volume Fd).toReal) := by exact_mod_cast h3
  have h6 : (volume Fd).toReal ≠ 0 := fun h => by simp [h] at h5
  rw [mul_comm, _root_.mul_assoc, mul_inv_cancel₀ h6, _root_.mul_one] at h5
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 h5.symm

end GlobalTheory.OneMapRef.VacUnit

end
