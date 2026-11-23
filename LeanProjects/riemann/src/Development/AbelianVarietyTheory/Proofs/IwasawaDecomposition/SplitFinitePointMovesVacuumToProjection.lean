import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateModelSameThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassically
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeVacuaTensorCorrespondLine
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.OneMapRef.SplitProj

open GlobalTheory.Ker GlobalTheory.AdTh.SplitClass

variable {D : D7} {S T : HSp D}

theorem span_of_vset {n : ℕ} {Λ : Lt D.host.E n} (h : Λ ∈ Vset D.host.E n 1) :
    Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤ :=
  DualFamily.span_eq_top Λ h.1 fun x => (h.2.1 x).2

theorem exists_selfDualC (hS : S.gram = 1) {Λ : Lt D.host.E S.rank} (h : Λ ∈ Vset D.host.E S.rank 1) :
    ∃ ΛS : Lt D.host.E S.rank, IsSelfDualC S ΛS ∧ ∀ v, v ∈ Λ ↔ star v ∈ ΛS := by
  obtain ⟨ΛS, h1⟩ := exists_conj Λ
  have h1' : ∀ v, v ∈ ΛS ↔ star v ∈ Λ := h1
  have hfg := GlobalTheory.AdTh.LatOf.fg_of_star h.1 h1'
  have hU := (GenLatCmp.unimod_iff Λ).2 h.2.1
  have key : ∀ y : Fin S.rank → D.host.E, y ∈ ΛS ↔
      ∀ x ∈ ΛS, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * S.gram i j * y j := by
    intro y
    have e : ∀ x : Fin S.rank → D.host.E,
        ∑ i, ∑ j, star (x i) * S.gram i j * y j = ∑ j, star ((star y) j) * (star x) j := by
      intro x
      simp [hS, Matrix.one_apply, mul_comm]
    have hy : star y ∈ Λ ↔ ∀ w ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ j, star ((star y) j) * w j := hU (star y)
    rw [h1', hy]
    simp only [e]
    constructor
    · intro H x hx
      exact H _ ((h1' x).1 hx)
    · intro H w hw
      have := H (star w) ((h1' _).2 (by rwa [star_star]))
      rwa [star_star] at this
  refine ⟨ΛS, ⟨⟨hfg, ?_⟩, key⟩, fun v => by rw [h1', star_star]⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha, h2⟩ := GlobalTheory.AdLat.cap_exists_denom Λ (span_of_vset h) (star x)
  have h3 : a • x ∈ ΛS := (h1' _).2 (by rwa [star_nsmul])
  rw [← Nat.cast_smul_eq_nsmul D.host.E] at h3
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 ha.ne')).1 (Submodule.subset_span h3)

open scoped ComplexOrder in
theorem cartan_one (hS : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by
    unfold gramAt
    rw [hS]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

theorem fmtC_mul (V : HSp D) (g g' : GA D V) : fmtC V (g * g') = fmtC V g * fmtC V g' := by
  simp only [fmtC, Formalism.L2.Theta.cM, AdelicLatMove.mt_mul, Matrix.map_mul]

theorem fmtC_one (V : HSp D) : fmtC V 1 = 1 := by
  simp only [fmtC, Formalism.L2.Theta.cM, AdelicLatMove.mt_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, AdelicLatMove.mt_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _)]

theorem finW_sub (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : finW S T (y - y') = finW S T y - finW S T y' :=
  map_sub (LatTens.gen S T 1) y y'

theorem good (C : Ctx S T) {w : D.host.E} (hw : IsIntegral ℤ w) (hw1 : w + cc w = 1) {L : Lt D.host.E T.rank}
    (hL : SelfD C.X L) {Λ : Lt D.host.E S.rank} (h : Λ ∈ Vset D.host.E S.rank 1) :
    TensVac.Good C.X w (tens Λ L) := by
  obtain ⟨a1, a2, a3, -⟩ := TensLat.tens_selfDual_semichar_index _ _ C.X C.g C.bas C.idx _ C.sympl C.even _
    hw hw1 L hL 1 _ h
  exact ⟨a1, a2, a3⟩

theorem th_sum (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {ι : Type} (s : Finset ι)
    {φ : ι → TF S.rank C.g} (h : ∀ i, GlobalTheory.SW.IsSB (φ i)) {v : TF S.rank C.g} (hv : GlobalTheory.SW.IsSB v) :
    GlobalTheory.SW.IsSB (∑ i ∈ s, φ i) ∧ C.Th x (∑ i ∈ s, φ i) = ∑ i ∈ s, C.Th x (φ i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h1 := TensVac.sb_smul 0 hv
    have h2 := (Ctx.th_laws D S T C x hx v hv).2.1 0
    rw [zero_smul] at h1 h2
    rw [zero_smul] at h2
    exact ⟨h1, h2⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih.2]
    exact ⟨(GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ _ _ (h i) ih.1).1, ((Ctx.th_laws D S T C x hx _ (h i)).1 _ ih.1).1⟩

theorem step (C : Ctx S T) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO C.ψ S T χS χT om) (hS : S.SigOK) (hT : T.SigOK) {w : D.host.E} (hw : IsIntegral ℤ w)
    (hw1 : w + cc w = 1) (hw2 : IdemTwo w) {B : C.Bas} (hB : C.IsB B) {LT L : Lt D.host.E T.rank}
    (hLT : IsSelfDualC T LT) (hL : SelfD C.X L) (hA : IsAA L LT) {Λ Λ₁ : Lt D.host.E S.rank}
    (hΛ : Λ ∈ Vset D.host.E S.rank 1) (hΛ₁ : Λ₁ ∈ Vset D.host.E S.rank 1) {e : AE D} (he : IsSplitIdem D e)
    {h : GA D S} (hh : SuppAt e S h) {y : (AE D)ˣ} (hy : IsDetAt e S h y) (hm : IsMov (fmtC S h) Λ Λ₁)
    {v : TF S.rank C.g} (hv : IsVac C.X C.bas w (tens Λ L) v) (κ : ℂ) :
    om (h, 1) (C.Th (C.xB B) (κ • v)) = C.Th (C.xB B)
      ((((χT y : Circle) : ℂ)⁻¹ * (Real.sqrt ((tens Λ L).relIndex (tens Λ₁ L) : ℝ) : ℂ)) •
        projA C.X C.bas w (tens Λ₁ L) (κ • v)) := by
  have g0 := good C hw hw1 hL hΛ
  have g1 := good C hw hw1 hL hΛ₁
  obtain ⟨ΛS, d0, s0⟩ := exists_selfDualC C.m.gS hΛ
  obtain ⟨ΛS₁, d1, s1⟩ := exists_selfDualC C.m.gS hΛ₁
  have l0 := LatTens.latO_eq_hatA D S T C ΛS Λ LT L s0 hA
  have l1 := LatTens.latO_eq_hatA D S T C ΛS₁ Λ₁ LT L s1 hA
  obtain ⟨-, hx, hc, -⟩ := (onBasis_frame_period D S T C).2 B hB
  have hLs := TensLat.span_of_selfD C.X hL
  obtain ⟨-, r0, -⟩ := HatLat.hatA_tens D S T C Λ L ⟨hΛ.1, span_of_vset hΛ⟩ ⟨hL.1, hLs⟩
  obtain ⟨-, r1, a1, -⟩ := HatLat.hatA_tens D S T C Λ₁ L ⟨hΛ₁.1, span_of_vset hΛ₁⟩ ⟨hL.1, hLs⟩
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D C.ψ C.θ C.std C.inf S T (fun _ => 1) (C.sB B) hS hT
    (cartan_one C.m.gS) (fun τ => (hc τ).1) ΛS LT d0 hLT
  obtain ⟨t, ht⟩ := (latVac_th_line D S T C w hw hw1 hw2 1 Λ hΛ L hL).2 B hB v hv f hf.2.theta hf.2.fock
    (l0 ▸ hf.2.lat)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    subst ht
    obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
    have := hn p hp
    simp [nrm2] at this
  obtain ⟨v₁, hv₁, -⟩ := g1.vac C.sympl
  have hidx : (tens Λ L).relIndex (tens Λ₁ L) ≠ 0 := by
    intro h0
    have := g1.overlap C.idx C.sympl C.even g0 hv₁ hv
    rw [h0, Nat.cast_zero, zero_mul] at this
    exact zero_ne_one this
  have : ((tens Λ L).addSubgroupOf (tens Λ₁ L)).FiniteIndex := ⟨hidx⟩
  haveI := Fintype.ofFinite (tens Λ₁ L ⧸ (tens Λ L).addSubgroupOf (tens Λ₁ L))
  obtain ⟨R, hR, hRu⟩ := exists_reps (tens Λ L) (fun z => z ∈ tens Λ₁ L) Finset.univ
    (fun q : tens Λ₁ L ⧸ (tens Λ L).addSubgroupOf (tens Λ₁ L) => (q.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))
    fun z hz => ⟨QuotientAddGroup.mk ⟨z, hz⟩, Finset.mem_univ _,
      AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq_iff_sub_mem.1 (QuotientAddGroup.out_eq'
        (QuotientAddGroup.mk ⟨z, hz⟩ : tens Λ₁ L ⧸ (tens Λ L).addSubgroupOf (tens Λ₁ L))).symm)⟩
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.AdTh.VacProj.proj_eq C.idx C.sympl C.even g1 g0 hv R hR hRu
  have hc0 : (0 : ℝ) < R.card := by rw [c1]; exact Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx)
  have hc0' : (R.card : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hsq : (Real.sqrt (R.card : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hc0).ne'
  have hp := (g1.proj C.idx C.sympl C.even hv.1 hv₁).1
  have lin := fun φ hφ => (Ctx.th_laws D S T C _ hx φ hφ).2.1
  have hG : ∑ z ∈ R, epsW C.X w z • heisO C.ψ S T (finW S T (-z)) f = C.Th (C.xB B)
      ((t * (Real.sqrt (R.card : ℝ) : ℂ)) • (Real.sqrt (R.card : ℝ) : ℂ) • projA C.X C.bas w (tens Λ₁ L) v) := by
    have hsb : ∀ z, GlobalTheory.SW.IsSB (epsW C.X w z • heisG C.X C.bas z v) := fun z =>
      TensVac.rho_sb C.idx C.sympl C.even z hv.1
    obtain ⟨u1, u2⟩ := th_sum C hx R hsb hv.1
    rw [c2, smul_smul, smul_smul, mul_assoc t, ← Complex.ofReal_mul, Real.mul_self_sqrt hc0.le,
      Complex.ofReal_natCast, mul_inv_cancel_right₀ hc0', lin _ u1, u2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have h1 := (Ctx.th_laws D S T C _ hx v hv.1).2.2.1 (-z)
    rw [neg_neg] at h1
    rw [lin (heisG C.X C.bas z v) (GlobalTheory.SW.heisS_laws _ _ _ _ v hv.1).1, ← h1, ht, GlobalTheory.SplitScalar.heisO_smul, smul_comm]
  have hN : hatA S T (tens Λ₁ L) ≤ (hatA S T (tens Λ L)).comap
      (nsmulAddMonoidHom ((tens Λ L).relIndex (tens Λ₁ L))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, z, hz, rfl⟩
    exact AddSubgroup.subset_closure ⟨α, hα, _, AddSubgroup.nsmul_relIndex_mem _ hz,
      (map_nsmul (LatTens.gen S T α) _ z).symm⟩
  have hone : IsMov (fmt T 1) L L := by
    rw [fmt_one]; exact (isMov_laws D _ L ⟨hL.1, hLs⟩).2.1
  have hom := om_eq_smul_sum hW C.inf hS hT (cartan_one C.m.gS) (fun τ => (hc τ).1) d0 d1 hLT he hh hy l0.symm l1.symm
    (GlobalTheory.TensLatMove.hatA_move D S T C h 1 Λ Λ₁ L L hm hone).1 hf R
    (fun z => finW S T (-z)) (epsW C.X w) (fun z hz => (r1 _).2 (neg_mem (hR z hz))) (fun z _ => norm_epsW C.X _ z)
    (fun u hu => by
      obtain ⟨z, hz, u', hu', rfl⟩ := (a1 u hu).2 _ (Nat.pos_of_ne_zero hidx)
      obtain ⟨z', ⟨hz', h3⟩, -⟩ := hRu _ (neg_mem hz)
      refine ⟨z', hz', ?_⟩
      rw [add_sub_right_comm, ← finW_sub]
      refine add_mem ((r0 _).2 ?_) (hN hu')
      convert neg_mem h3 using 1
      abel)
    (fun z hz z' hz' hm => by
      rw [← finW_sub, r0, neg_sub_neg, ← neg_sub, neg_mem_iff] at hm
      exact (hRu z (hR z hz)).unique ⟨hz, by rw [sub_self]; exact zero_mem _⟩ ⟨hz', hm⟩)
    (fun F hF hFl z hz => by
      have := (SignVac.isLatVac_iff D S T C w hw hw1 hw2 1 Λ₁ hΛ₁ L hL F hF).1 hFl _ (neg_mem (hR z hz))
      rwa [epsW_neg] at this)
    (by
      rw [hG]
      refine ((latVac_th_line D S T C w hw hw1 hw2 1 Λ₁ hΛ₁ L hL).1 _ hx _ (TensVac.sb_smul _ c3.1)).2 fun z hz => ?_
      rw [TensVac.heisG_smul, smul_comm, c3.2.2 z hz])
  rw [hG, ht, map_smul, lin _ c3.1, lin _ hp, smul_smul, smul_smul] at hom
  rw [projA_smul C.idx C.sympl C.even g1 _ hv.1, smul_smul, lin _ hp, lin _ hv.1, map_smul,
    ← inv_smul_smul₀ ht0 (om (h, 1) _), hom, smul_smul, smul_smul, ← c1]
  congr 1
  field_simp

open GlobalTheory.AdLat in

theorem mov_split {V : HSp D} {e : AE D} (he : IsSplitIdem D e) {h h' : GA D V}
    (h1 : (e + cA D e) • Formalism.L2.Theta.mt V h' = (e + cA D e) • 1)
    (h2 : (1 - (e + cA D e)) • Formalism.L2.Theta.mt V h' = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V h)
    {Λ₀ Λ' Λ₁ : Lt D.host.E V.rank} (v0 : Λ₀ ∈ Vset D.host.E V.rank 1) (v' : Λ' ∈ Vset D.host.E V.rank 1)
    (v1 : Λ₁ ∈ Vset D.host.E V.rank 1) (m' : IsMov (fmtC V h') Λ₀ Λ') (m : IsMov (fmtC V h) Λ₀ Λ₁) :
    ∀ v ∈ Λ', ∃ x, x ∈ Λ₀ ∧ x ∈ Λ' ∧ v - x ∈ Λ₁ := by
  intro v hv
  have hc : cA D (e + cA D e) = e + cA D e := by rw [RingHom.map_add, cA_cA, add_comm]
  obtain ⟨-, -, p, ε, ⟨α, rfl, a1, a0⟩, h3⟩ := he
  have hα : ∀ q, α q ∈ q.adicCompletionIntegers D.host.F := fun q => by
    by_cases hq : q = p
    · subst hq
      have : α q = 1 := a1
      rw [this]; exact one_mem _
    · have : α q = 0 := a0 q hq
      rw [this]; exact zero_mem _
  have ht : finPart D (e + cA D e) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by rw [h3]; rfl
  generalize e + cA D e = t at h1 h2 ht hc
  have hst : ∀ (L : Lt D.host.E V.rank), ∀ z ∈ hatV L, finPart D t • z ∈ hatV L :=
    fun L z hz => by rw [ht]; exact tmul_smul_mem _ hα hz
  have hv' : toAf v ∈ hatV Λ' := cap_fv_mem D.host.F _ v hv
  obtain ⟨u, hu, e0⟩ := (m' _).1 hv'
  have key : ∀ (s : AE D) (k k' : GA D V), cA D s = s → s • Formalism.L2.Theta.mt V k = s • Formalism.L2.Theta.mt V k' →
      finPart D s • fmtC V k *ᵥ u = fmtC V k' *ᵥ (finPart D s • u) := fun s k k' hs hM => by
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec]
    congr 1
    ext i j
    have := congrArg (fun a => finPart D (cA D a)) (congrFun (congrFun hM i) j)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hs] at this
    exact this
  refine exists_split (F := D.host.F) ⟨v0.1, span_of_vset v0⟩ ⟨v'.1, span_of_vset v'⟩ ⟨v1.1, span_of_vset v1⟩
    (z := finPart D t • toAf v) ?_ (hst _ _ hv') ?_
  · rw [e0, key t h' 1 hc (by rw [h1, AdelicLatMove.mt_one]), fmtC_one, Matrix.one_mulVec]
    exact hst _ _ hu
  · have e1 : toAf v - finPart D t • toAf v = finPart D (1 - t) • toAf v := by
      rw [RingHom.map_sub, RingHom.map_one, sub_smul, one_smul]
    have e2 : finPart D (1 - t) • u ∈ hatV Λ₀ := by
      rw [RingHom.map_sub, RingHom.map_one, sub_smul, one_smul]
      exact sub_mem hu (hst _ _ hu)
    change toAf v - finPart D t • toAf v ∈ hatV Λ₁
    rw [e1, e0, key _ h' h (by rw [RingHom.map_sub, RingHom.map_one, hc]) h2]
    exact (m _).2 ⟨_, e2, rfl⟩

theorem om_th (C : Ctx S T) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO C.ψ S T χS χT om) (hS : S.SigOK) (hT : T.SigOK) {w : D.host.E} (hw : IsIntegral ℤ w)
    (hw1 : w + cc w = 1) (hw2 : IdemTwo w) {B : C.Bas} (hB : C.IsB B) {LT L : Lt D.host.E T.rank}
    (hLT : IsSelfDualC T LT) (hL : SelfD C.X L) (hA : IsAA L LT) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) {h : GA D S} (hsupp : SuppAt e S h) {y : (AE D)ˣ} (hdet : IsDetAt e S h y)
    {Λ₁ : Lt D.host.E S.rank} (hΛ₁ : Λ₁ ∈ Vset D.host.E S.rank 1) (hm : IsMov (fmtC S h) (stdL D.host.E S.rank) Λ₁)
    {v : TF S.rank C.g} (hv : IsVac C.X C.bas w (tens (stdL D.host.E S.rank) L) v) (κ : ℂ) :
    om (h, 1) (C.Th (C.xB B) (κ • v)) = C.Th (C.xB B)
      ((((χT y : Circle) : ℂ)⁻¹ * (Real.sqrt ((tens (stdL D.host.E S.rank) L).relIndex (tens Λ₁ L) : ℝ) : ℂ)) •
        projA C.X C.bas w (tens Λ₁ L) (κ • v)) := by
  have hSv : stdL D.host.E S.rank ∈ Vset D.host.E S.rank 1 := Base.stdL_mem_Vset S.rank 1
  obtain ⟨-, m1, -, laws⟩ := isMov_laws D _ _ ⟨hSv.1, span_of_vset hSv⟩
  have hinv : ∀ k : GA D S, fmtC S k * fmtC S k⁻¹ = 1 := fun k => by rw [← fmtC_mul, mul_inv_cancel, fmtC_one]
  have hgood := fun Λ => @good D S T C w hw hw1 L hL Λ
  obtain ⟨ι, Q, es, h1, h2, rfl⟩ := PlaceModelSum.isOrthSum_of_isIdemSum he
  have h3 := he.2
  clear he
  induction Q using Finset.induction_on generalizing h y Λ₁ with
  | empty =>
    rw [Finset.sum_empty] at hsupp hdet
    obtain rfl : h = 1 := mt_inj (by
      have := (suppAt_iff _ _ _).1 hsupp
      rw [RingHom.map_zero, add_zero, zero_smul, eq_comm, sub_eq_zero] at this
      exact this)
    obtain rfl : y = 1 := Units.ext (by
      have : (y : AE D) = _ := hdet
      rw [this, zero_mul, zero_add, sub_zero, Units.val_one])
    rw [fmtC_one] at hm
    obtain rfl : Λ₁ = stdL D.host.E S.rank := ((laws 1 1 (one_mul _)).2 _ hSv.1 m1).2.2.1 _ hΛ₁.1 hm
    rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, AddSubgroup.relIndex_self, map_one,
      projA_smul C.idx C.sympl C.even (hgood _ hSv) _ hv.1, projA_vac C.idx C.sympl C.even (hgood _ hSv) hv]
    simp
  | insert i Q hi ih =>
    rw [Finset.sum_insert hi] at hsupp hdet h3
    have hsp := h1 i (Finset.mem_insert_self _ _)
    have h1' : ∀ j ∈ Q, IsSplitIdem D (es j) := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h2' : ∀ j ∈ Q, ∀ k ∈ Q, k ≠ j → es j * es k = 0 := fun j hj k hk =>
      h2 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have o4 : (∑ j ∈ Q, es j) * (∑ j ∈ Q, es j) = ∑ j ∈ Q, es j :=
      PlaceModelSum.IsOrthSum.idem ⟨ι, Q, es, h1', h2', rfl⟩
    have o7 : es i * ∑ j ∈ Q, es j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => h2 i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        fun hji => hi (hji ▸ hj)
    set a := es i with ha
    set a' := ∑ j ∈ Q, es j with ha'
    have o1 : a * a = a := hsp.1
    have o3 : a * cA D a = 0 := hsp.2.1
    have o2 : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, o1]
    have o5 : cA D a' * cA D a' = cA D a' := by rw [← RingHom.map_mul, o4]
    have o8 : cA D a * cA D a' = 0 := by rw [← RingHom.map_mul, o7, RingHom.map_zero]
    rw [RingHom.map_add] at h3
    have o9 : a * cA D a' = 0 := by
      linear_combination (a * cA D a') * h3 - (cA D a' * (cA D a + cA D a')) * o1 -
        (cA D a' * (cA D a + cA D a')) * o7 - a * o8 - a * o5
    have o10 : cA D a * a' = 0 := by
      have := congrArg (cA D) o9
      rwa [RingHom.map_mul, cA_cA, RingHom.map_zero] at this
    have o6 : a' * cA D a' = 0 := by linear_combination h3 - o3 - o9 - o10
    have hε : (a + cA D a) * (a + cA D a) = a + cA D a := by linear_combination o1 + o2 + 2 * o3
    have hcε : cA D (a + cA D a) = a + cA D a := by rw [RingHom.map_add, cA_cA, add_comm]
    obtain ⟨h₀, e₀⟩ := exists_part S hε hcε h
    obtain ⟨h', e'⟩ := exists_part S (ε := 1 - (a + cA D a)) (by linear_combination hε)
      (by rw [RingHom.map_sub, RingHom.map_one, hcε]) h
    have hsupp' := (suppAt_iff _ _ _).1 hsupp
    rw [RingHom.map_add] at hsupp'
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := alg_parts o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 hsupp' e₀ e'
    obtain ⟨y₀, hy₀⟩ := exists_detAt S o1 h₀
    obtain ⟨y', hy'⟩ := exists_detAt S o4 h'
    obtain rfl : y = y₀ * y' := Units.ext (by
      rw [Units.val_mul, show (y : AE D) = _ from hdet, show (y₀ : AE D) = _ from hy₀, show (y' : AE D) = _ from hy', b4])
    obtain ⟨⟨Λ', hf', m'⟩, law⟩ := laws _ _ (hinv h')
    have hΛ' : Λ' ∈ Vset D.host.E S.rank 1 := MovLev.mem_Vset C (h := h') (fun p hp => by
      rw [Nat.cast_one, Ideal.span_singleton_one, top_le_iff] at hp
      exact (p.isPrime.ne_top hp).elim) hf'.1 m'
    have hle := tens_le L (mov_split hsp b5 b6 hSv hΛ' hΛ₁ m' hm)
    clear e₀ e' b4 b5 b6 hsupp' hsupp hdet
    obtain rfl : h = h₀ * h' := mt_inj (b1.trans (AdelicLatMove.mt_mul S h₀ h').symm)
    have ih' := ih hΛ' m' h1' h2' ((suppAt_iff _ _ _).2 b3) hy' o6
    have m₀ : IsMov (fmtC S h₀) Λ' Λ₁ := by
      have := (((isMov_laws D _ _ hf').2.2.2 _ _ (hinv h'⁻¹)).2 _ hSv.1 (law _ hf'.1 m').2.1).2.2.2.1 _ _ hm
      rwa [← fmtC_mul, mul_inv_cancel_right] at this
    obtain ⟨b, hb, -⟩ := (hgood _ hΛ').vac C.sympl
    have hc := step C hW hS hT hw hw1 hw2 hB hLT hL hA hΛ' hΛ₁ hsp ((suppAt_iff _ _ _).2 b2) hy₀ m₀ hb
      ((((χT y' : Circle) : ℂ)⁻¹ * (Real.sqrt ((tens (stdL D.host.E S.rank) L).relIndex (tens Λ' L) : ℝ) : ℂ)) *
        SW.ip (κ • v) b)
    rw [mul_smul _ (SW.ip (κ • v) b), ← ((hgood _ hΛ').proj C.idx C.sympl C.even (TensVac.sb_smul κ hv.1) hb).2, ← ih',
      proj_step C.idx C.sympl C.even (hgood _ hSv) (hgood _ hΛ') (hgood _ hΛ₁) hle hv] at hc
    rw [show ((h₀ * h', 1) : GA D S × GA D T) = (h₀, 1) * (h', 1) from Prod.ext rfl (mul_one _).symm, map_mul,
      map_mul, Circle.coe_mul, mul_inv]
    exact hc

theorem zak_om_split : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → GlobalTheory.Ker.IdemTwo w → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ (LT : Lt D.host.E T.rank) (L : Lt D.host.E r), IsSelfDualC T LT → SelfD X L → GlobalTheory.Ker.IsAA (latW hr L) LT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ h ∈ GfC S, SuppAt e S h → ∀ x : (AE D)ˣ, IsDetAt e S h x → ∀ Λ ∈ Vset D.host.E S.rank 1, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC S h) (stdL D.host.E S.rank) Λ → ∀ v : TF S.rank g, IsVac X bas w (tens (stdL D.host.E S.rank) L) v → ∀ (t : ℂ) (f : WO S T → ℂ), Zak ψ θ hr eT bas idx (frOf hr eT Z) (t • v) f → Zak ψ θ hr eT bas idx (frOf hr eT Z) ((t * (((χT x)⁻¹ : Circle) : ℂ) * ((Real.sqrt (((((Λ ⊓ stdL D.host.E S.rank).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index ^ r : ℕ) : ℝ)) : ℝ) : ℂ)) • projA X bas w (tens Λ L) v) (om (h, 1) f) := by
  intro D S T r g hr ψ θ X eT bas idx hS kS kT χS χT om hW w hw hw1 hw2 Z hZ LT L hLT hL hA e P he h _ hsupp x hdet
    Λ hΛ hm v hv t f hf
  subst hr
  obtain ⟨X', m, hq', bas', idx', hs', π, -, hEF, hh, hfr⟩ :=
    GlobalTheory.T.exists_conjugateModel_same_thetaFunctions D S T _ g rfl ψ θ X eT bas idx hS _ (Nat.add_sub_cancel' X.p0_le)
  obtain ⟨hB, hz⟩ := hfr Z
  obtain ⟨-, hz, -⟩ := hz hZ
  replace hB := hB.1 hZ
  replace hEF : ∀ u v, EF X' u v = EF X u v := hEF
  replace hh : ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (φ : TF S.rank g),
    heisG X' bas' y φ = heisG X bas y φ := hh
  have hE : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, SW.epsW X' w y = SW.epsW X w y := fun y => by
    simp only [SW.epsW, hEF]
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs' with hC
  have hL' : SelfD C.X L := by
    refine ⟨hL.1, fun u => (hL.2 u).trans ?_⟩
    change _ ↔ ∀ y ∈ L, ∃ k : ℤ, EF X' u y = k
    simp only [hEF]
  have hv' : IsVac C.X C.bas w (tens (stdL D.host.E S.rank) L) v := by
    refine ⟨hv.1, hv.2.1, fun y hy => ?_⟩
    change SW.epsW X' _ y • heisG X' bas' y v = v
    rw [hE, hh]
    exact hv.2.2 y hy
  have hp : projA C.X C.bas w (tens Λ L) v = projA X bas w (tens Λ L) v := by
    change projA X' bas' w (tens Λ L) v = _
    simp only [projA, hE, hh]
  have hx := ((onBasis_frame_period D S T C).2 _ hB).2.1
  have g1 := good C hw hw1 hL' hΛ
  obtain ⟨b, hb, -⟩ := g1.vac C.sympl
  have key := om_th C hW kS kT hw hw1 hw2 hB hLT hL' hA he hsupp hdet hΛ hm hv' t
  obtain ⟨-, -, -, -, -, a4⟩ := TensLat.tens_selfDual_semichar_index _ _ C.X C.g C.bas C.idx _ C.sympl C.even _
    hw hw1 L hL' 1 _ hΛ
  have hi : ((Λ ⊓ stdL D.host.E S.rank).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index ^ T.rank =
      (tens (stdL D.host.E S.rank) L).relIndex (tens Λ L) := by
    rw [a4 _ (Base.stdL_mem_Vset S.rank 1), ← AddSubgroup.inf_relIndex_left]
    rfl
  rw [← (ZakEx.isZak_Th D S T C _ hx _ (TensVac.sb_smul t hv.1)).2 f ((hz _ _).2 hf),
    projA_smul C.idx C.sympl C.even g1 _ hv.1, smul_smul] at key
  rw [← hz, key, hi, ← hp, Circle.coe_inv, mul_assoc, mul_comm t]
  exact (ZakEx.isZak_Th D S T C _ hx _ (TensVac.sb_smul _ (g1.proj C.idx C.sympl C.even hv.1 hb).1)).1

end GlobalTheory.OneMapRef.SplitProj
