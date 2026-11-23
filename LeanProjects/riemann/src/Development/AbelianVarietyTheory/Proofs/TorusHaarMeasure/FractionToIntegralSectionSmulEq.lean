import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveSec
import Formalism.LocalToGlobal.ProjectiveLattices.CurveInj
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdegStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveLocOfCountQAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimesStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.SectionProduct

section Abstract

variable {K Fr : Type} [Field K] [CommRing Fr] [Algebra K Fr] (J : Ideal Fr)
  {ι : Type} {R : ι → Type} [∀ c, CommRing (R c)] [∀ c, Algebra K (R c)] (φ : ∀ c, Fr →ₐ[K] R c)

theorem map_mem_of_mem_sup {c : ι} {f : Fr} (hf : f ∈ J ⊔ RingHom.ker (φ c)) : φ c f ∈ Ideal.map (φ c) J := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  rw [map_add, (RingHom.mem_ker).1 hb, add_zero]
  exact Ideal.mem_map_of_mem _ ha

theorem exists_sub_mem {c : ι}
    (hloc : ∀ r : R c, ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a) (r : R c) :
    ∃ b : Fr, φ c b - r ∈ Ideal.map (φ c) J := by
  obtain ⟨a, p, hp, he⟩ := hloc r
  have hu : IsUnit (Ideal.Quotient.mk (J ⊔ RingHom.ker (φ c)) p) :=
    LocalUnitReduction.isUnit_mk_of_forall_prime fun Q hQ hIQ => hp Q hQ (le_sup_left.trans hIQ) (le_sup_right.trans hIQ)
  obtain ⟨q', hq⟩ := hu.exists_left_inv
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q'
  have h1 : q * p - 1 ∈ J ⊔ RingHom.ker (φ c) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hq, map_one, sub_self]
  refine ⟨q * a, ?_⟩
  have h2 := Ideal.mul_mem_right r _ (map_mem_of_mem_sup J φ h1)
  have e : φ c (q * a) - r = φ c (q * p - 1) * r := by
    rw [map_sub, map_mul, map_mul, map_one, ← he]; ring
  rwa [e]

theorem exists_forall_sub_mem [Finite ι]
    (hone : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q → RingHom.ker (φ c') ≤ Q → c = c')
    (hloc : ∀ c (r : R c), ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a)
    (r : ∀ c, R c) : ∃ b : Fr, ∀ c, φ c b - r c ∈ Ideal.map (φ c) J := by
  choose b hb using fun c => exists_sub_mem J φ (hloc c) (r c)
  have hcop : Pairwise (Function.onFun IsCoprime fun c => J ⊔ RingHom.ker (φ c)) := by
    intro c c' hcc'
    show IsCoprime (J ⊔ RingHom.ker (φ c)) (J ⊔ RingHom.ker (φ c'))
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hcc' (hone M hM.isPrime ((le_sup_left.trans le_sup_left).trans hle) c c'
      ((le_sup_right.trans le_sup_left).trans hle) ((le_sup_right.trans le_sup_right).trans hle))
  obtain ⟨f, hf⟩ := Ideal.exists_forall_sub_mem_ideal hcop b
  refine ⟨f, fun c => ?_⟩
  have h1 := map_mem_of_mem_sup J φ (hf c)
  have h2 := Ideal.add_mem _ h1 (hb c)
  rwa [map_sub, sub_add_sub_cancel] at h2

theorem exists_equiv_pi [Finite ι] (hinj : ∀ f : Fr, (∀ c, φ c f = 0) → f = 0)
    (hone : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q → RingHom.ker (φ c') ≤ Q → c = c')
    (hloc : ∀ c (r : R c), ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a)
    {M : Type} [AddCommGroup M] [Module Fr M] [Module K M] [IsScalarTower K Fr M] (e0 : M)
    (hs : ∀ m : M, ∃ b : Fr, b • e0 = m) (hk : ∀ b : Fr, b • e0 = 0 ↔ b ∈ J)
    {n : ℕ} (t : Fin n → M) (hli : LinearIndependent K t) (hsp : Submodule.span K (Set.range t) = ⊤) :
    letI : ∀ c, Module K (R c ⧸ Ideal.map (φ c) J) := fun c =>
      ((Ideal.Quotient.mk (Ideal.map (φ c) J)).comp (algebraMap K (R c))).toModule
    (∃ e : M ≃ₗ[K] (∀ c, R c ⧸ Ideal.map (φ c) J),
      ∀ (b : Fr) (c : ι), e (b • e0) c = Ideal.Quotient.mk (Ideal.map (φ c) J) (φ c b)) ∧
    n = ∑ᶠ c, Module.finrank K (R c ⧸ Ideal.map (φ c) J) := by
  letI inst : ∀ c, Module K (R c ⧸ Ideal.map (φ c) J) := fun c =>
    ((Ideal.Quotient.mk (Ideal.map (φ c) J)).comp (algebraMap K (R c))).toModule
  letI : Fintype ι := Fintype.ofFinite ι
  let f : Fr →ₗ[K] M := (LinearMap.toSpanSingleton Fr M e0).restrictScalars K
  let g : Fr →ₗ[K] (∀ c, R c ⧸ Ideal.map (φ c) J) :=
    { toFun := fun b c => Ideal.Quotient.mk (Ideal.map (φ c) J) (φ c b)
      map_add' := fun a b => funext fun c => by simp
      map_smul' := fun k b => funext fun c => by
        show Ideal.Quotient.mk _ (φ c (k • b)) =
          Ideal.Quotient.mk _ (algebraMap K (R c) k) * Ideal.Quotient.mk _ (φ c b)
        rw [map_smul, Algebra.smul_def, map_mul] }
  have hf : Function.Surjective f := hs
  have hg : Function.Surjective g := by
    intro x
    choose r hr using fun c => Ideal.Quotient.mk_surjective (x c)
    obtain ⟨b, hb⟩ := exists_forall_sub_mem J φ hone hloc r
    exact ⟨b, funext fun c => (Ideal.Quotient.eq.2 (hb c)).trans (hr c)⟩
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext b
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    refine (hk b).trans ⟨fun hb => funext fun c => ?_, fun hb => ?_⟩
    · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hb)
    · exact LocalUnitReduction.mem_of_forall_sup_ker J φ hinj hone fun c =>
        LocalUnitReduction.mem_sup_ker J φ (hloc c) (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hb c))
  let e : M ≃ₗ[K] (∀ c, R c ⧸ Ideal.map (φ c) J) :=
    (f.quotKerEquivOfSurjective hf).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ g.quotKerEquivOfSurjective hg
  have he : ∀ b, e (f b) = g b := by
    intro b
    have h1 : (f.quotKerEquivOfSurjective hf).symm (f b) = Submodule.Quotient.mk b := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show g.quotKerEquivOfSurjective hg (Submodule.quotEquivOfEq _ _ hker
      ((f.quotKerEquivOfSurjective hf).symm (f b))) = _
    rw [h1]; rfl
  refine ⟨⟨e, fun b c => congrFun (he b) c⟩, ?_⟩
  let bs : Module.Basis (Fin n) K M := Module.Basis.mk hli hsp.ge
  haveI : Module.Finite K M := Module.Finite.of_basis bs
  haveI : Module.Finite K (∀ c, R c ⧸ Ideal.map (φ c) J) := Module.Finite.equiv e
  haveI : ∀ c, Module.Finite K (R c ⧸ Ideal.map (φ c) J) := fun c =>
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun c => R c ⧸ Ideal.map (φ c) J) c)
      (Function.surjective_eval c)
  rw [finsum_eq_sum_of_fintype, ← Module.finrank_pi_fintype, ← e.finrank_eq, Module.finrank_eq_card_basis bs,
    Fintype.card_fin]

end Abstract

section Record

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {ka wL wF : WeightFamilies.Wt D j}
  (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))

theorem fractionToIntegralSection_smul_eq (b : ↥(Frac0 X la G.w)) (m : SectionSheafQuotient X la G.w wF) : toOsK X la G.w b • m = b • m :=
  algebraMap_smul (OsK X la G.w) b m

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem lwZ_mem (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (z : ↥(HK X la G.w wF))
    (hz : z ∈ Jid X la G.w • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) :
    lwZ X la G.N Ω gF G.w (z : Lw X la G.w) ∈ Ideal.map (phiZ X la G.N Ω gF G.w) (Jid X la G.w) := by
  refine Submodule.smul_induction_on hz (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · have e : ((r • n : ↥(HK X la G.w wF)) : Lw X la G.w) = (r : Lw X la G.w) * (n : Lw X la G.w) := rfl
    rw [e, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem (phiZ X la G.N Ω gF G.w) hr)
  · rw [Submodule.coe_add, map_add]
    exact Ideal.add_mem _ hx hy

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ratio_eq (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (g0 F : B.Cusp j wF)
    (b : ↥(Frac0 X la G.w)) (hb : b • resF G la g0 = resF G la F) :
    Ideal.Quotient.mk (Ideal.map (phiZ X la G.N Ω gF G.w) (Jid X la G.w)) (phiZ X la G.N Ω gF G.w b) *
      Ideal.Quotient.mk (Ideal.map (phiZ X la G.N Ω gF G.w) (Jid X la G.w))
        (lwZ X la G.N Ω gF G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF g0)))) =
      Ideal.Quotient.mk (Ideal.map (phiZ X la G.N Ω gF G.w) (Jid X la G.w))
        (lwZ X la G.N Ω gF G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF F)))) := by
  set x0 := toHK0 X la G.w wF ⟨emb X la G.N (X.inc wF g0), emb_mem_Vw X la G.N wF g0⟩ with hx0
  set x1 := toHK0 X la G.w wF ⟨emb X la G.N (X.inc wF F), emb_mem_Vw X la G.N wF F⟩ with hx1
  have h0 : toA0K X la G.w wF (b • x0 - x1) = 0 := by
    rw [map_sub, map_smul, sub_eq_zero]
    exact hb
  have h1 := lwZ_mem X G la Ω gF _ ((reduction_eq_zero_iff_mem_ideal_smul X la G.w wF _).1 h0)
  have e : ((b • x0 - x1 : ↥(HK X la G.w wF)) : Lw X la G.w) =
      (b : Lw X la G.w) * algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF g0)) -
        algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF F)) := by
    rw [Submodule.coe_sub, Submodule.coe_smul, hx0, hx1, coe_toHK0, coe_toHK0]
    rfl
  rw [e, map_sub, map_mul] at h1
  rw [← map_mul]
  exact Ideal.Quotient.eq.2 h1

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem tie_of {ι : Type} [Finite ι] (Ω : ι → Type) [∀ Z, CommRing (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
    (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) (g0 : B.Cusp j wF)
    (hinj : ∀ f : ↥(Frac0 X la G.w), (∀ Z, phiZ X la G.N (Ω Z) (gF Z) G.w f = 0) → f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 X la G.w), Q.IsPrime → Jid X la G.w ≤ Q → ∀ Z Z',
      RingHom.ker (phiZ X la G.N (Ω Z) (gF Z) G.w) ≤ Q → RingHom.ker (phiZ X la G.N (Ω Z') (gF Z') G.w) ≤ Q → Z = Z')
    (hloc : ∀ Z (r : RZs X la G.N (Ω Z) (gF Z) G.w), ∃ a p : ↥(Frac0 X la G.w),
      (∀ Q : Ideal ↥(Frac0 X la G.w), Q.IsPrime → Jid X la G.w ≤ Q →
        RingHom.ker (phiZ X la G.N (Ω Z) (gF Z) G.w) ≤ Q → p ∉ Q) ∧
      phiZ X la G.N (Ω Z) (gF Z) G.w p * r = phiZ X la G.N (Ω Z) (gF Z) G.w a)
    (hgen : IsGen (OsK X la G.w) (resF G la g0)) (hB : InBasis G la) :
    letI : ∀ Z, Module (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w ⧸
        Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w)) := fun Z =>
      ((Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))).comp
        (algebraMap (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w))).toModule
    (∃ e : SectionSheafQuotient X la G.w wF ≃ₗ[Kp X la G.N] (∀ Z, RZs X la G.N (Ω Z) (gF Z) G.w ⧸
        Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w)),
      ∀ (F : B.Cusp j wF) (Z : ι),
        e (resF G la F) Z * Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
          (lwZ X la G.N (Ω Z) (gF Z) G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF g0)))) =
        Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
          (lwZ X la G.N (Ω Z) (gF Z) G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF F))))) ∧
    G.del = ∑ᶠ Z, Module.finrank (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w ⧸
        Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w)) := by
  have hs : ∀ m : SectionSheafQuotient X la G.w wF, ∃ b : ↥(Frac0 X la G.w), b • resF G la g0 = m := by
    intro m
    obtain ⟨u, hu⟩ := hgen.2 m
    obtain ⟨b, rfl⟩ := toOsK_surjective X la G.w u
    exact ⟨b, (fractionToIntegralSection_smul_eq X G la b _).symm.trans hu⟩
  have hk : ∀ b : ↥(Frac0 X la G.w), b • resF G la g0 = 0 ↔ b ∈ Jid X la G.w := by
    intro b
    rw [← fractionToIntegralSection_smul_eq, ← toOsK_eq_zero_iff]
    refine ⟨fun hb => hgen.1 (hb.trans (zero_smul _ _).symm), fun hb => by rw [hb, zero_smul]⟩
  obtain ⟨⟨e, he⟩, hn⟩ := exists_equiv_pi (Jid X la G.w) (fun Z => phiZ X la G.N (Ω Z) (gF Z) G.w) hinj hone hloc
    (resF G la g0) hs hk (tL G la) hB.1 hB.2
  refine ⟨⟨e, fun F Z => ?_⟩, hn⟩
  obtain ⟨b, hb⟩ := hs (resF G la F)
  have h1 := he b Z
  rw [hb] at h1
  exact (congrArg (· * _) h1).trans (ratio_eq X G la (Ω Z) (gF Z) g0 F b hb)

end Record

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem tieS : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → InBasis G la → TieSSt h j hj hG hT G la g0 := by
  intro D T h j hj hG ka wL wF G hT S g0 la hH hB
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  have hV := GlobalTheory.Reg.genValInj_record D T h j hj hG
  have hC := GlobalTheory.Reg.compSplit_record D T h j hj hG
  obtain ⟨M⟩ := GlobalTheory.T.curveModel_exists_all_primes_allPoints D T h j hj hG hT hV hC
    (fun ka wL wF G => (GlobalTheory.T.birational_of_formRatios_full_trdeg D T h j hj hG ka wL wF G).2) hG ka wL wF G la S g0 hH.1 hH.2.1 hH.2.2.1 hH.2.2.2
  exact tie_of (recPlus h j hj) G la (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z) (fun Z => formsEvR j hG hT Z) g0
    (curveInj h j hj hG hT hV G la) (hone_of h j hj hG hT hC ka wL wF G S g0 la hH)
    (GlobalTheory.curveLoc_of_countQAt D T h j hj hG hT (GlobalTheory.T.countQAtSt_generic_section_primes D T h j hj hG hT) ka wL wF G S g0 la hH) M.isGen hB

end GlobalTheory.SectionProduct
