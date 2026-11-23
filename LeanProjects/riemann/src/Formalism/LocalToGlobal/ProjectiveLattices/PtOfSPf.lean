import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import Formalism.LocalToGlobal.ProjectiveLattices.CurveInj
import Formalism.LocalToGlobal.ProjectiveLattices.CurveUnit
import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPfBC

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

theorem pos_factor {K' Fr R L : Type} [Field K'] [CommRing Fr] [CommRing R] [Field L] [Algebra K' Fr] [Algebra K' R]
    [Algebra K' L] (φZ : Fr →ₐ[K'] R) (ψ : Fr →ₐ[K'] L) (hker : ∀ f, φZ f = 0 → ψ f = 0)
    (hloc : ∀ r, ∃ a p, ψ p ≠ 0 ∧ φZ p * r = φZ a) : ∃ χ : R →ₐ[K'] L, ∀ f, χ (φZ f) = ψ f := by
  classical
  choose a p hp hr using hloc
  have key : ∀ r a' p', ψ p' ≠ 0 → φZ p' * r = φZ a' → ψ (a r) / ψ (p r) = ψ a' / ψ p' := by
    intro r a' p' hp' hr'
    have h0 : φZ (a r * p' - a' * p r) = 0 := by
      rw [map_sub, map_mul, map_mul, ← hr r, ← hr']
      ring
    have h1 := hker _ h0
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
    rw [div_eq_div_iff (hp r) hp', h1]
  let χf : R → L := fun r => ψ (a r) / ψ (p r)
  have hχ : ∀ r a' p', ψ p' ≠ 0 → φZ p' * r = φZ a' → χf r = ψ a' / ψ p' := key
  refine ⟨{ toFun := χf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ }, ?_⟩
  · rw [hχ 1 1 1 (by simp) (by simp)]
    simp
  · intro r s
    rw [hχ (r * s) (a r * a s) (p r * p s) (by rw [map_mul]; exact mul_ne_zero (hp r) (hp s))
      (by rw [map_mul, map_mul, ← hr r, ← hr s]; ring)]
    simp only [χf, map_mul]
    rw [mul_div_mul_comm]
  · rw [hχ 0 0 1 (by simp) (by simp)]
    simp
  · intro r s
    rw [hχ (r + s) (a r * p s + a s * p r) (p r * p s) (by rw [map_mul]; exact mul_ne_zero (hp r) (hp s))
      (by simp only [map_add, map_mul]; rw [← hr r, ← hr s]; ring)]
    simp only [χf, map_add, map_mul]
    rw [div_add_div _ _ (hp r) (hp s)]
    ring
  · intro k
    show χf (algebraMap K' R k) = algebraMap K' L k
    rw [hχ _ (algebraMap K' Fr k) 1 (by simp) (by simp)]
    simp
  · intro f
    show χf (φZ f) = ψ f
    rw [hχ _ f 1 (by simp) (by simp)]
    simp

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pos_dualMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem pos_frMap_trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] {φ : S →ₐ[c.F] T} {ψ : T →ₐ[c.F] U} {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom := by
    show Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp φ.toRingHom)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, esp, CategoryTheory.Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, ← CategoryTheory.Category.assoc]
    congr 1
    show _ = Spec.map (CommRingCat.ofHom (dualMap (ψ.toRingHom.comp φ.toRingHom)))
    rw [pos_dualMap_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  · rw [CategoryTheory.Category.assoc, hs1, hs2]
  · rw [CategoryTheory.Category.assoc, hf1, ← CategoryTheory.Category.assoc, hf2, esp, CategoryTheory.Category.assoc]
  · intro i h
    have h1' := pos_ppx_le pm1 hs1 i
    have h2' := pos_ppx_le pm2 hs2 i
    have e : (pm2 ≫ pm1).appLE _ _ h = pm1.appLE _ _ h1' ≫ pm2.appLE _ _ h2' :=
      (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1' h2').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ha1 i h1', ha2 i h2']

theorem pos_evR (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁)
    (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', pos_frMap_trans hy' hm⟩
  unfold evR evalAt
  rw [dif_pos hT2, dif_pos hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (pos_frMap_trans hT1.choose_spec.choose_spec.choose_spec hm)

end Gen

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) {Ω : Type} [Field Ω] [Algebra B.KO Ω]
  (gF : X.Forms →ₐ[B.KO] Ω) {L : Type} [Field L] [Algebra (Kp X la N) L] (χ : RZs X la N Ω gF w →ₐ[Kp X la N] L)

theorem pos_psiZ_alg (a : B.KO) :
    CurveLoc.psiZ X la N w gF (algebraMap B.KO Ω a) = algebraMap (Kp X la N) (RZs X la N Ω gF w)
      (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) := by
  rw [CurveLoc.psiZ_apply]
  have e1 : ((1 : X.Kl la) ⊗ₜ[B.KO] algebraMap B.KO Ω a : X.Kl la ⊗[B.KO] Ω) =
      algebraMap B.KO (X.Kl la) a ⊗ₜ[B.KO] (1 : Ω) := by
    rw [Algebra.algebraMap_eq_smul_one (A := Ω), Algebra.algebraMap_eq_smul_one (A := X.Kl la), ← TensorProduct.smul_tmul]
  rw [e1, CurveLoc.tmul_eq, one_mul, IsScalarTower.algebraMap_apply (Kp X la N) (RZ X la N Ω) (RZs X la N Ω gF w),
    Algebra.algebraMap_eq_smul_one (A := RZ X la N Ω)]
  rfl

theorem pos_inv :
    χ (CurveLoc.invS X la N w gF) = (χ (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w)
      (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))))⁻¹ := by
  have e := congrArg χ (CurveLoc.weight_zero_section_mul_inv X la N w gF)
  rw [map_mul, map_one] at e
  exact eq_inv_of_mul_eq_one_right e

theorem pos_sec_ne :
    χ (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) ≠ 0 := by
  have e := congrArg χ (CurveLoc.weight_zero_section_mul_inv X la N w gF)
  rw [map_mul, map_one] at e
  exact left_ne_zero_of_mul_eq_one e

theorem pos_sec_eval :
    χ (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) =
      ∑ k, algebraMap (Kp X la N) L (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) *
        χ (CurveLoc.psiZ X la N w gF (gF (X.inc wL (w k)))) := by
  have e : rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) =
      ∑ k, (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) • rzMap X la N Ω gF (emb X la N (X.inc wL (w k))) := by
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    rw [map_sum]
    simp only [map_smul]
  refine (congrArg (fun v => χ (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) v)) e).trans ?_
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, map_mul, map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes,
    CurveLoc.alg_rzMap_emb]

theorem phi_fraction_base_value (k : ℕ) (F : X.Forms) (hF : emb X la N F ∈ Vw X la N (addL (wt0 D j) wL k)) :
    χ (phiZ X la N Ω gF w (fr0 X la w k ⟨emb X la N F, hF⟩)) =
      χ (CurveLoc.psiZ X la N w gF (gF F)) *
        (χ (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))))⁻¹ ^ k := by
  rw [CurveLoc.phiZ_of_eq X la N w gF _ k _ rfl, map_mul, map_pow, CurveLoc.alg_rzMap_emb, pos_inv]

end Rec

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

theorem pos_natural {u : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j u) :
    IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) (F : T.R j) :=
  (cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j u F.2)).1

theorem pos_birAt (hFT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (hB : BIRSt h j hj hG G) (Z : Comp (T.Q.Xo j) T.Q.c) :
    CurveLoc.BirAt (recPlus h j hj) G.N G.w (formsEvR j hG hFT Z) := by
  intro a
  obtain ⟨k, g, p, hp, hne, he⟩ := hB Z a
  have hw : (fun i => formsEvR j hG hFT Z ((recPlus h j hj).inc wL (G.w i))) =
      fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j) :=
    funext fun i => curveUnit_gF_inc h j hj hG hFT Z wL (G.w i)
  have e := congrArg (fun v => MvPolynomial.aeval v p) hw
  refine ⟨k, g, p, hp, fun h0 => hne (e.symm.trans h0), ?_⟩
  exact (congrArg (a * ·) e).trans (he.trans (curveUnit_gF_inc h j hj hG hFT Z _ g).symm)

def PtOfSBody (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  ∀ (L : Type) [Field L] [Algebra (Kp (recPlus h j hj) la G.N) L]
    (φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] L),
    ∃ (alg : T.Q.c.F →+* L) (y : letI := alg.toAlgebra; FrPt (T.Q.Xo j) T.Q.c L),
      (letI := alg.toAlgebra; ∃ (Z : Comp (T.Q.Xo j) T.Q.c) (ψ : Om Z →ₐ[T.Q.c.F] L), FrMap ψ (genFr hG Z) y) ∧
      (∀ a : T.Q.c.F, alg a = algebraMap (Kp (recPlus h j hj) la G.N) L
        (@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _ (Kp.algKl (recPlus h j hj) la G.N)
          (algebraMap T.Q.c.F ((recPlus h j hj).Kl la) a))) ∧
      letI := alg.toAlgebra
      (∑ k, algebraMap (Kp (recPlus h j hj) la G.N) L
          (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
          evR (T.Q.Xo j) T.Q.c ((G.w k : T.R j)) y) ≠ 0 ∧
      ∀ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (addL (wt0 D j) wL k)),
        φ (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
          ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ g), emb_mem_Vw (recPlus h j hj) la G.N _ g⟩)) =
        evR (T.Q.Xo j) T.Q.c ((g : T.R j)) y /
          (∑ k', algebraMap (Kp (recPlus h j hj) la G.N) L
            (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k'))) *
            evR (T.Q.Xo j) T.Q.c ((G.w k' : T.R j)) y) ^ k

set_option maxHeartbeats 1000000 in

theorem ptOfS_all [Finite (Comp (T.Q.Xo j) T.Q.c)] (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt)
    (hTw : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (hFT : GenFromTest (T.Q.Xo j) T.Q.c hG) (hV : GenValInjSt h j hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BIRSt h j hj hG G)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hC : ∀ Z, CurveLoc.CountQAt (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z)) :
    PtOfSBody h j hj hG G la := by
  classical
  have := Fintype.ofFinite (Comp (T.Q.Xo j) T.Q.c)
  intro L _ _ φ
  let ψ : ↥(Frac0 (recPlus h j hj) la G.w) →ₐ[Kp (recPlus h j hj) la G.N] L := φ.comp (toOsK (recPlus h j hj) la G.w)
  have hψ : ∀ f, ψ f = φ (toOsK (recPlus h j hj) la G.w f) := fun f => rfl
  have hQ : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _
  have hJ : Jid (recPlus h j hj) la G.w ≤ RingHom.ker ψ := fun x hx => by
    rw [RingHom.mem_ker, hψ, (toOsK_eq_zero_iff (recPlus h j hj) la G.w x).2 hx, map_zero]
  have hinf : (Finset.univ : Finset (Comp (T.Q.Xo j) T.Q.c)).inf
      (fun Z => RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hFT Z) G.w)) ≤ RingHom.ker ψ := by
    intro f hf
    have hf' : ∀ Z, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hFT Z) G.w f = 0 := fun Z =>
      RingHom.mem_ker.1 (Finset.inf_le (f := fun Z => RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z)
        (formsEvR j hG hFT Z) G.w)) (Finset.mem_univ Z) hf)
    rw [curveInj h j hj hG hFT hV G la f hf']
    exact Ideal.zero_mem _
  obtain ⟨Z, -, hZ⟩ := (Ideal.IsPrime.inf_le' hQ).1 hinf
  obtain ⟨χ, hχ⟩ := pos_factor (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hFT Z) G.w) ψ
    (fun f hf => RingHom.mem_ker.1 (hZ (RingHom.mem_ker.2 hf))) (fun r => by
      obtain ⟨a, p, hp, hr⟩ := CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z)
        (pos_birAt h j hj hG hFT G hB Z) (hC Z) r
      exact ⟨a, p, fun h0 => hp _ hQ hJ hZ (RingHom.mem_ker.2 h0), hr⟩)
  have hgF : ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u),
      formsEvR j hG hFT Z ((recPlus h j hj).inc u F) = evC hG Z (F : T.R j) := fun u F =>
    curveUnit_gF_inc h j hj hG hFT Z u F
  let alg : T.Q.c.F →+* L := (algebraMap (Kp (recPlus h j hj) la G.N) L).comp
    ((@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _ (Kp.algKl (recPlus h j hj) la G.N)).comp
      (algebraMap T.Q.c.F ((recPlus h j hj).Kl la)))
  let _ : Algebra T.Q.c.F L := alg.toAlgebra
  let ι : Om Z →+* L := χ.toRingHom.comp (CurveLoc.psiZ (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z))
  have hι : ∀ a : T.Q.c.F, ι (algebraMap T.Q.c.F (Om Z) a) = alg a := fun a =>
    (congrArg χ (pos_psiZ_alg (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z) a)).trans (χ.commutes _)
  let ιA : Om Z →ₐ[T.Q.c.F] L := { ι with commutes' := hι }
  obtain ⟨y, hy⟩ := pos_frMap hS hTw ιA (genFr hG Z)
  have hval : ∀ {u : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j u),
      evR (T.Q.Xo j) T.Q.c (F : T.R j) y = ι (evC hG Z (F : T.R j)) := fun F =>
    pos_evR (h.evalWD j hj) _ (pos_natural h j F) ιA (genFr hG Z) (hFT Z) y hy
  have hF : ∀ {u : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j u),
      χ (CurveLoc.psiZ (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z)
        (formsEvR j hG hFT Z ((recPlus h j hj).inc u F))) = evR (T.Q.Xo j) T.Q.c (F : T.R j) y := fun F =>
    (congrArg (fun v => χ (CurveLoc.psiZ (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z) v)) (hgF _ F)).trans
      (hval F).symm
  have hs : χ (algebraMap (RZ (recPlus h j hj) la G.N (Om Z)) (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hFT Z) G.w)
      (rzMap (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hFT Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))) =
      ∑ k, algebraMap (Kp (recPlus h j hj) la G.N) L
        (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
        evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y :=
    (pos_sec_eval (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z) χ).trans
      (Finset.sum_congr rfl fun k _ => congrArg _ (hF (G.w k)))
  refine ⟨alg, y, ⟨Z, ιA, hy⟩, fun a => rfl, ?_, fun k g => ?_⟩
  · rw [← hs]
    exact pos_sec_ne (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z) χ
  · refine ((hχ _).trans (hψ _)).symm.trans ((phi_fraction_base_value (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z) χ k
      ((recPlus h j hj).inc _ g) (emb_mem_Vw (recPlus h j hj) la G.N _ g)).trans ?_)
    rw [hs, div_eq_mul_inv, inv_pow]
    exact congrArg (· * _) (hF g)

theorem ptOfS_of [Finite (Comp (T.Q.Xo j) T.Q.c)] (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt)
    (hTw : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (hFT : GenFromTest (T.Q.Xo j) T.Q.c hG) (hV : GenValInjSt h j hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BIRSt h j hj hG G)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hC : ∀ Z, CurveLoc.CountQAt (recPlus h j hj) la G.N G.w (formsEvR j hG hFT Z)) :
    PtOfSSt h j hj hG G la :=
  fun _ => ptOfS_all h j hj hG hS hTw hFT hV G hB la hC

end Inst

end Formalism.L2.Pj
