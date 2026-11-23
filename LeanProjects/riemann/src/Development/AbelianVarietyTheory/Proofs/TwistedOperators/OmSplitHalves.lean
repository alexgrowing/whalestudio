import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLattices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetAtUnram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField
open MeasureTheory GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter
open scoped TensorProduct

namespace GlobalTheory.VacStabFixed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem parts_ext {x y : AE D} (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext ((he _).1.trans (h1.trans (he _).1.symm)) ((he _).2.trans (h2.trans (he _).2.symm)))

theorem place_comp {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 ∧
      compFin D v (finPart D (algebraMap (AF D.host.F) (AE D) ε)) = 1 ∧
      ∀ w, w ≠ v → compFin D w (finPart D (algebraMap (AF D.host.F) (AE D) ε)) = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  refine ⟨TensorProduct.zero_tmul _ _, ?_, fun w hw => ?_⟩
  · change evalV D.host.F v α ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [h1]; rfl
  · change evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h0 w hw, TensorProduct.zero_tmul]

theorem supp_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (z : AE D) :
    algebraMap (AF D.host.F) (AE D) ε * z = z ↔
      infPart D z = 0 ∧ ∀ w, w ≠ v → compFin D w (finPart D z) = 0 := by
  obtain ⟨hi, h1, h0⟩ := place_comp hε
  constructor
  · intro h
    refine ⟨by rw [← h, RingHom.map_mul, hi, zero_mul], fun w hw => ?_⟩
    rw [← h, RingHom.map_mul, RingHom.map_mul, h0 w hw, zero_mul]
  · rintro ⟨a, b⟩
    refine parts_ext (by rw [RingHom.map_mul, hi, zero_mul, a]) (GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_)
    change compFin D w _ = compFin D w _
    rw [RingHom.map_mul, RingHom.map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, one_mul]
    · rw [b w hw, mul_zero]

theorem unramAt_of {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    {χ : (AE D)ˣ →* Circle} (hχ : CharUnramAt D χ v) : UnramAt ε χ := by
  intro x hx h1 h2
  obtain ⟨a, b⟩ := (supp_iff hε _).1 hx
  refine hχ x ?_ (fun w hw => ?_) h1 h2
  · rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at a
  · have := b w hw
    rwa [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this

theorem map_sub_one {R R' n : Type} [CommRing R] [CommRing R'] [DecidableEq n] (φ : R →+* R') (M : Matrix n n R)
    (h : M.map φ = 1) (i j : n) : φ ((M - 1) i j) = 0 := by
  have h1 : φ (M i j) = (1 : Matrix n n R') i j := congrFun (congrFun h i) j
  rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem suppPl_of {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {V : HSp D}
    {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {k : GA D V} (hk : InStabAt V L v k) : SuppPl ε V k :=
  fun i j => (supp_iff hε _).2 ⟨map_sub_one _ _ hk.1 i j,
    fun w hw => map_sub_one ((compFin D w).comp (finPart D)) _ (hk.2.1 w hw) i j⟩

theorem det_int {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsLattice D.host.E L) (g : GA D V)
    (h : ∀ y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)),
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E))) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hL.fg hL.span_eq_top h

theorem unram_detAt {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsLattice D.host.E L) {g : GA D V}
    (h : ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)))
    {e : AE D} (he : e * e = e) {ε : AF D.host.F} (hs : algebraMap (AF D.host.F) (AE D) ε * e = e)
    {χ : (AE D)ˣ →* Circle} (hχ : UnramAt ε χ) : χ (GlobalTheory.VecInv.detAt e he V g) = 1 := by
  refine hχ _ ?_ (GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g fun y hy => (h y).1 hy)) ?_
  · change _ * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
    linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hs
  · rw [← MonoidHom.map_inv]
    exact GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g⁻¹ (GlobalTheory.LocalLatStab.inv_keeps V _ g h))

open GlobalTheory.SplitScalar GlobalTheory.SplitHecke in

theorem om_split_halves {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    (hL : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True,
      actO S T g h u ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) ∧
      actO S T g⁻¹ h⁻¹ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
    {x y : (AE D)ˣ} (hx : IsDetAt e S g x) (hy : IsDetAt e T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (v1 : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True, IsHalf e u → heisO ψ S T u f = f)
    (v2 : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True, IsHalf (cA D e) u → heisO ψ S T u f = f) :
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  by_cases hf0 : f = 0
  · subst hf0
    simp only [map_zero, smul_zero]
  have he' := isSplitIdem_conj he
  have hψ := hW.std.1
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he.1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he'.1
  have hfin := @latO_fin D S T (ΛS : Set _) (ΛT : Set _)
  generalize latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) = Λ at *
  have hL' : ∀ u, actO S T g⁻¹ h⁻¹ u ∈ Λ ↔ u ∈ Λ := fun u =>
    ⟨fun hu => by
      have := (hL _ hu).1
      rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this, fun hu => (hL u hu).2⟩
  have hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 :=
    fun y hy hn => exists_dual_half he hdual hstc hy hn
  have hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1 := fun y hy hn => by
    have := exists_dual_half he' hdual (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst) hy hn
    rwa [GlobalTheory.DualPairCheck.cA_cA] at this
  obtain ⟨r, hr, hom⟩ := om_eq_smul_sum hW he (fun u hu => (hdual u (hfin hu)).1 hu) hd hd' hg hh hx hy (R := {0})
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨(hL' 0).2 (zero_mem _), isHalf_zero e⟩)
    (fun w hw _ => ⟨0, ⟨Finset.mem_singleton_self _, by rw [sub_zero]; exact (hL' w).1 hw⟩,
      fun v hv => Finset.mem_singleton.1 hv.1⟩)
    (fun w hw _ => (hL' w).2 hw)
  simp only [Finset.sum_singleton, heisO_zero] at hom
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont hf0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul]))
  have hn : nrm2 μ 𝓕 (c • f) = 1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have hcf := GlobalTheory.WeilVacMove.isTheta_smul c hf
  have h1 := hom _ hcf (fun u hu hh => by rw [heisO_smul, v1 u hu hh])
    fun u hu hh => by rw [heisO_smul, v2 u hu hh]
  have h2 : nrm2 μ 𝓕 (om (g, h) (c • f)) = 1 := by
    rw [← hn, nrm2, nrm2, integral_normSq_eq _ (hW.om_pres _ _ hcf).cont.measurable,
      integral_normSq_eq _ hcf.cont.measurable, hW.om_unit μ 𝓕 hμ.1 hμ.2.1 _ _ hcf]
  have h3 : nrm2 μ 𝓕 ((splitFacO χS χT x y : ℂ) • c • f) = 1 := by
    rw [← hn, nrm2, nrm2]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  rw [h1, mul_smul, pairNorm_smul, h3, mul_one] at h2
  have h4 : r = 1 := by
    rw [← Real.sqrt_sq hr.le, h2, Real.sqrt_one]
  rw [hom f hf v1 v2, h4, Complex.ofReal_one, one_mul]

theorem half_mem_place {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {e : AE D}
    (hs : algebraMap (AF D.host.F) (AE D) ε * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True)
    (hh : IsHalf e u) : u ∈ latO S T LS LT fun w => w = v := by
  refine (GlobalTheory.VecInvInert.mem_place_iff hε u).2 ⟨hu, Matrix.ext fun i j => ?_⟩
  change _ * u i j = u i j
  rw [← hh i j, ← mul_assoc, hs]

theorem vacFixedAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : VacFixedAt D v := by
  intro ψ S T χS χT om hW uS uT LS LT hS hT f hf hvac k k' hk hk'
  obtain ⟨ε, hε⟩ : ∃ ε, IsPlaceIdem D v ε :=
    ⟨_, singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _,
      fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have uS' := unramAt_of hε uS
  have uT' := unramAt_of hε uT
  have sk := suppPl_of hε hk
  have sk' := suppPl_of hε hk'
  by_cases hsp : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e, he, hb⟩ := hsp
    have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
    have s1 : algebraMap (AF D.host.F) (AE D) ε * e = e := by
      rw [← hb]; linear_combination he.1 + he.2.1
    have s2 : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by
      rw [← hb]; linear_combination he'.1 + he.2.1
    have key := om_split_halves hW hS hT he (fun i j => by rw [hb]; exact sk i j) (fun i j => by rw [hb]; exact sk' i j)
      (fun u hu => ⟨GlobalTheory.LocalLatStab.actO_mem S T _ _ _ k k' (fun y hy => (hk.2.2 y).1 hy)
          (fun y hy => (hk'.2.2 y).1 hy) u hu,
        GlobalTheory.LocalLatStab.actO_mem S T _ _ _ k⁻¹ k'⁻¹ (GlobalTheory.LocalLatStab.inv_keeps S _ k hk.2.2)
          (GlobalTheory.LocalLatStab.inv_keeps T _ k' hk'.2.2) u hu⟩)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1 S k) (GlobalTheory.VecInv.isDetAt_detAt e he.1 T k') hf
      (fun u hu hh => hvac.2 e he u (half_mem_place hε s1 hu hh) hh)
      (fun u hu hh => hvac.2 _ he' u (half_mem_place hε s2 hu hh) hh)
    rwa [splitFacO, unram_detAt hS.1 hk.2.2 he.1 s1 uT', unram_detAt hT.1 hk'.2.2 he.1 s1 uS', inv_one, mul_one,
      Circle.coe_one, one_smul] at key
  · have hv : NonSplitAt D v ε := ⟨hε, hsp⟩
    obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
    refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T LS LT hS hT χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv uS' uT' k k' sk sk'
      (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T LS LT hS hT v ε hε k k' hk.2.2 hk'.2.2) f hf fun u hu => ?_
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
    have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
    rwa [h1] at h2

theorem vacFixed (D : D7) : VacFixed D := fun v _ => vacFixedAt D v

end GlobalTheory.VacStabFixed

end
