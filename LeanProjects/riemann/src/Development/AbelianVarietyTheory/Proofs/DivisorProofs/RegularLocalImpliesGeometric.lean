import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionOpenCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsElementHeightDifference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricDifferenceLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.CechPic GlobalTheory.ArInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetHT.GeoPf

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_add (hp : IsProjOver p) {N A B : LB X} (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (h : cls N hN = cls A hA + cls B hB) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ (N.pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have e2 (L : LB X) : topSelfIntersection κ (L.pull i) 1 = interNum κ (structureModule Z) ![L.pull i] := by
    rw [topSelf_def]
    congr 1
    funext j
    fin_cases j
    rfl
  rw [e2, e2, e2]
  refine interNum_one_of_cls_eq_add (hH.pull_of_isClosedImmersion i) hd (LB.isLB_pull hN i) (LB.isLB_pull hA i)
    (LB.isLB_pull hB i) ?_
  rw [cls_pull hN, cls_pull hA, cls_pull hB, h, map_add]

theorem topSelf_pow' (hp : IsProjOver p) (L : HermLB p) (m : ℕ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
  have c (n : ℕ) : cls (L.pow n).B (L.pow n).isLB = n • cls L.B L.isLB := cls_lbPow L.isLB n _
  induction m with
  | zero =>
    have := topSelf_add hp (L.pow 0).isLB (L.pow 0).isLB (L.pow 0).isLB (by rw [c]; simp) Z i κ hd
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    rw [topSelf_add hp (L.pow (n + 1)).isLB (L.pow n).isLB L.isLB (by rw [c, c, succ_nsmul]) Z i κ hd, ih]
    push_cast
    ring

end Curves

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem exists_integral_ext (V : Cover Y) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (hz : z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))) :
    ∃ yt : Sp e.O ⟶ V.X, spMap e.O.subtype ≫ yt = z ≫ V.j := by
  have hP : IsProper V.p := (isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O :=
    ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence V.p := by
    have h : UniversallyClosed V.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (z ≫ V.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) V.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, V.pb.w, ← Category.assoc, hz, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := z ≫ V.j, i₂ := spMap φ, commSq := hsq }
  exact ⟨l.l, l.fac_left⟩

end GlobalTheory.DetHT.GeoPf

namespace GlobalTheory.DetHT.GeoPf

open GlobalTheory.VertForm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem nefOver_of_norm_one (hRL : RegLocSt) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn)
    (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (lg : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ)
    (hN : Norms V L f a lg) (s : Y.Fn) (hs : s ≠ 0) (W : Y.X.Opens) (hW : (W : Set Y.X).Nonempty) (l : ℕ)
    (hl : l.Prime)
    (H : ∀ v : HeightOneSpectrum (𝓞 F), (l : 𝓞 F) ∈ v.asIdeal → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      UnitAt (below y.1) (s / f (below y.1)) ∧ Real.log (e.w (valAt y.1 (s / f (below y.1)))) + lg v e y = 0) :
    NefOver L l := by
  obtain ⟨r, hr, hu, -, hf⟩ := hN
  haveI := CoverHt.isPreimmersion_j V
  have hη := Isom.j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr

  obtain ⟨t, ht, htW⟩ := V.j.isEmbedding.isInducing.isOpen_iff.1 (V.π ⁻¹ᵁ W).isOpen
  let W' : V.X.Opens := ⟨t, ht⟩
  have hW' : (W' : Set V.X).Nonempty := by
    obtain ⟨w, hw⟩ := hW
    obtain ⟨u, hu⟩ := V.π.surjective w
    have : u ∈ V.j ⁻¹' t := by
      rw [htW]
      change V.π u ∈ W
      rw [hu]
      exact hw
    exact ⟨V.j u, this⟩

  have key : ∀ (i : L.B.ι) (v : HeightOneSpectrum (𝓞 F)), (l : 𝓞 F) ∈ v.asIdeal → ∀ (e : Ext v)
      (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ L.B.U i → below (z ≫ V.j) ∈ W' →
      UnitAt (below z) (V.φ s * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) ∧
      e.w (valAt z (V.φ s * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) = 1 := by
    intro i v hlv e z yt hz e₂ hU hWz
    let y : AlgPt Y := ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩
    have hyW : below y.1 ∈ W := by
      have : below z ∈ V.j ⁻¹' t := hWz
      rw [htW] at this
      exact this
    obtain ⟨hsf, hlog⟩ := H v hlv e y hyW
    have H₁ := hf v e y z yt (fun _ => i) rfl e₂ hU
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U i := by
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have m₁ : below z ∈ (L.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hpt
    have hπ : V.π (below z) = below y.1 := rfl
    have u₁ := hu _ _ m₁
    rw [hπ] at u₁
    have hC : UnitAt (V.π (below z)) (s / f (below y.1)) := by rw [hπ]; exact hsf
    have hCφ := V.unitAt_φ hC
    have hf0 : f (below y.1) ≠ 0 := fun h0 => by
      rw [h0, map_zero, zero_mul] at u₁
      exact u₁.ne_zero rfl
    have e₃ : V.φ s * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) =
        V.φ (s / f (below y.1)) *
          (V.φ (f (below y.1)) * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) := by
      rw [← mul_assoc, ← map_mul, div_mul_cancel₀ s hf0]
    rw [e₃]
    refine ⟨hCφ.mul u₁, ?_⟩
    have n1 : e.w (valAt y.1 (s / f (below y.1))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero hsf)
    have n2 : e.w (valAt z (V.φ (f (below y.1)) * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero u₁)
    have p1 := lt_of_le_of_ne (e.w.nonneg _) n1.symm
    have p2 := lt_of_le_of_ne (e.w.nonneg _) n2.symm
    rw [SmallSec.valAt_mul hCφ.regAt u₁.regAt, V.valAt_φ z hC.regAt, map_mul]
    refine Real.eq_one_of_pos_of_log_eq_zero (mul_pos p1 p2) ?_
    rw [Real.log_mul n1 n2, ← H₁]
    exact hlog
  refine HtGenCurve.nefOver_of_localGen (𝓞 F) V.X V.p Y.dim V.ar L _ hR l 1 (fun _ => ⊤)
    (fun _ _ => ρ.symm (V.φ s)) (fun _ => trivial) ?_
  intro x i x₀ _ hx₀ hl₀
  have hne : (l : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  obtain ⟨v, hvp⟩ : ∃ v : HeightOneSpectrum (𝓞 F), v.asIdeal = (V.p x₀).asIdeal :=
    ⟨⟨_, (V.p x₀).isPrime, fun h0 => hne (by rw [← Ideal.mem_bot, ← h0]; exact hl₀)⟩, rfl⟩
  have hlv : (l : 𝓞 F) ∈ v.asIdeal := hvp ▸ hl₀
  have eg : ρ.symm (V.φ s) * ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) : V.X.functionField) =
      ρ.symm (V.φ s * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) := by
    rw [map_mul]
    rfl
  have hg0 : ρ.symm (V.φ s * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ ρ.symm.injective]
    exact mul_ne_zero ((map_ne_zero V.φ).2 hs) (Units.ne_zero _)
  have hreg : RegAt x₀ (ρ.symm (V.φ s * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) := by
    refine hRL F Y V (L.B.U i) W' hW' v _ (fun e z yt hz e₂ hU hWz => ?_) x₀ hx₀ hvp.symm
    rw [hv, RingEquiv.apply_symm_apply]
    exact (key i v hlv e z yt hz e₂ hU hWz).2.le
  have hreg' : RegAt x₀ (ρ.symm (V.φ s * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)))⁻¹ := by
    refine hRL F Y V (L.B.U i) W' hW' v _ (fun e z yt hz e₂ hU hWz => ?_) x₀ hx₀ hvp.symm
    obtain ⟨k₁, k₂⟩ := key i v hlv e z yt hz e₂ hU hWz
    rw [hv, map_inv₀, RingEquiv.apply_symm_apply, GlobalTheory.LineNorm.Neg.valAt_inv k₁, map_inv₀, k₂, inv_one]
  have hunit := (unitAt_iff hg0).2 ⟨hreg, hreg'⟩
  refine ⟨fun _ => eg ▸ hreg, ⟨0, eg ▸ hunit⟩, fun _ _ _ => ?_⟩
  rw [sub_self, zero_mul]
  exact fun h => h.ne_zero rfl

end GlobalTheory.DetHT.GeoPf

namespace GlobalTheory.DetHT

open GlobalTheory.VertForm GlobalTheory.DetHT.GeoPf

theorem geoSt_of_regLocSt : RegLocSt → GeoSt := by
  intro hRL F _ _ Y V L f a lg hN s W hW l hl H
  intro Z i _ _ κ _ _ _ _ hd

  have hl0 : (l : Γ(Z, ⊤)) = 0 := by
    rw [← map_natCast (algebraMap κ Γ(Z, ⊤)), CharP.cast_eq_zero, map_zero]
  obtain ⟨z₀⟩ : Nonempty Z := inferInstance
  have hlx := HtGenCurve.natCast_mem_asIdeal V.p i l hl0 z₀
  have hnu : ¬ IsUnit (l : V.X.presheaf.stalk (i z₀)) := by
    intro hu
    have h1 := hu.map (i.stalkMap z₀).hom
    rw [map_natCast] at h1
    have h2 : (l : Z.presheaf.stalk z₀) = 0 := by
      rw [← map_natCast (Z.presheaf.germ ⊤ z₀ trivial).hom, hl0, map_zero]
    rw [h2] at h1
    exact not_isUnit_zero h1
  have hgen : genericPoint Y.X ∈ W :=
    ((genericPoint_spec Y.X).mem_open_set_iff W.isOpen).2 (by simpa using hW)
  obtain ⟨-, -, y₀, z₁, -, -, hy₀W, hz₁, -, -, -⟩ :=
    Cover.ThroughFibre.exists_algPt_through F Y V l hl W hgen ⊤ (i z₀) trivial hnu
  have hne : (l : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  obtain ⟨v₀, hv₀⟩ : ∃ v : HeightOneSpectrum (𝓞 F), v.asIdeal = (V.p (i z₀)).asIdeal :=
    ⟨⟨_, (V.p (i z₀)).isPrime, fun h0 => hne (by rw [← Ideal.mem_bot, ← h0]; exact hlx)⟩, rfl⟩
  have hs : s ≠ 0 := by
    obtain ⟨ρ, hρ⟩ := H v₀ (hv₀ ▸ hlx)
    obtain ⟨e⟩ : Nonempty (Ext v₀) := inferInstance
    have := (hρ e y₀ hy₀W).1.ne_zero
    intro h
    rw [h, zero_div] at this
    exact this rfl
  classical
  choose ρ hρ using H
  let c : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if h : (l : 𝓞 F) ∈ v.asIdeal then ρ v h else 0
  have hc : (Function.support c).Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(l : 𝓞 F)}) ?_).subset fun v hv => ?_
    · exact fun h0 => hne (Ideal.span_singleton_eq_bot.1 (h0.trans Ideal.zero_eq_bot))
    · by_contra hn
      apply hv
      have : (l : 𝓞 F) ∉ v.asIdeal := fun hm => hn (Ideal.dvd_span_singleton.2 hm)
      simp only [c, dif_neg this]

  have hq : ∀ v, ∃ (m : ℕ) (zz : ℤ), 0 < m ∧ (m : ℝ) * c v = (zz : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    intro v
    by_cases h : (l : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨e⟩ : Nonempty (Ext v) := inferInstance
      have hz₁' : z₁ ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) := by
        rw [← Category.assoc, hz₁]
        exact y₀.2
      obtain ⟨yt, hyt⟩ := exists_integral_ext V v e z₁ hz₁'
      obtain ⟨j, hj⟩ := exists_chart L.isLB (yt (IsLocalRing.closedPoint e.O))
      have hj' : ⊤ ≤ yt ⁻¹ᵁ L.B.U ((fun _ => j : (L.B.pull V.j).ι) PUnit.unit) :=
        ((IsLocalRing.closedPoint_mem_iff (R := e.O) (yt ⁻¹ᵁ L.B.U j)).1 hj).ge
      obtain ⟨r, -, -, -, hf⟩ := hN
      have H₁ := hf v e y₀ z₁ yt (fun _ => j) hz₁ hyt hj'
      have H₂ := (hρ v h e y₀ hy₀W).2
      obtain ⟨α, hα, hαe⟩ := ValGroup.exists_log_sub e.w (valAt y₀.1 (s / f (below y₀.1)))⁻¹
        (valAt z₁ (V.φ (f (below y₀.1)) * ((r fun _ => j : V.G.functionFieldˣ) : V.G.functionField)))
      have hcv : c v = Real.log (e.w α) := by
        simp only [c, dif_pos h]
        rw [← H₂, ← hαe, H₁, map_inv₀, Real.log_inv]
        ring
      rw [hcv]
      exact GlobalTheory.ExtValueGroup.log_w_rat F v e α hα
    · exact ⟨1, 0, one_pos, by simp [c, dif_neg h]⟩
  obtain ⟨M, b, b', hb, hb', E⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F c hc hq
  have nb : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hb
  have nb' : algebraMap (𝓞 F) F b' ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hb'
  have hβ : algebraMap (𝓞 F) F b' / algebraMap (𝓞 F) F b ≠ 0 := div_ne_zero nb' nb
  have hcst := IndScale.unitAt_constFn Y.str (genericPoint Y.X) hβ
  have hM : NefOver (L.pow (M : ℕ)) l := by
    refine nefOver_of_norm_one hRL V (L.pow (M : ℕ)) _ _ _ (norms_pow F Y V L f a lg M hN)
      (s ^ (M : ℕ) * Cartier.constFn Y.str (algebraMap (𝓞 F) F b' / algebraMap (𝓞 F) F b))
      (mul_ne_zero (pow_ne_zero _ hs) hcst.ne_zero) W hW l hl fun v hlv e y hy => ?_
    obtain ⟨hU, hL⟩ := hρ v hlv e y hy
    have e₀ : s ^ (M : ℕ) * Cartier.constFn Y.str (algebraMap (𝓞 F) F b' / algebraMap (𝓞 F) F b) /
        f (below y.1) ^ (M : ℕ) = (s / f (below y.1)) ^ (M : ℕ) *
          Cartier.constFn Y.str (algebraMap (𝓞 F) F b' / algebraMap (𝓞 F) F b) := by
      rw [div_pow]
      ring
    have hC := IndScale.unitAt_constFn Y.str (below y.1) hβ
    have hP := InducedPow.unitAt_pow hU (M : ℕ)
    beta_reduce
    rw [e₀]
    refine ⟨hP.mul hC, ?_⟩
    have n1 : e.w (valAt y.1 (s / f (below y.1))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero hU)
    have n2 : NumberField.HeightOneSpectrum.adicAbv F v
        (algebraMap (𝓞 F) F b' / algebraMap (𝓞 F) F b) ≠ 0 := (AbsoluteValue.ne_zero_iff _).2 hβ
    rw [SmallSec.valAt_mul hP.regAt hC.regAt, InducedPow.valAt_pow _ hU.regAt,
      IndScale.valAt_constFn Y.str _ y.1 y.2, map_mul, e.w_alg, map_pow,
      Real.log_mul (pow_ne_zero _ n1) n2, Real.log_pow, map_div₀,
      Real.log_div ((AbsoluteValue.ne_zero_iff _).2 nb') ((AbsoluteValue.ne_zero_iff _).2 nb)]
    have Ev := E v
    simp only [c, dif_pos hlv] at Ev
    rw [← hL] at Ev
    linarith
  have h := hM Z i κ hd
  rw [topSelf_pow' V.ar.isProjOver L M Z i κ hd] at h
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast M.pos)).1 h

end GlobalTheory.DetHT
