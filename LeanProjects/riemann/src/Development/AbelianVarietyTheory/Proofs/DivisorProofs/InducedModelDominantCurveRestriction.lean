import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefAtOfPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreOfNormsPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOverAntitoneCombStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm

namespace GlobalTheory.NefHodgeTateAt

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_of_cls_eq_add (hp : IsProjOver p) {N A B : LB X} (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
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

theorem topSelf_pow (hp : IsProjOver p) (L : HermLB p) (m : ℕ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
  have c (n : ℕ) : cls (L.pow n).B (L.pow n).isLB = n • cls L.B L.isLB := cls_lbPow L.isLB n _
  induction m with
  | zero =>
    have := topSelf_of_cls_eq_add hp (L.pow 0).isLB (L.pow 0).isLB (L.pow 0).isLB (by rw [c]; simp) Z i κ hd
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    rw [topSelf_of_cls_eq_add hp (L.pow (n + 1)).isLB (L.pow n).isLB L.isLB (by rw [c, c, succ_nsmul]) Z i κ hd, ih]
    push_cast
    ring

theorem nefOver_tens (hp : IsProjOver p) {L M : HermLB p} {l : ℕ} (hL : NefOver L l) (hM : NefOver M l) :
    NefOver (L.tens M) l := fun Z i _ _ κ _ _ _ _ hd => by
  rw [topSelf_of_cls_eq_add hp (L.tens M).isLB L.isLB M.isLB (cls_tens L.isLB M.isLB _) Z i κ hd]
  exact add_nonneg (hL Z i κ hd) (hM Z i κ hd)

theorem nefOver_pow (hp : IsProjOver p) {L : HermLB p} {l : ℕ} (hL : NefOver L l) (m : ℕ) :
    NefOver (L.pow m) l := fun Z i _ _ κ _ _ _ _ hd => by
  rw [topSelf_pow hp L m Z i κ hd]
  exact mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)

theorem nefOver_of_pow (hp : IsProjOver p) {L : HermLB p} {l m : ℕ} (hm : 0 < m) (hL : NefOver (L.pow m) l) :
    NefOver L l := fun Z i _ _ κ _ _ _ _ hd => by
  have h := hL Z i κ hd
  rw [topSelf_pow hp L m Z i κ hd] at h
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm)).1 h

omit [Module.Finite ℤ k] in

theorem nefOver_of_cls_eq {L M : HermLB p} {l : ℕ} (h : cls L.B L.isLB = cls M.B M.isLB) (hM : NefOver M l) :
    NefOver L l := fun Z i _ _ κ _ _ _ _ hd => by
  have : topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (M.B.pull i) 1 :=
    interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull M.isLB i) fun _ => by
      rw [cls_pull L.isLB, cls_pull M.isLB, h]
  rw [this]
  exact hM Z i κ hd

end Curves

theorem cls_eq_of_presents {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L M : LB X} {r : L.ι → X.functionFieldˣ}
    {r' : M.ι → X.functionFieldˣ} (h : Presents D L r) (h' : Presents D M r') : cls L h.isLB = cls M h'.isLB := by
  choose a ha using fun q : M.ι × L.ι => exists_unit_fnOf_eq (U := M.U q.1 ⊓ L.U q.2)
    fun x hx => (h.isEqn _ x hx.2).iff_unitAt.1 (h'.isEqn _ x hx.1)
  refine (cls_eq_iff _ _).2 ⟨⟨a⟩, fun p q => Units.ext (Cartier.fn_ext fun hpq => ?_)⟩
  have e := congrArg (fnOf (L.U p.2 ⊓ L.U q.2) (memInf hpq.1.2 hpq.2.2)) (L.g p.2 q.2).inv_mul
  rw [map_mul, map_one] at e
  refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ hpq _) (fnOf_resG _ hpq _)))
    (fnOf_resG _ hpq _))).symm)
  refine (ha p _).trans (Eq.trans ?_ (congrArg _ (ha q _)).symm)
  rw [h.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2), h'.isRatSec p.1 q.1 (memInf hpq.1.1 hpq.2.1),
    mul_div_mul_comm, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_left e]
  rfl

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem j_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h₁ (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
    change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
    have := ((V.π ≫ Y.str) y).isPrime
    rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have h₂ {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
    rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans (h₁ _).le)
  obtain ⟨y, hy⟩ := h₂ h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem w_div_eq_one {Z : Scheme.{0}} [IsIntegral Z] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ Z) {c a b : Z.functionField} (ha : UnitAt (below z) (c * a))
    (hb : UnitAt (below z) (c * b))
    (h : Real.log (e.w (valAt z (c * a))) = Real.log (e.w (valAt z (c * b)))) :
    e.w (valAt z (b / a)) = 1 := by
  have hc : c ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have ha0 : a ≠ 0 := right_ne_zero_of_mul ha.ne_zero
  have e₁ : b / a = (c * b) * (c * a)⁻¹ := by field_simp
  have pa := e.w.pos (SmallSec.valAt_ne_zero ha)
  have pb := e.w.pos (SmallSec.valAt_ne_zero hb)
  have e₂ := Real.log_injOn_pos pa pb h
  rw [e₁, SmallSec.valAt_mul hb.regAt ha.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv ha, map_mul, map_inv₀, ← e₂,
    mul_inv_cancel₀ pa.ne']

theorem cls_eq_of_norms {V : Cover Y} {L L' : HermLB V.p} {f : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (h' : Norms V L' f a' l) :
    cls L.B L.isLB = cls L'.B L'.isLB := by
  obtain ⟨r, hr, hu, -, hf⟩ := h
  obtain ⟨r', hr', hu', -, hf'⟩ := h'
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr
  have hR' := InducedIsom.isRatSec_lift V.j ρ hρ hj L'.B hr'
  have hP := presents_divOfRatSec L.isLB hR
  have eρ (a b : V.G.functionFieldˣ) : ρ ((Units.map ρ.symm.toMonoidHom b : V.X.functionField) /
      (Units.map ρ.symm.toMonoidHom a : V.X.functionField)) = (b : V.G.functionField) / a := by
    rw [map_div₀]
    exact congrArg₂ (· / ·) (ρ.apply_symm_apply _) (ρ.apply_symm_apply _)
  have key : ∀ (i : L.B.ι) (j : L'.B.ι) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
      (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ (L.B.U i ⊓ L'.B.U j) →
      e.w (valAt z (((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField) /
        ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) = 1 ∧
      e.w (valAt z (((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) /
        ((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField))) = 1 := by
    intro i j v e z yt hz e₂ hU
    let y : AlgPt Y := ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩
    have h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U ((fun _ => i : (L.B.pull V.j).ι) PUnit.unit) := fun w hw => (hU hw).1
    have h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U ((fun _ => j : (L'.B.pull V.j).ι) PUnit.unit) := fun w hw => (hU hw).2
    have H₁ := hf v e y z yt (fun _ => i) rfl e₂ h₁
    have H₂ := hf' v e y z yt (fun _ => j) rfl e₂ h₂
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U i ⊓ L'.B.U j := by
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have m₁ : below z ∈ (L.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hpt.1
    have m₂ : below z ∈ (L'.B.pull V.j).U (fun _ => j) := Set.mem_iInter.2 fun _ => hpt.2
    have hπ : V.π (below z) = below y.1 := rfl
    have u₁ := hu _ _ m₁
    have u₂ := hu' _ _ m₂
    rw [hπ] at u₁ u₂
    exact ⟨w_div_eq_one e z u₁ u₂ (H₁.symm.trans H₂), w_div_eq_one e z u₂ u₁ (H₂.symm.trans H₁)⟩
  refine cls_eq_of_presents hP ⟨L'.isLB, hR', fun j x hxj => ?_⟩
  obtain ⟨i, hxi⟩ := exists_chart L.isLB x
  refine (hP.isEqn i x hxi).iff_unitAt.2
    ((unitAt_iff (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))).2 ⟨?_, ?_⟩)
  · refine Cover.RegCrit.regAt_of_integral_values F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩
    rw [hv, eρ]
    exact (key i j v e z yt hz h hU).1.le
  · rw [inv_div]
    refine Cover.RegCrit.regAt_of_integral_values F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩
    rw [hv, eρ]
    exact (key i j v e z yt hz h hU).2.le

theorem norms_scale {V : Cover Y} {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) {b : F} (hb : b ≠ 0) :
    ∃ a', Norms V L f a' fun v e y => Real.log (NumberField.HeightOneSpectrum.adicAbv F v b) + l v e y := by
  have hu (x : Y.X) := IndScale.unitAt_constFn Y.str x hb
  obtain ⟨r, hr, h₁, h₂, h₃⟩ := norms_mul_unit F Y V L f a l (fun _ => Cartier.constFn Y.str b) hu h
  let c : V.G.functionFieldˣ := Units.mk0 (V.φ (Cartier.constFn Y.str b))
    ((map_ne_zero V.φ).2 (hu (genericPoint Y.X)).ne_zero)
  have e (g : Y.Fn) (i) : V.φ g * ((c * r i : V.G.functionFieldˣ) : V.G.functionField) =
      V.φ (Cartier.constFn Y.str b * g) * r i := by
    rw [map_mul, Units.val_mul, Units.val_mk0]
    ring
  refine ⟨fun σ y => Real.log ‖ratVal (Cartier.constFn Y.str b) y‖ + a σ y, fun i => c * r i, fun i j hij => ?_,
    fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_, fun v ε y z yt i e₁ e₂ hi => ?_⟩
  · rw [Units.val_mul, Units.val_mul, hr i j hij]
    ring
  · rw [e]
    exact h₁ i x hx
  · rw [e]
    exact h₂ σ z y y' i e₁ e₂ hi
  · have := h₃ v ε y z yt i e₁ e₂ hi
    beta_reduce at this
    rw [IndScale.valAt_constFn Y.str _ y.1 y.2, ε.w_alg] at this
    rw [e]
    exact this

theorem exists_integral_point (V : Cover Y) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) :
    ∃ (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 ∧
      spMap e.O.subtype ≫ yt = z ≫ V.j := by
  obtain ⟨y⟩ := ValGroup.nonempty_algPt Y
  obtain ⟨z, hz⟩ := exists_lift_pt V.π y.1
  have hP : IsProper V.p := (isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O := ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence V.p := by
    have h : UniversallyClosed V.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (z ≫ V.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) V.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, V.pb.w, ← Category.assoc, ← Category.assoc z, hz, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := z ≫ V.j, i₂ := spMap φ, commSq := hsq }
  exact ⟨y, z, l.l, hz, l.fac_left⟩

theorem nefOver_of_norms {V : Cover Y} {L L' : HermLB V.p} {f : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} {c : HeightOneSpectrum (𝓞 F) → ℝ}
    (hc : (Function.support c).Finite) (h : Norms V L f a fun v e y => l v e y + c v) (h' : Norms V L' f a' l) {q : ℕ}
    (hq : NefOver L' q) : NefOver L q := by
  obtain ⟨m, b, b', hb, hb', E⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F c hc fun v => by
    obtain ⟨e⟩ : Nonempty (Ext v) := inferInstance
    obtain ⟨y, z, yt, e₁, e₂⟩ := exists_integral_point V v e
    obtain ⟨r, -, -, -, hf⟩ := h
    obtain ⟨r', -, -, -, hf'⟩ := h'
    have chart (B : HermLB V.p) : ∃ i, ⊤ ≤ yt ⁻¹ᵁ B.B.U i := by
      obtain ⟨i, hi⟩ := exists_chart B.isLB (yt (IsLocalRing.closedPoint e.O))
      exact ⟨i, ((IsLocalRing.closedPoint_mem_iff (R := e.O) (yt ⁻¹ᵁ B.B.U i)).1 hi).ge⟩
    obtain ⟨i, hi⟩ := chart L
    obtain ⟨i', hi'⟩ := chart L'
    have h₁ := hf v e y z yt (fun _ => i) e₁ e₂ hi
    have h₂ := hf' v e y z yt (fun _ => i') e₁ e₂ hi'
    obtain ⟨α, hα, h₃⟩ := ValGroup.exists_log_sub e.w
      (valAt z (V.φ (f (below y.1)) * (r' fun _ => i' : V.G.functionFieldˣ)))
      (valAt z (V.φ (f (below y.1)) * (r fun _ => i : V.G.functionFieldˣ)))
    have : c v = Real.log (e.w α) := by
      rw [← h₃, ← h₁, ← h₂]
      ring
    rw [this]
    exact GlobalTheory.ExtValueGroup.log_w_rat F v e α hα
  have ne {x : 𝓞 F} (hx : x ≠ 0) : algebraMap (𝓞 F) F x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hx
  obtain ⟨a₁, h₁⟩ := norms_scale (norms_pow F Y V L _ _ _ m h) (ne hb')
  obtain ⟨a₂, h₂⟩ := norms_scale (norms_pow F Y V L' _ _ _ m h') (ne hb)
  have hcl := cls_eq_of_norms h₁ (h₂.congr (fun _ => rfl) (fun _ _ => rfl) fun v e y => by
    linear_combination -E v)
  exact nefOver_of_pow V.ar.isProjOver m.pos (nefOver_of_cls_eq hcl (nefOver_pow V.ar.isProjOver hq m))

theorem norms_of_comb {V : Cover Y} {C : CxSt F} {A : Adl C Y} {ι : Type} [Fintype ι] {ρ : ι → Adl C Y} {q : ℕ} {b : ι → ℤ}
    (hD : q • A.D = ∑ i, b i • (ρ i).D)
    (hfin : ∀ v e y, q * A.lg v e y =
      Real.log (e.w (valAt y.1 (genAt A.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) +
        ∑ i, b i * (ρ i).lg v e y) {N : HermLB V.p} {K : ℕ} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    (h : Norms V N (fun x => (∏ i, genAt (ρ i).D x ^ b i) ^ K) a fun v e y => K * ∑ i, b i * (ρ i).lg v e y) :
    ∃ a', Norms V N (fun x => genAt A.D x ^ (K * q)) a' fun v e y => ((K * q : ℕ) : ℝ) * A.lg v e y := by
  classical
  have hu0 : ∀ x, UnitAt x (genAt A.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i) := by
    intro x
    have h₁ := (Base.isEqn_eqn A.D x).nsmul q
    have h₂ : (∑ i, b i • (ρ i).D).IsEqn x (∏ i, eqn (ρ i).D x ^ b i) := by
      have key : ∀ s : Finset ι, (∑ i ∈ s, b i • (ρ i).D).IsEqn x (∏ i ∈ s, eqn (ρ i).D x ^ b i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using CartierDiv.isEqn_zero x
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.prod_insert hj]
          exact ((Base.isEqn_eqn (ρ j).D x).zsmul (b j)).add ih
      exact key _
    rw [hD] at h₁
    have h₃ := h₁.iff_unitAt.1 h₂
    convert h₃ using 1
    simp only [genAt, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.coe_prod, inv_pow, inv_zpow', Finset.prod_inv_distrib]
    simp only [zpow_neg, Finset.prod_inv_distrib, div_inv_eq_mul]
    rw [mul_comm, div_eq_mul_inv]
  have hP : ∀ x, (∏ i, genAt (ρ i).D x ^ b i) ≠ 0 := fun x =>
    Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (Units.ne_zero _)
  have h2 := norms_mul_unit F Y V _ _ _ _ (fun x => (genAt A.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i) ^ K)
    (fun x => InducedPow.unitAt_pow (hu0 x) K) h
  refine ⟨_, h2.congr (fun x => ?_) (fun _ _ => rfl) fun v w y => ?_⟩
  · rw [← mul_pow, div_mul_cancel₀ _ (hP x), ← pow_mul, mul_comm q K]
  · rw [InducedPow.valAt_pow _ (hu0 _).regAt K, map_pow, Real.log_pow]
    have H := hfin v w y
    generalize Real.log (w.w (TrueGeo.valAt y.1 (genAt A.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) = Aq at H ⊢
    push_cast
    linear_combination -(K : ℝ) * H

theorem nefAt_of_cover {C : CxSt F} {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hI : A.Induced M L k cf) (V : Cover Y) (l : ℕ) [Fact l.Prime]
    (h : ∀ V' : Cover Y, (∀ (B : HermLB V.p) f a g, Norms V B f a g → ∃ B' : HermLB V'.p, Norms V' B' f a g) →
      ∃ (N : HermLB V'.p) (m : ℕ) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), 0 < m ∧
        (Norms V' N (fun x => genAt A.D x ^ m) a fun v e y => m * A.lg v e y) ∧ NefOver N l)
    (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod l) Γ(Z, ⊤)]
    (hd : topologicalKrullDim Z = 1) : 0 ≤ topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
  obtain ⟨P, π, -, hP, hπ, -, hj, -, hU, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  have h₁ := InducedPull.induced_pull F C Y A M P π hπ hj L k cf hI
  have h₂ := h₁.twist_fin (c := -cf) (by rw [Function.support_neg]; exact hI.1)
  rw [add_neg_cancel] at h₂
  have h₃ := norms_of_induces (Cover.induces_ofModel hP h₂)
  obtain ⟨V', a, g, b, ha, hb, e₁, e₂, e₃, e₄⟩ := CoverDom.exists_cover_dominating F Y V P
  have hη : V'.π (genericPoint V'.G) = genericPoint Y.X := by
    have := (genericPoint_spec V'.G).image V'.π.continuous
    rw [Set.image_univ, V'.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  have h₄ := GlobalTheory.T.norms_pullback_along_cover F Y (Cover.ofModel P hP) V' b hb V'.π e₄ (Category.comp_id _) hη _ _ _ _ h₃
  have hbη := (CoverDeg.map_genericPoint_and_deg F Y (Cover.ofModel P hP) V' b hb V'.π e₄ (Category.comp_id _) hη).1
  obtain ⟨N, m, aN, hm, hN, hnef⟩ := h V' fun B f a' g' hB =>
    ⟨_, GlobalTheory.T.norms_pullback_along_cover F Y V V' a ha g e₁ e₂ e₃ B f a' g' hB⟩
  have h₅ := norms_pow F Y V' _ _ _ _ m h₄
  have h₆ := norms_pow F Y V' _ _ _ _ k hN
  have h₇ : NefOver (((L.pull π hπ).pull b hb).pow m) l :=
    nefOver_of_norms (c := fun v => (m : ℝ) * k * (A.n : ℕ) * cf v)
      (hI.1.subset fun v hv h0 => hv (by simp [h0]))
      (h₅.congr (fun x => by rw [← pow_mul, ← pow_mul, mul_comm]; rfl) (fun _ _ => rfl) fun v e y => by
        simp only [Adl.twist, Pi.neg_apply]
        ring) h₆ (nefOver_pow V'.ar.isProjOver hnef k)
  have h₈ := nefOver_of_pow V'.ar.isProjOver hm h₇
  have := P.ar.isIntegral
  have : IsProper P.p := (isProper_and_exists_isAmpleLB_of_isProjOver P.ar.isProjOver).1
  have : IsProper (b ≫ P.p) := by
    rw [hb]
    exact (isProper_and_exists_isAmpleLB_of_isProjOver V'.ar.isProjOver).1
  have : IsProper b := IsProper.of_comp b P.p
  have hbs : Function.Surjective b := fun x =>
    (genericPoint_specializes x).mem_closed b.isClosedMap.isClosed_range ⟨_, hbη⟩
  exact NefDeRhamAt.nefAt_of_pull _ M.X P.X M.p P.p M.ar.isProjOver P.ar.isProjOver π hπ
    (NefFibUniq.surjective_of_models M P π hπ hU) L l
    (NefDeRhamAt.nefAt_of_pull _ P.X V'.X P.p V'.p P.ar.isProjOver V'.ar.isProjOver b hb hbs _ l
      fun Z i _ _ _ hd => h₈ Z i (ZMod l) hd) Z i hd

end Covers

open Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4
open scoped ENNReal Classical

theorem nefAt_of_weights (hP : Hypotheses2) {D : D7} {O : Setup D} (hO : O.Core) {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y}
    (h : O.Reads A T H) {B : ℝ} (hB : 2 ≤ B) {u : Wt O.Y} {s : ℚ} (hu : IsRat O.Y u) (hs : 0 < s)
    (hdom : WeightThresholdDefs.Dominant O.Y (A.sh u s)) (c : O.s.Comp) (q : ℕ) [Fact q.Prime]
    (hw : ∀ (V : Cover (O.var c)) (L : DV.Rt D.what₂.Tau O.N → HermLB V.p),
      (∀ x, Norms V (L x) (fun z => genAt (O.root0 c (FlagAr.setB O.Y B) x).D z)
        (fun σ y => lnAdl (O.root0 c (FlagAr.setB O.Y B) x) σ y) fun v e y => (O.root0 c (FlagAr.setB O.Y B) x).lg v e y) →
      ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb L fun x => -n x.1 x.2) q)
    {M : TrueGeo.Model (O.var c)} {L : HermLB M.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ}
    (hI : (O.Mb B u s c).Induced M L k cf) (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z]
    [Algebra (ZMod q) Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) : 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1 := by
  have hab : (O.met.ab c).NefFib := by
    obtain ⟨x, P, hc⟩ := hO
    rw [hc.ab_eq]
    exact P.nefFib_ab c
  obtain ⟨m, b, hm, hb, hD, -, hfin⟩ := hO.mbIs B hB u s hu hs (A.sh u s)
    (by rw [← h.aux.dir]; rfl) hdom c
  let W := h.mdl (FlagAr.setB O.Y B) c
  refine nefAt_of_cover hI W.V q (fun V pl => ?_) Z i hd
  obtain ⟨amp, hamp⟩ := pl _ _ _ _ (norms_of_induces W.amp_spec)
  choose R hR using fun x => pl _ _ _ _ (norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c W _ subset_rfl x))
  replace hR := fun x => (hR x).congr (f' := fun z => genAt (O.root0 c (FlagAr.setB O.Y B) x).D z)
    (a' := fun σ y => lnAdl (O.root0 c (FlagAr.setB O.Y B) x) σ y)
    (l' := fun v e y => (O.root0 c (FlagAr.setB O.Y B) x).lg v e y) (fun _ => pow_one _) (fun _ _ => by simp)
    fun _ _ _ => by simp
  have hmn : (0 : ℝ) < (m : ℝ) * ((O.Mb B u s c).n : ℕ) := mul_pos (Nat.cast_pos.2 hm) (Nat.cast_pos.2 (O.Mb B u s c).n.2)
  have hb0 : 0 ≤ b none := by
    have h₁ : (m : ℝ) * ((O.Mb B u s c).n : ℕ) * (s : ℝ) = b none * ((O.met.ab c).n : ℕ) := hb none
    have h₂ : (0 : ℝ) < b none * ((O.met.ab c).n : ℕ) := h₁ ▸ mul_pos hmn (by exact_mod_cast hs)
    have h₃ : (0 : ℝ) < b none := by
      by_contra hh
      push Not at hh
      nlinarith [(Nat.cast_nonneg ((O.met.ab c).n : ℕ) : (0 : ℝ) ≤ _)]
    exact_mod_cast h₃.le
  have hbx (x : DV.Rt D.what₂.Tau O.N) : (m : ℝ) * ((O.Mb B u s c).n : ℕ) * -A.sh u s x.1 x.2 = b (some x) :=
    (hb (some x)).trans (by
      change _ * (((1 : ℕ+) : ℕ) : ℝ) = _
      simp)
  have hn := hw V R hR (fun τ j => -b (some (τ, j))) fun τ j j' hj => by
    have h₁ := hbx (τ, j)
    have h₂ := hbx (τ, j')
    have h₃ := mul_le_mul_of_nonneg_left (hdom τ j j' hj) hmn.le
    have : ((-b (some (τ, j')) : ℤ) : ℝ) ≤ (-b (some (τ, j)) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  simp only [neg_neg] at hn
  have hna := (nefFib_iff amp).1 (GlobalTheory.T.nef_fibre_of_norms_power hP _ _ _ hab V amp W.k W.k_pos hamp) q Fact.out
  have hN := norms_tens _ _ V _ _ _ _ _ _ _ _ (norms_pow _ _ V _ _ _ _ (b none).toNat hamp)
    (norms_pow _ _ V _ _ _ _ W.k (norms_comb hR fun x => b (some x)))
  have hc : (((b none).toNat : ℕ) : ℝ) = b none := by exact_mod_cast Int.toNat_of_nonneg hb0
  obtain ⟨a', ha'⟩ := norms_of_comb (K := W.k) hD hfin (hN.congr (fun x => by
    rw [Fintype.prod_option, mul_pow, ← pow_mul, mul_comm W.k, pow_mul]
    refine congrArg₂ (· * ·) (congrArg (· ^ W.k) ?_) rfl
    rw [← zpow_natCast, Int.toNat_of_nonneg hb0]
    rfl) (fun _ _ => rfl) fun v e y => by
    rw [Fintype.sum_option, hc]
    simp only [Option.elim]
    ring)
  exact ⟨_, W.k * m, a', Nat.mul_pos W.k_pos hm, ha',
    nefOver_tens V.ar.isProjOver (nefOver_pow V.ar.isProjOver hna _) (nefOver_pow V.ar.isProjOver hn _)⟩

theorem nefAt_HT : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
  ∀ (B : ℝ), 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → WeightThresholdDefs.Dominant O.Y (A.sh u s) →
  ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
  (O.Mb B u s c).Induced M L k cf → ∀ (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ)
  [Fact q.Prime] [Algebra (ZMod q) Γ(Z, ⊤)], q ∈ FlagAr.setB O.Y B → topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1 := by
  intro hP hH D O hO hf A T H hR B hB u s hu hs hdom c M L k cf hI Z i _ _ q _ _ hq hd
  exact nefAt_of_weights hP hO hR hB hu hs hdom c q
    (fun V R hR' n hn => GlobalTheory.T.nef_over_antitone_comb hP hH D O hO hf A T H hR c _ V R hR' n hn q hq Fact.out) hI Z i hd

end GlobalTheory.NefHodgeTateAt
