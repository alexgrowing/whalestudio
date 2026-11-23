import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsRegular
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.EndoExtend

open GlobalTheory.CechPic

theorem pic_ext {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X) [Smooth P.hom]
    [GeometricallyIntegral P.hom] (e : X ⟶ P.left) (he : e ≫ P.hom = 𝟙 X) {a b : Pic P.left}
    (h₁ : CechPic.pull e a = CechPic.pull e b)
    (h₂ : CechPic.pull (pullback.fst P.hom j) a = CechPic.pull (pullback.fst P.hom j) b) : a = b := by
  rw [← sub_eq_zero, ← map_sub] at h₁ h₂
  rw [← sub_eq_zero]
  obtain ⟨N, hN, hc⟩ := cls_surj (a - b)
  rw [← hc] at h₁ h₂ ⊢
  exact (cls_eq_zero_iff hN).2 (GenericExtend.exists_isGen_of_densePart X U j hn ‹_› ‹_› ‹_› ‹_› P e N he ‹_› ‹_› hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₂))

section Cube

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • CechPic.pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls G x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls {T T' : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (u : T' ⟶ T)
    (h : ∀ i, x' i = u ≫ x i) (c : Pic G.left) : CechPic.pull u.left (cubeCls G x c) = cubeCls G x' c := by
  obtain rfl : x' = fun i => u ≫ x i := funext h
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z : T' ⟶ G => _ • CechPic.pull z.left c) (psum_hom (preHom u) x I.down)

theorem cubeCls_one {n : ℕ} (c : Pic G.left) (hc : CechPic.pull (eSec G) c = 0) :
    cubeCls G (fun _ : Fin n => (η[G] : 𝟙_ (Over S) ⟶ G)) c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have : psum G (fun _ : Fin n => (1 : 𝟙_ (Over S) ⟶ G)) I.down = 1 := by
    unfold psum
    induction (List.finRange n).filter (· ∈ I.down) with
    | nil => rfl
    | cons k l ih => exact (_root_.one_mul _).trans ih
  rw [e₁] at this
  rw [this]
  exact (congrArg (_ • ·) hc).trans (smul_zero _)

variable {G} in
theorem push_cubeCls {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (u : T'.left ⟶ T.left) (hu : u ≫ T.hom = T'.hom ≫ f)
    (hx : ∀ i, (x' i).left ≫ φ = u ≫ (x i).left) (c : Pic G.left) :
    CechPic.pull u (cubeCls G x c) = cubeCls G' x' (CechPic.pull φ c) := by
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp,
    psum_push h x' x (Over.homMk u hu) (fun i => Over.OverMorphism.ext (hx i)) I.down]
  rfl

end Cube

theorem hypS_of_densePart {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over X) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G)
    (hext : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback j).map F = f)
    (h : HypS ((Over.pullback j).obj G) (L.L.pull (pullback.fst G.hom j))) : HypS G L.L := by
  obtain ⟨w', wd', hw', hwd', hs, hp, ha⟩ := h
  obtain ⟨w, ⟨hw, rfl⟩, -⟩ := hext w' hw'
  obtain ⟨wd, ⟨hwd, rfl⟩, -⟩ := hext wd' hwd'
  have hL := L.isLB
  have hL' := pull_isLB hL (pullback.fst G.hom j)
  have hG := isGrpPullback_pullback G j
  have A : ∀ {Y Z : Over X} (a : Y ⟶ Z),
      ((Over.pullback j).map a).left ≫ pullback.fst Z.hom j = pullback.fst Y.hom j ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  have h0 : CechPic.pull (eSec G) (cls L.L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨L.rig, L.rigGen⟩
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  refine ⟨w, wd, hw, hwd, ?_, ?_, ?_⟩
  · refine (hext (𝟙 _) inferInstance).unique ⟨Serre.isMonHom_mul w wd, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_mul, hs]
  · refine (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 (Eq.trans ?_ (cls_cubeLB G _ hL).symm)
    refine pic_ext j hn G (eSec G) (Over.w η[G]) (h0.trans ?_) ?_
    · refine ((pull_cubeCls G _ (fun _ => η[G]) η[G] (fun i => ?_) _).trans (cubeCls_one G _ h0)).symm
      fin_cases i <;> simp
    · have e := ((cls_eq_iff hL' (LB.isLB_linComb hL' _ _)).2 hp).trans (cls_cubeLB ((Over.pullback j).obj G) _ hL')
      have e' := push_cubeCls hG (T' := (Over.pullback j).obj G) (T := G) ![𝟙 _, (Over.pullback j).map w] ![𝟙 G, w]
        (pullback.fst G.hom j) pullback.condition (fun i => by
          fin_cases i
          · simp
          · exact A w) (cls L.L hL)
      exact e.trans e'.symm
  · refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
    refine pic_ext j hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
    · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
        (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
      fin_cases i <;> simp
    · let δ := lift ((Over.pullback j).map (fst G G)) ((Over.pullback j).map (snd G G))
      have e := congrArg (CechPic.pull δ.left) ((cls_cubeLB ((Over.pullback j).obj G) _ hL').symm.trans
        (((cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL' _ _)).2 ha).trans
          (cls_cubeLB ((Over.pullback j).obj G) _ hL')))
      have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hG (T' := (Over.pullback j).obj (G ⊗ G)) (T := G ⊗ G)
        (fun i => (Over.pullback j).map (x i)) x (pullback.fst (G ⊗ G).hom j) pullback.condition (fun i => A _)
        (cls L.L hL)
      rw [pull_cubeCls _ _ (fun i => (Over.pullback j).map (![fst G G ≫ w, snd G G] i)) δ
          (fun i => by fin_cases i <;> simp [δ]),
        pull_cubeCls _ _ (fun i => (Over.pullback j).map (![fst G G, snd G G ≫ wd] i)) δ
          (fun i => by fin_cases i <;> simp [δ])] at e
      exact (e' _).trans (e.trans (e' _).symm)

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isIso_stalkClosedPointTo : IsIso (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) := by
  have e : M.stalkHom (M.pt (IsLocalRing.closedPoint Ω)) =
      (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom := by
    unfold RatModel.stalkHom
    erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  change Function.Bijective (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom
  rw [← e]
  refine ⟨M.stalkHom_injective _, fun x => ?_⟩
  have hx : x ∈ M.O (M.pt (IsLocalRing.closedPoint Ω)) := by
    have h := M.O_genericPoint
    rw [← M.pt_apply (IsLocalRing.closedPoint Ω)] at h
    exact h.ge trivial
  obtain ⟨a, ha⟩ := (M.stalkEquiv _).surjective ⟨x, hx⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem isPreimmersion_pt : IsPreimmersion M.pt := by
  have := isIso_stalkClosedPointTo M
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt]
  infer_instance

theorem flat_pt : Flat M.pt := by
  have := isIso_stalkClosedPointTo M
  have := GenericExt.flat_fromSpecStalk M.Z (M.pt (IsLocalRing.closedPoint Ω))
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt]
  infer_instance

end Model

theorem hypS_and_endo_and_iso_extend : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → HypS Q.G Q.L.L ∧ (∀ f : (Over.pullback M.pt).obj Q.G ⟶ (Over.pullback M.pt).obj Q.G, IsMonHom f → ∃! F : Q.G ⟶ Q.G, IsMonHom F ∧ (Over.pullback M.pt).map F = f) ∧ (∀ (n : ℕ) (x x' : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)), (∀ i, IsMonHom (x i) ∧ IsMonHom (x' i)) → ∀ ε ε' : Fin n → ℤ, ∑ i, ε i = 0 → ∑ i, ε' i = 0 → LBIso ((LB.LinComb Q.L.L (fun i => (x i).left) ε).pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) ((LB.LinComb Q.L.L (fun i => (x' i).left) ε').pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) → LBIso (LB.LinComb Q.L.L (fun i => (x i).left) ε) (LB.LinComb Q.L.L (fun i => (x' i).left) ε')) := by
  intro hdvr o Ω _ _ _ hA S ρ M U₀ Q hO
  have := hA.ded
  have := hA.ft
  have := hA.char
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hX : Geo.Tor.IsNormalScheme M.Z ∧ ∃ z : M.Z ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z :=
    ⟨hO.normal, _, MinorModel.locallyOfFiniteType_int M, MinorModel.flat_int M _⟩
  have := isPreimmersion_pt M
  have := flat_pt M
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have hL := Q.L.isLB
  refine ⟨?_, GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr _ _ M.pt hX ‹_› ‹_› inferInstance inferInstance _ _ Q.semi Q.semi, ?_⟩
  · have : Nonempty U₀ := hO.ne.to_subtype
    have : IsDominant U₀.ι := ⟨by
      rw [DenseRange, Scheme.Opens.range_ι]
      exact U₀.isOpen.dense hO.ne⟩
    have := ρ.P.isAb.comm
    refine hypS_of_densePart U₀.ι hO.normal Q.G Q.L (GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr _ _ U₀.ι hX inferInstance inferInstance
      inferInstance inferInstance _ _ Q.semi Q.semi) ?_
    have hP := ρ.P.isLB
    have h₁ : HypS ((Over.pullback Q.u₀).obj ρ.P.A) (Q.L.L.pull Q.φ) :=
      SymBaseChange.hypS_baseChange _ _ ρ.P.A ((Over.pullback Q.u₀).obj ρ.P.A) Q.u₀ (pullback.fst ρ.P.A.hom Q.u₀) _ _ hP (pull_isLB hL _)
        (isGrpPullback_pullback _ _) ⟨Q.w, Q.w_gen⟩ ρ.hypS
    let ψ := Q.cart.1.lift (pullback.fst Q.G.hom U₀.ι) (pullback.snd _ _) pullback.condition
    have hψ : ψ ≫ Q.φ = pullback.fst Q.G.hom U₀.ι := Q.cart.1.lift_fst _ _ _
    refine SymBaseChange.hypS_baseChange _ _ ((Over.pullback Q.u₀).obj ρ.P.A) ((Over.pullback U₀.ι).obj Q.G) (𝟙 _) ψ _ _ (pull_isLB hL _) (pull_isLB hL _)
      (Q.cart.cancel ((isGrpPullback_pullback Q.G U₀.ι).congr (Category.id_comp _).symm hψ.symm)
        ((Q.cart.1.lift_snd _ _ _).trans (Category.comp_id _).symm)) ?_ h₁
    refine (cls_eq_iff (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)).1 ?_
    exact (congrArg (CechPic.pull · (cls _ hL)) hψ.symm).trans (pull_comp ψ Q.φ (cls _ hL))
  · intro n x x' hx ε ε' _ _ h
    have := smooth_tensorObj_hom Q.G Q.G
    have := geometricallyIntegral_tensorObj_hom Q.G Q.G
    have h0 : CechPic.pull (eSec Q.G) (cls Q.L.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨Q.L.rig, Q.L.rigGen⟩
    have key : ∀ (y : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)) (δ : Fin n → ℤ), (∀ i, IsMonHom (y i)) →
        CechPic.pull (η[Q.G ⊗ Q.G]).left (cls _ (LB.isLB_linComb hL (fun i => (y i).left) δ)) = 0 := by
      intro y δ hy
      rw [cls_linComb hL, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, ← pull_comp, ← Over.comp_left, (hy i).one_hom]
      exact (congrArg (_ • ·) h0).trans (smul_zero _)
    refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      (pic_ext M.pt hO.normal (Q.G ⊗ Q.G) (η[Q.G ⊗ Q.G]).left (Over.w _)
        ((key x ε fun i => (hx i).1).trans (key x' ε' fun i => (hx i).2).symm) ?_)
    exact (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2 h

end GlobalTheory.ZH.EndoExtend
