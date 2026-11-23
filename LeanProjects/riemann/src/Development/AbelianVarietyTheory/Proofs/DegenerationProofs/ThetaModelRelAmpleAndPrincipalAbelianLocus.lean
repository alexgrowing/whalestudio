import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsChartUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.AbPol

open GlobalTheory.CechPic

theorem pic_ext_local {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X) [Smooth P.hom]
    [GeometricallyIntegral P.hom] (e : X ⟶ P.left) (he : e ≫ P.hom = 𝟙 X) {a b : Pic P.left}
    (h : CechPic.pull (pullback.fst P.hom j) a = CechPic.pull (pullback.fst P.hom j) b) (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      CechPic.pull (P.hom ⁻¹ᵁ V).ι a = CechPic.pull (P.hom ⁻¹ᵁ V).ι b := by
  rw [← sub_eq_zero, ← map_sub] at h
  have key : a - b = CechPic.pull P.hom (CechPic.pull e (a - b)) := by
    refine EndoExtend.pic_ext j hn P e he ?_ ?_
    · rw [← pull_comp, he, pull_id]
    · let eU : U ⟶ pullback P.hom j :=
        pullback.lift (j ≫ e) (𝟙 U) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
      have h₁ : eU ≫ pullback.fst P.hom j = j ≫ e := pullback.lift_fst _ _ _
      rw [h, ← pull_comp, pullback.condition, pull_comp, ← pull_comp j, ← h₁, pull_comp eU, h, map_zero, map_zero]
  obtain ⟨D, hD, hc⟩ := cls_surj (CechPic.pull e (a - b))
  obtain ⟨i, hi⟩ := exists_chart hD x
  obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset hi
  refine ⟨V, hV, hx, ?_⟩
  rw [← sub_eq_zero, ← map_sub, key, ← hc, ← pull_comp]
  exact (cls_eq_zero_iff (pull_isLB hD _)).2 (IsoExtend.exists_gen_of_chart hD _ i fun y => hle y.2)

theorem relAmple_of_densePart {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hn : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X)
    [Smooth P.hom] [IsProper P.hom] [GeometricallyIntegral P.hom] (e : X ⟶ P.left) (he : e ≫ P.hom = 𝟙 X)
    {L O : LB P.left} (hL : L.IsLB) (hO : O.IsLB) {N : ℕ} (hN : 1 ≤ N) (ha : RelAmple P O)
    (h : CechPic.pull (pullback.fst P.hom j) (N • cls L hL) = CechPic.pull (pullback.fst P.hom j) (cls O hO)) :
    RelAmple P L := by
  refine AmpleLocal.relAmple_of_locally X P L hL inferInstance inferInstance fun x => ?_
  obtain ⟨V, hV, hx, hc⟩ := pic_ext_local j hn P e he h x
  refine ⟨V, hx, ?_⟩
  have : IsAffine V := hV
  have : IsProper (Over.mk (P.hom ∣_ V)).hom := inferInstanceAs (IsProper (P.hom ∣_ V))
  have hL' := pull_isLB hL (P.hom ⁻¹ᵁ V).ι
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk (P.hom ∣_ V)) hL').2 ?_
  refine (isAmpleLB_pow_iff hL' hN).1 ((isAmpleLB_of_relAmple P hO ha V hV).of_lbIso (isLB_lbPow hL' N) ?_)
  refine (cls_eq_iff (isLB_lbPow hL' N) (pull_isLB hO _)).1 ?_
  rw [cls_lbPow hL', cls_pull hL, cls_pull hO, ← hc, map_nsmul]

theorem exists_comb {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) {H : LB Y} {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → R) : ∃ σ : H.Sec, ∀ l, σ.f l = ∑ j, constFn q (H.U l) (a j) * (s j).f l := by
  have hres : ∀ {U V : Y.Opens} (h : V ≤ U) (c : R),
      (Y.presheaf.map (homOfLE h).op).hom (constFn q U c) = constFn q V c := fun h c => by
    exact congrArg (fun z => z.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
      (q.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)
  refine ⟨⟨fun l => ∑ j, constFn q (H.U l) (a j) * (s j).f l, fun i k => ?_⟩, fun _ => rfl⟩
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, hres, hres, (s j).compat i k]
  ring

theorem valR_comb {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} (q : Y ⟶ Sp R) (r : Y ⟶ X) {H : LB X}
    {J : Type} [Fintype J] (s : J → H.Sec) (a : J → R) (σ : (H.pull r).Sec)
    (hσ : ∀ l, σ.f l = ∑ j, constFn q ((H.pull r).U l) (a j) * (GlobalTheory.secPull (s j) r).f l) (x : Sp K ⟶ Y)
    (l : (H.pull r).ι) (hx : ⊤ ≤ x ⁻¹ᵁ (H.pull r).U l) :
    valR x _ (σ.f l) = ∑ j, (Spec.preimage (x ≫ q)).hom (a j) * valF (x ≫ r) _ ((s j).f (l PUnit.unit)) := by
  rw [hσ, Points.valR_eq x _ hx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← Points.valR_eq, ← Points.valR_eq, Points.valR_constFn q x _ hx]
  exact congrArg _ (Points.valR_appLE x r _ hx _)

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem cls_generic (hU : (U₀ : Set M.Z).Nonempty) {H Y : Scheme.{0}} [IsIntegral Y] (i : H ⟶ Q.G.left) (k : Y ⟶ H)
    (q : Y ⟶ Sp Ω) (w : (k ≫ i) ≫ Q.G.hom = q ≫ M.pt) (b : Matrix S.J S.J Ω) (O : LB H) (τ : S.J → LB.Sec O)
    (hO : O.IsLB) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (h : ∀ (K : Type) [Field K] (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (g' : Sp K ⟶ H)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι) (jO : O.ι),
      g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt → g' ≫ i = g ≫ Q.φ →
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
      Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range g' ⊆ O.U jO →
      ∃ c : K, c ≠ 0 ∧ ∀ i, ∑ l, β (b i l) * valF r _ ((ρ.s l).f (fun _ => jP)) = c * valF g' _ ((τ i).f jO)) :
    CechPic.pull k (S.N • CechPic.pull i (cls Q.L.L Q.L.isLB)) = CechPic.pull k (cls O hO) := by
  have hP := ρ.P.isLB
  have hL := Q.L.isLB
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hU)
  let x₀ : Sp Ω ⟶ U₀ := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx₀ : x₀ ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have w' : (k ≫ i) ≫ Q.G.hom = (q ≫ x₀) ≫ U₀.ι := by rw [w, Category.assoc, hx₀]
  let g₀ : Y ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift (k ≫ i) (q ≫ x₀) w'
  have g₁ : g₀ ≫ Q.φ = k ≫ i := Q.cart.1.lift_fst _ _ _
  have g₂ : g₀ ≫ pullback.snd _ _ = q ≫ x₀ := Q.cart.1.lift_snd _ _ _
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Y ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left,
      r₀ ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g₀ ≫ pullback.fst _ _ :=
    ⟨pullback.lift ((g₀ ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g₀ ≫ pullback.fst _ _) (Category.comp_id _),
      pullback.lift_snd _ _ _⟩
  have hN : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB := LB.isLB_linComb hP _ _
  choose σ hσ using fun i => exists_comb q (fun l => GlobalTheory.secPull (ρ.s l) r₀) (b i)
  obtain ⟨u, hu, -⟩ := CrdIso.exists_iso_of_crd Y (O.pull k) _ S.J (fun i => GlobalTheory.secPull (τ i) k) σ
    (pull_isLB hO k) (pull_isLB hN r₀) (by
      simp only [GlobalTheory.nonzeroLocus_secPull]
      rw [← Scheme.Hom.preimage_iSup, hτ]
      rfl) (by
      rintro K _ x v ⟨l, c, hl, hv⟩
      obtain ⟨jP, hj⟩ := exists_chart hP ((x ≫ g₀ ≫ pullback.fst _ _) (IsLocalRing.closedPoint K))
      have hj' : ⊤ ≤ (x ≫ g₀ ≫ pullback.fst _ _) ⁻¹ᵁ ρ.P.L.U jP := (Points.le_preimage_iff _ _).2 hj
      have hβ : spMap (Spec.preimage (x ≫ q)).hom = x ≫ q := Spec.map_preimage _
      have hl' : ⊤ ≤ (x ≫ k) ⁻¹ᵁ O.U (l PUnit.unit) := fun y _ =>
        (mem_pull (L := O) (F := k) (J := l)).1 (hl (x := y) trivial)
      obtain ⟨d, hd, e⟩ := h K (Spec.preimage (x ≫ q)).hom (x ≫ g₀) (x ≫ k) (x ≫ r₀) jP (l PUnit.unit)
        (by rw [hβ, Category.assoc, reassoc_of% g₂, hx₀, Category.assoc])
        (by rw [Category.assoc, Category.assoc, g₁]) (by rw [Category.assoc, Category.assoc, hr₀])
        ((top_le_preimage_iff _ _).1 (by rwa [Category.assoc])) ((top_le_preimage_iff _ _).1 hl')
      have hx : ⊤ ≤ x ⁻¹ᵁ ((LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).pull r₀).U (fun _ _ => jP) := fun y _ => by
        refine mem_pull.2 (Set.mem_iInter.2 fun _ => ?_)
        have := hj' (x := y) trivial
        rw [← hr₀] at this
        exact this
      refine ⟨fun _ _ => jP, c * (Units.mk0 d hd)⁻¹, hx, fun i => ?_⟩
      have e₁ : valR x _ ((GlobalTheory.secPull (τ i) k).f l) = valF (x ≫ k) _ ((τ i).f (l PUnit.unit)) :=
        Points.valR_appLE x k _ hl _
      have e₂ := valR_comb q r₀ ρ.s (b i) (σ i) (hσ i) x _ hx
      rw [hv, e₁, e₂.trans (e i)]
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, _root_.mul_assoc, inv_mul_cancel_left₀ hd])
  have e₁ := (cls_eq_iff (pull_isLB hO k) (pull_isLB hN r₀)).2 ⟨u, hu⟩
  have e₂ := (cls_eq_iff (pull_isLB hL Q.φ) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
  have e₃ : cls _ hN = S.N • CechPic.pull (snd (baseOver (Sp S.R)) ρ.P.A).left (cls _ hP) :=
    (cls_linComb hP _ _ _).trans (by rw [Fin.sum_univ_one, natCast_zsmul])
  rw [cls_pull hL, cls_pull hP] at e₂
  rw [cls_pull hO, cls_pull hN, e₃] at e₁
  rw [e₁, map_nsmul, map_nsmul, ← pull_comp, ← pull_comp, ← g₁, hr₀, pull_comp, pull_comp, e₂]

theorem isNormalScheme_opens {X : Scheme.{0}} (h : Geo.Tor.IsNormalScheme X) (V : X.Opens) :
    Geo.Tor.IsNormalScheme V.toScheme := fun x => by
  obtain ⟨h₁, h₂⟩ := h x.1
  have e := (V.stalkIso x).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

theorem relAmple_affine [IsLocallyNoetherian M.Z] (hO : S.Over₀ M U₀) {EE : M.Lat S.J} (hs : Q.SecO EE) (hA : Q.Ab)
    (V : M.Z.Opens) (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) (hab : (V : Set M.Z) ⊆ abLocus Q.G)
    (b : Matrix S.J S.J Ω) (hb : ∀ z ∈ V, EE.E z = Submodule.span (M.O z) (Set.range b)) :
    RelAmple (Over.mk (Q.G.hom ∣_ V)) (Q.L.L.pull (Q.G.hom ⁻¹ᵁ V).ι) := by
  obtain ⟨O, τ, hO', hτ, h, -, ha⟩ := hs V b hV hb
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ Q.G
  have sq := (isPullback_morphismRestrict Q.G.hom V).flip
  have : Smooth (Over.mk (Q.G.hom ∣_ V)).hom := inferInstanceAs (Smooth (Q.G.hom ∣_ V))
  have : GeometricallyIntegral (Over.mk (Q.G.hom ∣_ V)).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) sq ‹_›
  have : IsProper (Over.mk (Q.G.hom ∣_ V)).hom := by
    have := hA.2 V hab
    change IsProper (Q.G.hom ∣_ V)
    rw [← sq.isoPullback_hom_snd]
    infer_instance
  have hr : Set.range M.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hne)
  let j : Sp Ω ⟶ V := IsOpenImmersion.lift V.ι M.pt hr
  have hj : j ≫ V.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have sqj := (IsOpenImmersion.isPullback_lift_id M.pt V.ι hr).flip
  have : IsPreimmersion j :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) sqj (EndoExtend.isPreimmersion_pt M)
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) sqj (EndoExtend.flat_pt M)
  have : IsDominant (j ≫ V.ι) := hj ▸ M.isDominant_pt
  have : IsDominant j := IsDominant.of_comp_of_isOpenImmersion j V.ι
  have he : eSec Q.G ≫ Q.G.hom = 𝟙 _ := Over.w _
  have : IsIntegral (pullback (Q.G.hom ∣_ V) j) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback (Q.G.hom ∣_ V) j)
  refine relAmple_of_densePart j (isNormalScheme_opens hO.normal V) (Over.mk (Q.G.hom ∣_ V))
    (sq.lift (V.ι ≫ eSec Q.G) (𝟙 _) (by rw [Category.assoc, he, Category.id_comp]; exact Category.comp_id _))
    (sq.lift_snd _ _ _) (pull_isLB Q.L.isLB _) hO' (N := S.N) (one_le_two.trans S.N_ge) (ha hab) ?_
  refine cls_generic Q hO.ne (Q.G.hom ⁻¹ᵁ V).ι (pullback.fst (Q.G.hom ∣_ V) j) (pullback.snd _ _) ?_ b O τ hO' hτ h
  rw [Category.assoc, sq.w, pullback.condition_assoc, hj]

theorem relAmple_open [IsLocallyNoetherian M.Z] (hO : S.Over₀ M U₀) {EE : M.Lat S.J} (hs : Q.SecO EE) (hA : Q.Ab)
    (W : M.Z.Opens) (hW : (W : Set M.Z) ⊆ abLocus Q.G) :
    RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) := by
  have hL := Q.L.isLB
  have : IsProper ((Over.pullback W.ι).obj Q.G).hom := hA.2 W hW
  refine AmpleLocal.relAmple_of_locally _ _ _ (pull_isLB hL _) inferInstance inferInstance fun s => ?_
  obtain ⟨B, b, hz, -, hb⟩ := EE.loc s.1
  obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := B ⊓ W) (x := s.1) ⟨hz, s.2⟩
  have ha := relAmple_affine Q hO hs hA V hV ⟨_, hx⟩ (fun z hz => hW (hle hz).2) b fun z hz => hb z (hle hz).1
  refine ⟨W.ι ⁻¹ᵁ V, hx, ?_⟩
  have h := IsPullback.of_hasPullback Q.G.hom W.ι
  have le' : pullback.snd Q.G.hom W.ι ⁻¹ᵁ (W.ι ⁻¹ᵁ V) ≤ pullback.fst Q.G.hom W.ι ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ V) :=
    fun y hy => (congrArg (fun q => q y ∈ V) h.w).mpr hy
  let ψ := (pullback.fst Q.G.hom W.ι).resLE _ _ le'
  have hψ : ψ ≫ (Q.G.hom ⁻¹ᵁ V).ι = _ ≫ pullback.fst Q.G.hom W.ι := Scheme.Hom.resLE_comp_ι _ le'
  have H : IsPullback ψ (pullback.snd Q.G.hom W.ι ∣_ (W.ι ⁻¹ᵁ V)) (Q.G.hom ∣_ V) (W.ι ∣_ V) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict Q.G.hom V).flip
    · rw [hψ, morphismRestrict_ι]
      exact (isPullback_morphismRestrict _ _).flip.paste_horiz h
    · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
        reassoc_of% hψ, h.w, morphismRestrict_ι_assoc]
  obtain ⟨w, hw⟩ : LBIso ((Q.L.L.pull (pullback.fst Q.G.hom W.ι)).pull
      (pullback.snd Q.G.hom W.ι ⁻¹ᵁ (W.ι ⁻¹ᵁ V)).ι) ((Q.L.L.pull (Q.G.hom ⁻¹ᵁ V).ι).pull ψ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)).1 ?_
    rw [cls_pull (pull_isLB hL _), cls_pull (pull_isLB hL _), cls_pull hL, cls_pull hL, ← pull_comp, ← pull_comp, hψ]
  have : IsAffine V := hV
  exact relAmple_pull (A := Over.mk (Q.G.hom ∣_ V)) (A' := Over.mk (pullback.snd Q.G.hom W.ι ∣_ (W.ι ⁻¹ᵁ V))) H
    (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha

theorem kTriv_of_factor {T : Scheme.{0}} (G' : Over T) [GrpObj G'] (f : T ⟶ U₀) (φ : G'.left ⟶ Q.G.left)
    (h : IsGrpPullback G' Q.G (f ≫ U₀.ι) φ) {L' : LB G'.left} (hL' : L'.IsLB) (e : LBIso L' (Q.L.L.pull φ)) :
    KTriv G' L' := by
  have hP := ρ.P.isLB
  have hL := Q.L.isLB
  let ψ := Q.cart.1.lift φ (G'.hom ≫ f) (h.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ Q.φ = φ := Q.cart.1.lift_fst _ _ _
  have h₁ := (Q.cart.cancel (h.congr rfl hψ.symm) (Q.cart.1.lift_snd _ _ _)).comp
    (isGrpPullback_pullback ρ.P.A Q.u₀)
  obtain ⟨w, hw⟩ : LBIso L' (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Q.u₀)) := by
    have e₁ := (cls_eq_iff hL' (pull_isLB hL _)).2 e
    have e₂ := (cls_eq_iff (pull_isLB hL Q.φ) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
    refine (cls_eq_iff hL' (pull_isLB hP _)).1 (e₁.trans ?_)
    rw [cls_pull hL, cls_pull hP] at e₂
    rw [cls_pull hL, cls_pull hP, ← hψ]
    exact (pull_comp ψ Q.φ _).trans ((congrArg _ e₂).trans (pull_comp ψ _ _).symm)
  exact kTriv_pull h₁ hP hL' ((isGen_iff w).1 hw) ρ.P.ktriv

end Model

theorem relAmple_and_kTriv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), Laws → S.Over₀ M U₀ → Q.SecO EE → Q.Ab → ∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) := by
  intro o Ω _ _ _ hB S ρ M U₀ EE Q laws hO hs hA W hW
  have := hB.ded
  have := hB.char
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have ha := relAmple_open Q hO hs hA W hW
  refine ⟨ha, ?_⟩
  rcases (W : Set M.Z).eq_empty_or_nonempty with h0 | hne
  · intro R _ t x _
    have : IsEmpty (Spec (CommRingCat.of R)) := ⟨fun p => (h0.le (t p).2 : False)⟩
    exact Over.OverMorphism.ext ((isInitialOfIsEmpty (X := Spec (CommRingCat.of R))).hom_ext _ _)
  have : Nonempty W := hne.to_subtype
  have hL := Q.L.isLB
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have gp := isGrpPullback_pullback Q.G W.ι
  obtain ⟨hL', hr, ⟨c, -⟩, -⟩ := CubePf.cubePull _ _ Q.G _ (cubeMapOf gp) Q.L Q.cub
  have hab : IsAbelianScheme ((Over.pullback W.ι).obj Q.G) :=
    ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) gp.1 ‹_›, hA.2 W hW,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) gp.1 ‹_›⟩
  refine GlobalTheory.T.kTriv_of_kTriv_nonemptyOpen_normal_charZero laws W (isNormalScheme_opens hO.normal W) (fun n hn h => ?_) (W.ι ⁻¹ᵁ U₀) ?_ _
    ((cubeMapOf gp).rigLB Q.L hL' hr) c hab ha ?_
  · have e := congrArg ((M.res W hne).comp W.topIso.hom.hom) h
    rw [map_natCast, map_zero] at e
    exact hn (Nat.cast_eq_zero.1 e)
  · obtain ⟨z, hz⟩ := M.nonempty_inf hne hO.ne
    exact ⟨⟨z, hz.1⟩, hz.2⟩
  · refine kTriv_of_factor Q _ (W.ι ∣_ U₀) _ (((isGrpPullback_pullback _ (W.ι ⁻¹ᵁ U₀).ι).comp gp).congr
      (morphismRestrict_ι _ _).symm rfl) (pull_isLB hL' _) ?_
    exact (cls_eq_iff (pull_isLB hL' _) (pull_isLB hL _)).1 (pull_comp _ _ (cls _ hL)).symm

end GlobalTheory.ZH.AbPol

end
