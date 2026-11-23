import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def MemKL (L : LB A.left) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    ∃ c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen

theorem kTriv_iff_memKL (L : LB A.left) : Out.KTriv A L ↔
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (x : Over.mk t ⟶ A), MemKL A L x → x = toUnit _ ≫ η[A] :=
  Iff.rfl

end

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem memKL_of_push (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} (x : T' ⟶ A') (hx : MemKL A L (pushPt h.1.w x)) : MemKL A' L' x := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (T'.hom ≫ f)
  let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk (fst T' A').left (by
    show (fst T' A').left ≫ T'.hom ≫ f = (T' ⊗ A').hom ≫ f
    rw [← Category.assoc, Over.w (fst T' A')])
  let U : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T ⊗ A := lift a (pushPt h.1.w (snd T' A'))
  have k₁ : U.left ≫ (fst T A).left = (fst T' A').left := congrArg (fun q => q.left) (lift_fst a _)
  have k₂ : U.left ≫ (snd T A).left = (snd T' A').left ≫ φ :=
    congrArg (fun q => q.left) (lift_snd a (pushPt h.1.w (snd T' A')))
  have k₃ : U.left ≫ ((fst T A ≫ pushPt h.1.w x) * snd T A).left =
      ((fst T' A' ≫ x) * snd T' A').left ≫ φ := by
    have e := h.2 (T' ⊗ A') (fst T' A' ≫ x) (snd T' A') (U ≫ fst T A ≫ pushPt h.1.w x) (U ≫ snd T A)
      (by
        show U.left ≫ (fst T A).left ≫ x.left ≫ φ = ((fst T' A').left ≫ x.left) ≫ φ
        rw [← Category.assoc, k₁, Category.assoc]) k₂
    rw [← MonObj.comp_mul] at e
    exact e
  obtain ⟨n, hn⟩ : ∃ n : ((fst T' A').left ⁻¹ᵁ V).toScheme ⟶ ((fst T A).left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T A).left ⁻¹ᵁ V).ι = ((fst T' A').left ⁻¹ᵁ V).ι ≫ U.left :=
    ⟨IsOpenImmersion.lift _ (((fst T' A').left ⁻¹ᵁ V).ι ≫ U.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
  let φ' : Fin 2 → (((fst T' A').left ⁻¹ᵁ V).toScheme ⟶ A'.left) := fun k => ((fst T' A').left ⁻¹ᵁ V).ι ≫
    (![(lift (fst T' A' ≫ x) (snd T' A') ≫ μ[A']).left, (snd T' A').left] : Fin 2 → _) k
  obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k => φ' k ≫ φ) _ ![1, -1] n (fun k => by
    show (_ ≫ _) ≫ φ = n ≫ _ ≫ _
    rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
    fin_cases k
    exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm])) c₁ h₁
  obtain ⟨c₃, h₃⟩ := exists_down hw hL hL' c₂ h₂
  exact gen_chartPull (chartPullOut L' _ _ _ φ' fun _ => rfl) c₃ h₃

end

theorem sym_of_lbIso_neg {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
    (h : LBIso L (L.pull (GrpObj.inv : A ⟶ A).left)) : Out.Sym A L := by
  obtain ⟨w, hw⟩ := h
  intro s
  refine ⟨⊤, trivial, ?_⟩
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (![(A.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ ⊤).ι] : Fin 2 → _) j ≤
      (A.hom ⁻¹ᵁ ⊤).ι ⁻¹ᵁ ((L.pull (GrpObj.inv : A ⟶ A).left).U (fun _ => j 0) ⊓ L.U (j 1)) := fun j y hy =>
    ⟨mem_pull.2 (Set.mem_iInter.1 hy 0), Set.mem_iInter.1 hy 1⟩
  refine gen_chartPull (h := (A.hom ⁻¹ᵁ ⊤).ι) (A := LB.div (L.pull (GrpObj.inv : A ⟶ A).left) L)
    ⟨fun j => (fun _ => j 0, j 1), le, fun y j j' hj hj' => ?_⟩ w hw
  refine (gm_linComb L _ _ (𝟙 _) y j j' hj hj').trans (Eq.trans ?_
    (gm_div L (L.pull (GrpObj.inv : A ⟶ A).left) (A.hom ⁻¹ᵁ ⊤).ι y (fun _ => j 0, j 1) (fun _ => j' 0, j' 1)
      ⟨le j hj, le j' hj'⟩).symm)
  refine (Fin.prod_univ_two _).trans (congrArg₂ (· * ·) ?_ ?_)
  · refine Eq.trans ?_ (gm_pull_g L _ _ y (fun _ => j 0) (fun _ => j' 0) (le j hj).1 (le j' hj').1).symm
    rw [Category.id_comp]
    exact zpow_one _
  · rw [Category.id_comp]
    exact zpow_neg_one _

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _))).symm)
  have e₁ := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have e₂ := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  exact (eq_mul_inv_of_mul_eq (e₂.trans e₁.symm)).trans (mul_right_comm _ _ _)

theorem memKL_one {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (T : Over S) :
    MemKL A L (1 : T ⟶ A) := by
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have e : lift (fst T A ≫ (1 : T ⟶ A)) (snd T A) ≫ μ[A] = snd T A := by
    change (fst T A ≫ (1 : T ⟶ A)) * snd T A = snd T A
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨c, hc, -⟩ := exists_gen hL (φ := (PEmpty.elim : PEmpty → ((T ⊗ A).left ⟶ A.left))) (ε := PEmpty.elim)
    (φ' := (![(lift (fst T A ≫ (1 : T ⟶ A)) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun V _ h => by rw [e]; simp [Fin.prod_univ_two]) (LB.oneGen L)
    (fun i j => (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Finset.prod_of_isEmpty _) (map_one _)).trans
      (_root_.one_mul _))))
  exact gen_chartPull (chartPullPull _ _ _ rfl) c hc

theorem MemKL.comp {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {x : T ⟶ A}
    (hx : MemKL A L x) (u : T' ⟶ T) : MemKL A L (u ≫ x) := by
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx (u.left p)
  refine ⟨u.left ⁻¹ᵁ V, hV, ?_⟩
  let U : T' ⊗ A ⟶ T ⊗ A := lift (fst T' A ≫ u) (snd T' A)
  have k₁ : U ≫ fst T A = fst T' A ≫ u := lift_fst _ _
  have k₂ : U ≫ snd T A = snd T' A := lift_snd _ _
  have k₃ : U ≫ ((fst T A ≫ x) * snd T A) = (fst T' A ≫ u ≫ x) * snd T' A := by
    rw [MonObj.comp_mul, k₂, ← Category.assoc, k₁, Category.assoc]
  obtain ⟨n, hn⟩ : ∃ n : ((fst T' A).left ⁻¹ᵁ (u.left ⁻¹ᵁ V)).toScheme ⟶ ((fst T A).left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T A).left ⁻¹ᵁ V).ι = ((fst T' A).left ⁻¹ᵁ (u.left ⁻¹ᵁ V)).ι ≫ U.left :=
    ⟨IsOpenImmersion.lift _ (((fst T' A).left ⁻¹ᵁ (u.left ⁻¹ᵁ V)).ι ≫ U.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q.left y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₁ h₁ n)
  show n ≫ _ ≫ _ = _
  rw [← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

theorem memKL_iff_of_kTriv {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hk : Out.KTriv A L) {T : Over S} (x : T ⟶ A) : MemKL A L x ↔ ∃ z : T ⟶ 𝟙_ (Over S), z ≫ η[A] = x := by
  refine ⟨fun hx => ⟨toUnit T, Over.OverMorphism.ext (T.left.affineCover.hom_ext _ _ fun i => ?_)⟩, ?_⟩
  · obtain ⟨R, ⟨e⟩⟩ : ∃ R : CommRingCat.{0}, Nonempty (Spec R ≅ T.left.affineCover.X i) :=
      ⟨_, ⟨(T.left.affineCover.X i).isoSpec.symm⟩⟩
    let u : Over.mk ((e.hom ≫ T.left.affineCover.f i) ≫ T.hom) ⟶ T := Over.homMk (e.hom ≫ T.left.affineCover.f i) rfl
    have h₁ : u ≫ toUnit T ≫ η[A] = u ≫ x := by
      rw [← Category.assoc, comp_toUnit]
      exact (hk R _ (u ≫ x) (hx.comp u)).symm
    rw [← cancel_epi e.hom, ← Category.assoc, ← Category.assoc e.hom]
    exact congrArg (fun q => q.left) h₁
  · rintro ⟨z, rfl⟩
    rw [toUnit_unique z (toUnit T)]
    exact memKL_one hL T

namespace Published

def AmpleOfGenericSt : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (A : Over (Sp V)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.Rigidified A L → Out.Sym A L →
    ∀ (A' : Over (Sp K)) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap V K)) →
    ∀ L' : LB A'.left, L'.IsLB → LBIso L' (L.pull φ) → Out.RelAmple A' L' → Out.RelAmple A L

def KernelFiniteFlatSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsNoetherianRing V] (A : Over (Sp V)) [GrpObj A], IsAbelianScheme A →
    ∀ L : LB A.left, L.IsLB → Out.RelAmple A L →
    ∃ (Z : Over (Sp V)) (i : Z ⟶ A), IsClosedImmersion i.left ∧ IsFinite Z.hom ∧ Flat Z.hom ∧
      ∀ (T : Over (Sp V)) (x : T ⟶ A), MemKL A L x ↔ ∃ z : T ⟶ Z, z ≫ i = x

def PolExtSt : Prop := AmpleOfGenericSt ∧ KernelFiniteFlatSt

theorem KernelFiniteFlatSt.kTriv_of_generic (hK : KernelFiniteFlatSt) {V K : Type} [CommRing V] [IsDomain V]
    [IsNoetherianRing V] [Field K] [Algebra V K] [IsFractionRing V K] {A : Over (Sp V)} [GrpObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) (ha : Out.RelAmple A L) {A' : Over (Sp K)} [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap V K)) φ) {L' : LB A'.left} (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hk : Out.KTriv A' L') : Out.KTriv A L := by
  obtain ⟨Z, i, -, hfin, hflat, hZ⟩ := hK V A hA L hL ha
  have := hA.proper
  have := schemeTheoreticallyDominant_fractionField V K
  let Y := pullback Z.hom (spMap (algebraMap V K))
  have : IsAffine Y := isAffine_of_isAffineHom (pullback.snd Z.hom (spMap (algebraMap V K)))
  have : IsSchemeTheoreticallyDominant (pullback.fst Z.hom (spMap (algebraMap V K))) :=
    .of_isPullback (IsPullback.of_hasPullback Z.hom (spMap (algebraMap V K))).flip
  let d : Sp Γ(Y, ⊤) ⟶ Z.left := Y.isoSpec.inv ≫ pullback.fst Z.hom (spMap (algebraMap V K))
  let t : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd Z.hom (spMap (algebraMap V K))
  have hd : d ≫ Z.hom = t ≫ spMap (algebraMap V K) := by
    simp only [d, t, Category.assoc, pullback.condition]
  have hdi : (d ≫ i.left) ≫ A.hom = t ≫ spMap (algebraMap V K) := by
    rw [Category.assoc, Over.w i, hd]
  let x : Over.mk t ⟶ A' := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
  let z : Over.mk (t ≫ spMap (algebraMap V K)) ⟶ Z := Over.homMk d hd
  have hz : z ≫ i = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
  have hx : x = 1 := hk _ t x (memKL_of_push h hL hL' hw x ((hZ _ _).2 ⟨z, hz⟩))
  have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
  have hi : i = toUnit Z ≫ η[A] := by
    have : IsSchemeTheoreticallyDominant d := by
      dsimp only [d]; infer_instance
    refine over_ext_of_schemeTheoreticallyDominant d (congrArg (fun q => q.left)
      (show z ≫ i = z ≫ toUnit Z ≫ η[A] from ?_))
    rw [hz, hx', ← Category.assoc, comp_toUnit]
    rfl
  intro R _ s y hy
  obtain ⟨u, rfl⟩ := (hZ _ y).1 hy
  rw [hi, ← Category.assoc, comp_toUnit]

namespace PolExtSt

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

theorem relAmple_and_kTriv (hP : PolExtSt) {A : Over (Sp V)} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    (hL : L.IsLB) (hr : Out.Rigidified A L) (hs : Out.Sym A L) {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A (spMap (algebraMap V K)) φ) {L' : LB A'.left} (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (ha : Out.RelAmple A' L') (hk : Out.KTriv A' L') : Out.RelAmple A L ∧ Out.KTriv A L :=
  have a := hP.1 V K A hA L hL hr hs A' φ h.1 L' hL' hw ha
  ⟨a, hP.2.kTriv_of_generic hA hL a h hL' hw hk⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sab (hP : PolExtSt) (t : SAB H (Sp V)) (hA : IsAbelianScheme t.G) {A' : Over (Sp K)} [GrpObj A']
    {φ : A'.left ⟶ t.G.left} (h : IsGrpPullback A' t.G (spMap (algebraMap V K)) φ) {L' : LB A'.left} (hL' : L'.IsLB)
    (hw : LBIso L' (t.PP.L.pull φ)) (ha : Out.RelAmple A' L') (hk : Out.KTriv A' L') :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨_, w, hs, -⟩ := t.sym
  exact hP.relAmple_and_kTriv hA t.PP.isLB ⟨t.PP.rig, t.PP.rigGen⟩ (sym_of_lbIso_neg ⟨w, hs⟩) h hL' hw ha hk

end PolExtSt

end Published

end GlobalTheory
