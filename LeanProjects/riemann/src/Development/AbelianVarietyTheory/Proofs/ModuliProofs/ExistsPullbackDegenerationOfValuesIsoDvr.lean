import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnesses
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsPullCubicalOfIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesIdent
open GlobalTheory.ArcPull (om pmaps_om mul_push)

theorem exists_psiOn_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) :
    ∃ W : (Spec (CommRingCat.of V)).Opens, genericPoint (Spec (CommRingCat.of V)) ∈ W ∧ Nonempty (PsiOn D W) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  let W : (Spec (CommRingCat.of V)).Opens := PrimeSpectrum.basicOpen ϖ
  have hW : genericPoint (Spec (CommRingCat.of V)) ∈ W := by
    rw [genericPoint_eq_bot_of_affine]
    exact hϖ.ne_zero
  have key : ∀ x ∈ W, x = genericPoint (Spec (CommRingCat.of V)) := fun x hx => by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    by_contra h
    have hm : (PrimeSpectrum.asIdeal x).IsMaximal := Ring.DimensionLEOne.maximalOfPrime h (PrimeSpectrum.isPrime x)
    exact hx (by
      show ϖ ∈ PrimeSpectrum.asIdeal x
      rw [IsLocalRing.eq_maximalIdeal hm]; exact hϖ.not_isUnit)
  obtain ⟨g, hg⟩ := WitnessData.exists_generic_lift hW
  let κ : TK V ⟶ TW W := Over.homMk g hg
  refine ⟨W, hW, PsiSpread.nonempty_psiOn D κ fun χ => ?_⟩
  obtain ⟨U, hU, ext⟩ := PsiSpread.exists_extends D χ z
  refine ext W (fun x hx => ?_) κ
  rw [key x hx]
  exact ((genericPoint_spec (Spec (CommRingCat.of V))).mem_open_set_iff U.isOpen).2 ⟨_, trivial, hU⟩

section General
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X}

theorem exists_global_unit (hL : L.IsLB) {p p' : Y ⟶ X} (h : p' = p) (w : LB.Iso (L.pull p) (L.pull p')) (hw : PGen w) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (y : Z) (j : L.ι), p (f y) ∈ L.U j →
      gw w f y j (fun _ => j) = gm f y ⊤ u := by
  subst h
  obtain ⟨u, hu⟩ := glue_unit ⊤ (fun j : L.ι => (L.pull p').U (fun _ => j) ⊓ (L.pull p').U (fun _ => j)) (fun _ => le_top)
    (fun y _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (p' y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, mem_pull.2 hj, mem_pull.2 hj⟩)
    (fun j => w.s (fun _ => j, fun _ => j)) (fun i j y hy => by
      have e := hw _ (𝟙 Y) y i j (fun _ => i) (fun _ => j) (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) hy.1.1 hy.2.1
      rw [gm_pull_g L p' (𝟙 Y) y _ _ hy.1.1 hy.2.1, mul_inv_cancel, _root_.one_mul] at e
      exact e)
  refine ⟨u, fun Z f y j hj => ?_⟩
  have hm : f y ∈ (L.pull p').U (fun _ => j) ⊓ (L.pull p').U (fun _ => j) := ⟨mem_pull.2 hj, mem_pull.2 hj⟩
  exact (congrArg (gm f y _) (hu j)).symm.trans (gm_res f y _ hm u)

theorem chart_of_om {K : Type} [Fintype K] {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) {φ' : K → (Y ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : ∀ k, φ' k ≫ Φ = φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (ha : a.IsGen) (ht : t.IsGen) (r : Z ⟶ Y) (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J')
    (H : val t r z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J') (p : K → L.ι) (q : K → L'.ι)
    (hp : ∀ k, Φ (φ' k (r z)) ∈ L.U (p k)) (hq : ∀ k, φ' k (r z) ∈ L'.U (q k)) :
    gm r z (LB.wchart L φ p) (t.s p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q) := by
  obtain rfl : (fun k => φ' k ≫ Φ) = φ := funext hφ
  have mp : r z ∈ LB.wchart L (fun k => φ' k ≫ Φ) p := Set.mem_iInter.2 hp
  have mq : r z ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  have e₁ := gen_trans ht r z mp (hJ.mem _ r)
  have e₂ := gen_trans ha r z mq (hJ'.mem _ r)
  have e₃ := pw_trans hw φ' ε r z mp (hJ.mem _ r) mq (hJ'.mem _ r)
  have e₄ : pw w φ' ε r z (fun k => J (r ≫ φ' k ≫ Φ)) (fun k => J' (r ≫ φ' k)) = ∏ k, om w z J J' (r ≫ φ' k) ^ ε k :=
    Finset.prod_congr rfl fun k _ => by rw [om, Category.assoc]
  rw [e₄] at e₃
  refine e₁.trans ((congrArg (_ * ·) H).trans (Eq.symm ((congrArg₂ (· * ·) e₃ e₂).trans ?_)))
  unfold val
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end General

section Values
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F}

theorem good (ν : NumOf D F N) (z : Sp F) : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem toStk_vF {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    toStk z (vF t r J) = (val t r z J).val := toStk_valF r _ z (hJ.mem φ r) _

theorem exists_const (hG : GlobalFnsSt) {Φ : D'.P.A.left ⟶ D.P.A.left} {wD : LB.Iso D'.P.L (D.P.L.pull Φ)} (gD : PGen wD)
    (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A} (w : AbPartIso.BunIso φ)
    (hw : w.IsGen) (hq : (φ.hom ≫ snd _ _).left ≫ Φ = (snd (TF (R := R) F) D.P.A).left) (f : N.A → N'.A)
    (hc : ∀ x, AbPartIso.Carries ν ν' φ x (f x)) (z : Sp F) : ∃ κ : (Sp F).presheaf.stalk z, ∀ x,
      (om wD z ν.J ν'.J (ν'.eA (f x)).left).val * toStk z (AbPartIso.wVal ν ν' w f x) = κ := by
  have gw' := (isGen_iff w).1 hw
  obtain ⟨w₂, T⟩ := exists_comp D'.P.isLB wD w gD gw' D.P.isLB (pull_isLB D.P.isLB _)
  obtain ⟨u, hu⟩ := exists_global_unit D.P.isLB hq w₂ (T.pgen_comp D'.P.isLB gD gw')
  obtain ⟨c, hc'⟩ := surj_fst hG D.P.isAb (TF (R := R) F) u.val
  refine ⟨gs (𝟙 (Sp F)) z ⊤ c, fun x => ?_⟩
  let r : Sp F ⟶ (TF (R := R) F ⊗ D.P.A).left := (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left
  have r₁ : r ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := congrArg Over.Hom.left (lift_snd _ _)
  have r₀ : r ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := congrArg Over.Hom.left (lift_fst _ _)
  have r₂ : r ≫ (φ.hom ≫ snd _ _).left = (ν'.eA (f x)).left :=
    congrArg Over.Hom.left ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ snd _ _) (hc x)).trans (lift_snd _ _)))
  have r₃ : (ν'.eA (f x)).left ≫ Φ = (ν.eA x).left := by rw [← r₂, Category.assoc, hq, r₁]
  have m₁ : (snd (TF (R := R) F) D.P.A).left (r z) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
    (congrArg (fun q => q z ∈ D.P.L.U (ν.J (ν.eA x).left)) r₁).mpr (good ν z _)
  have m₂ : (φ.hom ≫ snd _ _).left (r z) ∈ D'.P.L.U (ν'.J (ν'.eA (f x)).left) :=
    (congrArg (fun q => q z ∈ D'.P.L.U (ν'.J (ν'.eA (f x)).left)) r₂).mpr (good ν' z _)
  have m₃ : Φ ((φ.hom ≫ snd _ _).left (r z)) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
    (congrArg (fun q => q (r z) ∈ D.P.L.U (ν.J (ν.eA x).left)) hq).mpr m₁
  have e := (T _ r z _ _ (fun _ => ν.J (ν.eA x).left) m₃ m₂ (mem_pull.2 m₁)).symm.trans (hu _ r z _ m₁)
  rw [r₂] at e
  have e₁ : toStk z (AbPartIso.wVal ν ν' w f x) =
      (gw w r z (ν'.J (ν'.eA (f x)).left) (fun _ => ν.J (ν.eA x).left)).val :=
    toStk_valF r ((D'.P.L.pull _).U (fun _ => ν'.J (ν'.eA (f x)).left) ⊓ (D.P.L.pull _).U (fun _ => ν.J (ν.eA x).left)) z
      ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _
  rw [e₁, om, r₃, ← Units.val_mul, e, ← gs_unit r z ⊤ trivial, ← hc', ← r₀]
  exact gs_pull r _ z ⊤ trivial c
end Values

theorem exists_isPullDeg_of_values : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D D' : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (J : NumD.Iso N N') (Ψ : D.P.A ≅ D'.P.A), IsMonHom Ψ.hom → LBIso D.P.L (D'.P.L.pull Ψ.hom.left) → ∀ (φ : TF (R := V) F ⊗ D.P.A ≅ TF (R := V) F ⊗ D'.P.A) (w : AbPartIso.BunIso φ), φ.hom ≫ fst _ _ = fst _ _ → φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom → w.IsGen → (∀ x, AbPartIso.Carries ν ν' φ x (J.φ x)) → (∀ x, (J.h x : F) * AbPartIso.wVal ν ν' w J.φ 1 = AbPartIso.wVal ν ν' w J.φ x) → ∃ e : IsPullDeg (RingHom.id V) D D', ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D' F k) (q : N.QT k) (q' : N'.QT k), ν.QPt p q → ν'.QPt p' q' → q'.1.1.toAdd = J.e q.1.1.toAdd → J.Rel q.1.2 q'.1.2 → GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition.Carries e p p' := by
  intro hL V _ _ _ D D' F _ _ N N' ν ν' I Ψ hΨ hiso φ w _ hsnd hw hcar hh
  have hs := specOf_id V
  have : IsMonHom Ψ.symm.hom := inferInstanceAs (IsMonHom Ψ.inv)
  have gp₀ : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id V)) Ψ.inv.left :=
    (isGrpPullback_of_iso Ψ.symm).congr hs.symm rfl
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp₀ (isGrpPullback_pullback D.P.A (specOf (RingHom.id V)))
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id V)) := ⟨_, rfl⟩
  replace he : Φ = Ψ.inv.left := hΦ.trans he
  have gp : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id V)) Φ := gp₀.congr rfl he.symm
  have i₁ : Ψ.hom.left ≫ Φ = 𝟙 _ := by rw [he, ← Over.comp_left, Ψ.hom_inv_id, Over.id_left]
  have i₂ : Φ ≫ Ψ.hom.left = 𝟙 _ := by rw [he, ← Over.comp_left, Ψ.inv_hom_id, Over.id_left]
  have hE : eSec D'.P.A ≫ Φ = specOf (RingHom.id V) ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨wD, gD, rD⟩ := CartTriple.exists_rigidified hE ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩
    ⟨D'.P.L, D'.rig, D'.P.isLB, D'.rig_gen⟩
    (hiso.symm.chartPull (chartPullSec D'.P.L Ψ.hom.left Φ i₂) (Geo.Tor.chartPullPull D.P.L Φ Φ rfl))
  have hq : (φ.hom ≫ snd _ _).left ≫ Φ = (snd (TF (R := V) F) D.P.A).left := by
    rw [hsnd, Over.comp_left, Category.assoc, i₁, Category.comp_id]
  have pt : ∀ x, (ν'.eA (I.φ x)).left ≫ Φ = (ν.eA x).left := fun x => by
    have a : ν'.eA (I.φ x) = ν.eA x ≫ Ψ.hom := by
      have b := congrArg (· ≫ snd _ _) (hcar x)
      simp only [Category.assoc, hsnd, lift_snd, lift_snd_assoc] at b
      exact b.symm
    rw [a, Over.comp_left, Category.assoc, i₁, Category.comp_id]
  let xe : D'.X ≃+ D.X := (ν'.eX.symm.trans I.e.symm).trans ν.eX
  have hxe : ∀ y, xe (ν'.eX (I.e y)) = ν.eX y := fun y => by simp [xe]
  have sur : ∀ x : D'.X, ∃ y, ν'.eX (I.e y) = x := (I.e.trans ν'.eX).surjective
  have cF : ∀ y, ν'.eA (I.φ (N.c y)) = DegPre.cF D' F (ν'.eX (I.e y)) := fun y => by rw [← I.c_eq, ν'.c_eq]
  have hc : ∀ y, (D'.c (ν'.eX (I.e y))).left ≫ Φ = (D.c (ν.eX y)).left := fun y => by
    refine DVR.GC.vpt_ext F D.P ?_ (Over.w _) ?_
    · rw [Category.assoc, gp.1.w, hs, Category.comp_id]; exact Over.w _
    · have a := pt (N.c y)
      rw [cF, ν.c_eq] at a
      exact (Category.assoc _ _ _).symm.trans a

  let Ω : (z : Sp F) → (TF (R := V) F ⟶ D'.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun z x => om wD z ν.J ν'.J x.left
  let tu : (z : Sp F) → Fˣ →* ((Sp F).presheaf.stalk z)ˣ := fun z => Units.map (toStk z).toMonoidHom
  have hΩ : ∀ z x, tu z (I.h x) * Ω z (ν'.eA (I.φ x)) = Ω z 1 := fun z x => by
    obtain ⟨κ, hκ⟩ := exists_const hL.globalFns gD ν ν' w hw hq I.φ hcar z
    have a := (hκ x).trans (hκ 1).symm
    rw [← hh x, map_mul, map_one, map_one] at a
    have r₁ : (lift (𝟙 (TF (R := V) F)) (ν.eA 1)).left ≫ (snd (TF (R := V) F) D.P.A).left = (ν.eA 1).left :=
      congrArg Over.Hom.left (lift_snd _ _)
    have r₃ : (lift (𝟙 (TF (R := V) F)) (ν.eA 1)).left ≫ (φ.hom ≫ snd _ _).left = (ν'.eA (I.φ 1)).left :=
      congrArg Over.Hom.left ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ snd _ _) (hcar 1)).trans (lift_snd _ _)))
    have u : IsUnit (toStk z (AbPartIso.wVal ν ν' w I.φ 1)) :=
      ⟨_, (toStk_valF _ ((D'.P.L.pull _).U (fun _ => ν'.J (ν'.eA (I.φ 1)).left) ⊓
        (D.P.L.pull _).U (fun _ => ν.J (ν.eA 1).left)) z ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D'.P.L.U (ν'.J (ν'.eA (I.φ 1)).left)) r₃).mpr
        (good ν' z _)), mem_pull.2 ((congrArg (fun q => q z ∈ D.P.L.U (ν.J (ν.eA 1).left)) r₁).mpr (good ν z _))⟩ _).symm⟩
    rw [← _root_.mul_assoc] at a
    exact Units.ext ((mul_comm _ _).trans (u.mul_right_cancel a))
  have rig : ∀ z : Sp F, val (Z := Sp F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := V) F).hom z ν.J =
      Ω z 1 * val (Z := Sp F) (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (TF (R := V) F).hom z ν'.J :=
    fun z => by
      have a := pmaps_om (Z := Sp F) (fun _ => hE) rD (TF (R := V) F).hom z (good ν z) (good ν' z)
      rw [Fintype.prod_unique, zpow_one, hs] at a
      exact (congrArg (fun q => val (Z := Sp F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig q z ν.J)
        (Category.comp_id _).symm).trans a
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := exists_psiOn_dvr D
  obtain ⟨g, hg⟩ := WitnessData.exists_generic_lift hWo
  subst hΦ
  refine ⟨⟨e, e_hom, wD, (isGen_iff wD).2 gD, hE, ?_, xe, fun x => ?_, Wo, ψW, g,
    by rw [hg, hs, Category.comp_id], fun x => ?_⟩, fun k p p' q q' hp hp' hy hr => ⟨?_, fun x => ?_⟩⟩
  · exact (maps_iff wD (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id V)) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf (RingHom.id V)) hE D.P.L) (fun _ => rfl)).2 rD
  · obtain ⟨y, rfl⟩ := sur x
    rw [hxe]
    exact (hc y).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  · obtain ⟨y, rfl⟩ := sur x
    rw [hxe]
    have hx : D'.xK (ν'.eX (I.e y)) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id V)) = D.xK (ν.eX y) :=
      (Category.assoc _ _ _).trans (congrArg (jK V ≫ ·) (hc y))
    refine WitnessData.exists_psi_pull wD ψW hg hx F fun z p q hp hq => ?_
    have v := chart_of_om gD (K := PUnit) (ε := fun _ => -1) (fun _ => hx) (D'.psi_gen _) (D.psi_gen _) (jFK (R := V) F) z
      (good ν z) (good ν' z) ?_ (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
    · rwa [Fintype.prod_unique] at v
    have a : tu z (N.ψ y) = _ * _ := Units.ext ((congrArg (toStk z) (ν.ψ_eq y)).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (toStk_vF _ _ (good ν z)) (toStk_vF _ _ (good ν z)))))
    have a' : tu z (N'.ψ (I.e y)) = _ * _ := Units.ext ((congrArg (toStk z) (ν'.ψ_eq (I.e y))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (toStk_vF _ _ (good ν' z)) (toStk_vF _ _ (good ν' z)))))
    have b := congrArg (tu z) (I.ψ_eq y)
    have c := hΩ z (N.c y)
    rw [map_mul, a, a', rig z] at b
    rw [cF] at c
    have d : om wD z ν.J ν'.J (jFK (R := V) F ≫ D'.xK (ν'.eX (I.e y))) = Ω z (DegPre.cF D' F (ν'.eX (I.e y))) :=
      congrArg (om wD z ν.J ν'.J) (Category.assoc _ _ _).symm
    rw [Fintype.prod_unique, d, zpow_neg, zpow_one]
    have E := fun {s t : ((Sp F).presheaf.stalk z)ˣ} (h : s = t) => congrArg Additive.ofMul h
    have b₁ := E b
    have c₁ := E c
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at b₁ c₁ ⊢
    linear_combination (norm := abel) c₁ - b₁
  · show xe p'.y = p.y
    rw [← hp'.1, hy, hxe, hp.1]
  · obtain ⟨y, rfl⟩ := sur x
    show GenRel (F := F) wD (p'.g.s _) (p.g.s (xe _)) 1
    rw [hxe]
    let z : Sp F := (default : PrimeSpectrum F)
    have hb : p'.g.b = ν'.eA (I.φ q.1.2.b) := hp'.2.1.symm.trans (congrArg ν'.eA hr.1)
    have f₁ := pt (N.c y * q.1.2.b)
    have f₂ := pt (N.c y)
    have f₃ := pt q.1.2.b
    have f₄ := pt 1
    have c₁ := hΩ z (N.c y * q.1.2.b)
    have c₂ := hΩ z (N.c y)
    have c₃ := hΩ z q.1.2.b
    rw [map_mul, map_mul, cF, ← hb] at f₁ c₁
    rw [map_mul, ν.c_eq, hp.2.1] at f₁
    rw [cF] at f₂ c₂
    rw [ν.c_eq] at f₂
    rw [← hb] at f₃ c₃
    rw [hp.2.1] at f₃
    rw [map_one, map_one, map_one] at f₄
    have hψ : ∀ i, DegPre.gtφ D' F p'.g.b (ν'.eX (I.e y)) i ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id V)) =
        DegPre.gtφ D F p.g.b (ν.eX y) i := fun i => by
      fin_cases i
      exacts [f₁, f₂, f₃, f₄]
    refine (genRel_iff wD _ _ 1 z).2 ⟨hψ, fun j j₀ h₀ h₁ => ?_⟩
    have v := chart_of_om gD hψ (p'.g.isGen _) (p.g.isGen _) (𝟙 (Sp F)) z (good ν z) (good ν' z) ?_ j₀ j h₀ h₁
    · simp only [Category.id_comp] at v
      rw [map_one, _root_.one_mul]
      exact congrArg Units.val v.symm
    have a : tu z (q.1.2.s y) = _ := Units.ext ((congrArg (toStk z) (hp.2.2 y)).trans (toStk_vF _ _ (good ν z)))
    have a' : tu z (q'.1.2.s (I.e y)) = _ :=
      Units.ext ((congrArg (toStk z) (hp'.2.2 (I.e y))).trans (toStk_vF _ _ (good ν' z)))
    have b := congrArg (tu z) (hr.2 y)
    rw [map_mul, map_mul, map_mul, a, a'] at b
    have d : ∏ i, om wD z ν.J ν'.J (𝟙 (Sp F) ≫ DegPre.gtφ D' F p'.g.b (ν'.eX (I.e y)) i) ^ DegPre.gtε i =
        (Ω z (DegPre.cF D' F (ν'.eX (I.e y)) * p'.g.b))⁻¹ * Ω z (DegPre.cF D' F (ν'.eX (I.e y))) * Ω z p'.g.b *
          (Ω z 1)⁻¹ := by
      simp only [Category.id_comp]
      exact prod_gt p'.g.b _ (om wD z ν.J ν'.J)
    refine Eq.trans ?_ (congrArg (· * _) d.symm)
    have E := fun {s t : ((Sp F).presheaf.stalk z)ˣ} (h : s = t) => congrArg Additive.ofMul h
    have b₁ := E b
    have e₁ := E c₁
    have e₂ := E c₂
    have e₃ := E c₃
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at b₁ e₁ e₂ e₃ ⊢
    linear_combination (norm := abel) e₁ - b₁ - e₂ - e₃

end GlobalTheory.ValuesIdent
end
