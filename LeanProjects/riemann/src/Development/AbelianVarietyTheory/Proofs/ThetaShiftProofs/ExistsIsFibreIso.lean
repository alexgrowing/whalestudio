import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective

noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

theorem exists_up_sec {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Y ⟶ Y') (hc : ∀ k, (h ≫ φ' k) ≫ Φ = φ k) (s : LB.Sec (LB.LinComb L' φ' ε)) :
    ∃ a : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      sval a r z J = (∏ k, om w z J J' ((r ≫ h) ≫ φ' k) ^ ε k).val * sval s (r ≫ h) z J' := by
  obtain rfl : (fun k => (h ≫ φ' k) ≫ Φ) = φ := funext hc
  choose u hu using fun p q => exists_pw w (fun k => h ≫ φ' k) ε p q
  have tc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q q' : K → L'.ι),
      trF φ' ε (r ≫ h) z q q' = trF (fun k => h ≫ φ' k) ε r z q q' := fun Z r z q q' => by
    simp only [trF, Category.assoc]
  have glue : ∀ p : K → L.ι, ∃ a : Γ(Y, LB.wchart L (fun k => (h ≫ φ' k) ≫ Φ) p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => (h ≫ φ' k) ≫ Φ) p → r z ∈ LB.wchart L' (fun k => h ≫ φ' k) q →
      gs r z _ a = (pw w (fun k => h ≫ φ' k) ε r z p q).val * gs (r ≫ h) z (LB.wchart L' φ' q) (s.f q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q => LB.wchart L (fun k => (h ≫ φ' k) ≫ Φ) p ⊓ LB.wchart L' (fun k => h ≫ φ' k) q
    have le : ∀ q, W q ≤ h ⁻¹ᵁ LB.wchart L' φ' q := fun q y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, W q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gs r z (W q) (v q) = (pw w (fun k => h ≫ φ' k) ε r z p q).val * gs (r ≫ h) z (LB.wchart L' φ' q) (s.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE (le q)).op).hom ((h.app _).hom (s.f q)),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (hu p q Z r z hz)))
          ((gs_res r z (le q) hz _).trans (gs_pull r h z _ (le q hz) _)))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L (fun k => (h ≫ φ' k) ≫ Φ) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' ((h ≫ φ' k) y)
        exact Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, sec_trans s (𝟙 Y ≫ h) y (le q hy.1) (le q' hy.2), tc,
          pw_trans hw _ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2, trF_self hL _ ε (𝟙 Y) y hy.1.1, _root_.one_mul,
          ← _root_.mul_assoc, ← Units.val_mul, mul_right_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨a, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W q)) (ha q)).trans (hv Z r z q hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · choose q hq using fun k => exists_chart hL' ((h ≫ φ' k) y)
    have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun k => h ≫ φ' k) q := Set.mem_iInter.2 hq
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y q hy.1 m).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y q hy.2 m)).symm)
    rw [pw_trans hw _ ε (𝟙 Y) y hy.1 hy.2 m m, trF_self hL' _ ε (𝟙 Y) y m, inv_one, _root_.mul_one, Units.val_mul,
      _root_.mul_assoc]
    rfl
  · refine (ha _ Z r z _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) ?_)
    · simp only [pw, om, Category.assoc]
    · exact (sval_of s (r ≫ h) z J' _ (fun k => by rw [Category.assoc])).symm

theorem exists_up_om {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (φ' : K → (Y ⟶ X')) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (hc : ∀ k, φ' k ≫ Φ = φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (y : Y) J J', Good L y J → Good L' y J' →
      val t (𝟙 Y) y J = (∏ k, om w y J J' (φ' k) ^ ε k) * val a (𝟙 Y) y J' := by
  obtain rfl : (fun k => φ' k ≫ Φ) = φ := funext hc
  obtain ⟨t, ht, hv⟩ := exists_up hw hL hL' a ha
  refine ⟨t, ht, fun y J J' hJ hJ' => (hv _ (𝟙 Y) y _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)⟩
  simp only [pw, om, Category.id_comp]

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem prod_delta_zero (k : ℕ) (α α₁ : D.X) (m : TF (R := R) F ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h ((DegPre.zF D F).left ≫ Sum.elim (DegPre.famφ D F α₁)
        (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i) i) ^ DegPre.deltaε k i =
      (h (cP D _ α * m).left)⁻¹ * h (cP D (TF (R := R) F) α).left * h m.left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ *
        (h (1 : TF (R := R) F ⟶ D.P.A).left ^ k * (h m.left ^ k)⁻¹) := by
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D F ≫ DegPre.trPt D F m) ≫ DegPre.prB D F = m := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  have p₁ := prod_fam D F (DegPre.zF D F) α₁ k h
  have p₂ := prod_fam D F (DegPre.zF D F ≫ DegPre.trPt D F m) α k h
  rw [z₂, _root_.mul_one] at p₁
  rw [z₃] at p₂
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₁ (prod_neg _ _
    ((Finset.prod_congr rfl fun i _ => by rw [Over.comp_left, Category.assoc]; rfl).trans p₂))).trans ?_
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

structure IsFibreIso (κ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left)
    (κ' : (DegPre.BF D F).left ⟶ (DegPre.BF D' F).left) : Prop where
  fst : κ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left
  snd : (DegPre.prB D' F).left ≫ proj hD = κ ≫ (DegPre.prB D F).left
  inv_hom : κ' ≫ κ = 𝟙 _
  hom_inv : κ ≫ κ' = 𝟙 _

theorem exists_isFibreIso (hF : Compat φ F) : ∃ κ κ', IsFibreIso hD (F := F) κ κ' := by
  have gp := (pull_grp hD).1
  have c' : (fst (TF (R := R') F) D'.P.A).left ≫ (TF (R := R') F).hom = (DegPre.prB D' F).left ≫ D'.P.A.hom :=
    pullback.condition
  have c : (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R) F).hom = (DegPre.prB D F).left ≫ D.P.A.hom :=
    pullback.condition
  obtain ⟨κ, k₁, k₂⟩ : ∃ κ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left,
      κ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left ∧
      κ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ proj hD :=
    ⟨pullback.lift (fst (TF (R := R') F) D'.P.A).left ((DegPre.prB D' F).left ≫ proj hD)
      ((congrArg (_ ≫ ·) hF.base.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) c').trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) gp.w.symm).trans (Category.assoc _ _ _).symm))))),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨b, b₁, b₂⟩ : ∃ b : (DegPre.BF D F).left ⟶ D'.P.A.left, b ≫ proj hD = (DegPre.prB D F).left ∧
      b ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom :=
    ⟨gp.lift (DegPre.prB D F).left ((fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom)
      (c.symm.trans ((congrArg (_ ≫ ·) hF.base.symm).trans (Category.assoc _ _ _).symm)), gp.lift_fst _ _ _,
      gp.lift_snd _ _ _⟩
  obtain ⟨κ', l₁, l₂⟩ : ∃ κ' : (DegPre.BF D F).left ⟶ (DegPre.BF D' F).left,
      κ' ≫ (fst (TF (R := R') F) D'.P.A).left = (fst (TF (R := R) F) D.P.A).left ∧ κ' ≫ (DegPre.prB D' F).left = b :=
    ⟨pullback.lift (fst (TF (R := R) F) D.P.A).left b b₂.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  refine ⟨κ, κ', k₁, k₂.symm, pullback.hom_ext ?_ ?_, pullback.hom_ext ?_ ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (κ' ≫ ·) k₁).trans (l₁.trans (Category.id_comp _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (κ' ≫ ·) k₂).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) l₂).trans (b₁.trans (Category.id_comp _).symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) l₁).trans (k₁.trans (Category.id_comp _).symm))
  · refine (Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) l₂).trans (Eq.trans (gp.hom_ext ?_ ?_) (Category.id_comp _).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) b₁).trans k₂)
    · exact (Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) b₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) k₁).trans c')))

theorem one_proj {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left) (hh : T'.hom ≫ spMap φ = h ≫ T.hom) :
    (1 : T' ⟶ D'.P.A).left ≫ proj hD = h ≫ (1 : T ⟶ D.P.A).left := by
  have := cPoint_proj hD h hh 0
  rwa [map_zero, cPoint_zero, cPoint_zero] at this

variable {hD} {κ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left} {κ' : (DegPre.BF D F).left ⟶ (DegPre.BF D' F).left}
  (hκ : IsFibreIso hD κ κ')

include hκ

theorem IsFibreIso.base : (DegPre.BF D' F).hom ≫ spMap φ = κ ≫ (DegPre.BF D F).hom := by
  rw [← Over.w (DegPre.prB D F), ← Over.w (DegPre.prB D' F), ← Category.assoc κ, ← hκ.snd, Category.assoc,
    Category.assoc, (pull_grp hD).1.w]

theorem IsFibreIso.fam (α : D'.X) (i : Fin 4) : DegPre.famφ D' F α i ≫ proj hD = κ ≫ DegPre.famφ D F (hD.xe α) i := by
  fin_cases i
  exacts [hκ.snd, mul_push (pull_grp hD) κ hκ.snd (cPoint_proj hD κ hκ.base α), cPoint_proj hD κ hκ.base α,
    one_proj hD κ hκ.base]

theorem IsFibreIso.tr {m' : TF (R := R') F ⟶ D'.P.A} {m : TF (R := R) F ⟶ D.P.A} (hm : m'.left ≫ proj hD = m.left) :
    (DegPre.trPt D' F m').left ≫ κ = κ ≫ (DegPre.trPt D F m).left := by
  have a := congrArg (fun q => q.left) (tr_fst D F m)
  have a' := congrArg (fun q => q.left) (tr_fst D' F m')
  have b := congrArg (fun q => q.left) (tr_pr D F m)
  have b' := congrArg (fun q => q.left) (tr_pr D' F m')
  have c : (CartesianMonoidalCategory.fst (TF (R := R') F) D'.P.A ≫ m').left ≫ proj hD =
      κ ≫ (CartesianMonoidalCategory.fst (TF (R := R) F) D.P.A ≫ m).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hm).trans ((congrArg (· ≫ m.left) hκ.fst.symm).trans
      (Category.assoc _ _ _)))
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ.fst).trans (a'.trans (hκ.fst.symm.trans
      ((congrArg (κ ≫ ·) a.symm).trans (Category.assoc _ _ _).symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ.snd.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) b').trans ((mul_push (pull_grp hD) κ hκ.snd c).trans
        ((congrArg (κ ≫ ·) b.symm).trans (Category.assoc _ _ _).symm)))))

theorem IsFibreIso.zero (hF : Compat φ F) : (DegPre.zF D' F).left ≫ κ = (DegPre.zF D F).left := by
  have z₁ : (DegPre.zF D F).left ≫ (CartesianMonoidalCategory.fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) (1 : _ ⟶ D.P.A))
  have z₂ : (DegPre.zF D F).left ≫ (DegPre.prB D F).left = (1 : TF (R := R) F ⟶ D.P.A).left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) F)) (1 : _ ⟶ D.P.A))
  have z₃ : (DegPre.zF D' F).left ≫ (CartesianMonoidalCategory.fst (TF (R := R') F) D'.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R') F)) (1 : _ ⟶ D'.P.A))
  have z₄ : (DegPre.zF D' F).left ≫ (DegPre.prB D' F).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R') F)) (1 : _ ⟶ D'.P.A))
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ.fst).trans (z₃.trans z₁.symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ.snd.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) z₄).trans ((one_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
        (hF.base.trans (Category.id_comp _).symm)).trans ((Category.id_comp _).trans z₂.symm)))))

omit hκ in
variable (hD κ) in

def SecUp {k : ℕ} {α : D'.X} {β : D.X} (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F α) (DegPre.famε k)))
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
    sval s (r ≫ κ) z J = (∏ i, om hD.w z J J' (r ≫ DegPre.famφ D' F α i) ^ DegPre.famε k i).val * sval s' r z J'

theorem exists_secUp {k : ℕ} {α : D'.X} {β : D.X} (e : hD.xe α = β)
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F α) (DegPre.famε k))) :
    ∃ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k)), SecUp hD κ s' s := by
  subst e
  obtain ⟨s, hs⟩ := exists_up_sec ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB _ (DegPre.famφ D F (hD.xe α)) _ κ'
    (fun i => by rw [Category.assoc, hκ.fam, ← Category.assoc, hκ.inv_hom, Category.id_comp]) s'
  refine ⟨s, fun Z r z J J' hJ hJ' => ?_⟩
  have := hs Z (r ≫ κ) z J J' hJ hJ'
  rwa [Category.assoc r κ κ', hκ.hom_inv, Category.comp_id] at this

theorem secRel_up (hF : Compat φ F) {k : ℕ} {α α₁ : D'.X} {β β₁ : D.X} (e : hD.xe α = β) (e₁ : hD.xe α₁ = β₁)
    {m' : TF (R := R') F ⟶ D'.P.A} {m : TF (R := R) F ⟶ D.P.A} (hm : m'.left ≫ proj hD = m.left)
    {tr' : DegPre.BF D' F ⟶ DegPre.BF D' F} {tr : DegPre.BF D F ⟶ DegPre.BF D F} (ht' : tr' = DegPre.trPt D' F m')
    (ht : tr = DegPre.trPt D F m) {s' s t' t} (hs : SecUp hD κ (k := k) (α := α) (β := β) s' s)
    (ht₁ : SecUp hD κ (k := k) (α := α₁) (β := β₁) t' t) {K K' : Type} [Fintype K] [Fintype K']
    {ψ : K → ((TF (R := R) F).left ⟶ D.P.A.left)} {ε : K → ℤ} {ψ' : K' → ((TF (R := R') F).left ⟶ D'.P.A.left)}
    {ε' : K' → ℤ} {v : LB.Gen (LB.LinComb D.P.L ψ ε)} {v' : LB.Gen (LB.LinComb D'.P.L ψ' ε')}
    (hv : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS v y J =
      (om hD.w y J J' (cP D' _ α * m').left)⁻¹ * om hD.w y J J' (cP D' (TF (R := R') F) α).left * om hD.w y J J' m'.left *
        (om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left)⁻¹ *
        (om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ k * (om hD.w y J J' m'.left ^ k)⁻¹) * vS v' y J')
    (H : ∀ u' : LB.Gen (LB.LinComb D'.P.L (Sum.elim (DegPre.famφ D' F α₁) (fun i => tr'.left ≫ DegPre.famφ D' F α i))
        (DegPre.deltaε k)), u'.IsGen → LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (DegPre.zF D' F).left) v' →
      GeneratorPullback.SecRel D'.P.L _ _ t' _ _ s' tr'.left _ _ u')
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (DegPre.famφ D F β₁) (fun i => tr.left ≫ DegPre.famφ D F β i))
      (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) v) :
    GeneratorPullback.SecRel D.P.L _ _ t _ _ s tr.left _ _ u := by
  subst e e₁ ht ht'
  obtain ⟨u', hu', vu⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB
    (φ' := Sum.elim (DegPre.famφ D' F α₁) (fun i => (DegPre.trPt D' F m').left ≫ DegPre.famφ D' F α i)) κ (by
      rintro (i | i)
      · exact hκ.fam _ i
      · show ((DegPre.trPt D' F m').left ≫ _) ≫ _ = κ ≫ (DegPre.trPt D F m).left ≫ _
        rw [Category.assoc, hκ.fam, ← Category.assoc, hκ.tr hm, Category.assoc]) u hu
  have R' := (secRel_iff D'.P.isLB _ _ _ _ _ _ _ _ _ u').1 (H u' hu' (corr_of_val D'.P.isLB fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB (Z := Sp F) y
    have a := vu _ (DegPre.zF D' F).left y J J' hJ hJ'
    rw [prod_delta_zero, hκ.zero hF] at a
    have b := (val_pull hJ _ _ _).symm.trans (val_corr hJ hc (𝟙 _))
    rw [val_pull hJ', Category.id_comp]
    exact mul_left_cancel (a.symm.trans (((congrArg (fun q => val u q y J) (Category.id_comp _).symm).trans b).trans
      (hv y J J' hJ hJ')))))
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB y
  have a₁ := ht₁ _ κ' y J J' hJ hJ'
  have a₂ := hs _ (κ' ≫ (DegPre.trPt D' F m').left) y J J' hJ hJ'
  have a₃ := (vu _ κ' y J J' hJ hJ').trans (congrArg₂ (· * ·) (prod_sum₂ (K := Fin 4) (K' := Fin 4) _
    (c := ∏ i, om hD.w y J J' (κ' ≫ DegPre.famφ D' F α₁ i) ^ DegPre.famε k i) rfl
    (prod_neg (c := ∏ i, om hD.w y J J' ((κ' ≫ (DegPre.trPt D' F m').left) ≫ DegPre.famφ D' F α i) ^ DegPre.famε k i)
      _ _ (Finset.prod_congr rfl fun i _ => by rw [Category.assoc]; rfl))) rfl)
  rw [Category.assoc, hκ.tr hm, ← Category.assoc, hκ.inv_hom] at a₂
  rw [hκ.inv_hom] at a₁ a₃
  rw [a₁, a₂, a₃, R' _ κ' y J' hJ', Units.val_mul, Units.val_mul]
  have := Units.mul_inv (∏ i, om hD.w y J J' ((κ' ≫ (DegPre.trPt D' F m').left) ≫ DegPre.famφ D' F α i) ^ DegPre.famε k i)
  linear_combination (-((∏ i, om hD.w y J J' (κ' ≫ DegPre.famφ D' F α₁ i) ^ DegPre.famε k i).val *
    sval s' (κ' ≫ (DegPre.trPt D' F m').left) y J' * (val u' κ' y J').val)) * this

theorem exists_famUp (hF : Compat φ F) {k : ℕ} (s' : Fam D' F k) :
    ∃ s : Fam D F k, ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β) := by
  choose s hs using fun β => exists_secUp hκ (hD.xe.apply_symm_apply β) (s'.s (hD.xe.symm β))
  have hs' : ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s β) := fun α β e => by
    obtain rfl : hD.xe.symm β = α := by rw [← e, AddEquiv.symm_apply_apply]
    exact hs β
  refine ⟨⟨s, fun mu β => ?_⟩, hs'⟩
  obtain ⟨mu, rfl⟩ := hD.xe.surjective mu
  obtain ⟨α, rfl⟩ := hD.xe.surjective β
  have e₁ : hD.xe (α + k • mu) = hD.xe α + k • hD.xe mu := by rw [map_add, map_nsmul]
  refine secRel_up hκ hF rfl e₁ ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
    (hF.base.trans (Category.id_comp _).symm) mu).trans (Category.id_comp _)) (trF_eq D' F mu) (trF_eq D F _)
    (hs' _ _ rfl) (hs' _ _ e₁) (fun y J J' hJ hJ' => ?_) (s'.fe mu α)
  have sq : (𝟙 (Sp F) ≫ jFK (R := R') F) ≫ jK R' ≫ spMap φ = (𝟙 (Sp F) ≫ jFK (R := R) F) ≫ jK R := by
    rw [Category.id_comp, Category.id_comp]; exact hF.sq
  have a₁ : ∀ χ, (𝟙 (Sp F) ≫ jFK (R := R') F) ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (Sp F) ≫ jFK (R := R') F) ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have b₁ := tau_val hD _ _ sq hJ hJ' mu α
  have b₂ := psi_val hD _ _ sq hJ hJ' mu
  have b₃ := rig_val hD _ _ sq hJ hJ'
  rw [a₁, a₁, a₁, a₂, cPoint_add, mul_comm (cP D' _ mu)] at b₁
  rw [a₁] at b₂
  rw [a₂] at b₃
  have c : vS (DegPre.famMult D F k (hD.xe mu) (hD.xe α)) y J =
      val (D.tau (hD.xe mu) (hD.xe α)) (𝟙 (Sp F) ≫ jFK (R := R) F) y J *
      (val (D.psi (hD.xe mu)) (𝟙 (Sp F) ≫ jFK (R := R) F) y J ^ k * val D.rigK (𝟙 (Sp F) ≫ jFK (R := R) F) y J ^ k) :=
    (val_famMult (𝟙 (TF (R := R) F)) hJ k _ _).trans (congrArg₂ (· * ·) rfl
      (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))
  have c' : vS (DegPre.famMult D' F k mu α) y J' = val (D'.tau mu α) (𝟙 (Sp F) ≫ jFK (R := R') F) y J' *
      (val (D'.psi mu) (𝟙 (Sp F) ≫ jFK (R := R') F) y J' ^ k * val D'.rigK (𝟙 (Sp F) ≫ jFK (R := R') F) y J' ^ k) :=
    (val_famMult (𝟙 (TF (R := R') F)) hJ' k _ _).trans (congrArg₂ (· * ·) rfl
      (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))
  rw [c, c', b₁, b₂, b₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  module

omit hκ in
variable (hD) in
theorem exists_lineUp (hF : Compat φ F) {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ proj hD = b.left) (w' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F b') (DegPre.lineε k)))
    (hw' : w'.IsGen) : ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b) (DegPre.lineε k)), w.IsGen ∧
      ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS w y J =
        om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ k * (om hD.w y J J' b'.left ^ k)⁻¹ * vS w' y J' := by
  obtain ⟨w, hw, vw⟩ := exists_up_om (Y := Sp F) ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (DegPre.lineφ D' F b')
    (DegPre.lineφ D F b) _ (fun i => by
      fin_cases i
      · exact (one_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
          (hF.base.trans (Category.id_comp _).symm)).trans (Category.id_comp _)
      · exact hb) w' hw'
  refine ⟨w, hw, fun y J J' hJ hJ' => (vw y J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)⟩
  rw [Fin.prod_univ_two]
  show om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ (k : ℤ) * om hD.w y J J' b'.left ^ (-(k : ℤ)) = _
  rw [zpow_neg, zpow_natCast, zpow_natCast]

theorem phiRel_up (hF : Compat φ F) {k : ℕ} {p : QkPt D F k} {p' : QkPt D' F k} (hy : p'.y = hD.xe.symm p.y)
    (hg : IsPullGtF φ hD F p.g p'.g) {w w'} (hw : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS w y J =
        om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ k * (om hD.w y J J' p'.g.b.left ^ k)⁻¹ * vS w' y J')
    {s t : Fam D F k} {s' t' : Fam D' F k} (hs : ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β))
    (ht : ∀ α β, hD.xe α = β → SecUp hD κ (t'.s α) (t.s β)) (H : PhiRel D' F k p' w' s' t') : PhiRel D F k p w s t := by
  intro β
  obtain ⟨α, rfl⟩ := hD.xe.surjective β
  have e₁ : hD.xe (α + p'.y) = hD.xe α + p.y := by rw [map_add, hy, AddEquiv.apply_symm_apply]
  refine secRel_up hκ hF rfl e₁ hg.1 rfl rfl (hs _ _ rfl) (ht _ _ e₁) (fun y J J' hJ hJ' => ?_) (H α)
  have b := pullGt_val hD hg α (𝟙 _) hJ hJ'
  simp only [Category.id_comp] at b
  have c : vS (LB.mulGen D.P.L _ _ _ _ (p.g.s (hD.xe α)) w) y J = val (p.g.s (hD.xe α)) (𝟙 (Sp F)) y J * vS w y J :=
    val_mul hJ _ _ _
  have c' : vS (LB.mulGen D'.P.L _ _ _ _ (p'.g.s α) w') y J' = val (p'.g.s α) (𝟙 (Sp F)) y J' * vS w' y J' :=
    val_mul hJ' _ _ _
  rw [c, c', b, hw y J J' hJ hJ']
  ac_rfl

omit hκ in
variable (hD) in

theorem weilQkIs_pull (hF : Compat φ F) {k : ℕ} {p q : QkPt D F k} {p' q' : QkPt D' F k} (hp : p'.y = hD.xe.symm p.y)
    (hpg : IsPullGtF φ hD F p.g p'.g) (hq : q'.y = hD.xe.symm q.y) (hqg : IsPullGtF φ hD F q.g q'.g) {ζ : F}
    (H : WeilQkIs D F k p q ζ) : WeilQkIs D' F k p' q' ζ := by
  intro w' v' hw' hv' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ α
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w, hw, vw⟩ := exists_lineUp hD hF hpg.1 w' hw'
  obtain ⟨v, hv, vv⟩ := exists_lineUp hD hF hqg.1 v' hv'
  choose up hup using exists_famUp hκ hF (k := k)
  have e := (isSmul_iff _ _ _).1 (H w v hw hv _ _ _ _ _ (phiRel_up hκ hF hq hqg vv (hup s) (hup s₁) r₁)
    (phiRel_up hκ hF hp hpg vw (hup s₁) (hup s₂) r₂) (phiRel_up hκ hF hp hpg vw (hup s) (hup s₃) r₃)
    (phiRel_up hκ hF hq hqg vv (hup s₃) (hup s₄) r₄))
  refine sec_ext_val D'.P.isLB (s := s₂.s α) (s' := (ζ • s₄).s α) fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have a := hup s₂ α _ rfl _ (𝟙 _) y J J' hJ hJ'
  rw [e, sval_smul _ _ _ _ y hJ, hup s₄ α _ rfl _ (𝟙 _) y J J' hJ hJ', Category.assoc, hκ.fst, mul_left_comm] at a
  rw [sval_smul _ _ _ _ y hJ']
  exact ((Units.mul_right_inj _).1 a).symm

end GlobalTheory.ArcPull
