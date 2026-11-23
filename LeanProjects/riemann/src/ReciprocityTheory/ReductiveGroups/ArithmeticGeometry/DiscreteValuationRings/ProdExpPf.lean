import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gs_prod {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(X, U)) : gs r z U (∏ i ∈ S, a i) = ∏ i ∈ S, gs r z U (a i) := by simp only [gs_eq r z U h, map_prod]

theorem gs_fsum {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(X, U)) : gs r z U (∑ i ∈ S, a i) = ∑ i ∈ S, gs r z U (a i) := by simp only [gs_eq r z U h, map_sum]

theorem gs_zero {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : gs r z U 0 = 0 := by
  simp only [gs_eq r z U h, map_zero]

theorem mem_finf {X : Scheme.{0}} {K : Type} (S : Finset K) (W : K → X.Opens) (x : X) (h : ∀ a ∈ S, x ∈ W a) :
    x ∈ S.inf W := by
  classical
  induction S using Finset.induction_on with
  | empty => trivial
  | insert a S _ ih =>
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self _ _), ih fun b hb => h b (Finset.mem_insert_of_mem hb)⟩

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

abbrev pGl : (thickObj R I e G).left ⟶ D.toPre.P.A.left := (U.gt e).pG.left

variable (I G) in
omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in

abbrev fGl : (thickObj R I e G).left ⟶ G.left := (fstG I e G).left

abbrev Oφl (α : D.toPre.X) : Fin 4 → ((thickObj R I e G).left ⟶ D.toPre.P.A.left) := D.toPre.Oφ (U.gt e).pG α

abbrev tG (α : D.toPre.X) : LB.Gen (LB.LinComb D.toPre.P.L (Oφl U e α) Oinvε) := (U.gt e).t α

def wv {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U (fun _ => jL))
    ((U.w e).s (fun _ => jM, fun _ => jL))

def sv (σ : H0 U.LG.L k) {Z : Scheme.{0}} (q : Z ⟶ G.left) (z : Z) (jL : U.LG.L.ι) : Z.presheaf.stalk z :=
  gs q z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL))

variable (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)

theorem exp_germ {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (S : Finset D.toPre.X) (jM : D.toPre.P.L.ι)
    (jL : U.LG.L.ι) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (hz : r z ∈ U.expW e (fun _ => jM, fun _ => jL) (fun _ => jL) S jf jt) :
    gs r z _ ((res (inf_le_left.trans inf_le_left : U.expW e (fun _ => jM, fun _ => jL) (fun _ => jL) S jf jt ≤
        (LB.div (D.toPre.P.L.pull (pGl U e)) (U.LG.L.pull (fGl I G e))).U (fun _ => jM, fun _ => jL))
        ((U.w e).s (fun _ => jM, fun _ => jL))).val ^ k *
      ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        U.expW e (fun _ => jM, fun _ => jL) (fun _ => jL) S jf jt ≤
          (fGl I G e) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL))).op).hom
        (((fGl I G e).app _).hom (σ.f (fun _ => jL)))) =
      (wv U e r z jM jL ^ k).val * sv U k σ (r ≫ (fGl I G e)) z jL ∧
    gs r z _ (∑ α ∈ S.attach, ((thickObj R I e G).left.presheaf.map
        (homOfLE (U.expW_le_f e (fun _ => jM, fun _ => jL) (fun _ => jL) jf jt α.2)).op).hom
        (((pGl U e).app _).hom ((f α.1).f (jf α.1))) *
        (res (U.expWeight_le_chart_weight e (fun _ => jM, fun _ => jL) (fun _ => jL) jf jt α.2) ((tG U e α.1).s (jt α.1))).val) =
      ∑ α ∈ S, gs (r ≫ (pGl U e)) z (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)) ((f α).f (jf α)) *
        (gm r z (LB.wchart D.toPre.P.L (Oφl U e α) (jt α)) ((tG U e α).s (jt α))).val := by
  constructor
  · refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ?_ ((gs_res r z _ hz _).trans (gs_pull r _ z _ hz.1.2 _)))
    rw [← Units.val_pow_eq_pow_val, gs_unit r z _ hz, map_pow]
    exact congrArg (fun u => (u ^ k).val) (gm_res r z _ hz _)
  · refine (gs_fsum r z _ hz _ _).trans (Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (Finset.sum_attach S _))
    have l₁ := U.expW_le_f e (fun _ => jM, fun _ => jL) (fun _ => jL) jf jt α.2
    have l₂ := U.expWeight_le_chart_weight e (fun _ => jM, fun _ => jL) (fun _ => jL) jf jt α.2
    have a₁ := (gs_res r z l₁ hz (((pGl U e).app _).hom ((f α.1).f (jf α.1)))).trans
      (gs_pull r (pGl U e) z (LB.wchart D.toPre.P.L (D.toPre.famφB α.1) (jf α.1)) (l₁ hz) ((f α.1).f (jf α.1)))
    have a₂ := (gs_unit r z _ hz (res l₂ ((tG U e α.1).s (jt α.1)))).trans (congrArg Units.val (gm_res r z l₂ hz _))
    exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) a₁ a₂)

theorem expandsAt_val (h : U.ExpandsAt e k σ f) : ∃ S : Finset D.toPre.X, ∀ (Z : Scheme.{0})
    (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      (∀ α ∉ S, sval (f α) (r ≫ (pGl U e)) z J = 0) ∧ ∀ jL, (fGl I G e) (r z) ∈ U.LG.L.U jL →
      (wv U e r z (J (r ≫ (pGl U e))) jL ^ k).val * sv U k σ (r ≫ (fGl I G e)) z jL =
        ∑ α ∈ S, sval (f α) (r ≫ (pGl U e)) z J * (val (tG U e α) r z J).val := by
  obtain ⟨S, h₀, h₁⟩ := h
  refine ⟨S, fun Z r z J hJ => ⟨fun α hα => ?_, fun jL hL => ?_⟩⟩
  · have m := hJ.mem (D.toPre.famφB α) (r ≫ (pGl U e))
    exact (gs_pull r _ z _ m _).symm.trans ((congrArg (gs r z _) (h₀ α hα _)).trans (gs_zero r z _ m))
  · have hz : r z ∈ U.expW e (fun _ => J (r ≫ (pGl U e)), fun _ => jL) (fun _ => jL) S
        (fun α a => J ((r ≫ (pGl U e)) ≫ D.toPre.famφB α a)) (fun α a => J (r ≫ Oφl U e α a)) :=
      ⟨⟨⟨mem_pull.2 (hJ (r ≫ (pGl U e))), mem_pull.2 hL⟩, Set.mem_iInter.2 fun _ => hL⟩,
        mem_finf S _ _ fun α _ => ⟨hJ.mem (D.toPre.famφB α) (r ≫ (pGl U e)), hJ.mem _ r⟩⟩
    obtain ⟨k₁, k₂⟩ := exp_germ U e k σ f r z S _ jL _ _ hz
    refine k₁.symm.trans ((congrArg (gs r z _) (h₁ (fun _ => J (r ≫ (pGl U e)), fun _ => jL) (fun _ => jL) _ _ rfl
      ?_)).trans k₂)
    have c : ∀ a, Sum.elim (fun _ : PUnit.{1} => J (r ≫ (pGl U e)))
        (Sum.elim (fun a : S × Fin 4 => J ((r ≫ (pGl U e)) ≫ D.toPre.famφB a.1.1 a.2))
          (fun a : S × Fin 4 => J (r ≫ Oφl U e a.1.1 a.2))) a =
        J (r ≫ Sum.elim (fun _ : PUnit.{1} => (pGl U e))
          (Sum.elim (fun a : S × Fin 4 => (pGl U e) ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => Oφl U e a.1.1 a.2)) a) := by
      rintro (a | a | a)
      exacts [rfl, congrArg J (Category.assoc _ _ _), rfl]
    exact fun a b hab => (c a).trans ((congrArg (fun q => J (r ≫ q)) hab).trans (c b).symm)

theorem expandsAt_of_val (S : Finset D.toPre.X) (h : ∀ (y : (thickObj R I e G).left) (J), Good D.toPre.P.L y J →
    (∀ α ∉ S, sval (f α) (pGl U e) y J = 0) ∧ ∀ jL, (fGl I G e) y ∈ U.LG.L.U jL →
      (wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL =
        ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val) : U.ExpandsAt e k σ f := by
  refine ⟨S, fun α hα j => fn_ext fun y hy => ?_, ?_⟩
  · choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_zero (𝟙 _) y _ hy).symm)
    rw [Category.id_comp]
    exact (sec_trans (f α) _ y hy (Good.mem hJ _ _)).trans ((congrArg _ ((h y J hJ).1 α hα)).trans (mul_zero _))
  · rintro ⟨p₁, p₂⟩ j₁ jf jt hj hc
    obtain rfl : j₁ = fun _ => p₂ PUnit.unit := funext fun i => (congrArg j₁ (Subsingleton.elim i 0)).trans hj
    refine fn_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := exp_germ U e k σ f (𝟙 _) y S (p₁ PUnit.unit) (p₂ PUnit.unit) jf jt hy
    obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ _ hc (by
      rintro (a | a | a)
      exacts [mem_pull.1 hy.1.1.1, Set.mem_iInter.1 (U.expW_le_f e _ _ jf jt a.1.2 hy) a.2,
        Set.mem_iInter.1 (U.expWeight_le_chart_weight e _ _ jf jt a.1.2 hy) a.2])
    have H := (h y J hJ).2 (p₂ PUnit.unit) (mem_pull.1 hy.1.1.2)
    have e₀ : J (pGl U e) = p₁ PUnit.unit := eJ (.inl PUnit.unit)
    rw [e₀] at H
    rw [Category.id_comp] at k₁ k₂
    refine k₁.trans (H.trans (Eq.trans (Finset.sum_congr rfl fun α hα => ?_) k₂.symm))
    rw [sval_of (f α) _ y J (jf α) (fun a => eJ (.inr (.inl (⟨α, hα⟩, a)))),
      val_of (tG U e α) _ y J (jt α) (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inr (⟨α, hα⟩, a))))]

end One

section Box

variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

def bw (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (ψ : Z ⟶ X') (z : Z) (jN : Fin j → M.ι) (k : M'.ι) :
    (Z.presheaf.stalk z)ˣ := gm ψ z (LB.wchart M pr jN ⊓ M'.U k) (w.s (jN, k))

theorem gm_linCombIso (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι)
    (hz : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ jN ⊓ LB.wchart M' φ jM) :
    gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ jN ⊓ LB.wchart M' φ jM) ((LB.linCombIso w φ ε).s (jN, jM)) =
      ∏ a, bw w (r ≫ φ a) z (jN a) (jM a) ^ ε a :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a)
    ((gm_res r z _ hz _).trans (gm_pull r (φ a) z (LB.wchart M pr (jN a) ⊓ M'.U (jM a))
      ⟨Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a⟩ _))))

theorem box_sec_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (X' ⟶ X')}
    {φ : Fin j → K → (X ⟶ X)} {ε : K → ℤ} (hφ : ∀ i a, φ' a ≫ pr i = pr i ≫ φ i a) (s' : LB.Sec (LB.LinComb M' φ' ε))
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
      pr i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(X', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((pr i).app _).hom ((s i).f (fun a => jN a i))))
    (q : Z ⟶ X') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * sval s' q y J' =
      ∏ i, sval (s i) (q ≫ pr i) y J := by
  have hm : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((q ≫ φ' a) ≫ pr i), hJ'.mem _ q⟩
  have E := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  refine ((gs_mul q y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit q y _ hm _).trans (congrArg Units.val
    (gm_linCombIso w φ' ε q y _ _ hm))) (gs_res q y _ hm _))).symm.trans (E.trans ((gs_prod q y _ hm _ _).trans
    (Finset.prod_congr rfl fun i _ => ?_)))
  rw [sval_of (s i) _ y J (fun a => J ((q ≫ φ' a) ≫ pr i)) (fun a => by rw [Category.assoc, ← hφ, Category.assoc])]
  exact (gs_res q y (hle _ _ i) hm _).trans (gs_pull q (pr i) y _ (hle _ _ i hm) _)

theorem box_gen_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (y : Y) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a) * val t' (𝟙 _) y J' = ∏ i, val (t i) (ρ i) y J := by
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J (φ' a ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ (φ' a ≫ pr i), Set.mem_iInter.2 fun a => hJ' (φ' a)⟩
  have E := congrArg (gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J (φ' a ≫ pr i)) ⊓
    LB.wchart M' φ' (fun a => J' (φ' a)))) (H (fun a i => J (φ' a ≫ pr i), fun a => J' (φ' a)))
  have E₁ := gm_linCombIso w φ' ε (𝟙 Y) y _ _ hm
  simp only [Category.id_comp] at E₁
  rw [val_of t' _ y J' (fun a => J' (φ' a)) (fun a => by rw [Category.id_comp])]
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) E₁ (gm_res (𝟙 Y) y inf_le_right hm _))).symm.trans
    (E.symm.trans ((gm_res (𝟙 Y) y inf_le_left hm _).trans ?_))
  refine (map_prod (gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J (φ' a ≫ pr i))))
    (fun i => res (GeneratorPullback.box_le M pr φ' (fun a i => J (φ' a ≫ pr i)) i)
      ((GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => J (φ' a ≫ pr i)))) Finset.univ).trans
    (Finset.prod_congr rfl fun i _ => ?_)
  rw [val_of (t i) (ρ i) y J (fun a => J (φ' a ≫ pr i)) (fun a => congrArg J (hψ i a).symm)]
  exact (gm_res (𝟙 Y) y (GeneratorPullback.box_le M pr φ' _ i) hm.1 _).trans (gm_rp₁ (ρ i) y _ _ _ (GeneratorPullback.box_le M pr φ' _ i hm.1) _)

end Box

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

variable (I pG) in

abbrev rhoE (e : ℕ) (i : Fin j) : (thickObj R I e G').left ⟶ (thickObj R I e G).left :=
  ((Over.pullback (thick R I e)).map (pG.pr i)).left

variable (pD) in

def omB {Z : Scheme.{0}} (y : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι)
    (ψ : Z ⟶ D'.toPre.P.A.left) : (Z.presheaf.stalk y)ˣ := bw pD.w ψ y (fun i => J (ψ ≫ (pD.pw.pr i).left)) (J' ψ)

theorem box_q (P : UnifPowOf3 pD pA pG U' U) (e : ℕ) (i : Fin j) :
    pGl U'.toUnifPre e ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ pGl U.toUnifPre e := (P.t_pr e 0).choose i 2

set_option maxHeartbeats 800000 in
theorem box_F (P : UnifPowOf3 pD pA pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {k : ℕ} {f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α}
    {f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α'} (hf' : IsBoxFamB pD k f' f) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a).val * sval (f' α') (pGl U'.toUnifPre e) y J' =
      ∏ i, sval (f i (pD.xe α' i)) (rhoE I pG e i ≫ (pGl U.toUnifPre e)) y J := by
  obtain ⟨hφ, H⟩ := hf' α'
  have := box_sec_val pD.w hφ (f' α') (fun i => f i (pD.xe α' i)) _ H (pGl U'.toUnifPre e) y hJ hJ'
  simp only [box_q P] at this
  exact this

set_option maxHeartbeats 800000 in
theorem box_product_transition_identity (P : UnifPowOf3 pD pA pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' (Oφl U'.toUnifPre e α' a) ^ Oinvε a) * val (tG U'.toUnifPre e α') (𝟙 _) y J' =
      ∏ i, val (tG U.toUnifPre e (pD.xe α' i)) (rhoE I pG e i) y J := by
  obtain ⟨hψ, H⟩ := P.t_pr e α'
  exact box_gen_val pD.w hψ _ (fun i => tG U.toUnifPre e (pD.xe α' i)) H y hJ hJ'

theorem box_om {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι} (k : ℕ) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a) * ∏ a, omB pD y J J' (Oφl U'.toUnifPre e α' a) ^ Oinvε a =
      omB pD y J J' (pGl U'.toUnifPre e) ^ k := by
  have a₀ : (pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' 0 = (pGl U'.toUnifPre e) := Category.comp_id _
  have a₁ : (pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' 1 = Oφl U'.toUnifPre e α' 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U'.gt e).pG (𝟙 _) (cP D'.toPre _ α')).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D'.toPre _ α')))
  have a₂ : (pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' 2 = Oφl U'.toUnifPre e α' 1 :=
    congrArg (fun z => z.left) (comp_cP D'.toPre (U'.gt e).pG α')
  have a₃ : (pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' 3 = Oφl U'.toUnifPre e α' 3 :=
    congrArg (fun z : _ ⟶ D'.toPre.P.A => z.left) (MonObj.comp_one (M := D'.toPre.P.A) (U'.gt e).pG)
  have a₄ : Oφl U'.toUnifPre e α' 2 = (pGl U'.toUnifPre e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

set_option maxHeartbeats 800000 in
theorem box_product_weight_identity (P : UnifPowOf3 pD pA pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    omB pD y J J' (pGl U'.toUnifPre e) * wv U'.toUnifPre e (𝟙 _) y (J' (pGl U'.toUnifPre e)) jL' =
        (∏ i, wv U.toUnifPre e (rhoE I pG e i) y (J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left)) (jL i)) *
          gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (P.wL.s (jL, jL')) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have hq := box_q P e
  have mM : (pGl U'.toUnifPre e) y ∈ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (fun i => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left), J' (pGl U'.toUnifPre e)) :=
    ⟨Set.mem_iInter.2 fun i => hJ ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left), hJ' (pGl U'.toUnifPre e)⟩
  have mW : ∀ i, rhoE I pG e i y ∈ (D.toPre.P.L.pull (pGl U.toUnifPre e)).U (fun _ => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left)) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL i) := fun i =>
    ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U (J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left))) (hq i)).mp (hJ _)),
      mem_pull.2 (hL₁ i)⟩
  have hm : (𝟙 _ : (thickObj R I e G').left ⟶ _) y ∈ (pGl U'.toUnifPre e) ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U
      (fun i => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left), J' (pGl U'.toUnifPre e)) ⊓
      (LB.div (D'.toPre.P.L.pull (pGl U'.toUnifPre e)) (U'.LG.L.pull (fGl I G' e))).U (fun _ => J' (pGl U'.toUnifPre e), fun _ => jL') ⊓
      (⨅ i, rhoE I pG e i ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (pGl U.toUnifPre e)) (U.LG.L.pull (fGl I G e))).U
        (fun _ => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left), fun _ => jL i)) ⊓
      (fGl I G' e) ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') :=
    ⟨⟨⟨mM, mem_pull.2 (hJ' (pGl U'.toUnifPre e)), mem_pull.2 hL'⟩, by
      rw [← Finset.inf_univ_eq_iInf]; exact mem_finf _ _ _ fun i _ => mW i⟩, mL⟩
  have W := congrArg (gm (𝟙 _) y _) (P.w_pr e (fun i => J ((pGl U'.toUnifPre e) ≫ (pD.pw.pr i).left)) (J' (pGl U'.toUnifPre e)) jL' jL)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ (pGl U'.toUnifPre e) y _ _ _ hm _) (gm_res (𝟙 _) y _ hm _))).symm.trans (W.trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
          gm_rp₁ (rhoE I pG e i) y _ _ _ hm _)) (gm_rp₁ (fGl I G' e) y _ _ _ hm _))))

set_option maxHeartbeats 800000 in
theorem box_S (P : UnifPowOf3 pD pA pG U' U) {e k : ℕ} {y : (thickObj R I e G').left} {σ : Fin j → H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    (hσ' : IsBoxSecG pG P.wL k σ' σ) {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    (gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (P.wL.s (jL, jL')) ^ k).val *
        sv U'.toUnifPre k σ' (fGl I G' e) y jL' = ∏ i, sv U.toUnifPre k (σ i) (rhoE I pG e i ≫ fGl I G e) y (jL i) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have Sg := congrArg (gs (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL'))) (hσ' jL jL')
  rw [gs_mul _ y _ mL, gs_unit _ y _ mL, map_pow] at Sg
  refine (congrArg₂ (· * ·) rfl (gs_res (fGl I G' e) y (boxG_le_b pG jL jL') mL _).symm).trans
    (Sg.trans ((gs_prod _ y _ mL _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]
  exact (gs_res (fGl I G' e) y (boxG_le_c pG jL jL' i) mL _).trans
    (gs_pull (fGl I G' e) (pG.pr i).left y _ (boxG_le_c pG jL jL' i mL) _)

theorem expandsAt_box' (P : UnifPowOf3 pD pA pG U' U) (k e : ℕ) (σ : Fin j → H0 U.LG.L k)
    (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ i, U.ExpandsAt e k (σ i) (f i))
    (σ' : H0 U'.LG.L k) (f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α')
    (hσ' : IsBoxSecG pG P.wL k σ' σ) (hf' : IsBoxFamB pD k f' f) :
    U'.ExpandsAt e k σ' f' := by
  classical
  choose S hS using fun i => expandsAt_val U.toUnifPre e k (σ i) (f i) (hE i)
  refine expandsAt_of_val U'.toUnifPre e k σ' f' ((Fintype.piFinset S).map pD.xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G').left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hF := box_F P hJ hJ' hf'
  have hT := box_product_transition_identity P hJ hJ'
  have hω := box_om (pD := pD) (U' := U') (y := y) (J := J) (J' := J') k
  have hq := box_q P e
  refine ⟨fun α' hα => ?_, fun jL' hL' => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, pD.xe α' i ∉ S i := by
      by_contra hc
      exact hα (Finset.mem_map.2 ⟨pD.xe α', Fintype.mem_piFinset.2 fun i => by_contra fun h => hc ⟨i, h⟩,
        pD.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').trans (Finset.prod_eq_zero (Finset.mem_univ i)
      ((hS i _ (rhoE I pG e i) y J hJ).1 _ hi)))
  · choose jL hL using fun i => exists_chart U.LG.isLB ((pG.pr i).left ((fGl I G' e) y))
    have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
      (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (pullback.lift_fst _ _ _ :
        rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left)).mpr (hL i)
    have W' := box_product_weight_identity P hJ hJ' hL hL'
    have Sg' := box_S P hσ' hL hL'
    refine (omB pD y J J' (pGl U'.toUnifPre e) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, W', mul_pow, Units.val_mul, _root_.mul_assoc, Sg', ← Finset.prod_pow,
      Units.coe_prod, ← Finset.prod_mul_distrib, Finset.sum_map, Finset.mul_sum]
    refine (Finset.prod_congr rfl fun i _ => ?_).trans ((Finset.prod_univ_sum S fun i α =>
      sval (f i α) (rhoE I pG e i ≫ (pGl U.toUnifPre e)) y J * (val (tG U.toUnifPre e α) (rhoE I pG e i) y J).val).trans
      (Finset.sum_congr rfl fun x _ => ?_))
    · rw [hq]; exact (hS i _ (rhoE I pG e i) y J hJ).2 (jL i) (hL₁ i)
    · obtain ⟨α', rfl⟩ := pD.xe.surjective x
      have e₀ : pD.xe.symm.toEquiv.toEmbedding (pD.xe α') = α' := pD.xe.symm_apply_apply α'
      rw [e₀, Finset.prod_mul_distrib, ← hF α', ← Units.coe_prod, ← hT α', ← hω α', Units.val_mul, Units.val_mul,
        _root_.mul_mul_mul_comm]

end Exp

end ReciprocityTheory.ChartRestriction.G.DVR
