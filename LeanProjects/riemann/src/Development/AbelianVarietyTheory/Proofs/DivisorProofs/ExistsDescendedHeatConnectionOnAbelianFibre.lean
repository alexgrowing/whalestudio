import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.KS.GlueDer (rsT_eq res_app pre_mono)
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_sub)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem exists_descData : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a, IsField ⊤ (dd a)) → (∀ a V r, dd a V (constFn Y.H.hom V r) = 0) → (∀ a α V f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∃ (V : h.J → Q.P.A.left.Opens) (E : h.J → Fld Q.P.A.left) (P : ∀ i, Γ(Q.P.A.left, V i)), (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ (∀ i, IsLift Q.P.A D (V i) (E i)) ∧ (∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (E i V' f) = GlobalTheory.HeatConn.dE h ν i _ ((Y.q.left.app V').hom f)) ∧ ∀ i, (Y.q.left.app (V i)).hom (P i) = rsT (GlobalTheory.HeatConn.pE h ν i) (Y.q.left ⁻¹ᵁ V i) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hfield hconst hwt hB
  choose V hV using fun i => (hB i).1
  have hlift : ∀ i, IsLift Y.H D (Y.q.left ⁻¹ᵁ V i) (dE h ν i) := fun i => by
    rw [← hV i]
    refine ⟨isField_dE h ν hfield i, fun O hO r => ?_⟩
    show h.d i O _ + constFn Y.H.hom O ν * ∑ a, constFn Y.H.hom O (h.u a) * dd a O (constFn Y.H.hom O r) = _
    simp only [hconst, mul_zero, Finset.sum_const_zero, add_zero]
    exact (h.lift i).2 O hO r
  have hwt0 : ∀ i (V' : Q.P.A.left.Opens), V' ≤ V i → ∀ f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V') f →
      IsWt Y 0 (Y.q.left ⁻¹ᵁ V') (dE h ν i _ f) := by
    intro i V' hV' f hf
    exact WtAlg.isWt_add ((hB i).2.2.2 0 V' ((GlobalTheory.KS.GlueDer.pre_mono _ hV').trans (hV i).ge) f hf)
      (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν)
        (WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hwt a 0 _ f hf)))
  choose E hE hq using fun i => AbConst.exists_desc Y (V i) (dE h ν i) D (hlift i) (hwt0 i)
  have hP : ∀ i, ∃ a, (Y.q.left.app (V i)).hom a = rsT (pE h ν i) (Y.q.left ⁻¹ᵁ V i) := fun i => by
    refine AbConst.exists_app_eq Y ?_
    have hw : IsWt Y 0 (h.W i) (pE h ν i) :=
      WtAlg.isWt_add (hB i).2.1 (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν) (hB i).2.2.1)
    have tr : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)), W = Y.q.left ⁻¹ᵁ V i → IsWt Y 0 W s →
        IsWt Y 0 _ (rsT s (Y.q.left ⁻¹ᵁ V i)) := by
      rintro W s rfl hs
      rwa [WtAlg.rsT_self]
    exact tr _ _ (hV i) hw
  choose P hP using hP
  exact ⟨V, E, P, hV, hE, hq, hP⟩

theorem exists_glue_desc : ∀ {R K : Type} [CommRing R] [Field K] (G : Over (Sp R)) (A₀ : Over (Sp K)) (m₀ : A₀.left ⟶ G.left) (φ : R →+* K), m₀ ≫ G.hom = A₀.hom ≫ spMap φ → ∀ (D : R → R) {I : Type} (V : I → G.left.Opens), ⨆ i, V i = ⊤ → ∀ (E : I → Fld G.left), (∀ i, IsLift G D (V i) (E i)) → (∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f)) → ∃ ed : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) ⊤ ed ∧ ∀ i U, U ≤ V i → ∀ f, ed U f = (m₀.app U).hom (E i U f) := by
  intro R K _ _ G A₀ m₀ φ hm D I V hV E hE hc
  have hW : ∀ y, ∃ i, m₀ y ∈ V i := fun y => by
    have hy : m₀ y ∈ ⨆ i, V i := by rw [hV]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have he : ∀ i, GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) (V i) (fun W f => (m₀.app W).hom (E i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(hE i).1.1 W hW, map_add]
    · rw [(hE i).1.2.1 W hW, map_add, map_mul, map_mul]
    · rw [(hE i).1.2.2 W W' h' hW, GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ h'), GlobalTheory.KS.GlueDer.res_app m₀ h']
    · rw [(hE i).2 W hW, GlobalTheory.KS.GlueDer.app_const φ _ _ m₀ hm]
  obtain ⟨ed, hed, hchar⟩ := GlobalTheory.InteriorKS.glue_along A₀.hom G.hom m₀ (fun r => φ (D r)) V hW
    (fun i W f => (m₀.app W).hom (E i W f)) he fun i i' O hO f => hc i i' O hO f
  refine ⟨ed, hed, fun i U hU f => hchar U f _ fun i' => ?_⟩
  have h1 := (he i).res U (U ⊓ V i') inf_le_left hU f
  rw [GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ inf_le_left)] at h1
  rw [← h1]
  exact hc i i' _ (le_inf (inf_le_left.trans hU) inf_le_right) _

theorem connK_transition : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] {φ : R →+* K} {e : ℕ} {ν : R} {A₀ : Over (Sp K)} [GrpObj A₀] {m₀ : A₀.left ⟶ Q.P.A.left}, GlobalTheory.HeatConn.IsFibre Y h φ e ν A₀ m₀ → ∀ {V : h.J → Q.P.A.left.Opens} {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}, GlobalTheory.HeatConn.IsDesc Y h ν m₀ V ed pb → (∀ i, V i ≤ Q.P.L.U (h.j i)) → ∀ (i i' : h.J), ed (V i ⊓ V i') (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) = pbT m₀ (Q.P.L.g (h.j i) (h.j i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) * (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hD hV i i'
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hF.inv
    rw [Nat.cast_zero, mul_zero] at this
    exact zero_ne_one this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0
  have hUL : V i ⊓ V i' ≤ Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i') := inf_le_inf (hV i) (hV i')
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hz' : (a ≫ Y.q.left) z ∈ V i ⊓ V i' := by rw [w]; exact hz
  have haΩ : a z ∈ Y.q.left ⁻¹ᵁ (V i ⊓ V i') := hz'
  have hΩW : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ h.W i ⊓ h.W i' := by
    rw [hD.1 i, hD.1 i']; exact le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right)
  have hΩL : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) := pre_mono _ hUL
  have hG : (Y.q.left.app (V i ⊓ V i')).hom (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) =
      pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [rsT_eq hUL, ← res_app Y.q.left hUL (pre_mono _ hUL), pbT, dif_pos hΩL]; rfl
  have hz1 : (b ≫ m₀) z ∈ V i := hz.1
  have hz2 : (b ≫ m₀) z ∈ V i' := hz.2
  rw [hD.2.1 Z a b w z i _ inf_le_left hz, hG, gs_mul b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (pre_mono _ hUL) hz,
    gs_rsT b z (pre_mono m₀ inf_le_right) hz, gs_rsT b z (pre_mono m₀ inf_le_left) hz, hD.2.2 Z a b w z i' hz2,
    hD.2.2 Z a b w z i hz1, ← w, ← gs_pbT a Y.q.left z hΩL haΩ, ← gs_rsT a z (hΩW.trans inf_le_right) haΩ,
    ← gs_rsT a z (hΩW.trans inf_le_left) haΩ]
  simp only [gs_eq_gsH a z _ haΩ]
  set π := gsH a z _ haΩ
  set G := pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i'))
  have hΘ : ∀ a' b', π (constFn Y.H.hom _ (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z _ haΩ, hF.symb, cst_eq_cstH, map_zero]
  have hpow : ∀ (m : ℕ) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))),
      dE h ν i _ (f ^ (m + 1)) = ((m + 1 : ℕ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))) * f ^ m * dE h ν i _ f := by
    intro m f
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, (isField_dE h ν hF.field i).2.1 _ (hΩW.trans inf_le_left), ih]
      push_cast; ring
  have e1 := congrArg π (h.glue (k + 1) i i' _ hΩW 1)
  rw [_root_.mul_one, map_op h ν (k + 1) hF.inv i _ (hΩW.trans inf_le_left) π hΘ, map_mul,
    map_op h ν (k + 1) hF.inv i' _ (hΩW.trans inf_le_right) π hΘ, hpow,
    AbConst.isField_one (isField_dE h ν hF.field i') (hΩW.trans inf_le_right)] at e1
  simp only [map_mul, map_pow, map_natCast, map_one, map_zero, zero_add, _root_.mul_one] at e1
  have h2 : IsUnit (2 : Z.presheaf.stalk z) := by
    simpa only [map_ofNat] using (two_ne_zero (α := K)).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hk : IsUnit (((k + 1 : ℕ)) : Z.presheaf.stalk z) := by
    simpa only [map_natCast] using
      (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k) : ((k + 1 : ℕ) : K) ≠ 0).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hGu : IsUnit G := by
    simp only [G, pbT, dif_pos hΩL]; exact (Units.isUnit _).map _
  have hc : IsUnit (2 * ((k + 1 : ℕ) : Z.presheaf.stalk z) ^ 2 * π G ^ k) := (h2.mul (hk.pow 2)).mul ((hGu.map π).pow k)
  refine hc.mul_left_cancel ?_
  push_cast at e1 ⊢
  linear_combination e1

theorem exists_connK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∃ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb ∧ IsDesc Y h ν m₀ V ed pb := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF
  have := (AbConst.surjective_q Y).1
  obtain ⟨V, E, P, hW, hE, hq, hP⟩ := exists_descData Y h ν hF.field hF.const hF.wt hF.basic
  have hm : m₀ ≫ Q.P.A.hom = A₀.hom ≫ spMap φ := hF.pull.1.w
  have hcov : ⨆ i, V i = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hW] at hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hVL : ∀ i, V i ≤ Q.P.L.U (h.j i) := fun i x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ h.W i := by rw [hW]; exact hx
    exact h.le i hy
  have hc : ∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f) := by
    intro i i' O hO f
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    have hz' : (a ≫ Y.q.left) z ∈ O := by rw [w]; exact hz
    rw [gs_pull b m₀ z O hz, gs_pull b m₀ z O hz, ← w, ← gs_pull a Y.q.left z O hz', ← gs_pull a Y.q.left z O hz',
      hq i O (hO.trans inf_le_left), hq i' O (hO.trans inf_le_right)]
    refine hF.dE_agree w z i i' _ ?_ hz' _
    rw [hW i, hW i']
    exact le_inf (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_left)) (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_right))
  obtain ⟨ed, hed, hedE⟩ := exists_glue_desc Q.P.A A₀ m₀ φ hm D V hcov E hE hc
  let pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i) := fun i => (m₀.app (V i)).hom (P i)
  have hD : IsDesc Y h ν m₀ V ed pb := by
    refine ⟨hW, fun Z a b w z i U hU hz f => ?_, fun Z a b w z i hz => ?_⟩
    · have hz' : (a ≫ Y.q.left) z ∈ U := by rw [w]; exact hz
      rw [hedE i U hU f, gs_pull b m₀ z U hz, ← w, ← gs_pull a Y.q.left z U hz', hq i U hU f]
    · have hz' : (a ≫ Y.q.left) z ∈ V i := by rw [w]; exact hz
      show gs b z _ ((m₀.app (V i)).hom (P i)) = _
      rw [gs_pull b m₀ z (V i) hz, ← w, ← gs_pull a Y.q.left z (V i) hz', hP i]
      exact GlobalTheory.KS.DlogPol.gs_rsT a z (hW i).ge hz' _
  exact ⟨V, ed, pb, ⟨hed, hcov, hVL, fun i i' => connK_transition Y h hF hD hVL i i'⟩, hD⟩

end GlobalTheory.HeatConn
