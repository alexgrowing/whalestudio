import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsThetaTraceMulTIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteSurjectiveOfPoints
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare GlobalTheory.ThetaTrace

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaTransport

section General

variable {X Y Y' : Scheme.{0}} {M : LB X} {K : Type} [Fintype K]

theorem exists_const {S₀ : Scheme.{0}} (hM : M.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ S₀)
    (hp : Function.Surjective p.appTop.hom)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    {u : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) u hu
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))

theorem exists_sec_of_invariant (hM : M.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) {I : Type}
    (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (s : LB.Sec (LB.LinComb M (fun k => m ≫ φ k) ε))
    (hinv : ∀ i y J, Good M y J → sval s (t i) y J = sval s (𝟙 Y') y J) :
    ∃ s' : LB.Sec (LB.LinComb M φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good M z J →
      sval s' (r ≫ m) z J = sval s r z J := by
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have le : ∀ j : K → M.ι, m ⁻¹ᵁ LB.wchart M φ j ≤ LB.wchart M (fun k => m ≫ φ k) j := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hex : ∀ j : K → M.ι, ∃ g : Γ(Y, LB.wchart M φ j),
      (m.app _).hom g = (Y'.presheaf.map (homOfLE (le j)).op).hom (s.f j) := fun j => by
    refine (hd _ _ fun i e => fn_ext fun y hy => ?_).exists
    choose J hJ using fun χ : Y' ⟶ X => exists_chart hM (χ y)
    have gJ : Good M y J := hJ
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ LB.wchart M φ j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    refine ((gs_res (t i) y (le j) (e hy) _).trans (sec_trans s (t i) y (le j (e hy)) (gJ.mem _ _))).trans
      (Eq.trans ?_ ((gs_res (𝟙 Y') y (le j) hy _).trans (sec_trans s (𝟙 Y') y (le j hy) (gJ.mem _ _))).symm)
    refine congrArg₂ (· * ·) (congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)) (hinv i y J gJ)
    exact congrArg (fun ψ : Y' ⟶ X => gm ψ y (M.U (j k) ⊓ M.U (J ψ)) (M.g (j k) (J ψ)) ^ ε k)
      (show t i ≫ m ≫ φ k = 𝟙 Y' ≫ m ≫ φ k by rw [reassoc_of% ht i, Category.id_comp])
  choose b hb using hex
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → M.ι), m (r z) ∈ LB.wchart M φ j →
      gs (r ≫ m) z _ (b j) = gs r z _ (s.f j) := fun Z r z j hj =>
    (gs_pull r m z _ hj _).symm.trans ((congrArg _ (hb j)).trans (gs_res r z (le j) hj _))
  refine ⟨⟨b, fun i j => hinj _ (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ => ?_⟩
  · refine (gs_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)
    refine ((gs_res _ y _ hy _).trans (v _ (𝟙 Y') y i hy.1)).trans
      ((sec_trans s (𝟙 Y') y (le i hy.1) (le j hy.2)).trans (Eq.symm ?_))
    refine (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val
      ((gm_linComb M φ ε _ y i j hy.1 hy.2).trans ?_))) ((gs_res _ y _ hy _).trans (v _ (𝟙 Y') y j hy.2)))
    simp only [trF, Category.assoc, Category.id_comp]
  · rw [sval_of _ (r ≫ m) z J (fun k => J (r ≫ m ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact v Z r z _ (Set.mem_iInter.2 fun k => hJ (r ≫ m ≫ φ k))

theorem descends_of_points {Ω : Type} [Field Ω] [IsAlgClosed Ω] (q : Y ⟶ Sp Ω) [LocallyOfFiniteType q]
    (m : Y' ⟶ Y) [Etale m] [QuasiCompact m] [Surjective m] {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (htr : ∀ y y' : Sp Ω ⟶ Y', y ≫ m ≫ q = 𝟙 _ → y ≫ m = y' ≫ m → ∃ i, y' = y ≫ t i)
    (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U))
    (hf : ∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) :
    ∃! g : Γ(Y, U), (m.app U).hom g = f := by
  have h0 : ∀ i, 𝟙 Y' ≫ m = t i ≫ m := fun i => by rw [ht, Category.id_comp]
  let gr := fun i => pullback.lift (𝟙 Y') (t i) (h0 i)
  have hgr : ∀ i, IsOpenImmersion (gr i) := fun i => LevQuot.isOpenImmersion_graph m (t i) (h0 i)
  let π : pullback m m ⟶ Sp Ω := pullback.fst m m ≫ m ≫ q
  have : JacobsonSpace ↥(pullback m m) := LocallyOfFiniteType.jacobsonSpace π
  have hW : IsOpen (⋃ i, Set.range (gr i)) := isOpen_iUnion fun i => (gr i).isOpenEmbedding.isOpen_range
  have all : ∀ w, w ∈ ⋃ i, Set.range (gr i) := fun w => by
    by_contra hw
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := (⋃ i, Set.range (gr i))ᶜ) ⟨w, hw⟩
      hW.isClosed_compl.isLocallyClosed
    replace hc' : IsClosed {c} := hc'
    let v := pointOfClosedPoint π c hc'
    obtain ⟨i, hi⟩ := htr (v ≫ pullback.fst m m) (v ≫ pullback.snd m m)
      ((Category.assoc _ _ _).trans (pointOfClosedPoint_comp π c hc'))
      (by rw [Category.assoc, Category.assoc, pullback.condition])
    have e : (v ≫ pullback.fst m m) ≫ gr i = v := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, hi]
    refine hc (Set.mem_iUnion.2 ⟨i, (v ≫ pullback.fst m m) (IsLocalRing.closedPoint Ω), ?_⟩)
    exact (congrArg (fun a : Sp Ω ⟶ pullback m m => a (IsLocalRing.closedPoint Ω)) e).trans
      (pointOfClosedPoint_apply π c hc' _)
  obtain ⟨h₁, h₂⟩ := LevQuot.invariant_descends m t ht (fun k _ _ y y' e => by
    let w := pullback.lift y y' e
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (all (w (IsLocalRing.closedPoint k)))
    have hr : Set.range w ⊆ Set.range (gr i) := by
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a (IsLocalRing.closedPoint k)]
    have e' := IsOpenImmersion.lift_fac (gr i) w hr
    have e₁ := congrArg (· ≫ pullback.fst m m) e'
    have e₂ := congrArg (· ≫ pullback.snd m m) e'
    simp only [gr, w, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at e₁ e₂
    exact ⟨i, by rw [← e₁, e₂]⟩) U
  obtain ⟨g, hg⟩ := h₂ f hf
  exact ⟨g, hg, fun g' hg' => h₁ (hg'.trans hg.symm)⟩

end General

section Algebra

theorem sum_reps_eq {G V : Type} [CommGroup G] [AddCommMonoid V] {C : Subgroup G} {p n n' : ℕ} {c : Fin n → G}
    {c' : Fin n' → G} (h : IsRepsModTors C p c) (h' : IsRepsModTors C p c') (Φ : G → V)
    (hΦ : ∀ a ∈ C, a ^ p = 1 → ∀ b, Φ (a * b) = Φ b) : ∑ i, Φ (c i) = ∑ j, Φ (c' j) := by
  choose e he hu using fun i => h'.2 _ (h.1 i)
  have sy : ∀ a b : G, (a * b⁻¹) ^ p = 1 → (b * a⁻¹) ^ p = 1 := fun a b hab => by
    rw [← inv_eq_one, ← inv_pow, mul_inv_rev, inv_inv, hab]
  refine Fintype.sum_bijective e ⟨fun i j hij => ?_, fun j => ?_⟩ _ _ fun i => ?_
  · exact (h.2 _ (h'.1 (e j))).unique (sy _ _ (hij ▸ he i)) (sy _ _ (he j))
  · obtain ⟨i, hi, -⟩ := h.2 _ (h'.1 j)
    exact ⟨i, (hu i j (sy _ _ hi)).symm⟩
  · rw [← hΦ _ (C.mul_mem (h.1 i) (C.inv_mem (h'.1 (e i)))) (he i) (c' (e i)), inv_mul_cancel_right]

theorem reps_mul {G : Type} [CommGroup G] {C : Subgroup G} {p n : ℕ} {c : Fin n → G} (h : IsRepsModTors C p c)
    {a : G} (ha : a ∈ C) : IsRepsModTors C p fun i => c i * a :=
  ⟨fun i => C.mul_mem (h.1 i) ha, fun b hb => by
    simpa only [mul_inv_rev, _root_.mul_assoc] using h.2 _ (C.mul_mem hb (C.inv_mem ha))⟩

theorem eq_zero_of_chars {G F : Type} [CommGroup G] [CommRing F] [IsDomain F] {n : ℕ} (δ : Fin n → G → Fˣ)
    (hδ : ∀ i a, ∃ u, ∀ b, δ i (a * b) = u * δ i b)
    (hsep : ∀ i j, (∀ a, δ i a * (δ i 1)⁻¹ = δ j a * (δ j 1)⁻¹) → i = j) (w : Fin n → F)
    (hw : ∀ a, ∑ i, (δ i a).val * w i = 0) (i : Fin n) : w i = 0 := by
  let χ : Fin n → G →* F := fun i => (Units.coeHom F).comp (MonoidHom.mk' (fun a => δ i a * (δ i 1)⁻¹) fun a b => by
    obtain ⟨u, hu⟩ := hδ i a
    have := hu 1
    rw [_root_.mul_one] at this
    rw [hu, this, mul_inv_cancel_right, _root_.mul_assoc])
  have hχ : Function.Injective χ := fun i j h => hsep i j fun a => Units.ext (DFunLike.congr_fun h a)
  have := Fintype.linearIndependent_iff.1 ((linearIndependent_monoidHom G F).comp χ hχ)
    (fun i => (δ i 1).val * w i) (funext fun a => by
      rw [Finset.sum_apply, Pi.zero_apply, ← hw a]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (δ i 1).val * w i * (δ i a * (δ i 1)⁻¹).val = _
      rw [mul_right_comm, ← Units.val_mul, mul_comm (δ i a), mul_inv_cancel_left]) i
  exact (Units.mul_right_eq_zero _).1 this

end Algebra
section Univ

open GlobalTheory.CechPic GlobalTheory.HeckePoint GlobalTheory.HeckeCompare GlobalTheory.HeckePointLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l}

theorem cls_prim {S : Scheme.{0}} (t : SAB H S) :
    cls _ t.PP.isLB = lam (cls _ t.PP.isLB) (𝟙 _) (t.act.act H.w0) :=
  ((cls_eq_iff t.PP.isLB (LB.isLB_linComb t.PP.isLB _ _)).2 t.prim).trans (cls_cube_two t.PP.isLB _ _ _)

theorem exists_isoGen {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} (hp : p.Prime) {x x' : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} {ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x'}
    {f : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)} (h : IsHkIsog p x x' C ψ f) :
    ∃ β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (conj x x' ψ) ((p : ℤ) ^ 2)), β.IsGen := by
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have : CharZero Ω := charZero_of_injective_ringHom (Spec.preimage (x ≫ Xo.s)).hom.injective
  have pl : ∀ y' : Sp Ω ⟶ Xo.X, y' ≫ Xo.s = x ≫ Xo.s →
      ∃ o : Obj Dw l (baseKA l) (x ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') := fun y' h =>
    obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x ≫ Xo.s) y' rfl rfl
      (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  obtain ⟨hy₂, g₁, g₂, g₃, -, -, g₆, -⟩ := h
  obtain ⟨o, ⟨m⟩⟩ := pl x rfl
  obtain ⟨ρ, e, e₀, e₁, e₂, e₃, e₄, -⟩ := exists_transfer_fst Xo.univ m
  obtain ⟨o₂, ⟨m₂⟩⟩ := pl x' hy₂
  obtain ⟨ρ₂, r, r₀, r₁, r₂, r₃, r₄, -⟩ := exists_transfer_fst Xo.univ m₂
  let ψ₂ : o.t.G ⟶ o₂.t.G := Over.homMk (e.hom ≫ ψ ≫ r.inv) (by
    rw [← r₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, g₁, e₁])
  have hψ : ∀ a, ρ₂ (a ≫ ψ₂) = f (ρ a) := fun a => fibPt_injective _ (by
    rw [r₂, ← g₂, e₂]
    show (a.left ≫ e.hom ≫ ψ ≫ r.inv) ≫ r.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
  have := o₂.proper
  have one : ∀ (G : Over (Sp Ω)) [GrpObj G], (1 : 𝟙_ (Over (Sp Ω)) ⟶ G) = η[G] := fun G _ => by
    rw [Hom.one_def]; simp
  have hom : IsMonHom ψ₂ := hL.rigidity _ _ _ hab hab₂ ψ₂ (by
    rw [← one, ← one]
    exact ρ₂.injective (by rw [hψ, map_one, map_one, map_one]))
  have lin : ∀ a, o.t.act.act a ≫ ψ₂ = ψ₂ ≫ o₂.t.act.act a := fun a => hom_ext_pts hab.smooth fun u =>
    ρ₂.injective (by rw [← Category.assoc, ← Category.assoc, hψ, r₃, hψ, e₃, g₃])
  have hA := o.t.PP.isLB
  have hM := o₂.t.PP.isLB
  have hU := Xo.univ.t.PP.isLB
  have hn : (lbPow o.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hA _ _
  have h' := lam_iso_of_weil_pairings hL Ω (objPol o) (objPol o₂) ψ₂ p (p ^ 2) hom hp inferInstance
    fun n a b c _ hc _ _ hw => (r₄ _ _ _ _).2 (by
      rw [hψ, hψ]
      exact g₆ n _ _ c hc ((e₄ _ _ _ _).1 hw))
  have h'' := (cls_cube_two hn _ _ _).symm.trans
    (((cls_eq_iff (LB.isLB_linComb hn _ _) (LB.isLB_linComb (pull_isLB hM _) _ _)).2 h').trans
      (cls_cube_two (pull_isLB hM _) _ _ _))
  rw [cls_lbPow hA, lam_nsmul, cls_pull hM, lam_pull] at h''
  have h₃ := congrArg (pull (lift (𝟙 o.t.G) (o.t.act.act H.w0)).left) h''
  rw [map_nsmul, pull_lam, pull_lam, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, ← cls_prim, lin,
    Category.id_comp] at h₃
  have h₄ : (p ^ 2) • cls _ hA = pull ψ₂.left (cls _ hM) := by
    rw [h₃]
    conv_rhs => rw [cls_prim, pull_lam, Category.comp_id]
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨w₂, hw₂, -⟩ := m₂.lin
  rw [(cls_eq_iff hA (pull_isLB hU _)).2 ⟨w, hw⟩, (cls_eq_iff hM (pull_isLB hU _)).2 ⟨w₂, hw₂⟩, cls_pull hU,
    cls_pull hU] at h₄
  have h₅ := congrArg (pull ((swap x).hom ≫ e.inv)) h₄
  have a₁ : ((swap x).hom ≫ e.inv) ≫ m.cm.F = (snd (Over.mk x) Xo.univ.t.G).left := by
    rw [← show _ = m.cm.F from e₀, Category.assoc, Iso.inv_hom_id_assoc, swap_hom_fst]
  have a₂ : (((swap x).hom ≫ e.inv) ≫ ψ₂.left) ≫ m₂.cm.F = conj x x' ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left := by
    rw [← show _ = m₂.cm.F from r₀, conj_apply]
    show (_ ≫ e.hom ≫ ψ ≫ r.inv) ≫ _ = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, swap_inv_snd]
  rw [map_nsmul, ← pull_comp, ← pull_comp, ← pull_comp, a₁, a₂] at h₅
  refine (cls_eq_zero_iff (LB.isLB_linComb hU _ _)).1 ?_
  rw [cls_linComb hU, Fin.sum_univ_two]
  show ((p : ℤ) ^ 2) • pull (snd (Over.mk x) Xo.univ.t.G).left _ + (-1 : ℤ) • pull (conj x x' ψ ≫ _) _ = 0
  rw [← h₅, ← Nat.cast_pow, natCast_zsmul, neg_one_zsmul, add_neg_cancel]

section Points

variable {Ω : Type} [CommRing Ω] {x x' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Z : Scheme.{0}}

def ptMap (h : IsLinHom Ψ) (σ : Z ⟶ Sp Ω) :
    (Over.mk (σ ≫ x) ⟶ Xo.univ.t.G) →* (Over.mk (σ ≫ x') ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun a => Over.homMk (push Ψ σ a) (push_hom h.1 _ a)) fun a b =>
    Over.OverMorphism.ext (h.2.1 _ _ a b _ _ rfl rfl).symm

theorem toFib_comp (h : IsLinHom Ψ) (σ : Z ⟶ Sp Ω) (a : Over.mk (σ ≫ x) ⟶ Xo.univ.t.G) :
    toFib x σ a ≫ Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left = (ptMap h σ a).left := rfl

theorem ptMap_act (h : IsLinHom Ψ) (σ : Z ⟶ Sp Ω) (r : 𝓞 E) (a : Over.mk (σ ≫ x) ⟶ Xo.univ.t.G) :
    ptMap h σ (a ≫ Xo.univ.t.act.act r) = ptMap h σ a ≫ Xo.univ.t.act.act r := by
  refine Over.OverMorphism.ext ?_
  have e : toFib x σ (a ≫ Xo.univ.t.act.act r) = toFib x σ a ≫ (Over.mk x ◁ Xo.univ.t.act.act r).left := by
    rw [toFib, toFib, ← Over.comp_left, lift_whiskerLeft]
  rw [Over.comp_left, ← toFib_comp, ← toFib_comp, e, Category.assoc, reassoc_of% (h.2.2 r),
    ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  simp only [Category.assoc]

abbrev toPt (x : Sp Ω ⟶ Xo.X) (σ : Z ⟶ Sp Ω) : (Over.mk (σ ≫ x) : Over Xo.X) ⟶ Over.mk x := Over.homMk σ rfl

theorem toFib_transl (σ : Z ⟶ Sp Ω) (a : Over.mk (σ ≫ x) ⟶ Xo.univ.t.G) (c : Over.mk x ⟶ Xo.univ.t.G) :
    toFib x σ a ≫ (translT Xo.univ.t.G c).left = toFib x σ (toPt x σ ≫ c * a) := by
  rw [toFib, toFib, ← Over.comp_left, lift_transl]

abbrev taut (x : Sp Ω ⟶ Xo.X) : Over.mk ((fst (Over.mk x) Xo.univ.t.G).left ≫ x) ⟶ Xo.univ.t.G :=
  Over.homMk (snd (Over.mk x) Xo.univ.t.G).left (snd_hom x)

theorem toFib_taut (x : Sp Ω ⟶ Xo.X) : toFib x _ (taut x) = 𝟙 _ :=
  gx_ext (by rw [toFib_fst, Category.id_comp]) (by rw [toFib_snd, Category.id_comp]; rfl)

theorem res_taut (σ : Z ⟶ Sp Ω) (a : Over.mk (σ ≫ x) ⟶ Xo.univ.t.G) :
    HeckeFrCompare.res x (toFib x σ a) (toFib_fst x σ a) ≫ taut x = a :=
  Over.OverMorphism.ext (toFib_snd x σ a)

theorem exists_toFib (r : Z ⟶ Gx x) : ∃ σ a, r = toFib x σ a :=
  ⟨_, HeckeFrCompare.res x r rfl ≫ taut x, by rw [toFib_res, toFib_taut, Category.comp_id]⟩

theorem isLinHom_mulT (x : Sp Ω ⟶ Xo.X) (n : ℕ) : IsLinHom (x := x) (x' := x) (mulT Xo.univ.t.G (Over.mk x) n).left := by
  have hp : ∀ (T : Scheme.{0}) (t : T ⟶ Sp Ω) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G),
      push (x := x) (x' := x) (mulT Xo.univ.t.G (Over.mk x) n).left t a = (a ^ n).left := fun T t a => by
    rw [push, toFib, ← Over.comp_left, ← Over.comp_left, mulT, lift_snd, MonObj.comp_pow, lift_snd]
  refine ⟨(isPointed_mulT n).1, fun T t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => ?_⟩
  · rw [hp] at h₁ h₂ ⊢
    rw [Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂, mul_pow]
  · have := Xo.univ.t.act.hom r
    rw [← Over.comp_left, ← Over.comp_left, mulT, comp_lift, lift_whiskerLeft, whiskerLeft_fst, MonObj.comp_pow,
      whiskerLeft_snd, MonObj.pow_comp]

theorem exists_primGen {S : Scheme.{0}} (t : SAB H S) :
    ∃ π : LB.Gen (LB.LinComb t.PP.L (K := Fin 4) ![(𝟙 t.G * t.act.act H.w0).left, 𝟙 _, (t.act.act H.w0).left,
      (1 : t.G ⟶ t.G).left] ![1, -2, -1, 1]), π.IsGen := by
  refine (cls_eq_zero_iff (LB.isLB_linComb t.PP.isLB _ _)).1 ?_
  have h := cls_prim t
  rw [lam, Over.id_left, pull_id] at h
  rw [cls_linComb t.PP.isLB, Fin.sum_univ_four]
  simp only [Matrix.cons_val, pull_id]
  linear_combination (norm := abel) -h

theorem prod_prim {S : Scheme.{0}} (t : SAB H S) {T : Over S} (y : T ⟶ t.G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ t.G.left) → U) :
    ∏ i, h (y.left ≫ (![(𝟙 t.G * t.act.act H.w0).left, 𝟙 _, (t.act.act H.w0).left,
      (1 : t.G ⟶ t.G).left] : Fin 4 → _) i) ^ (![1, -2, -1, 1] : Fin 4 → ℤ) i =
      h (y * y ≫ t.act.act H.w0).left * (h y.left ^ 2)⁻¹ * (h (y ≫ t.act.act H.w0).left)⁻¹ * h (1 : T ⟶ t.G).left := by
  rw [Fin.prod_univ_four]
  simp only [Matrix.cons_val, ← Over.comp_left, MonObj.comp_mul, Category.comp_id, MonObj.comp_one, zpow_one,
    zpow_neg, zpow_ofNat, pow_one]

variable {x₁ x₂ : Sp Ω ⟶ Xo.X} {Ψ₁ : Gx x ⟶ Gx x₁} {Ψ₂ : Gx x ⟶ Gx x₂} {k : ℤ}
  {β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k)} {β₂ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₂ k)}

theorem exists_quotGen (h₁ : β₁.IsGen) (h₂ : β₂.IsGen) :
    ∃ g : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![Ψ₂ ≫ (snd (Over.mk x₂) Xo.univ.t.G).left,
      Ψ₁ ≫ (snd (Over.mk x₁) Xo.univ.t.G).left] ![1, -1]), g.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) z J, Good Xo.univ.t.PP.L z J → val g r z J = val β₁ r z J * (val β₂ r z J)⁻¹ := by
  obtain ⟨g, hg, hv⟩ := exists_gen Xo.univ.t.PP.isLB (φ' := ![Ψ₂ ≫ (snd (Over.mk x₂) Xo.univ.t.G).left,
      Ψ₁ ≫ (snd (Over.mk x₁) Xo.univ.t.G).left]) (ε' := ![1, -1]) (fun V _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_iso' h) (prod_neg _ _ (prod_iso' h))).trans ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val, zpow_neg, zpow_one, mul_inv, inv_inv]
      rw [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul, mul_comm])
    (LB.mulGen _ _ _ _ _ β₁ (LB.invGen _ _ _ β₂)) (mulGen_isGen _ _ _ _ _ _ _ h₁ (invGen_isGen _ _ _ _ h₂))
  exact ⟨g, hg, fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv]⟩

theorem surj_gx (x : Sp Ω ⟶ Xo.X) : Function.Surjective (fst (Over.mk x) Xo.univ.t.G).left.appTop.hom :=
  surj_fst abelianSchemeLaws_all.1.globalFns (isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper) _

theorem exists_transl_const {φ : Fin 2 → (Gx x ⟶ Xo.univ.t.G.left)} {ε : Fin 2 → ℤ}
    {g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} (hg : g.IsGen) {c : Over.mk x ⟶ Xo.univ.t.G}
    (hc : ∀ i, (translT Xo.univ.t.G c).left ≫ φ i = φ i) :
    ∃ a : Γ(Sp Ω, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) z J, Good Xo.univ.t.PP.L z J →
      (val g (r ≫ (translT Xo.univ.t.G c).left) z J * (val g r z J)⁻¹).val =
        gs (r ≫ (fst (Over.mk x) Xo.univ.t.G).left) z ⊤ a := by
  obtain ⟨a, ha⟩ := exists_const Xo.univ.t.PP.isLB (fst (Over.mk x) Xo.univ.t.G).left (surj_gx x) (fun V _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (Finset.prod_congr rfl fun i _ =>
        congrArg (fun q => h q ^ ε i) (hc i)) (prod_neg _ _ rfl)).trans (mul_inv_cancel _))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hg (translT Xo.univ.t.G c).left) (invGen_isGen _ _ _ _ hg))
  refine ⟨a, fun Z r z J hJ => Eq.trans ?_ (ha Z r z J hJ)⟩
  rw [val_mul hJ, val_inv, val_pull hJ]

theorem quot_transl (l₁ : IsLinHom Ψ₁) (l₂ : IsLinHom Ψ₂) (h₁ : β₁.IsGen) (h₂ : β₂.IsGen)
    {c : Over.mk x ⟶ Xo.univ.t.G} (c₁ : c ∈ transKer _ Ψ₁) (c₂ : c ∈ transKer _ Ψ₂)
    (d₁ : c ≫ Xo.univ.t.act.act H.w0 ∈ transKer _ Ψ₁) (d₂ : c ≫ Xo.univ.t.act.act H.w0 ∈ transKer _ Ψ₂)
    (r : Z ⟶ Gx x) (z : Z) {J} (hJ : Good Xo.univ.t.PP.L z J) :
    val β₁ (r ≫ (translT Xo.univ.t.G c).left) z J * (val β₂ (r ≫ (translT Xo.univ.t.G c).left) z J)⁻¹ =
      val β₁ r z J * (val β₂ r z J)⁻¹ := by
  obtain ⟨g, hg, hv⟩ := exists_quotGen h₁ h₂
  obtain ⟨π, hπ⟩ := exists_primGen Xo.univ.t
  rw [← hv _ _ z J hJ, ← hv _ _ z J hJ]
  obtain ⟨σ, y, rfl⟩ := exists_toFib r
  have := Xo.univ.t.act.hom H.w0
  let w := Xo.univ.t.act.act H.w0
  let t₀ := (fst (Over.mk x) Xo.univ.t.G).left
  have F : ∀ (a : Over.mk (t₀ ≫ x) ⟶ Xo.univ.t.G) (V : Type) [CommGroup V] (h : (Gx x ⟶ Xo.univ.t.G.left) → V),
      ∏ i, h (toFib x t₀ a ≫ (![Ψ₂ ≫ (snd (Over.mk x₂) Xo.univ.t.G).left,
        Ψ₁ ≫ (snd (Over.mk x₁) Xo.univ.t.G).left] : Fin 2 → _) i) ^ (![1, -1] : Fin 2 → ℤ) i =
        h (ptMap l₂ t₀ a).left * (h (ptMap l₁ t₀ a).left)⁻¹ := fun a V _ h => by
    rw [Fin.prod_univ_two, ← zpow_neg_one, ← zpow_one (h (ptMap l₂ t₀ a).left)]; rfl
  let P := fun a : Over.mk (t₀ ≫ x) ⟶ Xo.univ.t.G => LB.pullGen _ _ _ g (toFib x t₀ a)
  have gP : ∀ a, (P a).IsGen := fun a => pullGen_isGen _ _ _ _ hg _
  obtain ⟨κ, hκ⟩ := exists_const Xo.univ.t.PP.isLB t₀ (surj_gx x) (fun V _ h => by
      refine (prod_sum₂ (K := (Fin 2 ⊕ Fin 2) ⊕ Fin 4) (K' := ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 4) (U := V) _
        (prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 4) (U := V) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (F _ V h) (F _ V h)) (prod_prim _ (ptMap l₁ t₀ (taut x)) h))
        (prod_neg _ _ (prod_sum₂ (K := (Fin 2 ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 4) (U := V) _
          (prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (F _ V h) (F _ V h)) (F _ V h))
          (prod_prim _ (ptMap l₂ t₀ (taut x)) h)))).trans ?_
      rw [map_mul, map_mul, map_one, map_one, ptMap_act, ptMap_act]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
      abel)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
        (gP (taut x * taut x ≫ w)) (gP 1)) (pullGen_isGen _ _ _ _ hπ (ptMap l₁ t₀ (taut x)).left))
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
        (gP (taut x)) (gP (taut x))) (gP (taut x ≫ w))) (pullGen_isGen _ _ _ _ hπ (ptMap l₂ t₀ (taut x)).left))))
  let v := fun a : Over.mk (σ ≫ x) ⟶ Xo.univ.t.G => val g (toFib x σ a) z J
  have vP : ∀ a b, val (P b) (toFib x σ a) z J = v (HeckeFrCompare.res x (toFib x σ a) (toFib_fst x σ a) ≫ b) :=
    fun a b => (val_pull hJ _ _ _).trans (by rw [← toFib_res x _ (toFib_fst x σ a)])
  have tm : ∀ {x' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} (l : IsLinHom Ψ) a,
      toFib x σ a ≫ (ptMap l t₀ (taut x)).left = toFib x σ a ≫ Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left :=
    fun l a => by rw [← toFib_comp, toFib_taut, Category.id_comp]
  have E₁ : ∀ a, (v (a * a ≫ w) * v 1 * val π (toFib x σ a ≫ Ψ₁ ≫ (snd (Over.mk x₁) Xo.univ.t.G).left) z J *
      (v a * v a * v (a ≫ w) * val π (toFib x σ a ≫ Ψ₂ ≫ (snd (Over.mk x₂) Xo.univ.t.G).left) z J)⁻¹).val =
      gs σ z ⊤ κ := fun a => by
    have := hκ _ (toFib x σ a) z J hJ
    rw [toFib_fst, val_mul hJ, val_inv, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, vP, vP, vP, vP,
      val_pull hJ, val_pull hJ, tm, tm, MonObj.comp_mul, MonObj.comp_one, ← Category.assoc, res_taut] at this
    exact this
  have E₂ : ∀ c' : Over.mk x ⟶ Xo.univ.t.G, c' ∈ transKer _ Ψ₁ → c' ∈ transKer _ Ψ₂ →
      ∃ u, ∀ a, v (toPt x σ ≫ c' * a) = u * v a := fun c' a₁ a₂ => by
    obtain ⟨b, hb⟩ := exists_transl_const hg (c := c') fun i => by
      fin_cases i
      · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) a₂)
      · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) a₁)
    have hb' : ∀ a, (v (toPt x σ ≫ c' * a) * (v a)⁻¹).val = gs σ z ⊤ b := fun a => by
      have := hb _ (toFib x σ a) z J hJ
      rwa [toFib_fst, toFib_transl] at this
    exact ⟨_, fun a => mul_inv_eq_iff_eq_mul.1 (Units.ext ((hb' a).trans (hb' 1).symm))⟩
  obtain ⟨u, hu⟩ := E₂ c c₁ c₂
  obtain ⟨u', hu'⟩ := E₂ _ d₁ d₂
  have E₃ := Units.ext ((E₁ (toPt x σ ≫ c * y)).trans (E₁ y).symm)
  rw [MonObj.mul_comp, Category.assoc, _root_.mul_mul_mul_comm, _root_.mul_assoc (toPt x σ ≫ c), hu, hu', hu, hu',
    ← toFib_transl, Category.assoc, Category.assoc, reassoc_of% (mem_transKer.1 c₁),
    reassoc_of% (mem_transKer.1 c₂)] at E₃
  have : u = 1 := by
    apply Additive.ofMul.injective
    have E₄ := congrArg Additive.ofMul E₃
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at E₄ ⊢
    linear_combination (norm := abel) -E₄
  rw [toFib_transl]
  exact (hu y).trans (by rw [this, _root_.one_mul])

end Points

section Field

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {p : ℕ}

theorem descends_ker (h : IsLinHom Ψ) [Etale Ψ] [QuasiCompact Ψ] [Surjective Ψ] (U : (Gx x').Opens)
    (f : Γ(Gx x, Ψ ⁻¹ᵁ U)) (hf : ∀ (c : transKer Xo.univ.t.G Ψ)
      (e : Ψ ⁻¹ᵁ U ≤ (translT Xo.univ.t.G c.1).left ⁻¹ᵁ (Ψ ⁻¹ᵁ U)),
      ((translT Xo.univ.t.G c.1).left.appLE _ _ e).hom f = f) : ∃! g : Γ(Gx x', U), (Ψ.app U).hom g = f := by
  have := Xo.univ.t.semi.smooth
  have : Smooth (fst (Over.mk x') Xo.univ.t.G).left := by
    show Smooth (pullback.fst x' Xo.univ.t.G.hom)
    infer_instance
  refine descends_of_points (Ω := Ω) (fst (Over.mk x') Xo.univ.t.G).left Ψ
    (fun c : transKer Xo.univ.t.G Ψ => (translT Xo.univ.t.G c.1).left) (fun c => c.2) (fun y y' e e' => ?_) U f hf
  obtain ⟨σ, a, rfl⟩ := exists_toFib y
  obtain ⟨σ', a', rfl⟩ := exists_toFib y'
  have e₁ := congrArg (· ≫ (fst (Over.mk x') Xo.univ.t.G).left) e'
  simp only [Category.assoc] at e₁
  rw [h.1, toFib_fst] at e e₁
  rw [toFib_fst] at e₁
  subst e₁ e
  have e₂ : ptMap h _ a = ptMap h _ a' := Over.OverMorphism.ext (by
    rw [← toFib_comp, ← toFib_comp, reassoc_of% e'])
  let j : Over.mk x ⟶ (Over.mk (𝟙 _ ≫ x) : Over Xo.X) := Over.homMk (𝟙 _) (by simp)
  refine ⟨⟨j ≫ (a' * a⁻¹), ?_⟩, ?_⟩
  · have e₃ : ptMap h _ (toPt x (fst (Over.mk x) Xo.univ.t.G).left ≫ j ≫ (a' * a⁻¹)) = 1 := by
      have e₄ : toPt x (fst (Over.mk x) Xo.univ.t.G).left ≫ j = HeckeFrCompare.res x _ (Category.comp_id _) :=
        Over.OverMorphism.ext (Category.comp_id _)
      refine Over.OverMorphism.ext ?_
      rw [← Category.assoc, e₄, ← MonObj.comp_one (HeckeFrCompare.res x' _ (Category.comp_id _))]
      refine (push_res Ψ _ _ _).trans (congrArg (_ ≫ ·) ?_)
      show (ptMap h _ _).left = _
      rw [map_mul, map_inv, e₂, mul_inv_cancel]
    rw [mem_transKer, ← Category.id_comp (translT _ _).left, ← toFib_taut, toFib_transl]
    refine gx_ext (by rw [Category.assoc, h.1, toFib_fst]) ?_
    rw [Category.assoc, toFib_comp h, map_mul, e₃, _root_.one_mul, ← toFib_comp, toFib_taut, Category.id_comp]
  · have e₅ : toPt x (𝟙 _) ≫ j = 𝟙 _ := Over.OverMorphism.ext (Category.comp_id _)
    rw [toFib_transl, reassoc_of% e₅, inv_mul_cancel_right]

omit [IsAlgClosed Ω] in

theorem mulT_props (x : Sp Ω ⟶ Xo.X) (hp : 1 ≤ p) : Etale (mulT Xo.univ.t.G (Over.mk x) p).left ∧
    QuasiCompact (mulT Xo.univ.t.G (Over.mk x) p).left ∧ Surjective (mulT Xo.univ.t.G (Over.mk x) p).left := by
  have := Xo.univ.t.semi.smooth
  have := Xo.univ.proper
  have hu : IsUnit ((p : ℕ) : Γ(Xo.X, ⊤)) := by
    have := ((baseKA l).unit p hp).map (Xo.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom)
    rwa [map_natCast] at this
  have he : Etale ((𝟙 Xo.univ.t.G) ^ p : Xo.univ.t.G ⟶ Xo.univ.t.G).left := GrpTangent.etale_id_pow Xo.univ.t.G hu
  have pb : IsPullback (snd (Over.mk x) Xo.univ.t.G) (mulT Xo.univ.t.G (Over.mk x) p) (𝟙 _ ^ p)
      (snd (Over.mk x) Xo.univ.t.G) := by
    refine ⟨⟨by simp [mulT, MonObj.comp_pow]⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst _ _) s.fst)
      (fun s => by simp) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
    · ext1
      · simp [mulT]
      · simpa [mulT, MonObj.comp_pow] using s.condition
    · ext1
      · simp [← h₂, mulT]
      · simp [← h₁]
  have : IsProper (fst (Over.mk x) Xo.univ.t.G).left := by
    show IsProper (pullback.fst x Xo.univ.t.G.hom)
    infer_instance
  have : QuasiCompact ((mulT Xo.univ.t.G (Over.mk x) p).left ≫ (fst (Over.mk x) Xo.univ.t.G).left) := by
    rw [(isPointed_mulT p).1]; infer_instance
  exact ⟨MorphismProperty.of_isPullback (P := @Etale) (pb.map (Over.forget _)) he,
    QuasiCompact.of_comp _ (fst (Over.mk x) Xo.univ.t.G).left,
    (EmbSpan.pt_pow_and_surjective abelianSchemeLaws_all.1 (GlobalTheory.UnivPol.pol Xo) x p hp).2⟩

omit [IsAlgClosed Ω] in

theorem isIntegral_gx (x : Sp Ω ⟶ Xo.X) : IsIntegral (Gx x) := by
  have hA := isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  exact pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral Ω x

theorem transl_quot (hp : 1 ≤ p)
    {g : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left,
      (mulT Xo.univ.t.G (Over.mk x) p).left ≫ (snd (Over.mk x) Xo.univ.t.G).left] ![1, -1])} (hg : g.IsGen)
    {c : Over.mk x ⟶ Xo.univ.t.G} (hc : c ∈ transKer _ Ψ) (z : Gx x) {J} (hJ : Good Xo.univ.t.PP.L z J)
    (v : (Over.mk x ⟶ Xo.univ.t.G) → ((Gx x).presheaf.stalk z)ˣ)
    (hv : ∀ b, v b = val g (translT Xo.univ.t.G b).left z J) :
    (∀ a, a ^ p = 1 → ∃ u, ∀ b, v (a * b * c) * (v (a * b))⁻¹ = u * (v (b * c) * (v b)⁻¹)) ∧
    ∀ b, (∀ a, a ^ p = 1 → v (a * b * c) * (v (a * b))⁻¹ = v (b * c) * (v b)⁻¹) → c ^ p = 1 := by
  have hU := Xo.univ.t.PP.isLB
  let φ : Fin 2 → (Gx x ⟶ Xo.univ.t.G.left) := ![(translPt _ (c ^ p)).left, (snd (Over.mk x) Xo.univ.t.G).left]
  let m : Gx x ⟶ Gx x := (mulT Xo.univ.t.G (Over.mk x) p).left
  have e : (translT _ c).left ≫ m ≫ (snd (Over.mk x) Xo.univ.t.G).left = m ≫ (translPt _ (c ^ p)).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, mulT, lift_snd, MonObj.comp_pow, translT, lift_snd,
      translPt_eq, translPt_eq, MonObj.comp_mul, lift_fst_assoc, lift_snd, mul_pow, MonObj.comp_pow]
  obtain ⟨D, hD, vD⟩ := exists_gen hU (φ' := fun k => m ≫ φ k) (ε' := fun k => -(![1, -1] : Fin 2 → ℤ) k)
    (fun V _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (Fin.prod_univ_two _) (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_two]
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, φ, reassoc_of% (mem_transKer.1 hc), ← e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, m]
      module)
    (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ g (translT _ c).left) (LB.invGen _ _ _ g))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hg _) (invGen_isGen _ _ _ _ hg))
  have tt : ∀ a b : Over.mk x ⟶ Xo.univ.t.G, (translT _ a).left ≫ (translT _ b).left = (translT _ (b * a)).left :=
    fun a b => by rw [translT_mul, Over.comp_left]
  have vD' : ∀ b, val D (translT _ b).left z J = v (b * c) * (v b)⁻¹ := fun b => by
    rw [vD _ _ z J hJ, val_mul hJ, val_pull hJ, val_inv, tt, hv, hv, mul_comm b]
  have hk : ∀ a : transKer Xo.univ.t.G m, ∀ i, (translT _ a.1).left ≫ m ≫ φ i = m ≫ φ i := fun a i =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) a.2)
  choose κ hκ using fun a => exists_transl_const hD (hk a)
  have hκ' : ∀ (a : transKer Xo.univ.t.G m) b, (v (a * b * c) * (v (a * b))⁻¹ * (v (b * c) * (v b)⁻¹)⁻¹).val =
      gs (fst (Over.mk x) Xo.univ.t.G).left z ⊤ (κ a) := fun a b => by
    have := hκ a _ (translT _ b).left z J hJ
    rwa [tt, vD', vD', ← Over.comp_left, translT, lift_fst] at this
  refine ⟨fun a ha => ⟨_, fun b => mul_inv_eq_iff_eq_mul.1 (Units.ext
    ((hκ' ⟨a, (mem_transKer_mulT p a).2 ha⟩ b).trans (hκ' ⟨a, (mem_transKer_mulT p a).2 ha⟩ 1).symm))⟩, fun b hb => ?_⟩
  have k₁ : ∀ a, κ a = 1 := fun a => by
    have := hκ' a b
    rw [hb _ ((mem_transKer_mulT p _).1 a.2), mul_inv_cancel, gs_eq _ _ ⊤ trivial] at this
    obtain ⟨t, ht⟩ := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.surjective (κ a)
    let ρ := (((Gx x).presheaf.germ ⊤ z trivial).hom.comp (fst (Over.mk x) Xo.univ.t.G).left.appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.toRingHom
    have h₁ : t = 1 := ρ.injective (by rw [map_one]; rw [← ht] at this; exact this.symm)
    rw [← ht, h₁, map_one]
  obtain ⟨i₁, i₂, i₃⟩ := mulT_props x hp
  have hiso := IsoDescent.lbIso_of_invariant hU hU (K := PEmpty) PEmpty.elim PEmpty.elim φ _ m
    (fun a : transKer Xo.univ.t.G m => (translT _ a.1).left) (fun a => a.2)
    (descends_ker (isLinHom_mulT x p)) _ (pullGen_isGen _ _ _ _ (AbLaw.Cube.oneGen_isGen (Y := Gx x)) m) D hD
    (fun a y I I' hI hI' => by
      rw [val_pull hI, val_pull hI, val_one, val_one]
      have := hκ a _ (𝟙 _) y I' hI'
      rw [k₁, gs_eq _ _ ⊤ trivial, map_one, map_one, Category.id_comp] at this
      rw [mul_inv_eq_one.1 (Units.ext this)])
  have h₀ := (cls_eq_iff (LB.isLB_linComb hU _ _) (LB.isLB_linComb hU _ _)).2 hiso
  rw [cls_linComb hU, cls_linComb hU, Fintype.sum_empty, eq_comm] at h₀
  simp only [neg_zsmul, Finset.sum_neg_distrib, neg_eq_zero] at h₀
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (LB.isLB_linComb hU φ ![1, -1])).1 (by rw [cls_linComb hU, h₀])
  exact Xo.univ.ktriv Ω x (c ^ p) fun q => ⟨⊤, trivial, gen_chartPull (Geo.Tor.chartPullPull _ _ _ rfl) t ht⟩

variable {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))} {s : LB.Sec (PPx x)}
  {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}

omit [IsAlgClosed Ω] in

theorem term_transl (h : IsLinHom Ψ) (hβ : β.IsGen) (hs : IsMulPull _ Xo.univ.t.PP p s s₁)
    (hst : ∀ a ∈ transKer _ Ψ, a ≫ Xo.univ.t.act.act H.w0 ∈ transKer _ Ψ) {Z : Scheme.{0}} (r : Z ⟶ Gx x) (z : Z)
    {J} (hJ : Good Xo.univ.t.PP.L z J) (a : Over.mk x ⟶ Xo.univ.t.G) (ha : a ∈ transKer _ Ψ) (hp : a ^ p = 1)
    (b : Over.mk x ⟶ Xo.univ.t.G) :
    ((val β (r ≫ (translT _ (a * b)).left) z J)⁻¹).val * sv _ Xo.univ.t.PP s₁ (r ≫ (translT _ (a * b)).left) z J =
      ((val β (r ≫ (translT _ b).left) z J)⁻¹).val * sv _ Xo.univ.t.PP s₁ (r ≫ (translT _ b).left) z J := by
  obtain ⟨α, hα, hc⟩ := hs.exists_isRigIso
  have := Xo.univ.t.act.hom H.w0
  have k := (mem_transKer_mulT p a).2 hp
  have e := quot_transl (isLinHom_mulT x p) h hα.2.1 hβ k ha ((mem_transKer_mulT p _).2 (by
    rw [← MonObj.pow_comp, hp, MonObj.one_comp])) (hst a ha) (r ≫ (translT _ b).left) z hJ
  rw [translT_mul, Over.comp_left, ← Category.assoc, hc.val _ z hJ, hc.val _ z hJ, Category.assoc _ _ (mulT _ _ _).left,
    mem_transKer.1 k, mul_left_comm, mul_left_comm (Units.val _), ← Units.val_mul, ← Units.val_mul, mul_comm _⁻¹, e,
    mul_comm _⁻¹]

theorem eq_zero_of_trace (hp : 1 ≤ p) (hβ : β.IsGen) (hs : IsMulPull _ Xo.univ.t.PP p s s₁) {n : ℕ}
    {c : Fin n → (Over.mk x ⟶ Xo.univ.t.G)} (hc : IsRepsModTors (transKer _ Ψ) p c)
    (h : ∀ (r : Gx x ⟶ Gx x) z J, Good Xo.univ.t.PP.L z J →
      ∑ i, ((val β (r ≫ (translT _ (c i)).left) z J)⁻¹).val *
        sv _ Xo.univ.t.PP s₁ (r ≫ (translT _ (c i)).left) z J = 0) (j) : s.f j = 0 := by
  obtain ⟨α, hα, hc'⟩ := hs.exists_isRigIso
  obtain ⟨g, hg, hv⟩ := exists_quotGen hα.2.1 hβ
  obtain ⟨i, -⟩ := hc.2 1 (Subgroup.one_mem _)
  have := isIntegral_gx x
  obtain ⟨-, -, i₃⟩ := mulT_props x hp
  let m : Gx x ⟶ Gx x := (mulT Xo.univ.t.G (Over.mk x) p).left
  have tt : ∀ a b : Over.mk x ⟶ Xo.univ.t.G, (translT _ a).left ≫ (translT _ b).left = (translT _ (a * b)).left :=
    fun a b => by rw [mul_comm, translT_mul, Over.comp_left]
  have : Surjective (translT _ (c i)).left := by
    have : Surjective ((translT _ (c i)⁻¹).left ≫ (translT _ (c i)).left) := by
      rw [tt, inv_mul_cancel, translT_one]; exact inferInstanceAs (Surjective (𝟙 _))
    exact Surjective.of_comp (translT _ (c i)⁻¹).left _
  have key : s = SecM.toSec _ 0 := by
    refine ThetaTraceTest.sec_eq_of_surjective (L := Xo.univ.t.PP) ((translT _ (c i)).left ≫ m) fun z J hJ => ?_
    let v := fun b : Over.mk x ⟶ Xo.univ.t.G => val g (translT Xo.univ.t.G b).left z J
    refine (eq_zero_of_chars (G := transKer Xo.univ.t.G m) (fun i a => v (a * c i) * (v a)⁻¹) (fun i a => ?_)
      (fun i j e => ?_) (fun i => sv _ Xo.univ.t.PP s ((translT _ (c i)).left ≫ m) z J) (fun a => ?_) i).trans ?_
    · obtain ⟨u, hu⟩ := (transl_quot hp hg (hc.1 i) z hJ v fun _ => rfl).1 a ((mem_transKer_mulT p _).1 a.2)
      exact ⟨u, fun b => hu b⟩
    · refine (hc.2 _ (hc.1 i)).unique (by simp) ((transl_quot hp hg ((transKer _ Ψ).mul_mem (hc.1 i)
        ((transKer _ Ψ).inv_mem (hc.1 j))) z hJ v fun _ => rfl).2 (c j) fun a ha => ?_)
      have e' := congrArg Additive.ofMul (e ⟨a, (mem_transKer_mulT p a).2 ha⟩)
      rw [_root_.mul_assoc a, mul_comm (c j), inv_mul_cancel_right]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, OneMemClass.coe_one, _root_.one_mul] at e' ⊢
      linear_combination (norm := abel) e'
    · have e := congrArg (((v a)⁻¹).val * ·) (h (translT _ a.1).left z J hJ)
      simp only [Finset.mul_sum, mul_zero] at e
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e
      have e₁ : (translT _ (a.1 * c i)).left ≫ m = (translT _ (c i)).left ≫ m := by
        rw [translT_mul, Over.comp_left, Category.assoc, mem_transKer.1 a.2]
      rw [tt, hc'.val _ z hJ, e₁]
      simp only [v, hv _ _ z J hJ, Units.val_mul]
      ring
    · exact ((gs_eq _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) _) _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _))).symm
  rw [key]; rfl

theorem exists_trace (h : IsLinHom Ψ) [Etale Ψ] [QuasiCompact Ψ] [Surjective Ψ] (hβ : β.IsGen)
    (hs : IsMulPull _ Xo.univ.t.PP p s s₁)
    (hst : ∀ a ∈ transKer _ Ψ, a ≫ Xo.univ.t.act.act H.w0 ∈ transKer _ Ψ) {n : ℕ}
    {c : Fin n → (Over.mk x ⟶ Xo.univ.t.G)} (hc : IsRepsModTors (transKer _ Ψ) p c) :
    ∃ s' : LB.Sec (PPx x'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J), Good Xo.univ.t.PP.L z J →
      sv _ Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ i, ((val β (r ≫ (translT _ (c i)).left) z J)⁻¹).val *
        sv _ Xo.univ.t.PP s₁ (r ≫ (translT _ (c i)).left) z J := by
  choose U hU' hU using fun i => exists_isDescLift hβ (hc.1 i)
  choose F hF using fun i => exists_isActOf (U i) s₁
  obtain rfl : c = fun i => (U i).pt := funext fun i => (hU' i).symm
  let t := SecM.toSec Xo.univ.t.G (∑ i, SecM.ofSec Xo.univ.t.G (F i))
  have ht : ∀ j, t.f j = ∑ i, (F i).f j := fun j => by
    show (∑ i, SecM.ofSec _ (F i) : SecM _ Xo.univ.t.PP.L _ _).1 j = _
    rw [Submodule.coe_sum, Finset.sum_apply]; rfl
  obtain ⟨u, hu⟩ := exists_sec Xo.univ.t.PP.isLB (φ' := fun _ : Fin 1 => Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left)
    (ε' := fun _ => 1) (fun V _ h => by
      refine (prod_sum₂ (K := Fin 1) (K' := Fin 2) (U := V) _ (Fin.prod_univ_one _)
        (prod_neg _ _ (prod_iso' h))).trans ?_
      rw [Fin.prod_univ_one]
      simp only [Sum.elim_inl, zpow_one, Category.id_comp, mul_inv, inv_inv, mul_inv_cancel_left])
    (pullMulSec (L := Xo.univ.t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
      (ε := fun _ => (p : ℤ) ^ 2) t (𝟙 _) (LB.invGen _ _ _ β) (invGen_isGen _ _ _ _ hβ))
  have hu' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J), Good Xo.univ.t.PP.L z J →
      sval u r z J = ∑ i, ((val β (r ≫ (translT _ (U i).pt).left) z J)⁻¹).val *
        sv _ Xo.univ.t.PP s₁ (r ≫ (translT _ (U i).pt).left) z J := fun Z r z J hJ => by
    refine (hu _ r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)
    rw [val_inv, Category.comp_id]
    refine (congrArg (· * _) (sv_sum ht r z hJ)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act_val (hF i) r z hJ, (hU i).val r z hJ, mul_right_comm, ← Units.val_mul, mul_right_comm, mul_inv_cancel,
      _root_.one_mul]
  obtain ⟨s', hs'⟩ := exists_sec_of_invariant Xo.univ.t.PP.isLB
    (fun _ : Fin 1 => (snd (Over.mk x') Xo.univ.t.G).left) (fun _ => 1) Ψ
    (fun a : transKer Xo.univ.t.G Ψ => (translT _ a.1).left) (fun a => a.2) (descends_ker h) u fun a y J hJ => by
      rw [hu' _ _ y J hJ, hu' _ _ y J hJ]
      have e := sum_reps_eq (reps_mul hc a.2) hc (fun b => ((val β (𝟙 _ ≫ (translT _ b).left) y J)⁻¹).val *
        sv _ Xo.univ.t.PP s₁ (𝟙 _ ≫ (translT _ b).left) y J) (term_transl h hβ hs hst (𝟙 _) y hJ)
      refine Eq.trans ?_ e
      simp only [translT_mul, Over.comp_left, Category.id_comp]
  exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (hu' Z r z J hJ)⟩

end Field

section Main

variable {c : Coeff l} {P : Ideal (𝓞 E)} {p i : ℕ} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X}
  {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} {Ψ : Gx x ⟶ Gx x'}

theorem existsUnique_trace (h : IsSplitOff l P p) (hC : Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C)
    (hΨ : IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.IsHeckeIsog p C Ψ) (s : LB.Sec (PPx x)) :
    (∃! s', IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s') ∧
      ∀ s', IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → (∀ j, s'.f j = 0) → ∀ j, s.f j = 0 := by
  obtain ⟨ψ, rfl⟩ := (conj x x').surjective Ψ
  obtain ⟨f, hf⟩ := (isog_iff ((Nat.Prime.coprime_iff_not_dvd h.2.2.1).2 h.2.2.2.2) _ _ _ _).2 hΨ
  obtain ⟨⟨a₁, a₂, a₃⟩, -⟩ := isHkIsog_etale_unique Xo h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hC hf
  have : Etale (conj x x' ψ) := by rw [conj_apply]; infer_instance
  have : QuasiCompact (conj x x' ψ) := by rw [conj_apply]; infer_instance
  have : Surjective (conj x x' ψ) := by rw [conj_apply]; infer_instance
  obtain rfl := transKer_of_isHkIsog hf
  have hst := fun a ha => hC.1 a ha H.w0
  have hA := isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  have hG := abelianSchemeLaws_all.1.globalFns
  refine ⟨?_, fun s' hs' h0 => ?_⟩
  · obtain ⟨β₀, h₀⟩ := exists_isoGen h.2.2.1 hf
    obtain ⟨β, hβ⟩ := RigIsoDescent.exists_isRigIso_of_gen (isPointed_of_isHkIsog hf) β₀ h₀
    obtain ⟨s₁, hs⟩ := exists_isMulPull p s
    have : Finite (transKer Xo.univ.t.G (conj x x' ψ)) :=
      Nat.finite_of_card_ne_zero (hC.2.2.2.2.1.trans_ne (pow_ne_zero _ h.2.2.1.ne_zero))
    obtain ⟨n, r, hr⟩ := exists_isRepsModTors (transKer Xo.univ.t.G (conj x x' ψ)) p
    obtain ⟨s', hs'⟩ := exists_trace hΨ.2.1 hβ.2.1 hs hst hr
    refine ⟨s', isThetaTrace_iff.2 ⟨β, s₁, n, r, hβ, hs, hr, hs'⟩, fun u hu => ?_⟩
    obtain ⟨β', s₂, n', r', hβ', hs₂, hr', hu'⟩ := isThetaTrace_iff.1 hu
    obtain rfl := hs.unique hG hA hs₂
    have := isIntegral_gx x'
    refine ThetaTraceTest.sec_eq_of_surjective (L := Xo.univ.t.PP) (conj x x' ψ) fun z J hJ => ?_
    rw [← Category.id_comp (conj x x' ψ), hu' _ _ z J hJ, hs' _ _ z J hJ]
    have e := sum_reps_eq hr' hr (fun b => ((val β (𝟙 _ ≫ (translT _ b).left) z J)⁻¹).val *
      sv _ Xo.univ.t.PP s₁ (𝟙 _ ≫ (translT _ b).left) z J) (term_transl hΨ.2.1 hβ.2.1 hs hst (𝟙 _) z hJ)
    refine Eq.trans ?_ e
    exact Finset.sum_congr rfl fun j _ => by rw [hβ'.val_unique hG hA hβ _ z hJ]
  · obtain ⟨β, s₁, n, r, hβ, hs, hr, hv⟩ := isThetaTrace_iff.1 hs'
    refine eq_zero_of_trace h.2.2.1.pos hβ.2.1 hs hr fun q z J hJ => (hv _ q z J hJ).symm.trans ?_
    exact (congrArg (gs _ z _) (h0 _)).trans ((gs_eq _ _ _
      (hJ.mem (fun _ : Fin 1 => (snd (Over.mk x') Xo.univ.t.G).left) _) _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _)))

omit [IsAlgClosed Ω] in

theorem isThGen_iff [Algebra c.F Ω] (hx : x ≫ Xo.s = sOf c Ω) (s : LB.Sec (PPx x)) :
    IsThGen x s ↔ ¬ ∀ j, s.f j = 0 := by
  have mul : ∀ (a b : Ω) j, scal x (a * b) j = scal x a j * scal x b j := fun a b j => by
    simp [Formalism.L2.Pj.scal, liftFun, toΓ]
  have zero : ∀ j, scal x 0 j = 0 := fun j => by simp [Formalism.L2.Pj.scal, liftFun, toΓ]
  refine ⟨fun h h0 => zero_ne_one ((h s).unique (y₁ := 0) (y₂ := 1) (fun j => by rw [h0, mul_zero])
    fun j => by rw [h0, mul_zero]), fun h u => ?_⟩
  obtain ⟨y, rfl⟩ := exists_frPt_local (c := c) abelianSchemeLaws_all.2.secTwist x hx
  obtain ⟨a, ha, -⟩ := y.gen s
  have a0 : a ≠ 0 := by
    rintro rfl
    exact h fun j => by rw [ha, zero, zero_mul]
  obtain ⟨b, hb, hu⟩ := y.gen u
  refine ⟨b * a⁻¹, fun j => by rw [ha, ← _root_.mul_assoc, ← mul, inv_mul_cancel_right₀ a0, hb], fun d hd => ?_⟩
  rw [← hu (d * a) fun j => by rw [hd, ha, mul, _root_.mul_assoc], mul_inv_cancel_right₀ a0]

theorem existsUnique_trace_isThGen [Algebra c.F Ω] (h : IsSplitOff l P p) (hx : x ≫ Xo.s = sOf c Ω)
    (hC : Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C) (hΨ : IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.IsHeckeIsog p C Ψ) {s : LB.Sec (PPx x)}
    (hs : IsThGen x s) : (∃! s', IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s') ∧
      ∀ s', IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → IsThGen x' s' :=
  ⟨(existsUnique_trace h hC hΨ s).1, fun s' hs' => (isThGen_iff (hΨ.1.trans hx) s').2 fun h0 =>
    (isThGen_iff hx s).1 hs ((existsUnique_trace h hC hΨ s).2 s' hs' h0)⟩

end Main

end Univ

theorem thetaTransportLaw : GlobalTheory.HeckePointLaw.ThetaTransportLaw := fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨fun _ _ _ _ _ _ _ _ _ hx hC hΨ hs =>
      have k := existsUnique_trace_isThGen h hx hC hΨ hs
      k.1.exists.imp fun s' hs' => ⟨k.2 s' hs', hs'⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ hx hC hΨ hs _ _ h₁ h₂ => (existsUnique_trace_isThGen h hx hC hΨ hs).1.unique h₁ h₂⟩

theorem heckePointLaws : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws :=
  GlobalTheory.HeckePointLaw.heckePointLaws_of_transport thetaTransportLaw

end GlobalTheory.ThetaTransport
