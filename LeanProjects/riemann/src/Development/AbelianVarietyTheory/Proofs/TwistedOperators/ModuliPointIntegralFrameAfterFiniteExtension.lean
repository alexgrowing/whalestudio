import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TateIsoExistsAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFrames
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrExtM
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.AnyLevelFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

open RationalTorsion in

theorem exists_obj_of_rational {B B₂ K Ω : Type} [CommRing B] [CommRing B₂] [Field K] [CharZero K] [Field Ω]
    [IsAlgClosed Ω] {b : Base l B} {b₂ : Base l₂ B₂} (b₀ : B →+* K) (j : B₂ →+* K) (σ : K →+* Ω)
    {s : Sp K ⟶ Sp B} (hs : s = spMap b₀) (o : Obj D l b s) (hA₂ : l₂.A = 1) (hρ : j b₂.ρ = b₀ b.ρ)
    (hrat : ∀ x : Over.mk (spMap σ) ⟶ o.t.G, x ^ l₂.M' = 1 → ∃ s : 𝟙_ (Over (Sp K)) ⟶ o.t.G, toUnit _ ≫ s = x) :
    ∃ o₂ : Obj D l₂ b₂ (spMap j), o₂.t = o.t := by
  subst hs
  let T : PAT H (Sp K) := ⟨o.t, ObjDim.isAbelianScheme o, _, ObjDim.smoothOfRelativeDimension o, ObjDim.sym,
    o.ample, o.ktriv⟩
  obtain ⟨-, I, -⟩ := o.geom Ω (spMap σ) _ (TorsionRat.sp_comp _ _)
  have hM : 0 < l₂.M := lt_of_lt_of_le (by norm_num) l₂.three_le
  have hA : 0 < l₂.A := l₂.A_pos
  have hsec : ∀ n : ℕ, 0 < n → n ∣ l₂.M' → ∀ a, ∃ s : 𝟙_ (Over (Sp K)) ⟶ o.t.G, toUnit _ ≫ s = I.ev n a := by
    rintro n hn ⟨m, hm⟩ a
    apply hrat
    rw [hm, pow_mul, (I.onto n hn _).2 ⟨a, rfl⟩, one_pow]
  choose sA hsA using hsec l₂.A hA (Nat.dvd_lcm_right _ _)
  choose sM hsM using hsec l₂.M hM (Nat.dvd_lcm_left _ _)
  obtain ⟨f, hf, e, he, hfe⟩ : ∃ f ∈ l₂.Mb, ∃ e ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), f + e = 1 :=
    Submodule.mem_sup.1 (by rw [l₂.coprime]; trivial)
  refine ⟨{
    t := o.t
    proper := o.proper
    ample := o.ample
    ktriv := o.ktriv
    eta := fun a => sM (e • a)
    eta_add := fun a c => section_ext (spMap σ) (by
      rw [MonObj.comp_mul, hsM, hsM, hsM, smul_add, I.add])
    eta_ker := fun a ha => section_ext (spMap σ) (by
      obtain ⟨c, hc⟩ := exists_eq_nsmul D l₂ (by rw [mul_comm]; exact l₂.prod) he ha
      rw [MonObj.comp_one, hsM]
      exact (I.ker _ hM _).2 ⟨c, hc⟩)
    etaA := sA
    etaA_add := fun a c => section_ext (spMap σ) (by
      rw [MonObj.comp_mul, hsA, hsA, hsA, I.add])
    etaA_ker := fun a => section_ext (spMap σ) (by
      rw [MonObj.comp_one, hsA]
      exact (I.ker _ hA _).2 ⟨a, rfl⟩)
    geom := ?_ }, rfl⟩
  intro k _ _ x β hx
  obtain ⟨ν, rfl⟩ : ∃ ν : K →+* k, x = spMap ν := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  have hβ : β = ν.comp j := by
    have h1 : spMap (ν.comp j) = spMap β := by
      rw [← hx, ← Spec.map_comp]; rfl
    have h2 := Spec.map_injective h1
    exact (congrArg CommRingCat.Hom.hom h2).symm
  subst hβ
  refine ⟨?_, ?_⟩
  · rw [RingHom.comp_apply, hρ]
    exact (o.geom k (spMap ν) _ (TorsionRat.sp_comp _ _)).1
  obtain ⟨i, hi⟩ := exists_algClosure_lift σ
  obtain ⟨i', hi'⟩ := exists_algClosure_lift ν
  obtain ⟨I', -, hev⟩ := cmTorsionIsometry_transport_geometricPoint abelianSchemeLaws_all.1 D T.pol (fun a => T.t.act.act a) T.t.act.hom i i'
    (spMap (algebraMap K (AlgebraicClosure K))) (spMap σ) (spMap ν)
    (by rw [← spMap_comp_eq, hi]) (by rw [← spMap_comp_eq, hi']) I
  refine ⟨I', ?_, fun a => hev _ a _ hA (hsA a), fun a ha => ?_⟩
  · have h1 := I'.ζ_prim 1 one_pos
    have h2 := b₂.ζ_prim
    rw [hA₂] at h2 ⊢
    rw [IsPrimitiveRoot.one_right_iff] at h1 h2
    rw [h1, h2, map_one, Units.val_one]
  obtain ⟨c, hc⟩ := exists_eq_nsmul D l₂ l₂.prod hf ha
  have h1 : a = e • a + l₂.M • c := by rw [← hc, ← add_smul, add_comm, hfe, one_smul]
  refine (hev _ (e • a) _ hM (hsM _)).trans ?_
  conv_rhs => rw [h1]
  exact (ev_add_smul I' hM _ _).symm

theorem exists_obj_level (c : Coeff l) (c₂ : Coeff l₂) (hle : c.F ≤ c₂.F) (hA : l₂.A = 1) {k : Type} [Field k]
    [CharZero k] (io : c.F →+* k) {s : Sp k ⟶ Sp (KA l)}
    (hs : s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom)) (o : Obj D l (baseKA l) s) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L) (j₂ : c₂.F →+* L)
      (o₂ : Obj D l₂ (baseKA l₂) (spMap (j₂.comp (IntermediateField.inclusion c₂.le).toRingHom))),
      Nonempty (SABMap o₂.t o.t (spMap (algebraMap k L))) := by
  have hM : 0 < l₂.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l₂.three_le) l₂.A_pos
  haveI := c₂.fin
  obtain ⟨F, _, _, _, _⟩ : ∃ (F : Type) (_ : Field F) (_ : Algebra k F), IsAlgClosed F ∧ Algebra.IsAlgebraic k F :=
    ⟨AlgebraicClosure k, inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap k F).injective
  obtain ⟨g, hg⟩ : ∃ g : c₂.F →+* F, ∀ a : c.F, g (IntermediateField.inclusion hle a) = algebraMap k F (io a) := by
    letI : Algebra c.F c₂.F := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    letI : Algebra c.F F := ((algebraMap k F).comp io).toAlgebra
    haveI : Algebra.IsAlgebraic c.F c₂.F := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
    let τ : c₂.F →ₐ[c.F] F := IsAlgClosed.lift
    exact ⟨τ, fun a => τ.commutes a⟩
  obtain ⟨T, hT, hT'⟩ := LevelRaise.exists_finite_set o hM (K := k) (F := F) (𝟙 _)
  obtain ⟨U, hU⟩ := (Module.Finite.fg_top (R := ℚ) (M := c₂.F))
  let T' : Set F := T ∪ g '' U
  haveI : Finite T' := (hT.union (U.finite_toSet.image g)).to_subtype
  let L := IntermediateField.adjoin k T'
  haveI : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hgL : ∀ a, g a ∈ L := fun a => by
    have hc : a ∈ Submodule.span ℚ (U : Set c₂.F) := hU ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul q x _ hx =>
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem L q) hx
  let j : c₂.F →+* L := g.codRestrict L hgL
  haveI : CharZero L := charZero_of_injective_ringHom (algebraMap k L).injective
  have hρ : (j.comp (IntermediateField.inclusion c₂.le).toRingHom) (baseKA l₂).ρ =
      ((algebraMap k L).comp (io.comp (IntermediateField.inclusion c.le).toRingHom)) (baseKA l).ρ := by
    have e : IntermediateField.inclusion c₂.le (baseKA l₂).ρ =
        IntermediateField.inclusion hle (IntermediateField.inclusion c.le (baseKA l).ρ) := Subtype.ext rfl
    apply (algebraMap L F).injective
    exact (congrArg g e).trans (hg _)
  obtain ⟨t', ⟨m⟩⟩ := exists_sab (spMap (algebraMap k L)) o.t
  have hrat : ∀ x : Over.mk (spMap (algebraMap L F)) ⟶ t'.G, x ^ l₂.M' = 1 →
      ∃ s : 𝟙_ (Over (Sp L)) ⟶ t'.G, toUnit _ ≫ s = x := by
    intro x hx
    let w := ObjPull.pushEquiv m.cart (Over.mk (spMap (algebraMap L F))) x
    have hw : ObjPull.pushEquiv m.cart (Over.mk (spMap (algebraMap L F))) x ^ l₂.M' = 1 := by rw [← map_pow, hx, map_one]
    have e : spMap (algebraMap k F) ≫ 𝟙 _ = spMap (algebraMap L F) ≫ spMap (algebraMap k L) := by
      rw [Category.comp_id, TorsionRat.sp_comp]
      rfl
    let g₂ : Over.mk (spMap (algebraMap k F) ≫ 𝟙 _) ⟶
        Over.mk (spMap (algebraMap L F) ≫ spMap (algebraMap k L)) := Over.homMk (𝟙 _) ((Category.id_comp _).trans e.symm)
    obtain ⟨q, hq⟩ := hT' L (Set.subset_union_left.trans (IntermediateField.subset_adjoin _ _)) (g₂ ≫ w)
      (by rw [← MonObj.comp_pow]; exact (congrArg (g₂ ≫ ·) hw).trans (MonObj.comp_one _))
    have hq₁ : q.left ≫ o.t.G.hom = 𝟙 _ ≫ spMap (algebraMap k L) :=
      (Over.w q).trans ((Category.comp_id _).trans (Category.id_comp _).symm)
    refine ⟨Over.homMk (m.cart.1.lift q.left (𝟙 _) hq₁) (m.cart.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [Over.comp_left, ObjPull.toUnit_left', Category.assoc]
      exact (congrArg (spMap (algebraMap L F) ≫ ·) (m.cart.1.lift_fst _ _ _)).trans
        (hq.trans (Category.id_comp _))
    · rw [Over.w, Over.w]
  obtain ⟨o₂, ho₂⟩ := exists_obj_of_rational (b₂ := baseKA l₂)
    ((algebraMap k L).comp (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (j.comp (IntermediateField.inclusion c₂.le).toRingHom) (algebraMap L F)
    (by rw [hs, TorsionRat.sp_comp]) (ModelCompare.objOfSABMap o m) hA
    hρ hrat
  exact ⟨L, inferInstance, inferInstance, inferInstance, j, o₂, ho₂ ▸ ⟨m⟩⟩

set_option maxHeartbeats 400000 in

theorem exists_intFr {Xo : Moduli D l} {c : Coeff l} (T : CDVR) (io : c.F →+* T.Fr) (x : Sp T.Fr ⟶ Xo.X)
    (hx : letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr))
    (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L)
    (hθ : ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = constFn G.G.hom _ a * θ.f i)
    (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L) (gr2 : RigIso m2 w2)
    (hcl : ∀ (j : G.PP.L.ι) (k : t'.PP.L.ι) (W : t'.G.left.Opens) (h₁ : W ≤ m2.φ ⁻¹ᵁ G.PP.L.U j)
      (h₂ : W ≤ (G.PP.L.pull m2.φ).U (fun _ => j) ⊓ t'.PP.L.U k),
      (m2.φ.appLE _ _ h₁).hom (θ.f j) =
        resG _ h₂ (w2.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ'.f k))
    (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : T.Fr, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ y : IntFr Xo c T io, (letI := io.toAlgebra; y.1.x = x) := by
  let _ := io.toAlgebra
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr)
    GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨ub, u, hub, htan, heig, hbas, -⟩ := lieFree Xo c T io G t' x m1 m2 hx y₀.u (h0 ▸ y₀.tan) y₀.eig (h0 ▸ y₀.basis)
  clear h0 y₀
  obtain ⟨w1, g1, r1, -⟩ := m1.lin
  have hw1 := (isGen_iff w1).1 g1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s1, hs1⟩ := thf_secUp hw1 hL hL' σ'
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t'.G.left := m1.cart.1.lift _ _ cond
  have hφ : h ≫ m1.φ = (snd (Over.mk x) A).left := m1.cart.1.lift_fst _ _ cond
  have hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left := m1.cart.1.lift_snd _ _ cond
  let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
  let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m1.φ m1.cart.1.w
  let g0 : t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) A).left = t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) A).left = m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  have uniq : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      g ≫ h = 𝟙 _ := fun g e₁ e₂ => m1.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
        (by rw [Category.assoc, hh, e₂, Category.id_comp])
  have hg0 : g0 ≫ h = 𝟙 _ := uniq g0 g0s g0f
  have h0g : h ≫ g0 = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      show h ≫ g0 ≫ (fst (Over.mk x) A).left = 𝟙 _ ≫ (fst (Over.mk x) A).left
      rw [g0f, hh, Category.id_comp]
    · rw [Category.assoc]
      show h ≫ g0 ≫ (snd (Over.mk x) A).left = 𝟙 _ ≫ (snd (Over.mk x) A).left
      rw [g0s, hφ, Category.id_comp]
  let s : LB.Sec (PPx x) := thfPull1 Xo.univ.t.PP.L h hφ s1
  have hsf : ∀ j : Fin 1 → Xo.univ.t.PP.L.ι, s.f j = (h.appLE _ _ (chart_le_pullback_open _ h hφ j)).hom (s1.f (fun _ => j 0)) :=
    fun j => rfl
  let θ2 := thfPull G.PP.L m2.φ θ
  have hI2 : IsoMaps w2 σ' θ2 := fun (i : PUnit → G.PP.L.ι) k => fn_ext fun y hy => by
    have h₁ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ m2.φ ⁻¹ᵁ G.PP.L.U (i PUnit.unit) :=
      inf_le_left.trans (LB.wchart_le G.PP.L _ i PUnit.unit)
    have h₂ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ (G.PP.L.pull m2.φ).U (fun _ => i PUnit.unit) ⊓ t'.PP.L.U k :=
      le_rfl
    have e := congrArg (gs (𝟙 _) y _) (hcl (i PUnit.unit) k _ h₁ h₂)
    refine (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      (((gs_appLE m2.φ _ _ h₁ (𝟙 _) y hy _).symm.trans e).trans ((gs_mul _ y _ hy _ _).trans ?_)))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_res _ y h₂ hy _).symm ((gs_res _ y _ hy _).trans (gs_res _ y _ hy _).symm)
  have hI1 : IsoMaps w1 σ' s1 := fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => by
    exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  have hgc : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      ∀ (j : PUnit → Xo.univ.t.PP.L.ι) (hj : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ hj).hom (s.f (fun _ => j PUnit.unit)) := fun g e₁ e₂ j hj => fn_ext fun y hy =>
    Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))
  have hgenS : ∀ s'' : LB.Sec (PPx x), ∃! a : T.Fr, ∀ i, s''.f i = scal x a i * s.f i := by
    intro s''
    have le : ∀ j, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j y hy =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) g0s).mpr hy
    let σ : ∀ j, Γ(t'.G.left, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j) := fun j => (g0.appLE _ _ (le j)).hom (s''.f (fun _ => j))
    have gP : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j, m1.φ (r z) ∈ Xo.univ.t.PP.L.U j →
        gs r z _ (σ j) = gs (r ≫ g0) z _ (s''.f (fun _ => j)) := fun Z r z j hz => gs_appLE g0 _ _ (le j) r z hz _
    obtain ⟨τ, hτ⟩ := sec_down hw1 hL hL' σ fun y j j' h₁ h₂ => by
      have m : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j h₁
      have m' : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j') := le j' h₂
      have gg : gm (𝟙 _ ≫ g0) y _ ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) A).left) (fun _ => 1) (𝟙 _ ≫ g0) y _ _ m m').trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, g0s, Category.id_comp])
      exact (gP _ (𝟙 _) y j h₁).trans ((gs_compat s'' (𝟙 _ ≫ g0) y m m').trans
        (congrArg₂ (· * ·) (congrArg Units.val gg) (gP _ (𝟙 _) y j' h₂).symm))
    obtain ⟨a, ha, hu⟩ := hgen τ
    refine ⟨a, fun (i : Fin 1 → Xo.univ.t.PP.L.ι) => ?_, fun a' ha' => hu a' ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
      refine fn_ext fun y hy => ?_
      have mφ : m1.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j :=
        (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j)
          (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m1.φ = (snd (Over.mk x) A).left)).mpr (Set.mem_iInter.1 hy 0)
      obtain ⟨k, hk⟩ := exists_chart hL' ((𝟙 _ ≫ h) y)
      have e1 : gs (𝟙 _) y _ (s''.f (fun _ => j)) =
          (gw w1 (𝟙 _ ≫ h) y j k).val * (cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a * gs (𝟙 _ ≫ h) y _ (σ'.f k)) := by
        have c1 : (𝟙 _ ≫ h) ≫ g0 = 𝟙 _ := by rw [Category.id_comp, h0g]
        refine (congrArg (fun q => gs q y _ (s''.f (fun _ => j))) c1).symm.trans ?_
        refine (gP _ (𝟙 _ ≫ h) y j mφ).symm.trans ((hτ _ (𝟙 _ ≫ h) y j k mφ hk).trans (congrArg _ ?_))
        rw [ha k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
      have e2 : gs (𝟙 _) y _ (s.f (fun _ => j)) = (gw w1 (𝟙 _ ≫ h) y j k).val * gs (𝟙 _ ≫ h) y _ (σ'.f k) :=
        (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _) y hy _).trans
          (hs1 _ (𝟙 _ ≫ h) y (fun _ => j) k (chart_le_pullback_open _ h hφ _ hy) hk)
      have e3 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a := by
        rw [show (𝟙 _ ≫ h) ≫ t'.G.hom = 𝟙 _ ≫ (fst (Over.mk x) A).left by rw [Category.assoc, hh]]
        exact gs_constFn (fst (Over.mk x) A).left _ (𝟙 _) y hy a
      exact e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))
    · intro k
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hL (m1.φ y)
      have c2 : (𝟙 _ ≫ g0) ≫ h = 𝟙 _ := by rw [Category.id_comp, hg0]
      have mg : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j hj
      have e1 := hτ _ (𝟙 _) y j k hj hy
      have e2 : gs (𝟙 _) y _ (σ j) =
          cst (𝟙 _ ≫ t'.G.hom) y a' * ((gw w1 (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) := by
        refine (gP _ (𝟙 _) y j hj).trans ?_
        rw [ha' (fun _ => j), gs_mul _ y _ mg]
        refine congrArg₂ (· * ·) ?_ ?_
        · exact (gs_constFn (fst (Over.mk x) A).left _ _ y mg a').trans (by rw [Category.assoc, g0f])
        · refine (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g0) y mg _).trans ?_
          rw [c2]
          exact hs1 _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy
      rw [gs_mul _ y _ hy, gs_constFn _ _ _ y hy]
      rw [e1, mul_left_comm] at e2
      exact (Units.mul_right_inj _).1 e2
  let y : FrPt Xo c T.Fr := ⟨x, hx, u, htan, heig, hbas, s, hgenS⟩
  exact ⟨⟨y, GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H D l Xo c T.Fr y, G, t', m1, m2,
    ⟨ub, hub⟩, θ, hθ, w1, w2, σ', s1, θ2, ⟨g1, r1⟩, gr2, hI1, hI2, fun j hj => rfl, hgc⟩, rfl⟩

theorem intFrExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → IntFrExt Xo c := by
  intro E _ _ _ H D l Xo c hpq T io hfin x hx
  have hC := ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨l₂, hA, hgood⟩ := GlobalTheory.GlobalModelGuards.exists_good_level H
  obtain ⟨c₂, hle⟩ := GlobalTheory.RaisedAmple.exists_coeff c l₂
  obtain ⟨X₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H D l₂ hpq
  obtain ⟨t₀, ⟨m₀⟩⟩ := exists_sab x Xo.univ.t
  obtain ⟨L, _, _, _, j₂, o₂, ⟨n₂⟩⟩ := exists_obj_level c c₂ hle hA io hx (ModelCompare.objOfSABMap Xo.univ m₀)
  obtain ⟨T', i, r, ψ, -, hr, hv, hψ, -, hfin'⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
  have hfin'' := hfin' hfin
  refine ⟨T', i, r, hr, hv, hfin'', ?_⟩
  obtain ⟨t₃, ⟨n₃⟩⟩ := exists_sab (spMap ψ.toRingHom) o₂.t
  let o₃ := ModelCompare.objOfSABMap o₂ n₃
  obtain ⟨x₂, ⟨hx₂, ⟨mu⟩⟩, -⟩ := X₂.rep _ _ inferInstance o₃
  let io₂ : c₂.F →+* T'.Fr := ψ.toRingHom.comp j₂
  have : Finite (IsLocalRing.ResidueField T'.V) := hfin''
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.Exist.exists_prime_mem_maximalIdeal_of_finite_residue T'.V
  obtain ⟨O, _, β, Y, hPI, b, hb⟩ := GlobalTheory.exists_model_pushInvertible_under_cdvr GlobalTheory.partI_closed
    GlobalTheory.Moduli.moduli_scheme_exists E H D l₂ X₂ c₂ hpq T' io₂ p hp hpm (hgood p hp)
  have hcond : x₂ ≫ X₂.s = spMap io₂ ≫ spMap (IntermediateField.inclusion c₂.le).toRingHom := by
    rw [hx₂, TorsionRat.sp_comp, TorsionRat.sp_comp]
  let z : Sp T'.Fr ⟶ X₂.XF c₂ := pullback.lift x₂ (spMap io₂) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io₂ := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x₂ := pullback.lift_fst _ _ _
  have hz : z ≫ Y.j ≫ Y.s = Out.jK T'.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, -⟩ := extPt Y T' b z hz
  obtain ⟨G, ⟨m⟩⟩ := exists_sab yt Y.t
  obtain ⟨t', m1, m2, -⟩ := genFibre X₂ c₂ hC T' io₂ O β Y yt z h1.symm hzs G m
  obtain ⟨θ, hθ, -, w2, σ', gr2, hcl, hgen⟩ := thetaCore_of hT E H D l₂ X₂ c₂ O β Y hPI T'.V yt z h1.symm G m t' m2
  have e₁ : z ≫ pullback.fst _ _ = 𝟙 _ ≫ x₂ := hzf.trans (Category.id_comp _).symm
  obtain ⟨a₁, -⟩ := sabCancel pullCubCancel E H _ _ _ X₂.univ.t t₃ t' x₂ (𝟙 _) mu.toSABMap (e₁ ▸ m1)
  obtain ⟨a₂, -⟩ := sabComp pullCubComp E H _ _ _ o₂.t t₃ t' _ _ n₃ a₁
  obtain ⟨a₃, -⟩ := sabComp pullCubComp E H _ _ _ t₀ o₂.t t' _ _ n₂ a₂
  obtain ⟨a₄, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t t₀ t' _ _ m₀ a₃
  have e₂ : ((𝟙 _ ≫ spMap ψ.toRingHom) ≫ spMap (algebraMap T.Fr L)) ≫ x = spMap i ≫ x := by
    rw [Category.id_comp, TorsionRat.sp_comp, show ψ.toRingHom.comp (algebraMap T.Fr L) = i from RingHom.ext hψ]
  refine exists_intFr T' (i.comp io) (spMap i ≫ x) ?_ G t' (e₂ ▸ a₄) m2 θ hθ w2 σ' gr2 hcl hgen
  rw [Category.assoc, hx, sOf, sOf, TorsionRat.sp_comp]

end GlobalTheory.AnyLevelFrame
