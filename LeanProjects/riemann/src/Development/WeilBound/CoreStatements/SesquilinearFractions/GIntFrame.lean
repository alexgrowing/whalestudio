import Development.WeilBound.CoreStatements.SesquilinearFractions.SpMapMonoOfFraction
import Development.WeilBound.CoreStatements.SesquilinearFractions.GModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

private theorem isTanAt_iff_epsScale_zero_comp_eq_one {R : Type} [CommRing R] {S : Scheme} (x : Sp R ⟶ S) (G : Over S) [GrpObj G]
    (v : epsAt x ⟶ G) : IsTanAt G x v ↔ LieTangent.epsScale x 0 ≫ v = 1 := by
  have one_left : ∀ (Y : Over S), (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hmul : Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    ext <;> simp [CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    apply RingHom.ext
    intro a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hsec : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id]
  unfold IsTanAt
  constructor
  · intro h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, one_left]
    change Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _
    rw [hmul, Category.assoc, h, one_left]
    simp [epsAt]
  · intro h
    rw [one_left]
    have h2 := congrArg Over.Hom.left h
    rw [Over.comp_left, one_left] at h2
    change Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _ at h2
    rw [hmul, Category.assoc] at h2
    have h3 := congrArg (fun q => Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ q) h2
    simp only [epsAt, Over.mk_hom, ← Category.assoc, hsec, Category.id_comp] at h3
    rw [h3]
    simp

open BaseChangeTangents in
theorem lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  intro E _ _ _ H D l Xo c K _ V _ _ _ y T tK m m' U _ _ M ρ σ I _ n r e uV u v hρ hσ huVt huVb hcorr hv hspan
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  let P : (epsAt (𝟙 (Sp V)) ⟶ T.G) → (epsAt (under y) ⟶ Xo.univ.t.G) :=
    fun w => BaseChangeTangents.push m.cart (BaseChangeTangents.bcTan (algebraMap V K) m'.cart w)
  have hP1 : P 1 = 1 := by
    simp only [P, BaseChangeTangents.bcTan_one]
    exact map_one (BaseChangeTangents.pushHom m.cart)
  have hPscale : ∀ (a : V) w, P (LieTangent.epsScale (𝟙 (Sp V)) a ≫ w) =
      LieTangent.epsScale (under y) (algebraMap V K a) ≫ P w := by
    intro a w
    simp only [P, BaseChangeTangents.bcTan_scale, BaseChangeTangents.push_scale]
  have hPcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)),
      P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod =
        (List.ofFn fun i => LieTangent.epsScale (under y) (algebraMap V K (cc i)) ≫ P (w i)).prod := by
    intro N cc w
    simp only [P, BaseChangeTangents.bcTan_comb, BaseChangeTangents.push_comb]
  have hPact : ∀ (a : 𝓞 E) w, P (w ≫ T.act.act a) = P w ≫ Xo.univ.t.act.act a := by
    intro a w
    simp only [P]
    rw [BaseChangeTangents.bcTan_act _ m'.cart (tK.act.act a) (T.act.act a) (m'.act a),
      BaseChangeTangents.push_act m.cart (tK.act.act a) (Xo.univ.t.act.act a) (m.act a)]
  have tprod : ∀ (L : List (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ w ∈ L, IsTanAt T.G (𝟙 (Sp V)) w) →
      IsTanAt T.G (𝟙 (Sp V)) L.prod := by
    intro L
    induction L with
    | nil =>
      intro _
      simpa using LieTangent.isTanAt_one
    | cons a L ih =>
      intro h
      rw [List.prod_cons]
      exact LieTangent.isTanAt_mul (h a (by simp)) (ih fun w hw => h w (by simp [hw]))
  have tcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)),
      (∀ k, IsTanAt T.G (𝟙 (Sp V)) (w k)) →
        IsTanAt T.G (𝟙 (Sp V)) (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod := by
    intro N cc w hw
    apply tprod
    intro z hz
    simp only [List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact LieTangent.isTanAt_scale _ (hw i)
  have hPinj : ∀ w w', IsTanAt T.G (𝟙 (Sp V)) w → IsTanAt T.G (𝟙 (Sp V)) w' → P w = P w' → w = w' := by
    intro w w' hw hw' h
    exact BaseChangeTangents.bcTan_inj _ m'.cart hinj hw hw' (BaseChangeTangents.push_inj m.cart h)
  have hM0 : M.pt 0 = 1 := by
    have h := M.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hMscale : ∀ (a : K) (z : U), M.pt (a • z) = LieTangent.epsScale (under y) a ≫ M.pt z := by
    intro a z
    apply Over.OverMorphism.ext
    rw [M.smul, Over.comp_left]
    rfl
  have hPu : ∀ k, P (uV k) = M.pt (u (e k)) := by
    intro k
    obtain ⟨s, hs1, hs2⟩ := hcorr k
    have hs := BaseChangeTangents.eq_bcTan_left (algebraMap V K) m'.cart rfl (uV k) s hs2
    apply Over.OverMorphism.ext
    simp only [P]
    rw [BaseChangeTangents.push_left, ← hs]
    exact hs1
  have hPsum : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (z : Fin N → U),
      (∀ k, P (w k) = M.pt (z k)) →
        P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod =
          M.pt (∑ i, algebraMap V K (cc i) • z i) := by
    intro N cc w z hwz
    rw [hPcomb]
    simp only [hwz]
    exact BaseChangeTangents.prod_pt M _ z
  have hsmul : ∀ (a : V) (z : U), a • z = algebraMap V K a • z := fun a z => (algebraMap_smul K a z).symm
  have hliV : LinearIndependent V u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let cc : Fin n → V := fun k => g (e k)
    have hsum : ∑ k, algebraMap V K (cc k) • u (e k) = 0 := by
      calc ∑ k, algebraMap V K (cc k) • u (e k) = ∑ k, g (e k) • u (e k) :=
            Finset.sum_congr rfl fun k _ => (hsmul _ _).symm
        _ = ∑ i, g i • u i := Equiv.sum_comp e (fun i => g i • u i)
        _ = 0 := hg
    have hcomb1 : P (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (cc k) ≫ uV k).prod = P 1 := by
      rw [hPsum cc uV (fun k => u (e k)) hPu]
      simp only [hsum, hM0, hP1]
    have heq1 := hPinj _ _ (tcomb cc uV huVt) LieTangent.isTanAt_one hcomb1
    obtain ⟨c0, _, huniq⟩ := huVb 1 LieTangent.isTanAt_one
    have hc1 : IsComb cc uV 1 := by
      rw [BaseChangeTangents.isComb_iff]
      exact heq1.symm
    have hc0 : IsComb (fun _ => (0 : V)) uV 1 := by
      rw [BaseChangeTangents.isComb_iff]
      have h0 : ∀ k, LieTangent.epsScale (𝟙 (Sp V)) (0 : V) ≫ uV k = 1 :=
        fun k => (isTanAt_iff_epsScale_zero_comp_eq_one _ _ _).mp (huVt k)
      simp only [h0, List.ofFn_const, List.prod_replicate, one_pow]
    have hcc := (huniq cc hc1).trans (huniq _ hc0).symm
    have hk := congrFun hcc (e.symm i)
    simpa [cc] using hk
  have hliK : LinearIndependent K u := LinearIndependent.localization K (nonZeroDivisors V) hliV
  refine ⟨hliK, ?_⟩
  let σV : 𝓞 E →+* V := (σ.comp (algebraMap (𝓞 E) E)).codRestrict V (fun a => hσ a)
  have hσV : ∀ a, algebraMap V K (σV a) = σ (a : E) := fun a => rfl
  have hvmem : ∀ a, v a ∈ Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V := by
    intro a
    rw [hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  choose d hd using fun a => (Submodule.mem_span_range_iff_exists_fun V).mp (hvmem a).1
  let vV : Fin r → (epsAt (𝟙 (Sp V)) ⟶ T.G) :=
    fun a => (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (d a (e k)) ≫ uV k).prod
  have hPv : ∀ a, P (vV a) = M.pt (v a) := by
    intro a
    rw [hPsum (fun k => d a (e k)) uV (fun k => u (e k)) hPu, ← hd a]
    congr 1
    rw [← Equiv.sum_comp e (fun i => d a i • u i)]
    exact Finset.sum_congr rfl fun k _ => (hsmul _ _).symm
  have hvVt : ∀ a, IsTanAt T.G (𝟙 (Sp V)) (vV a) := fun a => tcomb _ uV huVt
  have heig : ∀ w (z : U), IsTanAt T.G (𝟙 (Sp V)) w → P w = M.pt z →
      (IsEigVec T.act (𝟙 (Sp V)) σV w ↔ z ∈ HT.eigSp ρ σ) := by
    intro w z hw hwz
    have key : ∀ a : 𝓞 E, (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔
        ρ a z = σ (a : E) • z := by
      intro a
      have e1 : (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔
          w ≫ T.act.act a = LieTangent.epsScale (𝟙 (Sp V)) (σV a) ≫ w := by
        constructor
        · intro h
          apply Over.OverMorphism.ext
          rw [h, Over.comp_left]
          rfl
        · intro h
          rw [h, Over.comp_left]
          rfl
      rw [e1]
      haveI := T.act.hom a
      constructor
      · intro h
        have h2 := congrArg P h
        rw [hPact, hPscale, hwz, hσV] at h2
        apply M.inj
        rw [hMscale, ← h2]
        exact hρ a z
      · intro h
        apply hPinj _ _ (TransportLieModel.isTanAt_comp hw _) (LieTangent.isTanAt_scale _ hw)
        rw [hPact, hPscale, hwz, hσV, ← hMscale, ← h]
        exact (hρ a z).symm
    simp only [IsEigVec, hw, true_and, key]
    simp only [HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  refine ⟨σV, vV, ?_, ?_, ?_⟩
  · exact RingHom.ext fun a => rfl
  · refine ⟨?_, ?_⟩
    · intro a
      exact (heig (vV a) (v a) (hvVt a) (hPv a)).mpr ((Submodule.restrictScalars_mem _ _ _).mp (hvmem a).2)
    · intro w hw
      have hwt : IsTanAt T.G (𝟙 (Sp V)) w := hw.1
      obtain ⟨cc, hcc, _⟩ := huVb w hwt
      rw [BaseChangeTangents.isComb_iff] at hcc
      have hPw : P w = M.pt (∑ k, algebraMap V K (cc k) • u (e k)) := by
        rw [hcc]
        exact hPsum cc uV (fun k => u (e k)) hPu
      have hzE := (heig w _ hwt hPw).mp hw
      have hzU : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range u) := by
        apply Submodule.sum_mem
        intro k _
        rw [← hsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)
      have hzv : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range v) := by
        rw [← hspan]
        exact ⟨hzU, hzE⟩
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun V).mp hzv
      have hPg : P (List.ofFn fun a => LieTangent.epsScale (𝟙 (Sp V)) (g a) ≫ vV a).prod =
          M.pt (∑ k, algebraMap V K (cc k) • u (e k)) := by
        rw [hPsum g vV v hPv, ← hg]
        exact congrArg M.pt (Finset.sum_congr rfl fun a _ => (hsmul _ _).symm)
      refine ⟨g, ?_, ?_⟩
      · show Fl.IsComb g vV w
        rw [BaseChangeTangents.isComb_iff]
        exact hPinj _ _ hwt (tcomb g vV hvVt) (hPw.trans hPg.symm)
      · intro g' hg'
        change Fl.IsComb g' vV w at hg'
        rw [BaseChangeTangents.isComb_iff] at hg'
        have h1 : M.pt (∑ a, algebraMap V K (g' a) • v a) = M.pt (∑ a, algebraMap V K (g a) • v a) := by
          rw [← hPsum g' vV v hPv, ← hg', hPw, ← hg]
          exact congrArg M.pt (Finset.sum_congr rfl fun a _ => hsmul _ _)
        have h2 := M.inj h1
        funext a
        apply hinj
        have h3 := Fintype.linearIndependent_iff.mp hv (fun a => algebraMap V K (g' a) - algebraMap V K (g a))
          (by simp only [sub_smul, Finset.sum_sub_distrib, h2, sub_self]) a
        exact sub_eq_zero.mp h3
  · intro a
    refine ⟨(BaseChangeTangents.bcTan (algebraMap V K) m'.cart (vV a)).left, ?_, BaseChangeTangents.bcTan_left _ _ _⟩
    exact (BaseChangeTangents.push_left m.cart _).symm.trans (congrArg Over.Hom.left (hPv a))

end PositivityTheory.Xgf
