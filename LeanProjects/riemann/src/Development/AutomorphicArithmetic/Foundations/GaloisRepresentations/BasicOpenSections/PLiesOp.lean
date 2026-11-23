import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ gp fib IsWt)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.LiesOverOperations

private theorem unit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : IsUnit (m : k)) : IsUnit (m : Γ(X, ⊤)) := by
  have := h.map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

private theorem wt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : IsWt p (Wt.const Z 1) := by
  rw [← TranscendenceTraces.multBasic_holds.2.2 p]
  exact TranscendenceTraces.wtFlat_holds p

private theorem pq_comp (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

private theorem pq_id (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

section Geo
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

private theorem geo_fst {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

private theorem geo_snd {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

private theorem geo_pb {X Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of k)) (s : X ⟶ Y) :
    IsPullback (pullback.fst (s ≫ q) (sp (algebraMap k Ω))) (geomMap Ω (s ≫ q) s rfl) s
      (pullback.fst q (sp (algebraMap k Ω))) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q (sp (algebraMap k Ω))) (v₂₂ := q) (h₃₁ := sp (algebraMap k Ω)) ?_
    (geo_fst Ω _ _ _).symm (IsPullback.of_hasPullback q _)
  rw [geo_snd]
  exact IsPullback.of_hasPullback _ _

end Geo

private theorem card_fib {A B C D : Scheme.{0}} {a : A ⟶ C} {v : A ⟶ B} {u : C ⟶ D} {b : B ⟶ D}
    (h : IsPullback a v u b) {Ω : Type} [Field Ω] (x : gp Ω ⟶ B) : (fib v x).ncard = (fib u (x ≫ b)).ncard := by
  have himg : fib u (x ≫ b) = (fun z => z ≫ a) '' fib v x := by
    ext y
    constructor
    · intro hy
      have hy' : y ≫ u = x ≫ b := hy
      exact ⟨h.lift y x hy', h.lift_snd _ _ _, h.lift_fst _ _ _⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≫ v = x := hz
      change (z ≫ a) ≫ u = x ≫ b
      rw [Category.assoc, h.w, reassoc_of% hz']
  rw [himg, Set.ncard_image_of_injOn]
  intro z hz z' hz' hzz
  have e1 : z ≫ v = x := hz
  have e2 : z' ≫ v = x := hz'
  exact h.hom_ext hzz (e1.trans e2.symm)

private theorem gen_ext {O k Ω : Type} [CommRing O] [Field k] [Algebra O k] [Field Ω] [Algebra k Ω] {Y A : Scheme.{0}}
    (g : Y ⟶ Spec (CommRingCat.of O)) (a b : A ⟶ geom Ω (pullback.snd g (sp (algebraMap O k))))
    (h1 : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (h2 : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · have e : pullback.fst (pullback.snd g (sp (algebraMap O k))) (sp (algebraMap k Ω)) ≫ pullback.snd g (sp (algebraMap O k)) =
          pullback.snd _ _ ≫ sp (algebraMap k Ω) := pullback.condition
      rw [Category.assoc, Category.assoc, e, ← Category.assoc, h2, Category.assoc]
  · exact h2

end UpperTheory.Gal.Mod.LiesOverOperations

open UpperTheory.Gal.Mod.LiesOverOperations in
theorem UpperTheory.Gal.Mod.liesOp :
    HopOp → OpCover → LiesOp := by
  intro hHop hOC
  unfold LiesOp
  intro l _ p k L _ _ H θ O _ _ C Ω _ _ hl T g d m hF hLies c hBC
  obtain ⟨-, κ, h, hκt, hw⟩ := hLies
  obtain ⟨v, hvpb, hvf, hvb, hvw⟩ := hBC
  haveI := c.fin
  haveI : IsFinite (H.s g) := hF.1
  haveI : Etale (H.s g) := hF.2.1
  haveI : IsFinite (pullback.lift (H.s g) κ h) := hw.1
  let π := piG C Ω
  have hπs : π ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst H.q (sp (algebraMap k Ω)) ≫ C.π := by
    change geomMap Ω H.q (pullback.lift C.π H.q C.ov) (pullback.lift_snd _ _ _) ≫ _ ≫ _ = _
    rw [reassoc_of% (geo_fst Ω H.q (pullback.lift C.π H.q C.ov) (pullback.lift_snd _ _ _))]
    erw [pullback.lift_fst]
  have hπb : π ≫ pullback.snd _ _ = pullback.snd _ _ := geo_snd Ω _ _ _
  have P₁ := IsPullback.of_hasPullback c.p π
  have ha : (pullback.snd c.p π ≫ pullback.fst H.q (sp (algebraMap k Ω))) ≫ C.π = (pullback.fst c.p π ≫ v) ≫ T.p := by
    rw [Category.assoc, ← hπs, Category.assoc, hvpb.w, ← Category.assoc _ c.p, pullback.condition, Category.assoc]
  let a : pullback c.p π ⟶ pullback C.π T.p := pullback.lift _ _ ha
  have P₂ : IsPullback (a ≫ pullback.snd _ _) (pullback.snd c.p π) T.p (pullback.fst H.q (sp (algebraMap k Ω)) ≫ C.π) := by
    have := P₁.paste_horiz hvpb
    rw [hπs] at this
    rwa [show a ≫ pullback.snd _ _ = pullback.fst c.p π ≫ v from pullback.lift_snd _ _ _]
  have P₃ : IsPullback a (pullback.snd c.p π) (pullback.fst C.π T.p) (pullback.fst H.q (sp (algebraMap k Ω))) :=
    IsPullback.of_right P₂ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback C.π T.p).flip
  have hfY : pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ H.s g = H.sΩ Ω g ≫ pullback.fst _ _ :=
    (geo_fst Ω _ _ _).symm
  have hu : (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ pullback.lift (H.s g) κ h) ≫ pullback.fst C.π T.p =
      H.sΩ Ω g ≫ pullback.fst H.q (sp (algebraMap k Ω)) := by
    rw [Category.assoc, pullback.lift_fst, hfY]
  let u : geom Ω (H.s g ≫ H.q) ⟶ pullback c.p π := P₃.lift _ _ hu
  have hua : u ≫ a = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ pullback.lift (H.s g) κ h := P₃.lift_fst _ _ _
  have hus : u ≫ pullback.snd c.p π = H.sΩ Ω g := P₃.lift_snd _ _ _
  have P₄ : IsPullback (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω))) u (pullback.lift (H.s g) κ h) a := by
    refine IsPullback.of_bot ?_ hua.symm P₃
    rw [hus, pullback.lift_fst]
    exact geo_pb Ω H.q (H.s g)
  have hav : a ≫ pullback.snd _ _ = pullback.fst c.p π ≫ v := pullback.lift_snd _ _ _
  have hlS : IsUnit (l : Γ(H.geomZ Ω, ⊤)) := unit_nat (pullback.snd H.q _) l hl
  have hl₀ := unit_nat (pullback.snd (pullback.snd C.p (sp (algebraMap O k))) (sp (algebraMap k Ω))) l hl
  have hsF : IsFinite (H.sΩ Ω g) := MorphismProperty.of_isPullback (P := @IsFinite) (geo_pb Ω H.q (H.s g)) ‹_›
  have hsE : Etale (H.sΩ Ω g) := MorphismProperty.of_isPullback (P := @Etale) (geo_pb Ω H.q (H.s g)) ‹_›
  have hwt₁ : IsWt (pullback.snd c.p π) (Wt.const _ 1) := by
    have := TranscendenceTraces.all_holds.1.1 (pullback.fst c.p π) (pullback.snd c.p π) c.p π c.w P₁ c.wt
    rw [hvw] at this
    exact this
  let c₁ : TranscendenceTraces.Corr (H.geomZ Ω) (geom Ω (pullback.snd C.p (sp (algebraMap O k)))) :=
    ⟨pullback c.p π, pullback.snd _ _, pullback.fst _ _ ≫ c.f, Wt.const _ 1, inferInstance, hwt₁⟩
  let c₂ : TranscendenceTraces.Corr (H.geomZ Ω) (geom Ω (pullback.snd C.p (sp (algebraMap O k)))) :=
    ⟨geom Ω (H.s g ≫ H.q), H.sΩ Ω g, H.tΩ Ω g ≫ π, Wt.const _ 1, hsF, wt_one _⟩
  have huF : IsFinite u := MorphismProperty.of_isPullback (P := @IsFinite) P₄ ‹_›
  have e₁ : u ≫ pullback.fst c.p π ≫ v = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ κ := by
    rw [← hav, ← Category.assoc, hua, Category.assoc, pullback.lift_snd]
  have e₂ : u ≫ pullback.fst c.p π ≫ c.p = H.sΩ Ω g ≫ π := by
    rw [pullback.condition, ← Category.assoc, hus]
  have ht : H.tΩ Ω g ≫ pullback.fst H.q (sp (algebraMap k Ω)) = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ H.t g :=
    geo_fst Ω _ _ _
  have htb : H.tΩ Ω g ≫ pullback.snd H.q (sp (algebraMap k Ω)) = pullback.snd _ _ := geo_snd Ω _ _ _
  have hsb : H.sΩ Ω g ≫ pullback.snd H.q (sp (algebraMap k Ω)) = pullback.snd _ _ := geo_snd Ω _ _ _
  have huf : u ≫ c₁.f = c₂.f := by
    change u ≫ pullback.fst c.p π ≫ c.f = H.tΩ Ω g ≫ π
    apply gen_ext C.p
    · simp only [Category.assoc]
      rw [hvf, hπs, reassoc_of% e₁, hκt, reassoc_of% ht]
    · simp only [Category.assoc]
      rw [hvb, reassoc_of% e₂, hπb, hsb, htb]
  have hcnt : ∀ (Ω' : Type) [Field Ω'] [IsAlgClosed Ω'] (x : gp Ω' ⟶ c₁.Z), (fib u x).ncard = m := by
    intro Ω' _ _ x
    rw [card_fib P₄ x]
    exact (Nat.card_coe_set_eq _).symm.trans (hw.2.2 Ω' (x ≫ a))
  have hcov : ∀ n : ℤ, c₂.opQ l n 0 = (m : ℚ_[l]) • c₁.opQ l n 0 := fun n =>
    @hOC l _ _ _ c₂ c₁ u huF m rfl rfl hus huf hlS hcnt n 0
  have hbc : ∀ n : ℤ, pullHQ l (sch.map π) n 0 ∘ₗ c.opQ l n 0 = c₁.opQ l n 0 := fun n => by
    have := TranscendenceTraces.adic.2.2.2.2.2.2.1 l n 0 c₁ c π (𝟙 _) (pullback.fst c.p π) P₁ (Category.comp_id _)
      (by rw [hvw]; rfl) hl₀
    rw [this, CategoryTheory.Functor.map_id, pq_id]
    rfl
  have key : ∀ (n : ℤ) x, trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 (pullHQ l (sch.map (H.tΩ Ω g)) n 0 (pullHQ l (sch.map π) n 0 x)) =
      (m : ℚ_[l]) • pullHQ l (sch.map π) n 0 (c.opQ l n 0 x) := fun n x => by
    have h₁ := LinearMap.congr_fun (hcov n) x
    have h₂ := LinearMap.congr_fun (hbc n) x
    rw [LinearMap.comp_apply] at h₂
    rw [h₂, LinearMap.smul_apply] at *
    rw [← h₁]
    change _ = trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 (pullHQ l (sch.map (H.tΩ Ω g ≫ π)) n 0 x)
    rw [Functor.map_comp, pq_comp]
    rfl
  rw [hHop l k H Ω hl g d hF]
  refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => ?_
  unfold pullTot
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, DirectSum.lmap_lof]
  rw [key n x, map_smul]
