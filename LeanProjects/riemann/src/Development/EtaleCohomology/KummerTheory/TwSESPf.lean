import Development.EtaleCohomology.KummerTheory.BockCut

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwSESPf
open LateralTheory.KummerTheory.BockCut

theorem smap_add {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f + g) x = Sec.map f x + Sec.map g x := by
  show ((f+g).hom.app (op U)).hom x = (f.hom.app (op U)).hom x + (g.hom.app (op U)).hom x
  simp

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := by
  show ((0 : F ⟶ G).hom.app (op U)).hom x = 0
  simp

theorem smap_nsmul {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) (n : ℕ) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (n • f) x = n • Sec.map f x := by
  induction n with
  | zero => simp [smap_zero]
  | succ n ih => rw [succ_nsmul, smap_add, ih, succ_nsmul]

theorem smap_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem smap_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (𝟙 F) x = x := rfl

theorem sres_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem smap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem tz_kill (q : ℕ) (i : ℤ) {U : Scheme.{0}} (y : Sec (TZ q i) U) : q • y = 0 := by
  change q • (show ((tw q i).obj.obj (op U) : ModuleCat (ULift (ZMod q))) from y) = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift (ZMod q))]
  have : ((q : ℕ) : ULift (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

theorem TwSES_of (hEpi : RedEpi) (hKer : RedKer) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hEx : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : TwSES := by
  intro l _ b a i π₁ π₂ h₁ h₂
  have : NeZero (l ^ (b + a)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : Epi π₁ := hEpi l (b + a) a (by omega) i π₁ h₁
  have : Epi π₂ := hEpi l (b + a) b (by omega) i π₂ h₂
  have hm1 : l ^ (b + a) = l ^ b * l ^ a := pow_add _ _ _
  have hm2 : l ^ (b + a) = l ^ a * l ^ b := by rw [pow_add, mul_comm]
  have hk : kernel.ι π₁ ≫ (l ^ b • 𝟙 _) = 0 := by
    refine ((hME ℤ (kernel.ι π₁ ≫ (l ^ b • 𝟙 _))).2.2.2 0 fun U x => ?_)
    rw [smap_zero, smap_comp, smap_nsmul, smap_id]
    exact ((hKer _ _ _ hm1 i π₁ h₁ U _).1).1 (by rw [← smap_comp, kernel.condition, smap_zero])
  let ι := Abelian.epiDesc π₁ (l ^ b • 𝟙 _) hk
  have hι : π₁ ≫ ι = l ^ b • 𝟙 _ := Abelian.comp_epiDesc _ _ _
  have hιs : ∀ {U : Scheme.{0}} (y : Sec (TZ (l ^ (b + a)) i) U), Sec.map ι (Sec.map π₁ y) = l ^ b • y := by
    intro U y; rw [← smap_comp, hι, smap_nsmul, smap_id]
  have w : ι ≫ π₂ = 0 := by
    rw [← cancel_epi π₁, ← Category.assoc, hι, comp_zero]
    refine ((hME ℤ _).2.2.2 0 fun U y => ?_)
    rw [smap_zero, smap_comp, smap_nsmul, smap_id]
    refine ((hKer _ _ _ hm2 i π₂ h₂ U _).1).2 ?_
    rw [smul_smul, ← hm2]; exact tz_kill _ _ _
  refine ⟨ι, hι, w, ?_⟩
  have : Mono ι := by
    refine (hME ℤ ι).2.1.2 fun U x hx => ?_
    refine hL.2.1 _ _ _ ((hME ℤ π₁).2.2.1.1 ‹_› U x) fun V g ⟨y, hy⟩ => ?_
    rw [← hy]
    refine ((hKer _ _ _ hm1 i π₁ h₁ V y).1).2 ?_
    rw [← hιs, hy, smap_res, hx, sres_zero]
  refine ShortComplex.ShortExact.mk' ?_ ‹Mono ι› ‹Epi π₂›
  refine (hEx ℤ _).2 fun U y hy => ?_
  refine hL.2.1 _ _ _ ((hKer _ _ _ hm2 i π₂ h₂ U y).2 hy) fun V g ⟨x, hx⟩ => ⟨Sec.map π₁ x, ?_⟩
  show Sec.map ι (Sec.map π₁ x) = _
  rw [hιs, hx]

end LateralTheory.KummerTheory.TwSESPf
