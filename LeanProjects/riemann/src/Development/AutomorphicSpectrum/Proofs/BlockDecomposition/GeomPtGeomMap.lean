import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import BuildAid.D3
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FNatProof

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem geomPt_geomMap {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (A : PAlg l) (y : M.P.obj A) :
    geomPt M A y ≫ GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) =
      geomPt N A ((pxMap (okToOC l K) u hu).app A y) := by
  refine gb_ext N ?_ ?_
  · have e1 : GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) ≫
        pullback.fst _ _ ≫ pullback.fst _ _ = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ u := by
      rw [GlobalTheory.Et.geomMap, pullback.lift_fst_assoc, Category.assoc, Model.genMap, pullback.lift_fst, Category.assoc]
    rw [Category.assoc, e1, geomPt_fst, ← Category.assoc, geomPt_fst, Category.assoc]
    rfl
  · rw [Category.assoc, GlobalTheory.Et.geomMap, pullback.lift_snd, geomPt_snd, geomPt_snd]

def lcPull (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) :
    Mor (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).L (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L
      (RingHom.id ℤ) where
  G := elMap (pxMap (okToOC l K) u hu)
  τ _ := LinearMap.id
  nat _ _ := rfl

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem eM_eq (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) (j : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) j i) :
    eM hN H r M n i j x = (lcM hN H r M n).pull j ((pts H r M (𝟭 _) n).et i j x) := rfl

theorem cls_surj {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (n : ℕ) (h : CH.H F n) :
    ∃ (z : Cn F n) (hz : d F n z = 0), (cx F).cls z hz = h := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  exact ⟨z, hz, rfl⟩

theorem pull_square {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
    {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄}
    {σ₁₂ : R₁ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₁₃ : R₁ →+* R₃} {σ₃₄ : R₃ →+* R₄}
    (a : Mor F₁ F₂ σ₁₂) (b : Mor F₂ F₄ σ₂₄) (c : Mor F₁ F₃ σ₁₃) (e : Mor F₃ F₄ σ₃₄) (j : ℕ)
    (h : ∀ z : Cn F₁ j, b.pullC j (a.pullC j z) = e.pullC j (c.pullC j z)) (x : CH.H F₁ j) :
    b.pull j (a.pull j x) = e.pull j (c.pull j x) := by
  obtain ⟨z, hz, rfl⟩ := cls_surj F₁ j x
  change (cx F₄).cls (b.pullC j (a.pullC j z)) _ = (cx F₄).cls (e.pullC j (c.pullC j z)) _
  simp only [h]

theorem square (hN : LcNat) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ)
    (h : CH.H (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).L j) :
    (lcM hN H r M n).pull j ((lcPull H r u hu n).pull j h) =
      Model.pullMH u hu n j ((lcM hN H r N n).pull j h) :=
  pull_square (lcPull H r u hu n) (lcM hN H r M n) (lcM hN H r N n) (pullMor (pxMap (okToOC l K) u hu) n) j
    (fun z => funext fun s => rfl) h

theorem lcRes_id (q : ℕ) {U : Scheme.{0}} (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext v
  rfl

def gId (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P) :
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).U c ⟶
      (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).U ((lcPull H r u hu n).G.obj c) :=
  𝟙 (Spec (CommRingCat.of c.1.obj.Ug))

theorem gId_nat (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ)
    {c c' : El M.P} (φ : c ⟶ c') :
    gId H r u hu n c' ≫ ((probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).S.map ((lcPull H r u hu n).G.map φ)).unop =
      ((probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S.map φ).unop ≫ gId H r u hu n c :=
  (Category.id_comp _).trans (Category.comp_id _).symm

theorem gId_lc (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P)
    (f : LocallyConstant ((probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).U ((lcPull H r u hu n).G.obj c)) (ZMod (l ^ n))) :
    (lcPull H r u hu n).τ c f = lcRes (l ^ n) (gId H r u hu n c) f :=
  (lcRes_id _ f).symm

theorem gId_pts (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P) :
    (pts H r M (𝟭 _) n).y c ≫ GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) =
      gId H r u hu n c ≫ (pts H r N (𝟭 _) n).y ((lcPull H r u hu n).G.obj c) :=
  (geomPt_geomMap u hu c.1.obj c.2).trans (Category.id_comp _).symm

theorem key (hE : CrystallineSemistableComparison.E.EtNat) (hG : InGen) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X)
    (hu : u ≫ N.p = M.p) (n : ℕ) [NeZero (l ^ n)] (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0) :
    (lcPull H r u hu n).pull j ((pts H r N (𝟭 _) n).et 0 j x) =
      (pts H r M (𝟭 _) n).et 0 j
        (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) :=
  hE hG (l ^ n) (El N.P) (El M.P) (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n)
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb N) (gb M) (pts H r N (𝟭 _) n) (pts H r M (𝟭 _) n)
    (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu)) (lcPull H r u hu n)
    (gId H r u hu n) (gId_nat H r u hu n) (gId_lc H r u hu n) (gId_pts H r u hu n) 0 (Or.inl rfl) j x

theorem nat_step (hE : CrystallineSemistableComparison.E.EtNat) (hG : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X)
    (hu : u ≫ N.p = M.p) (n : ℕ) [NeZero (l ^ n)] (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0) :
    eM hN H r M n 0 j
        (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) =
      Model.pullMH u hu n j (eM hN H r N n 0 j x) :=
  (congrArg ((lcM hN H r M n).pull j) (key hE hG H r u hu n j x).symm).trans (square hN H r u hu n j _)

theorem fNat : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.FNat := by
  intro hE E hN l _ H r K M N u hu n j x
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact nat_step hE E.gen hN H r u hu n j x

end GlobalTheory.CompanionTheory.FNatProof

end
