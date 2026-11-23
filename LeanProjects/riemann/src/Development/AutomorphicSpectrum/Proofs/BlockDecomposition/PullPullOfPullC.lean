import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import BuildAid.D3

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FEquiProof

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pull_pull_of_pullC {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {C₀ C₁ C₂ C₃ : Type 1} [Category.{0} C₀] [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃]
    {F₀ : C₀ ⥤ ModuleCat.{0} R₀} {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃}
    {a : R₀ →+* R₁} {b : R₁ →+* R₃} {c : R₀ →+* R₂} {e : R₂ →+* R₃}
    (m₁ : Mor F₀ F₁ a) (m₂ : Mor F₁ F₃ b) (m₃ : Mor F₀ F₂ c) (m₄ : Mor F₂ F₃ e) (j : ℕ)
    (h : ∀ z : Cn F₀ j, m₂.pullC j (m₁.pullC j z) = m₄.pullC j (m₃.pullC j z)) (x : H F₀ j) :
    m₂.pull j (m₁.pull j x) = m₄.pull j (m₃.pull j x) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((cx F₃).B j).submoduleOf ((cx F₃).Z j))) (Subtype.ext (h z))

theorem twUg_sharp (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (e : (PAlg.tw σ A).A) :
    twUg σ A (algebraMap (PAlg.tw σ A).U (PAlg.tw σ A).Ug ((PAlg.tw σ A).sharp e)) =
      algebraMap A.U A.Ug (A.sharp (PAlg.twId σ A e)) := by
  rw [twUg_algebraMap]
  refine congrArg (algebraMap A.U A.Ug) ?_
  change PAlg.twU σ A ((PAlg.tw σ A).th (WittVector.teichmuller l e)) = A.th (WittVector.teichmuller l (PAlg.twId σ A e))
  rw [PAlg.twU_th, WittVector.map_teichmuller]

theorem twAcr_lcA (hN : LcNat) (H : RIn l) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU (PAlg.tw σ A)) (ZMod (l ^ n))) :
    PAlg.twAcr σ A n (lcA (PAlg.tw σ A) n f) =
      lcA A n (lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (twUg σ A))) f) :=
  (hN l H _ (hA.tw σ) n).1 A hA (PAlg.twId σ A) (PAlg.pdOk_twId σ A) (twUg σ A) (fun e _ => twUg_sharp σ A e) f

theorem lcRes_sq {q : ℕ} {A B C D : Scheme.{0}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (e : a ≫ b = c ≫ d)
    (x : LocallyConstant D (ZMod q)) : lcRes q a (lcRes q b x) = lcRes q c (lcRes q d x) := by
  ext v
  have e' : b (a v) = d (c v) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact congrArg x e'

abbrev pM (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) : Probe (El M.P) (l ^ n) :=
  probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

abbrev tM (M : Model l K) (σ : Gal(PadicAlgCl l/K)) : El M.P ⥤ El M.P :=
  elTw σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ))

def gM (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) (c : El M.P) :
    (pM H r M n).U c ⟶ (pM H r M n).U ((tM M σ).obj c) :=
  Spec.map (CommRingCat.ofHom (twUg σ c.1.obj))

theorem gM_sq (hT : TwUg) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) {c c' : El M.P}
    (φ : c ⟶ c') : gM H r M σ n c' ≫ ((pM H r M n).S.map ((tM M σ).map φ)).unop =
      ((pM H r M n).S.map φ).unop ≫ gM H r M σ n c := by
  change Spec.map (CommRingCat.ofHom (twUg σ c'.1.obj)) ≫
      Spec.map (CommRingCat.ofHom (PAlg.mapUg (PAlg.twMap σ φ.1.hom))) =
    Spec.map (CommRingCat.ofHom (PAlg.mapUg φ.1.hom)) ≫ Spec.map (CommRingCat.ofHom (twUg σ c.1.obj))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) ((hT l K σ).1 _ _ φ.1.hom)

def twMor (hT : TwUg) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    Mor (pM H r M n).L (pM H r M n).L (RingHom.id ℤ) where
  G := tM M σ
  τ c := (lcRes (l ^ n) (gM H r M σ n c)).toAddMonoidHom.toIntLinearMap
  nat {c c'} φ x := by
    have e := gM_sq hT H r M σ n φ
    change lcRes (l ^ n) (gM H r M σ n c') (lcRes (l ^ n) ((pM H r M n).S.map ((tM M σ).map φ)).unop x) =
      lcRes (l ^ n) ((pM H r M n).S.map φ).unop (lcRes (l ^ n) (gM H r M σ n c) x)
    exact lcRes_sq e x

def lM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (pM H r M n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

abbrev gaM (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : Mor (modF (AcrEl M.P n)) (modF (AcrEl M.P n)) (ACris.galCris σ) :=
  galMor σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ)) n

theorem lM_pullC_twMor (hT : TwUg) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (z : Cn (pM H r M n).L j) :
    (lM hN H r M n).pullC j ((twMor hT H r M σ n).pullC j z) = (gaM M σ n).pullC j ((lM hN H r M n).pullC j z) := by
  funext s
  have hA := (s.obj (Fin.last j)).1.property
  let f : LocallyConstant (SU (PAlg.tw σ (s.obj (Fin.last j)).1.obj)) (ZMod (l ^ n)) := z (s ⋙ tM M σ)
  exact (twAcr_lcA hN H σ (s.obj (Fin.last j)).1.obj hA n f).symm

theorem lM_pull_twMor (hT : TwUg) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (x : CH.H (pM H r M n).L j) :
    (lM hN H r M n).pull j ((twMor hT H r M σ n).pull j x) = (gaM M σ n).pull j ((lM hN H r M n).pull j x) :=
  pull_pull_of_pullC (twMor hT H r M σ n) (lM hN H r M n) (lM hN H r M n) (gaM M σ n) j
    (lM_pullC_twMor hT hN H r M σ n j) x

theorem key (hE : CrystallineSemistableComparison.E.EtNat) (hT : CrystallineSemistableComparison.E.TwUg) (E : EtIn) (H : RIn l) (r : Roots l) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    (twMor hT H r M σ n).pull j ((pts H r M (𝟭 _) n).et 0 j x) =
      (pts H r M (𝟭 _) n).et 0 j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) :=
  hE E.gen (l ^ n) (El M.P) (El M.P) (pM H r M n) (pM H r M n) (gb M) (gb M)
    (pts H r M (𝟭 _) n) (pts H r M (𝟭 _) n) (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ) (twMor hT H r M σ n)
    (gM H r M σ n) (fun φ => gM_sq hT H r M σ n φ) (fun c f => rfl)
    (fun c => (hT l K σ).2.2 M c.1.obj c.2) 0 (Or.inl rfl) j x

theorem eM_apply (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    eM hN H r M n 0 j x = (lM hN H r M n).pull j ((pts H r M (𝟭 _) n).et 0 j x) := rfl

theorem galMH_apply (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) (y : M.MH n j) :
    M.galMH σ n j y = (gaM M σ n).pull j y := rfl

theorem equi_at (hE : CrystallineSemistableComparison.E.EtNat) (hT : CrystallineSemistableComparison.E.TwUg) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0) :
    eM hN H r M n 0 j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) = M.galMH σ n j (eM hN H r M n 0 j x) :=
  (eM_apply hN H r M n j _).trans ((congrArg ((lM hN H r M n).pull j) (key hE hT E H r M σ n j x).symm).trans
    ((lM_pull_twMor hT hN H r M σ n j _).trans ((congrArg ((gaM M σ n).pull j) (eM_apply hN H r M n j x).symm).trans
      (galMH_apply M σ n j _).symm)))

theorem fEqui : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.TwUg → CrystallineSemistableComparison.E.FEqui :=
  fun hE hT E hN l _ H r K M n j σ x => equi_at hE hT E hN H r M σ n j x

end GlobalTheory.CompanionTheory.FEquiProof
