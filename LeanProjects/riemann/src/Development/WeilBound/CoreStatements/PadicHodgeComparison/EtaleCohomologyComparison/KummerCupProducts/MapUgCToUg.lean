import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.E

open CH GlobalTheory.EtC

variable {l : ℕ} [Fact l.Prime]

abbrev SU (A : PAlg l) : Scheme.{0} := Spec (CommRingCat.of A.Ug)

def toΓ (B : Type) [CommRing B] : B →+* Γ(Spec (CommRingCat.of B), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

theorem toΓ_nat {B B' : Type} [CommRing B] [CommRing B'] (g : B →+* B') (x : B) :
    (Spec.map (CommRingCat.ofHom g)).appTop.hom (toΓ B x) = toΓ B' (g x) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)) x).symm

def kb (A : PAlg l) : PadicAlgCl l →+* A.Ug := A.cToUg.comp (clToC l)

theorem mapUg_cToUg {A B : PAlg l} (f : A ⟶ B) (x : ℂ_[l]) : PAlg.mapUg f (A.cToUg x) = B.cToUg x := by
  have h : ((PAlg.mapUg f).comp A.cToUg).comp
        ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) =
      B.cToUg.comp ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : OC l)) (RingHom.ext fun y => ?_)
    have e : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y) = (y : ℂ_[l]) :=
      (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).commutes y
    change PAlg.mapUg f (A.cToUg ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y))) =
      B.cToUg ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y))
    rw [e, PAlg.cToUg_coe, PAlg.cToUg_coe, PAlg.mapUg_algebraMap, PAlg.mapU_oC]
  obtain ⟨y, rfl⟩ := (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).surjective x
  exact RingHom.congr_fun h y

theorem mapUg_kb {A B : PAlg l} (f : A ⟶ B) : (PAlg.mapUg f).comp (kb A) = kb B := RingHom.ext fun x => mapUg_cToUg f _

variable (l) in

structure Roots where
  ρ : ∀ n, Prim (l ^ n) (PadicAlgCl l)
  hρ : ∀ n, clToC l (ρ n).1 = rootSeq l n

def Roots.zeta (r : Roots l) (A : PAlg l) (n : ℕ) : Prim (l ^ n) Γ(SU A, ⊤) := (r.ρ n).map ((toΓ A.Ug).comp (kb A))

def IsLcA (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) (x : A.Acr n) : Prop :=
  ∀ (e : A.A) (a : ZMod (l ^ n)), IsIdempotentElem e →
    (∀ p : PrimeSpectrum A.Ug, algebraMap A.U A.Ug (A.sharp e) ∉ p.asIdeal → f p = a) →
    A.toAcr n (WittVector.teichmuller l e) * x = A.toAcr n (WittVector.teichmuller l e) * (a.val : A.Acr n)

def lcA (A : PAlg l) (n : ℕ) : LocallyConstant (SU A) (ZMod (l ^ n)) →+ A.Acr n := pick fun κ => ∀ f, IsLcA A n f (κ f)

variable {C : Type 1} [Category.{0} C]

def probe (H : RIn l) (r : Roots l) (G : C ⥤ Test l) (n : ℕ) : Probe C (l ^ n) where
  S := (G ⋙ testι l) ⋙ UgR l ⋙ Scheme.Spec.rightOp
  split c := H.splitUg _ (G.obj c).property
  ζ c := r.zeta (G.obj c).obj n
  ζ_nat {c c'} φ := Subtype.ext ((toΓ_nat (PAlg.mapUg (G.map φ).hom) _).trans
    (congrArg (toΓ _) (RingHom.congr_fun (mapUg_kb (G.map φ).hom) _)))

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem kb_ok (A : PAlg l) : ((kb A).comp (algebraMap K (PadicAlgCl l))).comp (OK l K).subtype =
    (algebraMap A.U A.Ug).comp (A.oC.comp (okToOC l K)) := RingHom.ext fun x => A.cToUg_coe (okToOC l K x)

def geomPt (M : Model l K) (A : PAlg l) (y : M.P.obj A) : SU A ⟶ gb M :=
  pullback.lift
    (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap A.U A.Ug)) ≫ y.1)
      (Spec.map (CommRingCat.ofHom ((kb A).comp (algebraMap K (PadicAlgCl l))))) (by
        rw [Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, kb_ok]))
    (Spec.map (CommRingCat.ofHom (kb A))) (by
      rw [pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

theorem geomPt_fst (M : Model l K) (A : PAlg l) (y : M.P.obj A) : geomPt M A y ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (algebraMap A.U A.Ug)) ≫ y.1 := by
  rw [geomPt, pullback.lift_fst_assoc, pullback.lift_fst]

theorem geomPt_snd (M : Model l K) (A : PAlg l) (y : M.P.obj A) : geomPt M A y ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (kb A)) := pullback.lift_snd _ _ _

theorem gb_ext (M : Model l K) {V : Scheme.{0}} {a b : V ⟶ gb M}
    (h₁ : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (h₂ : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _) : a = b := by
  refine pullback.hom_ext (pullback.hom_ext (by simpa only [Category.assoc] using h₁) ?_) h₂
  have e := pullback.condition (f := M.q) (g := Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
  rw [Category.assoc, Category.assoc]
  change a ≫ pullback.fst _ _ ≫ M.q = b ≫ pullback.fst _ _ ≫ M.q
  rw [e, ← Category.assoc, h₂, Category.assoc]

theorem geomPt_nat (M : Model l K) {A B : PAlg l} (f : A ⟶ B) (y : M.P.obj A) :
    Spec.map (CommRingCat.ofHom (PAlg.mapUg f)) ≫ geomPt M A y = geomPt M B (M.P.map f y) := by
  refine gb_ext M ?_ ?_
  · rw [Category.assoc, geomPt_fst, geomPt_fst]
    change _ = _ ≫ Spec.map (CommRingCat.ofHom (PAlg.mapU f)) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun x => PAlg.mapUg_algebraMap f x
  · rw [Category.assoc, geomPt_snd, geomPt_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, mapUg_kb]

def pts (H : RIn l) (r : Roots l) (M : Model l K) (G : C ⥤ El M.P) (n : ℕ) :
    (probe H r (G ⋙ CategoryOfElements.π _) n).Pts (gb M) where
  y c := geomPt M (G.obj c).1.obj (G.obj c).2
  nat {c c'} φ := (geomPt_nat M (G.map φ).1.hom (G.obj c).2).trans (congrArg (geomPt M _) (G.map φ).2)

def RootsEx : Prop := ∀ (l : ℕ) [Fact l.Prime], Nonempty (Roots l)

def LcIdem : Prop := ∀ (l : ℕ) [Fact l.Prime], RIn l → ∀ A : PAlg l, A.IsTest → ∀ (ι : Type) [Fintype ι] (f : LocallyConstant (SU A) ι),
  ∃ e : ι → A.A, CompleteOrthogonalIdempotents e ∧
    (∀ (a : ι) (p : PrimeSpectrum A.Ug), algebraMap A.U A.Ug (A.sharp (e a)) ∉ p.asIdeal ↔ f p = a) ∧
    ∀ (e' : A.A) (a : ι), IsIdempotentElem e' →
      (∀ p : PrimeSpectrum A.Ug, algebraMap A.U A.Ug (A.sharp e') ∉ p.asIdeal → f p = a) → e' * e a = e'

def LcSpec : Prop := ∀ (l : ℕ) [Fact l.Prime], RIn l → ∀ A : PAlg l, A.IsTest → ∀ n : ℕ,
  (∀ f, IsLcA A n f (lcA A n f)) ∧ lcA A n 1 = 1 ∧ (∀ f g, lcA A n (f * g) = lcA A n f * lcA A n g) ∧
  ∀ (f : LocallyConstant (SU A) (ZMod (l ^ n))) (e : ZMod (l ^ n) → A.A), CompleteOrthogonalIdempotents e →
    (∀ a (p : PrimeSpectrum A.Ug), algebraMap A.U A.Ug (A.sharp (e a)) ∉ p.asIdeal → f p = a) →
    lcA A n f = ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n)

def LcNat : Prop := ∀ (l : ℕ) [Fact l.Prime], RIn l → ∀ A : PAlg l, A.IsTest → ∀ n : ℕ,
  (∀ B : PAlg l, B.IsTest → ∀ (φ : A.A →+* B.A) (h : PAlg.PdOk φ) (g : A.Ug →+* B.Ug),
    (∀ e, IsIdempotentElem e → g (algebraMap A.U A.Ug (A.sharp e)) = algebraMap B.U B.Ug (B.sharp (φ e))) →
    ∀ f, h.acr n (lcA A n f) = lcA B n (lcRes _ (Spec.map (CommRingCat.ofHom g)) f)) ∧
  ∀ f : LocallyConstant (SU A) (ZMod (l ^ (n + 1))), A.red n.le_succ (lcA A (n + 1) f) =
    lcA A n (f.map (ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))))

def LogEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (A : PAlg l) (n : ℕ),
  (∀ w : A.W, A.th w = 1 → ∃ y, IsLog A n w y) ∧ (∀ w y y', IsLog A n w y → IsLog A n w y' → y = y') ∧
  ∀ (e w w' : A.W) y y', IsIdempotentElem e → e * w = e * w' → IsLog A n w y → IsLog A n w' y' → A.toAcr n e * y = A.toAcr n e * y'

def LogMul : Prop := ∀ (l : ℕ) [Fact l.Prime] (A : PAlg l) (n : ℕ) (w w' : A.W) (y y' : A.Acr n), A.th w = 1 → A.th w' = 1 →
  IsLog A n w y → IsLog A n w' y' → IsLog A n (w * w') (y + y')

def LogEps : Prop := ∀ (l : ℕ) [Fact l.Prime] (A : PAlg l) (n : ℕ),
  IsLog A n (WittVector.teichmuller l (A.s (epsilon l))) (A.cris n (ACris.periodT (untilt_epsilon (p := l))))

def EpsRoot : Prop := ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), ∃ η : Ob l, η ^ l ^ n = epsilon l ∧
  ∀ A : PAlg l, A.sharp (A.s η) = A.oC (rootSeqInt l n)

def LcLog : Prop := ∀ (l : ℕ) [Fact l.Prime], RIn l → ∀ (r : Roots l) (A : PAlg l), A.IsTest → ∀ (n : ℕ) (u : A.A)
  (f : LocallyConstant (SU A) (ZMod (l ^ n))), IsPow (r.zeta A n) f (toΓ A.Ug (algebraMap A.U A.Ug (A.sharp u))) →
  IsLog A n (WittVector.teichmuller l (u ^ l ^ n)) ((ACris.periodT (untilt_epsilon (p := l)) : Acris l) • lcA A n f)

def lcMor (hN : LcNat) (H : RIn l) (r : Roots l) (G : C ⥤ Test l) (n : ℕ) :
    Mor (probe H r G n).L (modF ((G ⋙ testι l) ⋙ AcrA l n)) (Int.castRingHom (Acris l)) where
  G := 𝟭 C
  τ c := { toFun := lcA (G.obj c).obj n
           map_add' := map_add _
           map_smul' := fun z x => (map_zsmul (lcA (G.obj c).obj n) z x).trans (Int.cast_smul_eq_zsmul (Acris l) z _).symm }
  nat {c c'} φ x := ((hN l H _ (G.obj c).property n).1 _ (G.obj c').property _ (PAlg.pdOk_hom (G.map φ).hom)
    (PAlg.mapUg (G.map φ).hom) (fun e _ => (PAlg.mapUg_algebraMap _ _).trans (congrArg (algebraMap _ _)
      (congrArg (G.obj c').obj.th (WittVector.map_teichmuller _ _ _)))) x).symm

def eG (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (G : C ⥤ El M.P) (n : ℕ) (i : ℤ) (j : ℕ) :
    Ht (l ^ n) (sch.obj (gb M)) j i →+ CH.H (G ⋙ modF (AcrEl M.P n)) j :=
  ((lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j).toAddMonoidHom.comp ((pts H r M G n).et i j)

def eM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) (j : ℕ) :
    Ht (l ^ n) (sch.obj (gb M)) j i →+ M.MH n j := eG hN H r M (𝟭 _) n i j

def Roots.zetaX (r : Roots l) (M : Model l K) (n : ℕ) : Prim (l ^ n) Γ(gb M, ⊤) :=
  primRes (pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))) ((r.ρ n).map (toΓ _))

end CrystallineSemistableComparison.E
