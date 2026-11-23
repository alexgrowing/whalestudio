import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)

universe u v

namespace UpperTheory.Gal.G3

abbrev etG (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : Th.{1} (sp k) ℚ_[l] :=
  (et l (sp Ω)).bc (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

def AlgIsoPts : Prop := ∀ (D E : Type) [CommRing D] [CommRing E] [Algebra D E] [Algebra.Etale D E],
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : D →+* Ω), ∃! y : E →+* Ω, y.comp (algebraMap D E) = x) →
  Function.Bijective (algebraMap D E)

def AlgSplit : Prop := ∀ (A A' C : Type) [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C] [Algebra.Etale A A']
  (J : Type) [Fintype J] (τ : J → (A' →ₐ[A] C)),
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : C →+* Ω) (y : A' →+* Ω), y.comp (algebraMap A A') = x.comp (algebraMap A C) →
    ∃! j, x.comp (τ j : A' →+* C) = y) →
  ∃ e : C ⊗[A] A' ≃ₐ[C] (J → C), ∀ b j, e (1 ⊗ₜ b) j = τ j b

def AlgTr : Prop := ∀ (A A' C : Type) [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C] [Module.Finite A A']
  [Algebra.Etale A A'] (J : Type) [Fintype J] (τ : J → (A' →ₐ[A] C)) (e : C ⊗[A] A' ≃ₐ[C] (J → C)),
  (∀ b j, e (1 ⊗ₜ b) j = τ j b) → ∀ b, algebraMap A C (etTrace A A' b) = ∑ j, τ j b

def FEtBasic : Prop :=
  (∀ {P Y Z' Z : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) (d : ℕ), IsPullback v s' s g → FEt s d → FEt s' d) ∧
  (∀ {W Y Z : Scheme.{0}} (r : W ⟶ Y) (s : Y ⟶ Z) (d e : ℕ), FEt r e → FEt s d → FEt (r ≫ s) (d * e)) ∧
  ∀ {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)), IsGalois c G a → FEt c (Nat.card G)

def SplitsBasic : Prop :=
  (∀ {Z Y W W' : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (g : W' ⟶ W),
    Splits s c σ → Splits s (g ≫ c) fun j => g ≫ σ j) ∧
  ∀ {P Y Z' Z W : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) [IsFinite s] [Etale s], IsPullback v s' s g →
    ∀ (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P)), (∀ j, σ j ≫ s' = c) →
      (Splits s' c σ ↔ Splits s (c ≫ g) fun j => σ j ≫ v)

def OrdEx : Prop := ∀ {Z Y : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ), ∃ (W : Scheme.{0}) (c : W ⟶ Z)
  (σ : Fin d → (W ⟶ Y)), IsFinite c ∧ Etale c ∧ (∀ j, σ j ≫ s = c) ∧
  (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j) ∧
  ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
    (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
    ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j

def OrdStep : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (d : ℕ) (σ : Fin d → (W ⟶ Y)),
  (∀ j, σ j ≫ s = c) → ∃ V : (pullback s c).Opens, IsClosed (V : Set ↑(pullback s c)) ∧
    ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ pullback s c),
      (x (IsLocalRing.closedPoint Ω) ∈ V ↔ ∀ j, x ≫ pullback.snd s c ≫ σ j ≠ x ≫ pullback.fst s c)

def GalClosD : Prop := ∀ {Z Y : Scheme.{0}} (s : Y ⟶ Z) (d : ℕ), FEt s d →
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (σ : Fin d → (W ⟶ Y)),
    IsGalois c G a ∧ Splits s c σ

def MultiSplit : Prop := ∀ {Z : Scheme.{0}} (n : ℕ) (Y : Fin n → Scheme.{0}) (s : ∀ i, Y i ⟶ Z) (d : Fin n → ℕ),
  (∀ i, FEt (s i) (d i)) → ∃ (W : Scheme.{0}) (c : W ⟶ Z) (e : ℕ), 0 < e ∧ FEt c e ∧
    ∀ i, ∃ σ : Fin (d i) → (W ⟶ Y i), Splits (s i) c σ

def FEtInj : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Z W : Scheme.{0}} (p : Z ⟶ B)
  (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r) (d : ℕ), 0 < d → FEt c d → Function.Injective (T.pull c hc)

def TrBase : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {P Y Z' Z : Scheme.{0}}
  (p : Z ⟶ B) (q : Y ⟶ B) (p' : Z' ⟶ B) (q' : P ⟶ B) (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) (d : ℕ)
  (hv : v ≫ q = q') (hg : g ≫ p = p'), s' ≫ p' = q' → IsPullback v s' s g → FEt s d →
  ∀ tr tr', T.IsTr p q s tr → T.IsTr p' q' s' tr' → ∀ x, T.pull g hg (tr x) = tr' (T.pull v hv x)

def TrPushM : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Y P Z : Scheme.{0}}
  (p : Z ⟶ B) (q : P ⟶ B) (r : Y ⟶ B) (κ : Y ⟶ P) (s : P ⟶ Z) (d m : ℕ) (hκ : κ ≫ q = r), s ≫ p = q → FEt s d → FEt κ m →
  ∀ tr tr', T.IsTr p q s tr → T.IsTr p r (κ ≫ s) tr' → ∀ x, tr' (T.pull κ hκ x) = (m : R) • tr x

def SplitsComp : Prop := ∀ {Y P Z W : Scheme.{0}} (κ : Y ⟶ P) (s : P ⟶ Z) [IsFinite κ] [Etale κ] [IsFinite s] [Etale s]
  (c : W ⟶ Z) (I J : Type) [Finite I] [Finite J] (τ : I → (W ⟶ P)) (σ : I → J → (W ⟶ Y)), Splits s c τ →
  (∀ i, Splits κ (τ i) (σ i)) → Splits (κ ≫ s) c fun x : I × J => σ x.1 x.2

def LiesAbs : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Z Y C D : Scheme.{0}}
  (pZ : Z ⟶ B) (pY : Y ⟶ B) (pC : C ⟶ B) (pD : D ⟶ B) (π : Z ⟶ Y) (hπ : π ≫ pY = pZ) (sg tg : C ⟶ Z) (htg : tg ≫ pZ = pC)
  (s t : D ⟶ Y) (ht : t ≫ pY = pD) (κ : C ⟶ D) (h : sg ≫ π = κ ≫ s) (d m : ℕ), sg ≫ pZ = pC → s ≫ pY = pD →
  κ ≫ t = tg ≫ π → FEt s d → FEt (pullback.lift sg κ h) m → ∀ tr trg, T.IsTr pY pD s tr → T.IsTr pZ pC sg trg →
  ∀ x, trg (T.pull tg htg (T.pull π hπ x)) = (m : R) • T.pull π hπ (tr (T.pull t ht x))

abbrev piK {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    H.Z ⟶ pullback C.p (gen O k) := pullback.lift C.π H.q C.ov

theorem piK_snd {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    piK C ≫ pullback.snd C.p (gen O k) = H.q := pullback.lift_snd _ _ _

def HopSpec : Prop := ∀ (l : ℕ) [Fact l.Prime] {k : Type} [Field k], (l : k) ≠ 0 → ∀ (H : HTower k) (Ω : Type) [Field Ω]
  [Algebra k Ω] (g : H.Γ) (d : ℕ), FEt (H.s g) d → IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g) ∧
    ∀ tr, (etG l k Ω).IsTr H.q (H.s g ≫ H.q) (H.s g) tr → hop l H Ω g = tr ∘ₗ (etG l k Ω).pull (H.t g) (H.comm g)

def LiesGen : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O) (g : H.Γ) {D : Scheme.{0}} (s t : D ⟶ C.Y) (hst : t ≫ C.p = s ≫ C.p) (m : ℕ), C.Lies g s t m →
  ∃ (κ : H.Y g ⟶ pullback (s ≫ C.p) (gen O k)) (h : H.s g ≫ piK C = κ ≫ bcMap (gen O k) s rfl),
    κ ≫ bcMap (gen O k) t hst = H.t g ≫ piK C ∧ FEt (pullback.lift (H.s g) κ h) m

def LiesOp : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O) (g : H.Γ) {D : Scheme.{0}} (s t : D ⟶ C.Y) (hst : t ≫ C.p = s ≫ C.p) (m d : ℕ), C.Lies g s t m →
  FEt (bcMap (gen O k) s (rfl : s ≫ C.p = _)) d → ∀ {R : Type} [Field R] (T : Th.{u} (sp k) R), T.Good →
  ∀ tr trg, T.IsTr (pullback.snd C.p (gen O k)) (pullback.snd (s ≫ C.p) (gen O k)) (bcMap (gen O k) s rfl) tr →
    T.IsTr H.q (H.s g ≫ H.q) (H.s g) trg →
    ∀ x, trg (T.pull (H.t g) (H.comm g) (T.pull (piK C) (piK_snd C) x)) =
      (m : R) • T.pull (piK C) (piK_snd C) (tr (T.pull (bcMap (gen O k) t hst) (bcMap_snd _ _ _) x))

def CoverInv : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O), C.Onto → ∀ {R : Type} [Field R] [CharZero R] (T : Th.{u} (sp k) R), T.Good →
  Function.Injective (T.pull (piK C) (piK_snd C)) ∧ ∀ y : T.H H.q,
    (∀ g, IsIso (H.s g) → θ g = 1 → ∃ tr, T.IsTr H.q (H.s g ≫ H.q) (H.s g) tr ∧ tr (T.pull (H.t g) (H.comm g) y) = y) →
    ∃ x, T.pull (piK C) (piK_snd C) x = y

def PieceLe : Prop := ∀ (l : ℕ) [Fact l.Prime] {k L O : Type} [Field k] [Field L] [Algebra ℚ_[l] L] [CommRing O] [Algebra O k],
  (l : k) ≠ 0 → ∀ {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O), C.Onto → ∀ (Ω : Type) [Field Ω] [Algebra k Ω],
  Function.Injective (((etG l k Ω).pull (piK C) (piK_snd C)).baseChange L) ∧
  ∀ y ∈ piece l H Ω L θ, ∃ x, ((etG l k Ω).pull (piK C) (piK_snd C)).baseChange L x = y

end UpperTheory.Gal.G3

end
