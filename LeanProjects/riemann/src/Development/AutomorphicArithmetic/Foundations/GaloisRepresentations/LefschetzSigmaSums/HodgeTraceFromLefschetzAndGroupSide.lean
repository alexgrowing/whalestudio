import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.HodgeCoh
open GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights
open UpperTheory.Gal.Int.Geo (KS Lv Sc Mem IsFnL KSHodge HOcc IsHEig bcAlong)
open UpperTheory.Gal.G3 (Tower Th hodge ind bcMap bcMap_fst bcMap_snd)
open scoped Classical

namespace UpperTheory.Gal.LocalSmoothExtension

theorem isPullback_bcMap {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} (f : Y ⟶ X) (h : f ≫ p = q) :
    IsPullback (pullback.fst q g) (bcMap g f h) f (pullback.fst p g) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p g) (v₂₂ := p) (h₃₁ := g) ?_ (bcMap_fst g f h).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd, h]
  exact IsPullback.of_hasPullback q g

def towerBc {B B' : Scheme.{0}} {Γ : Type} [Group Γ] (X : Tower B' Γ) (g : B ⟶ B') : Tower B Γ where
  ι := X.ι
  K := X.K
  Δ := X.Δ
  K_le := X.K_le
  deep := X.deep
  idx := X.idx
  Z i := pullback (X.q i) g
  q i := pullback.snd (X.q i) g
  tr i j h a b := bcMap g (X.tr i j h a b) (X.tr_q i j h a b)
  tr_q i j h a b := bcMap_snd _ _ _
  tr_self i k a b hk := by
    apply pullback.hom_ext
    · rw [bcMap_fst, X.tr_self i k a b hk, Category.comp_id, Category.id_comp]
    · rw [bcMap_snd, Category.id_comp]
  tr_mul i j m h h' a b a' b' a'' b'' := by
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, X.tr_mul i j m h h' a b a' b' a'' b'',
        bcMap_fst]
    · rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]
  fin i j a b := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_bcMap g _ _) (X.fin i j a b)
  etale i j a b := MorphismProperty.of_isPullback (P := @Etale) (isPullback_bcMap g _ _) (X.etale i j a b)
  onto i j a b := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_bcMap g _ _) (X.onto i j a b)
  trans i j a b hn Ω _ _ x y e := by
    have e1 := congrArg (· ≫ pullback.fst (X.q j) g) e
    have e2 := congrArg (· ≫ pullback.snd (X.q j) g) e
    simp only [Category.assoc, bcMap_fst, bcMap_snd] at e1 e2
    obtain ⟨k, hk, a', b', e3⟩ := X.trans i j a b hn Ω (x ≫ pullback.fst _ _) (y ≫ pullback.fst _ _)
      (by simpa only [Category.assoc] using e1)
    refine ⟨k, hk, a', b', ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, e3, Category.assoc]
    · rw [Category.assoc, bcMap_snd, e2]
  free i j hij k hk a b Ω _ _ x e := by
    have e1 := congrArg (· ≫ pullback.fst (X.q i) g) e
    simp only [Category.assoc, bcMap_fst] at e1
    exact X.free i j hij k hk a b Ω (x ≫ pullback.fst _ _) (by simpa only [Category.assoc] using e1)

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

def diagO (D : Datum p) {k : ℕ} (α : Fin k → 𝓞 D.F) : Matrix (Fin k) (Fin k) D.toG.O :=
  Matrix.diagonal fun s => algebraMap (𝓞 D.F) D.O (α s)

def StdC (D : Datum p) (gb : GBase D.toG ℂ) : Prop :=
  gb.ρ = D.ρc ∧ ∀ (i : Fin D.a) (c : 𝓞 D.F), gb.t i c = D.tau i (c : D.F)

variable {L : GlobalTheory.LKGeo.Link D G} {gb : GBase D.toG ℂ} {k : ℕ}

abbrev qAt (T : KS L gb k) (N : Lv p) : T.X.Z (T.lev N) ⟶ Sp ℂ := T.X.q (T.lev N)

def al (T : KS L gb k) (N : Lv p) (α : Fin k → 𝓞 D.F) : T.X.Z (T.lev N) ⟶ T.X.Z (T.lev N) :=
  (T.e N).hom ≫ (GlobalTheory.KS.matEnd (T.M N).univ.act (diagO D α)).left ≫ (T.e N).inv

theorem al_q (T : KS L gb k) (N : Lv p) (α : Fin k → 𝓞 D.F) : al T N α ≫ qAt T N = qAt T N := by
  have h := T.e_q N
  rw [al, qAt, Category.assoc, Category.assoc]
  conv_lhs => rw [← h]
  rw [Iso.inv_hom_id_assoc, ← Category.assoc (GlobalTheory.KS.matEnd (T.M N).univ.act (diagO D α)).left, Over.w, h]

def hk (T : KS L gb k) (N : Lv p) (f : G.GAf → ℂ) (a b : ℕ) : Module.End ℂ (hodgeH (qAt T N) a b) :=
  T.X.hecke (hodge ℂ a b) (T.lev N) f

def cutD (T : KS L gb k) (N : Lv p) (c : (Fin k → 𝓞 D.F) →₀ ℂ) (a b : ℕ) : Module.End ℂ (hodgeH (qAt T N) a b) :=
  c.sum fun α r => r • hodgePull (al_q T N α) a b

def leg (T : KS L gb k) (N' N : Lv p) (h : G.GAf) (b : T.X.admitted (T.lev N') (T.lev N) h) (α : Fin k → 𝓞 D.F) :
    T.X.Z (T.lev N') ⟶ T.X.Z (T.lev N) := T.X.tr _ _ h b.1 b.2 ≫ al T N α

theorem leg_q (T : KS L gb k) (N' N : Lv p) (h : G.GAf) (b : T.X.admitted (T.lev N') (T.lev N) h) (α : Fin k → 𝓞 D.F) :
    leg T N' N h b α ≫ qAt T N = qAt T N' := by
  rw [leg, Category.assoc, al_q, qAt, T.X.tr_q]

def altTr {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) (d : ℕ) (u : ∀ a b : ℕ, Module.End ℂ (hodgeH s a b)) (y : ℂ) : ℂ :=
  ∑ a ∈ Finset.range (d + 1), (-y) ^ a * ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (u a b)

def HolomorphicLefschetzFormula : Prop :=
  ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
  ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1],
  IsFinite c2 → Etale c2 →
  ∀ (F : Finset (CxPts s' (RingHom.id ℂ))), (∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2) →
  ∀ A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ,
    (∀ y ∈ F, GlobalTheory.W1.IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) →
  ∀ a : ℕ, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
    ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
      ∑ y ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det

def ZSm : Prop :=
  ∀ (G : GDatum) (gb : GBase G ℂ) (N : ℕ), 3 ≤ N → ∀ (X : GenModel gb N) (r : ℕ),
    ∃ d : ℕ, SmoothOfRelativeDimension d ((GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s)

def ZPr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.CompactB → ∀ (gb : GBase D.toG ℂ) (N : ℕ), 3 ≤ N → N.Coprime p →
    ∀ (X : GenModel gb N) (r : ℕ), IsProjOver ((GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s)

def KSProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G), Sc D G → ∀ (gb : GBase D.toG ℂ) (k : ℕ)
    (T : KS L gb k) (N : Lv p), IsProjOver (qAt T N) ∧ ∃ d, SmoothOfRelativeDimension d (qAt T N)

def FixK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G), Sc D G → ∀ gb : GBase D.toG ℂ, StdC D gb →
    ∀ (i₀ : Fin D.a) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 →
    ∀ (k : ℕ) (T : KS L gb k) (N' N : Lv p), N.1 ∣ N'.1 → ∀ d : ℕ, SmoothOfRelativeDimension d (qAt T N) →
    ∀ (h : G.GAf) (a : T.X.admitted (T.lev N') (T.lev N) 1) (b : T.X.admitted (T.lev N') (T.lev N) h),
    (∀ g, ind ℂ (L.KN N.1) h⁻¹ g ≠ 0 → RegAf G g) →
    ∀ α : Fin k → 𝓞 D.F, (∀ s, α s ≠ 0 ∧ (2 : 𝓞 D.F) ∣ α s) →
      CxFin G v (L.KN N.1) (ind ℂ (L.KN N.1) h⁻¹) ∧ IsFinite (leg T N' N h b α) ∧ Etale (leg T N' N h b α) ∧
      ∃ (F : Finset (CxPts (qAt T N') (RingHom.id ℂ)))
        (A : CxPts (qAt T N') (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ),
        (∀ x, x ∈ F ↔ x.1 ≫ T.X.tr _ _ 1 a.1 a.2 = x.1 ≫ leg T N' N h b α) ∧
        (∀ x ∈ F, GlobalTheory.W1.IsTan d (T.X.tr _ _ 1 a.1 a.2) (leg T N' N h b α) (T.X.tr_q _ _ 1 a.1 a.2) (leg_q T N' N h b α) x (A x) ∧
          (1 - A x).det ≠ 0) ∧
        ∀ y : ℂ, ∑ x ∈ F, UpperTheory.Gal.W2.lefTerm (A x) y =
          (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ) *
            cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (ind ℂ (L.KN N.1) h⁻¹) (Kp G) (oneP G)

def HodgeTr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ)
    (i₀ : Fin D.a) (h : Fin G.n → ℕ), IsHExp (D.tau i₀) (epsOf D) lam h →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 D.F) →₀ ℂ, Sc D G → ∀ gb : GBase D.toG ℂ, StdC D gb →
    ∀ (T : KS L gb k) (N : Lv p) (d : ℕ), SmoothOfRelativeDimension d (qAt T N) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V),
      IsWt L lam ξ → ∀ f : G.GAf → ℂ, T.X.IsFn (T.lev N) f → Good G (L.KN N.1) f → ∀ y : ℂ,
        altTr (qAt T N) d (fun a b => hk T N f a b ∘ₗ cutD T N c a b) y =
          dTrace G ξ (L.KN N.1) f (Kp G) (oneP G) * ∑ i, y ^ h i

def HodgeEig : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G), Sc D G →
    ∀ lam : (D.F →+* ℂ) → Fin G.n → ℕ, (∀ τ, Antitone (lam τ)) →
    ∃ k, ∀ gb : GBase D.toG ℂ, StdC D gb → ∀ (T : KS L gb k) (N : Lv p) (σ : ℂ ≃+* ℂ)
    (i₀ : Fin D.a) (h : Fin G.n → ℕ), IsHExp (D.tau i₀) (epsOf D) (conjWt σ lam) h →
    ∀ (J : Type) (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (f : G.GAf → ℂ), (∀ j, T.X.IsFn (T.lev N) (ψ j)) → T.X.IsFn (T.lev N) f →
      Spec L (conjWt σ lam) (L.KN N.1) ψ θ f →
      ∀ i, ∃ (b : ℕ) (x : hodgeH (qAt T N) (h i) b), x ≠ 0 ∧ ∀ j, hk T N (ψ j) (h i) b x = θ j • x

def KSBc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G) (R : Type) [Field R] [Algebra ℚ R]
    (gb : GBase D.toG R) (k : ℕ) (T : KS L gb k) (τ : R →+* ℂ) (gb' : GBase D.toG ℂ), gb'.ρ = τ gb.ρ →
    (∀ i c, gb'.t i c = τ (gb.t i c)) →
    ∃ T' : KS L gb' k, T'.X = towerBc T.X (Spec.map (CommRingCat.ofHom τ)) ∧ HEq T'.lev T.lev

def HodgeTraceFromLefschetzAndGroupSide : Prop := HolomorphicLefschetzFormula → KSProj → FixK → MarkWeightedFixedPointEqDefinitePairOdd → TraceDefinitePairsEqAutomorphicTrace → HodgeTr ∧ HodgeEig ∧ KSHodge

def HodgeFin : Prop :=
  ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ), SmoothOfRelativeDimension d s → IsProjOver s →
    ∀ a b, FiniteDimensional ℂ (hodgeH s a b)

def FnDecomp : Prop :=
  ∀ (B : Scheme.{0}) (Γ : Type) [Group Γ] (X : Tower B Γ) (j : X.ι) (f : Γ → ℂ),
    (X.IsFn j f → f ∈ Formalism.UG.Hecke ℂ (X.K j) ∧ ∃ (m : ℕ) (h : Fin m → Γ) (c : Fin m → ℂ), (∀ i, h i ∈ X.Δ) ∧
      f = ∑ i, c i • ind ℂ (X.K j) (h i)⁻¹ ∧ ∀ i g, ind ℂ (X.K j) (h i)⁻¹ g ≠ 0 → f g ≠ 0) ∧
    (f ∈ Formalism.UG.Hecke ℂ (X.K j) → (∀ g, f g ≠ 0 → g⁻¹ ∈ X.Δ) → X.IsFn j f)

def HopWord : Prop :=
  ∀ (B : Scheme.{0}) (Γ : Type) [Group Γ] (X : Tower B Γ) (T : Th.{0} B ℂ), T.Good → ∀ j : X.ι,
    (∀ (m : ℕ) (f : Fin m → Γ → ℂ) (c : Fin m → ℂ), (∀ i, X.IsFn j (f i)) →
      X.IsFn j (∑ i, c i • f i) ∧ X.hecke T j (∑ i, c i • f i) = ∑ i, c i • X.hecke T j (f i)) ∧
    ∀ (J : Type) (ψ : J → Γ → ℂ) (f : Γ → ℂ), (∀ i, X.IsFn j (ψ i)) → X.IsFn j f →
      (∀ w : List J, X.IsFn j (wordFn (X.K j) ψ w f) ∧
        X.hecke T j (wordFn (X.K j) ψ w f) = (w.map fun i => X.hecke T j (ψ i)).prod * X.hecke T j f) ∧
      ∀ s : List J →₀ ℂ, X.IsFn j (polyFn (X.K j) ψ s f) ∧
        X.hecke T j (polyFn (X.K j) ψ s f) = UpperTheory.Gal.CertificateRingHomMap.wop (fun i => X.hecke T j (ψ i)) s * X.hecke T j f

def GeoStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G), Sc D G → ∀ gb : GBase D.toG ℂ, StdC D gb →
    ∀ (i₀ : Fin D.a) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 →
    ∀ (k : ℕ) (T : KS L gb k) (N : Lv p) (d : ℕ), SmoothOfRelativeDimension d (qAt T N) →
    ∀ h ∈ T.X.Δ, (∀ g, ind ℂ (L.KN N.1) h⁻¹ g ≠ 0 → RegAf G g) →
    ∀ α : Fin k → 𝓞 D.F, (∀ s, α s ≠ 0 ∧ (2 : 𝓞 D.F) ∣ α s) →
      CxFin G v (L.KN N.1) (ind ℂ (L.KN N.1) h⁻¹) ∧ ∀ y : ℂ,
        altTr (qAt T N) d (fun a b => hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b) y =
          cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (ind ℂ (L.KN N.1) h⁻¹) (Kp G) (oneP G)

def AltLin : Prop :=
  ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d m : ℕ) (A : Type) (u : Fin m → ∀ a b : ℕ, Module.End ℂ (hodgeH s a b)) (c : Fin m → ℂ)
    (w : A →₀ ℂ) (e : A → ∀ a b : ℕ, Module.End ℂ (hodgeH s a b)) (y : ℂ),
    altTr s d (fun a b => (∑ i, c i • u i a b) ∘ₗ w.sum fun α r => r • e α a b) y =
      ∑ i, c i * w.sum fun α r => r * altTr s d (fun a b => u i a b ∘ₗ e α a b) y

def MemOp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G) (R : Type) [Field R] [Algebra ℚ R]
    (gb : GBase D.toG R) (k : ℕ) (T : KS L gb k) (N : Lv p) (J : Type) (g : J → Mem L N) (j : J),
    T.X.IsFn (T.lev N) (g j).fn ∧ IsFinite ((T.tower N g).s j) ∧ Etale ((T.tower N g).s j) ∧
    ∀ Θ : Th.{0} (Sp R) ℂ, Θ.Good → Θ.IsOp (T.X.q (T.lev N)) (T.X.q (T.lev N)) ((T.tower N g).s j) ((T.tower N g).t j)
      (T.X.hecke Θ (T.lev N) (g j).fn)

def OccOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G) (R : Type) [Field R] [Algebra ℚ R]
    (gb : GBase D.toG R) (k : ℕ) (T : KS L gb k) (N : Lv p) (J : Type) (g : J → Mem L N) (τ : R →+* ℂ) (θ : J → ℂ) (a b : ℕ)
    (x : ((hodge ℂ a b).bc (Spec.map (CommRingCat.ofHom τ))).H (T.X.q (T.lev N))), x ≠ 0 →
    (∀ j, T.X.hecke ((hodge ℂ a b).bc (Spec.map (CommRingCat.ofHom τ))) (T.lev N) (g j).fn x = θ j • x) →
    HOcc (bcAlong (T.tower N g) τ) θ a

end UpperTheory.Gal.LocalSmoothExtension
