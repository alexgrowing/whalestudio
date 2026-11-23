import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}}

def IsoBij : Prop := ∀ (K : Type) [Field K] (Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (π : Y ⟶ Z) (U V : Z.Opens),
  IsIso (π ∣_ U) → V ≤ U → ∀ (Q : ObjectProperty (Thick (smFun Z q))) (Q' : ObjectProperty (Thick (smFun Y (π ≫ q))))
    (hQ : Cosieve Q) (hQ' : Cosieve Q'), (∀ T, Q ((smS π rfl).G.obj T) → Q' T) → ∀ (a : ℕ) h h' (n : ℕ),
  Function.Bijective ((pullRC π rfl a (U := inU q V) (U' := inU (π ≫ q) (π ⁻¹ᵁ V)) hQ hQ' h h').mapH n)

def RelInjOf : Prop := SiteLaws → MVBij → CovDesc → ZarRel → ChartLaws → ChartBij → IsoBij → RelInj

def cupU (q : Z ⟶ Spec (CommRingCat.of K)) (U : ObjectProperty (Thick (smFun Z q))) {a a' c i j n : ℕ} (ha : a + a' = c)
    (h : i + j = n) : CH.Cn (U.ι ⋙ G q a) i →ₗ[K] CH.Cn (U.ι ⋙ G q a') j →ₗ[K] CH.Cn (U.ι ⋙ G q c) n :=
  (show CH.Pairing (U.ι ⋙ G q a) (U.ι ⋙ G q a') (U.ι ⋙ G q c) from
    ⟨fun T => (grOk (smFun Z q) ha).pair.μ T.obj, fun φ => (grOk (smFun Z q) ha).pair.nat φ.hom⟩).cupC h

def FormCup : Prop := ∀ (K : Type) [Field K] (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) (a a' : ℕ)
  (g₀ h₀ : Sec q V) (g : Fin a → Sec q V) (h : Fin a' → Sec q V) (x : CH.Cn ((inU q V).ι ⋙ G q a) a)
  (y : CH.Cn ((inU q V).ι ⋙ G q a') a') hx hy, IsForm q V g₀ g ((CH.cx _).cls x hx) → IsForm q V h₀ h ((CH.cx _).cls y hy) →
  ∃ hz, IsForm q V (a := a + a') (g₀ * h₀) (Fin.append g h) ((CH.cx _).cls (cupU q (inU q V) rfl rfl x y) hz)

def FirstChernCoboundary : Prop := ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Spec (CommRingCat.of K)) (D : E.LineData Y) (ι : Type)
  (U : ι → Y.Opens) (σ : ∀ α, (U α : Scheme.{0}) ⟶ D.Y) (hσ : ∀ α, σ α ≫ D.f = (U α).ι) (r : CH.Cn (G q 1) 2)
  (hr : CH.d (G q 1) 2 r = 0), IsDlogFirstChernClass q D (clsH (a := 1) q r hr) →
  ∃ (ε : ℤˣ) (β : ∀ α, CH.Cn ((inU q (U α)).ι ⋙ G q 1) 1),
    (∀ α, CH.d _ 1 (β α) = (CH.Mor.restrict (G q 1) (inU q (U α)).ι).pullC 2 r) ∧
    ∀ α α' (V : Y.Opens) (h : V ≤ U α) (h' : V ≤ U α') (k : inU q V ≤ inU q (U α)) (k' : inU q V ≤ inU q (U α')) (u : (Sec q V)ˣ),
      (V.topIso.inv.hom u.1 = D.u (Y.homOfLE h ≫ σ α) (Y.homOfLE h' ≫ σ α') (by simp [hσ])) →
      ∃ hz, IsForm q V (a := 1) ((ε : ℤ) • (↑u⁻¹ : Sec q V)) ![(u : Sec q V)]
        ((CH.cx ((inU q V).ι ⋙ G q 1)).cls ((resU (G q 1) k).pullC 1 (β α) - (resU (G q 1) k').pullC 1 (β α')) hz)

def DivCover : Prop := ∀ (K : Type) [Field K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q]
  (i : W ⟶ Z) (π : Y ⟶ Z) [IsProper π] (D : E.LineData Y) (d : ℕ) (B : Blow q i π D d),
  ∃ (m : ℕ) (U : Fin m → Y.Opens) (σ : ∀ α, (U α : Scheme.{0}) ⟶ D.Y), (∀ α, σ α ≫ D.f = (U α).ι) ∧ (⨆ α, U α) = ⊤ ∧
    (∀ α α', IsAffineOpen (U α ⊓ U α')) ∧ ∀ α (V : Y.Opens) (h : V ≤ U α), IsAffineOpen V →
      (∃ n, Nonempty (Coord (π ≫ q) V n)) ∧ (∃ n, Nonempty (Coord (pullback.snd i π ≫ π ≫ q) (pullback.snd i π ⁻¹ᵁ V) n)) ∧
      RingHom.ker ((pullback.snd i π).app V).hom = Ideal.span {V.topIso.hom.hom (B.f (Y.homOfLE h ≫ σ α))} ∧
      ∀ (a : ℕ) (ω : Om K (Sec (π ≫ q) V) a), (show Sec (π ≫ q) V from V.topIso.hom.hom (B.f (Y.homOfLE h ≫ σ α))) • ω = 0 → ω = 0

def ConeKill : Prop := ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (A B : Sy.{1} R ι) (a : ℕ), A.Desc → B.Desc → A.One a →
  B.One (a + 1) → ∀ (ρ : ∀ S n, (A.K S).X n →ₗ[R] (B.K S).X (n + 2))
    (η : ∀ (α : ι) (S : Finset ι), α ∈ S → ∀ n, (A.K S).X n →ₗ[R] (B.K S).X (n + 1)),
  (∀ S n x, (B.K S).d (n + 2) (ρ S n x) = ρ S (n + 1) ((A.K S).d n x)) →
  (∀ {S T : Finset ι} (h : S ⊆ T) n x, ρ T n ((A.res h).f n x) = (B.res h).f _ (ρ S n x)) →
  (∀ α {S T : Finset ι} (h : S ⊆ T) hS n x, η α T (h hS) n ((A.res h).f n x) = (B.res h).f _ (η α S hS n x)) →
  (∀ α S hS n x, (B.K S).d (n + 1) (η α S hS n x) + η α S hS (n + 1) ((A.K S).d n x) = ρ S n x) →
  ∀ lam : ∀ (α : ι) (S : Finset ι), α ∈ S → ((A.K S).H a →ₗ[R] (B.K S).H (a + 1)),
  (∀ α {S T : Finset ι} (h : S ⊆ T) hS x, lam α T (h hS) ((A.res h).mapH a x) = (B.res h).mapH _ (lam α S hS x)) →
  (∀ α α' S hS hS' x hx hz, (B.K S).cls (η α S hS a x - η α' S hS' a x) hz =
    lam α S hS ((A.K S).cls x hx) - lam α' S hS' ((A.K S).cls x hx)) →
  ∀ n x, (A.K ∅).d n x = 0 → ρ ∅ n x ∈ (B.K ∅).B (n + 2)

def ConeKillOf : Prop := OneSurj → ConeKill

def RelKillOf : Prop := SiteLaws → CovDesc → ZarRel → AffOm → OmNat → AffRel → FormLaws → DWedge → DLog → FormCup → FirstChernCoboundary →
  DivCover → ConeKill → RelKill

def KunAff : Prop := ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K))
  (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens)
  (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → Nonempty (Coord (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') (d + d')) ∧
  ∀ (c : ℕ) h h', ∃ e : (∀ a : Fin (c + 1), TensorProduct K (HV q V a a) (HV q' V' (c - a) (c - a))) ≃ₗ[K]
      HV (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') c c,
    ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : CH.Cn ((inU q V).ι ⋙ G q a) a) (y : CH.Cn ((inU q' V').ι ⋙ G q' (c - a)) (c - a)) hx hy hz,
      e (Pi.single a ((CH.cx _).cls x hx ⊗ₜ (CH.cx _).cls y hy)) = (CH.cx _).cls
        (cupU (p₁ ≫ q) _ hc hc
          ((morV p₁ rfl a h).pullC a x) ((morV p₂ hP.w.symm (c - a) h').pullC (c - a) y)) hz

def KunAffOf : Prop := SiteLaws → AffOm → OmNat → FormLaws → FormCup → OmKun → KunAff

def SlantOf : Prop := SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → Slant

def ZarRelOf : Prop := SiteLaws → OnIso → ZarAbs → ZarRel

def AffRelOf : Prop := SiteLaws → OnIso → AffOm → OmNat → FormLaws → AffRel

def RelLiftOf : Prop := SiteLaws → OnIso → RelLift

end CrystallineSemistableComparison.Onto

end
