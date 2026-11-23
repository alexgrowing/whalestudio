import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.LocalSmoothExtension (Spec IsHExp conjWt epsOf)

namespace UpperTheory.Gal.Int.Geo

def IsFnL {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (N : ℕ) (f : G.GAf → ℂ) : Prop :=
  f ∈ Formalism.UG.Hecke ℂ (L.KN N) ∧ ∀ y, f y ≠ 0 → Integ L y⁻¹

def KSHodge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G →
    ∀ lam : (D.F →+* ℂ) → Fin G.n → ℕ, (∀ τ, Antitone (lam τ)) → ∃ k : ℕ,
    ∀ (R : Type) [Field R] [Algebra ℚ R] (gb : GBase D.toG R) (T : KS L gb k) (N : Lv p) (J : Type) (g : J → Mem L N)
      (θ : J → ℂ) (f : G.GAf → ℂ), IsFnL L N.1 f → Spec L lam (L.KN N.1) (fun j => (g j).fn) θ f →
    ∀ τ : R →+* ℂ, τ gb.ρ = D.ρc → (∀ (i : Fin D.a) (c : 𝓞 D.F), τ (gb.t i c) = D.tau i (c : D.F)) →
    ∀ (σ : ℂ ≃+* ℂ) (i₀ : Fin D.a) (h : Fin G.n → ℕ), IsHExp (D.tau i₀) (epsOf D) (conjWt σ lam) h →
    ∀ i, HOcc (bcAlong (T.tower N g) τ) (fun j => σ (θ j)) (h i)

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def CongP (ι : Qbar l ≃+* ℂ) (a : ℕ) {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} (e : D.F ≃+* E) {N : Lv p}
    {J : Type} (g : J → Mem L N) (θ : J → Qbar l) (κ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  κ.UnrAt w ∧ ∃ (𝔴 : Ideal (𝓞 D.F)) (ϑ : ℕ → Qbar l), IsPl e w 𝔴 ∧ CongGrp g θ 𝔴 ϑ ∧
    HasRoots ι w a ϑ ((algSat a (normV w) B).map (· * ((κ.val w : ℂˣ) : ℂ)⁻¹))

structure Plan (ι : Qbar l ≃+* ℂ) (d : ℕ) (U : Submodule ℂ (UA E a → ℂ)) : Type 1 where
  p : ℕ
  [hp : Fact p.Prime]
  D : Datum p
  G : HTGroup p
  L : Link D G
  sc : Sc D G
  e : D.F ≃+* E
  n_eq : D.n = a
  N : Lv p
  J : Type
  g : J → Mem L N
  θ : J → Qbar l
  κ : HChar E
  m : (E →+* ℂ) → ℤ
  alg : IsAlgPos κ m
  lam : (D.F →+* ℂ) → Fin G.n → ℕ
  anti : ∀ τ, Antitone (lam τ)
  f : G.GAf → ℂ
  fn : IsFnL L N.1 f
  spec : Spec L lam (L.KN N.1) (fun j => (g j).fn) (fun j => ι (θ j)) f
  cong : ∃ X : Finset (HeightOneSpectrum (𝓞 E)), ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B → CongP ι a e g θ κ w B

attribute [instance] Plan.hp

variable {ι : Qbar l ≃+* ℂ} {d : ℕ} {U : Submodule ℂ (UA E a → ℂ)}

def Plan.ExpAt (P : Plan ι d U) (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ τ : E →+* ℂ, OverPl ι τ v → ∃ σ : ℂ ≃+* ℂ, (∀ i y, σ (τ (P.e y)) = P.D.tau i y) ∧
    ∀ lam, HasWeightAt U τ lam → ∀ j ∈ GlobalTheory.RoadWGeo.wtJumps lam, ∃ (i₀ : Fin P.D.a) (h : Fin P.G.n → ℕ) (i : Fin P.G.n),
      IsHExp (P.D.tau i₀) (epsOf P.D) (conjWt σ P.lam) h ∧ (h i : ℤ) = j + P.m τ

def Plan.HTFor (P : Plan ι d U) (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  P.κ.UnrAt v ∧ (∃ 𝔴, IsPl P.e v 𝔴 ∧ GoodGrp P.g P.θ 𝔴) ∧ P.ExpAt v

def Plan.CongAll (P : Plan ι d U) (w : HeightOneSpectrum (𝓞 E)) : Prop := ∀ B, SatU U w B → CongP ι a P.e P.g P.θ P.κ w B

end

def PlanEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a : ℕ), Odd a → ∀ d : ℕ, FieldOK E l d → ∀ x : E, x ^ 2 = -(d : E) →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → Apart v' w₀ → OneK x w₀ v' →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))) (U : Submodule ℂ (UA E a → ℂ)), AutOffT T U → GlobalTheory.CongW.TyEll E l a w₀ U → SphOffU w₀ S U →
    (∃ B, SatU U v' B) →
    (∃ P : Plan ι d U, P.HTFor v') ∧
    (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → (∃ B, SatU U w B) → ∃ P : Plan ι d U, P.HTFor v' ∧ P.CongAll w) ∧
    ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → OneK x w v' → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) →
      (∃ P : Plan ι d U, P.HTFor v' ∧ P.HTFor w) ∧ ∃ P : Plan ι d U, P.HTFor v' ∧ P.CongAll w

structure KSAll : Prop where
  std : StdEx
  ex : KSEx
  nice : KSNice
  good : KSGood
  cong : KSCong
  hodge : KSHodge

theorem Plan.pack (h : KSAll) {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}
    {ι : Qbar l ≃+* ℂ} {d : ℕ} {U : Submodule ℂ (UA E a → ℂ)} (P : Plan ι d U) :
    ∃ Q : Pack ι d U, (∀ v, P.HTFor v → Q.HTFor v) ∧ ∀ w, P.CongAll w → Q.CongAll w := by
  obtain ⟨gb, hgb⟩ := h.std P.p P.D P.sc.a1 E P.e
  obtain ⟨k, hk⟩ := h.hodge P.p P.D P.G P.L P.sc P.lam P.anti
  obtain ⟨T⟩ := h.ex P.p P.D P.G P.L P.sc E gb k
  have hc : ∀ w B, CongP ι a P.e P.g P.θ P.κ w B → CongFor ι a (T.tower P.N P.g) P.θ P.κ w B := by
    rintro w B ⟨hu, 𝔴, ϑ, h1, h2, h3⟩
    refine ⟨hu, ϑ, ?_, h3⟩
    have := h.cong P.p P.D P.G P.L P.sc E P.e gb hgb k T P.N P.J _ P.g P.θ w 𝔴 h1 ϑ h2
    rwa [P.n_eq] at this
  refine ⟨⟨T.tower P.N P.g, P.θ, P.κ, P.m, h.nice P.p P.D P.G P.L P.sc E gb k T P.N P.J P.g, P.alg, ?_⟩, ?_,
    fun w hw B hB => hc w B (hw B hB)⟩
  · obtain ⟨X, hX⟩ := P.cong
    exact ⟨X, fun w h1 h2 h3 B hB => hc w B (hX w h1 h2 h3 B hB)⟩
  · rintro v ⟨hu, ⟨𝔴, h1, h2⟩, h3⟩
    refine ⟨hu, h.good P.p P.D P.G P.L P.sc E P.e gb hgb k T P.N P.J _ P.g P.θ v 𝔴 h1 h2, fun τ hτ => ?_⟩
    obtain ⟨σ, hσ, h4⟩ := h3 τ hτ
    refine ⟨σ, fun lam hl j hj => ?_⟩
    obtain ⟨i₀, hh, i, h5, h6⟩ := h4 lam hl j hj
    refine ⟨hh i, h6, hk E gb T P.N P.J P.g _ P.f P.fn P.spec (σ.toRingHom.comp τ) ?_ (fun i c => ?_) σ i₀ hh h5 i⟩
    · rw [hgb.1]
      exact (hσ i₀ _).trans (P.D.tau_ω i₀)
    · rw [hgb.2]
      exact hσ i _

theorem packEx_of (h : KSAll) (hP : PlanEx) : PackEx := by
  intro E _ _ _ l _ ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph
  obtain ⟨⟨P, hP0⟩, hA, hB⟩ := hP E l ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph
  refine ⟨?_, fun w hw hl hs => ?_, fun w hl hk ha0 hav hs => ?_⟩
  · obtain ⟨Q, h1, -⟩ := P.pack h
    exact ⟨Q, h1 _ hP0⟩
  · obtain ⟨P, a1, a2⟩ := hA w hw hl hs
    obtain ⟨Q, h1, h2⟩ := P.pack h
    exact ⟨Q, h1 _ a1, h2 _ a2⟩
  · obtain ⟨⟨P, a1, a2⟩, P', b1, b2⟩ := hB w hl hk ha0 hav hs
    obtain ⟨Q, h1, -⟩ := P.pack h
    obtain ⟨Q', h1', h2'⟩ := P'.pack h
    exact ⟨⟨Q, h1 _ a1, h1 _ a2⟩, Q', h1' _ b1, h2' _ b2⟩

end UpperTheory.Gal.Int.Geo

end
