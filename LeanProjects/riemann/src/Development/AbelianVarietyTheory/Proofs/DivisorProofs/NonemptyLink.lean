import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM

namespace GlobalTheory.GenDeg

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {O : Type} [CommRing O] {β : O →+* i₀.c.F}

structure Link (Z : LocM.Mdl Y i₀) (T : Model (Xo i₀.l) i₀.c β) : Type 1 where

  τ : (Y Z.i).X ⟶ (Y i₀).X

  mu : SABMap (Y Z.i).t (Y i₀).t τ

  trans : IsTrans i₀ Z.i τ mu

  h : gen T ⟶ (Y i₀).X

  tg : SAB H (gen T)

  m₁ : SABMap tg T.t (genι T)

  m₂ : SABMap tg (Y i₀).t h

  jQ_h : T.jQ ≫ h = (Y i₀).j

  h_s : h ≫ (Y i₀).s = genStr T ≫ spMap (i₀.c.V W).subtype

variable {Z : LocM.Mdl Y i₀} {T : Model (Xo i₀.l) i₀.c β}

def Link.Match (L : Link Z T) {F : Type} [Field F] {e : F ≃+* i₀.c.F} (C : FlagCpt T e) {k : Type} [Field k]
    (w : Sp k ⟶ Z.X) (q : Sp k ⟶ C.Y.X) : Prop :=
  ∃ (x : Sp k ⟶ (Xo i₀.l).XF i₀.c) (u : Vecs Dw (Y Z.i).t k) (φ : i₀.c.F →+* k) (g : EigFrame T φ ((q ≫ C.π) ≫ genι T)),
    w ≫ Z.π ≫ L.τ = x ≫ (Y i₀).j ∧ q ≫ C.π = x ≫ T.jQ ∧ x ≫ pullback.snd _ _ = spMap φ ∧ Z.FlagAt w u ∧ C.Carries q g ∧
    ∀ σ j, ∃ v : Sp (DualNumber k) ⟶ L.tg.G.left,
      IsTanAtG L.tg (q ≫ C.π) v ∧ v ≫ L.m₁.φ = g.v σ j ∧ v ≫ L.m₂.φ = u σ j ≫ L.mu.φ

def FlagExt (z : admitted Y i₀) : Prop :=
  ∀ x : z.Z.X, z.Z.inQ x → ∃ (f : z.Z.i.c.F →+* z.Z.X.presheaf.stalk x) (u : Vecs Dw (Y z.Z.i).t (z.Z.X.presheaf.stalk x)),
    z.Z.X.fromSpecStalk x ≫ z.Z.s = spMap (f.comp (z.Z.i.c.V W).subtype) ∧
    LocM.IsFrame (Y z.Z.i).t f (z.Z.X.fromSpecStalk x ≫ z.Z.π) u ∧
    ∀ (ℓ : Letter Dw) (h : letterOf Dw (.inl (ℓ.1, ℓ.2)) = some ℓ) (i : Fin (z.line false _ ℓ h).L.n),
      x ∈ (z.line false _ ℓ h).L.U i → ∃ ε : (z.Z.X.presheaf.stalk x)ˣ,
        ∀ (k : Type) [Field k] (ψ : z.Z.X.presheaf.stalk x →+* k) (a : Fin z.Z.m) (φ : Γ(z.Z.X, (z.Z.U a).1) →+* k),
          Function.Injective ψ → spMap ψ ≫ z.Z.X.fromSpecStalk x = spMap φ ≫ z.Z.chart a →
          ∃ cf : Fin (Dw.mult ℓ.1) → k,
            cf ℓ.2 = ψ ε * valF (spMap φ ≫ z.Z.chart a) _ ((z.line false _ ℓ h).r a i).val ∧ (∀ m, ℓ.2 < m → cf m = 0) ∧
            IsCombAtG (Y z.Z.i).t (spMap φ ≫ z.Z.chart a ≫ z.Z.π) ((z.Z.fr a).bc φ ℓ.1) cf (u.bc ψ ℓ.1 ℓ.2)

end Free

theorem nonempty_link {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) {p : ℕ} (hp : p.Prime)
    {W : ValuationSubring ℂ} (hW : (p : ℂ) ∈ W.nonunits)
    (Z : LocM.Mdl (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩) : Nonempty (Link Z s.T.Z) := by
  obtain ⟨τ, mu, hτ⟩ := exists_isTrans (S.sys.clauses p W hp hW).1 Z.dvd Z.le
  let b : 𝓞 κ.c.F →+* κ.c.V W := (algebraMap (𝓞 κ.c.F) κ.c.F).codRestrict (κ.c.V W) fun x => by
    have hx : IsIntegral ℤ (x : κ.c.F) := x.2
    have h₂ : IsIntegral (κ.c.V W) (x : κ.c.F) := hx.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₂
    exact (show ((y : κ.c.V W) : κ.c.F) = algebraMap _ _ x from hy) ▸ y.2
  have hb : spMap (κ.c.V W).subtype ≫ spMap b = spMap (algebraMap (𝓞 κ.c.F) κ.c.F) := (Spec.map_comp _ _).symm
  obtain ⟨f, t, n₁, n₂, hf, hj, -⟩ := s.glob.2.1 p W hp hW b fun _ => rfl
  let k : gen s.T.Z ⟶ pullback s.Ygl.s (spMap b) :=
    pullback.lift (genι s.T.Z ≫ s.T.b) (genStr s.T.Z ≫ spMap (κ.c.V W).subtype) (by
      rw [Category.assoc, s.T.b_s, Category.assoc, hb]
      exact pullback.condition)
  have hk : k ≫ pullback.fst _ _ = genι s.T.Z ≫ s.T.b := pullback.lift_fst _ _ _
  obtain ⟨tg, ⟨m⟩⟩ := exists_sab k t
  obtain ⟨m₂, -⟩ := GlobalTheory.LevelCover.sab_comp m n₂ rfl
  obtain ⟨n, -⟩ := GlobalTheory.LevelCover.sab_comp m n₁ hk
  obtain ⟨m₁, -⟩ := GlobalTheory.LevelCover.sab_cancel s.T.pull n (genι s.T.Z) rfl
  refine ⟨⟨τ, mu, hτ, k ≫ f, tg, m₁, m₂, ?_, ?_⟩⟩
  · rw [← Category.assoc]
    refine hj _ ?_
    rw [Category.assoc, hk, ← Category.assoc]
    exact s.T.j_b
  · exact (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) hf).trans (pullback.lift_snd _ _ _))

end GlobalTheory.GenDeg
