import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.Gen.BaseChange (down exists_gObjMap_pull spMap_comp')
open UpperTheory.Gal.Int.Geo (IsTrans)
open UpperTheory.Gal.LocalSmoothExtension

private theorem objMap_along {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj b N s'} {o : GObj b N s} {f g : S' ⟶ S}
    (e : f = g) (n : GObjMap o' o f) : ∃ n' : GObjMap o' o g, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

theorem UpperTheory.Gal.LocalSmoothExtension.legBc_of :
    MapEq → TransPull → LegBc := by
  intro hME hTP p _ D G L R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N N' M M' P P' f f' hf hf' m m' h π o ψ φ hπ hψ
  have hw : (f' ≫ π) ≫ M.s = P'.s ≫ spMap τ := by
    rw [Category.assoc, hπ]
    exact hf'.w
  obtain ⟨π₁, hπf, hπs⟩ : ∃ π₁ : P'.X ⟶ P.X, π₁ ≫ f = f' ≫ π ∧ π₁ ≫ P.s = P'.s :=
    ⟨hf.lift (f' ≫ π) P'.s hw, hf.lift_fst _ _ _, hf.lift_snd _ _ _⟩
  obtain ⟨o₁, ⟨φ₁⟩⟩ : ∃ o₁ : GObj gb₂ N P'.s, Nonempty (GObjMap o₁ P.univ π₁) := by
    have key := exists_gObjMap_pull π₁ P.univ
    rw [hπs] at key
    exact key
  let d₁ : GObj gb₁ N (P'.s ≫ spMap τ) := down hρ ht rfl o₁
  let φd : GObjMap d₁ (down hρ ht rfl P.univ) π₁ :=
    ⟨φ₁.φ, φ₁.φ₂, φ₁.cart, φ₁.sq, φ₁.act, φ₁.pol, φ₁.eta⟩
  obtain ⟨n, hn⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ (down hρ ht rfl P.univ) M.univ π₁ f m).1 φd
  obtain ⟨n', hn'⟩ := objMap_along hπf n
  obtain ⟨m'', hm''⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ o M.univ f' π φ).2 n'
  obtain ⟨ψ₁, hψ₁, hT⟩ := hTP p D G L R₁ gb₁ N N' _ _ M'.s (P'.s ≫ spMap τ) f' hf'.w M'.univ o
    (down hρ ht rfl P'.univ) d₁ m' m'' h ψ hψ
  obtain ⟨t₁, t₂, t₃, t₄, t₅⟩ := hT
  refine ⟨π₁, o₁, ψ₁, φ₁, hπs, ⟨t₁, t₂, t₃, t₄, fun k _ _ t β hβ => ?_⟩, hπf, ?_⟩
  · exact t₅ k t (β.comp τ) (by rw [spMap_comp', ← Category.assoc, hβ])
  · have e : φ₁.φ ≫ m.φ = m''.φ ≫ φ.φ := by
      rw [hm'', hn', hn]
      rfl
    calc (ψ₁.left ≫ φ₁.φ) ≫ m.φ = ψ₁.left ≫ φ₁.φ ≫ m.φ := Category.assoc _ _ _
      _ = ψ₁.left ≫ m''.φ ≫ φ.φ := congrArg (fun z => ψ₁.left ≫ z) e
      _ = (ψ₁.left ≫ m''.φ) ≫ φ.φ := (Category.assoc _ _ _).symm
      _ = m'.φ ≫ ψ.left ≫ φ.φ := by rw [hψ₁, Category.assoc]
