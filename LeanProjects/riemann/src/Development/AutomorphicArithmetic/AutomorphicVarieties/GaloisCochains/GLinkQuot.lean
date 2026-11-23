import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.V.GC

structure Hypotheses₂ : Prop extends X.HcPublished where
  uo : UnramifiedOrthogonality
  gw : GreenbergWiles

def eqHom {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (D J : Subgroup Γ) : Submodule k (J → M) where
  carrier := {f | IsLocallyConstant f ∧ (∀ a b, f (a * b) = f a + f b) ∧
    ∀ d ∈ D, ∀ j j' : J, j'.1 = d * j.1 * d⁻¹ → f j' = ρ d (f j)}
  zero_mem' := ⟨IsLocallyConstant.const _, by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun x y => by simp only [Pi.add_apply, ha.2.1, hb.2.1]; abel,
    fun d hd j j' h => by simp [ha.2.2 d hd j j' h, hb.2.2 d hd j j' h]⟩
  smul_mem' c a ha := ⟨ha.1.comp (c • ·), fun x y => by simp [ha.2.1], fun d hd j j' h => by simp [ha.2.2 d hd j j' h]⟩

variable (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]

def cycF (k : Type) [Field k] [CharP k l] : G F Ω →* kˣ :=
  (Units.map (ZMod.castHom (dvd_pow_self l one_ne_zero) k).toMonoidHom).comp (cycMod F Ω l 1)

variable {F Ω}

def clRk (U : Subgroup (G F Ω)) : Cardinal := Module.rank (ZMod l) (Kum.XDual 1 U (ZMod l) (ZMod l))

def tameN (S : Set (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) : Subgroup (G F Ω) :=
  (Subgroup.normalClosure (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v},
    ((Ine (F := F) A ⊓ K : Subgroup (G F Ω)) : Set (G F Ω)))).topologicalClosure

structure GLink (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (π : G F Ω →* Γ) : Prop where
  odd : l ≠ 2
  above : ContainsAbove S l
  normal : K.Normal
  isOpen : IsOpen (K : Set (G F Ω))
  idx : ¬ l ∣ K.index
  cont : Continuous π
  onto : Function.Surjective π
  ker : π.ker = tameN (S : Set (HeightOneSpectrum (𝓞 F))) K

structure LLink {V : Type} {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] (ι : ∀ v, Gv v →* G F Ω)
    (A : V → ValuationSubring Ω) (pl : V → HeightOneSpectrum (𝓞 F)) : Prop where
  isOver : ∀ v, IsPlaceOver (A v) (pl v)
  inj : Function.Injective pl
  mem : ∀ w, w ∈ Set.range pl ↔ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
  cont : ∀ v, Continuous (ι v)
  ι_inj : ∀ v, Function.Injective (ι v)
  range : ∀ v, (ι v).range = Dec (F := F) (A v)

structure FLink {k : Type} [Field k] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω))
    (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F))
    (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω) : Prop where
  real : IsTotallyReal F
  g : GLink l S K π
  only : ∀ w ∈ S, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
  loc : LLink l ι A pl
  loc_eq : ∀ v s, Φ.loc v s = π (ι v s)
  ine : ∀ v, Φ.Iv v = (Ine (F := F) (A v)).comap (ι v)
  dv : ∀ v, Φ.dv v = locDeg (pl v)
  eps : ∀ g, Φ.eps (π g) = cycZ F Ω l g
  cc : ∀ w, IsCCAt (e w) (c w)
  cw : ∀ w, Φ.cw w = π (c w)
  del_open : IsOpen (Φ.del.ker : Set Φ.Γ)
  del_c : Φ.del Φ.c = -1
  K_del : ∀ g ∈ K, Φ.del (π g) = 1
  K_Ψ : ∀ g ∈ K, Φ.Ψ (π g) = 1

theorem gLink_quot (hl : l ≠ 2) {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ContainsAbove S l) {K : Subgroup (G F Ω)}
    (h1 : K.Normal) (h2 : IsOpen (K : Set (G F Ω))) (h3 : ¬ l ∣ K.index)
    [(tameN (S : Set (HeightOneSpectrum (𝓞 F))) K).Normal] :
    GLink l S K (QuotientGroup.mk' (tameN (S : Set (HeightOneSpectrum (𝓞 F))) K)) := by
  refine ⟨hl, hS, h1, h2, h3, ?_, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩
  exact continuous_quot_mk

end UpperTheory.V.GC

end
