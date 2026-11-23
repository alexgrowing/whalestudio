import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardKerMulCardEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.GWComplex

section Count

variable {R : Type*} [CommRing R] {A B C D E : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E]

theorem card_eq_ker_mul_range (f : A →ₗ[R] B) :
    Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv]

theorem card_five {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D} {k : D →ₗ[R] E}
    (hf : Function.Injective f) (h1 : Function.Exact f g) (h2 : Function.Exact g h)
    (h3 : Function.Exact h k) :
    Nat.card (LinearMap.ker k) * Nat.card B = Nat.card C * Nat.card A := by
  rw [card_eq_ker_mul_range g, card_eq_ker_mul_range h, h1.linearMap_ker_eq,
    h2.linearMap_ker_eq, h3.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv]
  ring

theorem card_comap {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) (L : Submodule R B) :
    Nat.card (L.comap f) =
      Nat.card (LinearMap.ker f) * Nat.card (LinearMap.ker (g.domRestrict L)) := by
  let u : L.comap f →ₗ[R] L := f.restrict (fun _ hx => hx)
  rw [card_eq_ker_mul_range u]
  have e1 : LinearMap.range u = LinearMap.ker (g.domRestrict L) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, h x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨y, by rw [Submodule.mem_comap, hy]; exact x.2⟩, Subtype.ext hy⟩
  have e2 : Nat.card (LinearMap.ker u) = Nat.card (LinearMap.ker f) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [Submodule.mem_comap, LinearMap.mem_ker.1 x.2]; exact L.zero_mem⟩, Subtype.ext x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e1, e2]

theorem card_pi {I : Type*} [Fintype I] {P : I → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] (L : ∀ i, Submodule R (P i)) :
    Nat.card (Submodule.pi Set.univ L) = ∏ i, Nat.card (L i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, x.2 i trivial⟩
      invFun := fun x => ⟨fun i => (x i).1, fun i _ => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Count

theorem arith {k p h2 h0 s i h1 s' q h0' m : ℕ} (a1 : k * p = h2 * h0) (a2 : s = k * i)
    (a3 : i * h1 = s' * q) (a4 : h0' * h2 * m = h1) : s * h0' * p * m = s' * h0 * q := by
  calc s * h0' * p * m = (k * p) * i * h0' * m := by rw [a2]; ring
    _ = i * (h0' * h2 * m) * h0 := by rw [a1]; ring
    _ = s' * h0 * q := by rw [a4, a3]; ring

open PoitouTate in

theorem ker_flip_eq {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Av : S → ValuationSubring Ω}
    {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
    {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
    (hj : ∀ v, Function.Injective (j v))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}
    (hρ : ContAction ρ) (L : LocCond ρ (locFam S Av)) :
    LinearMap.ker ((tr1 S Av μ j ρ hρ).domRestrict (Submodule.pi Set.univ L)).flip =
      Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)
        (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) := by
  classical
  ext y
  rw [mem_Sel, LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [mem_perpCond, LinearMap.flip_apply, LinearMap.domRestrict_apply, poitouTateNineTerm_transgressionOne_apply,
    LinearMap.zero_apply]
  constructor
  · intro h v x hx
    have hm : Pi.single v x ∈ Submodule.pi Set.univ L := fun w _ => by
      by_cases hw : w = v
      · subst hw; rw [Pi.single_eq_same]; exact hx
      · rw [Pi.single_eq_of_ne hw]; exact zero_mem _
    have e := h ⟨_, hm⟩
    rw [Finset.sum_eq_single v (fun w _ hw => by
      rw [Subtype.coe_mk, Pi.single_eq_of_ne hw, map_zero, map_zero]) (by simp),
      Subtype.coe_mk, Pi.single_eq_same] at e
    exact hj v (e.trans (map_zero _).symm)
  · intro h x
    exact Finset.sum_eq_zero fun v _ => by rw [h v _ (x.2 v trivial), map_zero]

open PoitouTate in

theorem greenbergWiles_totallyComplex : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (S : Finset (HeightOneSpectrum (𝓞 F))) (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), 0 < r → ContainsAbove S l → ∀ (hrho : ContAction rhoS) (muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ), muS.comp (toGS Ω _) = cycMod F Ω l r → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond rhoS (locFam S Av), Finite (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) ∧ Finite (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) ∧ Nat.card (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) * Nat.card (H0 (twDual muS rhoS)) * (∏ v : S, Nat.card (H0 (rhoS.comp (locFam S Av v)))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) * Nat.card (H0 rhoS) * ∏ v : S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ r M _ _ _ _ _ S ρ hr hS hρ μ hμ Av hA L
  classical
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  obtain ⟨inv, hinv, h⟩ := hPT F Ω l r hr ζ hζ
  obtain ⟨⟨δ₁, -, h0, h1, h2, h3, h4, -⟩, -⟩ := h S hS Av hA μ hμ M ρ hρ
  have := GlobalTheory.DualSide.finite_TDual_pow (l := l) (r := r) (M := M)
  have hρ' := GlobalTheory.DualSide.contAction_twDual (contAction_charRep hμ) hρ
  obtain ⟨-, f1, -⟩ := hGF F Ω l r M S ρ hr hS hρ
  obtain ⟨-, f1', f2', -⟩ := hGF F Ω l r _ S (twDual μ ρ) hr hS hρ'
  have fl : ∀ v : S, Finite (H1 (ρ.comp (locFam S Av v))) := fun v =>
    (hLF F Ω l r M (Av v) _ v.1 hr (hA v) (hρ.comp' (continuous_locFam S Av v))).2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  have a1 := card_five h0 h1 h2 h3
  rw [GlobalTheory.ZModDual.card_dual_eq, Nat.card_pi] at a1
  have a2 := card_comap h4 (Submodule.pi Set.univ L)
  have e2 : (Submodule.pi Set.univ L).comap (loc1 S Av ρ) =
      Sel ρ (locFam S Av) (continuous_locFam S Av) L := by
    ext x
    rw [mem_Sel]
    exact ⟨fun h v => h v trivial, fun h v _ => h v⟩
  rw [e2] at a2
  have a3 := GlobalTheory.ZModDual.card_ker_mul_card_eq (l ^ r) _ _
    ((tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ).domRestrict (Submodule.pi Set.univ L))
  rw [ker_flip_eq (fun v => (invAt_bijective S Av μ hμ hinv v (hA v)).1), card_pi] at a3
  have a4 := hEC F Ω l r _ S (twDual μ ρ) hr hS hρ' (fun _ => 1)
    (fun w hw => absurd hw (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)))
  have hM : Nat.card (TDual (ZMod (l ^ r)) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq _ _
  rw [archH0Card, Finset.filter_false_of_mem (fun w _ =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)), Finset.prod_empty,
    one_mul, hM, IsTotallyComplex.finrank, two_mul, pow_add, ← mul_assoc] at a4
  have a5 := Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos _) a4
  exact arith a1 a2 a3 a5

end GlobalTheory.GWComplex
