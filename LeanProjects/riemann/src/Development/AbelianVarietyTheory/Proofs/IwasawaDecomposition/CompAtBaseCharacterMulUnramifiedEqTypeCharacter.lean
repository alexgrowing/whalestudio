import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceComponentHeckeCharResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharactersTypePlacesEqLocalComponentsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TypeCharRead

variable {K : Type} [Field K] [NumberField K]

theorem isUnit_of_val_eq_one (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletionIntegers K)
    (h : Valued.v (x : v.adicCompletion K) = 1) : IsUnit x :=
  (Valuation.integer.integers (Valued.v (R := v.adicCompletion K))).isUnit_iff_valuation_eq_one.2 h

theorem red_eq_zero_of_val_lt_one (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (x : v.adicCompletionIntegers K)
    (hx : Valued.v (x : v.adicCompletion K) < 1) : red x = 0 := by
  by_contra h
  have ht : (red x)⁻¹ * red x = 1 := inv_mul_cancel₀ h
  set n : ℕ := ((red x)⁻¹ : ZMod p).val with hn
  set z : v.adicCompletionIntegers K := 1 - (n : v.adicCompletionIntegers K) * x with hz
  have hrz : red z = 0 := by
    rw [hz, map_sub, map_mul, map_one, map_natCast, hn, ZMod.natCast_zmod_val, ht, sub_self]
  have hnv : Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (n : v.adicCompletionIntegers K).2
  have hlt : Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K) * (x : v.adicCompletion K)) < 1 := by
    rw [map_mul]
    calc Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K)) * Valued.v (x : v.adicCompletion K)
        ≤ 1 * Valued.v (x : v.adicCompletion K) := by gcongr
      _ < 1 := by rw [one_mul]; exact hx
  have hvz : Valued.v (z : v.adicCompletion K) = 1 := by
    have e : (z : v.adicCompletion K) = 1 - ((n : v.adicCompletionIntegers K) : v.adicCompletion K) * (x : v.adicCompletion K) := by
      rw [hz]; push_cast; rfl
    rw [e]
    exact Valuation.map_one_sub_of_lt _ hlt
  have hu := (isUnit_of_val_eq_one v z hvz).map red
  rw [hrz] at hu
  exact not_isUnit_zero hu

end GlobalTheory.TypeCharRead

open Formalism.L2.DIV (kP)
open Formalism.IndefR.Links (IsRes)

namespace GlobalTheory.TypeCharRead

theorem compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf →
    ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
    (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    ∀ χ : HChar D.host.E, χ.UnrAt s.w →
    ∀ red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1),
    ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt (cf.mu0 j * χ) s ξ ∧
      ∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
        (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
          ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ (j.1 + 1) kv hy.unit : (↥D.LL0)ˣ) : ↥D.LL0) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv s hsw χ hχ red
  haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D 0
  obtain ⟨φ, hφs, hφ0, hφa, -⟩ := h4 s
  have hker : RingHom.ker φ ≤ RingHom.ker red := fun x hx =>
    (RingHom.mem_ker).2 (red_eq_zero_of_val_lt_one s.v red x ((hφ0 x).1 ((RingHom.mem_ker).1 hx)))
  set ι := φ.liftOfSurjective hφs ⟨red, hker⟩ with hι
  have hιφ : ∀ x, ι (φ x) = red x := fun x => RingHom.liftOfSurjective_comp_apply φ hφs ⟨red, hker⟩ x
  have hred0 : ∀ x, red x = 0 → Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 := by
    intro x hx
    refine lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2) (fun h1 => ?_)
    have hu := (isUnit_of_val_eq_one s.v x h1).map red
    rw [hx] at hu
    exact not_isUnit_zero hu
  let c : (kP s.w)ˣ →* ℂˣ :=
    (Units.map (embLL0 D).toMonoidHom).comp ((τ (j.1 + 1) kv).comp (Units.map ι.toMonoidHom))
  have hres : IsRes (cf.mu0 j * χ) s.w c := by
    intro a k u hk hu
    have ha : a ∉ s.w.asIdeal := by
      intro hm
      have : (u : kP s.w) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact u.ne_zero this
    have ha0 : ((a : 𝓞 D.host.E) : D.host.E) ≠ 0 := hk ▸ k.ne_zero
    obtain ⟨hia, hφia⟩ := hφa a
    set x : (ZMod (D.host.g kv.1))ˣ := Units.map ι.toMonoidHom u with hx
    have hxv : (x : ZMod (D.host.g kv.1)) = red ⟨_, hia⟩ := by
      show ι (u : kP s.w) = _
      rw [hu, ← hφia, hιφ]
    have hmem : (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a) ∈ (NX.pG D kv).asIdeal := by
      rw [← hsw]
      obtain ⟨hib, hφib⟩ := hφa (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφib]
      apply (hφ0 _).2
      apply hred0
      have e : (⟨_, hib⟩ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) =
          (((x : ZMod (D.host.g kv.1)).val : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) - ⟨_, hia⟩ := by
        apply Subtype.ext
        show s.i (((((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a : 𝓞 D.host.E)) : D.host.E) = _
        push_cast
        rw [map_sub, map_natCast]
      rw [e, map_sub, map_natCast, ZMod.natCast_zmod_val, hxv, sub_self]
    have h61 := GlobalTheory.T.levelCharacters_typePlaces_eq_local_components hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv x a ha0 hmem
    have hunit : IsUnitAt s.w (atFin s.w k) := by
      have e := GlobalTheory.ChainOnto.TameRes.val_alg s.w (k : D.host.E)
      show Valued.v (algebraMap D.host.E (s.w.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [e, hk]
      exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem s.w a ha
    have h2 : χ.locK s.w k = 1 := hχ _ hunit
    have hk' : Units.mk0 ((a : 𝓞 D.host.E) : D.host.E) ha0 = k := Units.ext hk.symm
    rw [hk', ← hsw] at h61
    apply Units.ext
    have e : (cf.mu0 j * χ).locK s.w k = (cf.mu0 j).locK s.w k * χ.locK s.w k := rfl
    rw [e, h2, mul_one, ← h61]
    rfl
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.exists_splitPlaceComponent_heckeChar_residue D s φ hφs hφ0 hφa _ c hres
  refine ⟨ξ, hξc, fun y hy uu huu => ?_⟩
  have hyv : Valued.v (y : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by
    refine le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2) (not_lt.1 fun hlt => ?_)
    have h0 := red_eq_zero_of_val_lt_one s.v red y hlt
    rw [h0] at hy
    exact not_isUnit_zero hy
  have hyu : IsUnit (φ y) := (isUnit_of_val_eq_one s.v y hyv).map φ
  rw [hξr uu y hyu.unit huu.symm hyu.unit_spec.symm]
  have hw : Units.map ι.toMonoidHom hyu.unit = hy.unit := by
    apply Units.ext
    show ι ((hyu.unit : kP s.w)) = red y
    rw [hyu.unit_spec, hιφ]
  show (embLL0 D) ((τ (j.1 + 1) kv (Units.map ι.toMonoidHom hyu.unit) : (↥D.LL0)ˣ) : ↥D.LL0) = _
  rw [hw]

end GlobalTheory.TypeCharRead

end
