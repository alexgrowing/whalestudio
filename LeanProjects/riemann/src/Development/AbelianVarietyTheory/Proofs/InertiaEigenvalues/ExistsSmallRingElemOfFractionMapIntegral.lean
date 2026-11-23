import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemDecIsFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryPlaceFamilyAtLevelMono
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem exists_small_ring_elem_of_fraction_map_integral {D : D7} (X : NTw D.R D.host D.what₂ D.LL0 D.nd) (i : X.Tw) (z : FractionRing (X.O0 i))
    (y : X.O i) (h : fracMap X i z = algebraMap (X.O i) (FractionRing (X.O i)) y) :
    ∃ a : X.O0 i, algebraMap (X.O0 i) (FractionRing (X.O0 i)) a = z := by
  haveI := GlobalTheory.TwistChoice.isLocalHom_O (X := X) i
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger (X.O0 i) z with ⟨a, e⟩ | ⟨c, e⟩
  · exact ⟨a, e⟩
  · by_cases hc : IsUnit c
    · obtain ⟨u, rfl⟩ := hc
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap (X.O0 i) (FractionRing (X.O0 i)) (u : X.O0 i) *
          algebraMap (X.O0 i) (FractionRing (X.O0 i)) ((u⁻¹ : (X.O0 i)ˣ) : X.O0 i) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [e] at h1
      rw [← inv_inv z]
      exact (eq_inv_of_mul_eq_one_right h1)
    · exfalso
      have e2 : algebraMap (X.O i) (FractionRing (X.O i)) (y * algebraMap (X.O0 i) (X.O i) c) = 1 := by
        rw [map_mul, ← h, ← fracMap_algebraMap, ← map_mul, e, mul_inv_cancel₀ hz, map_one]
      have e3 : y * algebraMap (X.O0 i) (X.O i) c = 1 :=
        IsFractionRing.injective (X.O i) (FractionRing (X.O i)) (by rw [e2, map_one])
      exact hc (isUnit_of_map_unit (algebraMap (X.O0 i) (X.O i)) c (isUnit_iff_exists_inv.2 ⟨y, by rw [mul_comm]; exact e3⟩))

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem delAt_unr {D : D7} (cf : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hS : P ∉ D.ntw.S0 i) :
    (cf.delAt (D.ntw.l i)).UnrAt P := by
  have hD : P ∉ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := fun h =>
    hS (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq i]; exact h))
  unfold CharFrame.delAt
  split_ifs with h
  · rw [if_pos h] at hD
    exact cf.isDel'.unr P hD
  · rw [if_neg h] at hD
    exact cf.isDel.unr P hD

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem toC_delta {D : D7} (cf : CharFrame D) (i : D.ntw.Tw) {b : Bool} (ρ : GlobalTheory.Triple.Reading D.ntw i b)
    {P : PlE D.host} (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (xd : D.LL0)
    (hxd : D.what₂.embLL (xd : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val P)⁻¹ : ℂˣ).1)
    (hdel : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) =
      D.ntw.emb0 i xd) :
    ρ.toC (((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ)) : D.ntw.O0 i) =
      (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)⁻¹ := by
  set δ : ℂ := (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) with hδ
  have hδ0 : δ ≠ 0 := Units.ne_zero _
  have hz : ‖δ‖ = 1 := cf.delAt_unitary _ _
  rw [Units.val_inv_eq_inv_val] at hxd
  have hread : ρ.toC ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = ρ.ι (ρ.κ (D.ntw.emb0 i xd)) := by
    rw [Reading.toC_apply, ← hdel]; rfl
  cases b
  ·
    have hx0 : (xd : D.what₂.LL) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxd; exact inv_ne_zero hδ0 hxd.symm
    have hstar : ((xd⁻¹ : D.LL0) : D.what₂.LL) = star (xd : D.what₂.LL) := by
      apply D.what₂.embLL.injective
      rw [D.starLL_cx, hxd, ← Complex.inv_eq_conj (by rw [norm_inv, hz, inv_one]), inv_inv]
      rw [IntermediateField.coe_inv, map_inv₀, hxd, inv_inv]
    have e : D.ntw.emb0 i xd = D.ntw.emb0b i xd⁻¹ := (D.ntw.restX_coefficientEmbedding_conj i xd⁻¹ xd ?_).symm
    · have h1 := ρ.read xd⁻¹
      simp only [embSide, Bool.false_eq_true, if_false] at h1
      simp only [Bool.false_eq_true, if_false]
      rw [map_units_inv, hread, e, h1]
      show (D.what₂.embLL ((xd⁻¹ : D.LL0) : D.what₂.LL))⁻¹ = δ⁻¹
      rw [IntermediateField.coe_inv, map_inv₀, hxd, inv_inv]
    · rw [hstar, star_star]
  · have h1 := ρ.read xd
    simp only [embSide, if_true] at h1
    simp only [if_true, hread, h1]
    exact hxd

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem hEig_eq_heckeVal : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → EigTrue D cf Rw Sb eig → ∀ i (s : D.ntw.Sig i) (ρ : GlobalTheory.Triple.Reading D.ntw i (D.ntw.side i s)) (π : D.naut.CG D.R.r), GlobalTheory.EigTie.IsRowPar Rw (Bs.rowS i s) π → ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → ∃ x : D.ntw.O0 i, algebraMap (D.ntw.O0 i) (D.ntw.O i) x = D.ntw.hEig i s k P ∧ ρ.toC x = GlobalTheory.Triple.heckeVal (GlobalTheory.Triple.muBase cf (D.ntw.l i) (GlobalTheory.Triple.jIdx s)) π k P := by
  intro D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hπ k P hk hP hS
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact ⟨1, by rw [map_one, Bs.hEig_zero], by rw [map_one, heckeVal_zero]⟩
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hS (D.ntw.twistExcludedPlaces_contains_residueChar i h)
  obtain ⟨xd, hxd, hdel⟩ := Bs.deltaRead i P hl (delAt_unr cf i hS) _ σ (D.nd.plOm.2 P) hσ
  set u : (D.ntw.O0 i)ˣ := if D.ntw.side i s then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ with hu
  have hc : Bs.cHk i (D.ntw.side i s) P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom u :=
    Bs.cHk_del i (D.ntw.side i s) P hS σ hσ
  set e : ↥D.LL0 := eig (D.ntw.jS i s) (Bs.rowS i s) k P with he
  set z : FractionRing (D.ntw.O0 i) := embSide D.ntw i (D.ntw.side i s) e with hz
  have hrow := Bs.rowS_eig i s k P hk1 hk hP hS
  have hread : (show FractionRing (D.ntw.O i) from readLL0 S i (D.ntw.side i s) e) = fracMap D.ntw i z := rfl
  rw [hread, hc] at hrow
  set A : D.ntw.O0 i →+* FractionRing (D.ntw.O i) :=
    (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)) with hA
  have hcu : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      ((Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom u : (D.ntw.O i)ˣ) : D.ntw.O i) = A u := rfl
  rw [hcu] at hrow
  have hAu : A (u : D.ntw.O0 i) * A ((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]

  have hzO : fracMap D.ntw i z = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      (D.ntw.hEig i s k P * algebraMap (D.ntw.O0 i) (D.ntw.O i) (((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ k)) := by
    rw [map_mul, hrow, map_pow, map_pow]
    change _ = A (u : D.ntw.O0 i) ^ k * fracMap D.ntw i z * A ((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ k
    rw [mul_comm _ (fracMap D.ntw i z), mul_assoc, ← mul_pow, hAu, one_pow, mul_one]
  obtain ⟨a, ha⟩ := exists_small_ring_elem_of_fraction_map_integral D.ntw i z _ hzO
  refine ⟨(u : D.ntw.O0 i) ^ k * a, ?_, ?_⟩
  · apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
    rw [hrow, ← fracMap_algebraMap, map_mul, map_mul, ha, map_pow, map_pow, fracMap_algebraMap]
    rfl
  · have hloc : D.naut.locG π P = Rw.locR (Bs.rowS i s) P := hπ.2 P hP
    obtain ⟨hocc, hgood, -⟩ := Bs.rhoS i s
    have hocc' : D.what₂.isot ((jIdx s).1 + 1) (Bs.rowS i s) ≠ ⊥ := by rwa [jIdx_add_one]
    have hET' := (hET (jIdx s) (Bs.rowS i s) hocc' hgood P hP (fun h => hS (hSb i h))).2 k hk1 hk
    rw [jIdx_add_one] at hET'
    have hδ : ρ.toC (u : D.ntw.O0 i) = _ := toC_delta cf i ρ σ xd hxd hdel
    have hae : ρ.toC a = D.what₂.embLL (e : D.what₂.LL) := by
      rw [Reading.toC_apply]
      change ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) a)) = _
      rw [ha, hz, ρ.read]
      rfl
    rw [map_mul, map_pow, hδ, hae, he, hET', heckeVal, satake, hloc, muBase, HChar.val_mul, Units.val_mul]
    set q : ℂ := ((normV P : ℕ) : ℂ)
    set c : ℂ := (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)⁻¹
    have hmap : (D.naut.frobEig (Rw.locR (Bs.rowS i s) P)).map (fun a =>
        a⁻¹ * ((((cf.mu0 (jIdx s)).val P : ℂˣ) : ℂ) * (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ))⁻¹ * (q ^ (D.R.nV / 2))⁻¹) =
        ((D.naut.frobEig (Rw.locR (Bs.rowS i s) P)).map (fun a =>
          a⁻¹ * (((cf.mu0 (jIdx s)).val P : ℂˣ) : ℂ)⁻¹ * (q ^ (D.R.nV / 2))⁻¹)).map (fun y => c • y) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun a _ => ?_
      simp only [Function.comp_apply, smul_eq_mul, c, mul_inv]
      ring
    rw [hmap, ← Multiset.pow_smul_esymm, smul_eq_mul]
    ring

end GlobalTheory.TwInputs.HEig
