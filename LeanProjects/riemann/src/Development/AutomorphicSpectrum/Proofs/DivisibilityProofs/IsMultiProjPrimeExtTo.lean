import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.ZpModel

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} (ι : K → Type) (p : Nat.Primes)

abbrev consts : Submonoid (MRing ι ℤ) :=
  (Ideal.span {((p : ℕ) : ℤ)}).primeCompl.map (C : ℤ →+* MRing ι ℤ)

theorem isLocalization_consts : IsLocalization (consts ι p) (MRing ι (ZP p)) :=
  MvPolynomial.isLocalization _ _

attribute [local instance] isLocalization_consts

theorem algebraMap_eq :
    algebraMap (MRing ι ℤ) (MRing ι (ZP p)) = MvPolynomial.map (Int.castRingHom (ZP p)) := by
  have h : algebraMap ℤ (ZP p) = Int.castRingHom (ZP p) := RingHom.ext_int _ _
  rw [← h]
  rfl

variable {ι} {P : Ideal (MRing ι ℤ)}

theorem disjoint_consts (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) :
    Disjoint (consts ι p : Set (MRing ι ℤ)) (P : Set (MRing ι ℤ)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨a, ha, rfl⟩ hmem
  have h0 : a ∈ P.comap (C : ℤ →+* MRing ι ℤ) := hmem
  rw [hC] at h0
  have h1 : a = 0 := (Submodule.mem_bot _).1 h0
  subst h1
  exact ha (Ideal.zero_mem _)

theorem extTo_eq (P : Ideal (MRing ι ℤ)) :
    extTo (ZP p) P = P.map (algebraMap (MRing ι ℤ) (MRing ι (ZP p))) := by
  rw [algebraMap_eq]
  rfl

theorem isPrime_extTo (hP : P.IsPrime) (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) :
    (extTo (ZP p) P).IsPrime := by
  rw [extTo_eq]
  exact IsLocalization.isPrime_of_isPrime_disjoint (consts ι p) _ P hP (disjoint_consts p hC)

theorem comap_extTo (hP : P.IsPrime) (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) :
    (extTo (ZP p) P).comap (MvPolynomial.map (Int.castRingHom (ZP p))) = P := by
  have h := IsLocalization.under_map_of_isPrime_disjoint (consts ι p) (MRing ι (ZP p)) hP
    (disjoint_consts p hC)
  rw [extTo_eq, ← algebraMap_eq]
  exact h

theorem mem_of_map_mem (hP : P.IsPrime) (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥)
    {f : MRing ι ℤ} (h : MvPolynomial.map (Int.castRingHom (ZP p)) f ∈ extTo (ZP p) P) : f ∈ P :=
  (comap_extTo p hP hC).le h

theorem comap_C_extTo (hP : P.IsPrime) (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) :
    (extTo (ZP p) P).comap (C : ZP p →+* MRing ι (ZP p)) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (Ideal.span {((p : ℕ) : ℤ)}).primeCompl a
  have hs' : a * algebraMap ℤ (ZP p) s = algebraMap ℤ (ZP p) n := hs
  have h1 : (C (algebraMap ℤ (ZP p) n) : MRing ι (ZP p)) ∈ extTo (ZP p) P := by
    rw [← hs', C_mul]
    exact Ideal.mul_mem_right _ _ ha
  have h2 : MvPolynomial.map (Int.castRingHom (ZP p)) (C n : MRing ι ℤ) ∈ extTo (ZP p) P := by
    rw [map_C]
    have e : Int.castRingHom (ZP p) n = algebraMap ℤ (ZP p) n := by simp
    rwa [e]
  have h3 : n ∈ P.comap (C : ℤ →+* MRing ι ℤ) := mem_of_map_mem p hP hC h2
  rw [hC] at h3
  have h4 : n = 0 := (Submodule.mem_bot _).1 h3
  subst h4
  rw [map_zero] at hs'
  have hu : algebraMap ℤ (ZP p) s ≠ 0 := (IsLocalization.map_units (ZP p) s).ne_zero
  exact (Submodule.mem_bot _).2 ((mul_eq_zero.1 hs').resolve_right hu)

theorem isRelevant_extTo (hP : P.IsPrime) (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥)
    (hR : IsRelevant P) : IsRelevant (extTo (ZP p) P) := by
  intro k
  obtain ⟨i, hi⟩ := hR k
  refine ⟨i, fun h => hi (mem_of_map_mem p hP hC ?_)⟩
  rwa [map_X]

def quotHom (P : Ideal (MRing ι ℤ)) : (MRing ι ℤ ⧸ P) →+* (MRing ι (ZP p) ⧸ extTo (ZP p) P) :=
  Ideal.quotientMap _ (MvPolynomial.map (Int.castRingHom (ZP p))) Ideal.le_comap_map

theorem dim_le (P : Ideal (MRing ι ℤ)) :
    ringKrullDim (MRing ι (ZP p) ⧸ extTo (ZP p) P) ≤ ringKrullDim (MRing ι ℤ ⧸ P) := by
  refine Order.krullDim_le_of_strictMono
    (fun J : PrimeSpectrum (MRing ι (ZP p) ⧸ extTo (ZP p) P) =>
      (⟨J.asIdeal.comap (quotHom p P), inferInstance⟩ : PrimeSpectrum (MRing ι ℤ ⧸ P))) ?_
  refine Monotone.strictMono_of_injective (fun J J' h => Ideal.comap_mono h) ?_
  intro J J' h
  have h1 : J.asIdeal.comap (quotHom p P) = J'.asIdeal.comap (quotHom p P) :=
    congrArg PrimeSpectrum.asIdeal h
  have key : ∀ J : PrimeSpectrum (MRing ι (ZP p) ⧸ extTo (ZP p) P),
      ((((J.asIdeal.comap (quotHom p P)).comap (Ideal.Quotient.mk P)).map
        (algebraMap (MRing ι ℤ) (MRing ι (ZP p)))).map (Ideal.Quotient.mk (extTo (ZP p) P))) =
        J.asIdeal := by
    intro J
    have e : (J.asIdeal.comap (quotHom p P)).comap (Ideal.Quotient.mk P) =
        (J.asIdeal.comap (Ideal.Quotient.mk (extTo (ZP p) P))).comap
          (algebraMap (MRing ι ℤ) (MRing ι (ZP p))) := by
      rw [Ideal.comap_comap, Ideal.comap_comap, algebraMap_eq]
      congr 1
    rw [e]
    have e2 := IsLocalization.map_comap (consts ι p) (MRing ι (ZP p))
      (J.asIdeal.comap (Ideal.Quotient.mk (extTo (ZP p) P)))
    erw [e2]
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  apply PrimeSpectrum.ext
  rw [← key J, ← key J', h1]

theorem trdeg_eq (hP : P.IsPrime) (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) :
    Algebra.trdeg (ZP p) (MRing ι (ZP p) ⧸ extTo (ZP p) P) = Algebra.trdeg ℤ (MRing ι ℤ ⧸ P) := by
  haveI : (extTo (ZP p) P).IsPrime := isPrime_extTo p hP hC
  haveI := hP
  have hφ : Function.Injective (quotHom p P) :=
    Ideal.quotientMap_injective' (comap_extTo p hP hC).le
  let _ : Algebra (MRing ι ℤ ⧸ P) (MRing ι (ZP p) ⧸ extTo (ZP p) P) := (quotHom p P).toAlgebra
  have : @IsScalarTower ℤ (MRing ι ℤ ⧸ P) (MRing ι (ZP p) ⧸ extTo (ZP p) P)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : @IsScalarTower ℤ (ZP p) (MRing ι (ZP p) ⧸ extTo (ZP p) P)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : FaithfulSMul (MRing ι ℤ ⧸ P) (MRing ι (ZP p) ⧸ extTo (ZP p) P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : @FaithfulSMul ℤ (MRing ι ℤ ⧸ P) Algebra.toSMul := by
    refine (faithfulSMul_iff_algebraMap_injective ℤ (MRing ι ℤ ⧸ P)).2
      ((injective_iff_map_eq_zero (algebraMap ℤ (MRing ι ℤ ⧸ P))).2 fun a ha => ?_)
    have h : (C a : MRing ι ℤ) ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using ha)
    have h' : a ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [hC] at h'
    exact (Submodule.mem_bot _).1 h'
  have : FaithfulSMul (ZP p) (MRing ι (ZP p) ⧸ extTo (ZP p) P) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2
      ((injective_iff_map_eq_zero (algebraMap (ZP p) (MRing ι (ZP p) ⧸ extTo (ZP p) P))).2 fun a ha => ?_)
    have h : (C a : MRing ι (ZP p)) ∈ extTo (ZP p) P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk (extTo (ZP p) P) (C a) = 0 from ha)
    have h' : a ∈ (extTo (ZP p) P).comap (C : ZP p →+* MRing ι (ZP p)) := h
    rw [comap_C_extTo p hP hC] at h'
    exact (Submodule.mem_bot _).1 h'
  have : @FaithfulSMul ℤ (ZP p) Algebra.toSMul :=
    (faithfulSMul_iff_algebraMap_injective ℤ (ZP p)).2
      (IsLocalization.injective (ZP p) (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl)
        (Ideal.primeCompl_le_nonZeroDivisors _))
  have : Algebra.IsAlgebraic ℤ (ZP p) :=
    IsLocalization.isAlgebraic (ZP p) (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
  have : Algebra.IsAlgebraic (MRing ι ℤ ⧸ P) (MRing ι (ZP p) ⧸ extTo (ZP p) P) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective (consts ι p) g
    have hspec := IsLocalization.mk'_spec (MRing ι (ZP p)) s m
    let y := algebraMap (MRing ι ℤ ⧸ P) (MRing ι (ZP p) ⧸ extTo (ZP p) P)
      (Ideal.Quotient.mk P (m : MRing ι ℤ))
    have hy0 : y ≠ 0 := by
      refine (map_ne_zero_iff _ hφ).2 fun h => ?_
      exact Set.disjoint_left.1 (disjoint_consts p hC) m.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) (isAlgebraic_algebraMap _) ?_
    have : y * Ideal.Quotient.mk (extTo (ZP p) P) (IsLocalization.mk' (MRing ι (ZP p)) s m) =
        algebraMap (MRing ι ℤ ⧸ P) (MRing ι (ZP p) ⧸ extTo (ZP p) P) (Ideal.Quotient.mk P s) := by
      change quotHom p P _ * _ = quotHom p P _
      have e : ∀ t : MRing ι ℤ, quotHom p P (Ideal.Quotient.mk P t) =
          Ideal.Quotient.mk (extTo (ZP p) P) (algebraMap (MRing ι ℤ) (MRing ι (ZP p)) t) := by
        intro t
        rw [algebraMap_eq]
        exact Ideal.quotientMap_mk
      rw [e, e, ← map_mul, mul_comm, hspec]
    rw [this]
    exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq ℤ (ZP p) (A := MRing ι (ZP p) ⧸ extTo (ZP p) P)
  have h2 := trdeg_add_eq ℤ (MRing ι ℤ ⧸ P) (A := MRing ι (ZP p) ⧸ extTo (ZP p) P)
  rw [trdeg_eq_zero (R := ℤ) (A := ZP p), zero_add] at h1
  rw [trdeg_eq_zero (R := MRing ι ℤ ⧸ P) (A := MRing ι (ZP p) ⧸ extTo (ZP p) P), add_zero] at h2
  exact h1.trans h2.symm

theorem dim_le_trdeg [Fintype K] [∀ k, Fintype (ι k)] (hP : P.IsPrime)
    (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) :
    ringKrullDim (MRing ι ℤ ⧸ P) ≤
      (((Algebra.trdeg ℤ (MRing ι ℤ ⧸ P)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  haveI := hP
  have hinj : Function.Injective (algebraMap ℤ (MRing ι ℤ ⧸ P)) := by
    refine (injective_iff_map_eq_zero (algebraMap ℤ (MRing ι ℤ ⧸ P))).2 fun a ha => ?_
    have h : (C a : MRing ι ℤ) ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using ha)
    have h' : a ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [hC] at h'
    exact (Submodule.mem_bot _).1 h'
  refine (ringKrullDim_le_iff_isMaximal_height_le _).2 fun N hN => ?_
  haveI : N.IsPrime := hN.isPrime
  have key := DimensionInequality.full.{0, 0} ℤ (MRing ι ℤ ⧸ P) hinj N
  have key' := OrderHomClass.mono Cardinal.toENat key
  rw [map_add, map_add, Cardinal.toENat_ofENat, Cardinal.toENat_ofENat] at key'
  have hu : (N.under ℤ).height ≤ 1 := by
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := N.under ℤ) (Ideal.IsPrime.ne_top inferInstance)
    rw [IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField] at h
    exact_mod_cast h
  have hfin : N.height ≤ (Algebra.trdeg ℤ (MRing ι ℤ ⧸ P)).toENat + 1 := by
    calc N.height ≤ _ := le_self_add
      _ ≤ _ := key'
      _ ≤ 1 + (Algebra.trdeg ℤ (MRing ι ℤ ⧸ P)).toENat := by gcongr
      _ = _ := add_comm _ _
  exact_mod_cast hfin

theorem irreducible_p : Irreducible (((p : ℕ) : ZP p)) := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 ?_
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {((p : ℕ) : ℤ)}) (ZP p),
    Ideal.map_span, Set.image_singleton]
  simp

variable [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_extTo (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P)
    (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) : IsMultiProjPrime (extTo (ZP p) P) := by
  obtain ⟨hp, ⟨S, hS, hspan⟩, hrel⟩ := hP
  refine (Objects.isMultiProjPrime_iff _).2 ⟨isPrime_extTo p hp hC,
    ⟨MvPolynomial.map (Int.castRingHom (ZP p)) '' S, ?_, ?_⟩, isRelevant_extTo p hp hC hrel⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Ideal.map_span, ← hspan]
    rfl

theorem isModelOver_extTo {D : ℕ} (h : IsArithVar P (D + 1)) : IsModelOver (extTo (ZP p) P) D := by
  obtain ⟨-, hmp, hC, hd⟩ := h
  have hC' : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ := hC
  have hp : P.IsPrime := hmp.1
  have hm := isMultiProjPrime_extTo p hmp hC'
  have hn := comap_C_extTo p hp hC'
  have hdim := DvrConeDimTrdeg.proof (ZP p) K ι (extTo (ZP p) P) hm hn
  refine ⟨hm, hn, ?_⟩
  rw [← hd]
  refine le_antisymm (dim_le p P) ?_
  rw [hdim, trdeg_eq p hp hC']
  exact dim_le_trdeg hp hC'

theorem isVert_map {σ : Type} {S : Finset Nat.Primes} {T : LocPair ι ℤ σ} (hP : P.IsPrime)
    (hC : P.comap (C : ℤ →+* MRing ι ℤ) = ⊥) (hT : T.IsVertOff P S) :
    (T.map (Int.castRingHom (ZP p))).IsVert (extTo (ZP p) P) ((p : ℕ) : ZP p) := by
  intro i
  obtain ⟨⟨bf, bg, hbf, hbg, hb⟩, hf, hg, hu⟩ := hT i
  have hhom : ∀ {f : MRing ι ℤ} {b : K → ℕ}, IsMultiHomog f b →
      IsMultiHomog (MvPolynomial.map (Int.castRingHom (ZP p)) f) b := by
    intro f b h d hd
    refine h fun h0 => hd ?_
    rw [coeff_map, h0, map_zero]
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, hhom hbf, hhom hbg, hb⟩
    (fun h => hf (mem_of_map_mem p hP hC h)) (fun h => hg (mem_of_map_mem p hP hC h)) ?_
  intro W' hW' hPW' hrel hpW'
  have hWp : (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))).IsPrime := Ideal.comap_isPrime _ _
  have hPW : P ≤ W'.comap (MvPolynomial.map (Int.castRingHom (ZP p))) :=
    fun x hx => hPW' (Ideal.mem_map_of_mem _ hx)
  have hrelW : IsRelevant (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := by
    intro k
    obtain ⟨j, hj⟩ := hrel k
    refine ⟨j, fun h => hj ?_⟩
    have h' : MvPolynomial.map (Int.castRingHom (ZP p)) (X ⟨k, j⟩ : MRing ι ℤ) ∈ W' := h
    rwa [map_X] at h'
  have hoff : ∀ q ∈ S, (C ((q : ℕ) : ℤ) : MRing ι ℤ) ∉
      W'.comap (MvPolynomial.map (Int.castRingHom (ZP p))) := by
    intro q _ hq
    have hq' : MvPolynomial.map (Int.castRingHom (ZP p)) (C ((q : ℕ) : ℤ) : MRing ι ℤ) ∈ W' := hq
    rw [map_C] at hq'
    by_cases hd : ((q : ℕ) : ℤ) ∈ Ideal.span {((p : ℕ) : ℤ)}
    · have hdvd : (p : ℕ) ∣ (q : ℕ) := by
        exact_mod_cast Ideal.mem_span_singleton.1 hd
      have hpq : (p : ℕ) = (q : ℕ) := (Nat.prime_dvd_prime_iff_eq p.2 q.2).1 hdvd
      have e1 : Int.castRingHom (ZP p) ((q : ℕ) : ℤ) = (((q : ℕ) : ℕ) : ZP p) := by simp
      have e2 : (((q : ℕ) : ℕ) : ZP p) = (((p : ℕ) : ℕ) : ZP p) :=
        congrArg (fun n : ℕ => (n : ZP p)) hpq.symm
      apply hpW'
      rw [← e2, ← e1]
      exact hq'
    · have hunit : IsUnit (algebraMap ℤ (ZP p) ((q : ℕ) : ℤ)) :=
        IsLocalization.map_units (ZP p) (⟨((q : ℕ) : ℤ), hd⟩ : (Ideal.span {((p : ℕ) : ℤ)}).primeCompl)
      have e : Int.castRingHom (ZP p) ((q : ℕ) : ℤ) = algebraMap ℤ (ZP p) ((q : ℕ) : ℤ) := by simp
      rw [e] at hq'
      exact hW'.ne_top (Ideal.eq_top_of_isUnit_mem _ hq' (hunit.map C))
  obtain ⟨u, v, huW, hvW, huv⟩ := hu _ hWp hPW hrelW hoff
  refine ⟨MvPolynomial.map (Int.castRingHom (ZP p)) u, MvPolynomial.map (Int.castRingHom (ZP p)) v,
    huW, hvW, ?_⟩
  have h := Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZP p))) huv
  rw [map_sub, map_mul, map_mul] at h
  exact h

end

end GlobalTheory.CompanionTheory.Ar.Num.ZpModel

theorem GlobalTheory.CompanionTheory.Ar.Num.zp_model : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ p : Nat.Primes, Irreducible (((p : ℕ) : ZP p)) ∧ IsModelOver (extTo (ZP p) P) D ∧ ∀ (σ : Type) (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff P S → (T.map (Int.castRingHom (ZP p))).IsVert (extTo (ZP p) P) ((p : ℕ) : ZP p) := by
  intro K _ _ ι _ P D h p
  exact ⟨ZpModel.irreducible_p p, ZpModel.isModelOver_extTo p h, fun σ S T hT =>
    ZpModel.isVert_map p h.2.1.1 h.2.2.1 hT⟩
