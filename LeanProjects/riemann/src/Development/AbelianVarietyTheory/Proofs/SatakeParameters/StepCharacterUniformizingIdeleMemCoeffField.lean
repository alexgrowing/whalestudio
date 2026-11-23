import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterFiniteIdeleEqProdValuesZpowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdeleIsoComponentZeroOfInfinitelyDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatMulDivPowMemIntegralFiniteAdeleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsH90EqOneOffOfNormOneAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatCastCoprimeMemHeightOneSpectrumStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.MuLL

theorem hchar_eq_prod_val {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    (T : Finset (HeightOneSpectrum (𝓞 L))) (b : Neutral.B1.Ideles L) (hb : Formalism.L2.Host.IsFinIdele b)
    (h1 : ∀ P, P ∉ T → (b : AdeleRing (𝓞 L) L).2 P = 1) (hu : ∀ P ∈ T, χ.UnrAt P) :
    ∃ n : HeightOneSpectrum (𝓞 L) → ℤ, χ.1 b = ∏ P ∈ T, χ.val P ^ n P :=
  GlobalTheory.T.heckeCharacter_finite_idele_eq_prod_values_zpow χ T b hb h1 hu

theorem transfer_eq_zero {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E) (hrat : ∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1)
    (hint : ∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E')
    (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E') (hι : GlobalTheory.TwU.IsAdIso ι)
    (z : AfE F E) (ℓ D : ℕ) (hℓ : 0 < ℓ) (hD : 0 < D)
    (hz : ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E)
    (P : HeightOneSpectrum (𝓞 E')) (hP : ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal) :
    ι (iA.symm z) P = 0 :=
  GlobalTheory.T.finiteAdele_iso_component_zero_of_infinitely_divisible iE iA hrat hint ι hι z ℓ D hℓ hD hz P hP

theorem exists_div_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E) (hz : ∀ w', w' ≠ w → prV (E := E) w' z = 0)
    (ℓ : ℕ) (hℓ : ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E :=
  GlobalTheory.T.exists_nat_mul_div_pow_mem_integral_finiteAdele w z hz ℓ hℓ

theorem exists_h90_oneOff_preimage_at_splitPlace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (hsig : ∀ x, spl (sigR σ (w.adicCompletion F) x) = swapR (w.adicCompletion F) (spl x))
    (π : (AfE F E)ˣ) (hπ : π ∈ U1 σ) (hoff : OneOff w π) :
    ∃ x : (AfE F E)ˣ, h90 σ x = π ∧ OneOff w x :=
  GlobalTheory.T.hilbert90_normOne_oneOff_at_split_place_forall σ w spl hsig π hπ hoff

theorem exists_nat_mem_coprime {E : Type} [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (hP : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p :=
  GlobalTheory.T.exists_natCast_coprime_mem_heightOneSpectrum p hp P hP

end GlobalTheory.TwV.Xc.MuLL

namespace GlobalTheory.TwV.Xc.MuLL

open GlobalTheory.TwU (IsAdIso exists_isAdIso)

theorem exists_unitaryOneFiniteAdelic_of_det_normOne (D : D7) (π : (AfE D.host.F D.host.E)ˣ) (hπ : π ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = π := by
  have hd' : (π : AfE D.host.F D.host.E) * sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) π = 1 := by
    have := congrArg Units.val hπ
    simpa [Formalism.L2.DIV.U1, Formalism.L2.DIV.conjId] using this
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1) : AfE D.host.F D.host.E →+* _).toMonoidHom π, ?_⟩, ?_⟩
  · show cT _ _ * _ * _ = _
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, sigD]
    rw [mul_comm]
    exact hd'
  · ext
    simp

end GlobalTheory.TwV.Xc.MuLL

namespace GlobalTheory.TwV.Xc.MuLL

open GlobalTheory.TwU (IsAdIso exists_isAdIso)

theorem natCast_not_mem_of_coprime {R : Type} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) (a b : ℕ) (hab : Nat.Coprime a b)
    (hb : ((b : ℕ) : R) ∈ I) : ((a : ℕ) : R) ∉ I := by
  intro ha
  obtain ⟨c, d, h⟩ := (Nat.isCoprime_iff_coprime.2 hab : IsCoprime (a : ℤ) (b : ℤ))
  have h' := congrArg (Int.cast : ℤ → R) h
  push_cast at h'
  apply hI
  rw [Ideal.eq_top_iff_one, ← h']
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

set_option maxHeartbeats 4000000 in

theorem mu_mem_LL : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    KIn t → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∃ r : D.what₂.LL, D.what₂.embLL r = S.muT (j + 1) π) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hDict _hSpl hK v π hπ j hj
  have hpp : (D.what₂.places.resChar w).Prime := Fact.out
  have hpw0 : (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.F) ∈ ((A0 J).pl v).1.asIdeal := ((A0 J).pl v).2
  obtain ⟨x', hx'h, hx'off⟩ := exists_h90_oneOff_preimage_at_splitPlace (sigD D) ((A0 J).pl v).1 ((A0 J).spl v) (J.one.good.sig v) π hπ.1 hπ.2.1
  obtain ⟨y, hy⟩ := exists_unitaryOneFiniteAdelic_of_det_normOne D π hπ.1
  set x : (AfE t.X.F t.X.E)ˣ := Units.map J.A.iA.symm.toRingHom.toMonoidHom x' with hxdef
  have hxx : Units.map J.A.iA.toRingHom.toMonoidHom x = x' := by ext; simp [hxdef]
  have hq : J.A.q x = J.dtU y := J.pins.q_dt x y (by rw [hy, hxx, hx'h])
  have hmu : S.muT (j + 1) π = (((t.O u μ).mt (j + 1) (J.A.q x) : ℂˣ) : ℂ) := by
    rw [← hy, S.law.mu_read j hj y, hq]
  obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
  set b : Neutral.B1.Ideles t.X.E := MulEquiv.prodUnits.symm (1, Units.map ι.toRingHom.toMonoidHom x) with hbdef
  have hb : Formalism.L2.Host.IsFinIdele b := fun _ => rfl
  have hmuTil := J.pins.muTil ι hι ⟨j, hj⟩ b x hb rfl

  have hfin : {P : HeightOneSpectrum (𝓞 t.X.E) | P.asIdeal ∣ Ideal.span {((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E)}}.Finite :=
    Ideal.finite_factors (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hpp.ne_zero)
  set T := hfin.toFinset with hT
  have hmemT : ∀ P, P ∈ T ↔ ((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
    intro P
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have h1 : ∀ P, P ∉ T → (b : AdeleRing (𝓞 t.X.E) t.X.E).2 P = 1 := by
    intro P hP
    rw [hmemT] at hP
    obtain ⟨ℓ, hℓ0, hℓP, hcop⟩ := exists_nat_mem_coprime _ hpp P hP
    have hℓw : ((ℓ : ℕ) : 𝓞 D.host.F) ∉ ((A0 J).pl v).1.asIdeal :=
      natCast_not_mem_of_coprime _ ((A0 J).pl v).1.isPrime.ne_top ℓ _ hcop hpw0
    set z : AfE D.host.F D.host.E := (x' : AfE D.host.F D.host.E) - 1 with hzdef
    have hz : ∀ w', w' ≠ ((A0 J).pl v).1 → prV (E := D.host.E) w' z = 0 := by
      intro w' hw'
      rw [hzdef, map_sub, hx'off w' hw', map_one, sub_self]
    obtain ⟨Dd, hDd, hdiv⟩ := exists_div_int _ z hz ℓ hℓw
    have h0 := transfer_eq_zero t.seam.iE J.A.iA J.pins.iA_rat J.pins.iA_int ι hι z ℓ Dd hℓ0 hDd hdiv P hℓP
    have e1 : ((x : (AfE t.X.F t.X.E)ˣ) : AfE t.X.F t.X.E) = J.A.iA.symm z + 1 := by
      rw [hzdef, map_sub, map_one, sub_add_cancel]
      rfl
    have e2 : (b : AdeleRing (𝓞 t.X.E) t.X.E).2 = ι ((x : (AfE t.X.F t.X.E)ˣ) : AfE t.X.F t.X.E) := rfl
    rw [e2, e1, map_add, map_one]
    show ι (J.A.iA.symm z) P + 1 = 1
    rw [h0, zero_add]
  have hu : ∀ P ∈ T, (t.glob.mu0 ⟨j, hj⟩).UnrAt P := by
    intro P hP
    rw [hmemT] at hP
    refine (J.pins.mu0 ⟨j, hj⟩).unr P fun i hgi => ?_
    have hne : D.what₂.places.resChar w ≠ t.Pr.g i := by
      rw [t.g_rec i]
      exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.2 i
    have hcop : Nat.Coprime (t.Pr.g i) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes (t.pr_ok.g_prime i) hpp).2 hne.symm
    exact natCast_not_mem_of_coprime _ P.isPrime.ne_top _ _ hcop hP hgi
  obtain ⟨n, hn⟩ := hchar_eq_prod_val (t.glob.mu0 ⟨j, hj⟩) T b hb h1 hu
  set kU : t.X.Kˣ := ∏ P ∈ T, t.Ch.muVal ⟨j, hj⟩ P ^ n P with hkU
  have hk : Units.map t.seam.σ₀.toMonoidHom kU = (t.glob.mu0 ⟨j, hj⟩).1 b := by
    rw [hn, hkU, map_prod]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [map_zpow]
    congr 1
    apply Units.ext
    rw [Units.coe_map, ← t.glob_σ]
    refine J.pins.ch.muVal ⟨j, hj⟩ P fun i hgi => ?_
    rw [hmemT] at hP
    have hne : D.what₂.places.resChar w ≠ t.Pr.g i := by
      rw [t.g_rec i]
      exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.2 i
    have hcop : Nat.Coprime (t.Pr.g i) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes (t.pr_ok.g_prime i) hpp).2 hne.symm
    exact natCast_not_mem_of_coprime _ P.isPrime.ne_top _ _ hcop hP hgi
  rw [hmu]
  by_cases hμ : μ = D.what₂.mu0
  · obtain ⟨r, hr⟩ := hK (kU : t.X.K)
    refine ⟨r, ?_⟩
    rw [hr, (J.pins.ref hμ).2, hmuTil, ← hk]
    rfl
  · obtain ⟨ξ, hξ, hmt⟩ := J.pins.tw μ hμ rfl
    have e : (t.O u μ).mt (j + 1) = D.muTil (j + 1) * ξ := by
      rw [hmt u]
      exact if_pos (⟨by omega, by omega⟩ : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m)
    obtain ⟨r, hr⟩ := hK ((kU : t.X.K) * ((t.tup μ : Chr t.X.F t.X.E t.X.K) x : t.X.K))
    refine ⟨r, ?_⟩
    rw [hr, e, MonoidHom.mul_apply, Units.val_mul, hmuTil, hξ x, ← hk, map_mul]
    rfl

end GlobalTheory.TwV.Xc.MuLL
