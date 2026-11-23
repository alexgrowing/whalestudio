import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevUAnti
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevelRk
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbField
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.RkTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.GenOfRk
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CharStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.QuadStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.HasMuQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DegBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LayerFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CompIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ShaTwo

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

noncomputable section

namespace UpperTheory.V.Two

theorem complex_of_root {L : Type} [Field L] [NumberField L] {n : ℕ} (hn : 2 < n) (h : ∃ ζ : L, IsPrimitiveRoot ζ n) :
    IsTotallyComplex L := by
  obtain ⟨ζ, hζ⟩ := h
  exact nrRealPlaces_eq_zero_iff.1 (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hn hζ)

theorem fwRk (hFW : Published.FerreroWashington) (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K]
    [IsAbelianGalois ℚ K] (hμ : HasMuQ l K) :
    ∃ r, ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], XRk l 1 (cycU l (⊤ : Subgroup (G K Ω))) r := by
  obtain ⟨r, hr⟩ := hFW l K hμ
  refine ⟨r, fun Ω _ _ _ => infRk K Ω l 1 r ⊤ one_ne_zero isClosed_univ fun n hn => ?_⟩
  haveI := (fnCyc K Ω l n).1
  exact levelRk K Ω l n r hn (hr n _)

theorem isAlgClosure_rat (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra ℚ Ω] :
    IsAlgClosure ℚ Ω :=
  ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans ℚ L Ω⟩

theorem abRk (hFW : Published.FerreroWashington) (l : ℕ) [Fact l.Prime] (A : AbF)
    (hμ : ∀ (L : Type) [Field L] [NumberField L], IsAbField A L → HasMuQ l L) :
    ∃ r, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω], XRk l 1 (cycU l (abU Ω A)) r := by
  obtain ⟨K, _, _, hK⟩ := abExists A
  haveI := (abProps A K hK).1
  obtain ⟨r, hr⟩ := fwRk hFW l K (hμ K hK)
  refine ⟨r, fun Ω _ _ _ => ?_⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  rw [← abField Ω A K hK]
  exact (rkTransport ℚ Ω K l 1 r).1 (hr Ω)

theorem genLE_of_abRk {l : ℕ} [Fact l.Prime] {A : AbF} {r : ℕ} (N : ℕ) (L : Type) [Field L] [NumberField L]
    [IsAlgClosure ℚ (AlgebraicClosure L)] (hL : IsAbField A L)
    (h : XRk l 1 (cycU l (abU (AlgebraicClosure L) A)) r) : Tower.GenLE ℤ_[l] (Tower.XN l L (AlgebraicClosure L) N) r := by
  rw [← abField _ A L hL] at h
  exact genOfRk L _ l N r ⊤ isClosed_univ (((rkTransport ℚ _ L l 1 r).2 h).of_one N)

theorem baseRk (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (q d g : ℕ) (hp : PrimePair M.m q d)
    (h : XRk 2 1 (cycU 2 (abU Ω (withI M))) g) : XRk 2 1 (cycU 2 (abU Ω (base2 M q d))) (4 * (g + 6 * M.deg)) := by
  obtain ⟨hq, hq8, hd, hd16, hc⟩ := hp
  have q2 : q.Coprime 2 := (Nat.coprime_two_right).2 (Nat.odd_iff.2 (by omega))
  have d2 : d.Coprime 2 := (Nat.coprime_two_right).2 (Nat.odd_iff.2 (by omega))
  have h0 : CardLe (CharOff (cycU 2 (abU Ω (withI M))) (ineOff ℚ Ω 1) 2) (2 ^ g) :=
    CardLe.of_injective h _ (Submodule.inclusion_injective (xDual_one _ 2).ge)
  have h1 := charStep ℚ Ω 2 _ 1 q _ _ q2 (orbTwo Ω M q 2 hq (Or.inl ⟨hq8, rfl⟩))
    (fun A hA => ineTwo Ω M q A (q2.mul_right (Nat.Coprime.coprime_mul_right hc)) hA) h0
  have h2 := charStep ℚ Ω 2 _ (1 * q) d _ _ d2 (orbTwo Ω M d 4 hd (Or.inr ⟨hd16, rfl⟩))
    (fun A hA => ineTwo Ω M d A (d2.mul_right (Nat.Coprime.coprime_mul_left hc)) hA) h1
  have h3 := quadStep Ω _ q _ _ hq (by simp) h2
  have h4 := quadStep Ω _ d _ _ hd (by simp) h3
  refine (h4.of_injective _ (Submodule.inclusion_injective (xDual_le_charOff 1 _ _ 2))).mono (le_of_eq ?_)
  rw [← pow_add, ← pow_add, ← pow_mul, ← pow_mul]
  congr 1
  ring

theorem towerTwo (hFW : Published.FerreroWashington) (M : AbF) : ∃ R : ℕ, ∀ q d : ℕ, PrimePair M.m q d →
    ∀ (L : Type) [Field L] [NumberField L], IsAbField (base2 M q d) L →
      Tower.GenLE ℤ_[2] (Tower.XX 2 L) R ∧ Tower.IsTower 2 L R := by
  obtain ⟨g, hg⟩ := abRk hFW 2 (withI M) fun L _ _ hL => hasMuQ.2.1 M L hL
  refine ⟨4 * (g + 6 * M.deg), fun q d hp L _ _ hL => ?_⟩
  haveI := isAlgClosure_rat L (AlgebraicClosure L)
  have h := baseRk (AlgebraicClosure L) M q d g hp (hg _)
  have hμ := hasMuQ.2.2 M q d L hL
  have ho := ((abBasic (AlgebraicClosure L)).2.1 M).2.1
  exact ⟨genLE_of_abRk 1 L hL h, complex_of_root (by norm_num) hμ, hμ, by omega, genLE_of_abRk 2 L hL h⟩

theorem towerFixed (hFW : Published.FerreroWashington) (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (A : AbF) (hA : A.HasMu l) :
    ∃ R : ℕ, ∀ (L : Type) [Field L] [NumberField L], IsAbField A L →
      Tower.GenLE ℤ_[l] (Tower.XX l L) R ∧ Tower.IsTower l L R := by
  have hμ : ∀ (L : Type) [Field L] [NumberField L], IsAbField A L → HasMuQ l L := fun L _ _ hL => by
    unfold HasMuQ
    rw [if_neg h2]
    exact hasMuQ.1 l A L hA hL
  obtain ⟨r, hr⟩ := abRk hFW l A hμ
  refine ⟨max 1 r, fun L _ _ hL => ?_⟩
  haveI := isAlgClosure_rat L (AlgebraicClosure L)
  have h := (hr (AlgebraicClosure L)).mono hl.out.pos (le_max_right 1 r)
  exact ⟨genLE_of_abRk 1 L hL h, complex_of_root (lt_of_le_of_ne hl.out.two_le h2.symm) (hasMuQ.1 l A L hA hL),
    hμ L hL, le_max_left _ _, genLE_of_abRk l L hL h⟩

theorem twoBase (M : AbF) (q d : ℕ) (hp : PrimePair M.m q d) (L : Type) [Field L] [NumberField L]
    (hL : IsAbField (base2 M q d) L) : Win.TwoBase M q d L := by
  obtain ⟨hq, -, hd, -, -⟩ := hp
  obtain ⟨-, h1, h2⟩ := abProps _ L hL
  have hμ := hasMuQ.2.2 M q d L hL
  refine ⟨hμ, h1 ▸ degBasic.2.2.2 M q d hq hd, ?_, fun e _ E _ _ hE => ?_⟩
  · rwa [modulus_adjoinISqrtNegPrimes M hq.pos hd.pos, mul_comm M.m 4] at h2
  · haveI := isAlgClosure_rat L (AlgebraicClosure L)
    letI : Algebra E (AlgebraicClosure L) := (IsAlgClosed.lift : E →ₐ[ℚ] AlgebraicClosure L).toRingHom.toAlgebra
    obtain ⟨ζ, hζ⟩ := hμ
    obtain ⟨m, hm, hlay⟩ := layerFn L (AlgebraicClosure L) 2 (e + 2) ⟨ζ ^ 2, hζ.pow (by norm_num) (by norm_num)⟩
    haveI := (fnCyc L (AlgebraicClosure L) 2 (e + 2)).1
    have e1 := galOfCyc ℚ (AlgebraicClosure L) 2 (e + 2) L (Fn L (AlgebraicClosure L) 2 (e + 2))
    rw [abField _ _ L hL] at e1
    obtain ⟨a, b⟩ := compIndex (AlgebraicClosure L) M e q d E hq hd hE
    exact ⟨m, Fn L (AlgebraicClosure L) 2 (e + 2), inferInstance, inferInstance, inferInstance, hlay, hm,
      fun k _ => shaTwo (AlgebraicClosure L) E _ k (e1 ▸ a) (e1 ▸ b)⟩

def TowerBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] (R : ℕ), Tower.IsTower l L R → Win.ABound l R L

theorem twoIn (hFW : Published.FerreroWashington) (hA : TowerBound) : Win.TwoIn := fun M => by
  obtain ⟨R, hR⟩ := towerTwo hFW M
  refine ⟨R, fun q d hp => ?_⟩
  obtain ⟨L, _, _, hL⟩ := abExists (base2 M q d)
  exact ⟨L, inferInstance, inferInstance, twoBase M q d hp L hL, hA 2 L R (hR q d hp L hL).2⟩

theorem fixedIn (hFW : Published.FerreroWashington) (hA : TowerBound) : Win.FixedIn := fun l _ h2 A hμ L _ _ hL => by
  obtain ⟨R, hR⟩ := towerFixed hFW l h2 A hμ
  exact ⟨R, hA l L R (hR L hL).2⟩

end UpperTheory.V.Two

end
