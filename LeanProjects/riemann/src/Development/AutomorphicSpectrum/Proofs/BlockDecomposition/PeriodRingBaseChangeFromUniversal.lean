import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedDividedPowers
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.AcrMod

theorem factor_factor {R : Type} [CommRing R] {I J K : Ideal R} (h1 : I ≤ J) (h2 : J ≤ K) (y : R ⧸ I) :
    Ideal.Quotient.factor h2 (Ideal.Quotient.factor h1 y) = Ideal.Quotient.factor (h1.trans h2) y := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem fil_extend {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    (δ : DividedPowers J) (δ' : DividedPowers J') (φ : B →+* B') (hJ : J' = J.map φ)
    (h : IsDPMorphism δ δ' φ) (r : ℕ) : fil δ' r = (fil δ r).map φ := by
  subst hJ
  exact (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers δ φ δ' h).1 r

theorem pow_mem_span {R : Type} [CommRing R] {I : Ideal R} (δ : DividedPowers I) {p : ℕ} (hp : p ≠ 0)
    {x : R} (hx : x ∈ I) : x ^ p ∈ Ideal.span {(p : R)} := by
  rw [← δ.factorial_mul_dpow_eq_pow hx]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [Nat.factorial_succ, Nat.cast_mul, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

theorem l_mem_pfil : (l : A.Acr n) ∈ A.PFil n :=
  Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

theorem sharp_zero : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem uToPQ_th (x : A.W) : A.uToPQ n (A.th x) = Ideal.Quotient.mk _ (A.toAcr n x) := by
  rw [uToPQ, RingHom.comp_apply, uToQ_th, Ideal.Quotient.factor_mk]

theorem exists_pi : ∃ π : A.A →+* A.Acr n ⧸ A.PFil n,
    (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧
      π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi}) := by
  let g : A.W →+* A.Acr n ⧸ A.PFil n := (Ideal.Quotient.mk _).comp (A.toAcr n)
  let π : A.A →+* A.Acr n ⧸ A.PFil n :=
    (WittVector.constantCoeff : A.W →+* A.A).liftOfSurjective A.constantCoeff_surjective ⟨g, fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff x).2 hx)
      rw [RingHom.mem_ker, map_mul, RingHom.comp_apply (Ideal.Quotient.mk _) (A.toAcr n) (l : A.W), map_natCast,
        Ideal.Quotient.eq_zero_iff_mem.2 (l_mem_pfil A n), mul_zero]⟩
  have hπ : ∀ x : A.W, π (x.coeff 0) = g x := fun x => RingHom.liftOfSurjective_comp_apply _ _ _ x
  have ht : ∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a)) := fun a => by
    have := hπ (WittVector.teichmuller l a)
    rwa [WittVector.teichmuller_coeff_zero] at this
  have hs : ∀ a, π a = A.uToPQ n (A.sharp a) := fun a => by
    rw [ht]
    exact (uToPQ_th A n _).symm
  refine ⟨π, ht, fun y => ?_, ?_, fun hn => ?_⟩
  · obtain ⟨u, rfl⟩ := (RL.uToQ A n).2.2.1 y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨x.coeff 0, (hπ x).trans (uToPQ_th A n x).symm⟩
  · rw [hs, sharp_pi, map_natCast, ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (l_mem_pfil A n)
  · ext a
    have h := (RL.sharp_cong A).2.1 a 0
    rw [sharp_zero, sub_zero, sub_zero] at h
    rw [RingHom.mem_ker, hs, ← RingHom.mem_ker, (RL.uToQ A n).2.2.2 hn, h]

theorem fil_eq_map (r : ℕ) : A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n) := by
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 (mapAcr_fil A.fromBase n r))
  rw [PAlg.Fil, Ideal.span_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [← mapAcr_dxi A.fromBase n k]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨k, hk, rfl⟩)

theorem pfil_eq_map : A.PFil n = ((base l).PFil n).map (mapAcr A.fromBase n) := by
  rw [PFil, PFil, Ideal.map_sup, ← fil_eq_map, Ideal.map_span, Set.image_singleton, map_natCast]

theorem jj_eq_map (k : Bool) : JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n) := by
  cases k
  · exact fil_eq_map A n 1
  · exact pfil_eq_map A n

theorem fil_mono {r s : ℕ} (h : r ≤ s) : A.Fil n s ≤ A.Fil n r := by
  refine Ideal.span_mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, h.trans hk, rfl⟩

theorem fil_pdFil (r : ℕ) : fil (A.pdFil n) r = A.Fil n r := by
  refine le_antisymm ?_ ?_
  · have hprod : ∀ L : List (ℕ × A.Acr n), (∀ p ∈ L, p.2 ∈ A.Fil n 1) →
        (L.map fun p => (A.pdFil n).dpow p.1 p.2).prod ∈ A.Fil n (L.map Prod.fst).sum := by
      intro L
      induction L with
      | nil =>
        intro _
        simp only [List.map_nil, List.prod_nil, List.sum_nil]
        rw [(RL.filtration_multiplicative A).2.2.2.2.2.2.1 n]
        trivial
      | cons p L ih =>
        intro hL
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        exact (RL.filtration_multiplicative A).2.2.2.2.2.2.2 n _ _ (Ideal.mul_mem_mul
          (A.dpow_mem_fil n p.1 (hL p (by simp))) (ih fun q hq => hL q (by simp [hq])))
    refine Ideal.span_le.2 ?_
    rintro _ ⟨L, h1, h2, rfl⟩
    exact fil_mono A n h2 (hprod L h1)
  · rw [PAlg.Fil, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [← A.dpow_dxi n k]
    have h1 : A.dxi n 1 ∈ A.Fil n 1 := Ideal.subset_span ⟨1, le_rfl, rfl⟩
    exact GlobalTheory.CompanionTheory.PDMap.fil_anti (A.pdFil n) hk (GlobalTheory.CompanionTheory.PDMap.dpow_mem_fil (A.pdFil n) h1 k)

theorem pfil_pow (x : A.Acr n) (hx : x ∈ A.PFil n) : IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)} := by
  have h := pow_mem_span (A.pdPFil n) (Fact.out : l.Prime).ne_zero hx
  refine ⟨?_, h⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨l * n, by rw [pow_mul, ← hc, mul_pow, A.pow_l_acr n, mul_zero]⟩

theorem uJ_facts (k : Bool) (hn : n ≠ 0) :
    Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨u, hu⟩ := (RL.uToQ A n).1 (Ideal.Quotient.mk _ z)
    refine ⟨u, ?_⟩
    rw [uJ, RingHom.comp_apply, hu, Ideal.Quotient.factor_mk]
  · have e : A.uToPQ n x = Ideal.Quotient.factor (le_pfil k A n) (uJ k A n x) := by
      rw [uJ, RingHom.comp_apply, factor_factor]
      rfl
    have h0 : x ∈ RingHom.ker (A.uToPQ n) := by
      rw [RingHom.mem_ker, e, RingHom.mem_ker.1 hx, map_zero]
    rw [(RL.uToQ A n).2.2.2 hn] at h0
    exact (Ideal.span_singleton_le_iff_mem _).2 (R.mem_jacobson_of_complete (l : A.U)) h0

theorem acr_modp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ π : A.A →+* A.Acr n ⧸ A.PFil n, (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧ π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi})) ∧ (∀ r, A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n)) ∧ (∀ k, JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n)) ∧ (∀ r, fil (A.pdFil n) r = A.Fil n r) ∧ (∀ k r, fil (DD k A n) r = (fil (DD k (base l) n) r).map (mapAcr A.fromBase n)) ∧ (∀ x ∈ A.PFil n, IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)}) ∧ ∀ k, n ≠ 0 → Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  intro l _ A n
  exact ⟨exists_pi A n, fil_eq_map A n, jj_eq_map A n, fil_pdFil A n,
    fun k r => fil_extend _ _ _ (jj_eq_map A n k) (dd_map k A.fromBase n) r,
    pfil_pow A n, fun k hn => uJ_facts A n k hn⟩

end GlobalTheory.CompanionTheory.AcrMod
