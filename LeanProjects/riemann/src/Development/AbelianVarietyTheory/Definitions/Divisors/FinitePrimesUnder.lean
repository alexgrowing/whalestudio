import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt)
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples

namespace GlobalTheory.FunObj

namespace SqNum

section Std

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum

variable (D : D7)

def hatId (𝔪 : Ideal (𝓞 D.host.E)) : AddSubgroup (AE D) :=
  AddSubgroup.closure {y | ∃ b ∈ 𝔪, ∃ s ∈ OhE D, y = inc D (b : D.host.E) * s}

def CongOne (𝔪 : Ideal (𝓞 D.host.E)) {N : ℕ} (k : GA D N) : Prop :=
  ∀ i j, (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j ∈ hatId D 𝔪

def skewLat (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : Submodule (𝓞 D.host.E) (Fin N → D.host.E) :=
  Submodule.pi Set.univ fun _ => (((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
      FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)

def unitBlock (o a d : ℕ) : Matrix (Fin d) (Fin a) D.host.E := Matrix.of fun i j => if i.1 = o + j.1 then 1 else 0

variable {D} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (𝔪 : Ideal (𝓞 D.host.E))

def cosetVec (o : ℕ) : VC D P.a P.d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0)

def IsStdDatum (o : ℕ) : Prop :=
  ∃ R : Finset (GA D P.a), (∀ r ∈ R, r ∈ intG D P.a) ∧ (∀ k ∈ intG D P.a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) ∧
    P.F = ∑ r ∈ R, P.W.Om r 1 (cosetVec P 𝔪 o)

def IsBlockLevel (a : ℕ) : Prop :=
  ∀ h, h ∈ P.J ↔ h ∈ intG D P.d ∧ ∀ i j : Fin P.d, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin P.d) (AE D)) : Matrix (Fin P.d) (Fin P.d) (AE D)) i j ∈ hatId D 𝔪

def HasChars (χ χ' : HChar D.host.E) : Prop :=
  (∀ x, P.W.chV.f x ^ P.W.ep = χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) ∧
    ∀ x, P.W.chV'.f x ^ P.W.ep' = χ'.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)

theorem mem_hatId_top {x : AE D} (h : x ∈ OhE D) : x ∈ hatId D ⊤ :=
  AddSubgroup.subset_closure ⟨1, trivial, x, h, by simp⟩

theorem skewLat_top (N : ℕ) : skewLat D ⊤ N = stdL D N := by
  have : (D.host.conj • ⊤ : Ideal (𝓞 D.host.E)) = ⊤ := by
    rw [← Ideal.one_eq_top, smul_one]
  simp [skewLat, stdL, this]

theorem pt_unitBlock_mem (δ : ℂ) (o a d : ℕ) : pt D (tor0 D ⊤ δ) δ (unitBlock D o a d) ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun x hx i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, unitBlock D o a d i j * x j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      have := hx j trivial
      by_cases h : i.1 = o + j.1
      · simpa [unitBlock, h] using this
      · simp [unitBlock, h]
    exact this

theorem isStdDatum_top (P : Pair D ⊤ δ t0 Q) (hF : P.F = P.e0) (hJ : P.J = intG D P.d) (o a : ℕ) :
    IsStdDatum P ⊤ o ∧ IsBlockLevel P ⊤ a := by
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have e : cosetVec P ⊤ o = P.e0 := by
    rw [cosetVec, skewLat_top, show La D _ _ _ = La0 D (tor0 D ⊤ δ) P.a P.d from rfl, VacMove.iop_self D _ (La0 D _ _ _) P.vac.1,
      VacMove.wd_fix h1 P.crv (VacMove.klat _ (VacMove.moves_one D _) (VacMove.moves_one D _)) P.vac.1
        (pt_unitBlock_mem δ o _ _)]
    simp
  refine ⟨⟨{1}, by simp, fun k hk => ⟨1, ⟨by simp, fun i j => mem_hatId_top ?_⟩, fun r hr => by simpa using hr.1⟩, ?_⟩,
    fun h => ⟨fun hh => ⟨hJ ▸ hh, fun i j _ _ => mem_hatId_top (((mem_intG h).1 (hJ ▸ hh)) i j).1⟩, fun hh => hJ ▸ hh.1⟩⟩
  · rw [inv_one, one_mul, Matrix.sub_apply]
    exact sub_mem ((mem_intG k).1 hk i j).1 ((mem_intG 1).1 (one_mem _) i j).1
  · rw [Finset.sum_singleton, e, P.W.one _ (VacMove.vac_TT h1 P.crv P.vac.1), hF]

end Std

section Mean

variable {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)

def IsMinPol (β : ℂ) (p : K[X]) : Prop := p.Monic ∧ Irreducible p ∧ p.eval₂ σ β = 0

def meanVal_vw (w : Formalism.PairingDivisionLocalBalance.Pl K) (p : K[X]) : ℝ := (vw w (p.coeff 0) : ℝ) / p.natDegree

variable {σ}

omit [NumberField K] in

theorem IsMinPol.eq_minpoly {β : ℂ} {p : K[X]} (h : IsMinPol σ β p) : p = @minpoly K ℂ _ _ σ.toAlgebra β := by
  let := σ.toAlgebra
  exact minpoly.eq_of_irreducible_of_monic h.2.1 h.2.2 h.1

omit [NumberField K] in

theorem exists_isMinPol {β : ℂ} (h : IsAlgebraic ℚ β) [Algebra ℚ K] : ∃ p, IsMinPol σ β p := by
  let := σ.toAlgebra
  have : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hi : IsIntegral K β := (h.tower_top K).isIntegral
  exact ⟨minpoly K β, minpoly.monic hi, minpoly.irreducible hi, minpoly.aeval K β⟩

omit [NumberField K] in

theorem IsMinPol.ne_zero {β : ℂ} {p : K[X]} (h : IsMinPol σ β p) (h0 : β ≠ 0) : p.coeff 0 ≠ 0 ∧ p.natDegree ≠ 0 := by
  refine ⟨fun hc => h0 ?_, h.2.1.natDegree_pos.ne'⟩
  have e : p = X := eq_of_monic_of_associated h.1 monic_X
    (irreducible_X.associated_of_dvd h.2.1 (X_dvd_iff.2 hc)).symm
  simpa [e] using h.2.2

theorem meanVal_of_mem {b : K} {p : K[X]} (h : IsMinPol σ (σ b) p) (w : Formalism.PairingDivisionLocalBalance.Pl K) : meanVal_vw w p = vw w b := by
  have h' : IsMinPol σ (σ b) (X - C b) := ⟨monic_X_sub_C b, irreducible_X_sub_C b, by simp⟩
  have e : FractionalIdeal.spanSingleton (𝓞 K)⁰ (-b) = FractionalIdeal.spanSingleton (𝓞 K)⁰ b :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, by simp⟩
  rw [h.eq_minpoly.trans h'.eq_minpoly.symm]
  simp [meanVal_vw, vw, e]

theorem prime_unique {w : Formalism.PairingDivisionLocalBalance.Pl K} {l l' : ℕ} (hl : l.Prime) (hl' : l'.Prime) (h : (l : 𝓞 K) ∈ w.asIdeal)
    (h' : (l' : 𝓞 K) ∈ w.asIdeal) : l = l' := by
  by_contra e
  obtain ⟨x, y, e'⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl hl').2 e)).map (Int.castRingHom (𝓞 K))
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e']
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using h)) (Ideal.mul_mem_left _ _ (by simpa using h'))

theorem finite_primes_under {p : Formalism.PairingDivisionLocalBalance.Pl K → Prop} (h : {w | p w}.Finite) :
    {l : ℕ | l.Prime ∧ ∃ w, p w ∧ (l : 𝓞 K) ∈ w.asIdeal}.Finite := by
  refine (h.biUnion (t := fun w => {l : ℕ | l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal}) fun w _ =>
    Set.Subsingleton.finite fun l hl l' hl' => prime_unique hl.1 hl'.1 hl.2 hl'.2).subset ?_
  rintro l ⟨hl, w, h, h'⟩
  exact Set.mem_biUnion (x := w) h ⟨hl, h'⟩

theorem finite_primes_den {ι : Type} [Finite ι] {n : ι → ℤ → ℕ → ℝ} {u : ι → ℤ}
    (b : ∀ i s, ¬ (1 ≤ s ∧ s ≤ u i) → n i s = 0) (c : ∀ i s, {l | l.Prime ∧ n i s l ≠ 0}.Finite) :
    {l | l.Prime ∧ ∃ i s, n i s l ≠ 0}.Finite := by
  refine (Set.finite_iUnion fun i => (Set.finite_Icc (1 : ℤ) (u i)).biUnion fun s _ => c i s).subset ?_
  rintro l ⟨hl, i, s, h⟩
  refine Set.mem_iUnion.2 ⟨i, Set.mem_biUnion (x := s) (by_contra fun hs => h ?_) ⟨hl, h⟩⟩
  rw [b i s hs]; rfl

theorem le_add_truncZero {n a : ℤ} {y : ℝ} (h : (n : ℝ) ≤ a + y) : n ≤ a + truncZero y := by
  have h1 : n - a ≤ ⌊y⌋ := Int.le_floor.2 (by push_cast; linarith)
  have h2 := Int.floor_le_ceil y
  unfold truncZero
  split_ifs <;> omega

end Mean

variable (D : D7)

def botBig (i j : ℕ) : ℕ := rankV D (i + 1) (j + 1) - 2 * ((D.R.m - (j + 1)) / 2)

def botSmall (i j : ℕ) : ℕ := rankV D i j - 2 * ((D.R.m - j) / 2)

def halfRank (i j : ℕ) : ℕ := (rankV D (i + 1) (j + 1) + rankV D i j) / 2

theorem ranks_exact (i j : ℕ) : botBig D i j + 2 * ((D.R.m - (j + 1)) / 2) = rankV D (i + 1) (j + 1) ∧
    botSmall D i j + 2 * ((D.R.m - j) / 2) = rankV D i j ∧
    2 * halfRank D i j = rankV D (i + 1) (j + 1) + rankV D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := odd_sLen D
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have h1 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have h2 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  simp only [botBig, botSmall, halfRank]
  omega

def cmPhi (τ : D.what₂.Tau) : D.host.E →+* ℂ := ComplexEmbedding.conjugate (embTau D τ)

def kap (C : ℝ) (i j s : ℕ) (τ : D.what₂.Tau) : ℕ := ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i) - s).toNat

def wtA (C : ℝ) (i j : ℕ) (τ : D.what₂.Tau) : ℤ :=
  (2 * (num D C τ).e (j + 1) - (rankV D i j % 2 : ℕ) - botSmall D i j) / 2

def wtA' (C : ℝ) (i j : ℕ) (τ : D.what₂.Tau) : ℤ :=
  (-2 * cen D C τ (D.R.m - i) - (rankV D i j % 2 : ℕ) + botBig D i j) / 2

theorem two_mul_wtA_sub (C : ℝ) (i j : ℕ) (τ : D.what₂.Tau) : 2 * (wtA D C i j τ - wtA' D C i j τ) =
    2 * ((num D C τ).e (j + 1) + cen D C τ (D.R.m - i)) - (botBig D i j + botSmall D i j : ℕ) := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  simp only [wtA, wtA']
  omega

def maxWt (C : ℝ) : ℕ :=
  max 1 (Finset.univ.sup fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
    max (wtA D C x.1 x.2.1 x.2.2).natAbs (wtA' D C x.1 x.2.1 x.2.2).natAbs)

variable {D} {T : Type} {L : LevCh D T} {sc : Consts}

open Classical in

def condExp (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℕ := if v = P.v0 then 1 else 2

def condF (P : Places L) : Ideal (GlobalTheory.CMVal.OF D.host.E) :=
  (∏ v ∈ P.S0, v.asIdeal ^ condExp P v : Ideal (𝓞 D.host.F))

def condE (P : Places L) : Ideal (𝓞 D.host.E) := ∏ v ∈ P.S0, (P.w v).asIdeal ^ condExp P v

def levQ (P : Places L) : ℕ := ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ condExp P v

theorem condE_ne_bot (P : Places L) : condE P ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (P.w v).ne_bot

theorem log_levQ (P : Places L) :
    Real.log (levQ P) = ∑ v ∈ P.S0, (condExp P v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  rw [levQ, Nat.cast_prod, Real.log_prod fun v _ => by
    exact_mod_cast pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)]
  simp

def delOf (L : LevCh D T) (c : Bool) : HChar D.host.E := cond c L.C.del' L.C.del

variable (G : GridData L sc) (t : T) (i j : Fin D.R.m)

def nuH : HChar D.host.E := L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i)

def alphaH (L : LevCh D T) (t : T) (i j : Fin D.R.m) : HChar D.host.E := L.C.mu0 j * L.xiH t * L.C.eta ^ (rankV D i j % 2)

def betaH : HChar D.host.E := G.ch.chiH (D.R.m - i) * L.C.eta ^ (rankV D i j % 2)

theorem alphaH_div_betaH : alphaH L t i j / betaH G i j = nuH G t i j := mul_div_mul_right_eq_div _ _ _

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum in

theorem chrEq_nu {μ₀ : T} (hL : L.Is μ₀) : ChrEq (G.nu t i (j + 1)) (nuH G t i j) := by
  have h1 := hL.mu0 j
  have h2 := hL.xi t
  have h3 := G.ch.chi_eq (D.R.m - i) (by omega) (by omega)
  refine ⟨⟨(h1.1.1.mul h2.1.1).div' h3.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · show L.mu0 (j + 1) _ * L.xi t _ / G.ch.chi (D.R.m - i) _ = 1
    rw [h1.1.2, h2.1.2, h3.1.2]; simp
  · have e1 : G.nu t i (j + 1) x = L.mu0 (j + 1) x * L.xi t x / G.ch.chi (D.R.m - i) x := rfl
    have e2 : (nuH G t i j).locK P k =
        (L.C.mu0 j).locK P k * (L.xiH t).locK P k / (G.ch.chiH (D.R.m - i)).locK P k := rfl
    rw [e1, e2, Circle.coe_div, Circle.coe_mul, h1.2 P e he k x hx, h2.2 P e he k x hx, h3.2 P e he k x hx]
    simp

structure IsBottom (𝔪 : Ideal (𝓞 D.host.E)) {δ t0 : ℂ} {Q : ℕ} (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) : Prop where

  rank : P.a = botBig D i j ∧ P'.a = botSmall D i j ∧ P.d = botBig D i j + botSmall D i j ∧ P'.d = P.d

  chars : HasChars P (betaH G i j)⁻¹ (nuH G t i j)⁻¹

  chars' : HasChars P' (alphaH L t i j) (nuH G t i j)⁻¹

  std : IsStdDatum P 𝔪 0

  std' : IsStdDatum P' (D.host.conj • 𝔪) (botBig D i j)

  lev : IsBlockLevel P 𝔪 (botBig D i j) ∧ IsBlockLevel P' 𝔪 (botBig D i j)

def IsTor (s : ℕ) (χ : HChar D.host.E) (x : ℂ) : Prop :=
  GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ χ ∧
    GlobalTheory.CMVal.IsToricSum (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) χ x

def IsTorVal (s : ℕ) (zd : Bool → D.what₂.LL) (g : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℤ) : Prop :=
  ∃ x, IsTor G i j s (nuH G t i j) x ∧ x ≠ 0 ∧
    (∀ c, IsTor G i j s (nuH G t i j * delOf L c) (D.what₂.embLL (zd c) * x)) ∧
    ∃ Λ p, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ ∧
      IsMinPol D.what₂.embLL (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ x) p ∧
      ∀ w, g w = truncZero (meanVal_vw w p / 12)

def IsDenom (s : ℕ) (n_vp : ℕ → ℝ) : Prop :=
  ∃ z, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals (E := D.host.E) (2 * s) z ∧ ∀ l : ℕ, l.Prime →
    n_vp l = (⌈GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) z l / 12⌉₊ : ℕ)

def IsIntExp (C : ℝ) (dl : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℝ) : Prop :=
  ∃ (S : Finset ℕ) (del_vp : ℕ → ℝ),
    GlobalTheory.NormSum.Exponents S del_vp
      (GlobalTheory.NormSum.intBound C D.R.f (bigN D) (maxWt D sc.cGap) (Real.log sc.b) (levQ G.pl)) ∧
    GlobalTheory.NormSum.CoordInt D (bigN D) (maxWt D sc.cGap) (levQ G.pl) del_vp ∧
    GlobalTheory.NormSum.NormInt D (bigN D) (maxWt D sc.cGap) (levQ G.pl) S del_vp
      (GlobalTheory.NormSum.intBound C D.R.f (bigN D) (maxWt D sc.cGap) (Real.log sc.b) (levQ G.pl)) ∧
    dl = wt S del_vp

variable {G t i j}

theorem IsTorVal.coord_unique {s : ℕ} {zd zd' g g'} (h : IsTorVal G t i j s zd g) (h' : IsTorVal G t i j s zd' g') :
    zd = zd' := by
  obtain ⟨x, h1, h0, h2, -⟩ := h
  obtain ⟨x', h1', -, h2', -⟩ := h'
  obtain rfl := h1.2.unique h1'.2
  exact funext fun c => D.what₂.embLL.injective (mul_right_cancel₀ h0 ((h2 c).2.unique (h2' c).2))

theorem exists_isIntExp (h : GlobalTheory.NormSum.IntSt) : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts)
    (G : GridData L sc), GlobalTheory.NormSum.GoodLevel D (levQ G.pl) → 1 ≤ Real.log sc.b → Real.log D.host.rdE ≤ Real.log sc.b →
    ∃ dl, IsIntExp G C dl := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun D T L sc G h1 h2 h3 => ?_⟩
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  obtain ⟨S, del, h4, h5, h6⟩ := h D _ (bigN D) (maxWt D sc.cGap) _ h1 hN (by exact_mod_cast le_max_left _ _) h2 h3
  exact ⟨_, S, del, h4, h5, h6, rfl⟩

end SqNum

open SqNum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

structure IsSqOf (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (C : ℝ) (μ₀ : T) (μ : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → T)
    (rq : T → Fin D.R.m × Fin D.R.m → D.what₂.LL) (zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL)
    (zT : Fin D.R.m × Fin D.R.m → ℤ → D.what₂.LL) (zTd : Fin D.R.m × Fin D.R.m → Bool → ℤ → D.what₂.LL)
    (gT : Fin D.R.m × Fin D.R.m → ℤ → Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℤ) (ch : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → Bool)
    (N0 : Fin D.R.m × Fin D.R.m → ℤ → ℕ → ℝ) (Sd Se : Finset ℕ) (dl : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℝ) (Bw : ℝ) : Prop where

  ratio : ∀ ij : Fin D.R.m × Fin D.R.m, ∃ c : T → ℂ, c μ₀ ≠ 0 ∧ ∀ t, (t = μ₀ ∨ ∃ w, μ w = t) →
    SquareNonzero W B ρ t ij.1 ij.2 ∧ IsSquareConst W B ρ t ij.1 ij.2 (c t) ∧ D.what₂.embLL (rq t ij) * c μ₀ = c t

  norms : ∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
    IsBottom G μ₀ ij.1 ij.2 (condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧ D.what₂.embLL (zA' ij) = (P'.norm : ℂ)

  base : ∀ ij s, zT ij s = 1

  inside : ∀ (ij : Fin D.R.m × Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D ij.1 ij.2 →
    IsTorVal G μ₀ ij.1 ij.2 s (fun c => zTd ij c s) (gT ij s) ∧ IsDenom G ij.1 ij.2 s (N0 ij s)

  outside : ∀ (ij : Fin D.R.m × Fin D.R.m) (s : ℤ), ¬ (1 ≤ s ∧ s ≤ halfRank D ij.1 ij.2) →
    (∀ c, zTd ij c s = 1) ∧ gT ij s = 0 ∧ N0 ij s = 0

  choice : ∀ w, ch w = true ↔ ((D.host.pde : ℕ) : 𝓞 D.what₂.LL) ∈ w.asIdeal

  den : ∀ l, l ∈ Sd ↔ l.Prime ∧ ∃ ij s, N0 ij s l ≠ 0

  err : ∀ l, l ∈ Se ↔ l.Prime ∧ ∃ w, μ w ≠ μ₀ ∧ (l : 𝓞 D.what₂.LL) ∈ w.asIdeal

  int : IsIntExp G C dl

  weight : Bw = maxWt D sc.cGap

namespace IsSqOf

variable {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {C : ℝ} {μ₀ : T} {μ : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → T}
  {rq zA zA' zT zTd gT ch N0 Sd Se dl Bw} (h : IsSqOf W B ρ C μ₀ μ rq zA zA' zT zTd gT ch N0 Sd Se dl Bw)
include h

theorem rq_base (ij : Fin D.R.m × Fin D.R.m) : rq μ₀ ij = 1 := by
  obtain ⟨c, h0, hc⟩ := h.ratio ij
  exact D.what₂.embLL.injective (mul_right_cancel₀ h0 (by rw [(hc _ (Or.inl rfl)).2.2, map_one, one_mul]))

theorem rq_mul {ij : Fin D.R.m × Fin D.R.m} {t : T} (ht : t = μ₀ ∨ ∃ w, μ w = t) {c₀ c : ℂ}
    (h₀ : IsSquareConst W B ρ μ₀ ij.1 ij.2 c₀) (h₁ : IsSquareConst W B ρ t ij.1 ij.2 c) : D.what₂.embLL (rq t ij) * c₀ = c := by
  obtain ⟨c', -, hc⟩ := h.ratio ij
  rw [h₀.unique (hc _ (Or.inl rfl)).1 (hc _ (Or.inl rfl)).2.1, h₁.unique (hc t ht).1 (hc t ht).2.1, (hc t ht).2.2]

theorem delOf_ch {l : ℕ} (hl : l.Prime) {w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL} (hw : (l : 𝓞 D.what₂.LL) ∈ w.asIdeal) :
    delOf L (ch w) = L.C.delAt l := by
  unfold Formalism.L2.Host.CharFrame.delAt
  split_ifs with e
  · rw [(h.choice w).2 (e ▸ hw)]; rfl
  · have : ch w = false := Bool.eq_false_iff.2 fun hc => e (prime_unique hl D.host.pde_prime hw ((h.choice w).1 hc))
    rw [this]; rfl

end IsSqOf

open Classical in

theorem exists_isSqOf {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {C : ℝ} {μ₀ : T} {μ : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → T}
    {rq : T → Fin D.R.m × Fin D.R.m → D.what₂.LL} {zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL} {dl}
    (h1 : ∀ ij : Fin D.R.m × Fin D.R.m, ∃ c : T → ℂ, c μ₀ ≠ 0 ∧ ∀ t, (t = μ₀ ∨ ∃ w, μ w = t) →
      SquareNonzero W B ρ t ij.1 ij.2 ∧ IsSquareConst W B ρ t ij.1 ij.2 (c t) ∧ D.what₂.embLL (rq t ij) * c μ₀ = c t)
    (h2 : ∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ ij.1 ij.2 (condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧
        D.what₂.embLL (zA' ij) = (P'.norm : ℂ))
    (h3 : ∀ (ij : Fin D.R.m × Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D ij.1 ij.2 → ∃ zd g n,
      IsTorVal G μ₀ ij.1 ij.2 s zd g ∧ IsDenom G ij.1 ij.2 s n ∧ {l | l.Prime ∧ n l ≠ 0}.Finite)
    (h4 : IsIntExp G C dl) (h5 : {w | μ w ≠ μ₀}.Finite) :
    ∃ zT zTd gT ch N0 Sd Se Bw, IsSqOf W B ρ C μ₀ μ rq zA zA' zT zTd gT ch N0 Sd Se dl Bw := by
  have H : ∀ (ij : Fin D.R.m × Fin D.R.m) (s : ℤ), ∃ (zd : Bool → D.what₂.LL) (g : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℤ) (n : ℕ → ℝ),
      (∀ s' : ℕ, s = s' → 1 ≤ s' → s' ≤ halfRank D ij.1 ij.2 →
        IsTorVal G μ₀ ij.1 ij.2 s' zd g ∧ IsDenom G ij.1 ij.2 s' n) ∧
      (¬ (1 ≤ s ∧ s ≤ halfRank D ij.1 ij.2) → (∀ c, zd c = 1) ∧ g = 0 ∧ n = 0) ∧ {l | l.Prime ∧ n l ≠ 0}.Finite := by
    intro ij s
    by_cases hs : 1 ≤ s ∧ s ≤ halfRank D ij.1 ij.2
    · obtain ⟨zd, g, n, a, b, c⟩ := h3 ij s.toNat (by omega) (by omega)
      refine ⟨zd, g, n, fun s' e _ _ => ?_, fun h => absurd hs h, c⟩
      obtain rfl : s' = s.toNat := by omega
      exact ⟨a, b⟩
    · exact ⟨1, 0, 0, fun s' e _ _ => absurd ⟨by omega, by omega⟩ hs, fun _ => ⟨fun _ => rfl, rfl, rfl⟩, by simp⟩
  choose zd g n a b c using H
  have f1 := finite_primes_den (fun ij s hs => (b ij s hs).2.2) c
  have f2 := finite_primes_under h5
  exact ⟨fun _ _ => 1, fun ij c s => zd ij s c, g, fun w => decide (((D.host.pde : ℕ) : 𝓞 D.what₂.LL) ∈ w.asIdeal), n,
    f1.toFinset, f2.toFinset, _, h1, h2, fun _ _ => rfl, fun ij s => a ij s s rfl, b, fun _ => decide_eq_true_iff,
    fun _ => f1.mem_toFinset, fun _ => f2.mem_toFinset, h4, rfl⟩

example : unitBlock D 1 1 2 1 0 = 1 ∧ unitBlock D 1 1 2 0 0 = 0 := by simp [unitBlock]

example {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) (a : K) :
    meanVal_vw w (X ^ 2 + C a) = vw w a / 2 := by simp [meanVal_vw]

end GlobalTheory.FunObj

end
