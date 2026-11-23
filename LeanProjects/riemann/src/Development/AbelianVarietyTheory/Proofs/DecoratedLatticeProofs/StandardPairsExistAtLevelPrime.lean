import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PadicResidueFieldCardAndPrimeIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotSqDvdOfRationalPrimeSplitsCompletelyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvdStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace StdExProof

theorem qt_facts (T : ℕ) [Fact T.Prime] : Nat.card 𝓀[ℚ_[T]] = T ∧ Irreducible ((T : 𝒪[ℚ_[T]])) := GlobalTheory.T.padic_residueField_card_and_prime_irreducible T

theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (T : ℕ) (hT : T.Prime) (hs : GlobalTheory.St.G.SplitsIn E T)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (T : 𝓞 E) ∈ w.asIdeal) : ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} :=
  GlobalTheory.T.not_sq_dvd_of_rationalPrimeSplitsCompletely E T hT hs w hw

theorem places_over (D : D7) (π π' : 𝓞 D.host.E) (T : ℕ) (hπ' : (π' : D.host.E) = star (π : D.host.E))
    (hT : π * π' = (T : 𝓞 D.host.E)) (hne : π ≠ 0) (x : HeightOneSpectrum (𝓞 D.host.F)) :
    (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x :=
  GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd D π π' T hπ' hT hne x

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_int (p : SplitPt D k) (x : 𝓞 D.host.E) : p.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (p.pr (incA D (x : D.host.E))) := (x.2).map ((p.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (p.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

theorem val_pr_eq_one (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w)
    (y : 𝓞 D.host.E) (hy : y ∉ w.asIdeal) : valuation k (p.pr (incA D (y : D.host.E))) = 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ w.asIdeal.zero_mem)
  have hyE : (y : D.host.E) ≠ 0 := by exact_mod_cast hy0
  have hI : finPart D (p.e * incA D ((y : D.host.E))⁻¹) ∈ intAE D := not_not.1 (mt (hw.2 y hy0).2 hy)
  have h1 : p.pr (incA D ((y : D.host.E))⁻¹) ∈ 𝒪[k] := by
    rw [p.int_iff, p.sec_pr]; exact hI
  have h2 := pr_int p y
  have hmul : p.pr (incA D (y : D.host.E)) * p.pr (incA D ((y : D.host.E))⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hyE, map_one, map_one]
  have e1 : valuation k (p.pr (incA D (y : D.host.E))) ≤ 1 := h2
  have e2 : valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) ≤ 1 := h1
  have e3 := congrArg (valuation k) hmul
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  by_contra hlt
  push_neg at hlt
  have : valuation k (p.pr (incA D (y : D.host.E))) * valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt e2
  rw [e3] at this
  exact lt_irrefl _ this

theorem isLat_std (p : SplitPt D k) (S : HSp D) (β : Frame p S (Fin S.rank)) (hb : β.b = 1) (L : Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D _) : β.IsLat L (stdLat k (Fin S.rank)) := by
  intro x
  have hL' : ∀ z : Fin S.rank → D.host.E, z ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = z i := fun z => by
    rw [hL z]
    exact ⟨fun h i => ⟨⟨z i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩
  rw [hb, Matrix.one_mulVec, GlobalTheory.FinPl.Model.mem_latV_std S L hL' p.v, mem_stdLat]
  refine forall_congr' fun i => ?_
  rw [p.int_iff]
  exact ⟨fun h => ⟨GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _, h⟩, fun h => h.2⟩

def scPair (c : 𝒪[k]) (hc : IsUnit c) {n : Type} [Fintype n] (i : n) : Pair k n where
  lat := stdLat k n
  isLat := inferInstance
  fn := c • (stdPair k i).fn
  fn_ne h := (stdPair k i).fn_ne (LinearMap.ext fun x => (hc.smul_eq_zero).1 (LinearMap.congr_fun h x))

theorem scPair_hasVal (c : 𝒪[k]) (hc : IsUnit c) {n : Type} [Fintype n] (i : n) (x : n → k) (hx : ∀ j, x j ∈ 𝒪[k]) :
    (scPair c hc i).HasVal x (residue 𝒪[k] (c * ⟨x i, hx i⟩)) :=
  ⟨mem_stdLat.2 hx, by
    show c • residue 𝒪[k] ⟨x i, _⟩ = _
    rw [map_mul, Algebra.smul_def]; rfl⟩

end StdExProof
end GlobalTheory.AdForm

namespace GlobalTheory.AdForm.StdExProof
open GlobalTheory.AdForm

theorem stdEx' : StdEx' := by
  intro B X I hI _hP l Z u ψ hψ L hL
  haveI hTf : Fact (B.T u).Prime := ⟨l.pr.T_prime u⟩
  obtain ⟨hcard, hirr⟩ := qt_facts (B.T u)
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hmem : ∀ i : (B.primes X).vT u, X.piT u ∈ i.1.asIdeal := fun i => (Formalism.L2.Col.mem_divs hne _).1 i.2
  have hconj : ∀ i : (B.primes X).vT u, B.fields.conjO (X.piT u) ∉ i.1.asIdeal := by
    intro i hc
    obtain ⟨a, b, hab⟩ := hcop
    exact i.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ i.1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i)) (Ideal.mul_mem_left _ b hc)))
  have hcP : ∀ i : (B.primes X).vT u, GlobalTheory.IdemSupport.cP (D := I.rec7 l Z) i.1 ≠ i.1 := by
    intro i h
    apply hconj i
    have h1 : X.piT u ∈ (GlobalTheory.IdemSupport.cP (D := I.rec7 l Z) i.1).asIdeal := by rw [h]; exact hmem i
    have h2 := (GlobalTheory.IdemSupport.mem_cP (D := I.rec7 l Z) i.1 (X.piT u)).1 h1
    have h3 : B.fields.conjO (X.piT u) = GlobalTheory.IdemSupport.cO (I.rec7 l Z) (X.piT u) := RingOfIntegers.ext rfl
    rw [h3]; exact h2
  choose e he using fun i : (B.primes X).vT u => GlobalTheory.StdFrames.exists_isIdemAt (hcP i)
  have hsplitT := (GlobalTheory.St.G.record_facts (I.rec7 l Z) u).1
  have hsp : ∀ i : (B.primes X).vT u, ∃ p : SplitPt (I.rec7 l Z) ℚ_[B.T u], p.e = e i := fun i =>
    (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).1 ℚ_[B.T u] (B.T u) hTf.out hcard hirr i.1 (e i) (he i) (he i).1
      (l.pr.vT_norm u _ i.2) (not_sq_dvd _ (B.T u) hTf.out hsplitT i.1 (by
        have h := Ideal.mul_mem_right (B.fields.conjO (X.piT u)) _ (hmem i)
        rw [l.pr.piT_norm u] at h
        exact h))
  choose p hpe using hsp
  have hidem : ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e i.1 := fun i => (hpe i).symm ▸ he i
  let wE : (B.primes X).vT u → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) := fun i => i.1
  have hv : ∀ i : (B.primes X).vT u, HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (wE i) = (p i).v := by
    intro i
    obtain ⟨ε, h1, h2⟩ := (p i).above
    exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (hidem i) h1 h2
  have hover := fun x => places_over (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl (l.pr.piT_norm u) hne x
  have hTv : ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := fun i =>
    (hover (p i).v).2 ⟨wE i, i.2, hv i⟩
  have hunit : ∀ i, (p i).UnitAA := fun i => GlobalTheory.FinPl.UnitAt.unitAA_level I l Z u (p i) (hTv i)
  have hpart2 := fun i => (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).2 ℚ_[B.T u] (p i)
  choose χ hχ using fun i => (hpart2 i).2 ψ hψ
  choose β hβ using fun j i => (hpart2 i).1 ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank) 1 1 (mul_one 1) (mul_one 1)
  have hβ' : ∀ j i, (β j i).b' = 1 := fun j i => by
    have := (β j i).bb'
    rwa [hβ j i, one_mul] at this
  have hrank : ∀ j, 0 < ((I.rec7 l Z).sp.X j).rank := by
    intro j
    obtain ⟨hs, h1, -⟩ := hI.spaces
    rw [show (I.rec7 l Z).sp.X j = B.sp.X j from rfl, h1 j]
    show 0 < B.R.k + j * (B.R.t + 1)
    have := B.R.m_add_three_le_k
    omega
  let c : (B.primes X).vT u → 𝒪[ℚ_[B.T u]] := fun i =>
    ⟨(p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)), pr_int (p i) (B.fields.conjO (X.piT u))⟩
  have hcv : ∀ i, valuation ℚ_[B.T u] ((p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E))) = 1 :=
    fun i => val_pr_eq_one (p i) (hidem i) (B.fields.conjO (X.piT u)) (hconj i)
  have hc : ∀ i, IsUnit (c i) := fun i =>
    (Valuation.integer.integers (valuation ℚ_[B.T u])).isUnit_iff_valuation_eq_one.2 (hcv i)
  let last : ∀ j, Fin ((I.rec7 l Z).sp.X j).rank := fun j => ⟨((I.rec7 l Z).sp.X j).rank - 1, by have := hrank j; omega⟩
  let Q : ∀ j, (B.primes X).vT u → Pair ℚ_[B.T u] (Fin ((I.rec7 l Z).sp.X j).rank) := fun j i => scPair (c i) (hc i) (last j)
  have hStd : StdT I l Z u p β Q L := by
    refine ⟨⟨Equiv.refl _, fun i => hidem i⟩, fun j hj => ⟨hL j hj, fun i => ⟨isLat_std (p i) _ (β j i) (hβ j i) (L j) (hL j hj), ?_⟩⟩⟩
    intro z hz r hr
    have hz' : ∀ r', IsIntegral ℤ (z r') := (hL j hj z).1 hz
    have hx : ∀ r', (p i).pr (incA (I.rec7 l Z) (z r')) ∈ 𝒪[ℚ_[B.T u]] := fun r' => pr_int (p i) ⟨z r', hz' r'⟩
    have hrl : r = last j := Fin.ext (by show r.1 = _ - 1; omega)
    subst hrl
    refine ⟨c i * ⟨_, hx (last j)⟩, ?_, ?_⟩
    · show (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) * (p i).pr (incA (I.rec7 l Z) (z (last j))) = _
      rw [← map_mul]
      exact congrArg _ (map_mul _ _ _).symm
    · rw [hβ' j i, Matrix.one_mulVec]
      exact scPair_hasVal (c i) (hc i) (last j) _ hx
  refine ⟨ℚ_[B.T u], inferInstance, inferInstance, inferInstance, inferInstance, (B.primes X).vT u, p, Finset.univ.toList,
    ⟨(B.T u : 𝒪[ℚ_[B.T u]]), hirr⟩, χ, β, Q, ⟨Finset.nodup_toList _, fun i => Finset.mem_toList.2 (Finset.mem_univ _),
    GlobalTheory.AdForm.StdT.places_injective I hI _hP l Z u p β Q L hStd, fun x => Iff.rfl, hunit⟩,
    fun i => ⟨(hχ i).2.2.2 (hunit i), (hχ i).1⟩, hcard, fun i => ⟨?_, hcv i⟩, fun x => ?_, hβ, hStd⟩
  · have hm : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) *
        (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) = (B.T u : ℚ_[B.T u]) := by
      have : ((X.piT u : B.fields.E) * (B.fields.conjO (X.piT u) : B.fields.E)) = ((B.T u : ℕ) : B.fields.E) := by
        exact_mod_cast congrArg (fun x : 𝓞 B.fields.E => (x : B.fields.E)) (l.pr.piT_norm u)
      have h2 : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) *
          (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) =
          (p i).pr (incA (I.rec7 l Z) (((B.T u : ℕ) : B.fields.E))) := by
        rw [← map_mul, ← this]
        exact congrArg _ (map_mul _ _ _).symm
      rw [h2]
      exact map_natCast ((p i).pr.comp (incA (I.rec7 l Z))) (B.T u)
    have hv2 := congrArg (valuation ℚ_[B.T u]) hm
    rw [map_mul, hcv i, mul_one] at hv2
    rw [hv2]
    rfl
  · rw [hover x]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨wE i, i.2, hv i⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, hv ⟨w, hw⟩⟩

end GlobalTheory.AdForm.StdExProof
