import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsBuiltAndNot
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasResOfValSubLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.StdOff

section Gen

open GlobalTheory.FinPl GlobalTheory.FinPl.AlmostAll GlobalTheory.FinPl.AeUnit

variable {D : D7}

theorem incA_mul_mem_intAt {v : Pl D} {c : D.host.E} {N : ℕ} (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal)
    (hint : IsIntegral ℤ ((N : D.host.E) * c)) : ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro a ha
  have hv' : ((N : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by rwa [Int.cast_natCast]
  have hN : N ≠ 0 := by
    rintro rfl
    exact hv (by simp)
  have hNF : ((N : ℤ) : D.host.F) ≠ 0 := by exact_mod_cast hN
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, inv_smul_singleV_mem v N hv', ⟨(N : ℤ) • c, by rw [zsmul_eq_mul, Int.cast_natCast]; exact hint⟩, ?_⟩
  exact tmul_eq_inv_smul_tmul N hNF _ c

theorem latA_eq_latV_of {v : Pl D} {N M : ℕ} (hvN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (hvM : (M : 𝓞 D.host.F) ∉ v.asIdeal)
    (hNI : ∀ a ∈ D.host.AA, ∃ b : 𝓞 D.host.E, algebraMap _ _ b = a * (N : D.host.E)) (hMI : (M : D.host.E) ∈ D.host.AA)
    (S : HSp D) (L : Lat S) : latA S L (· = v) = latV S L (· = v) := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact hvN (by simp)
  have hM : M ≠ 0 := by
    rintro rfl
    exact hvM (by simp)
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨h1, h2⟩ := smul_inv_mem hvN hα h0
    refine ⟨_, h1, h2, 1, rfl, b • x, L.smul_mem b hx, funext fun i => ?_⟩
    rw [tmul_eq hN, ← mul_assoc, mul_comm (N : D.host.E) a, ← hb, one_mul, Pi.smul_apply, Algebra.smul_def b]
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain rfl : a = 1 := ha
    obtain ⟨h1, h2⟩ := smul_inv_mem hvM hα h0
    refine ⟨_, h1, h2, (M : D.host.E), hMI, x, hx, funext fun i => ?_⟩
    rw [tmul_eq hM, one_mul]

theorem notMem_of_coprime {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsPrime) {a b : ℕ} (h : a.Coprime b) (hb : (b : R) ∈ P) :
    (a : R) ∉ P := fun ha => by
  obtain ⟨x, y, hxy⟩ : IsCoprime (a : R) (b : R) := Nat.Coprime.cast h
  exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitAA_of (p : SplitPt D k) {l : ℕ} (hl : l.Prime) (hv : (l : 𝓞 D.host.F) ∈ p.v.asIdeal)
    (hq : (D.host.QS * D.host.q).Coprime l) (hd : D.host.d.Coprime l) (hc : (Ideal.absNorm D.host.ccK).Coprime l) : p.UnitAA := by
  have hb : (Ideal.absNorm D.host.𝔟).Coprime l := by
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd, GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hl, ← hl.coprime_iff_not_dvd]
    exact hq.symm
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hd4 : 2 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs2 := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hs2
    exact hd0 (neg_eq_zero.1 hs2.symm)
  have hsi : IsIntegral ℤ D.host.sqrtMinusD := IsIntegral.of_pow two_pos (by rw [hs2]; exact (isIntegral_natCast _).neg)
  refine ⟨fun a ha => ⟨incA_mul_mem_intAt (N := Ideal.absNorm D.host.ccK * D.host.d)
    (notMem_of_coprime p.v.isPrime (hc.mul_left hd) hv) ?_ a ha, incA_mul_mem_intAt (N := 1)
    (notMem_of_coprime p.v.isPrime (Nat.coprime_one_left l) hv) ?_ a ha⟩,
    latA_eq_latV_of (notMem_of_coprime p.v.isPrime hb hv) (notMem_of_coprime p.v.isPrime hc hv)
      (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)⟩
  · convert hsi using 1
    unfold Host.xi0
    push_cast
    field_simp
    linear_combination -hs2
  · have : ((1 : ℕ) : D.host.E) * D.host.xi0⁻¹ = -((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) := by
      unfold Host.xi0
      rw [Nat.cast_one, one_mul, inv_div, div_neg, div_one]
    rw [this]
    exact ((isIntegral_natCast _).mul hsi).neg

theorem mxAt_of_half (q : SplitPt D k) {m n : ℕ} {w : Mx D m n} (h : IsHalf (q.e + cA D q.e) w) : MxAt (· = q.v) w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff, ← h2]
  exact h i j

theorem sec_mem_idAt (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  have h1 : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have h2 : (p.e + cA D p.e) * p.sec a = p.sec a := by
    rw [← h1, ← mul_assoc, add_mul, p.split.1, mul_comm (cA D p.e), p.split.2.1, add_zero]
  exact mxAt_of_half p (m := 1) (n := 1) (w := Matrix.of fun _ _ => p.sec a) (fun _ _ => h2) 0 0

theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) : idAt D P ≤ idAt D Q := fun _ ha =>
  Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 ha).1, (Submodule.mem_iInf _).2 fun u =>
    (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 ha).2 ⟨u.1, fun hu => u.2 (h _ hu)⟩⟩

theorem mem_latV_int {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (v : Pl D) (y : Fin S.rank → AE D) :
    y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intAt D (· = v) :=
  GlobalTheory.FinPl.Model.mem_latV_std S L (fun x => (hL x).trans (forall_congr' fun i =>
    ⟨fun h => ⟨⟨x i, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩)) v y

def intLat (S : HSp D) : Lat S := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)

end Gen

section Loc

open GlobalTheory.LatPair IsLocalRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

section Level

open GlobalTheory.FinPl

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E}

end Level

theorem exists_vT_over {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (v' : HeightOneSpectrum (𝓞 X.F))
    (hT : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v'.asIdeal) : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v' := by
  have hinj : Function.Injective (algebraMap (𝓞 X.F) (𝓞 X.E)) := by
    intro x y e
    apply RingOfIntegers.ext
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) e
    simpa using this
  haveI : Algebra.IsIntegral (𝓞 X.F) (𝓞 X.E) := inferInstance
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 X.E) v'.asIdeal ⊥ (by
    rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hQ
    exact v'.ne_bot hQ.symm
  let QQ : HeightOneSpectrum (𝓞 X.E) := ⟨Q, hQp, hQ0⟩
  have hTQ : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ QQ.asIdeal := by
    have : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) Q := hQ ▸ hT
    simpa using this
  rw [← hPr.piT_norm u] at hTQ
  rcases hQp.mem_or_mem hTQ with hπ | hπ
  · exact ⟨QQ, (GlobalTheory.MuOffMove.mem_vT hPr u QQ).2 hπ, HeightOneSpectrum.ext hQ⟩
  · refine ⟨Formalism.L2.Col.conjPrime₂ QQ, (GlobalTheory.MuOffMove.mem_vT hPr u _).2 ((Formalism.L2.Col.mem_conjP _ _).2 ?_), HeightOneSpectrum.ext ?_⟩
    · exact hπ
    · show Ideal.under _ _ = _
      rw [GlobalTheory.MuOffMove.under_conjP hX]
      exact hQ

end GlobalTheory.SeeSaw.StdOff

end
