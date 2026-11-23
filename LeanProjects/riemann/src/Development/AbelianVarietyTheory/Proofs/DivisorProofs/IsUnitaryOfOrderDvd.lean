import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHCharN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterTrivialSubfieldKillsIdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedInertKillsUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.XiSplit

open Formalism.L2.Host

theorem isUnitary_of_orderDvd {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) : χ.IsUnitary := by
  intro x
  have h1 : (χ.1 x) ^ n = 1 := by
    have : (χ ^ n).1 x = 1 := by rw [h]; rfl
    rw [← this]; rfl
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  rw [MonoidHom.finset_prod_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem smul_eq_of_isConjPl {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (hc : Formalism.IndefR.Lev.IsConjPl w w') :
    D.host.conj • w.asIdeal = w'.asIdeal := by
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hzv, hz⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hz.trans (GlobalTheory.TypePlaces.star_eq_conj D _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hzv
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  exact hmax.eq_of_le w'.isPrime.ne_top hle

theorem isConjPl_of_smul_eq {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : D.host.conj • w.asIdeal = w'.asIdeal) : Formalism.IndefR.Lev.IsConjPl w w' := fun c hc =>
  ⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩

theorem unrAt_of_inert {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    (L.xiH t).UnrAt P := by
  obtain ⟨q, -, hI, hqP⟩ := hP
  have hfix : D.host.conj • P.asIdeal = P.asIdeal := hI P.asIdeal P.isPrime P.ne_bot hqP
  by_contra h
  rcases (hL.Q_ram t P).1 h with hPQ | ⟨P', hP', hc⟩
  · exact ((hL.Q_pl t) P hPQ).2 P hPQ (isConjPl_of_smul_eq hfix)
  · have e1 := (smul_eq_of_isConjPl hc).trans hfix.symm
    have e2 : P'.asIdeal = P.asIdeal := by
      simpa using congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e1
    have e3 : P' = P := HeightOneSpectrum.ext e2
    subst e3
    exact ((hL.Q_pl t) P' hP').2 P' hP' hc

theorem exists_heckeU_xi : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    ∃ χ : HeckeU D 0, (∀ x, χ.f x = (L.xiH t).1 (finIdl D x)) ∧ ∀ τ, χ.n τ = 0 := by
  intro D T L μ₀ hL t
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hu : (L.xiH t).IsUnitary := isUnitary_of_orderDvd hn ho
  have hi : (L.xiH t).HasInf (Formalism.L2.Host.embTau D) 0 := fun k => by
    rw [inf_eq_one hn ho k]
    simp
  have hp : ∀ τ, Even ((0 : D.what₂.Tau → ℤ) τ - ((0 : ℕ) : ℤ)) := fun τ => by simp
  have hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) →
      (L.xiH t).1 (finIdl D u) = 1 := by
    obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (L.xiH t)
    refine ⟨M, hM, fun u hu ⟨s, hs, e⟩ => h _ (GlobalTheory.Mem.Col2.SplitChar.finIdl_unit hu)
      (fun w => by rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_fst]; rfl) fun P => ?_⟩
    rw [GlobalTheory.Mem.Col2.SplitChar.vl_sub_one, e, map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs P)
  have hnorm := GlobalTheory.NuCharNorm.chi_norm_one D (L.xiH t) (hL.xi_triv t)
    (GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (L.xiH t))
  have hr := GlobalTheory.UnrKill.unr_kill D (L.xiH t) (unrAt_of_inert hL t)
  exact ⟨GlobalTheory.SplitCharGen.ofHChar 0 (L.xiH t) 0 hu hi hp hc hnorm hr, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.XiSplit
