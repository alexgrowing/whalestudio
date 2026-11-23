import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfFischSelf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import Formalism.LocalToGlobal.Columns.StdLatUnimodular

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.HarmInCoef

open NumberField IsDedekindDomain Formalism.L2.DIV

theorem exists_nat_smul_mem_nabAtr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι]
    {n : ℕ} (emb : ι → E →+* K) (lam : ι → DomWeight n) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (h' : ∀ x ∈ L', a • x ∈ L) (w₀ : HeightOneSpectrum (𝓞 K)) (ha : a.Coprime (ringChar (𝓞 K ⧸ w₀.asIdeal)))
    {x : VV K lam} (hx : x ∈ nabAtr emb lam L) :
    ∃ s : ℕ, (s : 𝓞 K) ∉ w₀.asIdeal ∧ s • x ∈ nabAtr emb lam L' := by
  classical
  have hp : (ringChar (𝓞 K ⧸ w₀.asIdeal)).Prime := by
    haveI := w₀.isMaximal
    haveI : Finite (𝓞 K ⧸ w₀.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w₀.ne_bot
    letI := Ideal.Quotient.field w₀.asIdeal
    exact CharP.prime_ringChar _
  set p := ringChar (𝓞 K ⧸ w₀.asIdeal) with hpdef
  have hpw : ((p : ℕ) : 𝓞 K) ∈ w₀.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl
  let J : Ideal (𝓞 K) := (nabAtr emb lam L').comap (LinearMap.toSpanSingleton (𝓞 K) _ x)
  have hmemJ : ∀ r : 𝓞 K, r ∈ J ↔ r • x ∈ nabAtr emb lam L' := fun r => Iff.rfl
  have hJw : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → ¬ J ≤ w.asIdeal := by
    intro w hw hle
    have hcong := (GlobalTheory.GO.localization_nabAtr_delAtr_congr emb lam hL hL' h h' w
      (GlobalTheory.GO.natCast_notMem_of_coprime ha w hw)).1
    have hx0 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L) :=
      ⟨1, fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hx⟩
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L') := hcong ▸ hx0
    obtain ⟨u, hu, hux⟩ := hx'
    exact hu (hle ((hmemJ u).2 hux))
  have hp0 : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hJp : J ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpm : ((p : ℕ) : 𝓞 K) ∈ m := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hm0 : m ≠ ⊥ := fun h0 => hp0 (by rw [h0] at hpm; exact (Submodule.mem_bot _).1 hpm)
    exact hJw ⟨m, hm.isPrime, hm0⟩ hpm (le_sup_left.trans hle)
  have hJ0 : J ≠ ⊥ := fun h0 => hJw w₀ hpw (h0 ▸ bot_le)
  refine ⟨Ideal.absNorm J, ?_, ?_⟩
  · intro hmem
    have hdvd : p ∣ Ideal.absNorm J := by
      refine (ringChar.spec (𝓞 K ⧸ w₀.asIdeal) _).1 ?_
      rw [← map_natCast (Ideal.Quotient.mk w₀.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite (𝓞 K ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hJ0
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ J) p
      (by rwa [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply])
    have h1mem : (1 : 𝓞 K) ∈ J ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := hJp ▸ Submodule.mem_top
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1mem
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have h1 : Ideal.Quotient.mk J (c * (p : 𝓞 K)) = 1 := by
      rw [← map_one (Ideal.Quotient.mk J), ← hjy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
    have hpz : p • z = 0 := hz ▸ addOrderOf_nsmul_eq_zero z
    have hz0 : z = 0 := by
      calc z = Ideal.Quotient.mk J (c * (p : 𝓞 K)) * z := by rw [h1, one_mul]
        _ = Ideal.Quotient.mk J c * (p • z) := by rw [map_mul, nsmul_eq_mul, map_natCast]; ring
        _ = 0 := by rw [hpz, mul_zero]
    rw [hz0, addOrderOf_zero] at hz
    exact hp.one_lt.ne hz
  · rw [← Nat.cast_smul_eq_nsmul (𝓞 K)]
    exact (hmemJ _).1 (Ideal.absNorm_mem J)

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open NumberField MvPolynomial Formalism.L2.Pj

theorem coeff_aeval_scale {σ K : Type} [Field K] (t : K) (P : MvPolynomial σ K) (m : σ →₀ ℕ) :
    (aeval (fun i => C t * X i) P).coeff m = t ^ (m.sum fun _ e => e) * P.coeff m := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
    have e : aeval (fun i => C t * X i) (monomial d a) = monomial d (t ^ (d.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_pow, Finsupp.prod_mul, Finsupp.prod, Finsupp.sum,
        Finset.prod_pow_eq_pow_sum, C_mul, C_pow, algebraMap_eq]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    rw [e, coeff_monomial, coeff_monomial]
    by_cases h : d = m
    · subst h; simp
    · simp [h]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (c : Coeff l)

theorem symO_std_le {n : ℕ} :
    symO (Dw := Dw) c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n) ≤
      (MvPolynomial.map (algebraMap (integralClosure ℤ c.F) c.F)).range := by
  refine (Subring.closure_le).2 ?_
  rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
  · exact ⟨C o, by simp⟩
  · have hb' : ∀ j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = b j := fun j => by
      have := (Submodule.mem_pi.1 hb) j (Set.mem_univ _)
      exact Submodule.mem_one.1 this
    choose y hy using hb'
    have hint : ∀ j, IsIntegral ℤ (embF c σ (b j)) := fun j => by
      rw [← hy j]
      exact (RingOfIntegers.isIntegral_coe (y j)).map (embF c σ).toIntAlgHom
    refine ⟨∑ j, C (⟨embF c σ (b j), (mem_integralClosure_iff ℤ c.F).2 (hint j)⟩ : integralClosure ℤ c.F) *
      X (⟨σ, i, j⟩ : LtN Dw n), ?_⟩
    simp [letB]

theorem scale_mem_symO {n : ℕ} (Λ : GenLat E n) (k : ℕ) (hk : ∀ b ∈ Λ.La, (k : 𝓞 E) • b ∈ Formalism.L2.Pj.stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) :
    aeval (fun i => C (k : c.F) * X i) P ∈ symO c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n) := by
  let φ : MvPolynomial (LtN Dw n) c.F →+* MvPolynomial (LtN Dw n) c.F :=
    (aeval (fun i => C (k : c.F) * X i) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] _).toRingHom
  have hle : symO c Λ ≤ (symO c (⟨Formalism.L2.Pj.stdLat E n⟩ : GenLat E n)).comap φ := by
    refine (Subring.closure_le).2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨o, ?_⟩)
      simp [φ]
    · refine Subring.subset_closure (Or.inr ⟨σ, i, (k : 𝓞 E) • b, hk b hb, ?_⟩)
      simp only [φ, letB, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, aeval_C, aeval_X,
        algebraMap_eq, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← C_mul]
      congr 2
      rw [Algebra.smul_def, map_mul, map_natCast, map_natCast, mul_comm]
  exact hle hP

theorem exists_pow_mul_coeff_integral {n : ℕ} (Λ : GenLat E n) (k : ℕ) (hk : ∀ b ∈ Λ.La, (k : 𝓞 E) • b ∈ Formalism.L2.Pj.stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) :
    ∃ D : ℕ, ∀ m, IsIntegral ℤ ((k : c.F) ^ D * P.coeff m) := by
  refine ⟨P.totalDegree, fun m => ?_⟩
  by_cases hm : m ∈ P.support
  · obtain ⟨Q, hQ⟩ := symO_std_le c (scale_mem_symO c Λ k hk hP)
    have h1 : IsIntegral ℤ ((k : c.F) ^ (m.sum fun _ e => e) * P.coeff m) := by
      rw [← coeff_aeval_scale, ← hQ, coeff_map]
      exact (mem_integralClosure_iff ℤ c.F).1 (Q.coeff m).2
    have h2 : (m.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hm
    rw [← Nat.sub_add_cancel h2, pow_add, mul_assoc]
    have hk' : IsIntegral ℤ (k : c.F) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ c.F (k : ℤ)))
    exact (hk'.pow _).mul h1
  · rw [notMem_support_iff.1 hm, mul_zero]
    exact isIntegral_zero

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open MvPolynomial Formalism.L2.Pj

theorem smul_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop} {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ HHa r n k cc isX a) (t : k) : t • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ t hP.1, fun σ i i' h s => by rw [map_smul, hP.2.1 σ i i' h s],
    fun m hm σ i => hP.2.2 m (MvPolynomial.support_smul hm) σ i⟩

theorem map_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k K : Type} [Field k] [CharZero k] [Field K] (f : k →+* K)
    {cc : T → T} {isX : T → Prop} {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map f P ∈ HHa r n K cc isX a :=
  ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map f hP.1, GlobalTheory.RowSpan.rowInv_map f hP.2.1,
    fun m hm => hP.2.2 m (MvPolynomial.support_map_subset f P hm)⟩

theorem coeff_smul_map_mem {σ k K : Type} [Field k] [Field K] (f : k →+* K) (t : k) (P : MvPolynomial σ k) (m : σ →₀ ℕ)
    (h : IsIntegral ℤ (t * P.coeff m)) :
    (f t • MvPolynomial.map f P).coeff m ∈ (integralClosure ℤ K).toSubring := by
  rw [coeff_smul, coeff_map, smul_eq_mul, ← map_mul]
  exact Subalgebra.mem_toSubring.2 ((mem_integralClosure_iff ℤ _).2 (h.map f.toIntAlgHom))

end GlobalTheory.HarmInCoef

namespace GlobalTheory.HarmInCoef

open NumberField IsDedekindDomain MvPolynomial Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.FWT

set_option maxHeartbeats 1000000 in

theorem harm_mem_coefLat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (lam : HeightOneSpectrum (𝓞 D.what₂.LL)), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∀ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)), ∃ (y : VsV D i (O i).c'.F) (s : ℕ), (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P ∧ (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ InCoefLat R i h ((s : ℂ) • (O i).c0' y) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT _hk i hpins Λ h _hsplit hLa lam htriv P hP

  obtain ⟨hfield, hP'⟩ := hpins
  obtain ⟨k, hkcop, hk1, hk2⟩ := htriv
  have hlift := hP'.lift
  obtain ⟨gramR, c0R, c0L, hFT, hC0⟩ := hlift.c0
  have hfld : (inC (O i).c').comp (O i).jL = D.what₂.embLL := hlift.field
  obtain ⟨_, cga, hIo⟩ := hP'.io
  have hsub := hIo.2.2.2.2.2.2.2

  have hp : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
    haveI := lam.isMaximal
    haveI : Finite (𝓞 D.what₂.LL ⧸ lam.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ lam.ne_bot
    letI := Ideal.Quotient.field lam.asIdeal
    exact CharP.prime_ringChar _
  have hplam : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.1 hkcop)
  have hklam : ((k : ℕ) : 𝓞 D.what₂.LL) ∉ lam.asIdeal := GlobalTheory.GO.natCast_notMem_of_coprime hkcop lam hplam

  have hkΛ : ∀ b ∈ Λ.La, (k : 𝓞 D.host.E) • b ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := fun b hb =>
    hk1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hb)
  obtain ⟨Dg, hDg⟩ := exists_pow_mul_coeff_integral _ Λ k hkΛ hP.2

  set f := incF T.J.toCore.Q.c (O i).c' (O i).hle with hf
  have hQ : f ((k : T.Q.c.F) ^ Dg) • MvPolynomial.map f P ∈ harmA (Dw := T.J.toCore.Q.Dw ((i : ℕ) + 1)) (O i).c'
      (wtA (κ i)) (Vc D i).rank :=
    ⟨smul_mem_HHa (map_mem_HHa f hP.1) _, fun m => coeff_smul_map_mem f _ P m (hDg m)⟩
  obtain ⟨y0, hy0, hy0io⟩ := hsub hQ

  have hsurj : Function.Surjective (O i).jL := by
    intro z
    have hz : (z : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hfield ▸ z.2
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.1 hz
    refine ⟨a, Subtype.ext ?_⟩
    exact (RingHom.congr_fun hfld a).trans ha
  let e : D.what₂.LL ≃+* (O i).c'.F := RingEquiv.ofBijective (O i).jL ⟨(O i).jL.injective, hsurj⟩
  have hje : (O i).jL.comp (e.symm : (O i).c'.F →+* D.what₂.LL) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    exact e.apply_symm_apply z
  let F0 : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank := MvPolynomial.map (e.symm : (O i).c'.F →+* D.what₂.LL) (y0 : Pol _ _ _)
  have hF0 : MvPolynomial.map (O i).jL F0 = (y0 : Pol _ _ _) := by
    rw [MvPolynomial.map_map, hje, MvPolynomial.map_id]
  have hx0V : F0 ∈ VV D.what₂.LL (lamV D i) :=
    ((Formalism.L2.DIV.baseChangeSpace_holds D.what₂.LL (O i).c'.F (O i).jL D.what₂.Tau (Vc D i).rank (lamV D i)).1 F0).2
      (hF0 ▸ y0.2)
  let x0 : VsV D i D.what₂.LL := ⟨F0, hx0V⟩

  have hstd : Submodule.IsLattice D.host.E (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank) := by
    have := GlobalTheory.RepsCompare.isLattice_hLat (Vc D i) 1
    rw [hlift.std.2] at this
    exact this
  have hemb : (fun τ => (O i).jL.comp (labLL D τ)) = fun τ => embF (O i).c' (tauE D τ) :=
    funext fun τ => embV_eq_embF (O i).c' (O i).jL hfld τ
  have hx0nab : x0 ∈ nabAtr (labLL D) (lamV D i) (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank) := by
    refine ((Formalism.L2.DIV.nablaDeltaDescentAt_holds D.host.E D.what₂.LL (O i).c'.F (O i).jL D.what₂.Tau (Vc D i).rank
      (labLL D) (lamV D i) _ hstd x0 y0 hF0.symm).2.2.1).2 ?_
    rw [hemb]
    exact hy0

  have hstarStd : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank,
      (fun b => star (x b)) ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := by
    intro x hx
    refine Submodule.mem_pi.2 fun j _ => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 hx) j (Set.mem_univ _))
    have hint : IsIntegral ℤ (star (x j)) := by
      rw [← hy]
      exact (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom
    exact Submodule.mem_one.2 ⟨⟨star (x j), (mem_integralClosure_iff ℤ _).2 hint⟩, rfl⟩
  have hcmp1 : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank, k • x ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h) := by
    intro x hx
    have h2 : (k : 𝓞 D.host.E) • (fun b => star (x b)) ∈ Λ.La :=
      hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hstarStd x hx))
    have h3 := (hLa _).1 h2
    convert h3 using 1
    funext b
    simp [Algebra.smul_def, star_mul', star_natCast]
  have hcmp2 : ∀ x ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h), k • x ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := by
    intro x hx
    have h1 : (fun b => star (x b)) ∈ Λ.La := (hLa _).2 (by simpa using hx)
    have h2 : (k : 𝓞 D.host.E) • (fun b => star (x b)) ∈ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank :=
      hk1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) h1)
    have h3 := hstarStd _ h2
    convert h3 using 1
    funext b
    simp [Algebra.smul_def, star_mul', star_natCast]
  obtain ⟨s, hs, hsx⟩ := exists_nat_smul_mem_nabAtr (labLL D) (lamV D i) hstd
    (GlobalTheory.RepsCompare.isLattice_hLat (Vc D i) (fin (Vc D i) h)) hcmp1 hcmp2 lam hkcop hx0nab

  obtain ⟨v', hv'pol, hv'c⟩ := hC0 (s • x0)
  have hv'eq : v' = s • y0 := by
    apply Subtype.ext
    rw [hv'pol]
    show MvPolynomial.map (O i).jL (s • F0) = s • (y0 : Pol _ _ _)
    rw [map_nsmul, hF0]
  set r : (O i).c'.F := f ((k : T.Q.c.F) ^ Dg) with hrdef
  have hr : r = (k : (O i).c'.F) ^ Dg := by rw [hrdef]; erw [map_pow, map_natCast]
  have hr0 : r ≠ 0 := by rw [hr]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hk0)
  refine ⟨r⁻¹ • y0, s * k ^ Dg, ?_, ?_, ?_⟩
  · rw [map_smul, hy0io]
    exact inv_smul_smul₀ hr0 _
  · push_cast
    intro hm
    rcases lam.isPrime.mem_or_mem hm with h1 | h1
    · exact hs h1
    · exact hklam (lam.isPrime.mem_of_pow_mem _ h1)
  · refine ⟨gramR, c0R, c0L, hFT, s • x0, hsx, ?_⟩
    have hsm : (s * k ^ Dg) • (r⁻¹ • y0) = s • y0 := by
      rw [← Nat.cast_smul_eq_nsmul (O i).c'.F, ← Nat.cast_smul_eq_nsmul (O i).c'.F s, smul_smul, Nat.cast_mul,
        Nat.cast_pow, ← hr, mul_assoc, mul_inv_cancel₀ hr0, mul_one]
    refine Eq.trans ?_ hv'c
    rw [hv'eq, ← hsm, map_nsmul, Nat.cast_smul_eq_nsmul]

end GlobalTheory.HarmInCoef
