import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHoldsStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmEmbeddingConjugateCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeHeightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeCountStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBoundStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq

theorem isCp_dvd_sq (Ω : Type) [Field Ω] (A : Subring Ω) (p : ℕ) [hp : Fact p.Prime] (κ : Ω) (hκA : κ ∈ A)
    (hκ : HT.IsCp p κ) : ∃ u ∈ A, (p : Ω) ^ 2 = κ * u := by
  unfold HT.IsCp at hκ
  split_ifs at hκ with h2
  · exact ⟨1, A.one_mem, by rw [hκ, h2]; norm_num⟩
  · obtain ⟨ζ, hζ, rfl⟩ := hκ
    have hζA : ζ ∈ A := by simpa using A.add_mem hκA A.one_mem
    have hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0 := hζ.geom_sum_eq_zero hp.out.one_lt
    have hp' : (p : Ω) = ∑ i ∈ Finset.range p, (1 - ζ ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    have hterm : ∀ i, (1 : Ω) - ζ ^ i = (1 - ζ) * ∑ j ∈ Finset.range i, ζ ^ j := fun i => by
      rw [mul_comm, geom_sum_mul_neg]
    have hv : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) ∈ A :=
      A.sum_mem fun i _ => A.sum_mem fun j _ => A.pow_mem hζA j
    have hpv : (p : Ω) = -(ζ - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j := by
      rw [hp', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm]
      ring
    refine ⟨-(p : Ω) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j,
      A.mul_mem (A.neg_mem (natCast_mem A p)) hv, ?_⟩
    calc (p : Ω) ^ 2 = p * p := sq _
      _ = p * (-(ζ - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) := by rw [← hpv]
      _ = _ := by ring

theorem generatesDiff_one {O Ω E : Type} [CommRing O] [Field Ω] [Algebra O Ω] [Field E] [NumberField E]
    (R : Subalgebra O Ω) (σ : E →+* Ω) (h1 : ∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E))
    (h2 : ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1) :
    HT.GeneratesDiff σ (1 : R) := by
  have hmem : ∀ a : 𝓞 E, σ (a : E) ∈ R := fun a => by
    obtain ⟨o, ho⟩ := h1 a
    rw [← ho]
    exact R.algebraMap_mem o
  obtain ⟨x, hx, o, ho⟩ := h2
  unfold HT.GeneratesDiff
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, map_one]
    have : (1 : Ω) = (algebraMap O R o) • σ (x : E) := by
      rw [← ho]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨z, -, rfl⟩
    have : σ (z : E) = (⟨σ (z : E), hmem z⟩ : R) • algebraMap R Ω 1 := by
      rw [map_one]; exact (_root_.mul_one _).symm
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem seq_holds : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (t : CMType H ⊕ CMType H), ∃ i : (Fin (labelRk D t) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p t) (b t) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p t.swap) (b t.swap) c')) i (qMap P (b t.swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb t a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p t) (b t) c') (b t) i := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hA hpq p _ hpS hfree hp2 hdisc b hb A _ _ _ m _ hpm O _ _ _
    _ _ _ _ w hw G c' hc' P t
  obtain ⟨hchar, hN, hI, hFr, hreg, hpt⟩ := GlobalTheory.T.arith_variety_prime_hodge_relay E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS A m hpm O c' hc'
  haveI := hchar
  haveI := hN
  haveI := hI
  haveI := hFr
  have hc : ∀ x, HT.cmConj E (HT.cmConj E x) = x := fun x => by simp [HT.cmConj]
  obtain ⟨σ, hσ, hσ', huniq⟩ := GlobalTheory.T.cm_embedding_conjugate_compat E H D l Xo c O₀ β Y S Ω K J y 𝔐 t
  have hd := GlobalTheory.T.arith_variety_prime_hodge_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hdisc A m hpm O
  have hgd : ∀ τ : E →+* Ω, HT.GeneratesDiff τ (1 : CR O y c') := fun τ =>
    generatesDiff_one _ τ (hd τ).1 (hd τ).2
  have hloc := GlobalTheory.T.arith_variety_prime_hodge_height E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS A m hpm O G c' hc' P
  obtain ⟨hpO, hpH⟩ := GlobalTheory.T.arith_variety_prime_hodge_value E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hfree hdisc A m hpm O G c' hc' P hN hpt hloc
  have htest := GlobalTheory.T.arith_variety_model_prime_relay hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hp2 A m hpm O w hw G c' hc' P
  have hR := 𝔐.R_ge p hpS
  obtain ⟨n, hn⟩ : ∃ n, 𝔐.R p = (n + 2) + 2 := ⟨𝔐.R p - 4, by omega⟩
  have hm : 𝔐.R p - 2 = n + 2 := by omega
  obtain ⟨u, huR, hu⟩ := isCp_dvd_sq Ω (CR O y c').toSubring p (algebraMap O Ω w)
    ((CR O y c').algebraMap_mem w) hw
  have hdiv : algebraMap O (CR O y c') w * (p : CR O y c') ^ (𝔐.R p - 2) ∣ (p : CR O y c') ^ (𝔐.R p) := by
    refine ⟨⟨u, huR⟩, Subtype.ext ?_⟩
    rw [hm, hn]
    push_cast
    rw [pow_add (p : Ω) (n + 2) 2, hu]
    ring
  obtain ⟨-, hseq⟩ := GlobalTheory.T.chart_sequence_holds (CR O y c') Ω E (HT.cmConj E) hc p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) P.Dh
    (algebraMap O (CR O y c') w) (𝔐.R p - 2) hdiv htest hpO
  obtain ⟨i₀, hDm, hEx⟩ := hseq σ 1 1 (hgd σ) (hgd _) (hpH t σ hσ) (hpH t.swap _ hσ')
  have hact : ∀ (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), P.Dh.ρΩ a w = w ∘ₗ 𝔐.ρ (RingOfIntegers.mapRingEquiv (HT.cmConj E) a) :=
    fun a w => by
      rw [HT.ModelTest.bar_eq H a]
      exact P.Dh_act a w
  have hV : ∀ (s : CMType H ⊕ CMType H) (τ : E →+* Ω), (∀ a : 𝓞 E, τ (a : E) = 𝔐.emb s a) →
      Submodule.span Ω (Set.range (b s)) = HT.eigSp 𝔐.ρ τ := by
    intro s τ hτ
    rw [(hb s).2]
    unfold HodgeCpt.Vgen GlobalTheory.CompanionTheory.Ar.eigSp HT.eigSp
    refine iInf_congr fun a => ?_
    rw [hτ a]
    rfl
  have hcoord := fun (s : CMType H ⊕ CMType H) (τ : E →+* Ω) (hτ : ∀ a : 𝓞 E, τ (a : E) = 𝔐.emb s a) =>
    GlobalTheory.T.arith_variety_prime_hodge_count E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS b hb A m hpm O G c' hc' P s
      (fun a => by rw [← hτ a]; exact (hd τ).1 a)
      (by
        obtain ⟨x, hx, o, ho⟩ := (hd τ).2
        exact ⟨x, hx, o, by rw [← hτ x]; exact ho⟩) hreg hpt hloc
  have hwu : ∃ v ∈ CR O y c', (p : Ω) ^ (𝔐.R p - 2) = algebraMap O Ω w * v := by
    refine ⟨u * (p : Ω) ^ n, (CR O y c').mul_mem huR ((CR O y c').pow_mem (natCast_mem _ p) n), ?_⟩
    rw [hm, pow_add, mul_comm ((p : Ω) ^ n), hu]
    ring
  obtain ⟨i, h1, h2⟩ := GlobalTheory.T.hodge_chart_exists_seqHyp_gram_congr_mod_pow O Ω 𝔐.Li (CR O y c') E (HT.cmConj E) hc p (𝔐.R p) (D.p + D.q) _ _ (𝔐.R p - 2) P.Dh 𝔐.ρ hact σ
    i₀ hEx hDm (hpH t σ hσ) (b t) (b t.swap) (hb t).1 (hV t σ hσ) (hb t.swap).1 (hV t.swap _ hσ') _ _
    (hcoord t σ hσ) (hcoord t.swap _ hσ') (algebraMap O Ω w) ((CR O y c').algebraMap_mem w) hwu
  refine ⟨i, h1, fun σE hσE a ha j => ?_⟩
  rw [huniq σE hσE]
  exact h2 a ha j

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq
