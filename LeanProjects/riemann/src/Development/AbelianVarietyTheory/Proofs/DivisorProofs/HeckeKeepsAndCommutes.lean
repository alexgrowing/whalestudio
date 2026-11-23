import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeOffLevel

variable {D : D7}

theorem sep_of_offS {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q PP : HeightOneSpectrum (𝓞 D.host.E)}
    (hS : OffS D S Q) (hP : PP.under (𝓞 D.host.F) ∈ S) : PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q := by
  obtain ⟨x, hx, hQ⟩ := hS _ hP
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  refine ⟨fun h => hQ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl (h ▸ hx'), fun h => ?_⟩
  obtain ⟨c, hc, e⟩ := h _ hx'
  exact hQ c (e.trans ((D.sp.cm.fixed _).2 ⟨x, rfl⟩)) hc

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_mul : ∀ k ∈ Lev.levG V β L, ∀ k' ∈ Lev.levG V β L,
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  intro k hk k' hk'
  unfold Lev.levChi
  rw [MonoidHom.map_mul, ← Units.val_mul]
  exact congrArg Units.val ((levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {Rp : Finset (GA D V)}

theorem hasType_heckeLin (hB : Lev.IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q)
    (h : Hecke₂ V (Lev.levG V β L : Set (GA D V)) (Lev.levChi V β L) S Q d Rp) {Φ : GA D V → ℂ}
    (hΦ : Lev.HasType V β L Φ) : Lev.HasType V β L (heckeLin V Rp Φ) :=
  GlobalTheory.SphericalOps.level_heckeLin levChi_mul
    (fun e f _ hi => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 Q e f hi hN hP).2.2) h hΦ

theorem actL_heckeLin (hB : Lev.IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q)
    (h : Hecke₂ V (Lev.levG V β L : Set (GA D V)) (Lev.levChi V β L) S Q d Rp) (g0 : G0 L.Pg L.r)
    {Φ : GA D V → ℂ} (hΦ : Lev.HasType V β L Φ) :
    actL V β L g0 (heckeLin V Rp Φ) = heckeLin V Rp (actL V β L g0 Φ) := by
  have hT := hasType_heckeLin hB hN hP h hΦ
  show Lev.actG0 V β L g0 _ = heckeLin V Rp (Lev.actG0 V β L g0 Φ)
  unfold Lev.actG0
  split_ifs with hk
  swap
  · rw [LinearMap.map_zero]
  have hκ := hk.choose_spec
  generalize hk.choose = κ at hκ ⊢
  obtain ⟨e, f, ϖ, α, -, hi, -, -, -, hJ, hχ, -, -, hR, -⟩ := h
  obtain ⟨a1, -, a3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (Lev.flagL L) hB).2 Q e f hi hN hP
  obtain ⟨k₁, m₁, k₂, -, s₁, s₂, rfl⟩ := a3 κ ⟨hκ.1, hκ.2.1, Subgroup.mem_top _⟩
  have m₁' : k₁ ∈ Lev.levG V β L := (hJ k₁ s₁).2 ((a1 k₁ s₁).1 m₁)
  have c₁ := hχ k₁ m₁' s₁
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 Q e f hi).1
  have hc : ∀ a, SuppF V f a → a * k₂ = k₂ * a := fun a ha =>
    (GlobalTheory.IdemSupport.commute_of_suppF V (by rw [mul_sub, mul_one, hff, sub_self]) ha s₂).eq
  funext x
  rw [hc k₁ s₁, ← mul_assoc, hT k₁ m₁', c₁, one_mul]
  show _ * ∑ γ ∈ Rp, _ = ∑ γ ∈ Rp, _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  beta_reduce
  rw [← mul_assoc (x * γ), hΦ k₁ m₁', c₁, one_mul, mul_assoc x, mul_assoc x, hc γ (hR γ hγ)]

theorem hecke_keeps_and_commutes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → ∀ (i : Fin D.R.m) (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D (Wc D i))), GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.IsHecke R i Q d Rp → (∀ σ, ∀ U ∈ R.Wall i σ, heckeOn (R.MW i σ) Rp U ∈ R.Wall i σ) ∧ ∀ (g0 : G0 R.Pg D.R.r) (Φ : GA D (Wc D i) → ℂ), Lev.HasType (Wc D i) (R.βW i) (R.datWp i R.triv) Φ → actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (heckeLin (Wc D i) Rp Φ) = heckeLin (Wc D i) Rp (actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 Φ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL _ i Q d Rp h
  obtain ⟨c, hB⟩ := hL.βW i
  have hN : (((1 ^ c : ℕ) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top
  have hS : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.finS R) Q := by
    obtain ⟨_, _, _, _, hS, -⟩ := h
    exact hS
  have hP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q := by
    classical
    rintro PP (hP | hP)
    · exact sep_of_offS hS (by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.finS
        exact Finset.mem_image.2 ⟨PP, hP, rfl⟩)
    · exact absurd hP (Finset.notMem_empty _)
  refine ⟨fun σ U hU => ?_, fun g0 Φ hΦ => actL_heckeLin hB hN hP h g0 hΦ⟩
  unfold RealDat.Wall at hU ⊢
  rw [GlobalTheory.MultMem.mem_mult_iff] at hU ⊢
  refine GlobalTheory.SphericalOps.isMultMap_heckeOn hU (fun k hk => ?_) fun v => hasType_heckeLin hB hN hP h (hU.lev v)
  obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := h
  exact (hc.1 k hk).1

end GlobalTheory.HeckeOffLevel
