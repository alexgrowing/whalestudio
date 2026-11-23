import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusTwistDivisorRecursion
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechVanishingFrobeniusDescentStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SerreVanishingSncAtlasStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.TopLogFormsCanonicalGeneratorStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLatticeCohomologyVanish
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LatticeModelUniqueInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelOfPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFormsEqBotOfLtCard
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharPVanish

theorem gen_mem_inter {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens)
    (h : ∀ i, genericPoint X ∈ U i) (s : Finset ι) : genericPoint X ∈ inter U s := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.inf_insert]; exact ⟨h i, ih⟩

theorem cechZero_of_forall_eq_zero {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (N : Finset ι → AddSubgroup E) (h : ∀ s, ∀ x ∈ N s, x = 0) (b : ℕ) : DI.CechZero N b := by
  intro c hc _
  refine ⟨0, ⟨rfl, fun s => zero_mem _, fun _ _ => rfl⟩, ?_⟩
  funext t
  simp only [DI.delta, Pi.zero_apply, smul_zero, Finset.sum_const_zero]
  exact (h t _ (hc.2.1 t)).symm

theorem cechFam_eq_zero {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) {a : ℕ} (ha : n < a) (s : Finset ι) :
    ∀ x ∈ cechFam 𝒜 G a s, x = 0 := by
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ 𝒜.U i := by
    have : genericPoint X ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
    simpa [Opens.mem_iSup] using this
  have hx' : x ∈ logAt (suppAll E) G a (genericPoint X) :=
    AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hx (genericPoint X)) (gen_mem_inter _ 𝒜.gen s)
  have hc := ((𝒜.chart i).chart _ hi).coord
  rw [logAt, spanForms_eq_bot_of_lt_card _ n (𝒜.x i) _ _ a hc ha] at hx'
  exact (AddSubgroup.mem_bot).1 hx'

theorem isSeparated_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : X.IsSeparated := by
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver h
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

theorem twist_split {X : Scheme.{0}} [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X)
    (M K H : CartierDiv X) (r : ℕ) (b : C → ℕ) (hr : 0 < r) (key : r • (M - K) = ∑ c, b c • E c + H)
    (N : ℕ) :
    N • (M - K) - ∑ c, (N * b c / r) • E c - ∑ c, E c =
      (N / r) • H + ((N % r) • (M - K) - ∑ c, ((N % r) * b c / r) • E c - ∑ c, E c) := by
  conv_lhs => rw [← Nat.div_add_mod N r]
  generalize N / r = Q
  generalize N % r = ρ
  have hfl : ∀ c, (r * Q + ρ) * b c / r = ρ * b c / r + Q * b c := by
    intro c
    rw [show (r * Q + ρ) * b c = ρ * b c + r * (Q * b c) by ring, Nat.add_mul_div_left _ _ hr]
  simp only [hfl, add_smul, Finset.sum_add_distrib]
  rw [show r * Q = Q * r from mul_comm _ _, mul_smul, key]
  simp only [mul_smul, ← Finset.smul_sum, smul_add]
  abel

theorem subsingleton_coh_of_decomp : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f], IsProjOver f → d < p →
    ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} [Fintype ι] [LinearOrder ι]
      (𝒜 : SncAtlas E d ι), Decomp p 𝒜 → ∀ (M H : CartierDiv X) (r : ℕ) (b : C → ℕ),
      IsAmpleLB (toLB H) → 0 < r → (∀ c, b c < r) → r • M = r • canonical f d + ∑ c, b c • E c + H →
      ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (toLB M)) q) := by
  intro p _ X _ f d _ hproj _ C _ E ι _ _ 𝒜 hdec M H r b hH hr hb hM q hq
  haveI : CharP X.functionField p := charP_of_injective_ringHom (Cartier.constFn f).injective p
  haveI : X.IsSeparated := isSeparated_of_isProjOver hproj
  let G : ℕ → CartierDiv X := fun e =>
    p ^ e • (M - canonical f d) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c
  let R : Fin r → CartierDiv X := fun j =>
    (j : ℕ) • (M - canonical f d) - ∑ c, ((j : ℕ) * b c / r) • E c - ∑ c, E c
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.T.serre_vanishing_snc_atlas (ZMod p) X f hproj E 𝒜 H r R hH
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpow : q₀ * r ≤ p ^ (q₀ * r) := by
    have := Nat.lt_pow_self hp1 (n := q₀ * r)
    omega
  have hQ : q₀ ≤ p ^ (q₀ * r) / r := (Nat.le_div_iff_mul_le hr).2 hpow
  have key : r • (M - canonical f d) = ∑ c, b c • E c + H := by
    rw [smul_sub, hM]; abel
  have hG : G (q₀ * r) = (p ^ (q₀ * r) / r) • H + R ⟨p ^ (q₀ * r) % r, Nat.mod_lt _ hr⟩ :=
    twist_split E M (canonical f d) H r b hr key _
  have hrec : ∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c :=
    GlobalTheory.T.frobenius_twist_divisor_recursion X p E M (canonical f d) r b (by omega) hr
  have hvan : ∀ a b' : ℕ, d < a + b' → DI.CechZero (cechFam 𝒜 (G (q₀ * r)) a) b' := by
    intro a b' hab
    rcases Nat.eq_zero_or_pos b' with rfl | hb'
    · exact cechZero_of_forall_eq_zero _ (cechFam_eq_zero 𝒜 _ (by omega)) 0
    · rw [hG]; exact hq₀ _ hQ _ a b' hb'
  have h0 := GlobalTheory.T.cech_vanishing_frobenius_descent p X E 𝒜 G hdec hrec (q₀ * r) hvan d q (by omega)
  have hG0 : G 0 = M - canonical f d - ∑ c, E c := by
    simp only [G, pow_zero, one_smul, one_mul, Nat.div_eq_of_lt (hb _), zero_smul,
      Finset.sum_const_zero, sub_zero]
  obtain ⟨ω₀, hω₀, htop⟩ := GlobalTheory.T.top_log_forms_canonical_generator p X f d E 𝒜
  let φ : X.functionField →ₗ[X.functionField] abelian₂ X.functionField :=
    LinearMap.toSpanSingleton _ _ ω₀
  have hφ : Function.Injective φ := fun c c' h => smul_left_injective _ hω₀ h
  have hD : canonical f d + ∑ c, E c + G 0 = M := by rw [hG0]; abel
  have hlat : logAt (suppAll E) (G 0) d =
      fun y => ((M.secOn {y}).toAddSubgroup).map φ.toAddMonoidHom := by
    funext y; ext η
    rw [htop, AddSubgroup.mem_map, hD]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, CartierDiv.mem_secOn.2 (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hc), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, CartierDiv.mem_secOn.1 hc y rfl, rfl⟩
  obtain ⟨L0⟩ := nonempty_latModel_of_presents X M (toLB M) _ (presents_toLB M)
  obtain ⟨L1⟩ := (GlobalTheory.T.lattice_model_unique_injective X _ (LB.toMod (toLB M)) (LB.toMod (toLB M)) φ hφ L0).1
  haveI := LB.isQuasicoherent_toMod (isLB_toLB M)
  refine (GlobalTheory.T.cech_lattice_cohomology_vanish X _ (LB.toMod (toLB M)) 𝒜.U L1 𝒜.affine 𝒜.gen 𝒜.cover q hq).1 ?_
  have hfam : cechFam 𝒜 (G 0) d = fun s =>
      latSec (fun y => ((M.secOn {y}).toAddSubgroup).map φ.toAddMonoidHom) (inter 𝒜.U s) := by
    funext s; simp only [cechFam, logSec]; rw [hlat]
  rwa [hfam] at h0

end GlobalTheory.CharPVanish
