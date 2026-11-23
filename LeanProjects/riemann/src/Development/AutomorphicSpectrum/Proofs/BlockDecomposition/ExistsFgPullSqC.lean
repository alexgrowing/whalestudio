import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlmostFinitelyGeneratedSerreClassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverLatticeBaseStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatticeFinite

universe u v u' v'

section General

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem pull_sqC_comb (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} {c c₁ c₂ e e' : R'}
    (hc : c = e * c₁ + e' * c₂) (ha : m.LeC c a a') (hb : m.LeC c b b') (ha₁ : m.LeC c₁ a a') (hb₁ : m.LeC c₁ b b')
    (ha₂ : m.LeC c₂ a a') (hb₂ : m.LeC c₂ b b') (j : ℕ) (x : CH.H (sq a b) j) :
    (m.sqC c ha hb).pull j x =
      e • (m.sqC c₁ ha₁ hb₁).pull j x + e' • (m.sqC c₂ ha₂ hb₂).pull j x := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = e • Submodule.Quotient.mk _ + e' • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  refine congrArg _ (Subtype.ext (funext fun s => ?_))
  change (m.sqC c ha hb).τ _ (f (s ⋙ m.G)) =
    e • (m.sqC c₁ ha₁ hb₁).τ _ (f (s ⋙ m.G)) + e' • (m.sqC c₂ ha₂ hb₂).τ _ (f (s ⋙ m.G))
  generalize f (s ⋙ m.G) = w
  obtain ⟨z, hz⟩ := w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine Subtype.ext ?_
  have key : algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c * m.ρ (s.obj (Fin.last j)) y =
      e • (algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c₁ * m.ρ (s.obj (Fin.last j)) y) +
      e' • (algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c₂ * m.ρ (s.obj (Fin.last j)) y) := by
    rw [hc, map_add, map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  exact congrArg (Ideal.Quotient.mk (b'.S (s.obj (Fin.last j)))) key

theorem exists_fg_pull_sqC (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (P : Ideal R') (hP : P.FG)
    (h₁ : ∀ c ∈ P, m.LeC c a a') (h₂ : ∀ c ∈ P, m.LeC c b b') (j : ℕ) (hfin : Module.Finite R (CH.H (sq a b) j)) :
    ∃ N : Submodule R' (CH.H (sq a' b') j), N.FG ∧ ∀ (c : R') (ha : m.LeC c a a') (hb : m.LeC c b b'), c ∈ P →
      ∀ x, (m.sqC c ha hb).pull j x ∈ N := by
  classical
  obtain ⟨G, rfl⟩ := hP
  obtain ⟨X, hX⟩ := (Module.Finite.fg_top : (⊤ : Submodule R (CH.H (sq a b) j)).FG)
  let φ : G × X → CH.H (sq a' b') j := fun p =>
    (m.sqC p.1.1 (h₁ _ (Ideal.subset_span p.1.2)) (h₂ _ (Ideal.subset_span p.1.2))).pull j p.2.1
  refine ⟨Submodule.span R' (Set.range φ), Submodule.fg_span (Set.finite_range φ), ?_⟩
  have hgen : ∀ (g : R') (hg : g ∈ G) (ha : m.LeC g a a') (hb : m.LeC g b b') (x : CH.H (sq a b) j),
      (m.sqC g ha hb).pull j x ∈ Submodule.span R' (Set.range φ) := by
    intro g hg ha hb x
    have hx : x ∈ Submodule.span R (X : Set (CH.H (sq a b) j)) := hX ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨(⟨g, hg⟩, ⟨x, hx⟩), rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  intro c ha hb hc x
  refine Submodule.span_induction
    (p := fun c _ => ∀ (ha : m.LeC c a a') (hb : m.LeC c b b'), (m.sqC c ha hb).pull j x ∈ Submodule.span R' (Set.range φ))
    ?_ ?_ ?_ ?_ hc ha hb
  · intro g hg ha hb
    exact hgen g hg ha hb x
  · intro ha hb
    rw [pull_sqC_comb m (c₁ := 0) (c₂ := 0) (e := 0) (e' := 0) (by simp) ha hb ha hb ha hb j x]
    simp
  · intro c₁ c₂ m₁ m₂ i₁ i₂ ha hb
    rw [pull_sqC_comb m (c₁ := c₁) (c₂ := c₂) (e := 1) (e' := 1) (by simp) ha hb (h₁ _ m₁) (h₂ _ m₁) (h₁ _ m₂) (h₂ _ m₂) j x]
    simpa using add_mem (i₁ (h₁ _ m₁) (h₂ _ m₁)) (i₂ (h₁ _ m₂) (h₂ _ m₂))
  · intro e c₁ m₁ i₁ ha hb
    rw [pull_sqC_comb m (c₁ := c₁) (c₂ := c₁) (e := e) (e' := 0) (by simp) ha hb (h₁ _ m₁) (h₂ _ m₁) (h₁ _ m₁) (h₂ _ m₁) j x]
    simpa using Submodule.smul_mem _ e (i₁ (h₁ _ m₁) (h₂ _ m₁))

end General

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') :
    pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, h₁, h₂, h₃⟩ => ⟨l, h₁, h.trans h₂, h₃⟩

theorem tfBase_mono {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} {l m s : ℕ} (h : TFBase δ l m)
    (hms : m ≤ s) : TFBase δ l s :=
  ⟨le_bot_iff.1 (h.nil ▸ dividedPowerFiltration_anti δ hms), h.tf, h.dv⟩

theorem afgA_of_bcOn_finO : BcOn False → FinO → AfgA := by
  intro hB hF O A _ _ _ _ _ I γ l s m hl hO hL hms X q _ U 𝒱 h𝒱 r r' hr hr' j
  obtain ⟨S⟩ := GlobalTheory.T.graded_splitting_over_lattice_base γ l m hl hL
  have hA : TFBase γ l s := tfBase_mono hL.tf hms
  have hC : ∀ (i : Fin m) (t : ℤ) (c : A), c ∈ pdP γ i →
      (smO γ q l s 𝒱).LeC c (sFil _ (t - i)) (sFil _ t) :=
    fun i t c hc => GlobalTheory.T.scalar_multiplication_shifts_filtration γ q l s 𝒱 i c hc t
  have ha : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
    fun i n => hC i r _ (S.mem i n)
  have hb : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r' - i)) (sFil _ r') :=
    fun i n => hC i r' _ (S.mem i n)
  obtain ⟨g, hg⟩ := hB γ l s m hO hA S q 𝒱 (Or.inr ⟨not_false, ⟨U⟩, h𝒱⟩) r r' hr hr' ha hb j
  have hN : ∀ i : Fin m, ∃ N : Submodule A (HQ (TS γ q l s 𝒱) r r' j), N.FG ∧
      ∀ n x, ((smO γ q l s 𝒱).sqC (S.ν i n) (ha i n) (hb i n)).pull j x ∈ N := by
    intro i
    have hi : (0 : ℤ) ≤ (i : ℕ) := Int.natCast_nonneg _
    obtain ⟨N, h₁, h₂⟩ := exists_fg_pull_sqC (smO γ q l s 𝒱) (pdP γ i) (hL.fg i) (fun c hc => hC i r c hc)
      (fun c hc => hC i r' c hc) j (hF l s hO q U 𝒱 h𝒱 (r - i) (r' - i) (by omega) (by omega) j)
    exact ⟨N, h₁, fun n x => h₂ _ _ _ (S.mem i n) x⟩
  choose N hNfg hNmem using hN
  refine ⟨0, ⨆ i, N i, Submodule.fg_iSup _ hNfg, fun y => ?_⟩
  rw [pow_zero, one_smul]
  have hsingle : ∀ (i : Fin m) (t : S.N i ⊗[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j),
      g (Pi.single i t) ∈ ⨆ i, N i := by
    intro i t
    induction t using TensorProduct.induction_on with
    | zero => rw [Pi.single_zero, map_zero]; exact zero_mem _
    | tmul n x => rw [hg]; exact Submodule.mem_iSup_of_mem i (hNmem i n x)
    | add t t' ht ht' => rw [Pi.single_add, map_add]; exact add_mem ht ht'
  have hy : y = ∑ i, g (Pi.single i (g.symm y i)) := by
    rw [← map_sum, Finset.univ_sum_single, g.apply_symm_apply]
  rw [hy]
  exact sum_mem fun i _ => hsingle i _

end GlobalTheory.CompanionTheory.LatticeFinite
