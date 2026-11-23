import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIsoDef
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatRetract
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
import Lemmata.DualWeylPullback.DualWeylPull

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem nuOf_add {m : ℕ} (lam mu : Fin (m + 1) → ℤ) (h1 : Antitone lam) (h2 : Antitone mu) :
    nuOf (lam + mu) = nuOf lam + nuOf mu := by
  funext t
  have a1 : lam (Fin.last m) ≤ lam t := h1 (Fin.le_last t)
  have a2 : mu (Fin.last m) ≤ mu t := h2 (Fin.le_last t)
  simp only [nuOf, Pi.add_apply]
  omega

section One

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem smulO_eq {σ : Type} (a : O) (F : MvPolynomial σ K) : a • F = algebraMap O K a • F :=
  (algebraMap_smul K a F).symm

theorem exists_pow_mem (w : O) (hw : Irreducible w) (m : ℕ) (mu : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (hF : F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu)) : ∃ n : ℕ, w ^ n • F ∈ H0 O m mu (colSpan O g) := by
  first | exact Bl.DualWeylPullback.goal1 .. | (apply Bl.DualWeylPullback.goal1 <;> assumption) | (intros; apply Bl.DualWeylPullback.goal1 <;> assumption) | (apply @Bl.DualWeylPullback.goal1 <;> assumption) | (intros; apply @Bl.DualWeylPullback.goal1 <;> assumption) | (apply @Bl.DualWeylPullback.goal1 <;> first | assumption | infer_instance) | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg F hF | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg F | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› | exact @Bl.DualWeylPullback.goal1 O K | exact @Bl.DualWeylPullback.goal1 O

theorem iso_one (hCD : CartanDomain) (w : O) (hw : Irreducible w) (m : ℕ) (mu ze : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (hze : Antitone ze) (Λ : Submodule O (Fin (m + 1) → K)) (hΛ : IsLattice O Λ)
    (z : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hz : z ∈ H0 O m ze Λ)
    (hprim : ¬ ∃ z' ∈ H0 O m ze Λ, z = w • z') (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (hF : F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu)) (hzF : z * F ∈ H0 O m (mu + ze) Λ) : F ∈ H0 O m mu Λ := by
  have hwK : algebraMap O K w ≠ 0 := by
    intro h
    exact hw.ne_zero ((IsFractionRing.injective O K) (by rw [h, map_zero]))
  have key : ∀ n : ℕ, ∀ F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, w ^ n • F ∈ H0 O m mu Λ →
      z * F ∈ H0 O m (mu + ze) Λ → F ∈ H0 O m mu Λ := by
    intro n
    induction n with
    | zero => intro F h _; simpa using h
    | succ n ih =>
      intro F h1 h2
      apply ih F _ h2
      have hX : (w ^ (n + 1) • F) * z = w • (w ^ n • (z * F)) := by
        rw [smul_mul_assoc, pow_succ', mul_smul, mul_comm F z]
      rcases hCD O K w hw m mu ze Λ hΛ hmu hze _ h1 z hz ⟨_, Submodule.smul_mem _ _ h2, hX⟩ with ⟨F', hF', he⟩ | h
      · have : w ^ n • F = F' := by
          rw [pow_succ', mul_smul, smulO_eq w, smulO_eq w F'] at he
          exact smul_right_injective _ hwK he
        rw [this]; exact hF'
      · exact absurd h hprim
  obtain ⟨g, hg, rfl⟩ := hΛ
  obtain ⟨n, hn⟩ := exists_pow_mem w hw m mu hmu g hg F hF
  exact key n F hn hzF

theorem retract_one (hCD : CartanDomain) (hCO : CartanOnto) (w : O) (hw : Irreducible w) (m : ℕ)
    (mu ze : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (hze : Antitone ze) (Λ : Submodule O (Fin (m + 1) → K)) (hΛ : IsLattice O Λ)
    (z : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hz : z ∈ H0 O m ze Λ)
    (hprim : ¬ ∃ z' ∈ H0 O m ze Λ, z = w • z') :
    ∃ ρ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K,
      (∀ G ∈ H0 O m (mu + ze) Λ, ρ G ∈ H0 O m mu Λ) ∧
      ∀ F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu), ρ (z * F) = F := by
  classical
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hΛ' := hΛ
  obtain ⟨g, hg, rfl⟩ := hΛ
  have hsum : Antitone (mu + ze) := hmu.add hze
  obtain ⟨B, -, hB1, hB3, hB2⟩ := la_basis hinj m mu g hg
  obtain ⟨B', -, hB1', hB3', hB2'⟩ := la_basis hinj m (mu + ze) g hg
  rw [← H0_eq_twisted_nabla (la_indep hinj) m mu hmu g hg] at hB1
  rw [← H0_eq_twisted_nabla (la_indep hinj) m (mu + ze) hsum g hg] at hB1'
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf mu)) := (sSIdxFinite _ _ _).fintype
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (mu + ze))) := (sSIdxFinite _ _ _).fintype
  let b : Module.Basis _ K (dualWeyl K (m + 1) (m + 1) (nuOf mu)) :=
    (Module.Basis.span hB3).map (LinearEquiv.ofEq _ _ hB2)
  let b' : Module.Basis _ K (dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze))) :=
    (Module.Basis.span hB3').map (LinearEquiv.ofEq _ _ hB2')
  have hb : ∀ i, (b i : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = B i := by
    intro i
    simp [b, Module.Basis.span_apply]
  have hb' : ∀ i, (b' i : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = B' i := by
    intro i
    simp [b', Module.Basis.span_apply]
  have hmem : ∀ F : dualWeyl K (m + 1) (m + 1) (nuOf mu),
      F ∈ Submodule.span O (Set.range b) ↔ (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ H0 O m mu (colSpan O g) := by
    intro F
    have e : (Submodule.span O (Set.range b)).map ((dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype.restrictScalars O) =
        H0 O m mu (colSpan O g) := by
      rw [Submodule.map_span, ← Set.range_comp, ← hB1]
      congr 2
      funext i
      exact hb i
    rw [← e]
    constructor
    · intro h; exact ⟨F, h, rfl⟩
    · rintro ⟨F', h, he⟩
      have : F' = F := Subtype.ext he
      rwa [← this]
  have hmem' : ∀ F : dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)),
      F ∈ Submodule.span O (Set.range b') ↔
        (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ H0 O m (mu + ze) (colSpan O g) := by
    intro F
    have e : (Submodule.span O (Set.range b')).map
        ((dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze))).subtype.restrictScalars O) = H0 O m (mu + ze) (colSpan O g) := by
      rw [Submodule.map_span, ← Set.range_comp, ← hB1']
      congr 2
      funext i
      exact hb' i
    rw [← e]
    constructor
    · intro h; exact ⟨F, h, rfl⟩
    · rintro ⟨F', h, he⟩
      have : F' = F := Subtype.ext he
      rwa [← this]
  have hzK : z ∈ dualWeyl K (m + 1) (m + 1) (nuOf ze) := la_nablaLTw_le m ze g hg z (H0_le_twisted_nabla m ze hze g hg hz)
  let io : dualWeyl K (m + 1) (m + 1) (nuOf mu) →ₗ[K] dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)) :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft K z) ∘ₗ (dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype) (by
      intro F
      rw [nuOf_add mu ze hmu hze, add_comm (nuOf mu) (nuOf ze)]
      exact dualWeyl_mul K _ _ _ _ hzK F.2)
  have hio : ∀ F, (io F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = z * F := fun F => rfl
  obtain ⟨ret, hr1, hr2⟩ := KP.latRetract b b' io (by
    intro F
    rw [hmem, hmem', hio]
    constructor
    · intro h
      exact iso_one hCD w hw m mu ze hmu hze _ hΛ' z hz hprim F F.2 h
    · intro h
      rw [hCO O K m mu ze _ hΛ' hmu hze]
      exact Submodule.subset_span ⟨F, h, z, hz, mul_comm _ _⟩)
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_extend ((dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype ∘ₗ ret)
  have hρ' : ∀ G : dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)),
      ρ (G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = (ret G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
    fun G => LinearMap.congr_fun hρ G
  refine ⟨ρ, ?_, ?_⟩
  · intro G hG
    have hGK : G ∈ dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)) :=
      la_nablaLTw_le m _ g hg G (H0_le_twisted_nabla m _ hsum g hg hG)
    rw [hρ' ⟨G, hGK⟩, ← hmem]
    exact hr2 _ ((hmem' ⟨G, hGK⟩).2 hG)
  · intro F hF
    have := hρ' (io ⟨F, hF⟩)
    rw [hio] at this
    rw [this, hr1]

end One

theorem iso_ten {O K : Type} [CommRing O] [Field K] [Algebra O K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}
    (V : S → Submodule K (MvPolynomial (Fin k × Fin n) K)) (N Np : S → Submodule O (MvPolynomial (Fin k × Fin n) K))
    (z : S → MvPolynomial (Fin k × Fin n) K)
    (ρ : S → MvPolynomial (Fin k × Fin n) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
    (h1 : ∀ s, ∀ G ∈ Np s, ρ s G ∈ N s) (h2 : ∀ s, ∀ F ∈ V s, ρ s (z s * F) = F)
    (F : MvPolynomial (S × (Fin k × Fin n)) K) (hF : F ∈ tensorLat K K V)
    (hzF : (∏ s, blockEmb K s (z s)) * F ∈ tensorLat O K Np) : F ∈ tensorLat O K N := by
  obtain ⟨T, hT⟩ := KP.tensorMap (K := K) (S := S) (α := Fin k × Fin n)
    (fun s => (blockEmb K (k := k) (n := n) s).toLinearMap ∘ₗ ρ s)
  have hT' : ∀ P : S → MvPolynomial (Fin k × Fin n) K,
      T (∏ s, blockEmb K s (P s)) = ∏ s, blockEmb K s (ρ s (P s)) := fun P => hT P
  have hA : ∀ G ∈ tensorLat O K Np, T G ∈ tensorLat O K N := by
    intro G hG
    unfold tensorLat at hG
    refine Submodule.span_induction (p := fun G _ => T G ∈ tensorLat O K N) ?_ ?_ ?_ ?_ hG
    · rintro _ ⟨P, hP, rfl⟩
      rw [hT']
      exact Submodule.subset_span ⟨fun s => ρ s (P s), fun s => h1 s _ (hP s), rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [← algebraMap_smul K c x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx
  have hB : ∀ F ∈ tensorLat K K V, T ((∏ s, blockEmb K s (z s)) * F) = F := by
    intro F hF
    unfold tensorLat at hF
    refine Submodule.span_induction (p := fun F _ => T ((∏ s, blockEmb K s (z s)) * F) = F) ?_ ?_ ?_ ?_ hF
    · rintro _ ⟨P, hP, rfl⟩
      rw [← Finset.prod_mul_distrib]
      have : (∏ s, blockEmb K s (z s) * blockEmb K s (P s)) = ∏ s, blockEmb K s (z s * P s) :=
        Finset.prod_congr rfl fun s _ => (map_mul _ _ _).symm
      rw [this, hT']
      exact Finset.prod_congr rfl fun s _ => by rw [h2 s _ (hP s)]
    · rw [mul_zero, map_zero]
    · intro x y _ _ hx hy
      rw [mul_add, map_add, hx, hy]
    · intro c x _ hx
      rw [mul_smul_comm, map_smul, hx]
  rw [← hB F hF]
  exact hA _ hzF

theorem cloudIso (hCD : CartanDomain) (hCO : CartanOnto) : CloudIsoP := by
  classical
  intro O K _ _ _ _ _ _ w hw n' m mu ze hmu hze M hM z hz hprim F hF hzF
  choose ρ hρ1 hρ2 using fun s =>
    retract_one hCD hCO w hw m (mu s) (ze s) (hmu s) (hze s) (M s) (hM s) (z s) (hz s) (hprim s)
  exact iso_ten (fun s => dualWeyl K (m + 1) (m + 1) (nuOf (mu s))) (fun s => H0 O m (mu s) (M s))
    (fun s => H0 O m (mu s + ze s) (M s)) z ρ hρ1 hρ2 F hF hzF

end Formalism.MainNotions.flipOneThree.Pf

end
