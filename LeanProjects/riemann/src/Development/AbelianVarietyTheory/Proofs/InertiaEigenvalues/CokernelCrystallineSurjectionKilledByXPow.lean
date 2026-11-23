import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneNotMemFilOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValOfPowAssociated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XXPowMemOfQQPowMulMemMapPhi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CokerKill

section Algebra

variable {A D : Type} [CommRing A] [AddCommGroup D] [Module A D]

theorem indep_of_commensurable {κ : Type} [Fintype κ] (q : A) (hq : ∀ a, a * q = 0 → a = 0)
    (b c : κ → D) (hb : LinearIndependent A b)
    (h1 : ∀ k, ∃ m : ℕ, q ^ m • c k ∈ Submodule.span A (Set.range b))
    (h2 : ∀ k, ∃ m : ℕ, q ^ m • b k ∈ Submodule.span A (Set.range c)) : LinearIndependent A c := by
  classical
  have unif : ∀ b c : κ → D, (∀ k, ∃ m : ℕ, q ^ m • c k ∈ Submodule.span A (Set.range b)) →
      ∃ (m : ℕ) (M : Matrix κ κ A), ∀ k, q ^ m • c k = ∑ j, M k j • b j := by
    intro b c h
    choose m hm using h
    have : ∀ k, ∃ u : κ → A, ∑ j, u j • b j = q ^ (Finset.univ.sup m) • c k := fun k => by
      rw [← Submodule.mem_span_range_iff_exists_fun]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) (Finset.mem_univ k))
      rw [hd, add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ (hm k)
    choose u hu using this
    exact ⟨_, Matrix.of u, fun k => (hu k).symm⟩
  obtain ⟨m, M, hM⟩ := unif b c h1
  obtain ⟨m', M', hM'⟩ := unif c b h2
  have hpow : ∀ (N : ℕ) a, a * q ^ N = 0 → a = 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => intro a ha; exact ih a (hq _ (by rw [mul_assoc, ← pow_succ]; exact ha))
  rw [Fintype.linearIndependent_iff] at hb ⊢
  have hMM : M' * M = (q ^ (m + m')) • (1 : Matrix κ κ A) := by
    ext k i
    have e : ∑ i, ((M' * M) k i - ((q ^ (m + m')) • (1 : Matrix κ κ A)) k i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [sub_eq_zero, pow_add, mul_smul, hM', Finset.smul_sum]
      simp only [Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm, hM, Finset.smul_sum]
      simp only [mul_smul]
    exact sub_eq_zero.1 (hb _ e i)
  intro a ha k
  have h3 : Matrix.vecMul a M = 0 := by
    funext i
    refine hb (Matrix.vecMul a M) ?_ i
    have : ∑ j, a j • (q ^ m • c j) = 0 := by
      simp only [smul_comm (a _) (q ^ m)]
      rw [← Finset.smul_sum, ha, smul_zero]
    rw [← this]
    simp only [hM, Matrix.vecMul, dotProduct, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have h4 : M.det • a = 0 := by
    have := congrArg (fun x => Matrix.vecMul x M.adjugate) h3
    simpa [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul] using this
  have h5 := congrArg Matrix.det hMM
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, ← pow_mul] at h5
  refine hpow ((m + m') * Fintype.card κ) _ ?_
  have h6 : M.det * a k = 0 := congrFun h4 k
  rw [← h5]
  linear_combination M'.det * h6

variable (φ : A →+* A) (Φ : D →+ D) (hΦ : ∀ a x, Φ (a • x) = φ a • Φ x) {ι : Type} [Fintype ι]
  (t : ι → A)
include hΦ

theorem decomp_unique {κ : Type} [Fintype κ] (ht : ∀ z : ι → A, ∑ j, t j * φ (z j) = 0 → z = 0)
    (b : κ → D) (hb : LinearIndependent A fun k => Φ (b k)) (u : ι → D)
    (hu : ∀ j, u j ∈ Submodule.span A (Set.range b)) (h : ∑ j, t j • Φ (u j) = 0) (j : ι) :
    u j = 0 := by
  choose z hz using fun j => (Submodule.mem_span_range_iff_exists_fun A).1 (hu j)
  rw [Fintype.linearIndependent_iff] at hb
  have h1 : ∀ k, ∑ j, t j * φ (z j k) = 0 := hb (fun k => ∑ j, t j * φ (z j k)) (by
    rw [← h]
    simp only [← hz, map_sum, hΦ, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm)
  rw [← hz]
  exact Finset.sum_eq_zero fun k _ => by
    rw [show z j k = 0 from congrFun (ht (fun j => z j k) (h1 k)) j, zero_smul]

theorem decomp_exists (ht : ∀ a : A, ∃ z : ι → A, a = ∑ j, t j * φ (z j)) (S : Submodule A D)
    (x : D) (hx : x ∈ Submodule.span A (Φ '' (S : Set D))) :
    ∃ u : ι → D, (∀ j, u j ∈ S) ∧ x = ∑ j, t j • Φ (u j) := by
  have key : ∀ a : A, ∃ u : ι → D, (∀ j, u j ∈ S) ∧ a • x = ∑ j, t j • Φ (u j) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      intro a
      obtain ⟨z, rfl⟩ := ht a
      exact ⟨fun j => z j • y, fun j => S.smul_mem _ hy, by simp [hΦ, Finset.sum_smul, mul_smul]⟩
    | zero => exact fun a => ⟨0, fun _ => S.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      intro a
      obtain ⟨u, hu, e⟩ := hx a
      obtain ⟨u', hu', e'⟩ := hy a
      exact ⟨u + u', fun j => S.add_mem (hu j) (hu' j), by
        simp [e, e', Finset.sum_add_distrib]⟩
    | smul c x _ hx => intro a; rw [smul_smul]; exact hx _
  simpa using key 1

end Algebra

section Kernel

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem exists_kernel [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]
    {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (hπ : π.Onto) :
    ∃ (T₀ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L), IsSESLat (Qp := Qp) ι π := by
  haveI := T₁.L.free
  haveI : Module.Finite O ↥T₁.L.T := Module.Finite.iff_fg.2 T₁.L.fg
  let V' : Submodule LL T₁.V := LinearMap.ker π.f
  have hV' : ∀ g, V' ≤ V'.comap (T₁.ρ g) := fun g x hx => by
    change π.f (T₁.ρ g x) = 0
    rw [π.equiv, show π.f x = 0 from hx, map_zero]
  let ρ' : Representation LL G V' := T₁.ρ.subrepresentation V' hV'
  let S₂ : Submodule O V' := T₁.L.T.comap (V'.subtype.restrictScalars O)
  let e : S₂ →ₗ[O] T₁.L.T :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : Function.Injective e := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : T₁.L.T => (z : T₁.V)) h))
  haveI : Module.Finite O S₂ := Module.Finite.of_injective e he
  haveI : Module.IsTorsionFree O S₂ := he.moduleIsTorsionFree e e.map_smul
  have hden : ∀ x : T₁.V, ∃ c : O, c ≠ 0 ∧ c • x ∈ T₁.L.T := by
    intro x
    have hx : x ∈ Submodule.span LL (T₁.L.T : Set T₁.V) := by rw [T₁.L.span]; trivial
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL _ x hx
    rw [Submodule.span_eq] at hc
    exact ⟨c, nonZeroDivisors.ne_zero c.2, hc⟩
  letI : TopologicalSpace V' := moduleTopology LL V'
  haveI : IsModuleTopology LL V' := ⟨rfl⟩
  haveI : ContinuousAdd V' := IsModuleTopology.toContinuousAdd LL V'
  haveI : ContinuousSMul LL V' := IsModuleTopology.toContinuousSMul LL V'
  haveI : ContinuousSMul LL T₁.V := IsModuleTopology.toContinuousSMul LL T₁.V
  obtain ⟨r, hr⟩ := V'.subtype.exists_leftInverse_of_injective V'.ker_subtype
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  let T' : LocLat G Qp LL O :=
    { V := V'
      ρ := ρ'
      cont := fun x => by
        have : (fun g => ρ' g x) = fun g => r (T₁.ρ g x) :=
          funext fun g => (LinearMap.congr_fun hr (ρ' g x)).symm
        rw [this]
        exact hrc.comp (T₁.cont x)
      L :=
        { T := S₂
          stable := fun g x hx => T₁.L.stable g _ hx
          fg := Module.Finite.iff_fg.1 inferInstance
          free := inferInstance
          span := by
            rw [eq_top_iff]
            intro x _
            obtain ⟨c, hc0, hc⟩ := hden x
            have h1 : c • x ∈ Submodule.span LL (S₂ : Set V') := Submodule.subset_span hc
            have h2 : algebraMap O LL c ≠ 0 := by simpa using hc0
            rw [← algebraMap_smul LL] at h1
            exact (Submodule.smul_mem_iff _ h2).1 h1 } }
  refine ⟨T', ⟨V'.subtype, fun _ _ => rfl, IsModuleTopology.continuous_of_linearMap V'.subtype,
    fun x hx => hx⟩, V'.injective_subtype, ?_, hπ, fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩, fun y hy => hy⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← T₂.L.span, Submodule.span_le]
    intro y hy
    obtain ⟨x, -, rfl⟩ := hπ y hy
    exact ⟨x, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

end Kernel

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L)

def ann (i : ZMod n) : Ideal (PowerSeries O) where
  carrier := {g | ∀ y ∈ W.N T₂, (Pi.single i g : LetA O n) • y ∈ (W.N T₁).map (mapA W π)}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {a b} ha hb y hy => by
    rw [Pi.single_add, add_smul]; exact add_mem (ha y hy) (hb y hy)
  smul_mem' := fun c a ha y hy => by
    have : (Pi.single i (c • a) : LetA O n) = (fun _ => c) * Pi.single i a := by
      funext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [this, mul_smul]
    exact Submodule.smul_mem _ _ (ha y hy)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a, W.φD_smul, W.φE_ext, algebraMap_smul]; rfl

theorem φA_single (i : ZMod n) (g : PowerSeries O) :
    W.φA (Pi.single (i - 1) g) = Pi.single i (W.φ₀ g) := by
  funext j
  change W.φ₀ ((Pi.single (i - 1) g : LetA O n) (j - 1)) = _
  by_cases h : j = i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun e => h (sub_left_injective e)), map_zero]

omit [CommRing O] in
theorem single_eq_mul [CommRing O] (i : ZMod n) (a : LetA O n) (g : PowerSeries O) :
    (Pi.single i (a i * g) : LetA O n) = a * Pi.single i g := by
  funext j; by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem key_inclusion {ι κ : Type} [Fintype ι] [Fintype κ] (t : ι → PowerSeries O)
    (ht : ∀ y : PowerSeries O, ∃! z : ι → PowerSeries O, y = ∑ j, t j * W.φ₀ (z j))
    (c1 : IsCrys PD T₁.ρ) (c2 : IsCrys PD T₂.ρ) (b : Module.Basis κ (LetA O n) (W.N T₂)) (hQ : ∀ a, a * W.Q = 0 → a = 0)
    (M h : ZMod n → ℕ) (h1 : p5 W T₁ M h) (h2 : p5 W T₂ M h) (H : ℕ) (i : ZMod n)
    (hH : M i + h i ≤ H) (g : PowerSeries O) (hg : g ∈ ann W π i) :
    W.Q i ^ H * g ∈ (ann W π (i - 1)).map W.φ₀ := by
  obtain ⟨z, hz, -⟩ := ht (W.Q i ^ H * g)
  rw [hz]
  refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ fun y hy => ?_)
  let φ : LetA O n →+* LetA O n := W.φA
  let Φ : W.DD T₂ →+ W.DD T₂ := (W.φD T₂).toAddMonoidHom
  have hΦ : ∀ a x, Φ (a • x) = φ a • Φ x := φD_smulA W T₂
  let tt : ι → LetA O n := fun j _ => t j
  have hex : ∀ a : LetA O n, ∃ z : ι → LetA O n, a = ∑ j, tt j * φ (z j) := fun a => by
    choose z hz using fun i => (ht (a i)).exists
    refine ⟨fun j i => z (i + 1) j, funext fun i => ?_⟩
    rw [hz i, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = t j * W.φ₀ (z (i - 1 + 1) j)
    rw [sub_add_cancel]
  have hun : ∀ z : ι → LetA O n, ∑ j, tt j * φ (z j) = 0 → z = 0 := fun z hz => by
    funext j i
    have e := congrFun hz (i + 1)
    rw [Finset.sum_apply] at e
    have := (ht 0).unique (y₁ := fun j => z j (i + 1 - 1)) (y₂ := 0) e.symm (by simp)
    simpa using congrFun this j
  let b' : κ → W.DD T₂ := fun k => b k
  have hspan : Submodule.span (LetA O n) (Set.range b') = W.N T₂ := by
    have := congrArg (Submodule.map (W.N T₂).subtype) b.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at this
  have hb' : LinearIndependent (LetA O n) b' :=
    b.linearIndependent.map' (W.N T₂).subtype (Submodule.ker_subtype _)
  have hind : LinearIndependent (LetA O n) fun k => Φ (b' k) := by
    refine indep_of_commensurable W.Q hQ b' _ hb' (fun k => ?_) fun k => ?_
    · rw [hspan]; exact W.N_φ T₂ _ (b k).2
    · obtain ⟨m, hm⟩ := W.N_φinv T₂ _ (b k).2
      refine ⟨m, (Submodule.span_le.2 ?_ : _ ≤ _) hm⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [← hspan, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, rfl⟩ := hx
      change Φ _ ∈ _
      rw [map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [hΦ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hw := h2.1 i _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxe⟩ := hg _ hw
  have hx2 := h1.2.1 i _ ⟨x, hx, rfl⟩
  have hx3 : mapA W π (W.Q ^ h i • (letE i : LetA O n) • x) ∈
      Submodule.span (LetA O n) (Φ '' ((W.N T₁).map (mapA W π) : Set (W.DD T₂))) := by
    refine (Submodule.span_le (p := Submodule.comap (mapA W π) (Submodule.span (LetA O n)
      (Φ '' ((W.N T₁).map (mapA W π) : Set (W.DD T₂)))))).2 ?_ hx2
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨_, ⟨_, (W.N T₁).smul_mem (letE (i - 1)) hu, rfl⟩,
      (W.map_φ π _).symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hH
  have hx4 : W.Q ^ d • mapA W π (W.Q ^ h i • (letE i : LetA O n) • x) =
      ∑ j, tt j • Φ ((Pi.single (i - 1) (z j) : LetA O n) • y) := by
    have e1 : ∀ j, tt j • Φ ((Pi.single (i - 1) (z j) : LetA O n) • y) =
        (Pi.single i (t j * W.φ₀ (z j)) : LetA O n) • Φ y := fun j => by
      rw [hΦ, smul_smul, single_eq_mul i (tt j), ← φA_single]; rfl
    simp only [e1]
    rw [← Finset.sum_smul, map_smul, map_smul, hxe]
    change _ • _ • _ • _ • _ • Φ ((Pi.single (i - 1) 1 : LetA O n) • y) = _
    rw [hΦ]
    simp only [smul_smul]
    congr 1
    change _ * (_ * (_ * (_ * (_ * W.φA _)))) = _
    rw [φA_single]
    funext k
    by_cases hk : k = i
    · subst hk
      simp only [Finset.sum_apply, Pi.single_eq_same, ← hz, Pi.mul_apply, Pi.pow_apply, letE, map_one]
      ring
    · simp [hk]
  obtain ⟨u, hu, hue⟩ := decomp_exists φ Φ hΦ tt hex _ _ (Submodule.smul_mem _ (W.Q ^ d) hx3)
  rw [hx4] at hue
  have hN : ∀ j, u j ∈ W.N T₂ := fun j => by
    obtain ⟨x, hx, e⟩ := hu j
    exact e ▸ W.map_N π c1 c2 x hx
  have := decomp_unique φ Φ hΦ tt hun b' hind
    (fun j => (Pi.single (i - 1) (z j) : LetA O n) • y - u j)
    (fun j => hspan ▸ sub_mem ((W.N T₂).smul_mem _ hy) (hN j))
    (by simp only [map_sub, smul_sub, Finset.sum_sub_distrib, hue, sub_self]) j
  rw [sub_eq_zero.1 this]
  exact hu j

theorem kills_of_mem_ann (i : ZMod n) (a : LetA O n) (ha : a i ∈ ann W π i) (y : W.DD T₂)
    (hy : y ∈ W.Nl T₂ i) : a • y ∈ (W.Nl T₁ i).map (mapA W π) := by
  obtain ⟨y, hy, rfl⟩ := hy
  obtain ⟨x, hx, e⟩ := ha y hy
  refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
  change mapA W π ((letE i : LetA O n) • x) = a • (letE i : LetA O n) • y
  rw [map_smul, e, smul_smul, smul_smul, letE, ← single_eq_mul, ← single_eq_mul]
  simp

theorem kills_of_cyclotomic {l : ℕ} [Fact l.Prime] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O] [NeZero n]
    (hl0 : (l : O) ≠ 0) (hu : ¬ IsUnit (l : O)) (hp : PD.p = l) {s : ℕ} (hWs : W.s = s)
    (hφ : W.φ₀ = GlobalTheory.Cyc.phi l O) (hX : ∀ i, W.X i = GlobalTheory.Cyc.XX l O s)
    (hQ : ∀ i, W.Q i = GlobalTheory.Cyc.QQ l O s)
    (hQu : IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ 0) W.Q)))
    (hcard : l ≠ 2 → s = 1 → Module.finrank K₀ K ∣ l - 1)
    (c1 : IsCrys PD T₁.ρ) (c2 : IsCrys PD T₂.ρ) {r : ℕ}
    (hb : Nonempty (Module.Basis (Fin r) (LetA O n) (W.N T₂))) (M h : ZMod n → ℕ)
    (h1 : JumpsLet W T₁ M h → p5 W T₁ M h) (h2 : JumpsLet W T₁ M h → p5 W T₂ M h)
    (hc : ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : LetA O n) ^ c • z) ∧
      ∃ y ∈ W.N T₁, W.map π y = (letπ : LetA O n) ^ c • z) : wachLengthLatticeMap W π M h := by
  intro _ hJ
  replace h1 := h1 hJ
  replace h2 := h2 hJ
  obtain ⟨b⟩ := hb
  obtain ⟨c, hc⟩ := hc
  have hs1 : 1 ≤ s := hWs ▸ W.s_pos
  have hQr : ∀ a, a * W.Q = 0 → a = 0 := fun a ha => by
    apply W.EE_inj
    rw [pow_zero, AlgHom.one_apply] at hQu
    rw [map_zero, ← hQu.mul_left_eq_zero, ← map_mul, ha, map_zero]
  have hmain : ∀ i, W.X i ^ (⨆ j, (M j + h j)) ∈ ann W π i := by
    intro i
    rw [hX]
    refine GlobalTheory.Cyc.XX_pow_mem_of_QQ_pow_mul_mem_map_phi l _ hl0 hu s _ _ c hs1 (ann W π)
      (fun i y hy => ?_) (fun i g hg => ?_) i
    · obtain ⟨x, hx, e⟩ := (hc y hy).2
      have e2 : (Pi.single i (PowerSeries.X ^ c) : LetA O n) = Pi.single i 1 * letπ ^ c := by
        rw [mul_comm, ← single_eq_mul, mul_one]; rfl
      rw [e2, mul_smul]
      exact Submodule.smul_mem _ _ ⟨x, hx, e⟩
    · rw [← hQ i, ← hφ]
      refine key_inclusion W π (fun j : Fin l => (1 + PowerSeries.X) ^ (j : ℕ)) ?_ c1 c2 b hQr M h
        h1 h2 _ i (le_ciSup (f := fun j => M j + h j) (Set.finite_range _).bddAbove i) g hg
      rw [hφ]
      exact GlobalTheory.Cyc.phi_free l _ hl0 hu
  refine ⟨fun i y hy => kills_of_mem_ann W π i _ (hmain i) y hy, ?_⟩
  rintro hs π' - ⟨w, rfl⟩ i y hy -
  refine kills_of_mem_ann W π i _ ?_ y hy
  have hl : l ≠ 2 := fun e => by
    have := W.s_two (hp.trans e)
    omega
  obtain ⟨s', hs'⟩ := hcard hl (hWs.symm.trans hs)
  have hXi : W.X i = PowerSeries.X := by
    rw [LocWach.X, hs]; rfl
  have h2l := (Fact.out : l.Prime).two_le
  have hm := hmain i
  rw [hXi] at hm
  rw [hp]
  generalize (⨆ j, (M j + h j)) = H at *
  generalize Module.finrank K₀ K = e at *
  have he : 0 < e := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hs'; omega
  have hle : H ≤ (l - 1) / e * ⌈((e * H : ℕ) : ℚ) / ((l : ℚ) - 1)⌉₊ := by
    have h3 := Nat.le_ceil (((e * H : ℕ) : ℚ) / ((l : ℚ) - 1))
    generalize ⌈((e * H : ℕ) : ℚ) / ((l : ℚ) - 1)⌉₊ = a at *
    have h4 : (l : ℚ) - 1 = ((e * s' : ℕ) : ℚ) := by
      rw [← hs', Nat.cast_sub (by omega), Nat.cast_one]
    have h5 : 0 < e * s' := by omega
    rw [h4, div_le_iff₀ (by exact_mod_cast h5)] at h3
    have h6 : e * H ≤ a * (e * s') := by exact_mod_cast h3
    rw [hs', Nat.mul_div_cancel_left _ he]
    exact Nat.le_of_mul_le_mul_left (h6.trans_eq (by ring)) he
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [mul_pow, ← pow_mul, hd, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hm)

end Generic

theorem exists_kernel_padic {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (T₁ T₂ : Lt K LL)
    (π : LatHom T₁.L T₂.L) (hπ : π.Onto) :
    ∃ (T₀ : Lt K LL) (ι : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) ι π := by
  obtain ⟨_, -, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
    haveI := LL.2
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  exact exists_kernel π hπ

end GlobalTheory.NL.CokerKill

open GlobalTheory.NL.CokerKill in

theorem GlobalTheory.NL.CokerKill.X_pow_kills_coker : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), lem3 D HW F := by
  intro D HW F Cm l _ K s LL hG T₁ T₂ π M h c1 c2
  obtain ⟨_, hcomp, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨χ, -, hφ, -, hX, hQ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL hG
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := by
    haveI := K.2
    haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
    exact ⟨Module.finrank_pos.ne'⟩
  by_cases hπ : π.Onto
  swap
  · exact fun h => absurd h hπ
  obtain ⟨T₀, ι, hses⟩ := exists_kernel_padic K LL T₁ T₂ π hπ
  have c0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL _ T₀.ρ _ T₁.ρ ι.f ι.equiv).1
    hses.1 c1
  have hj := (GlobalTheory.NL.JumpsSES.jumps_ses_and_one D HW l K s LL hG T₀ T₁ T₂ ι π c1 hses).1
  exact kills_of_cyclotomic _ π (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hu
    ((D.loc l).PD_p K) ((HW l).W_s K s LL hG) hφ hX hQ
    ((GlobalTheory.NL.IoXQ.main D HW F l K s LL hG).2.2.2.2.2.2 0).2
    (fun hl hs => Dvd.intro_left _ (GlobalTheory.TorsionCard.card_torsion_mul_finrank (D.loc l) K LL
      ((HW l).W K s LL hG) hl (hs ▸ hG.2.2.1)))
    c1 c2 (GlobalTheory.NL.N_basis D HW F l K s LL hG T₂ c2) M h
    (GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm l K s LL hG T₁ M h c1)
    (fun hJ => GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm l K s LL hG T₂ M h c2 fun τ i hτ a ha =>
      hJ τ i hτ a ((hj τ a).2 (Or.inr ha)))
    (GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL hG T₀ T₁ T₂ ι π c0 c1 c2 hses)
