import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.WachLatticeTwists.TheoremNFiveSplit

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions.N

namespace Formalism.MainNotions.EmbeddingTypes

section Rank

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V] (ρ : Representation LL G V)

theorem rank_eq_count (hBK : BlochKatoDim PD LL) (hS : Splits LL (K := K) (Qp := Qp))
    (hc : ∀ x, Continuous fun g => ρ g x) (hcr : IsCrys PD ρ) (h0 : H0V ρ = ⊥)
    (hF : FilCount PD ρ) (S : (K →ₐ[Qp] LL) → Finset ℤ)
    (hS1 : ∀ τ a, multV PD ρ τ a = if a ∈ S τ then 1 else 0) :
    finrank LL (FiniteCohomology PD ρ) = 0 + ∑ τ, Formalism.RepresentationBoundsCohomology.negCount (S τ).val := by
  have h1 := hBK hS V ρ hc hcr
  rw [h0, finrank_bot] at h1
  have h2 : ∀ τ : K →ₐ[Qp] LL, (finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0) =
      (Formalism.RepresentationBoundsCohomology.negCount (S τ).val : ℤ) := by
    intro τ
    rw [hF τ (S τ) (fun a ha => by rw [hS1, if_neg ha])]
    rw [Finset.sum_congr rfl (fun a ha => by rw [hS1, if_pos (Finset.mem_filter.mp ha).1])]
    simp [Formalism.RepresentationBoundsCohomology.negCount, Finset.filter_val, Finset.card_def]
  rw [Finset.sum_congr rfl (fun τ _ => h2 τ)] at h1
  have h3 : (finrank LL (FiniteCohomology PD ρ) : ℤ) = ((0 + ∑ τ, Formalism.RepresentationBoundsCohomology.negCount (S τ).val : ℕ) : ℤ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h3

theorem rank_le_col (hBK : BlochKatoDim PD LL) (hS : Splits LL (K := K) (Qp := Qp))
    (hc : ∀ x, Continuous fun g => ρ g x) (hcr : IsCrys PD ρ) (h0 : H0V ρ = ⊥)
    (hF : FilCount PD ρ) (m : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, ∃ C L : Finset ℤ, (∀ a ∈ C, 0 < a) ∧ L.card ≤ m ∧
      ∀ a, multV PD ρ τ a = if a ∈ C ∪ L then 1 else 0) :
    finrank LL (FiniteCohomology PD ρ) ≤ finrank Qp K * m := by
  choose C Lo hC hLo hm using hJ
  have h := rank_eq_count PD ρ hBK hS hc hcr h0 hF (fun τ => C τ ∪ Lo τ) hm
  have hS' := hS
  obtain ⟨-, hcard⟩ := hS'
  have hb : ∀ τ, Formalism.RepresentationBoundsCohomology.negCount (C τ ∪ Lo τ).val ≤ m := by
    intro τ
    have hsub : (C τ ∪ Lo τ).filter (fun u => u < 0) ⊆ Lo τ := by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_union] at ha
      obtain ⟨h1 | h1, h2⟩ := ha
      · exact absurd h2 (lt_asymm (hC τ a h1))
      · exact h1
    calc Multiset.card (Multiset.filter (fun u => u < 0) (C τ ∪ Lo τ).val)
        = ((C τ ∪ Lo τ).filter (fun u => u < 0)).card := rfl
      _ ≤ (Lo τ).card := Finset.card_le_card hsub
      _ ≤ m := hLo τ
  rw [h, zero_add]
  calc _ ≤ ∑ _τ : K →ₐ[Qp] LL, m := Finset.sum_le_sum (fun τ _ => hb τ)
    _ = finrank Qp K * m := by rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]

theorem rank_le_row (hBK : BlochKatoDim PD LL) (hS : Splits LL (K := K) (Qp := Qp))
    (hc : ∀ x, Continuous fun g => ρ g x) (hcr : IsCrys PD ρ) (h0 : H0V ρ = ⊥)
    (hF : FilCount PD ρ) (m : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, ∃ C L : Finset ℤ, (∀ a ∈ C, a < 0) ∧ L.card ≤ m ∧
      ∀ a, multV PD ρ τ a = if -a - 1 ∈ C ∪ L then 1 else 0) :
    finrank LL (FiniteCohomology PD ρ) ≤ finrank Qp K * m := by
  choose C Lo hC hLo hm using hJ
  have hmem : ∀ τ a, a ∈ (C τ ∪ Lo τ).image (fun b => -b - 1) ↔ -a - 1 ∈ C τ ∪ Lo τ := by
    intro τ a
    rw [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      convert hb using 1
      show -(-b - 1) - 1 = b
      ring
    · intro h
      exact ⟨-a - 1, h, by show -(-a - 1) - 1 = a; ring⟩
  have hS1 : ∀ τ a, multV PD ρ τ a =
      if a ∈ (C τ ∪ Lo τ).image (fun b => -b - 1) then 1 else 0 := by
    intro τ a
    rw [hm τ a]
    by_cases h : -a - 1 ∈ C τ ∪ Lo τ
    · rw [if_pos h, if_pos ((hmem τ a).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((hmem τ a).mp h'))]
  have h := rank_eq_count PD ρ hBK hS hc hcr h0 hF
    (fun τ => (C τ ∪ Lo τ).image (fun b => -b - 1)) hS1
  have hS' := hS
  obtain ⟨-, hcard⟩ := hS'
  have hb : ∀ τ, Formalism.RepresentationBoundsCohomology.negCount ((C τ ∪ Lo τ).image (fun b => -b - 1)).val ≤ m := by
    intro τ
    have hsub : ((C τ ∪ Lo τ).image (fun b => -b - 1)).filter (fun u => u < 0) ⊆
        (Lo τ).image (fun b => -b - 1) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨ha1, ha2⟩ := ha
      have h1 := (hmem τ a).mp ha1
      rw [Finset.mem_union] at h1
      rcases h1 with h1 | h1
      · have := hC τ _ h1
        omega
      · exact Finset.mem_image.mpr ⟨-a - 1, h1, by show -(-a - 1) - 1 = a; ring⟩
    calc Multiset.card
          (Multiset.filter (fun u => u < 0) ((C τ ∪ Lo τ).image (fun b => -b - 1)).val)
        = (((C τ ∪ Lo τ).image (fun b => -b - 1)).filter (fun u => u < 0)).card := rfl
      _ ≤ ((Lo τ).image (fun b => -b - 1)).card := Finset.card_le_card hsub
      _ ≤ (Lo τ).card := Finset.card_image_le
      _ ≤ m := hLo τ
  rw [h, zero_add]
  calc _ ≤ ∑ _τ : K →ₐ[Qp] LL, m := Finset.sum_le_sum (fun τ _ => hb τ)
    _ = finrank Qp K * m := by rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]

end Rank

section Row

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

section Two

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']

variable {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}

theorem col_le_of_lift (F : LatHom L L') (e : ℕ) (h : F.LiftF PD e) :
    F.col PD ≤ lenModPow PD L' e := by
  have hle : (powB PD L' e).comap (latticeFiniteCocycles PD L').subtype ≤ (F.ImF PD).comap (latticeFiniteCocycles PD L').subtype := by
    apply Submodule.comap_mono
    refine sup_le ?_ le_sup_right
    rintro _ ⟨c, hc, rfl⟩
    exact h c hc
  exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

theorem lenModPow_le_of_retract (E : LatHom L L') (E' : LatHom L' L) (hE : ∀ x, E.f (E'.f x) = x)
    (n : ℕ) : lenModPow PD L' n ≤ lenModPow PD L n := by
  let φ : ↥(latticeFiniteCocycles PD L) →ₗ[O] ↥(latticeFiniteCocycles PD L') := E.post.restrict fun c hc => E.post_Z1fT PD c hc
  have hφ : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    refine ⟨⟨E'.post c, E'.post_Z1fT PD c hc⟩, ?_⟩
    apply Subtype.ext
    funext g
    exact hE (c g)
  have hmap : (powB PD L n).comap (latticeFiniteCocycles PD L).subtype ≤
      ((powB PD L' n).comap (latticeFiniteCocycles PD L').subtype).comap φ := by
    rintro ⟨c, hc⟩ hmem
    change E.post c ∈ powB PD L' n
    have hmem' : c ∈ powB PD L n := hmem
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hmem'
    rw [map_add]
    refine Submodule.add_mem_sup ?_ (E.post_B1T b hb)
    obtain ⟨a0, ha0, rfl⟩ := ha
    refine ⟨E.post a0, E.post_Z1fT PD a0 ha0, ?_⟩
    simp
  have hsurj : Function.Surjective (Submodule.mapQ _ _ φ hmap) := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  exact Module.length_le_of_surjective (Submodule.mapQ _ _ φ hmap) hsurj

end Two

theorem subquot_of_sub {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V)
    {ι : Type} {k : ℕ} (Ms : ι → G → Matrix (Fin k) (Fin k) LL) (h : IsSubOfSums ρ Ms) :
    IsSubquotOfSums ρ Ms := by
  unfold IsSubOfSums at h
  unfold IsSubquotOfSums
  obtain ⟨m, xs, j, hj, hjρ⟩ := h
  have hker : LinearMap.ker j = ⊥ := LinearMap.ker_eq_bot.mpr hj
  obtain ⟨q, hq⟩ := j.exists_leftInverse_of_injective hker
  have hqj : ∀ v, q (j v) = v := fun v => by
    have := LinearMap.congr_fun hq v
    simpa using this
  refine ⟨m, xs, LinearMap.range j, q, ?_, ?_, ?_⟩
  · intro g u hu
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hu
    exact LinearMap.mem_range.mpr ⟨ρ g v, hjρ g v⟩
  · intro v
    exact ⟨j v, LinearMap.mem_range.mpr ⟨v, rfl⟩, hqj v⟩
  · intro g u hu
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hu
    rw [← hjρ g v, hqj, hqj]

theorem subquot_of_quot {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V')
    {ι : Type} {k : ℕ} (Ms : ι → G → Matrix (Fin k) (Fin k) LL) (h : IsSubquotOfSums ρ Ms)
    (f : V →ₗ[LL] V') (hf : Function.Surjective f) (hfg : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    IsSubquotOfSums ρ' Ms := by
  unfold IsSubquotOfSums at h ⊢
  obtain ⟨m, xs, U, q, hU, hs, hq⟩ := h
  first
  | (refine ⟨m, xs, U, f.comp q, hU, ?_, ?_⟩
     · intro v'
       obtain ⟨v, rfl⟩ := hf v'
       obtain ⟨u, hu, rfl⟩ := hs v
       exact ⟨u, hu, rfl⟩
     · intro g u hu
       simp only [LinearMap.comp_apply]
       rw [hq g u hu, hfg])
  | (refine ⟨m, xs, U, fun u => f (q u), hU, ?_, ?_⟩
     · intro v'
       obtain ⟨v, rfl⟩ := hf v'
       obtain ⟨u, hu, rfl⟩ := hs v
       exact ⟨u, hu, rfl⟩
     · intro g u hu
       show f (q _) = ρ' g (f (q u))
       rw [hq g u hu, hfg])

theorem rowAt_of_lift {ι : Type} {k k2 : ℕ} (Ms : ι → G → Matrix (Fin k) (Fin k) LL)
    (M2 : G →* Matrix (Fin k2) (Fin k2) LL) (L2 : Lattice (O := O) (matRep M2))
    (hL2 : ∀ v, v ∈ L2.T ↔ ∀ j, v j ∈ Set.range (algebraMap O LL))
    (e' : ℕ) (hLift : LiftAt PD (O := O) Ms e') (rk n m r c0 : ℕ) (lenH0 : ℕ∞)
    (hH1f : lenModPow PD L2 e' ≤ (e' : ℕ∞) * (rk : ℕ∞) * lenOl PD (O := O) + lenH0)
    (hrk : rk ≤ n * m) (hH0 : lenH0 ≤ (r : ℕ∞) * (c0 : ℕ∞) * lenOl PD (O := O))
    (hfin : lenOl PD (O := O) ≠ ⊤) :
    RowAt PD (O := O) Ms (⇑M2) ((n : ℚ) * (m : ℚ) * (e' : ℚ) + (r : ℚ) * (c0 : ℚ)) := by
  intro V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hmat V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hsub F hF
  have hsq1 := subquot_of_sub ρ1 Ms hsub
  have hFs : Function.Surjective F.f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← T2.span, Submodule.span_le]
    intro y hy
    obtain ⟨x, _, rfl⟩ := hF y hy
    exact ⟨x, rfl⟩
  have hsq2 := subquot_of_quot ρ1 ρ2 Ms hsq1 F.f hFs F.equiv
  have hl := hLift V1 ρ1 T1 hc1 hsq1 V2 ρ2 T2 hc2 hsq2 F hF
  have h1 := col_le_of_lift PD F e' hl
  obtain ⟨e, heg, heT⟩ := hmat
  have : ContinuousSMul LL V2 := IsModuleTopology.toContinuousSMul LL V2
  let E : LatHom L2 T2 :=
    { f := (e.symm : (Fin k2 → LL) →ₗ[LL] V2)
      equiv := by
        intro g x
        apply e.injective
        rw [heg]
        simp [matRep]
      cont := IsModuleTopology.continuous_of_linearMap _
      T_le := by
        intro x hx
        rw [heT]
        simpa using (hL2 x).mp hx }
  let E' : LatHom T2 L2 :=
    { f := (e : V2 →ₗ[LL] (Fin k2 → LL))
      equiv := by
        intro g x
        change e (ρ2 g x) = _
        rw [heg]
        simp [matRep]
      cont := IsModuleTopology.continuous_of_linearMap _
      T_le := by
        intro x hx
        exact (hL2 _).mpr ((heT x).mp hx) }
  have h2 := lenModPow_le_of_retract PD E E' (fun x => by simp [E, E']) e'
  obtain ⟨kO, hkO⟩ := ENat.ne_top_iff_exists.mp hfin
  have h3 : F.col PD ≤ ((e' * rk * kO + r * c0 * kO : ℕ) : ℕ∞) := by
    refine (h1.trans h2).trans (hH1f.trans ?_)
    rw [← hkO] at hH0 ⊢
    push_cast
    exact add_le_add le_rfl hH0
  obtain ⟨mm, hmm, hle⟩ := ENat.le_natCast_iff.mp h3
  refine ⟨mm, kO, hmm, hkO.symm, ?_⟩
  have h4 : (mm : ℚ) ≤ ((e' * rk * kO + r * c0 * kO : ℕ) : ℚ) := by exact_mod_cast hle
  have h5 : (rk : ℚ) ≤ (n : ℚ) * m := by exact_mod_cast hrk
  push_cast at h4
  have h6 : (e' : ℚ) * rk * kO ≤ (e' : ℚ) * ((n : ℚ) * m) * kO := by gcongr
  nlinarith [h4, h6]

end Row

section Len

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]

theorem len_le_of_kill [IsFractionRing O LL] {k : ℕ} (T : Submodule O (Fin k → LL))
    (hT : ∀ v, v ∈ T ↔ ∀ j, v j ∈ Set.range (algebraMap O LL))
    (N : Submodule O ((Fin k → LL) ⧸ T)) (c : ℕ)
    (hk : ∀ x ∈ N, (((PD.p : ℕ) : O) ^ c) • x = 0) :
    Module.length O N ≤ (k : ℕ∞) * (c : ℕ∞) * lenOl PD (O := O) := by
  let a : LL →ₗ[O] Formalism.NG.KO O :=
    (Submodule.mkQ (1 : Submodule O (FractionRing O))).comp
      (FractionRing.algEquiv O LL).symm.toLinearMap
  have ha : ∀ x : LL, a x = 0 ↔ x ∈ Set.range (algebraMap O LL) := by
    intro x
    change Submodule.Quotient.mk ((FractionRing.algEquiv O LL).symm x) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have := congrArg (FractionRing.algEquiv O LL) hy
      simpa using this
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp⟩
  let ψ : (Fin k → LL) →ₗ[O] (Fin k → Formalism.NG.KO O) := a.compLeft (Fin k)
  have hker : LinearMap.ker ψ = T := by
    ext v
    rw [LinearMap.mem_ker, hT, funext_iff]
    exact forall_congr' fun j => ha (v j)
  let Ψ : ((Fin k → LL) ⧸ T) →ₗ[O] (Fin k → Formalism.NG.KO O) := T.liftQ ψ hker.ge
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have h1 := Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O (Fin k) (N.map Ψ) PD.p c (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_smul, hk x hx, map_zero])
  rw [← (Submodule.equivMapOfInjective Ψ hΨ N).length_eq, Fintype.card_fin] at h1
  rw [mul_assoc]
  exact h1

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

abbrev H1fQuotient (L : Lattice (O := O) ρ) : Type := ↥(latticeFiniteCocycles PD L) ⧸ (latticeCoboundaries L).comap (latticeFiniteCocycles PD L).subtype

theorem lenModPow_le_of_fg (L : Lattice (O := O) ρ) [Module.Finite O (H1fQuotient PD L)] (n : ℕ) :
    lenModPow PD L n ≤ (n : ℕ∞) * (finrank O (H1fQuotient PD L) : ℕ∞) * lenOl PD (O := O) +
      Module.length O (Submodule.torsion O (H1fQuotient PD L)) := by
  let I : Submodule O (H1fQuotient PD L) :=
    LinearMap.range ((((PD.p : ℕ) : O) ^ n) • (LinearMap.id : H1fQuotient PD L →ₗ[O] H1fQuotient PD L))
  have h1 := Formalism.RepresentationBoundsCohomology.rowColength O (H1fQuotient PD L) I PD.p n (fun m => ⟨m, rfl⟩)
  have hle : (latticeCoboundaries L).comap (latticeFiniteCocycles PD L).subtype ≤ (powB PD L n).comap (latticeFiniteCocycles PD L).subtype :=
    Submodule.comap_mono le_sup_right
  have hI : I ≤ LinearMap.ker (Submodule.factor hle) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker]
    change Submodule.factor hle ((((PD.p : ℕ) : O) ^ n) • Submodule.Quotient.mk c) = 0
    rw [← Submodule.Quotient.mk_smul]
    change (Submodule.Quotient.mk ((((PD.p : ℕ) : O) ^ n) • c) :
      ↥(latticeFiniteCocycles PD L) ⧸ (powB PD L n).comap (latticeFiniteCocycles PD L).subtype) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_left ⟨c.1, c.2, rfl⟩
  have hs : Function.Surjective (I.liftQ (Submodule.factor hle) hI) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.factor_surjective hle y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine (Module.length_le_of_surjective _ hs).trans (h1.trans (le_of_eq ?_))
  rw [lenOl]
  ring

end Len

section TypeU

private theorem exists_ringOfIntegers_eq_algEquiv_apply {E : Type} [Field E] [NumberField E] (f : E ≃ₐ[ℚ] E)
    (x : NumberField.RingOfIntegers E) :
    ∃ y : NumberField.RingOfIntegers E, (y : E) = f (x : E) :=
  ⟨⟨f (x : E), (NumberField.RingOfIntegers.isIntegral_coe x).map f.toAlgHom.toRingHom.toIntAlgHom⟩, rfl⟩

theorem not_typeU_conj {E Lc Kf : Type} [Field E] [Field Lc] [Field Kf] (cj : E →+* E) (b : E) (z : ℂ)
    (hz : z ≠ 0) (hzi : starRingEnd ℂ z = -z)
    (hcj : ∀ (φ : E →+* ℂ) (x : E), φ (cj x) = starRingEnd ℂ (φ x))
    (embK : Lc →+* Kf) (embC : Lc →+* ℂ) (σ : E →+* Kf)
    (h1 : (∀ x, ∃ y, embK y = σ x) ∧ ∃ φ : E →+* ℂ, φ b = z ∧ ∀ x y, embK y = σ x → embC y = φ x)
    (h2 : ∃ φ : E →+* ℂ, φ b = z ∧ ∀ x y, embK y = σ (cj x) → embC y = φ x) : False := by
  obtain ⟨hsurj, φ, hφb, hφ⟩ := h1
  obtain ⟨φ', hφ'b, hφ'⟩ := h2
  obtain ⟨y, hy⟩ := hsurj (cj b)
  have e : z = -z := by
    calc z = φ' b := hφ'b.symm
      _ = embC y := (hφ' b y hy).symm
      _ = φ (cj b) := hφ (cj b) y hy
      _ = starRingEnd ℂ (φ b) := hcj φ b
      _ = starRingEnd ℂ z := by rw [hφb]
      _ = -z := hzi
  exact hz (by linear_combination e / 2)

open NumberField IsDedekindDomain in

theorem conjPl_unique {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E)
    (u v v' : HeightOneSpectrum (𝓞 E))
    (h : ∀ x y : 𝓞 E, (y : E) = cj (x : E) → (x ∈ u.asIdeal ↔ y ∈ v.asIdeal))
    (h' : ∀ x y : 𝓞 E, (y : E) = cj (x : E) → (x ∈ u.asIdeal ↔ y ∈ v'.asIdeal)) : v = v' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := exists_ringOfIntegers_eq_algEquiv_apply cj.symm y
  have hx' : (y : E) = cj (x : E) := by rw [hx]; exact (cj.apply_symm_apply _).symm
  exact (h x y hx').symm.trans (h' x y hx')

open NumberField IsDedekindDomain in

theorem conjPl_unique' {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E)
    (u u' v : HeightOneSpectrum (𝓞 E))
    (h : ∀ x y : 𝓞 E, (y : E) = cj (x : E) → (x ∈ u.asIdeal ↔ y ∈ v.asIdeal))
    (h' : ∀ x y : 𝓞 E, (y : E) = cj (x : E) → (x ∈ u'.asIdeal ↔ y ∈ v.asIdeal)) : u = u' := by
  apply HeightOneSpectrum.ext
  ext x
  obtain ⟨y, hy⟩ := exists_ringOfIntegers_eq_algEquiv_apply cj x
  exact (h x y hy).trans (h' x y hy).symm

open NumberField IsDedekindDomain Pointwise in

theorem ef_conj {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E)
    (u w : HeightOneSpectrum (𝓞 E))
    (h : ∀ x y : 𝓞 E, (y : E) = cj (x : E) → (x ∈ u.asIdeal ↔ y ∈ w.asIdeal)) :
    w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ =
      u.asIdeal.ramificationIdx ℤ * u.asIdeal.inertiaDeg ℤ := by
  have hw : w.asIdeal = cj • u.asIdeal := by
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hy : (y : E) = cj ((cj⁻¹ • y : 𝓞 E) : E) := by
      have : ((cj⁻¹ • y : 𝓞 E) : E) = cj⁻¹ (y : E) := rfl
      rw [this]
      exact (AlgEquiv.apply_symm_apply cj (y : E)).symm
    exact (h _ y hy).symm
  rw [hw, Ideal.ramificationIdx_smul, Ideal.inertiaDeg_smul]

end TypeU

section TypeD

open NumberField IsDedekindDomain

variable {E Lc Kf : Type} [Field E] [NumberField E] [Field Lc] [Field Kf]

def TypeUAt (b : E) (z : ℂ) (embK : Lc →+* Kf) (embC : Lc →+* ℂ) (σ : E →+* Kf) : Prop :=
  (∀ x, ∃ y, embK y = σ x) ∧ ∃ φ : E →+* ℂ, φ b = z ∧ ∀ x y, embK y = σ x → embC y = φ x

def Induces (sm : Set Kf) (v : HeightOneSpectrum (𝓞 E)) (σ : E →+* Kf) : Prop :=
  ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ σ (x : E) ∈ sm

theorem induces_conj (sm : Set Kf) (cj : E ≃ₐ[ℚ] E) (u w : HeightOneSpectrum (𝓞 E))
    (h : ∀ x y : 𝓞 E, (y : E) = cj (x : E) → (x ∈ u.asIdeal ↔ y ∈ w.asIdeal)) (σ : E →+* Kf)
    (hσ : Induces sm w σ) : Induces sm u (σ.comp (cj : E →+* E)) := by
  unfold Induces at hσ ⊢
  intro x
  obtain ⟨y, hy⟩ := exists_ringOfIntegers_eq_algEquiv_apply cj x
  have e : (σ.comp (cj : E →+* E)) (x : E) = σ (y : E) := by
    show σ (cj (x : E)) = σ (y : E)
    rw [hy]
  rw [e, h x y hy]
  exact hσ y

theorem typeD_of_conj (sm : Set Kf) (cj : E ≃ₐ[ℚ] E) (b : E) (z : ℂ) (hz : z ≠ 0)
    (hzi : starRingEnd ℂ z = -z)
    (hcj : ∀ (φ : E →+* ℂ) (x : E), φ (cj x) = starRingEnd ℂ (φ x))
    (embK : Lc →+* Kf) (embC : Lc →+* ℂ) (u w : HeightOneSpectrum (𝓞 E))
    (h : ∀ x y : 𝓞 E, (y : E) = cj (x : E) → (x ∈ u.asIdeal ↔ y ∈ w.asIdeal))
    (hU : ∀ σ : E →+* Kf, Induces sm u σ → TypeUAt b z embK embC σ)
    (σ : E →+* Kf) (hσ : Induces sm w σ) : ¬ TypeUAt b z embK embC σ := by
  intro hT
  have hI := induces_conj sm cj u w h σ hσ
  obtain ⟨_, hT2⟩ := hU _ hI
  exact not_typeU_conj (cj : E →+* E) b z hz hzi hcj embK embC σ hT hT2

end TypeD

section Std

theorem mem_stdG_iff {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (k : ℕ) (v : Fin k → LL) :
    v ∈ stdG O LL k ↔ ∀ j, v j ∈ Set.range (algebraMap O LL) := by
  unfold stdG
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩ j
    exact ⟨x j, rfl⟩
  · intro h
    choose x hx using h
    exact ⟨x, funext hx⟩

theorem length_quot_ne_top {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O)
    (ha : a ≠ 0) : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
  rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
  exact fun h => ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)

end Std

section Arith

theorem sum_lenW_le {P : Type} [DecidableEq P] (row col : Finset P) (hd : Disjoint row col)
    (lenW colB rowB : P → ℚ) (back : P → P) (hback : ∀ v ∈ row, back v ∈ col)
    (hinj : Set.InjOn back row) (hcol : ∀ u ∈ col, lenW u ≤ colB u)
    (hrow : ∀ v ∈ row, lenW v ≤ rowB (back v)) (hnn : ∀ u ∈ col, 0 ≤ rowB u) :
    ∑ w ∈ row ∪ col, lenW w ≤ ∑ u ∈ col, (colB u + rowB u) := by
  rw [Finset.sum_union hd, Finset.sum_add_distrib]
  have h1 : ∑ v ∈ row, lenW v ≤ ∑ v ∈ row, rowB (back v) := Finset.sum_le_sum hrow
  have h2 : ∑ u ∈ row.image back, rowB u = ∑ v ∈ row, rowB (back v) := by
    apply Finset.sum_image
    intro x hx y hy hxy
    exact hinj hx hy hxy
  have h3 : ∑ u ∈ row.image back, rowB u ≤ ∑ u ∈ col, rowB u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact hback v hv
    · intro u hu _
      exact hnn u hu
  have h4 : ∑ u ∈ col, lenW u ≤ ∑ u ∈ col, colB u := Finset.sum_le_sum hcol
  linarith

theorem lenCol_le (e' j n m : ℕ) (vd h0 : ℚ) (hvd : 0 ≤ vd) (hj : j ≤ n * m) :
    (e' : ℚ) + (j : ℚ) * ((e' : ℚ) + vd) + 2 * vd + h0 ≤
      (e' : ℚ) + (n : ℚ) * (m : ℚ) * ((e' : ℚ) + vd) + 2 * vd + h0 := by
  have hj' : (j : ℚ) ≤ (n : ℚ) * (m : ℚ) := by exact_mod_cast hj
  have hpos : 0 ≤ (e' : ℚ) + vd := add_nonneg (Nat.cast_nonneg _) hvd
  have := mul_le_mul_of_nonneg_right hj' hpos
  linarith

theorem cloud_sign (sgn : ℤ) (C : Finset ℤ) (s : ℚ) (hs : 0 < s)
    (h : ∀ a ∈ C, s ≤ ((sgn * a : ℤ) : ℚ)) : ∀ a ∈ C, 0 < sgn * a := by
  intro a ha
  have h2 : (0 : ℚ) < ((sgn * a : ℤ) : ℚ) := lt_of_lt_of_le hs (h a ha)
  exact_mod_cast h2

end Arith

section AtPlace

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (L : LocTheory)
  (nbr : Br.NBr N) (i : N.Loc) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)
  (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))

theorem jW_le (hBK : BlochKatoDim (Br.PD L nbr i w hw) (Br.LL nbr i w hw))
    (hS : Splits (Br.LL nbr i w hw) (K := Br.Kw nbr i w hw) (Qp := ℚ_[N.l i]))
    (hdeg : Br.DegW nbr i w hw)
    (hc : ∀ x, Continuous fun g => matRep (Br.loc nbr i w hw (WpO N i ρ π)) g x)
    (hcr : IsCrys (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))))
    (h0 : H0V (matRep (Br.loc nbr i w hw (WpO N i ρ π))) = ⊥)
    (hF : FilCount (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π)))) (m : ℕ)
    (hJ : ∀ τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw, ∃ C Lo : Finset ℤ,
      (∀ a ∈ C, 0 < a) ∧ Lo.card ≤ m ∧
      ∀ a, multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ a =
        if a ∈ C ∪ Lo then 1 else 0) :
    Br.jW L nbr i w hw ρ π ≤ locDeg H.E w * m := by
  have h := rank_le_col (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π)))
    hBK hS hc hcr h0 hF m hJ
  unfold Br.DegW at hdeg
  unfold Br.jW
  first
  | (rw [← hdeg]; exact h)
  | (rw [hdeg] at h; exact h)
  | (simpa [hdeg] using h)
  | exact (0 : Nat)

theorem rank_second_lattice_le (hBK : BlochKatoDim (Br.PD L nbr i w hw) (Br.LL nbr i w hw))
    (hS : Splits (Br.LL nbr i w hw) (K := Br.Kw nbr i w hw) (Qp := ℚ_[N.l i]))
    (hdeg : Br.DegW nbr i w hw)
    (hc : ∀ x, Continuous fun g => matRep (Br.loc nbr i w hw (T2O N i ρ π)) g x)
    (hcr : IsCrys (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π))))
    (h0 : H0V (matRep (Br.loc nbr i w hw (T2O N i ρ π))) = ⊥)
    (hF : FilCount (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π)))) (m : ℕ)
    (hdual : ∀ (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) (a : ℤ),
      multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π))) τ a =
        multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ (-a - 1))
    (hJ : ∀ τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw, ∃ C Lo : Finset ℤ,
      (∀ a ∈ C, a < 0) ∧ Lo.card ≤ m ∧
      ∀ a, multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ a =
        if a ∈ C ∪ Lo then 1 else 0) :
    finrank (Br.LL nbr i w hw)
      (FiniteCohomology (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π)))) ≤ locDeg H.E w * m := by
  have hJ' : ∀ τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw, ∃ C Lo : Finset ℤ,
      (∀ a ∈ C, a < 0) ∧ Lo.card ≤ m ∧
      ∀ a, multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π))) τ a =
        if -a - 1 ∈ C ∪ Lo then 1 else 0 := by
    intro τ
    obtain ⟨C, Lo, hC, hLo, hmW⟩ := hJ τ
    exact ⟨C, Lo, hC, hLo, fun a => (hdual τ a).trans (hmW (-a - 1))⟩
  have h := rank_le_row (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π)))
    hBK hS hc hcr h0 hF m hJ'
  unfold Br.DegW at hdeg
  first
  | (rw [← hdeg]; exact h)
  | (rw [hdeg] at h; exact h)
  | (simpa [hdeg] using h)
  | exact absurd hdeg (0 : Nat)

theorem rowAt_le (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (e' n m c0 : ℕ)
    (hLift : LiftAt (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw)
      (fun x : N.X i => ⇑(Br.loc nbr i w hw (rDuO N i r x))) e')
    (hrk : finrank (Br.LL nbr i w hw)
      (FiniteCohomology (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π)))) ≤ n * m)
    (lenH0 : ℕ∞)
    (hH1f : lenModPow (Br.PD L nbr i w hw) (Br.locLat nbr i w hw (T2O N i ρ π)) e' ≤
      (e' : ℕ∞) * (finrank (Br.LL nbr i w hw)
        (FiniteCohomology (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π)))) : ℕ∞) *
        lenOl (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw) + lenH0)
    (hH0 : lenH0 ≤ (R.r : ℕ∞) * (c0 : ℕ∞) * lenOl (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw))
    (hfin : lenOl (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw) ≠ ⊤) :
    RowAt (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw)
      (fun x : N.X i => ⇑(Br.loc nbr i w hw (rDuO N i r x))) ⇑(Br.loc nbr i w hw (T2O N i ρ π))
      ((n : ℚ) * (m : ℚ) * (e' : ℚ) + (R.r : ℚ) * (c0 : ℚ)) := by
  refine rowAt_of_lift (Br.PD L nbr i w hw) _ _ (Br.locLat nbr i w hw (T2O N i ρ π)) ?_ e' hLift _ n m R.r c0
    lenH0 hH1f hrk hH0 hfin
  intro v
  first
  | exact mem_stdG_iff _ v
  | (unfold Br.locLat; exact mem_stdG_iff _ v)
  | (simp only [Br.locLat]; exact mem_stdG_iff _ v)

theorem locDeg_conj {u : HeightOneSpectrum (𝓞 H.E)} (huw : IsConjPl H u w) :
    locDeg H.E w = locDeg H.E u := by
  first
  | exact ef_conj _ u w huw
  | (unfold locDeg; exact ef_conj _ u w huw)

theorem rowAt_conj_le (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (e' m c0 : ℕ)
    {u : HeightOneSpectrum (𝓞 H.E)} (huw : IsConjPl H u w)
    (hBK : BlochKatoDim (Br.PD L nbr i w hw) (Br.LL nbr i w hw))
    (hS : Splits (Br.LL nbr i w hw) (K := Br.Kw nbr i w hw) (Qp := ℚ_[N.l i]))
    (hdeg : Br.DegW nbr i w hw)
    (hc : ∀ x, Continuous fun g => matRep (Br.loc nbr i w hw (T2O N i ρ π)) g x)
    (hcr : IsCrys (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π))))
    (h0 : H0V (matRep (Br.loc nbr i w hw (T2O N i ρ π))) = ⊥)
    (hF : FilCount (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π))))
    (hdual : ∀ (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) (a : ℤ),
      multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π))) τ a =
        multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ (-a - 1))
    (hJ : ∀ τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw, ∃ C Lo : Finset ℤ,
      (∀ a ∈ C, a < 0) ∧ Lo.card ≤ m ∧
      ∀ a, multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ a =
        if a ∈ C ∪ Lo then 1 else 0)
    (hLift : LiftAt (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw)
      (fun x : N.X i => ⇑(Br.loc nbr i w hw (rDuO N i r x))) e')
    (lenH0 : ℕ∞)
    (hH1f : lenModPow (Br.PD L nbr i w hw) (Br.locLat nbr i w hw (T2O N i ρ π)) e' ≤
      (e' : ℕ∞) * (finrank (Br.LL nbr i w hw)
        (FiniteCohomology (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (T2O N i ρ π)))) : ℕ∞) *
        lenOl (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw) + lenH0)
    (hH0 : lenH0 ≤ (R.r : ℕ∞) * (c0 : ℕ∞) * lenOl (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw))
    (hfin : lenOl (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw) ≠ ⊤) :
    RowAt (Br.PD L nbr i w hw) (O := Br.OLL nbr i w hw)
      (fun x : N.X i => ⇑(Br.loc nbr i w hw (rDuO N i r x))) ⇑(Br.loc nbr i w hw (T2O N i ρ π))
      ((locDeg H.E u : ℚ) * (m : ℚ) * (e' : ℚ) + (R.r : ℚ) * (c0 : ℚ)) := by
  have hrk := rank_second_lattice_le L nbr i ρ π w hw hBK hS hdeg hc hcr h0 hF m hdual hJ
  rw [locDeg_conj w huw] at hrk
  exact rowAt_le L nbr i ρ π w hw r e' (locDeg H.E u) m c0 hLift hrk lenH0 hH1f hH0 hfin

end AtPlace

section Joint

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Classical

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

def backPl (v : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.E) :=
  if h : ∃ u ∈ dc.col, IsConjPl D.host u v then h.choose else v

def lenRowSplit (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.E)) : ℚ := rowNum e' c0 (backPl i dc v)

theorem backPl_eq {u v : HeightOneSpectrum (𝓞 D.host.E)} (hu : u ∈ dc.col)
    (huv : IsConjPl D.host u v) : backPl i dc v = u := by
  have hex : ∃ u ∈ dc.col, IsConjPl D.host u v := ⟨u, hu, huv⟩
  unfold backPl
  rw [dif_pos hex]
  obtain ⟨_, hc⟩ := hex.choose_spec
  exact conjPl_unique' _ _ _ _ hc huv

theorem lenRowSplit_eq (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    {u v : HeightOneSpectrum (𝓞 D.host.E)} (hu : u ∈ dc.col) (huv : IsConjPl D.host u v) :
    lenRowSplit i dc e' c0 v = rowNum e' c0 u := by
  unfold lenRowSplit
  rw [backPl_eq i dc hu huv]

theorem vdel_nonneg : 0 ≤ D.nd.vdel i := by
  unfold Formalism.BasicNotions.NData.vdel
  apply Finset.sum_nonneg
  intro k _
  positivity

theorem sum_lenW_split (hdecl : RowsAreConj i dc) (e' : ℕ)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (hJ : ∀ u (hu : u ∈ dc.col), Br.jW D.loc D.nbr i u ((dc.cover u).1 (Or.inr hu)) ρ π ≤
      locDeg D.host.E u * D.R.m) :
    ∑ w ∈ dc.row ∪ dc.col,
        Formalism.MainNotions.TruncatedSeriesCountingIdentities.lenW i ρ π dc (lenRowSplit i dc e' c0) (fun _ => e') w ≤
      ∑ u ∈ dc.col, ((e' : ℚ) + (locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * ((e' : ℚ) + D.nd.vdel i) +
        2 * D.nd.vdel i + Br.h0W i u ρ π +
        (locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * (e' : ℚ) + (D.R.r : ℚ) * (c0 u : ℚ)) := by
  have hback : ∀ v ∈ dc.row, backPl i dc v ∈ dc.col := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := (hdecl v).mp hv
    rw [backPl_eq i dc hu huv]
    exact hu
  have hinj : Set.InjOn (backPl i dc) dc.row := by
    intro v1 hv1 v2 hv2 heq
    obtain ⟨u1, hu1, huv1⟩ := (hdecl v1).mp hv1
    obtain ⟨u2, hu2, huv2⟩ := (hdecl v2).mp hv2
    rw [backPl_eq i dc hu1 huv1, backPl_eq i dc hu2 huv2] at heq
    subst heq
    exact conjPl_unique _ _ _ _ huv1 huv2
  have hcol : ∀ u ∈ dc.col,
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.lenW i ρ π dc (lenRowSplit i dc e' c0) (fun _ => e') u ≤
        (e' : ℚ) + (locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * ((e' : ℚ) + D.nd.vdel i) +
          2 * D.nd.vdel i + Br.h0W i u ρ π := by
    intro u hu
    unfold Formalism.MainNotions.TruncatedSeriesCountingIdentities.lenW
    rw [dif_pos hu]
    unfold Br.lenCol
    first
    | exact lenCol_le e' _ _ _ _ _ (vdel_nonneg i) (hJ u hu)
    | exact (0 : Nat)
  have hrow : ∀ v ∈ dc.row,
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.lenW i ρ π dc (lenRowSplit i dc e' c0) (fun _ => e') v ≤
        rowNum e' c0 (backPl i dc v) := by
    intro v hv
    have hnc : v ∉ dc.col := Finset.disjoint_left.mp dc.disj hv
    unfold Formalism.MainNotions.TruncatedSeriesCountingIdentities.lenW
    rw [dif_neg hnc]
    exact le_refl _
  have hnn : ∀ u ∈ dc.col, 0 ≤ rowNum e' c0 u := by
    intro u _
    unfold rowNum
    positivity
  refine le_trans (sum_lenW_le dc.row dc.col dc.disj
    (fun w => Formalism.MainNotions.TruncatedSeriesCountingIdentities.lenW i ρ π dc (lenRowSplit i dc e' c0) (fun _ => e') w)
    (fun u => (e' : ℚ) + (locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * ((e' : ℚ) + D.nd.vdel i) +
      2 * D.nd.vdel i + Br.h0W i u ρ π)
    (rowNum e' c0) (backPl i dc) hback hinj hcol hrow hnn)
    (le_of_eq (Finset.sum_congr rfl (fun u _ => ?_)))
  beta_reduce
  unfold rowNum
  ring

theorem length_bound_of_theorem (hdecl : RowsAreConj i dc) (e' : ℕ)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hJ : ∀ u (hu : u ∈ dc.col), Br.jW D.loc D.nbr i u ((dc.cover u).1 (Or.inr hu)) ρ π ≤
      locDeg D.host.E u * D.R.m)
    (hthm : Formalism.MainNotions.TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc (lenRowSplit i dc e' c0) (fun _ => e') cB)
    (hg0 : D.nd.l i ≠ D.host.g 0) (hg1 : D.nd.l i ≠ D.host.g 1) (hπ : π ∈ D.nd.Z i)
    (hs : Br.sFin D.loc D.nbr i ρ π)
    (hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) :
    D.nd.vcc i π ≤ boundSplit i ρ π dc e' c0 cB := by
  have h1 := hthm hg0 hg1 hπ hs hsha
  have h2 := sum_lenW_split i ρ π dc hdecl e' c0 hJ
  unfold boundSplit
  linarith

theorem admissible_length_of_local (hdecl : RowsAreConj i dc) (e' : ℕ)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (hrow : ∀ u ∈ dc.col, ∀ (w : HeightOneSpectrum (𝓞 D.host.E))
      (hw : w ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host u w →
      ∀ C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw, C.IsGood →
      RowAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL))
        (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)))
        ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) (rowNum e' c0 u)) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowSplit i dc e' c0) := by
  intro w hw hwr C hC
  obtain ⟨u, hu, huw⟩ := (hdecl w).mp hwr
  rw [lenRowSplit_eq i dc e' c0 hu huw]
  exact hrow u hu w hw huw C hC

theorem length_bound_of_norm_bound (hdecl : RowsAreConj i dc) (e' : ℕ)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hN5 : Formalism.MainNotions.LargeLevelLemmas.GlobalIndexTheoremPlaces i r ρ π dc (lenRowSplit i dc e' c0) (fun _ => e') cB)
    (hJ : ∀ u (hu : u ∈ dc.col), Br.jW D.loc D.nbr i u ((dc.cover u).1 (Or.inr hu)) ρ π ≤
      locDeg D.host.E u * D.R.m)
    (hrow : ∀ u ∈ dc.col, ∀ (w : HeightOneSpectrum (𝓞 D.host.E))
      (hw : w ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host u w →
      ∀ C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw, C.IsGood →
      RowAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL))
        (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)))
        ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) (rowNum e' c0 u))
    (hlift : Formalism.MainNotions.TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc (fun _ => e')) (hTB : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admTB i r π cB)
    (hg0 : D.nd.l i ≠ D.host.g 0) (hg1 : D.nd.l i ≠ D.host.g 1) (hπ : π ∈ D.nd.Z i)
    (hs : Br.sFin D.loc D.nbr i ρ π)
    (hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) :
    D.nd.vcc i π ≤ boundSplit i ρ π dc e' c0 cB := by
  have hROW := admissible_length_of_local i r ρ π dc hdecl e' c0 hrow
  exact length_bound_of_theorem i ρ π dc hdecl e' c0 cB hJ (hN5 hROW hlift hTB) hg0 hg1 hπ hs hsha

end Joint

section Final

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Classical
open Formalism.MainNotions.TruncatedSeriesCountingIdentities (Decl CoefExt locC)

section PDgen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem lenOl_ne_top {O : Type} [CommRing O] [IsDedekindDomain O]
    (h : ((PD.p : ℕ) : O) ≠ 0) : lenOl PD (O := O) ≠ ⊤ := by
  rw [lenOl, Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  rwa [mem_nonZeroDivisors_iff_ne_zero]

theorem lenOl_OL_ne_top {l : ℕ} [Fact l.Prime] (hp : PD.p = l) (LL : FinExt l) :
    lenOl PD (O := ↥(OL LL)) ≠ ⊤ := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  apply lenOl_ne_top
  rw [hp]
  intro h
  have h2 := congrArg (Subtype.val : ↥(OL LL) → ↥LL.1) h
  have h3 : ((l : ℕ) : ↥LL.1) = 0 := by simpa using h2
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h3)

end PDgen

theorem multW_of_shape (k m t : ℕ) (sgn : ℤ) (Cl Lo : Finset ℤ) (μ μW : ℤ → ℤ) (μc : ℕ → ℤ → ℤ)
    (hS : ShapeJumps k m t sgn Cl Lo μ)
    (hadd : ∀ a, μ a = μW a + ∑ c ∈ Finset.Icc 1 t, μc c a)
    (hc : ∀ c ∈ Finset.Icc 1 t, ∀ a, μc c a = if a = (c : ℤ) - 1 then 1 else 0) (a : ℤ) :
    μW a = if a ∈ Cl ∪ Lo then 1 else 0 := by
  unfold ShapeJumps at hS
  obtain ⟨-, -, -, -, hdC, hdL, -, -, hμ⟩ := hS
  have hsum : ∑ c ∈ Finset.Icc 1 t, μc c a =
      if a ∈ Finset.Ico (0 : ℤ) (t : ℤ) then 1 else 0 := by
    rw [Finset.sum_congr rfl (fun c hc' => hc c hc' a)]
    by_cases ha : a ∈ Finset.Ico (0 : ℤ) (t : ℤ)
    · rw [if_pos ha]
      rw [Finset.mem_Ico] at ha
      have e : (((a + 1).toNat : ℕ) : ℤ) = a + 1 := Int.toNat_of_nonneg (by omega)
      have hmem : (a + 1).toNat ∈ Finset.Icc 1 t := by
        rw [Finset.mem_Icc]
        omega
      have hzero : ∀ c ∈ Finset.Icc 1 t, c ≠ (a + 1).toNat →
          (if a = (c : ℤ) - 1 then (1 : ℤ) else 0) = 0 := by
        intro c _ hne
        have hx : ¬ (a = (c : ℤ) - 1) := by omega
        rw [if_neg hx]
      rw [Finset.sum_eq_single_of_mem (a + 1).toNat hmem hzero]
      have hx : a = (((a + 1).toNat : ℕ) : ℤ) - 1 := by omega
      rw [if_pos hx]
    · rw [if_neg ha]
      rw [Finset.mem_Ico] at ha
      apply Finset.sum_eq_zero
      intro c hc'
      rw [Finset.mem_Icc] at hc'
      have hx : ¬ (a = (c : ℤ) - 1) := by omega
      rw [if_neg hx]
  have h1 := hadd a
  have h2 := hμ a
  rw [hsum] at h1
  by_cases hCL : a ∈ Cl ∪ Lo
  · have hI : a ∉ Finset.Ico (0 : ℤ) (t : ℤ) := by
      rcases Finset.mem_union.mp hCL with h | h
      · exact Finset.disjoint_left.mp hdC h
      · exact Finset.disjoint_left.mp hdL h
    rw [if_pos hCL]
    rw [if_neg hI] at h1
    rw [if_pos (Finset.mem_union_left _ hCL)] at h2
    omega
  · rw [if_neg hCL]
    by_cases hI : a ∈ Finset.Ico (0 : ℤ) (t : ℤ)
    · rw [if_pos hI] at h1
      rw [if_pos (Finset.mem_union_right _ hI)] at h2
      omega
    · have hn : a ∉ Cl ∪ Lo ∪ Finset.Ico (0 : ℤ) (t : ℤ) :=
        fun h => (Finset.mem_union.mp h).elim hCL hI
      rw [if_neg hI] at h1
      rw [if_neg hn] at h2
      omega

variable {D : D7}

section AtW

variable {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locC_self {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    locC (CoefExt.self i w hw) M = Br.loc D.nbr i w hw M := by
  first
  | rfl
  | (ext g a b; rfl)
  | (unfold locC; rfl)
  | (unfold locC CoefExt.self; exact (0 : Nat))

variable (C : CoefExt D i w hw)

def incO : Br.OLL D.nbr i w hw →+* ↥(OL C.LL) :=
  (C.inc.comp (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw))).codRestrict (OL C.LL)
    (fun x => (x.2 : IsIntegral ℤ_[D.nd.l i] (x : Br.LL D.nbr i w hw)).map
      ((IntermediateField.inclusion C.le).restrictScalars ℤ_[D.nd.l i]))

theorem exists_std {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    ∃ L2 : Lattice (O := ↥(OL C.LL)) (matRep (locC C M)), IsStd C L2 := by
  have hM : mapM (algebraMap ↥(OL C.LL) ↥C.LL.1)
      (mapM (incO C) (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)))) = locC C M := by
    ext g a b
    rfl
  rw [← hM]
  exact ⟨stdLatG Subtype.val_injective _, fun v => mem_stdG_iff _ v⟩

end AtW

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : Decl D i)

theorem multW_eq (hπ : π ∈ D.nd.Z i) (hg0 : D.nd.l i ≠ D.host.g 0) (hg1 : D.nd.l i ≠ D.host.g 1)
    (hBl : ambBlock i r ρ π) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (sgn : ℤ) (Cl Lo : Finset ℤ)
    (hs : ShapeJumps D.R.k D.R.m D.R.t sgn Cl Lo
      (multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rTwO D.nd i r π))) τ)) (a : ℤ) :
    multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π))) τ a =
      if a ∈ Cl ∪ Lo then 1 else 0 := by
  obtain ⟨hadd, hc⟩ := hBl hπ hg0 hg1 w hw C τ
  exact multW_of_shape D.R.k D.R.m D.R.t sgn Cl Lo _ _ _ hs hadd hc a

variable {ep : Bool}

set_option maxHeartbeats 1600000 in

theorem jump_bound_of_admitted (hL : hypL i) (hD : hypDecl i dc ep) (hπ : π ∈ D.nd.Z i) (hG2 : admG2 i r ep)
    (hBl : ambBlock i r ρ π) (h56 : ColumnH0Vanishing i ρ π dc) (hBK : admBK i) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hW : ambW i ρ π dc) (hFil : ambFil i r ρ π dc) (hCont : ambCont i r ρ π) :
    JumpConditions i ρ π dc := by
  intro u hu
  have hw := (dc.cover u).1 (Or.inr hu)
  have hg0 := hL.2.2.2.1
  have hg1 := hL.2.2.2.2
  have hU : PlTypeUe i u hw ep := (hD.1 u hw).1 hu
  have h := rank_le_col (Br.PD D.loc D.nbr i u hw)
    (matRep (locC (CoefExt.self i u hw) (WpO D.nd i ρ π)))
    (hBK.1 u hw (CoefExt.self i u hw)).2.1 (LargeLevelLemmas.splits_coef (CoefExt.self i u hw))
    ((hCont u hw (CoefExt.self i u hw)).2 hπ).1 (hW hπ u hw hu (CoefExt.self i u hw))
    (h56 hπ u hw hu (CoefExt.self i u hw)) ((hFil.2 hπ).1 u hw hu (CoefExt.self i u hw)) D.R.m
    (fun τ => by
      obtain ⟨Cl, Lo, hsh⟩ := (hG2 hg0 hg1 u hw (CoefExt.self i u hw)).2.2 τ
      have hs := hsh π
      have hE : EmbU (CoefExt.self i u hw) ep τ := ⟨τ, hU τ, fun x => rfl⟩
      rw [if_pos hE] at hs
      obtain ⟨s, S, η, hs0, -, -, hcl, -⟩ := hs.1
      refine ⟨Cl, Lo, fun a ha => ?_, le_of_eq hs.2.2.1,
        multW_eq i r ρ π hπ hg0 hg1 hBl u hw _ τ 1 Cl Lo hs⟩
      have := cloud_sign 1 Cl s hs0 (fun a ha => (hcl a ha).1) a ha
      simpa using this)
  rw [locC_self] at h
  have hdeg : finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i u hw) = locDeg D.host.E u := (hTie u hw).2.2
  rw [hdeg] at h
  exact h

set_option maxHeartbeats 1600000 in

theorem length_bound_of_admitted (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hL : hypL i)
    (hD : hypDecl i dc ep) (hπ : π ∈ D.nd.Z i) (hG2 : admG2 i r ep) (hBl : ambBlock i r ρ π)
    (hBK : admBK i) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (hLift : LiftExponentDualPlaces i r dc e') (hH0 : H0ColumnLengthBound i ρ π dc c0)
    (hDual : ambDual i ρ π dc) (hT2 : ambT2 i ρ π dc) (hFil : ambFil i r ρ π dc)
    (hH1f : H1fFiniteRankTorsion i ρ π dc) (hCont : ambCont i r ρ π) (hTD : ambTypeD i ep) :
    ColengthRowPlaceBound i r ρ π dc e' c0 := by
  intro u hu w hw huw C hC
  have hwr : w ∈ dc.row := (hD.2 w).2 ⟨u, hu, huw⟩
  have hu' := (dc.cover u).1 (Or.inr hu)
  have hg0 := hL.2.2.2.1
  have hg1 := hL.2.2.2.2
  have hU : PlTypeUe i u hu' ep := (hD.1 u hu').1 hu
  have hrk := rank_le_row (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π)))
    (hBK.1 w hw C).2.1 (LargeLevelLemmas.splits_coef C) ((hCont w hw C).2 hπ).2 (hT2 hπ w hw hwr C).1
    (hT2 hπ w hw hwr C).2.2 ((hFil.2 hπ).2 w hw hwr C) D.R.m
    (fun τ => by
      obtain ⟨Cl, Lo, hsh⟩ := (hG2 hg0 hg1 w hw C).2.2 τ
      have hs := hsh π
      have hE : ¬ EmbU C ep τ := fun ⟨τ₀, h1, _⟩ => hTD u hu' hU w hw huw τ₀ h1
      rw [if_neg hE] at hs
      obtain ⟨s, S, η, hs0, -, -, hcl, -⟩ := hs.1
      refine ⟨Cl, Lo, fun a ha => ?_, le_of_eq hs.2.2.1, fun a => ?_⟩
      · have := cloud_sign (-1) Cl s hs0 (fun a ha => (hcl a ha).1) a ha
        omega
      · rw [hDual hπ w hw hwr C τ a]
        exact multW_eq i r ρ π hπ hg0 hg1 hBl w hw C τ (-1) Cl Lo hs (-a - 1))
  have hdeg : finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = locDeg D.host.E w := (hTie w hw).2.2
  rw [hdeg, locDeg_conj w huw] at hrk
  obtain ⟨L2, hL2⟩ := exists_std C (T2O D.nd i ρ π)
  exact rowAt_of_lift (Br.PD D.loc D.nbr i w hw) _ (locC C (T2O D.nd i ρ π)) L2 hL2 e'
    (hLift w hw hwr C hC) _ (locDeg D.host.E u) D.R.m D.R.r (c0 u) (lenInvD L2)
    (hH1f hπ w hw hwr C L2 hL2 e') hrk (hH0 hπ u hu w hw huw C hC L2 hL2)
    (lenOl_OL_ne_top _ (Br.PD_p D.loc D.nbr i w hw) C.LL)

theorem shaBound_of_globalIndex_of_colength_of_lift (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) (hL : hypL i)
    (hD : hypDecl i dc ep) (hπ : π ∈ D.nd.Z i)
    (hN5 : LargeLevelLemmas.GlobalIndexTheoremPlaces i r ρ π dc (lenRowSplit i dc e' c0) (fun _ => e') cB)
    (hTB : TruncatedSeriesCountingIdentities.admTB i r π cB) (hJ : JumpConditions i ρ π dc) (hRow : ColengthRowPlaceBound i r ρ π dc e' c0)
    (hLift : LiftExponentColumn i r dc e') : ShaBoundTheoremB i ρ π dc e' c0 cB := by
  intro hs hsha _
  obtain ⟨-, -, -, hg0, hg1⟩ := hL
  obtain ⟨-, hdecl⟩ := hD
  exact length_bound_of_norm_bound i r ρ π dc hdecl e' c0 cB hN5 hJ hRow hLift hTB hg0 hg1 hπ hs hsha

theorem jump_and_length_of_admitted (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hA : admitted i r ρ π dc ep e' c0 cB) (hL : hypL i) (hD : hypDecl i dc ep) (hπ : π ∈ D.nd.Z i) :
    JumpConditions i ρ π dc ∧ ColengthRowPlaceBound i r ρ π dc e' c0 := by
  obtain ⟨-, hG2, -, -, -, -, -, h56, -, -, -, hBK, -, hLiftRow, hH0, -, -, -, -, -, -, hTie, -, -, -,
    -, -, hBl, hDual, hT2, hW, hFil, hH1f, -, hCont, hTD⟩ := hA
  exact ⟨jump_bound_of_admitted i r ρ π dc hL hD hπ hG2 hBl h56 hBK hTie hW hFil hCont,
    length_bound_of_admitted i r ρ π dc e' c0 hL hD hπ hG2 hBl hBK hTie hLiftRow hH0 hDual hT2 hFil hH1f hCont hTD⟩

theorem bound_of_norm_estimate (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hA : admitted i r ρ π dc ep e' c0 cB)
    (hN5 : LargeLevelLemmas.GlobalIndexTheoremPlaces i r ρ π dc (lenRowSplit i dc e' c0) (fun _ => e') cB)
    (hTB : TruncatedSeriesCountingIdentities.admTB i r π cB) : aux₃ i r ρ π dc ep e' c0 cB := by
  intro hL hD hπ
  obtain ⟨hJ, hRow⟩ := jump_and_length_of_admitted i r ρ π dc e' c0 cB hA hL hD hπ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hLC, -⟩ := hA
  exact ⟨hJ, hRow, shaBound_of_globalIndex_of_colength_of_lift i r ρ π dc e' c0 cB hL hD hπ hN5 hTB hJ hRow hLC⟩

end Final

end Formalism.MainNotions.EmbeddingTypes
