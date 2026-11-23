import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootEqOne
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem graph_ext {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [T2Space Y]
    (I : Subgroup G) (σ : G) (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤)
    (hU : ∀ n : ℕ, 0 < n → ∃ U : Subgroup G, U.Normal ∧ IsOpen (U : Set G) ∧ I ≤ U ∧
      ∀ k : ℤ, σ ^ k ∈ U → (n : ℤ) ∣ k) (y : Y) :
    ∃ f : G →* Y, Continuous f ∧ (∀ g ∈ I, f g = 1) ∧ f σ = y := by
  set Δ : Subgroup (G × Y) := I.prod ⊥ ⊔ Subgroup.zpowers (σ, y) with hΔ
  set Γ : Subgroup (G × Y) := Δ.topologicalClosure with hΓ
  have hΓc : IsClosed (Γ : Set (G × Y)) := Δ.isClosed_topologicalClosure
  have hIΓ : ∀ g ∈ I, (g, (1 : Y)) ∈ Γ := fun g hg =>
    Δ.le_topologicalClosure ((le_sup_left : I.prod ⊥ ≤ Δ) ⟨hg, rfl⟩)
  have hσΓ : (σ, y) ∈ Γ :=
    Δ.le_topologicalClosure ((le_sup_right : Subgroup.zpowers (σ, y) ≤ Δ) (Subgroup.mem_zpowers _))
  have hsurj : Γ.map (MonoidHom.fst G Y) = ⊤ := by
    rw [eq_top_iff, ← hd]
    refine Subgroup.topologicalClosure_minimal _ (sup_le (fun g hg => ⟨_, hIΓ g hg, rfl⟩) ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨_, hσΓ, rfl⟩
    · exact isClosedMap_fst_of_compactSpace _ hΓc
  have hker : ∀ z : Y, ((1 : G), z) ∈ Γ → z = 1 := by
    intro z hz
    by_contra hne
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := Y) (U := {z}ᶜ)
      isOpen_compl_singleton (fun h => hne (Set.mem_singleton_iff.1 h).symm)
    haveI : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨U, hUn, hUo, hIU, hUk⟩ := hU N.toSubgroup.index (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
    have hle : Γ ≤ U.prod N.toSubgroup ⊔ Subgroup.zpowers (σ, y) := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le_sup_right (Subgroup.prod_mono hIU bot_le) _) ?_
      refine Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_left ?_)
      exact hUo.prod N.isOpen
    have h1 := hle hz
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at h1
    obtain ⟨⟨u, w⟩, ⟨hu, hw⟩, _, ⟨k, rfl⟩, h⟩ := h1
    have e1 : u * σ ^ k = 1 := congrArg Prod.fst h
    have e2 : w * y ^ k = z := congrArg Prod.snd h
    have h2 : σ ^ k ∈ U := by
      rw [← (inv_eq_of_mul_eq_one_right e1)]
      exact U.inv_mem hu
    obtain ⟨c, rfl⟩ := hUk k h2
    have h3 : z ∈ N.toSubgroup := by
      rw [← e2, zpow_mul, zpow_natCast]
      exact N.toSubgroup.mul_mem hw (N.toSubgroup.zpow_mem (N.toSubgroup.pow_index_mem y) c)
    exact hN h3 rfl
  obtain ⟨f, hf⟩ := Subgroup.exists_eq_graph (G := Γ) (by
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
      obtain rfl : a = a' := h
      have := hker (b⁻¹ * b') (by simpa using Γ.mul_mem (Γ.inv_mem hab) hab')
      obtain rfl : b = b' := inv_mul_eq_one.1 this
      rfl
    · intro g
      obtain ⟨p, hp, rfl⟩ : g ∈ Γ.map (MonoidHom.fst G Y) := by rw [hsurj]; trivial
      exact ⟨⟨p, hp⟩, rfl⟩)
  have hmem : ∀ a b, (a, b) ∈ Γ ↔ f a = b := fun a b => by rw [hf]; rfl
  refine ⟨f, continuous_iff_isClosed.2 fun C hC => ?_, fun g hg => (hmem _ _).1 (hIΓ g hg), (hmem _ _).1 hσΓ⟩
  have : f ⁻¹' C = Prod.fst '' ((Γ : Set (G × Y)) ∩ Prod.snd ⁻¹' C) := by
    ext g
    constructor
    · intro hg
      exact ⟨(g, f g), ⟨(hmem _ _).2 rfl, hg⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨h1, h2⟩, rfl⟩
      show f a ∈ C
      rw [(hmem _ _).1 h1]
      exact h2
  rw [this]
  exact isClosedMap_fst_of_compactSpace _ (hΓc.inter (hC.preimage continuous_snd))

private theorem root_eq_one {v : ℕ} [Fact v.Prime] {m : ℕ} (hm : ¬ v ∣ m) {η : Om v} (hη : η ^ m = 1)
    (h : ‖η - 1‖ < 1) : η = 1 :=
  _root_.UpperTheory.Reformulated.B.Qe14.root_eq_one hm hη h

private theorem exists_level {v : ℕ} [Fact v.Prime] (σ : GQ v) (hσ : IsFrob σ) (n : ℕ) (hn : 0 < n) :
    ∃ U : Subgroup (GQ v), U.Normal ∧ IsOpen (U : Set (GQ v)) ∧ Iq v ≤ U ∧ ∀ k : ℤ, σ ^ k ∈ U → (n : ℤ) ∣ k := by
  have hv : v.Prime := Fact.out
  have h1 : 1 < v ^ n := Nat.one_lt_pow hn.ne' hv.one_lt
  obtain ⟨m, hm⟩ : ∃ m, m = v ^ n - 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hvm : ¬ v ∣ m := by
    intro h
    have h2 : v ∣ v ^ n := dvd_pow_self v hn.ne'
    have e : v ^ n = m + 1 := by omega
    rw [e] at h2
    exact hv.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (m : Om v) := ⟨by exact_mod_cast hm0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om v) m
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0.ne'
  have hnorm : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 this
  have hg : ∀ g : GQ v, (g ζ) ^ m = 1 := fun g => by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hσζ : σ ζ = ζ ^ v := by
    have hz : ζ ^ v ≠ 0 := pow_ne_zero _ hζ0
    rw [← div_eq_one_iff_eq hz]
    refine root_eq_one hvm ?_ ?_
    · rw [div_pow, hg, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, div_one]
    · rw [div_sub_one hz, norm_div, norm_pow, hnorm, one_pow, div_one]
      exact hσ ζ hnorm.le
  have hpow : ∀ k : ℕ, (σ ^ k) ζ = ζ ^ v ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hσζ, ← pow_mul, ← pow_succ']
  refine ⟨MulAction.stabilizer (GQ v) ζ, ⟨fun g hgζ h => ?_⟩, stabilizer_isOpen_of_isIntegral ζ, fun g hgI => ?_,
    fun k hk => ?_⟩
  · have hgζ' : g ζ = ζ := hgζ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (hg h⁻¹)
    show h (g (h⁻¹ ζ)) = ζ
    rw [← hi, map_pow, hgζ', hi, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  · exact hgI ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm0, hvm, hζ.pow_eq_one⟩⟩
  · have hk' : σ ^ k.natAbs ∈ MulAction.stabilizer (GQ v) ζ := by
      rcases Int.natAbs_eq k with e | e
      · rwa [e, zpow_natCast] at hk
      · rwa [e, zpow_neg, zpow_natCast, inv_mem_iff] at hk
    have h2 : (σ ^ k.natAbs) ζ = ζ := hk'
    rw [hpow] at h2
    rw [Int.natCast_dvd]
    generalize k.natAbs = j at h2
    have hj : 0 < v ^ j := pow_pos hv.pos j
    have h3 : ζ ^ (v ^ j - 1) = 1 := by
      apply mul_right_cancel₀ hζ0
      rw [← pow_succ, Nat.sub_add_cancel hj, h2, one_mul]
    have h4 : v ^ n - 1 ∣ v ^ j - 1 := hm ▸ (hζ.pow_eq_one_iff_dvd _).1 h3
    have h5 := Nat.pow_sub_one_gcd_pow_sub_one v n j
    rw [Nat.gcd_eq_left h4] at h5
    have h6 : 0 < v ^ n.gcd j := pow_pos hv.pos _
    have h7 : v ^ n = v ^ n.gcd j := by omega
    exact Nat.gcd_eq_left_iff_dvd.1 (Nat.pow_right_injective hv.two_le h7).symm

theorem UpperTheory.V.Loc.frobFree :
    ∀ {v : ℕ} [Fact v.Prime] (σ : GQ v), IsFrob σ → ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [T2Space Y] (y : Y), ∃ f : GQ v →* Y, Continuous f ∧ (∀ g ∈ Iq v, f g = 1) ∧ f σ = y := by
  intro v _ σ hσ Y _ _ _ _ _ _ y
  exact graph_ext (Iq v) σ (frobDense σ hσ) (exists_level σ hσ) y
