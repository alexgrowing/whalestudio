import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChoiceFunction

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem pick {k D : Type} [Field k] (P : Set D) {p0 : D} (hp0 : p0 ∈ P) (W : Submodule k (D → k))
    (hW : ∀ f, f ∈ W ↔ ∀ p ∈ P, f p = 0) : ∀ (n : ℕ) (Y : Submodule k (D → k)) [FiniteDimensional k Y],
    finrank k Y ≤ n + finrank k (Y ⊓ W : Submodule k (D → k)) →
    ∃ u : Fin n → D, (∀ a, u a ∈ P) ∧ ∀ f ∈ Y, (∀ a, f (u a) = 0) → f ∈ W :=
  _root_.UpperTheory.Reformulated.B.InterpolationPointsOfFinrankBound.pick P hp0 W hW

private theorem cyc1 {D : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D]
    {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (J : Subgroup D) (hJ : IsClosed (J : Set D)) (e : D →* ℤ_[l]ˣ)
    (he : Continuous e) (N : Set D) (hN : IsOpen N) (hJN : ∀ g ∈ J, e g = 1 → g ∈ N) :
    ∃ u ∈ J, ∀ g ∈ J, ∃ m : ℕ, g⁻¹ * u ^ m ∈ N := by
  let C : ℕ → Set D := fun n => (J : Set D) ∩ Nᶜ ∩ {g | ‖(e g : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(n : ℤ))}
  have hC : ∀ n, IsClosed (C n) := fun n =>
    (hJ.inter hN.isClosed_compl).inter
      (isClosed_le ((Units.continuous_val.comp he).sub continuous_const).norm continuous_const)
  have hiff : ∀ (n : ℕ) (x : ℤ_[l]), ‖x - 1‖ ≤ (l : ℝ) ^ (-(n : ℤ)) ↔ PadicInt.toZModPow n x = 1 := by
    intro n x
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
  have hex : ∃ n, C n = ∅ := by
    by_contra hne
    push Not at hne
    have hanti : ∀ n, C (n + 1) ⊆ C n := fun n g hg => ⟨hg.1, le_trans (b := (l : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) hg.2
      (zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_le) (by push_cast; omega))⟩
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hanti hne
      (hC 0).isCompact hC
    rw [Set.mem_iInter] at hg
    refine (hg 0).1.2 (hJN g (hg 0).1.1 ?_)
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [(hiff n _).mp (hg n).2]
    simp
  obtain ⟨n, hn⟩ := hex
  let en : D →* (ZMod (l ^ n))ˣ := (Units.map (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toMonoidHom).comp e
  haveI : IsCyclic (ZMod (l ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow l Fact.out hl n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨⟨_, u, hu, rfl⟩, hgen⟩ := IsCyclic.exists_monoid_generator (α := J.map en)
  refine ⟨u, hu, fun g hg => ?_⟩
  obtain ⟨m, hm⟩ := hgen ⟨en g, g, hg, rfl⟩
  have hm' : en u ^ m = en g := congrArg Subtype.val hm
  refine ⟨m, ?_⟩
  by_contra hN'
  have : g⁻¹ * u ^ m ∈ C n := by
    refine ⟨⟨J.mul_mem (J.inv_mem hg) (J.pow_mem hu m), hN'⟩, (hiff n _).mpr ?_⟩
    have h1 : en (g⁻¹ * u ^ m) = 1 := by rw [map_mul, map_inv, map_pow, hm', inv_mul_cancel]
    exact congrArg Units.val h1
  rw [hn] at this
  exact this

private theorem exChar {B : Type} [CommGroup B] [Finite B] {l : ℕ} [Fact l.Prime] (hB : IsPGroup l B)
    (H : Subgroup B) (hH : H ≠ ⊤) :
    ∃ θ : B →* Multiplicative (ZMod l), (∀ x ∈ H, θ x = 1) ∧ ∃ x, θ x ≠ 1 := by
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  haveI : Nontrivial (B ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM.1
  haveI : IsSimpleGroup (B ⧸ M) := by
    refine ⟨fun N _ => ?_⟩
    have h1 : M ≤ N.comap (QuotientGroup.mk' M) := fun x hx => by
      rw [Subgroup.mem_comap, show QuotientGroup.mk' M x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact N.one_mem
    have h2 := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) N
    rcases hM.le_iff.mp h1 with h | h
    · right
      rw [← h2, h]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)
    · left
      rw [← h2, h, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hp : (Nat.card (B ⧸ M)).Prime := IsSimpleGroup.prime_card
  have hq : IsPGroup l (B ⧸ M) := hB.to_quotient M
  have hc : Nat.card (B ⧸ M) = l := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hq
    have : Nat.card (B ⧸ M) ∣ l := hp.dvd_of_dvd_pow (n := n) (by rw [hn])
    exact (Nat.prime_dvd_prime_iff_eq hp Fact.out).mp this
  let ε : (B ⧸ M) ≃* Multiplicative (ZMod l) := mulEquivOfPrimeCardEq hc (by simp)
  refine ⟨ε.toMonoidHom.comp (QuotientGroup.mk' M), fun x hx => ?_, ?_⟩
  · have : (QuotientGroup.mk' M x) = 1 := (QuotientGroup.eq_one_iff x).mpr (hHM hx)
    simp only [MonoidHom.comp_apply, this, map_one]
  · obtain ⟨x, hx⟩ : ∃ x, x ∉ M := by
      by_contra h; push Not at h
      exact hM.1 (eq_top_iff.mpr fun x _ => h x)
    refine ⟨x, fun h => hx ?_⟩
    have : (QuotientGroup.mk' M x) = 1 := ε.injective (by simpa using h)
    exact (QuotientGroup.eq_one_iff x).mp this

private theorem fratt {D B : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CommGroup B] [Finite B]
    {l : ℕ} [Fact l.Prime] (hB : IsPGroup l B) (χ : D →* B) (hχ : IsOpen (χ.ker : Set D)) (S : Set D)
    (hS : ∀ f : D → ZMod l, Continuous f → (∀ g h, f (g * h) = f g + f h) → (∀ s ∈ S, f s = 0) → f = 0)
    (H : Subgroup B) (hH : ∀ s ∈ S, χ s ∈ H) (g : D) : χ g ∈ H := by
  by_contra hg
  have hne : H.subgroupOf χ.range ≠ ⊤ := fun e => hg (by
    have : (⟨χ g, g, rfl⟩ : χ.range) ∈ H.subgroupOf χ.range := e ▸ Subgroup.mem_top _
    exact this)
  obtain ⟨θ, h1, ⟨_, x, rfl⟩, h2⟩ := exChar (hB.to_subgroup χ.range) _ hne
  let ψ : D →* Multiplicative (ZMod l) := θ.comp χ.rangeRestrict
  have hψ : IsOpen (ψ.ker : Set D) := Subgroup.isOpen_mono (fun y hy => by
    have : χ.rangeRestrict y = 1 := Subtype.ext hy
    simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, this, map_one]) hχ
  have hc : Continuous ψ := by
    refine continuous_of_continuousAt_one ψ ?_
    rw [ContinuousAt, map_one]
    exact tendsto_const_nhds.congr' (Filter.eventually_of_mem (hψ.mem_nhds ψ.ker.one_mem) fun y hy => Eq.symm hy)
  have := hS (fun y => (ψ y).toAdd) (continuous_toAdd.comp hc) (fun a b => by simp)
    (fun s hs => by
      have : ψ s = 1 := h1 _ (hH s hs)
      simp [this])
  exact h2 (by
    have h3 := congrFun this x
    exact h3)

private theorem lastStep {D B : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CommGroup B] [Finite B]
    {l : ℕ} [Fact l.Prime] (hB : IsPGroup l B) (χ : D →* B) (hχ : IsOpen (χ.ker : Set D)) (I : Subgroup D) (φ : D)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) (S : Set D) (hSI : ∀ s ∈ S, s ∈ I)
    (hS : ∀ f : D → ZMod l, Continuous f → (∀ g h, f (g * h) = f g + f h) → f φ = 0 → (∀ s ∈ S, f s = 0) → f = 0)
    (h0 : ∀ s ∈ S, χ s = 1) (g : D) (hg : g ∈ I) : χ g = 1 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hB
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  obtain ⟨d, hd1, hd2, hd3⟩ := hd (l ^ n) hpos
  have hB' : IsPGroup l (B × Multiplicative (ZMod (l ^ n))) :=
    IsPGroup.of_card (n := n + n) (by rw [Nat.card_prod, hn, pow_add]; simp)
  have hker : IsOpen (((χ.prod d).ker : Subgroup D) : Set D) := by
    rw [MonoidHom.ker_prod]
    exact hχ.inter (hd1.isOpen_fiber 1)
  have := fratt hB' (χ.prod d) hker (insert φ S)
    (fun f h1 h2 h3 => hS f h1 h2 (h3 φ (Set.mem_insert _ _)) fun s hs => h3 s (Set.mem_insert_of_mem _ hs))
    (Subgroup.zpowers ((χ.prod d) φ)) (by
      rintro s (rfl | hs)
      · exact Subgroup.mem_zpowers _
      · have : (χ.prod d) s = 1 := Prod.ext (h0 s hs) (hd2 s (hSI s hs))
        rw [this]
        exact Subgroup.one_mem _) g
  obtain ⟨k, hk⟩ := this
  have k1 : χ φ ^ k = χ g := congrArg Prod.fst hk
  have k2 : d φ ^ k = d g := congrArg Prod.snd hk
  rw [hd2 g hg, hd3, ← ofAdd_zsmul, ofAdd_eq_one, zsmul_eq_mul, mul_one, ZMod.intCast_zmod_eq_zero_iff_dvd] at k2
  obtain ⟨c, rfl⟩ := k2
  rw [← k1, zpow_mul, zpow_natCast, ← hn, pow_card_eq_one', one_zpow]

private theorem core {D : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D]
    {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (I J : Subgroup D) (hJ : IsClosed (J : Set D)) (e : D →* ℤ_[l]ˣ)
    (he : Continuous e) (r : ℕ) (hr : ¬ l ∣ r) (hIJ : ∀ g ∈ I, g ^ r ∈ J) (φ : D)
    (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (X : Submodule (ZMod l) (D → ZMod l)) (hX : ∀ f, f ∈ X ↔ Continuous f ∧ ∀ g h, f (g * h) = f g + f h)
    [FiniteDimensional (ZMod l) X] (n : ℕ) (hn : finrank (ZMod l) X ≤ n + 2) (f0 : D → ZMod l) (hf0 : f0 ∈ X)
    (hf0' : f0 φ ≠ 0) :
    ∃ u : Fin (n + 1) → D, (∀ a, u a ∈ J) ∧ (∀ a, a ≠ 0 → e (u a) = 1) ∧
      ∀ f : D → ZMod l, Continuous f → (∀ g h, f (g * h) = f g + f h) → f φ = 0 → (∀ a, f (u a) = 0) → f = 0 := by
  let P : Set D := {g | g ∈ J ∧ e g = 1}
  have hP : (1 : D) ∈ P := ⟨J.one_mem, map_one e⟩
  let W : Submodule (ZMod l) (D → ZMod l) := ⨅ p ∈ P, LinearMap.ker (LinearMap.proj p)
  have hW : ∀ f, f ∈ W ↔ ∀ p ∈ P, f p = 0 := fun f => by simp [W, Submodule.mem_iInf]
  let Y : Submodule (ZMod l) (D → ZMod l) := X ⊓ LinearMap.ker (LinearMap.proj φ)
  have hlt : Y < X := lt_of_le_of_ne inf_le_left fun h => hf0' (by
    have : f0 ∈ Y := h ▸ hf0
    exact this.2)
  haveI : FiniteDimensional (ZMod l) Y := Submodule.finiteDimensional_of_le hlt.le
  haveI : FiniteDimensional (ZMod l) (Y ⊓ W : Submodule (ZMod l) (D → ZMod l)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  by_cases hYW : Y ⊓ W = ⊥
  · obtain ⟨u, hu, hu'⟩ := pick P hP W hW (n + 1) Y (by omega)
    refine ⟨u, fun a => (hu a).1, fun a _ => (hu a).2, fun f c1 c2 c3 c4 => ?_⟩
    have hf : f ∈ Y := ⟨(hX f).mpr ⟨c1, c2⟩, c3⟩
    have : f ∈ Y ⊓ W := ⟨hf, hu' f hf c4⟩
    rwa [hYW] at this
  · have h2 : finrank (ZMod l) (Y ⊓ W : Submodule (ZMod l) (D → ZMod l)) ≠ 0 := fun h =>
      hYW (Submodule.finrank_eq_zero.mp h)
    obtain ⟨u, hu, hu'⟩ := pick P hP W hW n Y (by omega)
    haveI : Finite (Y ⊓ W : Submodule (ZMod l) (D → ZMod l)) := Module.finite_of_finite (ZMod l)
    let N : Set D := ⋂ f : (Y ⊓ W : Submodule (ZMod l) (D → ZMod l)), f.1 ⁻¹' {0}
    have hN : IsOpen N := isOpen_iInter_of_finite fun f =>
      (isOpen_discrete _).preimage ((hX f.1).mp f.2.1.1).1
    obtain ⟨u0, hu0, hgen⟩ := cyc1 hl J hJ e he N hN fun g hg hg' =>
      Set.mem_iInter.mpr fun f => (hW f.1).mp f.2.2 g ⟨hg, hg'⟩
    refine ⟨Fin.cons u0 u, fun a => ?_, fun a => ?_, fun f c1 c2 c3 c4 => ?_⟩
    · refine Fin.cases ?_ (fun a => ?_) a
      · exact hu0
      · exact (hu a).1
    · refine Fin.cases ?_ (fun a => ?_) a
      · exact fun h => absurd rfl h
      · exact fun _ => (hu a).2
    · have hf : f ∈ Y := ⟨(hX f).mpr ⟨c1, c2⟩, c3⟩
      have hfW : f ∈ Y ⊓ W := ⟨hf, hu' f hf fun a => c4 a.succ⟩
      let ψ : D →* Multiplicative (ZMod l) := MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) fun a b => by
        rw [c2, ofAdd_add]
      have p0 : ψ u0 = 1 := congrArg Multiplicative.ofAdd (c4 0)
      have pJ : ∀ g ∈ J, ψ g = 1 := fun g hg => by
        obtain ⟨m, hm⟩ := hgen g hg
        have : ψ (g⁻¹ * u0 ^ m) = 1 := congrArg Multiplicative.ofAdd (Set.mem_iInter.mp hm ⟨f, hfW⟩)
        rwa [map_mul, map_pow, p0, one_pow, mul_one, map_inv, inv_eq_one] at this
      have pI : I ≤ ψ.ker := fun g hg => by
        have h3 := pJ _ (hIJ g hg)
        rw [map_pow] at h3
        have h4 : (r : ZMod l) * f g = 0 := by
          have := congrArg Multiplicative.toAdd h3
          rw [toAdd_pow, nsmul_eq_mul] at this
          exact this
        have h5 : (r : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
        exact congrArg Multiplicative.ofAdd ((mul_eq_zero.mp h4).resolve_left h5)
      have hcl : IsClosed (ψ.ker : Set D) := (isClosed_discrete ({0} : Set (ZMod l))).preimage c1
      have htop : ⊤ ≤ ψ.ker := by
        rw [← hφ]
        refine Subgroup.topologicalClosure_minimal _ (sup_le pI ?_) hcl
        rw [Subgroup.zpowers_le]
        exact congrArg Multiplicative.ofAdd c3
      funext g
      exact congrArg Multiplicative.toAdd (htop (Subgroup.mem_top g))

private theorem finrank_cocycles_trivial_mod_l {D : Type} [Group D] [TopologicalSpace D] {l : ℕ} [Fact l.Prime] (d : ℕ) (ω : D →* (ZMod l)ˣ)
    (hω : ∃ g, ω g ≠ 1) (h1 : Module.Finite (ZMod l) (H1 (Representation.trivial (ZMod l) D (ZMod l))))
    (h2 : finrank (ZMod l) (H1 (Representation.trivial (ZMod l) D (ZMod l))) =
      finrank (ZMod l) (H0 (Representation.trivial (ZMod l) D (ZMod l))) +
      finrank (ZMod l) (Loc.H0dual ω (Representation.trivial (ZMod l) D (ZMod l))) + d * finrank (ZMod l) (ZMod l)) :
    FiniteDimensional (ZMod l) (Z1 (Representation.trivial (ZMod l) D (ZMod l))) ∧
      finrank (ZMod l) (Z1 (Representation.trivial (ZMod l) D (ZMod l))) ≤ d + 1 := by
  have hb : (B1 (Representation.trivial (ZMod l) D (ZMod l))).comap
      (Z1 (Representation.trivial (ZMod l) D (ZMod l))).subtype = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).mp hf
    exact Subtype.ext (funext fun g => by simpa using hm g)
  let ε := Submodule.quotEquivOfEqBot _ hb
  have h3 : Loc.H0dual ω (Representation.trivial (ZMod l) D (ZMod l)) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    obtain ⟨g, hg⟩ := hω
    refine LinearMap.ext fun x => ?_
    have h4 : f x = (ω g : ZMod l) * f x := hf g x
    by_contra h5
    have h6 : f x ≠ 0 := h5
    exact hg (Units.ext ((mul_eq_right₀ h6).mp h4.symm))
  have h4 := Submodule.finrank_le (H0 (Representation.trivial (ZMod l) D (ZMod l)))
  rw [h3, finrank_bot, finrank_self, ε.finrank_eq] at h2
  rw [finrank_self] at h4
  exact ⟨Module.Finite.equiv ε, by omega⟩

theorem UpperTheory.V.GC.genDec :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → (∃ g ∈ Dec (F := F) A, cycMod F Ω l 1 g ≠ 1) →
    ∀ K : Subgroup (G F Ω), K.Normal → IsOpen (K : Set (G F Ω)) → ¬ l ∣ K.index →
    ∃ (u : Fin (locDeg v) → Dec (F := F) A) (a₀ : Fin (locDeg v)), (∀ a, (u a).1 ∈ Ine (F := F) A ∧ (u a).1 ∈ K) ∧ (∀ a, a ≠ a₀ → cycZ F Ω l (u a).1 = 1) ∧
    ∀ (B : Type) [CommGroup B] [Finite B], IsPGroup l B → ∀ χ : Dec (F := F) A →* B, IsOpen (χ.ker : Set (Dec (F := F) A)) → (∀ a, χ (u a) = 1) → ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → χ g = 1 := by
  intro p1 p2 p3 F Ω _ _ _ _ _ l _ hl v A hA hv hω K hK hKo hKi
  obtain ⟨φ, -, hφ, hd⟩ := decZhat F Ω v A hA
  obtain ⟨e1, -, e2, -, e3⟩ := locEuler p1 p2 p3 F Ω l v A hA (ZMod l) (ZMod l)
    (Representation.trivial (ZMod l) (Dec (F := F) A) (ZMod l)) continuous_snd
  have hω' : ∃ g, ((cycF F Ω l (ZMod l)).comp (Dec (F := F) A).subtype) g ≠ 1 := by
    obtain ⟨g, hg, hg'⟩ := hω
    refine ⟨⟨g, hg⟩, fun h => hg' (Units.ext ?_)⟩
    have h1 : ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l) (cycMod F Ω l 1 g : ZMod (l ^ 1)) = 1 :=
      congrArg Units.val h
    haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
    exact (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).injective (by rw [h1]; simp)
  obtain ⟨f1, f2⟩ := finrank_cocycles_trivial_mod_l (locDeg v) _ hω' e1 (by rw [e2 hv, e3])
  obtain ⟨n, hn⟩ : ∃ n, locDeg v = n + 1 := by
    have := v.isPrime
    have h1 := Ideal.ramificationIdx_pos v.asIdeal ℤ
    have h2 := Ideal.inertiaDeg_pos v.asIdeal ℤ
    exact Nat.exists_eq_succ_of_ne_zero (Nat.mul_ne_zero h1.ne' h2.ne')
  rw [hn] at f2 ⊢
  haveI : IsGalois F Ω := {}
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.mp (isClosed_Dec A).isCompact
  obtain ⟨d, d1, -, d3⟩ := hd l (Fact.out : l.Prime).pos
  obtain ⟨u, u1, u2, u3⟩ := core hl ((Ine (F := F) A).subgroupOf (Dec (F := F) A))
    ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A))
    (((isClosed_Ine A).inter (K.isClosed_of_isOpen hKo)).preimage continuous_subtype_val)
    ((cycZ F Ω l).comp (Dec (F := F) A).subtype) ((continuous_cycZ F Ω l).comp continuous_subtype_val)
    K.index hKi (fun g hg => ⟨(Ine (F := F) A).pow_mem hg _, K.pow_index_mem g.1⟩) φ hφ
    (Z1 (Representation.trivial (ZMod l) (Dec (F := F) A) (ZMod l))) (fun f => Iff.rfl) n f2
    (fun g => (d g).toAdd) ⟨continuous_toAdd.comp d1.continuous, fun g h => by simp⟩ (by simp [d3])
  refine ⟨u, 0, u1, u2, fun B _ _ hB χ hχ h0 g hg => ?_⟩
  exact lastStep hB χ hχ _ φ hd (Set.range u) (by rintro _ ⟨a, rfl⟩; exact (u1 a).1)
    (fun f c1 c2 c3 c4 => u3 f c1 c2 c3 fun a => c4 _ ⟨a, rfl⟩) (by rintro _ ⟨a, rfl⟩; exact h0 a) g hg
