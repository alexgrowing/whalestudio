import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.TameEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.IsClosedOfClosedFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem ch_ur {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M) (J : Subgroup D) (hJ : ∀ j ∈ J, ∀ m, ρ j m = m)
    (z : Z1 ρ) : (Submodule.Quotient.mk z : H1 ρ) ∈ H1ur ρ J ↔ ∀ j ∈ J, z.1 j = 0 := by
  refine (Submodule.Quotient.mk_eq_zero _).trans ((mem_coboundaries1 _ _).trans ⟨fun ⟨m, hm⟩ j hj => ?_, fun h => ⟨0, fun j => ?_⟩⟩)
  · exact (hm ⟨j, hj⟩).trans (sub_eq_zero.2 (hJ j hj m))
  · rw [map_zero, sub_zero]
    exact h j.1 j.2

private theorem ch_low (hF : LocalFiniteness) (hT : LocalTateDuality) (hE : LocalEulerChar) {F Ω : Type} [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (K : Subgroup (G F Ω)) [K.Normal] (ho : IsOpen (K : Set (G F Ω)))
    (hi : ¬ l ∣ K.index) (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (G F Ω) M) (hρ : ContAction ρ) (hK : ∀ g ∈ K, ρ g = 1) :
    Nat.card (H0 (ρ.comp (Dec (F := F) A).subtype)) ≤
      Nat.card (H1ur (ρ.comp (Dec (F := F) A).subtype) ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A))) := by
  haveI : Module.Finite k M := Module.Finite.of_finite
  let σ : Representation k (Dec (F := F) A) M := ρ.comp (Dec (F := F) A).subtype
  obtain ⟨f1, -, -, e1, -⟩ := locEuler hF hT hE F Ω l v A hA k M σ
    (Continuous.comp hρ ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  obtain ⟨f2, e2⟩ := tameEq hF hT hE F Ω l v A hA hv K ho hi k M ρ hρ fun g hg => hK g hg.2
  let i : (Ine (F := F) A ⊓ K : Subgroup (G F Ω)) → Dec (F := F) A := fun j => ⟨j.1, Ine_le_Dec A j.2.1⟩
  have hi' : ∀ j m, σ (i j) m = m := fun j m => LinearMap.congr_fun (hK _ j.2.2) m
  let r : Z1 σ →ₗ[k] eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K) :=
    { toFun := fun z => ⟨fun j => z.1 (i j),
        (IsLocallyConstant.iff_continuous _).2 (z.2.1.comp (continuous_subtype_val.subtype_mk _)),
        fun a b => (z.2.2 (i a) (i b)).trans (by rw [hi']), fun d hd j j' h => by
          have e : i j' * ⟨d, hd⟩ = ⟨d, hd⟩ * i j := Subtype.ext (by
            show j'.1 * d = d * j.1
            rw [h, inv_mul_cancel_right])
          have e' := congrArg z.1 e
          rw [z.2.2, z.2.2, hi', add_comm] at e'
          exact add_left_cancel e'⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let r' : H1 σ →ₗ[k] eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K) := Submodule.liftQ _ r fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
    exact Subtype.ext (funext fun j => (hm (i j)).trans (sub_eq_zero.2 (hi' j m)))
  have hker : LinearMap.ker r' ≤ H1ur σ ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)) := by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (ch_ur σ _ (fun j hj m => hi' ⟨j.1, hj⟩ m) z).2 fun j hj => ?_
    exact congrFun (congrArg Subtype.val (show r z = 0 from hx)) ⟨j.1, hj⟩
  have h1 := r'.finrank_range_add_finrank_ker
  have h2 := Submodule.finrank_mono hker
  have h3 := (LinearMap.range r').finrank_le
  have h4 := e1 hv
  change Nat.card (H0 σ) ≤ Nat.card (H1ur σ ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)))
  rw [Module.natCard_eq_pow_finrank (K := k) (V := H0 σ),
    Module.natCard_eq_pow_finrank (K := k) (V := H1ur σ ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)))]
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  change _ = finrank k (H2 σ) at e2
  omega

private theorem ch_cup {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (hA : IsPlaceOver A v) (K : Subgroup (G F Ω)) [K.Normal]
    (ho : IsOpen (K : Set (G F Ω))) (hi : ¬ l ∣ K.index) (k : Type) [Field k] [Finite k] [CharP k l] [TopologicalSpace k]
    [DiscreteTopology k] (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
    {Γ : Type} [Group Γ] (μ : Γ →* kˣ) (ρ : Representation k Γ M) (φ : Dec (F := F) A →* Γ)
    (hρ : ContAction (ρ.comp φ)) (hμ : ContAction ((charRep μ).comp φ))
    (hK : ∀ g : Dec (F := F) A, g.1 ∈ K → ρ (φ g) = 1 ∧ μ (φ g) = 1)
    (y : Z1 ((twDual μ ρ).comp φ)) (hy : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ⊓ K → y.1 g = 0)
    (x : H1 (ρ.comp φ)) (hx : x ∈ H1ur (ρ.comp φ) ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A))) :
    cupH1H1TwistedDual μ ρ φ hρ (Submodule.Quotient.mk y) x = 0 := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  replace hx := (ch_ur _ ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A))
    (fun j hj m => LinearMap.congr_fun (hK j hj.2).1 m) x).1 hx
  obtain ⟨γ, -, h1, h2⟩ := decZhat F Ω v A hA
  haveI : ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)).Normal :=
    ⟨fun n hn g => ⟨conj_mem_Ine g.2 hn.1, Subgroup.Normal.conj_mem inferInstance _ hn.2 _⟩⟩
  obtain ⟨b, hb1, -, hb2⟩ := H2_unramified_inflation l (Dec (F := F) A) k k ((charRep μ).comp φ) hμ
    ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)) γ
    (fun g hg => hg.1) (((isClosed_Ine A).inter (K.isClosed_of_isOpen ho)).preimage continuous_subtype_val)
    (by
      rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec A), Subgroup.inf_relIndex_left]
      exact fun h => hi (h.trans (Subgroup.relIndex_dvd_index_of_normal _ _)))
    (fun j hj => LinearMap.ext fun m => by simp [(hK j hj.2).2]) h1 h2
    (cupCocycleZ1Z1 ((twDual μ ρ).comp φ) (ρ.comp φ) ((charRep μ).comp φ) evalPair.flip
      continuous_of_discreteTopology (fun g y x => evalPair_equiv μ ρ (φ g) x y) hρ y x)
    (fun s t j hj j' hj' => by
      show y.1 (s * j) (ρ (φ (s * j)) (x.1 (t * j'))) = y.1 s (ρ (φ s) (x.1 t))
      rw [y.2.2, x.2.2, hy j hj, hx j' hj', map_zero, map_zero, add_zero, add_zero, map_mul, map_mul,
        (hK j hj.2).1, mul_one])
  exact (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2
    ⟨b, (IsLocallyConstant.iff_continuous _).1 hb1, funext fun p => (hb2 p.1 p.2).symm⟩)

open scoped Classical in

theorem UpperTheory.V.GC.gwTame (P : Hypotheses₂) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [Fact l.Prime] (hl : l ≠ 2) (S S' : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l) (hS' : ContainsAbove S' l)
    (A : S' → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (A v) v.1) (K : Subgroup (G F Ω)) [K.Normal]
    (ho : IsOpen (K : Set (G F Ω))) (hi : ¬ l ∣ K.index) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ)
    (μ : GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ 1))ˣ) (hμ : μ.comp (toGS Ω _) = cycMod F Ω l 1)
    (hK : ∀ g ∈ K, ρ (toGS Ω _ g) = 1 ∧ μ (toGS Ω _ g) = 1) (c : InfinitePlace F → G F Ω) (hc : ∀ w, IsCCAt w (c w))
    (X : Type) (f : X → Z1 (twDual μ ρ))
    (hf : Function.Injective fun x => (Submodule.Quotient.mk (f x) : H1 (twDual μ ρ)))
    (hf' : ∀ x (q : S'), q.1 ∉ S → ∀ g ∈ Ine (F := F) (A q) ⊓ K, (f x).1 (toGS Ω _ g) = 0) :
    Finite X ∧ Nat.card X ≤
      Nat.card {y : H1 ρ // ∃ z : Z1 ρ, Submodule.Quotient.mk z = y ∧
        ∀ v : S', ∀ g ∈ Ine (F := F) (A v) ⊓ K, z.1 (toGS Ω _ g) = 0} * Nat.card (H0 (twDual μ ρ)) *
      (∏ v : S', if v.1 ∈ S then Nat.card (H0 (ρ.comp (locFam S' A v))) else 1) * archH0Card S' ρ c := by
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  haveI : CharP (ZMod (l ^ 1)) l := CharP.congr (l ^ 1) (pow_one l)
  let L : LocCond ρ (locFam S' A) := fun v => if v.1 ∈ S then ⊥ else
    H1ur (ρ.comp (locFam S' A v)) ((Ine (F := F) (A v) ⊓ K).subgroupOf (Dec (F := F) (A v)))
  have hc' : ∀ v, ContAction (ρ.comp (locFam S' A v)) := fun v => hρ.comp' (continuous_locFam S' A v)
  have gw := P.gw F Ω l 1 M S' ρ one_pos hl hS' hρ μ hμ A hA c (fun w _ => hc w) L
  obtain ⟨-, f1, -⟩ := P.gf F Ω l 1 M S' ρ one_pos hS' hρ
  have f2 : ∀ v, Finite (H1 (ρ.comp (locFam S' A v))) := fun v => (P.lf F Ω l 1 M (A v) _ v.1 one_pos (hA v) (hc' v)).2.1
  haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
  have ha : 0 < archH0Card S' ρ c := by
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (Nat.pow_pos Nat.card_pos)
    haveI : Nonempty {m : M // ρ (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  have hmem : ∀ x, (Submodule.Quotient.mk (f x) : H1 (twDual μ ρ)) ∈ Sel (twDual μ ρ) (locFam S' A) (continuous_locFam S' A)
      (perpCond μ ρ (locFam S' A) hc' L) := by
    intro x
    rw [mem_Sel]
    intro v
    rw [mem_perpCond]
    intro y hy
    by_cases hv : v.1 ∈ S
    · simp only [L, if_pos hv, Submodule.mem_bot] at hy
      rw [hy, map_zero]
    · simp only [L, if_neg hv] at hy
      exact ch_cup l v.1 (A v) (hA v) K ho hi (ZMod (l ^ 1)) M μ ρ (locFam S' A v) (hc' v)
        ((GlobalTheory.Published.PoitouTate.contAction_charRep hμ).comp' (continuous_locFam S' A v)) (fun g hg => hK g.1 hg)
        (restrictCocycles1 _ _ (continuous_locFam S' A v) (f x)) (fun g hg => hf' x v hv g.1 hg) y hy
  have hpos : 0 < Nat.card (Sel ρ (locFam S' A) (continuous_locFam S' A) L) * Nat.card (H0 (twDual μ ρ)) *
      (∏ v : S', Nat.card (H0 (ρ.comp (locFam S' A v)))) * archH0Card S' ρ c :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) (Finset.prod_pos fun v _ => Nat.card_pos)) ha
  haveI : Finite (Sel (twDual μ ρ) (locFam S' A) (continuous_locFam S' A) (perpCond μ ρ (locFam S' A) hc' L)) := by
    refine Nat.finite_of_card_ne_zero fun h => ?_
    rw [gw, h, zero_mul, zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hinj : Function.Injective fun x => (⟨_, hmem x⟩ : Sel (twDual μ ρ) (locFam S' A) (continuous_locFam S' A)
      (perpCond μ ρ (locFam S' A) hc' L)) := fun a b h => hf (congrArg Subtype.val h)
  refine ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans ?_⟩
  have h1 : (∏ v : S', Nat.card (H0 (ρ.comp (locFam S' A v)))) ≤
      (∏ v : S', if v.1 ∈ S then Nat.card (H0 (ρ.comp (locFam S' A v))) else 1) * ∏ v : S', Nat.card (L v) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun v _ => ?_
    by_cases hv : v.1 ∈ S
    · rw [if_pos hv]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    · simp only [L, if_neg hv, one_mul]
      exact ch_low P.lf P.lt P.le l v.1 (A v) (hA v) (fun h => hv (hS _ h)) K ho hi (ZMod (l ^ 1)) M (ρ.comp (toGS Ω _))
        (hρ.comp' (continuous_toGS Ω _)) fun g hg => (hK g hg).1
  have h2 : Nat.card (Sel ρ (locFam S' A) (continuous_locFam S' A) L) ≤
      Nat.card {y : H1 ρ // ∃ z : Z1 ρ, Submodule.Quotient.mk z = y ∧
        ∀ v : S', ∀ g ∈ Ine (F := F) (A v) ⊓ K, z.1 (toGS Ω _ g) = 0} := by
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) fun a b h => Subtype.ext (Subtype.mk.inj h)
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨z, rfl, fun v g hg => ?_⟩
    have h3 : resH1 ρ _ (continuous_locFam S' A v) (Submodule.Quotient.mk z) ∈
        H1ur (ρ.comp (locFam S' A v)) ((Ine (F := F) (A v) ⊓ K).subgroupOf (Dec (F := F) (A v))) := by
      have := (mem_Sel _ _ _ _ _).1 hy v
      by_cases hv : v.1 ∈ S
      · simp only [L, if_pos hv, Submodule.mem_bot] at this
        rw [this]
        exact zero_mem _
      · simpa only [L, if_neg hv] using this
    exact (ch_ur _ ((Ine (F := F) (A v) ⊓ K).subgroupOf (Dec (F := F) (A v)))
      (fun j hj m => LinearMap.congr_fun (hK j.1 hj.2).1 m) (restrictCocycles1 ρ _ (continuous_locFam S' A v) z)).1 h3
      ⟨g, Ine_le_Dec _ hg.1⟩ hg
  have h3 : 0 < ∏ v : S', Nat.card (L v) := Finset.prod_pos fun v _ => Nat.card_pos
  have h4 : 0 < Nat.card (H0 ρ) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ h3
  refine (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h4)).trans (gw.ge.trans ?_)
  calc _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ h2) h1)
    _ = _ := by ring
