import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.RedUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.NotDvdTorsionOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Base

private theorem glue {G H : Type*} [CommGroup G] [CommGroup H] (p : G →* H)
    (f : G →* ℂˣ) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* ℂˣ, ∀ x, F (p x) = f x := by
  have hker : p.rangeRestrict.ker ≤ f.ker := by
    intro c hc
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hc
    rw [MonoidHom.mem_ker]
    exact h c hc
  let ω' : p.range →* ℂˣ :=
    p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨f, hker⟩
  have hω' : ∀ c, ω' (p.rangeRestrict c) = f c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  obtain ⟨F, hF⟩ := KStar.Choice.isDiv_complex_circle.1.exists_extension p.range ω'
  refine ⟨F, fun c => ?_⟩
  rw [← hω', ← hF]
  rfl

private def lev (K : Type) [Field K] [NumberField K] (N : ℕ) : Subgroup (Ideles K) where
  carrier := {a | a ∈ GlobalTheory.Mem.Chr.unitIdl K ∧ ∀ v : HeightOneSpectrum (𝓞 K),
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤ Valued.v (N : v.adicCompletion K)}
  one_mem' := ⟨one_mem _, fun v => by
    show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    rw [sub_self, map_zero]
    exact zero_le⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v => by
    show Valued.v ((a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1) ≤ _
    have e : (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1 =
        (a : AdeleRing (𝓞 K) K).2 v * ((b : AdeleRing (𝓞 K) K).2 v - 1) + ((a : AdeleRing (𝓞 K) K).2 v - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ (ha.2 v)
    rw [map_mul, ha.1 v, one_mul]
    exact hb.2 v⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v => by
    have h : (a : AdeleRing (𝓞 K) K).2 v * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
    have e : (a : AdeleRing (𝓞 K) K).2 v * (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v - 1) =
        -((a : AdeleRing (𝓞 K) K).2 v - 1) := by linear_combination h
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion K) _) e
    rw [map_mul, ha.1 v, one_mul, Valuation.map_neg] at h2
    rw [h2]
    exact ha.2 v⟩

private theorem lev_mem_nhds (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : N ≠ 0) :
    (lev K N : Set (Ideles K)) ∈ nhds (1 : Ideles K) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 K) K | ∀ v, a v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      fun _ => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun x : Ideles K => x.val.2 := continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun x : Ideles K => (x⁻¹).val.2 := h1.comp continuous_inv
  have h3 : Continuous fun x : Ideles K =>
      (x.val.2 - 1) * algebraMap K (FiniteAdeleRing (𝓞 K) K) (N : K)⁻¹ :=
    (h1.sub continuous_const).mul continuous_const
  have hU := ((hO.preimage h1).inter (hO.preimage h2)).inter (hO.preimage h3)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨⟨fun v => one_mem _, fun v => one_mem _⟩, fun v => ?_⟩) ?_
  · have : ((1 : Ideles K).val.2 - 1) = 0 := sub_self _
    simp only [this, zero_mul]
    exact zero_mem _
  · rintro y ⟨⟨hy, hy'⟩, hy''⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have e : y.val.2 v * (y⁻¹).val.2 v = 1 :=
        congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) y.mul_inv
      have e' := congrArg Valued.v e
      rw [map_mul, map_one] at e'
      exact eq_one_of_one_le_mul_left (hy v) (hy' v) e'.ge
    · have e : Valued.v ((y.val.2 v - 1) * algebraMap K (v.adicCompletion K) (N : K)⁻¹) ≤ 1 := hy'' v
      haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
      have h0 : Valued.v (N : v.adicCompletion K) ≠ 0 := by
        rw [Valuation.ne_zero_iff]
        exact Nat.cast_ne_zero.2 hN
      rw [map_inv₀, map_natCast, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul] at e
      exact e

private noncomputable def crd (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) : Ideles K →* ℂˣ :=
  Units.map ((InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))).toMonoidHom

private noncomputable def kap (K : Type) [Field K] [NumberField K] (a : ℤ) : Ideles K →* ℂˣ :=
  ∏ w : InfinitePlace K, crd K w ^ a

private theorem coe_kap (K : Type) [Field K] [NumberField K] (a : ℤ) (x : Ideles K) :
    (kap K a x : ℂ) = ∏ w : InfinitePlace K, InfinitePlace.Completion.extensionEmbedding w (x.val.1 w) ^ a := by
  rw [kap, MonoidHom.finsetProd_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]
  rfl

private theorem continuous_kap (K : Type) [Field K] [NumberField K] (a : ℤ) : Continuous (kap K a) := by
  have e : (kap K a : Ideles K → ℂˣ) = fun x => ∏ w : InfinitePlace K, (crd K w x) ^ a := by
    funext x
    rw [kap, MonoidHom.finsetProd_apply]
    rfl
  rw [e]
  refine continuous_finsetProd _ fun w _ => Continuous.zpow (f := crd K w) (Continuous.units_map _ ?_) a
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

private theorem coe_infDiag' {E : Type} [Field E] [NumberField E] (k : Eˣ) :
    (infDiag k : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
  classical
  rw [infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
  let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
  refine Prod.ext ?_ ?_
  · change p1 _ = _
    rw [map_prod]
    change ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _
    exact Finset.univ_prod_mulSingle _
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ => rfl

private theorem kap_of_fst {K : Type} [Field K] [NumberField K] (a : ℤ) (x : Ideles K) (k : K)
    (h : x.val.1 = algebraMap K (InfiniteAdeleRing K) k) :
    (kap K a x : ℂ) = ∏ w : InfinitePlace K, w.embedding k ^ a := by
  rw [coe_kap, h]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ k)

open Classical in
private theorem prod_type (E : Type) [Field E] [NumberField E] (a : ℤ) (k : E) :
    ∏ w : InfinitePlace E, w.embedding k ^ a =
      ∏ φ : E →+* ℂ, φ k ^ (if (InfinitePlace.mk φ).embedding = φ then a else 0) := by
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_eq_single_of_mem w.embedding (by simp)]
  · rw [InfinitePlace.mk_embedding, if_pos rfl]
  · intro φ hφ hne
    rw [(Finset.mem_filter.1 hφ).2, if_neg hne.symm, zpow_zero]

private theorem loc_self {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) : ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion E)

private theorem loc_ne {E : Type} [Field E] [NumberField E] {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v)
    (x : (v.adicCompletion E)ˣ) : ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion E)

private theorem loc_mem {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)}
    {x : (v.adicCompletion E)ˣ} (hx : IsUnitAt v x) : localIdele E v x ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro w
  by_cases h : w = v
  · subst h
    rw [loc_self]
    exact hx
  · rw [loc_ne h, map_one]

private theorem kap_loc {E : Type} [Field E] [NumberField E] (a : ℤ) (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) : kap E a (localIdele E v x) = 1 := by
  apply Units.ext
  rw [kap_of_fst a _ 1 (by rw [map_one]; rfl)]
  simp

private theorem val_alg {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (v.adicCompletion E) a) = v.valuation E a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem exists_unit {E : Type} [Field E] [NumberField E] (k : Eˣ)
    (h : diagUnits E k ∈ GlobalTheory.Mem.Chr.unitIdl E) : ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k := by
  have key : ∀ k : Eˣ, diagUnits E k ∈ GlobalTheory.Mem.Chr.unitIdl E → ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = k :=
    fun k h => HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E (k : E) fun v => by
      rw [← val_alg]
      exact (h v).le
  obtain ⟨r, hr⟩ := key k h
  obtain ⟨s, hs⟩ := key k⁻¹ (by rw [map_inv]; exact inv_mem h)
  have e : r * s = 1 := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, hr, hs, map_one, Units.mul_inv]
  exact ⟨Units.mkOfMulEqOne r s e, hr⟩

theorem UpperTheory.V.Sd.Tw.hecke :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (l : ℕ), l.Prime → l ≠ 2 →
        ¬ (l : ℤ) ∣ discr K → ∀ (N : ℕ), 3 ≤ N → ∀ (χ : (ZMod N)ˣ →* ℂˣ), χ ^ 2 = 1 → χ (-1) = -1 →
        ∃ (Y : HChar K) (a : (K →+* ℂ) → ℤ) (τ : K →+* ℂ), Y.IsAlg a ∧ a τ = -1 ∧ a (ComplexEmbedding.conjugate τ) = 0 ∧
          (∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∉ v.asIdeal → Y.UnrAt v) ∧
          (∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ∀ (v : HeightOneSpectrum (𝓞 K)) x, IsUnitAt v x → Y.loc v x ^ m = 1) ∧
          ∀ (p : ℕ) (h : p.Coprime N) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal = Ideal.span {(p : 𝓞 K)} →
            ((Y.val w : ℂˣ) : ℂ) = (p : ℂ) * (((χ (ZMod.unitOfCoprime p h))⁻¹ : ℂˣ) : ℂ) := by
  intro K _ _ _ h2 l hl hl2 hd N hN χ hχ hχ1
  classical
  have hc : Fintype.card (InfinitePlace K) = 1 := by
    have := IsTotallyComplex.finrank K
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  obtain ⟨w₀, hw₀⟩ := Fintype.card_eq_one_iff.1 hc
  have hk : ∀ (x : Ideles K) (k : K), x.val.1 = algebraMap K (InfiniteAdeleRing K) k →
      (kap K (-1) x : ℂ) = (w₀.embedding k)⁻¹ := fun x k h => by
    rw [kap_of_fst _ x k h, Fintype.prod_eq_single w₀ (fun y hy => absurd (hw₀ y) hy), zpow_neg_one]
  obtain ⟨red, hred⟩ := UpperTheory.V.Sd.Tw.red K N (by omega)
  obtain ⟨e, m, hm, hlm, hem, heu, hen⟩ := UpperTheory.V.Sd.Tw.fin K h2 l hl hl2 hd N hN χ hχ hχ1 w₀.embedding
  obtain ⟨ξ, hξ⟩ := glue ((GlobalTheory.Mem.Chr.unitIdl K).subtype.coprod (diagUnits K))
    ((((kap K (-1)).comp (GlobalTheory.Mem.Chr.unitIdl K).subtype) * e.comp red).coprod 1) (by
      rintro ⟨⟨b, hb⟩, k⟩ h
      change b * diagUnits K k = 1 at h
      change kap K (-1) b * e (red ⟨b, hb⟩) * 1 = 1
      obtain rfl : b = diagUnits K k⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
      obtain ⟨u, hu⟩ := exists_unit _ hb
      have h1 : red ⟨_, hb⟩ = Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})).toMonoidHom u :=
        Units.ext (hred _ u fun v _ => by
          rw [hu]
          show Valued.v (algebraMap K (v.adicCompletion K) ((k⁻¹ : Kˣ) : K) - _) ≤ _
          rw [sub_self, map_zero]
          exact zero_le)
      apply Units.ext
      rw [mul_one, Units.val_mul, h1, heu, hk _ ((k⁻¹ : Kˣ) : K) rfl, hu, Units.val_one]
      exact inv_mul_cancel₀ (by simp))
  have hu : ∀ u (h : u ∈ GlobalTheory.Mem.Chr.unitIdl K), ξ u = kap K (-1) u * e (red ⟨u, h⟩) := fun u h => by
    simpa using hξ (⟨u, h⟩, 1)
  have hu1 : ∀ u (h : u ∈ GlobalTheory.Mem.Chr.unitIdl K), (∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∈ v.asIdeal →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v - 1) ≤ Valued.v (N : v.adicCompletion K)) →
      ξ u = kap K (-1) u := fun u h h' => by
    have h1 : red ⟨u, h⟩ = 1 := Units.ext (by
      rw [hred ⟨u, h⟩ 1 fun v hv => by simpa using h' v hv]
      rfl)
    rw [hu u h, h1, map_one, mul_one]
  have hcont : Continuous ξ := by
    refine continuous_of_continuousAt_one ξ ((continuous_kap K (-1)).continuousAt.congr ?_)
    filter_upwards [lev_mem_nhds K (N := N) (by omega)] with x hx
    exact (hu1 x hx.1 fun v _ => hx.2 v).symm
  have hdiag : ∀ k, ξ (diagUnits K k) = 1 := fun k => by simpa using hξ (1, k)
  let Y : HChar K := ⟨ξ, hcont, hdiag⟩
  have hunr : ∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∉ v.asIdeal → Y.UnrAt v := fun v hv x hx => by
    change ξ (localIdele K v x) = 1
    rw [hu1 _ (loc_mem hx), kap_loc]
    intro w hw
    rw [loc_ne (fun h : w = v => hv (h ▸ hw)), sub_self, map_zero]
    exact zero_le
  refine ⟨Y, fun φ => if (InfinitePlace.mk φ).embedding = φ then -1 else 0, w₀.embedding, fun k => ?_, ?_, ?_,
    hunr, ⟨m, hm, hlm, fun v x hx => ?_⟩, fun p hp w hw => ?_⟩
  · change ((ξ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hu1, kap_of_fst _ _ (k : K) (by rw [coe_infDiag']), prod_type]
    · intro v
      rw [coe_infDiag']
      exact map_one _
    · intro v _
      rw [coe_infDiag']
      show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
      rw [sub_self, map_zero]
      exact zero_le
  · simp
  · refine if_neg ?_
    rw [hw₀ (InfinitePlace.mk _)]
    intro h
    exact IsTotallyComplex.complexEmbedding_not_isReal _ (ComplexEmbedding.isReal_iff.2 h.symm)
  · change ξ (localIdele K v x) ^ m = 1
    rw [hu _ (loc_mem hx), kap_loc, one_mul, hem]
  · have hp0 : (p : 𝓞 K) ≠ 0 := fun h => w.ne_bot (by rw [hw, h, Ideal.span_singleton_eq_bot])
    have hpw : (p : 𝓞 K) ∈ w.asIdeal := hw ▸ Ideal.mem_span_singleton_self _
    have hNw : (N : 𝓞 K) ∉ w.asIdeal := fun h => by
      obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (N : 𝓞 K) := Nat.Coprime.cast hp
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ h)))
    let k : Kˣ := Units.mk0 ((p : 𝓞 K) : K) (by simpa using hp0)
    have hval : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (algebraMap K (v.adicCompletion K) k) = v.intValuation (p : 𝓞 K) := fun v => by
      rw [val_alg]
      exact v.valuation_of_algebraMap _
    have hun : IsUnifAt w (atFin w k) := (hval w).trans (w.intValuation_singleton hp0 hw)
    let b : Ideles K := diagUnits K k * localIdele K w (atFin w k)⁻¹
    have hb2 : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ w →
        (b : AdeleRing (𝓞 K) K).2 v = algebraMap K (v.adicCompletion K) k := fun v hv => by
      change algebraMap K (v.adicCompletion K) k * (localIdele K w (atFin w k)⁻¹).val.2 v = _
      rw [loc_ne hv, mul_one]
    have hb : b ∈ GlobalTheory.Mem.Chr.unitIdl K := fun v => by
      by_cases hv : v = w
      · subst hv
        change Valued.v (((atFin v k : (v.adicCompletion K)ˣ) : v.adicCompletion K) *
          (localIdele K v (atFin v k)⁻¹).val.2 v) = 1
        rw [loc_self, Units.mul_inv, map_one]
      · rw [hb2 v hv, hval, v.intValuation_eq_one_iff]
        intro h
        refine hv (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top ?_).symm)
        rw [hw]
        exact (Ideal.span_singleton_le_iff_mem _).2 h
    have h1 : e (red ⟨b, hb⟩) = χ (ZMod.unitOfCoprime p hp) := hen _ p hp (by
      rw [hred ⟨b, hb⟩ p, map_natCast]
      intro v hv
      rw [hb2 v fun h => hNw (h ▸ hv)]
      show Valued.v (algebraMap K (v.adicCompletion K) k - algebraMap K (v.adicCompletion K) k) ≤ _
      rw [sub_self, map_zero]
      exact zero_le)
    have h3 : (kap K (-1) b : ℂ) = (p : ℂ)⁻¹ := by
      rw [hk b k (mul_one _)]
      simp [k]
    have h4 : ξ b = (Y.val w)⁻¹ := by
      rw [← Y.val_eq (hunr w hNw) _ hun, map_mul, hdiag, one_mul, map_inv, map_inv]
      rfl
    rw [← inv_inv (Y.val w), ← h4, hu b hb, h1, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, h3, inv_inv]
