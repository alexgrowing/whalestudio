import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

namespace DifferentiableLines.Cpt

open AlgebraicGeometry CategoryTheory Topology Filter TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Points

variable {B : Type} (𝒰 : Ultrafilter B)

abbrev K : Type := Germ (𝒰 : Filter B) ℂ

theorem exists_tendsto_of_bdd (f : B → ℂ) (h : ∀ᶠ b in (𝒰 : Filter B), ‖f b‖ ≤ 1) :
    ∃ a, Tendsto f 𝒰 (𝓝 a) := by
  obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : ℂ) 1).ultrafilter_le_nhds (𝒰.map f)
    (le_principal_iff.2 (by
      show ∀ᶠ b in (𝒰 : Filter B), f b ∈ Metric.closedBall (0 : ℂ) 1
      simpa using h))
  exact ⟨a, ha⟩

def V : ValuationSubring (K 𝒰) where
  carrier := {g | ∃ a, g.Tendsto (𝓝 a)}
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    induction g using Germ.inductionOn
    induction h using Germ.inductionOn
    exact ⟨a * b, Tendsto.mul ha hb⟩
  one_mem' := ⟨1, tendsto_const_nhds⟩
  add_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    induction g using Germ.inductionOn
    induction h using Germ.inductionOn
    exact ⟨a + b, Tendsto.add ha hb⟩
  zero_mem' := ⟨0, tendsto_const_nhds⟩
  neg_mem' := by
    rintro g ⟨a, ha⟩
    induction g using Germ.inductionOn
    exact ⟨-a, Tendsto.neg ha⟩
  mem_or_inv_mem' g := by
    induction g using Germ.inductionOn with
    | h f =>
    rcases 𝒰.em (fun b => ‖f b‖ ≤ 1) with h | h
    · exact Or.inl (exists_tendsto_of_bdd 𝒰 f h)
    · refine Or.inr (exists_tendsto_of_bdd 𝒰 f⁻¹ (h.mono fun b hb => ?_))
      rw [Pi.inv_apply, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 hb).le

theorem tendsto_unique {g : K 𝒰} {a b : ℂ} (ha : g.Tendsto (𝓝 a)) (hb : g.Tendsto (𝓝 b)) : a = b := by
  induction g using Germ.inductionOn
  exact tendsto_nhds_unique (l := (𝒰 : Filter B)) ha hb

theorem tendsto_choose (g : V 𝒰) : (g : K 𝒰).Tendsto (𝓝 (Exists.choose g.2)) := Exists.choose_spec g.2

def st : V 𝒰 →+* ℂ where
  toFun g := Exists.choose g.2
  map_one' := tendsto_unique 𝒰 (tendsto_choose 𝒰 1) tendsto_const_nhds
  map_zero' := tendsto_unique 𝒰 (tendsto_choose 𝒰 0) tendsto_const_nhds
  map_mul' g h := tendsto_unique 𝒰 (tendsto_choose 𝒰 (g * h)) (by
    have ha := tendsto_choose 𝒰 g
    have hb := tendsto_choose 𝒰 h
    generalize Exists.choose g.2 = a at ha
    generalize Exists.choose h.2 = b at hb
    show ((g : K 𝒰) * h).Tendsto _
    generalize (g : K 𝒰) = g at ha
    generalize (h : K 𝒰) = h at hb
    induction g using Germ.inductionOn
    induction h using Germ.inductionOn
    exact Tendsto.mul ha hb)
  map_add' g h := tendsto_unique 𝒰 (tendsto_choose 𝒰 (g + h)) (by
    have ha := tendsto_choose 𝒰 g
    have hb := tendsto_choose 𝒰 h
    generalize Exists.choose g.2 = a at ha
    generalize Exists.choose h.2 = b at hb
    show ((g : K 𝒰) + h).Tendsto _
    generalize (g : K 𝒰) = g at ha
    generalize (h : K 𝒰) = h at hb
    induction g using Germ.inductionOn
    induction h using Germ.inductionOn
    exact Tendsto.add ha hb)

theorem tendsto_st (g : V 𝒰) : (g : K 𝒰).Tendsto (𝓝 (st 𝒰 g)) := tendsto_choose 𝒰 g

def cst : ℂ →+* V 𝒰 where
  toFun a := ⟨((fun _ => a : B → ℂ) : K 𝒰), a, tendsto_const_nhds⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem st_cst (a : ℂ) : st 𝒰 (cst 𝒰 a) = a := tendsto_unique 𝒰 (tendsto_st 𝒰 _) tendsto_const_nhds

instance : IsLocalHom (st 𝒰) := IsLocalHom.of_surjective _ fun a => ⟨_, st_cst 𝒰 a⟩

variable {X : Scheme.{0}} (e : B → (Sp ℂ ⟶ X))

def gm (W : X.Opens) (f : Γ(X, W)) : K 𝒰 := ((fun b => valR (e b) W f : B → ℂ) : K 𝒰)

def gmHom (W : X.Opens) (h : ∀ᶠ b in (𝒰 : Filter B), ⊤ ≤ e b ⁻¹ᵁ W) : Γ(X, W) →+* K 𝒰 where
  toFun := gm 𝒰 e W
  map_one' := Germ.coe_eq.2 (h.mono fun _ hb => valR_one _ _ hb)
  map_zero' := Germ.coe_eq.2 (h.mono fun _ hb => valR_zero _ _ hb)
  map_mul' f g := Germ.coe_eq.2 (h.mono fun _ hb => valR_mul _ _ hb f g)
  map_add' f g := Germ.coe_eq.2 (h.mono fun _ hb => valR_add _ _ hb f g)

theorem gm_res {W W' : X.Opens} (i : W' ≤ W) (h : ∀ᶠ b in (𝒰 : Filter B), ⊤ ≤ e b ⁻¹ᵁ W') (f : Γ(X, W)) :
    gm 𝒰 e W' ((X.presheaf.map (homOfLE i).op).hom f) = gm 𝒰 e W f :=
  Germ.coe_eq.2 (h.mono fun _ hb => valR_res _ i hb f)

theorem valR_eq_gm {U : X.Opens} (hU : IsAffineOpen U) (h : ∀ᶠ b in (𝒰 : Filter B), ⊤ ≤ e b ⁻¹ᵁ U)
    (z : Sp (K 𝒰) ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ U) (H : ∀ f, valR z U f = gm 𝒰 e U f) (W : X.Opens) (hW : ⊤ ≤ z ⁻¹ᵁ W) :
    (∀ᶠ b in (𝒰 : Filter B), ⊤ ≤ e b ⁻¹ᵁ W) ∧ ∀ f, valR z W f = gm 𝒰 e W f := by
  obtain ⟨g, hgW, hg⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (le_preimage_iff z W).1 hW⟩
    ((le_preimage_iff z U).1 hz)
  have hzg : ⊤ ≤ z ⁻¹ᵁ X.basicOpen g := (le_preimage_iff z _).2 hg
  have hu : gm 𝒰 e U g ≠ 0 := H g ▸ ((le_preimage_basicOpen_iff z hz g).1 hzg).ne_zero
  have hne : ∀ᶠ b in (𝒰 : Filter B), ¬ valR (e b) U g = 0 :=
    Ultrafilter.eventually_not.2 fun h0 => hu (Germ.coe_eq.2 h0)
  have hb : ∀ᶠ b in (𝒰 : Filter B), ⊤ ≤ e b ⁻¹ᵁ X.basicOpen g := by
    filter_upwards [h, hne] with b h1 h2 using (le_preimage_basicOpen_iff _ h1 g).2 (IsUnit.mk0 _ h2)
  refine ⟨hb.mono fun b => le_preimage_mono _ hgW, fun f => ?_⟩
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g ((X.presheaf.map (homOfLE hgW).op).hom f)
  have ha' : (X.presheaf.map (homOfLE hgW).op).hom f *
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ n =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom a := ha
  have e₁ := congrArg (valR z _) ha'
  rw [valR_mul _ _ hzg, valR_pow _ _ hzg, valR_res _ _ hzg, valR_res _ _ hzg, valR_res _ _ hzg, H, H] at e₁
  have e₂ := congrArg (gmHom 𝒰 e _ hb) ha'
  rw [map_mul, map_pow] at e₂
  change gm 𝒰 e _ _ * gm 𝒰 e _ _ ^ n = gm 𝒰 e _ _ at e₂
  rw [gm_res 𝒰 e _ hb, gm_res 𝒰 e _ hb, gm_res 𝒰 e _ hb] at e₂
  exact mul_right_cancel₀ (pow_ne_zero n hu) (e₁.trans e₂.symm)

theorem exists_tendsto {R : Type} [CommRing R] (p : X ⟶ Sp R) [IsProper p] (σ : R →+* ℂ)
    (he : ∀ b, e b ≫ p = spMap σ) : ∃ y : Sp ℂ ⟶ X, y ≫ p = spMap σ ∧ Tendsto e 𝒰 (𝓝 y) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => ((U : X.Opens) : Set X))
    (fun U => U.1.isOpen) fun x _ => by
      obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  obtain ⟨⟨U, hU⟩, -, h⟩ := (Ultrafilter.eventually_exists_mem_iff (f := 𝒰) (is := (t : Set X.affineOpens))
    (P := fun U b => ⊤ ≤ e b ⁻¹ᵁ U.1) t.finite_toSet).1 (Eventually.of_forall fun b => by
      obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (e b (IsLocalRing.closedPoint ℂ))))
      exact ⟨U, hU, (le_preimage_iff _ _).2 hx⟩)
  let φ : Γ(X, U) ⟶ CommRingCat.of (K 𝒰) := CommRingCat.ofHom (gmHom 𝒰 e U h)
  let z : Sp (K 𝒰) ⟶ X := Spec.map φ ≫ IsAffineOpen.fromSpec hU
  have hz : ⊤ ≤ z ⁻¹ᵁ U := le_preimage_specMap_fromSpec hU φ
  have H : ∀ f, valR z U f = gm 𝒰 e U f := fun f => by
    rw [valR_eq z U hz, valMap_specMap_fromSpec hU φ hz]; rfl
  have hw : z ≫ p = spMap (algebraMap (V 𝒰) (K 𝒰)) ≫ spMap ((cst 𝒰).comp σ) := by
    rw [← Spec.map_comp, ← Spec.map_preimage (z ≫ p)]
    congr 1
    ext a
    refine (valR_constFn p z U hz a).symm.trans ((H _).trans ?_)
    exact Germ.coe_eq.2 (h.mono fun b hb => valR_constFn_of_over p σ _ (he b) U hb a)
  have hex : ValuativeCriterion.Existence p :=
    (UniversallyClosed.eq_valuativeCriterion.le _ _ p inferInstance).1
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Sp (V 𝒰) ⟶ X, spMap (algebraMap (V 𝒰) (K 𝒰)) ≫ l = z ∧
      l ≫ p = spMap ((cst 𝒰).comp σ) := by
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hex
      { R := V 𝒰, K := K 𝒰, i₁ := z, i₂ := spMap ((cst 𝒰).comp σ), commSq := ⟨hw⟩ }).exists_lift
    exact ⟨l, hl₁, hl₂⟩
  refine ⟨spMap (st 𝒰) ≫ l, ?_, tendsto_iff.2 fun W hW => ?_⟩
  · rw [Category.assoc, hl₂, ← Spec.map_comp]
    congr 1
    ext a
    exact st_cst 𝒰 _
  · have hl : ⊤ ≤ l ⁻¹ᵁ W := by
      have h₁ : l (spMap (st 𝒰) (IsLocalRing.closedPoint ℂ)) ∈ W := (le_preimage_iff _ W).1 hW
      have h₂ : spMap (st 𝒰) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint (V 𝒰) :=
        IsLocalRing.comap_closedPoint (st 𝒰)
      exact (le_preimage_iff l W).2 (h₂ ▸ h₁)
    have hzW : ⊤ ≤ z ⁻¹ᵁ W := hl₁ ▸ fun s _ => hl (Set.mem_univ _)
    obtain ⟨h₁, h₂⟩ := valR_eq_gm 𝒰 e hU h z hz H W hzW
    refine ⟨h₁, fun f => ?_⟩
    have h₃ := tendsto_st 𝒰 (valR l W f)
    rw [← valR_spMap_comp (st 𝒰) l W hl] at h₃
    have h₄ := valR_spMap_comp (algebraMap (V 𝒰) (K 𝒰)) l W hl f
    rw [hl₁, h₂] at h₄
    have h₅ : ((valR l W f : V 𝒰) : K 𝒰) = gm 𝒰 e W f := h₄.symm
    rw [h₅] at h₃
    exact h₃

theorem compactSpace_of_isProper {R : Type} [CommRing R] (p : X ⟶ Sp R) [IsProper p] (σ : R →+* ℂ) :
    CompactSpace (PtsOver p (spMap σ)) :=
  ⟨isCompact_iff_ultrafilter_le_nhds.2 fun 𝒰 _ => by
    obtain ⟨y, hy, h⟩ := exists_tendsto 𝒰 (fun b : PtsOver p (spMap σ) => b.1) p σ fun b => b.2
    exact ⟨⟨y, hy⟩, trivial, (tendsto_subtype_rng (f := id) (x := ⟨y, hy⟩)).2 h⟩⟩

end DifferentiableLines.Cpt
