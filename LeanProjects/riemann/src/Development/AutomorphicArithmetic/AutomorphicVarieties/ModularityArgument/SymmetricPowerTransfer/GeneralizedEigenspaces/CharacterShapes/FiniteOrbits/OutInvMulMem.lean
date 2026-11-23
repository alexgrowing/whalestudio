import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem dc_right (U : Subgroup G) (a : G) {r s : G} (h : r⁻¹ * s ∈ U) (hr : r ∈ DC U a) :
    s ∈ DC U a := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hr
  refine ⟨u, hu, w * ((u * a * w)⁻¹ * s), U.mul_mem hw h, ?_⟩
  group

private theorem dc_left (U : Subgroup G) (b : G) {c g : G} (h : c ∈ U) (hg : g ∈ DC U b) :
    c * g ∈ DC U b := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hg
  exact ⟨c * u, U.mul_mem h hu, w, hw, by group⟩

private theorem out_inv_mul_mem (U : Subgroup G) (s : G) :
    (Quotient.out (s : G ⧸ U))⁻¹ * s ∈ U :=
  QuotientGroup.eq.1 (QuotientGroup.out_eq' (s : G ⧸ U))

private theorem uf_unique_iff (U : Subgroup G) (a b g : G) :
    (∃! y : G ⧸ U, y.out ∈ DC U a ∧ y.out⁻¹ * g ∈ DC U b) ↔
      ∃ r, (r ∈ DC U a ∧ r⁻¹ * g ∈ DC U b) ∧
        ∀ s, s ∈ DC U a → s⁻¹ * g ∈ DC U b → r⁻¹ * s ∈ U := by
  have hq : ∀ s, s ∈ DC U a → s⁻¹ * g ∈ DC U b →
      (Quotient.out (s : G ⧸ U)) ∈ DC U a ∧ (Quotient.out (s : G ⧸ U))⁻¹ * g ∈ DC U b := by
    intro s hs hs'
    have h1 := out_inv_mul_mem U s
    have h2 : s⁻¹ * Quotient.out (s : G ⧸ U) ∈ U := by
      have := U.inv_mem h1
      simpa using this
    refine ⟨dc_right U a h2 hs, ?_⟩
    have := dc_left U b h1 hs'
    simpa [mul_assoc] using this
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, huniq⟩
    refine ⟨y.out, ⟨hy1, hy2⟩, fun s hs hs' => ?_⟩
    have h3 : (s : G ⧸ U) = y := huniq _ (hq s hs hs')
    have h4 : ((y.out : G) : G ⧸ U) = (s : G ⧸ U) := by
      rw [h3]; exact QuotientGroup.out_eq' y
    exact QuotientGroup.eq.1 h4
  · rintro ⟨r, ⟨hr1, hr2⟩, hall⟩
    refine ⟨(r : G ⧸ U), hq r hr1 hr2, fun y hy => ?_⟩
    have h5 := hall _ hy.1 hy.2
    have h6 : (r : G ⧸ U) = ((y.out : G) : G ⧸ U) := QuotientGroup.eq.2 h5
    rw [h6]
    exact (QuotientGroup.out_eq' y).symm

private theorem reps_of_finOrb (U : Subgroup G) (a : G) (h : AlgebraTools.FinOrb U U a) :
    ∃ R : Finset G, (∀ y ∈ R, y ∈ DC U a) ∧ (∀ y ∈ DC U a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U) := by
  classical
  have hf : (MulAction.orbit U (a : G ⧸ U)).Finite := h
  have hmk : ∀ y ∈ DC U a, (y : G ⧸ U) ∈ MulAction.orbit U (a : G ⧸ U) := by
    rintro y ⟨u, hu, w, hw, rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    show ((u * a : G) : G ⧸ U) = ((u * a * w : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    simpa [mul_assoc] using hw
  refine ⟨hf.toFinset.image (fun q : G ⧸ U => q.out), ?_, ?_⟩
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨u, rfl⟩ := hf.mem_toFinset.1 hq
    have h1 : ((Quotient.out (u • (a : G ⧸ U)) : G) : G ⧸ U) = ((u * a : G) : G ⧸ U) :=
      QuotientGroup.out_eq' _
    have h2 := QuotientGroup.eq.1 h1
    refine ⟨u, u.2, _, U.inv_mem h2, ?_⟩
    group
  · intro y hy
    refine ⟨Quotient.out (y : G ⧸ U), ⟨?_, out_inv_mul_mem U y⟩, ?_⟩
    · exact Finset.mem_image.2 ⟨_, hf.mem_toFinset.2 (hmk y hy), rfl⟩
    · rintro r ⟨hr, hr'⟩
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hr
      have h3 : ((q.out : G) : G ⧸ U) = (y : G ⧸ U) := QuotientGroup.eq.2 hr'
      have h4 : q = (y : G ⧸ U) := (QuotientGroup.out_eq' q).symm.trans h3
      rw [h4]

private theorem finOrb_of_cover (U : Subgroup G) (a : G) (R : Finset G)
    (h : ∀ y ∈ DC U a, ∃ r ∈ R, r⁻¹ * y ∈ U) : AlgebraTools.FinOrb U U a := by
  classical
  refine (R.image (fun r : G => (r : G ⧸ U))).finite_toSet.subset ?_
  rintro q ⟨u, rfl⟩
  obtain ⟨r, hr, hr'⟩ := h ((u : G) * a) ⟨u, u.2, 1, U.one_mem, by simp⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨r, hr, ?_⟩)
  exact QuotientGroup.eq.2 hr'

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcMap :
    UpperTheory.V.Z.Sym.So.DcMap := by
  classical
  intro G G' V _ _ _ _ e he U' a b
  set U := U'.comap e with hU
  set inv : G' → G := Function.surjInv he.2 with hinv
  have einv : ∀ x, e (inv x) = x := Function.surjInv_eq he.2
  have hDC : ∀ c g : G, g ∈ DC U c ↔ e g ∈ DC U' (e c) := by
    intro c g
    constructor
    · rintro ⟨u, hu, w, hw, rfl⟩
      exact ⟨e u, hu, e w, hw, by simp⟩
    · rintro ⟨u, hu, w, hw, h⟩
      refine ⟨inv u, ?_, inv w, ?_, he.1 ?_⟩
      · show e (inv u) ∈ U'
        rwa [einv]
      · show e (inv w) ∈ U'
        rwa [einv]
      · simp [einv, h]
  have hmem : ∀ x y : G, x⁻¹ * y ∈ U ↔ (e x)⁻¹ * e y ∈ U' := by
    intro x y
    show e (x⁻¹ * y) ∈ U' ↔ _
    simp
  have hfin : AlgebraTools.FinOrb U U a ↔ AlgebraTools.FinOrb U' U' (e a) := by
    constructor
    · intro h
      obtain ⟨R, -, hR⟩ := reps_of_finOrb U a h
      refine finOrb_of_cover U' (e a) (R.image e) fun y' hy' => ?_
      have hy : inv y' ∈ DC U a := (hDC a _).2 (by rwa [einv])
      obtain ⟨r, ⟨hr, hr'⟩, -⟩ := hR _ hy
      refine ⟨e r, Finset.mem_image_of_mem _ hr, ?_⟩
      have := (hmem _ _).1 hr'
      rwa [einv] at this
    · intro h
      obtain ⟨R, -, hR⟩ := reps_of_finOrb U' (e a) h
      refine finOrb_of_cover U a (R.image inv) fun y hy => ?_
      obtain ⟨r, ⟨hr, hr'⟩, -⟩ := hR _ ((hDC a y).1 hy)
      refine ⟨inv r, Finset.mem_image_of_mem _ hr, (hmem _ _).2 ?_⟩
      rwa [einv]
  refine ⟨hDC a, hfin, ?_, ?_⟩
  · have hQ : ∀ g : G, (∃! y : G ⧸ U, y.out ∈ DC U a ∧ y.out⁻¹ * g ∈ DC U b) ↔
        ∃! y : G' ⧸ U', y.out ∈ DC U' (e a) ∧ y.out⁻¹ * e g ∈ DC U' (e b) := by
      intro g
      rw [uf_unique_iff, uf_unique_iff]
      have hin : ∀ (r : G), (r ∈ DC U a ∧ r⁻¹ * g ∈ DC U b) ↔
          (e r ∈ DC U' (e a) ∧ (e r)⁻¹ * e g ∈ DC U' (e b)) := by
        intro r
        rw [hDC a r, hDC b (r⁻¹ * g)]
        simp
      constructor
      · rintro ⟨r, hr, hall⟩
        refine ⟨e r, (hin r).1 hr, fun s' h1 h2 => ?_⟩
        have h3 := (hin (inv s')).2 (by rw [einv]; exact ⟨h1, h2⟩)
        have := (hmem _ _).1 (hall _ h3.1 h3.2)
        rwa [einv] at this
      · rintro ⟨r', hr', hall⟩
        have h0 := (hin (inv r')).2 (by rw [einv]; exact hr')
        refine ⟨inv r', h0, fun s h1 h2 => (hmem _ _).2 ?_⟩
        have h3 := (hin s).1 ⟨h1, h2⟩
        rw [einv]
        exact hall _ h3.1 h3.2
    have hR : ∀ g y : G, (y ∈ DC U a → y⁻¹ * g ∈ DC U b → g ∈ DC U (a * b)) ↔
        (e y ∈ DC U' (e a) → (e y)⁻¹ * e g ∈ DC U' (e b) → e g ∈ DC U' (e a * e b)) := by
      intro g y
      rw [hDC a y, hDC b (y⁻¹ * g), hDC (a * b) g]
      simp
    constructor
    · intro h g'
      have hg : e (inv g') = g' := einv g'
      obtain ⟨h1, h2⟩ := h (inv g')
      rw [← hg]
      refine ⟨fun hm => (hQ _).1 (h1 ((hDC _ _).2 (by simpa using hm))), fun y' hy1 hy2 => ?_⟩
      have := (hR (inv g') (inv y')).1 (h2 _)
      rw [einv] at this
      exact this hy1 hy2
    · intro h g
      obtain ⟨h1, h2⟩ := h (e g)
      refine ⟨fun hm => (hQ g).2 (h1 (by simpa using (hDC _ _).1 hm)), fun y hy1 hy2 => ?_⟩
      exact (hR g y).2 (h2 (e y)) hy1 hy2
  · intro hf φ hφ
    obtain ⟨R', hR1', hR2'⟩ := reps_of_finOrb U' (e a) hf
    have hφe : ∀ u ∈ U, ∀ g, (φ ∘ e) (g * u) = (φ ∘ e) g := by
      intro u hu g
      simp only [Function.comp_apply, map_mul]
      exact hφ _ hu _
    have hinj : Set.InjOn inv (R' : Set G') := fun x _ y _ h => by
      rw [← einv x, ← einv y, h]
    have hR1 : ∀ y ∈ R'.image inv, y ∈ DC U a := by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      exact (hDC a _).2 (by rw [einv]; exact hR1' r hr)
    have hR2 : ∀ y ∈ DC U a, ∃! r, r ∈ R'.image inv ∧ r⁻¹ * y ∈ U := by
      intro y hy
      obtain ⟨r, ⟨hr, hr'⟩, huniq⟩ := hR2' _ ((hDC a y).1 hy)
      refine ⟨inv r, ⟨Finset.mem_image_of_mem _ hr, (hmem _ _).2 (by rwa [einv])⟩, ?_⟩
      rintro s ⟨hs, hs'⟩
      obtain ⟨s', hs1, rfl⟩ := Finset.mem_image.1 hs
      have := (hmem _ _).1 hs'
      rw [einv] at this
      rw [huniq s' ⟨hs1, this⟩]
    funext g
    rw [(dcBasic G V U a (hfin.2 hf) (φ ∘ e) hφe).2.2.2.2 _ hR1 hR2 g, Function.comp_apply,
      (dcBasic G' V U' (e a) hf φ hφ).2.2.2.2 R' hR1' hR2' (e g), Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [einv]

end
