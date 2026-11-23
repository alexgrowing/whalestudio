import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.NatCastPowLePowOfExponentLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FgChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FChars
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GChmap

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem level_field {n h : ℕ} {k G : Type} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ) (hχ : MultFree χ h)
    (U : OpenNormalSubgroup G) : ∃ s : Finset G, s.card ≤ finBound n h ∧ ∀ y : MonoidAlgebra k G,
      ∃ z ∈ Submodule.span k ((fun g => MonoidAlgebra.single g (1 : k)) '' (s : Set G)),
        y - z ∈ TwoSidedIdeal.span ((GDet.ofChars χ).CH ∪ {z | ∃ u ∈ U, z = MonoidAlgebra.single u 1 - 1}) := by
  classical
  have ho : IsOpen ((U : Set G) ∩ ⋂ i, ((χ i).ker : Set G)) :=
    U.toOpenSubgroup.isOpen.inter (isOpen_iInter_of_finite hχ.isOpen)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    ⟨one_mem U, Set.mem_iInter.2 fun i => one_mem (χ i).ker⟩
  obtain ⟨π, hπs, hπg, hπk, hπc⟩ := f_chars χ hχ.inj
  set D := GDet.ofChars χ with hD
  let J : TwoSidedIdeal (MonoidAlgebra k G) :=
    TwoSidedIdeal.span (D.CH ∪ {z | ∃ u ∈ H, z = MonoidAlgebra.single u 1 - 1})
  let f : MonoidAlgebra k G →ₐ[k] J.ringCon.Quotient := RingCon.mkₐ k J.ringCon
  have hk : ∀ y, y ∈ D.toDet.ker ↔ D.Kills y := fun y =>
    (d_ker D.toDet y).1.trans (d_toDet D y).2.2.2
  have hJ : J ≤ D.toDet.ker := by
    refine TwoSidedIdeal.span_le.2 ?_
    rintro z (hz | ⟨u, hu, rfl⟩)
    · refine d_ch_ker D.toDet ?_
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span hz
    · refine (hk _).2 ((hπk _).2 ?_)
      funext i
      have : χ i u = 1 := Set.mem_iInter.1 (hH hu).2 i
      simp [hπg, this]
  have hmem : ∀ x, f x = 0 ↔ x ∈ J := fun x => by
    rw [← map_zero f]
    exact (RingCon.eq _)
  have hsurj : Function.Surjective f := fun q => Quotient.exists_rep q
  obtain ⟨DE, hDE, -⟩ := d_factor D.toDet f hsurj fun x hx => hJ ((hmem x).1 hx)
  have hCH : DE.IsCH := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := ((d_pull DE f).2.2.2 hsurj).2 y hy
    rw [hDE, d_toDet_CH] at hx
    rw [TwoSidedIdeal.mem_bot, hmem]
    exact TwoSidedIdeal.span_mono Set.subset_union_left hx
  obtain ⟨π', hπ'⟩ : ∃ π' : J.ringCon.Quotient →ₐ[k] (Fin n → k), ∀ x, π' (f x) = π x := by
    refine ⟨RingCon.liftₐ _ π fun x y hxy => ?_, fun x => rfl⟩
    have := (hπk _).1 ((hk _).1 (hJ ((TwoSidedIdeal.rel_iff _ _ _).1 hxy)))
    rwa [map_sub, sub_eq_zero] at this
  let ρ : G →* J.ringCon.Quotient := f.toMonoidHom.comp (MonoidAlgebra.of k G)
  have hρ : ∀ g, ρ g = f (MonoidAlgebra.single g 1) := fun g => rfl
  have hker : H.toSubgroup ≤ ρ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker, hρ, ← sub_eq_zero, ← map_one f, ← map_sub, hmem]
    exact TwoSidedIdeal.subset_span (Or.inr ⟨u, hu, rfl⟩)
  have hopen : IsOpen (ρ.ker : Set G) := Subgroup.isOpen_mono hker H.toOpenSubgroup.isOpen
  have hspan : Submodule.span k (Set.range ρ) = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨x, rfl⟩ := hsurj q
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem (ha trivial) (hb trivial)
    | single g a =>
      have : MonoidAlgebra.single g a = a • MonoidAlgebra.single g (1 : k) := by simp
      rw [this, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  have hfr : (Set.range ρ).Finite := by
    haveI : Finite (G ⧸ ρ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
    refine (Set.finite_range (QuotientGroup.lift ρ.ker ρ le_rfl)).subset ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨(g : G ⧸ ρ.ker), rfl⟩
  haveI : Module.Finite k J.ringCon.Quotient := ⟨hspan ▸ Submodule.fg_span hfr⟩
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]; infer_instance
  obtain ⟨-, e, he, hπe⟩ := f_gma DE π' hCH (fun v => by
      obtain ⟨x, rfl⟩ := hπs v; exact ⟨f x, hπ' x⟩) (fun q => by
      obtain ⟨x, rfl⟩ := hsurj q
      rw [← (d_pull DE f).1, hDE, (d_toDet D x).1, hπc, hπ']
      simp)
  have hfin := f_cot χ ρ e π' hχ hopen hspan (fun g i => by rw [hρ, hπ', hπg]) he.idem hπe
    (fun i x => ⟨_, (d_corner DE (e i) hCH (he.idem.idem i) (he.rank i) (Nat.one_le_of_lt i.2 )).1 x⟩)
  obtain ⟨c, hc, hcs, -⟩ := Submodule.exists_fun_fin_finrank_span_eq k (Set.range ρ)
  choose g hg using hc
  refine ⟨Finset.univ.image g, Finset.card_image_le.trans ?_, fun y => ?_⟩
  · rw [Finset.card_univ, Fintype.card_fin, hspan, finrank_top]
    exact hfin
  · have h1 : f y ∈ (Submodule.span k ((fun g => MonoidAlgebra.single g (1 : k)) ''
        ((Finset.univ.image g : Finset G) : Set G))).map f.toLinearMap := by
      have : f y ∈ Submodule.span k (Set.range c) := by rw [hcs, hspan]; trivial
      refine Submodule.span_le.2 ?_ this
      rintro _ ⟨i, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨g i, by simp, rfl⟩, hg i⟩
    obtain ⟨z, hz, hzy⟩ := h1
    refine ⟨z, hz, ?_⟩
    have h2 : y - z ∈ J := by
      rw [← hmem, map_sub, sub_eq_zero]; exact hzy.symm
    refine TwoSidedIdeal.span_mono ?_ h2
    rintro w (hw | ⟨u, hu, rfl⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨u, (hH hu).1, rfl⟩

theorem UpperTheory.V.CA.f_level :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → ∀ (N : ℕ) (U : OpenNormalSubgroup G), ∃ s : Finset G, s.card ≤ finBound n h ∧ ∀ y : MonoidAlgebra B G, ∃ z ∈ Submodule.span B ((fun g => MonoidAlgebra.single g (1 : B)) '' (s : Set G)), y - z ∈ TwoSidedIdeal.span (D.CH ∪ {z | ∃ a ∈ maximalIdeal B ^ N, z = MonoidAlgebra.single 1 a} ∪ {z | ∃ u ∈ U, z = MonoidAlgebra.single u 1 - 1}) := by
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ _ hD hχ N U
  obtain ⟨s, hs, hy⟩ := level_field χ hχ U
  refine ⟨s, hs, ?_⟩
  set Q := TwoSidedIdeal.span (D.CH ∪ {z | ∃ a ∈ maximalIdeal B ^ N, z = MonoidAlgebra.single 1 a} ∪
    {z : MonoidAlgebra B G | ∃ u ∈ U, z = MonoidAlgebra.single u 1 - 1}) with hQ
  set S := Submodule.span B ((fun g => MonoidAlgebra.single g (1 : B)) '' (s : Set G)) with hS
  let φ := MonoidAlgebra.mapRingHom G (residue B)
  have hφs : ∀ (b : B) (x : MonoidAlgebra B G), φ (b • x) = residue B b • φ x := by
    intro b x; ext g; simp [φ]
  have hφ : Function.Surjective φ := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | single g a =>
      obtain ⟨a, rfl⟩ := residue_surjective a
      exact ⟨MonoidAlgebra.single g a, MonoidAlgebra.mapRingHom_single _ _ _⟩
  have lift : ∀ T : Set (MonoidAlgebra (ResidueField B) G), (∀ w ∈ T, ∃ x ∈ Q, φ x = w) →
      ∀ w ∈ TwoSidedIdeal.span T, ∃ x ∈ Q, φ x = w := by
    intro T hT w hw
    induction hw using TwoSidedIdeal.span_induction with
    | mem x hx => exact hT x hx
    | zero => exact ⟨0, Q.zero_mem, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Q.add_mem ha hb, map_add _ _ _⟩
    | neg x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨-a, Q.neg_mem ha, map_neg _ _⟩
    | left_absorb c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hφ c
      exact ⟨c * a, Q.mul_mem_left _ _ ha, map_mul _ _ _⟩
    | right_absorb c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hφ c
      exact ⟨a * c, Q.mul_mem_right _ _ ha, map_mul _ _ _⟩
  let Q' : Submodule B (MonoidAlgebra B G) :=
    { carrier := Q
      add_mem' := Q.add_mem
      zero_mem' := Q.zero_mem
      smul_mem' := fun c x hx => by rw [Algebra.smul_def]; exact Q.mul_mem_left _ _ hx }
  have step : (⊤ : Submodule B (MonoidAlgebra B G)) ≤ (S ⊔ Q') ⊔ maximalIdeal B • ⊤ := by
    intro y _
    obtain ⟨z, hz, hyz⟩ := hy (φ y)
    obtain ⟨x, hx, hxe⟩ := lift _ (by
      rintro w (hw | ⟨u, hu, rfl⟩)
      · refine lift (φ '' D.CH) ?_ w ?_
        · rintro _ ⟨x, hx, rfl⟩
          exact ⟨x, TwoSidedIdeal.subset_span (Or.inl (Or.inl hx)), rfl⟩
        · rw [← g_chmap, hD]
          exact TwoSidedIdeal.subset_span hw
      · exact ⟨_, TwoSidedIdeal.subset_span (Or.inr ⟨u, hu, rfl⟩), by simp [φ]⟩) _ hyz
    obtain ⟨z', hz', rfl⟩ : ∃ z' ∈ S, φ z' = z := by
      clear hyz hxe
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨g, hg, rfl⟩ := hw
        exact ⟨_, Submodule.subset_span ⟨g, hg, rfl⟩, by simp [φ]⟩
      | zero => exact ⟨0, S.zero_mem, map_zero _⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a + b, S.add_mem ha hb, map_add _ _ _⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨c, rfl⟩ := residue_surjective c
        exact ⟨c • a, S.smul_mem c ha, hφs _ _⟩
    have h0 : φ (y - z' - x) = 0 := by rw [map_sub, map_sub, hxe, sub_self]
    have h1 : y - z' - x ∈ maximalIdeal B • (⊤ : Submodule B (MonoidAlgebra B G)) := by
      generalize y - z' - x = w at h0
      rw [← MonoidAlgebra.sum_coeff_single w]
      refine Submodule.sum_mem _ fun g _ => ?_
      have h2 : MonoidAlgebra.single g (w.coeff g) = w.coeff g • MonoidAlgebra.single g (1 : B) := by simp
      have h3 := congrArg (fun v => v.coeff g) h0
      simp only [h2]
      refine Submodule.smul_mem_smul ((residue_eq_zero_iff _).1 ?_) trivial
      simpa [φ] using h3
    have : y = z' + x + (y - z' - x) := by abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hz' hx) h1
  have iter : ∀ j : ℕ, (⊤ : Submodule B (MonoidAlgebra B G)) ≤ (S ⊔ Q') ⊔ maximalIdeal B ^ j • ⊤ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      refine (Submodule.smul_mono le_rfl step).trans ?_
      rw [Submodule.smul_sup, pow_succ, mul_smul]
      exact sup_le_sup_right Submodule.smul_le_right _
  have last : maximalIdeal B ^ N • (⊤ : Submodule B (MonoidAlgebra B G)) ≤ Q' := by
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [Algebra.smul_def]
    exact Q.mul_mem_right _ _ (TwoSidedIdeal.subset_span (Or.inl (Or.inr ⟨a, ha, by simp⟩)))
  intro y
  have : y ∈ S ⊔ Q' := ((iter N).trans (sup_le le_rfl (last.trans le_sup_right))) trivial
  obtain ⟨z, hz, x, hx, rfl⟩ := Submodule.mem_sup.1 this
  exact ⟨z, hz, by rw [add_sub_cancel_left]; exact hx⟩
