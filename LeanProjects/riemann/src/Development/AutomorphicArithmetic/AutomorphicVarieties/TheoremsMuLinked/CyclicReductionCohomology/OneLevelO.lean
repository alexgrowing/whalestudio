import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedOneAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LocSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.CountFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LcOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CCount

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem natL (ZL B' M V U J A S' PV PU PJ K a b c1 c2 e f Sel B ci : ℕ) (hB : 0 < B') (hM : 0 < M)
    (h1 : ZL * B' * M ^ (V + (U + J)) * A ≤ M * S' * (PV * (PU * PJ))) (h2 : S' ≤ B' * K ^ c2)
    (h3 : PV * K ^ a ≤ M ^ V * K ^ e) (h4 : PU ≤ M ^ U) (h5 : PJ ≤ M ^ J * K ^ f) (h6 : K ^ b ≤ A)
    (h7 : Sel * B ≤ ZL) (h8 : B * ci = M) (h9 : ci ≤ K ^ c1) :
    Sel * K ^ (a + b) ≤ K ^ (c1 + c2 + e + f) := by
  have k1 : ZL * K ^ (a + b) * (B' * M ^ (V + (U + J))) ≤ M * K ^ (c2 + e + f) * (B' * M ^ (V + (U + J))) := by
    calc ZL * K ^ (a + b) * (B' * M ^ (V + (U + J))) = ZL * B' * M ^ (V + (U + J)) * K ^ b * K ^ a := by ring
      _ ≤ ZL * B' * M ^ (V + (U + J)) * A * K ^ a := by gcongr
      _ ≤ M * S' * (PV * (PU * PJ)) * K ^ a := by gcongr
      _ = M * S' * (PV * K ^ a) * PU * PJ := by ring
      _ ≤ M * (B' * K ^ c2) * (M ^ V * K ^ e) * M ^ U * (M ^ J * K ^ f) := by gcongr
      _ = M * K ^ (c2 + e + f) * (B' * M ^ (V + (U + J))) := by ring
  have k2 : ZL * K ^ (a + b) ≤ M * K ^ (c2 + e + f) := Nat.le_of_mul_le_mul_right k1 (by positivity)
  have hB0 : 0 < B := Nat.pos_of_mul_pos_right (h8 ▸ hM : 0 < B * ci)
  refine Nat.le_of_mul_le_mul_right (c := B) ?_ hB0
  calc Sel * K ^ (a + b) * B = Sel * B * K ^ (a + b) := by ring
    _ ≤ ZL * K ^ (a + b) := by gcongr
    _ ≤ B * ci * K ^ (c2 + e + f) := by rw [h8]; exact k2
    _ ≤ B * K ^ c1 * K ^ (c2 + e + f) := by gcongr
    _ = K ^ (c1 + c2 + e + f) * B := by ring

private theorem block_le₂ {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (h : LC ρ) : (Bl ρ).toAddSubgroup ≤ (Zl ρ).toAddSubgroup := by
  intro z hz
  obtain ⟨m, hm⟩ := (mem_Bl ρ).1 hz
  have : z = fun g => ρ g m - m := funext hm
  subst this
  refine (mem_Zl ρ).2 ⟨(h m).comp (fun y => y - m), fun g g' => ?_⟩
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

private theorem lc_comp {R Γ D M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group D] [TopologicalSpace D]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (h : LC ρ) (φ : D →* Γ) (hφ : Continuous φ) :
    LC (ρ.comp φ : Representation R D M) := fun m => (h m).comp_continuous hφ

private theorem zl_comp {R Γ D M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group D] [TopologicalSpace D]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (φ : D →* Γ) (hφ : Continuous φ) {z : Γ → M}
    (hz : z ∈ Zl ρ) : z ∘ φ ∈ Zl (ρ.comp φ : Representation R D M) :=
  ⟨hz.1.comp_continuous hφ, fun g g' => by simp [hz.2]⟩

theorem UpperTheory.V.Th.oneLevelO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (q d : ℕ) (a : ArData G q d) (rep rep' : Representation O G.Γ (Mm O n m)) (e : L.Vl → ℕ) (f : Option (Fin q) → ℕ) (c₁ c₂ : ℕ), l ≠ 2 → Cnts a → IsAd0 h y m rep → IsAd1 h y m rep' → (∀ v, Finite (Zbor y m v) ∧ Nat.card (Zbor y m v) ≤ Nat.card (ResidueField O) ^ e v) → (∀ j, Nat.card (Representation.invariants (rep'.comp (a.ι (.inr (.inr j))) : Representation O (a.D (.inr (.inr j))) _)) ≤ Nat.card (ResidueField O) ^ f j) → Nat.card rep.invariants ≤ Nat.card (ResidueField O) ^ c₁ → (Finite (Zl rep') → {z | z ∈ Zl rep' ∧ ∀ j : Fin q, z ∘ a.ι (.inr (.inr (some j))) ∈ Bl (rep'.comp (a.ι (.inr (.inr (some j)))) : Representation O (a.D (.inr (.inr (some j)))) _)}.ncard ≤ Nat.card (Bl rep') * Nat.card (ResidueField O) ^ c₂) → (trFun h y m '' Sel h y m).Finite ∧ (trFun h y m '' Sel h y m).ncard * Nat.card (ResidueField O) ^ (m * (n + n.choose 2) * Fintype.card L.Vl + m * n.choose 2 * d) ≤ Nat.card (ResidueField O) ^ (c₁ + c₂ + ∑ v, e v + ∑ j, f j) := by
  intro l _ L G G0 h O _ _ _ _ _ n y m q d a rep rep' e f c₁ c₂ hl hC hrep hrep' hZb hf hc1 hc2
  classical
  obtain ⟨h2, hOm⟩ := omFacts l O
  obtain ⟨hfD, -, hlD, -⟩ := hOm m
  haveI := hfD
  haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))
  obtain ⟨k, b, hk, hb⟩ := pairP l L G G0 h O n y m a.c_ε
  have hb := hb rep rep' hrep hrep'
  have hLC : LC rep := (adExP l L G G0 h O n y m).2.2 rep (Or.inl hrep)
  have hι : ∀ w, Continuous (a.ι w) := by
    rintro (v | u | j)
    · exact continuous_subtype_val.comp (G.φ_cont v)
    · exact continuous_subtype_val.comp (G.φu_cont u)
    · exact continuous_subtype_val.comp (a.φq_cont j)
  have hLCw : ∀ w, LC (rep.comp (a.ι w) : Representation O (a.D w) _) := fun w => lc_comp rep hLC _ (hι w)
  have hpu : ∀ u g, h.p₀ (G.φu u g) = G0.φu u g := fun u g => Subtype.ext (h.φu u g)
  have hρ : ∀ u, ∀ g ∈ L.Ju u, y.ρm h m (G.φu u g) = 1 := fun u g hg => by
    have h1 : y.ρ (G0.φu u g) = 1 := y.ine u _ ⟨g, hg, rfl⟩
    have h3 : mat y.ρ (G0.φu u g) = 1 := congrArg Units.val h1
    rw [Pt.ρm, hpu, h3, red]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hu : ∀ u, ∀ g ∈ L.Ju u, rep (G.φu u g : G.Γ) = 1 := fun u g hg => by
    refine LinearMap.ext fun Z => ?_
    have := hrep.1 (G.φu u g) Z
    have e1 := hρ u g⁻¹ (inv_mem hg)
    rw [map_inv] at e1
    rw [hρ u g hg, one_smul, one_mul] at this
    exact this.trans ((congrArg (Z * ·) e1).trans (mul_one Z))
  let 𝓛 : ∀ w, AddSubgroup (a.D w → Mm O n m) := fun w => match w with
    | .inl v => (Bl (rep.comp (a.ι (.inl v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v
    | .inr (.inl u) => (Zl (rep.comp (a.ι (.inr (.inl u))) : Representation O (L.Gu u) _)).toAddSubgroup ⊓
        AddSubgroup.pi (L.Ju u : Set (L.Gu u)) (fun _ => ⊥)
    | .inr (.inr j) => (Zl (rep.comp (a.ι (.inr (.inr j))) : Representation O (a.Dq j) _)).toAddSubgroup
  have hloc := fun v => locSup l L G G0 h O n y m rep v hrep hLC (hZb v).1
  have h𝓛 : ∀ w, (Bl (rep.comp (a.ι w) : Representation O (a.D w) _)).toAddSubgroup ≤ 𝓛 w ∧
      𝓛 w ≤ (Zl (rep.comp (a.ι w) : Representation O (a.D w) _)).toAddSubgroup := by
    rintro (v | u | j)
    · exact ⟨le_sup_left, (hloc v).1⟩
    · refine ⟨le_inf (block_le₂ _ (hLCw _)) fun z hz g hg => ?_, inf_le_left⟩
      obtain ⟨Y, hy⟩ := (mem_Bl _).1 hz
      have e1 : rep (G.φu u g : G.Γ) Y - Y = 0 := by rw [hu u g hg]; simp
      exact AddSubgroup.mem_bot.2 ((hy g).trans e1)
    · exact ⟨block_le₂ _ (hLCw _), le_rfl⟩
  obtain ⟨hF, hF', hgw⟩ := hC.gw k hk O _ _ rep rep' b hLC hb 𝓛 h𝓛
  obtain ⟨hS1, hS2⟩ := selTr l L G G0 h O n y m rep hrep hLC hF
  have hS3 := (cCount O G.Γ (Mm O n m) rep G.c G.c_sq (h2 hl)).2.1
  refine ⟨hS1, ?_⟩
  have hFs : (Zl rep : Set (G.Γ → Mm O n m)).Finite := Set.toFinite _
  have hFs' : (Zl rep' : Set (G.Γ → Mm O n m)).Finite := Set.toFinite _
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.card_sum, Fintype.card_sum] at hgw
  haveI : Finite (Bl rep') := Finite.of_surjective _ (LinearMap.surjective_rangeRestrict _)
  refine natL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Nat.card_pos Nat.card_pos hgw ?_ ?_ ?_ ?_ ?_
    (hS2.trans ?_) hS3 hc1
  · refine le_trans (Set.ncard_le_ncard ?_ (hFs'.subset fun y hy => hy.1)) (hc2 hF')
    exact fun y hy => ⟨hy.1, fun j => hy.2 _ rfl⟩
  · rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun v _ => ?_
    exact le_trans (hloc v).2.2 (Nat.mul_le_mul_left _ (hZb v).2)
  · rw [← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod' fun u _ => ?_
    have := (hC.unr u m O _ (rep.comp (a.ι (.inr (.inl u)))) (hLCw _) (fun Y => Matrix.ext fun i j => hlD (Y i j)) (hu u)).2
    rw [← Nat.card_coe_set_eq] at this
    exact this
  · rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun j _ => ?_
    have := (hC.locQ j k hk O _ _ (rep.comp (a.ι (.inr (.inr j)))) (rep'.comp (a.ι (.inr (.inr j)))) b (hLCw _)
      ⟨hb.left, hb.right, fun g y z => hb.equiv _ y z⟩).2
    rw [add_zero, pow_one] at this
    exact this.le.trans (Nat.mul_le_mul_left _ (hf j))
  · rw [pow_mul]
    conv_lhs => rw [← Fintype.card_fin d, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun i _ =>
      pow_choose_two_le_card_fixed_ad0_of_odd_involution l L G G0 h O n y m rep _ hl hrep (a.cw_sq i) (a.cw_η i)
  · refine Set.ncard_le_ncard ?_ (hFs.subset fun y hy => hy.1)
    rintro z ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    rintro (v | u | j)
    · exact h2 v
    · exact ⟨zl_comp rep _ (hι _) h1, fun g hg => h3 u g hg⟩
    · exact zl_comp rep _ (hι _) h1
