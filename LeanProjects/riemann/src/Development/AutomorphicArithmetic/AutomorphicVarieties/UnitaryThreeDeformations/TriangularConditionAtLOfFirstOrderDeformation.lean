import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] {m : Ideal R}

private def Kil (m : Ideal R) (X : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, ∀ x ∈ m, x * X a b = 0

private theorem kil_left {X M : Matrix (Fin 3) (Fin 3) R} (hX : Kil m X) (hM : EntIn m M) : M * X = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => hX c b _ (hM a c)

private theorem kil_right {X M : Matrix (Fin 3) (Fin 3) R} (hX : Kil m X) (hM : EntIn m M) : X * M = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact hX a c _ (hM c b)

private theorem ent_left {M : Matrix (Fin 3) (Fin 3) R} (N : Matrix (Fin 3) (Fin 3) R) (hM : EntIn m M) :
    EntIn m (N * M) := fun a b => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hM c b)

private theorem ent_right {M : Matrix (Fin 3) (Fin 3) R} (N : Matrix (Fin 3) (Fin 3) R) (hM : EntIn m M) :
    EntIn m (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hM a c)

private theorem core {h hi A D Y γ : Matrix (Fin 3) (Fin 3) R} (hh : EntIn m (h - 1)) (hhi : EntIn m (hi - 1))
    (hA : EntIn m (A - D)) (hY : Kil m Y) (hYm : EntIn m Y) (hγ : Kil m γ) :
    hi * (1 + Y) * ((1 + γ) * A) * ((1 - Y) * h) = hi * A * h + (Y * D + γ * D - D * Y) := by
  obtain ⟨p, rfl⟩ : ∃ p, h = 1 + p := ⟨h - 1, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, hi = 1 + q := ⟨hi - 1, by abel⟩
  obtain ⟨e, rfl⟩ : ∃ e, A = D + e := ⟨A - D, by abel⟩
  simp only [add_sub_cancel_left] at hh hhi hA
  have e1 : (1 + Y) * ((1 + γ) * (D + e)) * (1 - Y) = (D + e) + (Y * D + γ * D - D * Y) := by
    have a1 : Y * γ = 0 := kil_left hγ hYm
    have a2 : Y * e = 0 := kil_right hY hA
    have a3 : γ * e = 0 := kil_right hγ hA
    have a4 : e * Y = 0 := kil_left hY hA
    have a5 : Y * (D * Y) = 0 := kil_right hY (ent_left _ hYm)
    have a6 : γ * (D * Y) = 0 := kil_right hγ (ent_left _ hYm)
    have : (1 + Y) * ((1 + γ) * (D + e)) * (1 - Y) = (D + e) + (Y * D + γ * D - D * Y) +
        ((Y * γ) * (D + e) * (1 - Y) + (Y * e) * (1 - Y) + (γ * e) * (1 - Y) - e * Y - Y * (D * Y) - γ * (D * Y)) := by
      noncomm_ring
    rw [this, a1, a2, a3, a4, a5, a6]; simp
  have hW : Kil m (Y * D + γ * D - D * Y) := fun a b x hx => by
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, mul_sub, mul_add, Finset.mul_sum,
      ← mul_assoc, hY _ _ x hx, hγ _ _ x hx, zero_mul, hY _ _ _ (Ideal.mul_mem_right _ _ hx)]
    simp
  generalize Y * D + γ * D - D * Y = W at e1 hW
  have b1 : q * W = 0 := kil_left hW hhi
  have b2 : W * p = 0 := kil_right hW hh
  calc _ = (1 + q) * ((1 + Y) * ((1 + γ) * (D + e)) * (1 - Y)) * (1 + p) := by simp only [Matrix.mul_assoc]
    _ = (1 + q) * (D + e) * (1 + p) + W + ((q * W) * (1 + p) + W * p) := by rw [e1]; noncomm_ring
    _ = _ := by rw [b1, b2]; simp

private theorem conj_mat {D : Type} [Group D] (h : GL (Fin 3) R) (r : D →* GG 3 R) (g : D) (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem ad_entry {D k : Type} [Group D] [CommRing k] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (hg : η g = 1)
    (X : Matrix (Fin 3) (Fin 3) k) (a b : Fin 3) :
    adRep (r0 η Ψ) g X a b * ((Ψ g ^ wt1 b : kˣ) : k) = ((Ψ g ^ wt1 a : kˣ) : k) * X a b := by
  show (GG.adFun (r0 η Ψ g) X) a b * _ = _
  unfold GG.adFun GG.mat
  rw [unitaryThreeReflection_left, ← map_inv, tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul, unitaryThreeReflection_right, if_pos hg,
    mul_assoc, ← Units.val_mul, ← mul_zpow]
  simp

private theorem condT_deform {O D : Type} [CommRing O] [IsLocalRing O] [Group D] [Algebra O R] [IsCO O R]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (f : R) (hf : ∀ x ∈ maximalIdeal R, x * f = 0)
    (hfm : f ∈ maximalIdeal R) (r r₂ : D →* GG 3 R) (z : D → Matrix (Fin 3) (Fin 3) (ResidueField O))
    (γ : D → Matrix (Fin 3) (Fin 3) R) (hr : Red η Ψ r) (ht : CondT η Ψ I r)
    (hγ : ∀ g a b, ∃ o : O, residue O o = z g a b ∧ γ g a b = o • f) (hd : IsDeform r γ r₂)
    (μ : Matrix (Fin 3) (Fin 3) (ResidueField O))
    (h1 : ∀ g, η g = 1 → ∀ a b, wt a b < 0 →
      μ a b * residue O (psi Ψ b g) + z g a b * residue O (psi Ψ b g) - residue O (psi Ψ a g) * μ a b = 0)
    (h2 : ∀ s ∈ I, ∀ a, z s a a = 0) : CondT η Ψ I r₂ := by
  obtain ⟨h, hh, htri, hine⟩ := ht
  have hk : ∀ o : O, ∀ x ∈ maximalIdeal R, x * (o • f) = 0 := fun o x hx => by
    rw [mul_smul_comm, hf x hx, smul_zero]
  have h0 : ∀ o : O, residue O o = 0 → o • f = 0 := fun o ho => by
    rw [Algebra.smul_def]
    exact hf _ (map_nonunit (algebraMap O R) o ((residue_eq_zero_iff _).1 ho))
  choose o ho using fun a b => residue_surjective (μ a b)
  let Y : Matrix (Fin 3) (Fin 3) R := Matrix.of fun a b => o a b • f
  have hY : Kil (maximalIdeal R) Y := fun a b => hk _
  have hYm : EntIn (maximalIdeal R) Y := fun a b => Submodule.smul_of_tower_mem _ _ hfm
  have hYY : Y * Y = 0 := kil_left hY hYm
  let u : GL (Fin 3) R := ⟨1 - Y, 1 + Y,
    by rw [show (1 - Y) * (1 + Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero],
    by rw [show (1 + Y) * (1 - Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero]⟩
  have hhi : EntIn (maximalIdeal R) (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1) := by
    have := ent_left (-((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) hh
    rwa [Matrix.mul_sub, Matrix.neg_mul, Units.inv_mul, Matrix.mul_one, sub_neg_eq_add, neg_add_eq_sub] at this
  have key : ∀ g, η g = 1 → ∀ a b, ∃ c : O, residue O c = z g a b ∧ (conjBy (u * h)⁻¹ r₂ g).mat a b =
      (conjBy h⁻¹ r g).mat a b + (o a b * psi Ψ b g + c * psi Ψ b g - psi Ψ a g * o a b) • f := by
    intro g hg a b
    obtain ⟨c, hc, hc'⟩ := hγ g a b
    refine ⟨c, hc, ?_⟩
    have hrg : (r g).right = 1 := (hr.mult g).trans hg
    have hγk : Kil (maximalIdeal R) (γ g) := fun a b => by
      obtain ⟨c, -, hc'⟩ := hγ g a b
      rw [hc']; exact hk c
    have hD : ((r0 η Ψ g).mat).map (algebraMap O R) = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g) := by
      unfold GG.mat
      rw [unitaryThreeReflection_left, tor_val, Matrix.diagonal_map (map_zero _)]
      rfl
    have hA := hr.red g
    rw [hD] at hA
    have := core hh hhi hA hY hYm hγk
    rw [conj_mat _ _ _ hrg, conj_mat _ _ _ ((hd g).1.trans hrg), (hd g).2, _root_.mul_inv_rev, Units.val_mul,
      Units.val_mul]
    refine (congrFun (congrFun this a) b).trans ?_
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hc', Y,
      Matrix.of_apply, Algebra.smul_def, map_sub, map_add, map_mul]
    ring
  refine ⟨u * h, ?_, fun g hg a b hab => ?_, fun s hs hη a => ?_⟩
  · have e : ((u * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1 = ((h : Matrix (Fin 3) (Fin 3) R) - 1) - Y * h := by
      show (1 - Y) * (h : Matrix (Fin 3) (Fin 3) R) - 1 = _
      noncomm_ring
    intro a b
    rw [e, Matrix.sub_apply]
    exact Ideal.sub_mem _ (hh a b) (ent_right _ hYm a b)
  · obtain ⟨c, hc, e⟩ := key g hg a b
    rw [e, htri g hg a b hab, zero_add]
    apply h0
    rw [map_sub, map_add, map_mul, map_mul, map_mul, ho, hc]
    exact h1 g hg a b hab
  · obtain ⟨c, hc, e⟩ := key s hη a a
    rw [e, hine s hs hη a, h0, add_zero]
    rw [map_sub, map_add, map_mul, map_mul, map_mul, hc, h2 s hs a]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.triangular_condition_at_l_of_first_order_deformation :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v = F.vl →
      ∀ (r r₂ : F.D v →* GG 3 R) (z : F.D v → Gb (ResidueField O) j) (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R _ _ _ f hf hfm j v hv r r₂ z γ hr hl hz hγ hd
  refine ⟨fun _ => ?_, fun h => absurd (hv ▸ h) hF.vl_notMem, fun h => absurd (Set.mem_insert_iff.2 (Or.inl hv)) h⟩
  have hw : ∀ (X : Gb (ResidueField O) j) a b, wt a b ≠ j → X.val a b = 0 := fun X => Subtype.property X
  have h2 : ∀ s ∈ F.Iv v, ∀ a, (z s).val a a = 0 := fun s hs a => by
    by_cases hj : j = 0
    · rw [hz.2.2.2 hv hj s hs]; rfl
    · exact hw _ _ _ (by simpa [wt] using Ne.symm hj)
  by_cases hj : j < 0
  · obtain ⟨μ, hμ⟩ := (mem_coboundaries1 _ _).1 (hz.2.2.1 hv hj)
    refine condT_deform _ _ _ f hf hfm r r₂ (fun g => (z g).val) γ hr (hl.1 hv) hγ hd μ.val ?_ h2
    intro g hg a b _
    have e : (z g).val a b = adRep (r0 F.η F.Ψbar) (F.loc v g) μ.val a b - μ.val a b := by
      rw [hμ g]; rfl
    have hp : ∀ a, residue O (psi (F.Ψv v) a g) = ((F.Ψbar (F.loc v g) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O) :=
      fun a => by
        show _ = ((Units.map (residue O).toMonoidHom (F.Ψ (F.loc v g)) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O)
        rw [← map_zpow]; rfl
    have := ad_entry F.η F.Ψbar (F.loc v g) hg μ.val a b
    simp only [e, hp]
    linear_combination this
  · refine condT_deform _ _ _ f hf hfm r r₂ (fun g => (z g).val) γ hr (hl.1 hv) hγ hd 0 ?_ h2
    intro g _ a b hab
    simp [hw (z g) a b (by omega)]
