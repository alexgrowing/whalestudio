import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ZzScale

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

theorem nz1 {F : Type} [Field F] {A a t u : F} (hA : A ≠ 0) (h : u ≠ -t * a / A) : A * u + t * a ≠ 0 := by
  intro h0
  apply h
  rw [eq_div_iff hA]
  linear_combination h0

theorem nz2 {F : Type} [Field F] {B b t u : F} (hB : B ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) (h : u ≠ -B / (t * b)) :
    B * u⁻¹ + t * b ≠ 0 := by
  intro h0
  by_cases hb : b = 0
  · rw [hb, mul_zero, add_zero] at h0
    exact mul_ne_zero hB (inv_ne_zero hu) h0
  · apply h
    rw [eq_div_iff (mul_ne_zero ht hb)]
    have h1 : B + t * b * u = 0 := by
      have h2 := congrArg (· * u) h0
      simp only [add_mul, inv_mul_cancel_right₀ hu, zero_mul] at h2
      exact h2
    linear_combination h1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem firstProj_conj_algebra (x : E) : ph1 g (M.L.cj x) = ph2 g x := by
  show (g.e (M.L.cj x)).1 = (g.e x).2
  rw [g.e_cj]
  rfl
theorem secondProj_conj_algebra (x : E) : ph2 g (M.L.cj x) = ph1 g x := by
  show (g.e (M.L.cj x)).2 = (g.e x).1
  rw [g.e_cj]
  rfl

theorem scaleChoice_holds : ScaleChoiceP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT hq hT0 Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel
  classical
  have hq0 := q_ne g
  obtain ⟨c0, hc⟩ := hq
  obtain ⟨uT, vT, huT, hvT⟩ := hT
  have hTne : T ≠ 0 := by rintro rfl; simp at huT
  have hT'ne : T' ≠ 0 := by rintro rfl; simp at hvT
  have hT'0 : T' ∈ 𝒪[F] := by
    have : T' = T - (g.q : F) ^ 2 * c0 := by rw [← hc]; ring
    rw [this]; exact sub_mem hT0 (mul_mem (pow_mem g.q.2 2) c0.2)
  have hu₁ := (isUnit_iff_ph (g := g) _).1 u₁
  have hu₂ := (isUnit_iff_ph (g := g) _).1 u₂
  set d₁ := (Zh₁.submatrix Fin.castSucc Fin.castSucc).det
  set d₂ := (Zh₂.submatrix Fin.castSucc Fin.castSucc).det

  let L : List F := [-T * ph1 g d₁ / ph1 g Zh₁.det, -T' * ph1 g d₁ / ph1 g Zh₁.det,
    -ph2 g Zh₁.det / (T' * ph2 g d₁), -ph2 g Zh₁.det / (T * ph2 g d₁),
    -T * ph1 g d₂ / ph1 g Zh₂.det, -T' * ph1 g d₂ / ph1 g Zh₂.det,
    -ph2 g Zh₂.det / (T' * ph2 g d₂), -ph2 g Zh₂.det / (T * ph2 g d₂)]
  let f : ℕ → F := fun k => ((1 + g.q ^ (k + 1) : 𝒪[F]) : F)
  have finj : Function.Injective f := by
    intro j k h
    have h' : (1 + g.q ^ (j + 1) : 𝒪[F]) = 1 + g.q ^ (k + 1) := Subtype.ext h
    have := pow_injective_of_not_isUnit g.q_irr.not_isUnit g.q_irr.ne_zero (add_left_cancel h')
    simpa using this
  obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.range 9, f k ∉ L.toFinset := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.range 9).image f ⊆ L.toFinset := fun x hx => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx; exact hcon k hk
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ finj, Finset.card_range] at h1
    have h2 : L.toFinset.card ≤ 8 := (List.toFinset_card_le L).trans (by simp [L])
    omega
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or, L] at hk
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hk

  have hU : IsUnit (1 + g.q ^ (k + 1) : 𝒪[F]) := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-(g.q ^ (k + 1)) : 𝒪[F]) with h | h
    · exact absurd ((isUnit_pow_iff (Nat.succ_ne_zero k)).1 ((IsUnit.neg_iff _).1 h)) g.q_irr.not_isUnit
    · rwa [sub_neg_eq_add] at h
  obtain ⟨uO, huOd⟩ : ∃ uO : 𝒪[F], uO = 1 + g.q ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨u', hu'd⟩ : ∃ u' : 𝒪[F], u' = ((hU.unit⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) := ⟨_, rfl⟩
  have huu : (uO : F) * (u' : F) = 1 := by
    have h := congrArg Subtype.val hU.mul_val_inv
    rw [huOd, hu'd]
    exact_mod_cast h
  obtain ⟨u, hud⟩ : ∃ u : F, u = (uO : F) := ⟨_, rfl⟩
  rw [← hud] at huu
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one huu
  have hu' : (u' : F) = u⁻¹ := eq_inv_of_mul_eq_one_right huu
  have huv : u = 1 + (g.q : F) ^ (k + 1) := by rw [hud, huOd]; push_cast; ring
  have huvO : (uO : F) = 1 + (g.q : F) ^ (k + 1) := by rw [← hud, huv]
  have hfk : f k = u := by simp only [f]; push_cast; rw [huv]

  obtain ⟨α, hαd⟩ : ∃ α : E, α = g.e.symm (u, u⁻¹) := ⟨_, rfl⟩
  have hα : g.e α = (u, u⁻¹) := by simp [hαd]
  have mq : (g.q : F) ^ k ∈ 𝒪[F] := pow_mem g.q.2 k
  let δ₁ : M.R := ⟨g.e.symm (u, 1), mem_R_of hs _ uO 1 (g.q ^ k) (by simp [hud]) (by push_cast; rw [huvO]; ring)⟩
  let δ₁i : M.R := ⟨g.e.symm (u⁻¹, 1), mem_R_of hs _ u' 1 (-(u' * g.q ^ k)) (by simp [hu'])
    (by push_cast; rw [hu']; field_simp; rw [huv]; ring)⟩
  let δ₂ : M.R := ⟨g.e.symm (1, u⁻¹), mem_R_of hs _ 1 u' (u' * g.q ^ k) (by simp [hu'])
    (by push_cast; rw [hu']; field_simp; rw [huv]; ring)⟩
  let δ₂i : M.R := ⟨g.e.symm (1, u), mem_R_of hs _ 1 uO (-(g.q ^ k)) (by simp [hud])
    (by push_cast; rw [huvO]; ring)⟩
  let cc : M.R := ⟨g.e.symm ((1 - u) * T / (g.q : F), (1 - u) * T' / (g.q : F)),
    mem_R_of hs _ (-(g.q ^ k) * ⟨T, hT0⟩) (-(g.q ^ k) * ⟨T', hT'0⟩) (-(g.q ^ (k + 1)) * c0)
      (by rw [AlgEquiv.apply_symm_apply]; push_cast; rw [huv]; refine Prod.ext ?_ ?_ <;> (simp only; field_simp; ring))
      (by push_cast; linear_combination (-(g.q : F) ^ k) * hc)⟩
  have he1 : g.e (δ₁ : E) = (u, 1) := by simp [δ₁]
  have he2 : g.e (δ₂ : E) = (1, u⁻¹) := by simp [δ₂]
  have hcc : g.e (cc : E) = ((1 - u) * T / (g.q : F), (1 - u) * T' / (g.q : F)) := by simp [cc]
  have hδ₁ : IsUnit δ₁ := isUnit_iff_exists_inv.2 ⟨δ₁i, by
    apply Subtype.ext; apply g.e.injective
    simp [δ₁, δ₁i, hu0]⟩
  have hδ₂ : δ₂ * δ₂i = 1 := by
    apply Subtype.ext; apply g.e.injective
    simp [δ₂, δ₂i, hu0]
  let C : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R := Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then cc else 0
  refine ⟨α, ?_, ?_, ?_, dlast r δ₂ * (Z₁ * dlast r δ₁ + C), dlast r δ₂ * (Z₂ * dlast r δ₁ + C),
    zz_scale hs Zh₁ T T' Z₁ e₁ u hu0 δ₁ δ₂ cc α he1 he2 hcc hα,
    zz_scale hs Zh₂ T T' Z₂ e₂ u hu0 δ₁ δ₂ cc α he1 he2 hcc hα, ?_, ?_, ?_, ?_, ?_⟩
  · apply g.e.injective
    rw [map_mul, e_cjA, hα, map_one]
    refine Prod.ext ?_ ?_ <;> simp [hu0]
  · exact mem_O_of_comp g _ (by rw [hα, hud]; exact uO.2) (by rw [hα, ← hu']; exact u'.2)
  · refine mem_O_of_comp g _ ?_ ?_
    · rw [map_mul, map_sub, hα, map_one, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg]
      have : (u - 1) * (g.q : F)⁻¹ = (g.q : F) ^ k := by rw [huv]; field_simp; ring
      simp only [Prod.fst_mul, Prod.fst_sub, Prod.fst_one]
      rw [this]; exact mq
    · rw [map_mul, map_sub, hα, map_one, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg]
      have : (u⁻¹ - 1) * (g.q : F)⁻¹ = -((u' : F) * (g.q : F) ^ k) := by
        rw [hu']; field_simp; rw [huv]; ring
      simp only [Prod.snd_mul, Prod.snd_sub, Prod.snd_one]
      rw [this]; exact neg_mem (mul_mem u'.2 mq)
  · rw [zz_scale hs Zh₁ T T' Z₁ e₁ u hu0 δ₁ δ₂ cc α he1 he2 hcc hα, zz_unit_iff hs, Matrix.det_mul, dlast_det,
      head_mul_dlast, map_mul, map_mul, firstProj_apply (g := g) α, secondProj_apply (g := g) α, hα]
    rw [hfk] at b1 b3
    exact ⟨nz1 hu₁.1 b1, nz2 hu₁.2 hT'ne hu0 b3⟩
  · rw [zz_scale hs Zh₂ T T' Z₂ e₂ u hu0 δ₁ δ₂ cc α he1 he2 hcc hα, zz_unit_iff hs, Matrix.det_mul, dlast_det,
      head_mul_dlast, map_mul, map_mul, firstProj_apply (g := g) α, secondProj_apply (g := g) α, hα]
    rw [hfk] at b5 b7
    exact ⟨nz1 hu₂.1 b5, nz2 hu₂.2 hT'ne hu0 b7⟩
  · rw [zz_unit_iff hs, det_map_cj, head_map_cj, firstProj_conj_algebra, firstProj_conj_algebra, secondProj_conj_algebra, secondProj_conj_algebra, Matrix.det_mul, dlast_det,
      head_mul_dlast, map_mul, map_mul, firstProj_apply (g := g) α, secondProj_apply (g := g) α, hα]
    rw [hfk] at b2 b4
    exact ⟨nz2 hu₁.2 hTne hu0 b4, nz1 hu₁.1 b2⟩
  · rw [zz_unit_iff hs, det_map_cj, head_map_cj, firstProj_conj_algebra, firstProj_conj_algebra, secondProj_conj_algebra, secondProj_conj_algebra, Matrix.det_mul, dlast_det,
      head_mul_dlast, map_mul, map_mul, firstProj_apply (g := g) α, secondProj_apply (g := g) α, hα]
    rw [hfk] at b6 b8
    exact ⟨nz2 hu₂.2 hTne hu0 b8, nz1 hu₂.1 b6⟩
  · exact (card_isoMbe_lastRow _ _ δ₂ δ₂i hδ₂).symm.trans (card_isoMbe_lastCol Z₁ Z₂ δ₁ cc hδ₁).symm

end Formalism.L2.SG.LocalCountModules.AlgGSplit
