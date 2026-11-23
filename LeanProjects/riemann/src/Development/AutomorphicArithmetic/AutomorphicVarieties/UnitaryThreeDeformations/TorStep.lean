import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia.TorStep

theorem exists_procyc_lift {D H H' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group H] [Finite H]
    [Group H'] (I : Subgroup D) (φ : D) (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (π : H →* H') (u' : D →* H') (hu' : IsLocallyConstant u') (hI : ∀ s ∈ I, u' s = 1) (y : H) (hy : π y = u' φ) :
    ∃ u : D →* H, IsLocallyConstant u ∧ (∀ s ∈ I, u s = 1) ∧ π.comp u = u' ∧ ∀ g, ∃ k : ℕ, u g = y ^ k := by
  have hn : 0 < orderOf y := orderOf_pos y
  obtain ⟨d, hd1, hd2, hd3⟩ := hd (orderOf y) hn
  haveI : NeZero (orderOf y) := ⟨hn.ne'⟩
  let e : Multiplicative (ZMod (orderOf y)) →* H :=
    { toFun := fun k => y ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun a b => by rw [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add] }
  have he : e (Multiplicative.ofAdd 1) = y := by
    show y ^ (1 : ZMod (orderOf y)).val = y
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  have hlc : IsLocallyConstant (e.comp d) := hd1.comp e
  refine ⟨e.comp d, hlc, fun s hs => by simp [hd2 s hs], ?_, fun g => ⟨_, rfl⟩⟩
  have h1 : I ⊔ Subgroup.zpowers φ ≤ (π.comp (e.comp d)).eqLocus u' := by
    refine sup_le (fun s hs => ?_) ?_
    · show π (e (d s)) = u' s
      rw [hd2 s hs, hI s hs, map_one, map_one]
    · rw [Subgroup.zpowers_le]
      show π (e (d φ)) = u' φ
      rw [hd3, he, hy]
  have h2 : IsClosed (((π.comp (e.comp d)).eqLocus u' : Subgroup D) : Set D) := by
    have := ((hlc.comp π).prodMk hu').isClopen_fiber
    have h3 := ((hlc.comp π).prodMk hu') {z | z.1 = z.2}ᶜ
    rw [← isOpen_compl_iff]
    exact h3
  have h4 := Subgroup.topologicalClosure_minimal _ h1 h2
  rw [hφ] at h4
  exact MonoidHom.ext fun g => h4 (Subgroup.mem_top g)

section

variable {R : Type} [CommRing R]

theorem inv_val_eq_pow [Finite R] (z : GL (Fin 3) R) :
    ∃ k : ℕ, ((z⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = (z : Matrix (Fin 3) (Fin 3) R) ^ k := by
  refine ⟨orderOf z - 1, ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos z), pow_orderOf_eq_one]

theorem J_conj_apply (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

theorem theta_apply (z : GL (Fin 3) R) (a b : Fin 3) :
    (theta z : Matrix (Fin 3) (Fin 3) R) a b = ((z⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) b.rev a.rev := by
  rw [theta_val, J_conj_apply]

theorem isDiag_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : X.IsDiag) (hY : Y.IsDiag) : (X * Y).IsDiag := by
  rw [← hX.diagonal_diag, ← hY.diagonal_diag, Matrix.diagonal_mul_diagonal]
  exact Matrix.isDiag_diagonal _

theorem isDiag_inv [Finite R] {z : GL (Fin 3) R} (hz : z.val.IsDiag) : (z⁻¹).val.IsDiag := by
  obtain ⟨k, hk⟩ := inv_val_eq_pow z
  rw [hk]
  clear hk
  induction k with
  | zero => rw [pow_zero]; exact Matrix.isDiag_one
  | succ k ih => rw [pow_succ]; exact isDiag_mul ih hz

theorem isDiag_GG_mul [Finite R] {z w : GG 3 R} (hz : z.mat.IsDiag) (hw : w.mat.IsDiag) : (z * w).mat.IsDiag := by
  unfold GG.mat
  rw [SemidirectProduct.mul_left, Units.val_mul]
  refine isDiag_mul hz ?_
  rcases Int.units_eq_one_or z.right with h | h
  · rw [h, sgnAct_one]; exact hw
  · rw [h, sgnAct_neg_one]
    intro a b hab
    rw [theta_apply]
    exact isDiag_inv hw fun e => hab (Fin.rev_injective e).symm

theorem commute_tor {z : GG 3 R} (hz : z.mat.IsDiag) (t : Rˣ) : Commute (GG.ofGL (tor R t)) z := by
  have h : sgnAct 3 R z.right (tor R t) = tor R t := by
    rcases Int.units_eq_one_or z.right with h | h
    · rw [h, sgnAct_one]
    · rw [h, sgnAct_neg_one, theta_tor]
  refine SemidirectProduct.ext ?_ (by simp)
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, h]
  apply Units.ext
  have hz' : z.left.val = diagonal z.left.val.diag := (Matrix.IsDiag.diagonal_diag hz).symm
  rw [Units.val_mul, Units.val_mul, hz', tor_val, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem map_tor {S : Type} [CommRing S] (f : R →+* S) (t : Rˣ) :
    GeneralLinearGroup.map f (tor R t) = tor S (Units.map f.toMonoidHom t) := by
  apply Units.ext
  ext a b
  show f ((tor R t).val a b) = _
  rw [tor_val, tor_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rw [← map_zpow]; rfl
  · exact map_zero f

variable {O : Type} [CommRing O] [Algebra O R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜]

theorem grMat_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) : GrMat 𝒜 (X * Y) := by
  intro a b
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have : wt a b = wt a c + wt c b := by unfold wt; ring
  rw [this]
  exact SetLike.mul_mem_graded (hX a c) (hY c b)

theorem grMat_diagonal {d : Fin 3 → R} (hd : ∀ a, d a ∈ 𝒜 0) : GrMat 𝒜 (diagonal d) := by
  intro a b
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    have : wt a a = 0 := sub_self _
    rw [this]; exact hd a
  · exact zero_mem _

theorem grMat_one : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) :=
  grMat_diagonal 𝒜 (d := fun _ => 1) fun _ => SetLike.one_mem_graded 𝒜

theorem grMat_inv [Finite R] {z : GL (Fin 3) R} (hz : GrMat 𝒜 z.val) : GrMat 𝒜 (z⁻¹).val := by
  obtain ⟨k, hk⟩ := inv_val_eq_pow z
  rw [hk]
  clear hk
  induction k with
  | zero => rw [pow_zero]; exact grMat_one 𝒜
  | succ k ih => rw [pow_succ]; exact grMat_mul 𝒜 ih hz

theorem grMat_GG_mul [Finite R] {z w : GG 3 R} (hz : GrMat 𝒜 z.mat) (hw : GrMat 𝒜 w.mat) :
    GrMat 𝒜 (z * w).mat := by
  unfold GG.mat
  rw [SemidirectProduct.mul_left, Units.val_mul]
  refine grMat_mul 𝒜 hz ?_
  rcases Int.units_eq_one_or z.right with h | h
  · rw [h, sgnAct_one]; exact hw
  · rw [h, sgnAct_neg_one]
    intro a b
    rw [theta_apply]
    have : wt a b = wt b.rev a.rev := by fin_cases a <;> fin_cases b <;> rfl
    rw [this]
    exact grMat_inv 𝒜 hw _ _

theorem grMat_tor (t : Oˣ) : GrMat 𝒜 (tor R (Units.map (algebraMap O R).toMonoidHom t)).val := by
  rw [tor_val]
  refine grMat_diagonal 𝒜 fun a => ?_
  rw [← map_zpow]
  exact SetLike.algebraMap_mem_graded 𝒜 _

end

abbrev chr {O D : Type} [CommRing O] [Group D] (Ψ : D →* Oˣ) (A : Type) [CommRing A] [Algebra O A] : D →* Aˣ :=
  (Units.map (algebraMap O A).toMonoidHom).comp Ψ

theorem tor_chr_apply {O D : Type} [CommRing O] [Group D] (Ψ : D →* Oˣ) (A : Type) [CommRing A] [Algebra O A]
    (g : D) : (tor A (chr Ψ A g)).val = diagonal fun a => algebraMap O A (psi Ψ a g) := by
  rw [tor_val]
  congr 1
  funext a
  show (((Units.map (algebraMap O A).toMonoidHom (Ψ g)) ^ wt1 a : Aˣ) : A) = _
  rw [← map_zpow]
  rfl

theorem isLocallyConstant_chr {O D : Type} [CommRing O] [IsLocalRing O] [Group D] [TopologicalSpace D] (Ψ : D →* Oˣ)
    (hΨ : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (Ψ g : O))
    (A : Type) [CommRing A] [Algebra O A] [IsCO O A] [Finite A] : IsLocallyConstant (chr Ψ A) := by
  obtain ⟨n, hn⟩ : IsNilpotent (maximalIdeal A) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at this
  have hk : ∀ a ∈ maximalIdeal O ^ n, algebraMap O A a = 0 := by
    intro a ha
    have h1 : maximalIdeal O ^ n ≤ (maximalIdeal A ^ n).comap (algebraMap O A) := by
      refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) n) (Ideal.le_comap_pow _ n)
      exact map_nonunit (algebraMap O A) y hy
    have h2 := h1 ha
    rw [hn] at h2
    simpa using h2
  refine IsLocallyConstant.desc _ (Units.val) ?_ Units.val_injective
  exact (hΨ n).comp (Ideal.Quotient.lift _ _ hk)

theorem isLocallyConstant_GG {A D : Type} [CommRing A] [Group D] [TopologicalSpace D] (η : D →* ℤˣ)
    (hη : IsLocallyConstant η) (r : D →* GG 3 A) (hr : HasMult η r) (h : IsLocallyConstant (mats r)) :
    IsLocallyConstant r := by
  refine IsLocallyConstant.desc _ (fun z : GG 3 A => (z.mat, z.right)) ?_ ?_
  · have : (fun z : GG 3 A => (z.mat, z.right)) ∘ r = fun g => (mats r g, η g) := by
      funext g
      exact Prod.ext rfl (hr g)
    rw [this]
    exact h.prodMk hη
  · intro z w e
    exact SemidirectProduct.ext (Units.ext (congrArg Prod.fst e)) (congrArg Prod.snd e)

def twist {A D : Type} [CommRing A] [Group D] (χ : D →* Aˣ) (u : D →* GG 3 A) (hu : ∀ g, (u g).mat.IsDiag) :
    D →* GG 3 A where
  toFun g := GG.ofGL (tor A (χ g)) * u g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul, map_mul]
    exact (commute_tor (hu g) (χ h)).mul_mul_mul_comm _ _

theorem exists_torus_lift {O D R R' : Type} [CommRing O] [IsLocalRing O] [Group D] [TopologicalSpace D]
    [IsTopologicalGroup D] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] [IsCO O R']
    [Finite R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') [IsLocalHom (p : R →+* R')]
    (I : Subgroup D) (φ : D) (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (Ψ : D →* Oˣ) (hΨ : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (Ψ g : O))
    (t' : D →* GG 3 R') (hlc : IsLocallyConstant t') (hdiag : ∀ g, (t' g).mat.IsDiag)
    (hI : ∀ s ∈ I, t' s = GG.ofGL (tor R' (chr Ψ R' s)))
    (hgr : ∀ a, ∃ x ∈ 𝒜 0, p x = (t' φ).mat a a) :
    ∃ t : D →* GG 3 R, push p t = t' ∧ IsLocallyConstant t ∧ (∀ g, (t g).mat.IsDiag) ∧
      (∀ s ∈ I, t s = GG.ofGL (tor R (chr Ψ R s))) ∧ ∀ g, GrMat 𝒜 (t g).mat := by
  haveI : Finite (GG 3 R) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  choose x hx0 hx using hgr
  have hdet : IsUnit (diagonal x).det := by
    have h1 : (diagonal x).map (p : R →+* R') = (t' φ).mat := by
      rw [Matrix.diagonal_map (map_zero _), ← (hdiag φ).diagonal_diag]
      congr 1
      funext a
      exact hx a
    apply IsUnit.of_map (p : R →+* R')
    rw [RingHom.map_det, RingHom.mapMatrix_apply, h1]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (t' φ).left.isUnit
  obtain ⟨X, hX⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  have hmt : ∀ g, GG.map (p : R →+* R') (GG.ofGL (tor R (chr Ψ R g))) = GG.ofGL (tor R' (chr Ψ R' g)) := by
    intro g
    refine SemidirectProduct.ext ?_ rfl
    show GeneralLinearGroup.map _ (tor R (chr Ψ R g)) = tor R' (chr Ψ R' g)
    rw [map_tor]
    congr 1
    exact Units.ext (p.commutes _)
  let y₀ : GG 3 R := ⟨X, (t' φ).right⟩
  have hy₀ : GG.map (p : R →+* R') y₀ = t' φ := by
    refine SemidirectProduct.ext (Units.ext ?_) rfl
    show X.val.map (p : R →+* R') = (t' φ).mat
    rw [hX, Matrix.diagonal_map (map_zero _), ← (hdiag φ).diagonal_diag]
    congr 1
    funext a
    exact hx a
  have htd : ∀ t : Rˣ, (GG.ofGL (tor R t)).mat.IsDiag := fun t => Matrix.isDiag_diagonal _
  have htg : ∀ g, GrMat 𝒜 (GG.ofGL (tor R (chr Ψ R g))).mat := fun g => grMat_tor 𝒜 (Ψ g)
  let y : GG 3 R := GG.ofGL (tor R (chr Ψ R φ⁻¹)) * y₀
  have hyd : y.mat.IsDiag := isDiag_GG_mul (htd _) (by
    show X.val.IsDiag
    rw [hX]; exact Matrix.isDiag_diagonal _)
  have hyg : GrMat 𝒜 y.mat := grMat_GG_mul 𝒜 (htg _) (by
    show GrMat 𝒜 X.val
    rw [hX]; exact grMat_diagonal 𝒜 hx0)
  have hpow : ∀ k : ℕ, (y ^ k).mat.IsDiag ∧ GrMat 𝒜 (y ^ k).mat := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact ⟨Matrix.isDiag_one, grMat_one 𝒜⟩
    | succ k ih => rw [pow_succ]; exact ⟨isDiag_GG_mul ih.1 hyd, grMat_GG_mul 𝒜 ih.2 hyg⟩
  let u' : D →* GG 3 R' := twist (chr Ψ R')⁻¹ t' hdiag
  have hu' : ∀ g, u' g = (GG.ofGL (tor R' (chr Ψ R' g)))⁻¹ * t' g := fun g => by
    rw [← map_inv, ← map_inv]; rfl
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := exists_procyc_lift I φ hφ hd (GG.map (p : R →+* R')) u'
    (((isLocallyConstant_chr Ψ hΨ R').prodMk hlc).comp fun z => GG.ofGL (tor R' z.1⁻¹) * z.2)
    (fun s hs => by rw [hu', hI s hs, inv_mul_cancel]) y
    (by rw [hu', map_mul, hmt, hy₀, map_inv, map_inv, map_inv])
  have hud : ∀ g, (u g).mat.IsDiag := fun g => by
    obtain ⟨k, hk⟩ := hu4 g
    rw [hk]; exact (hpow k).1
  refine ⟨twist (chr Ψ R) u hud, MonoidHom.ext fun g => ?_,
    ((isLocallyConstant_chr Ψ hΨ R).prodMk hu1).comp fun z => GG.ofGL (tor R z.1) * z.2,
    fun g => isDiag_GG_mul (htd _) (hud g), fun s hs => ?_, fun g => grMat_GG_mul 𝒜 (htg g) ?_⟩
  · show GG.map _ (GG.ofGL (tor R (chr Ψ R g)) * u g) = t' g
    have : GG.map (p : R →+* R') (u g) = u' g := DFunLike.congr_fun hu3 g
    rw [map_mul, hmt, this, hu', mul_inv_cancel_left]
  · show GG.ofGL (tor R (chr Ψ R s)) * u s = _
    rw [hu2 s hs, mul_one]
  · obtain ⟨k, hk⟩ := hu4 g
    rw [hk]; exact (hpow k).2

end UpperTheory.V.UnitaryThreeInertia.TorStep
