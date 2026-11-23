import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem lu_section {G A : Type} [Group G] [Finite G] [Group A] (g : G →* A) (hg : Function.Surjective g)
    (hc : Nat.Coprime (Nat.card g.ker) (Nat.card A)) : ∃ σ : A →* G, ∀ a, g (σ a) = a := by
  have hi : g.ker.index = Nat.card A := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hg, Subgroup.card_top]
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := g.ker) (by rwa [hi])
  have hb : Function.Bijective (g.comp C.subtype) := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro c hc
      have : (c : G) ∈ g.ker ⊓ C := ⟨hc, c.2⟩
      rw [hC.disjoint.eq_bot] at this
      exact Subtype.ext this
    · intro a
      obtain ⟨x, rfl⟩ := hg a
      obtain ⟨⟨k, c⟩, rfl⟩ := hC.2 x
      refine ⟨c, ?_⟩
      have hk : g k = 1 := k.2
      simp [hk]
  exact ⟨C.subtype.comp (MulEquiv.ofBijective _ hb).symm.toMonoidHom,
    fun a => (MulEquiv.ofBijective _ hb).apply_symm_apply a⟩

private theorem lu_conj {H H' A : Type} [Group H] [Finite H] [Group H'] [Group A] [Finite A] (f : H →* H')
    (hK : ∀ a b, f a = 1 → f b = 1 → a * b = b * a) (hc : Nat.Coprime (Nat.card f.ker) (Nat.card A))
    (σ τ : A →* H) (h : ∀ a, f (σ a) = f (τ a)) : ∃ k, f k = 1 ∧ ∀ a, τ a = k * σ a * k⁻¹ := by
  classical
  letI := Fintype.ofFinite A
  letI : CommGroup f.ker := { (inferInstance : Group f.ker) with
    mul_comm := fun a b => Subtype.ext (hK _ _ a.2 b.2) }
  let c : A → f.ker := fun a => ⟨τ a * (σ a)⁻¹, by simp [h a]⟩
  let act : A → f.ker →* f.ker := fun a => (MulAut.conjNormal (σ a) : MulAut f.ker).toMonoidHom
  have hact : ∀ a (k : f.ker), (act a k : H) = σ a * k * (σ a)⁻¹ := fun a k => rfl
  have hcoc : ∀ a b, c (a * b) = c a * act a (c b) := fun a b => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hact]
    simp [c, mul_assoc]
  have hbij := (powCoprime hc).bijective
  obtain ⟨k, hk⟩ := hbij.2 (∏ b, c b)
  rw [powCoprime_apply] at hk
  refine ⟨k, k.2, fun a => ?_⟩
  have h1 : ∏ b, c b = c a ^ Nat.card A * act a (∏ b, c b) := by
    refine (Equiv.prod_comp (Equiv.mulLeft a) c).symm.trans ?_
    simp only [Equiv.coe_mulLeft, hcoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card, map_prod]
  have h2 : k = c a * act a k := by
    apply hbij.1
    rw [powCoprime_apply, powCoprime_apply, mul_pow, ← map_pow, hk]
    exact h1
  have h3 := congrArg Subtype.val h2
  rw [Subgroup.coe_mul, hact] at h3
  simp only [c] at h3
  calc τ a = (τ a * (σ a)⁻¹ * (σ a * k * (σ a)⁻¹)) * σ a * (k : H)⁻¹ := by group
    _ = _ := by rw [← h3]

private theorem lu_abs {D H H' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group H] [Finite H]
    [Group H'] (f : H →* H') (hK : ∀ a b, f a = 1 → f b = 1 → a * b = b * a) (l e : ℕ) (hl : l.Prime)
    (hle : ¬ l ∣ e) (hKl : ∀ a, f a = 1 → a ^ l = 1) (I : Subgroup D) (hI : I.Normal) (φ : D)
    (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (r' : D →* H') (hlc : IsLocallyConstant r') (hs : ∀ g, ∃ h, f h = r' g) (he : ∀ s ∈ I, r' s ^ e = 1) :
    ∃ r : D →* H, (∀ g, f (r g) = r' g) ∧ IsLocallyConstant r ∧ ∀ s ∈ I, r' s = 1 → r s = 1 := by
  haveI := Fact.mk hl
  let A : Subgroup H' := I.map r'
  have hsurj : Function.Surjective (f.subgroupComap A) := by
    rintro ⟨_, s, hsI, rfl⟩
    obtain ⟨h, hh⟩ := hs s
    exact ⟨⟨h, show f h ∈ A from hh ▸ ⟨s, hsI, rfl⟩⟩, Subtype.ext hh⟩
  haveI : Finite A := Finite.of_surjective _ hsurj
  have hA : Nat.Coprime l (Nat.card A) := by
    rw [hl.coprime_iff_not_dvd]
    intro hdv
    obtain ⟨⟨_, s, hsI, rfl⟩, ha⟩ := exists_prime_orderOf_dvd_card' l hdv
    exact hle (ha ▸ orderOf_dvd_of_pow_eq_one (Subtype.ext (he s hsI)))
  have hP : ∀ {G : Type} [Group G] [Finite G], (∀ a : G, a ^ l = 1) → Nat.Coprime (Nat.card G) (Nat.card A) := by
    intro G _ _ hG
    have : IsPGroup l G := fun a => ⟨1, by simpa using hG a⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 this
    rw [hn]
    exact Nat.Coprime.pow_left n hA
  obtain ⟨σ₀, hσ₀⟩ := lu_section (f.subgroupComap A) hsurj (hP fun a =>
    Subtype.ext (Subtype.ext (hKl _ (congrArg Subtype.val a.2))))
  let σ : A →* H := (Subgroup.subtype _).comp σ₀
  have hσ : ∀ a, f (σ a) = a := fun a => congrArg Subtype.val (hσ₀ a)
  have hn : ∀ g : D, ∀ a : A, (r' g)⁻¹ * a * r' g ∈ A := by
    rintro g ⟨_, s, hsI, rfl⟩
    exact ⟨g⁻¹ * s * g, hI.conj_mem' s hsI g, by simp⟩
  let cj : D → A →* A := fun g =>
    { toFun := fun a => ⟨_, hn g a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcj : ∀ g a, (cj g a : H') = (r' g)⁻¹ * a * r' g := fun _ _ => rfl
  obtain ⟨x₀, hx₀⟩ := hs φ
  obtain ⟨k, hk, hkc⟩ := lu_conj f hK (hP fun a => Subtype.ext (hKl _ a.2)) σ
    ((MulAut.conj x₀).toMonoidHom.comp (σ.comp (cj φ))) (fun a => by simp [hσ, hcj, hx₀, mul_assoc])
  set x := k⁻¹ * x₀ with hxdef
  have hx : f x = r' φ := by simp [hxdef, hk, hx₀]
  have hxa : ∀ a, x * σ (cj φ a) * x⁻¹ = σ a := fun a => by
    have := hkc a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    calc x * σ (cj φ a) * x⁻¹ = k⁻¹ * (x₀ * σ (cj φ a) * x₀⁻¹) * k := by rw [hxdef]; group
      _ = σ a := by rw [this]; group
  have hnorm : x ∈ Subgroup.normalizer (σ.range : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨cj φ⁻¹ a, ?_⟩
      rw [← hxa]
      congr 3
      exact Subtype.ext (by simp [hcj, mul_assoc])
    · rintro ⟨a, ha⟩
      refine ⟨cj φ a, ?_⟩
      rw [← hxa] at ha
      simpa using ha
  have hz : ∀ (m : ℤ) (t : H), t ∈ σ.range → x ^ m * t * (x ^ m)⁻¹ ∈ σ.range := fun m t ht =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ hnorm m) t).1 ht
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf x) (orderOf_pos x)
  let L : Subgroup (H × Multiplicative (ZMod (orderOf x))) :=
    { carrier := {z | ∃ m : ℤ, z.1 * (x ^ m)⁻¹ ∈ σ.range ∧ z.2 = Multiplicative.ofAdd (m : ZMod (orderOf x))}
      one_mem' := ⟨0, by simp, by simp⟩
      mul_mem' := by
        rintro z w ⟨m, h1, h2⟩ ⟨m', h1', h2'⟩
        refine ⟨m + m', ?_, by simp [h2, h2', ofAdd_add]⟩
        have := mul_mem h1 (hz m _ h1')
        convert this using 1
        simp only [Prod.fst_mul]; group
      inv_mem' := by
        rintro z ⟨m, h1, h2⟩
        refine ⟨-m, ?_, by simp [h2]⟩
        have := hz (-m) _ (inv_mem h1)
        convert this using 1
        simp only [Prod.fst_inv]; group }
  let Φ : L →* H' × Multiplicative (ZMod (orderOf x)) := (f.prodMap (MonoidHom.id _)).comp L.subtype
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨z, u⟩, m, ⟨a, ha⟩, h2⟩ h
    have e1 : f z = 1 := congrArg Prod.fst h
    have e2 : u = 1 := congrArg Prod.snd h
    have e3 : x ^ m = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [e2] at h2
      exact (ofAdd_eq_one.1 h2.symm)
    simp only [e3, inv_one, mul_one] at ha
    have e4 : a = 1 := Subtype.ext (by rw [← hσ, ha, e1]; rfl)
    have e5 : z = 1 := by rw [← ha, e4, map_one]
    exact Subtype.ext (Prod.ext e5 e2)
  have hlc2 : IsLocallyConstant (r'.prod d) := hlc.prodMk hdl
  have hr : ∀ g, (r'.prod d) g ∈ Φ.range := by
    have hcl : IsClosed ((Φ.range.comap (r'.prod d) : Subgroup D) : Set D) :=
      ⟨hlc2 ((Φ.range : Set (H' × Multiplicative (ZMod (orderOf x))))ᶜ)⟩
    have hle : I ⊔ Subgroup.zpowers φ ≤ Φ.range.comap (r'.prod d) := by
      refine sup_le (fun s hsI => ?_) ((Subgroup.zpowers_le).2 ?_)
      · exact ⟨⟨(σ ⟨_, s, hsI, rfl⟩, 1), 0, by simp, by simp⟩, Prod.ext (hσ _) (hdI s hsI).symm⟩
      · exact ⟨⟨(x, Multiplicative.ofAdd 1), 1, by simp, by simp⟩, Prod.ext hx hdφ.symm⟩
    intro g
    have := Subgroup.topologicalClosure_minimal _ hle hcl
    rw [hφ] at this
    exact this (Subgroup.mem_top g)
  let ρ : D →* L := (MonoidHom.ofInjective hΦ).symm.toMonoidHom.comp ((r'.prod d).codRestrict _ hr)
  have hρ : ∀ g, Φ (ρ g) = (r'.prod d) g := fun g => MonoidHom.apply_ofInjective_symm hΦ _
  refine ⟨(MonoidHom.fst _ _).comp (L.subtype.comp ρ), fun g => congrArg Prod.fst (hρ g), ?_, fun s hsI h1 => ?_⟩
  · have : IsLocallyConstant ρ := IsLocallyConstant.desc ρ Φ (by
      have : Φ ∘ ρ = r'.prod d := funext hρ
      rw [this]; exact hlc2) hΦ
    exact this.comp fun z : L => z.1.1
  · have : ρ s = 1 := hΦ (by rw [hρ, map_one]; exact Prod.ext h1 (hdI s hsI))
    simp [this]

private theorem lu_inv_mem {M : Type} [Group M] [Finite M] (S : Submonoid M) {x : M} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  rw [this]
  exact pow_mem hx _

private theorem lu_sub {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Finite R]
    (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] : ∃ S : Subgroup (GG 3 R), ∀ x, x ∈ S ↔ GrMat 𝒜 x.mat := by
  have h1 : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) := fun a b => by
    by_cases h : a = b
    · subst h
      simp only [wt, sub_self, Matrix.one_apply_eq]
      exact SetLike.GradedOne.one_mem
    · simp [Matrix.one_apply_ne h]
  have hm : ∀ X Y : Matrix (Fin 3) (Fin 3) R, GrMat 𝒜 X → GrMat 𝒜 Y → GrMat 𝒜 (X * Y) := fun X Y hX hY a b => by
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    have := SetLike.GradedMul.mul_mem (hX a c) (hY c b)
    rwa [show wt a c + wt c b = wt a b by simp [wt]] at this
  let S₀ : Submonoid (GL (Fin 3) R) :=
    { carrier := {x | GrMat 𝒜 (x : Matrix (Fin 3) (Fin 3) R)}
      one_mem' := h1
      mul_mem' := fun ha hb => hm _ _ ha hb }
  have hθ : ∀ g : GL (Fin 3) R, g ∈ S₀ → theta g ∈ S₀ := fun g hg a b => by
    have hi : GrMat 𝒜 ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := lu_inv_mem S₀ hg
    rw [theta_val]
    generalize ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = X at hi
    have e : (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
    have e' : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
    rw [e, ← e']
    exact hi _ _
  let S₁ : Submonoid (GG 3 R) :=
    { carrier := {x | x.left ∈ S₀}
      one_mem' := S₀.one_mem
      mul_mem' := fun {x y} hx hy => by
        show x.left * sgnAct 3 R x.right y.left ∈ S₀
        refine mul_mem hx ?_
        rcases Int.units_eq_one_or x.right with h | h <;> rw [h]
        · rw [sgnAct_one]; exact hy
        · rw [sgnAct_neg_one]; exact hθ _ hy }
  haveI : Finite (GG 3 R) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  exact ⟨{ S₁ with inv_mem' := fun hx => lu_inv_mem S₁ hx }, fun _ => Iff.rfl⟩

private theorem lu_ker {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R')
    (hp : ∀ x y, p x = 0 → p y = 0 → x * y = 0) (l : ℕ) (hl : ∀ x, p x = 0 → (l : R) * x = 0) :
    (∀ a b : GG 3 R, GG.map p a = 1 → GG.map p b = 1 → a * b = b * a) ∧
      ∀ a : GG 3 R, GG.map p a = 1 → a ^ l = 1 := by
  have hk : ∀ a : GG 3 R, GG.map p a = 1 → ∃ u : GL (Fin 3) R, a = GG.ofGL u ∧
      ∃ X : Matrix (Fin 3) (Fin 3) R, (u : Matrix (Fin 3) (Fin 3) R) = 1 + X ∧ ∀ i j, p (X i j) = 0 := by
    intro a ha
    have h1 : a.right = 1 := congrArg SemidirectProduct.right ha
    have h2 : a.mat.map p = 1 := congrArg GG.mat ha
    refine ⟨a.left, SemidirectProduct.ext rfl h1, a.mat - 1, by simp [GG.mat], fun i j => ?_⟩
    have := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hz : ∀ X Y : Matrix (Fin 3) (Fin 3) R, (∀ i j, p (X i j) = 0) → (∀ i j, p (Y i j) = 0) → X * Y = 0 :=
    fun X Y hX hY => by
      ext i j
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun c _ => hp _ _ (hX _ _) (hY _ _)
  constructor
  · intro a b ha hb
    obtain ⟨u, rfl, X, hu, hX⟩ := hk a ha
    obtain ⟨w, rfl, Y, hw, hY⟩ := hk b hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hu, hw]
    simp only [add_mul, mul_add, hz X Y hX hY, hz Y X hY hX, one_mul, mul_one]
    abel
  · intro a ha
    obtain ⟨u, rfl, X, hu, hX⟩ := hk a ha
    have hn : ∀ n : ℕ, (1 + X) ^ n = 1 + (n : R) • X := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ih]
        simp only [add_mul, mul_add, smul_mul_assoc, hz X X hX hX, one_mul, mul_one, smul_zero, Nat.cast_succ,
          add_smul, one_smul]
        abel
    have : u ^ l = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hu, hn, Units.val_one, add_eq_left]
      ext i j
      exact hl _ (hX i j)
    rw [← map_pow, this, map_one]

theorem UpperTheory.V.UnitaryThreeInertia.exists_lift_u :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    ∀ (v : ι), v ∉ F.Tb → ∀ (r' : F.D v →* GG 3 R'), Red (F.ηv v) (F.Ψv v) r' → F.LocAt v r' → IsLocallyConstant (mats r') →
      (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ r : F.D v →* GG 3 R, push p r = r' ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧ ∀ g, GrMat 𝒜 (r g).mat := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R R' _ _ _ _ _ _ 𝒜 _ p j hp hS v hv r' hred hloc hlc hgr
  haveI := hS.fin
  haveI : Finite (GG 3 R) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  obtain ⟨S, hSm⟩ := lu_sub 𝒜
  letI := Fintype.ofFinite (ResidueField O)
  obtain ⟨l, hchar, n, hl, hcard⟩ := FiniteField.card' (ResidueField O)
  have hkill : ∀ x y : R, x ∈ maximalIdeal R → p y = 0 → x * y = 0 := fun x y hx hy => by
    have := Ideal.mul_mem_mul hx (show y ∈ RingHom.ker p from hy)
    rwa [hS.kill] at this
  have hlm : (l : R) ∈ maximalIdeal R := by
    rw [← res_eq_zero_iff O, map_natCast]
    exact CharP.cast_eq_zero _ l
  obtain ⟨hK, hKl⟩ := lu_ker (p : R →+* R') (fun x y hx hy => hkill x y (hS.le hx) hy) l
    (fun x hx => hkill _ x hlm hx)
  have hle : ¬ l ∣ 2 * Nat.card (ResidueField O)ˣ := by
    rw [hl.dvd_mul, Nat.card_units, Nat.card_eq_fintype_card, hcard]
    rintro (h | h)
    · have h2 : ((2 : ℕ) : ResidueField O) = 0 := (CharP.cast_eq_zero_iff _ l 2).2 h
      have h3 := hF.two.map (residue O)
      rw [map_ofNat] at h3
      exact h3.ne_zero (by exact_mod_cast h2)
    · have h1 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
      have h2 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h1 h
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hl.pos)] at h2
      exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨φ, hφ, hd⟩ := hF.frob v
  have hU := hloc.2.2 hv
  have hlc' : IsLocallyConstant r' := by
    have h1 : IsLocallyConstant (F.ηv v) :=
      hF.η_cont.comp_continuous (hF.π_cont.comp continuous_subtype_val)
    refine IsLocallyConstant.desc r' (fun x : GG 3 R' => (x.mat, x.right)) ?_ ?_
    · have := hlc.prodMk h1
      convert this using 1
      funext g
      exact Prod.ext rfl (hred.mult g)
    · intro x y h
      exact SemidirectProduct.ext (Units.ext (congrArg Prod.fst h)) (congrArg Prod.snd h)
  have hs : ∀ g, ∃ h : S, ((GG.map (p : R →+* R')).comp S.subtype) h = r' g := by
    intro g
    obtain ⟨X, hX, hXp⟩ := hgr g
    have hu : IsUnit X := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have h1 : IsUnit (p X.det) := by
        have : p X.det = (r' g).mat.det := by
          rw [← hXp]; exact (p : R →+* R').map_det X
        rw [this, ← Matrix.isUnit_iff_isUnit_det]
        exact (r' g).left.isUnit
      by_contra hn
      have h2 : X.det ∈ maximalIdeal R := hn
      rw [← res_eq_zero_iff O, ← res_map p, res_eq_zero_iff] at h2
      exact h2 h1
    exact ⟨⟨⟨hu.unit, (r' g).right⟩, (hSm _).2 hX⟩, SemidirectProduct.ext (Units.ext hXp) rfl⟩
  have he : ∀ s ∈ F.Iv v, r' s ^ (2 * Nat.card (ResidueField O)ˣ) = 1 := fun s hs => by
    rw [← map_pow]
    refine hU _ ⟨⟨pow_mem hs _, ?_⟩, ?_⟩
    · show F.ηv v _ = 1
      rw [map_pow, pow_mul, Int.units_sq, one_pow]
    · show ((Units.map (residue O).toMonoidHom).comp (F.Ψv v)) _ = 1
      rw [map_pow, pow_mul', pow_card_eq_one', one_pow]
  obtain ⟨r, hr, hrl, hrI⟩ := lu_abs ((GG.map (p : R →+* R')).comp S.subtype)
    (fun a b ha hb => Subtype.ext (hK _ _ ha hb)) l _ hl hle (fun a ha => Subtype.ext (hKl _ ha))
    (F.Iv v) (hF.I_normal v) φ hφ hd r' hlc' hs he
  refine ⟨S.subtype.comp r, MonoidHom.ext hr, ⟨fun h => ?_, fun h => ?_, fun _ s hs => ?_⟩,
    hrl.comp fun x : S => x.1.mat, fun g => (hSm _).1 (r g).2⟩
  · exact (hv (Or.inl h)).elim
  · exact (hv (Or.inr h)).elim
  · exact congrArg Subtype.val (hrI s hs.1.1 (hU s hs))
