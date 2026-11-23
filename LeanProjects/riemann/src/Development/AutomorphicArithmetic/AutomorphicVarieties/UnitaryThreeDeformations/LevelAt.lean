import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.DyadicCharacterPowerNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalMultiplication

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem conj_left {R : Type} [CommRing R] (x y : GG 3 R) (hy : y.right = 1) :
    (x * y * x⁻¹).left = x.left * sgnAct 3 R x.right y.left * x.left⁻¹ := by
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left, hy, mul_one]
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem conjBy_left {D R : Type} [Group D] [CommRing R] (h : GL (Fin 3) R) (r : D →* GG 3 R) (d : D)
    (hd : (r d).right = 1) : (conjBy h r d).left = h * (r d).left * h⁻¹ := by
  have := conj_left (GG.ofGL h) (r d) hd
  rw [SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one] at this
  exact this

private theorem conjBy_right {D R : Type} [Group D] [CommRing R] (h : GL (Fin 3) R) (r : D →* GG 3 R) (d : D) :
    (conjBy h r d).right = (r d).right := by
  show (GG.ofGL h * r d * (GG.ofGL h)⁻¹).right = _
  simp

private theorem diag_mul {R : Type} [CommRing R] (X Y : Matrix (Fin 3) (Fin 3) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin 3) : (X * Y) a a = X a a * Y a a :=
  _root_.UpperTheory.Reformulated.B.UpperTriangularThreeDiagonalOfMul.diag_mul X Y hX hY a

private theorem tri_sgn {R : Type} [CommRing R] (ε : ℤˣ) (T : GL (Fin 3) R) (hT : ∀ i j, j < i → T i j = 0) :
    (∀ i j, j < i → sgnAct 3 R ε T i j = 0) ∧ ∀ (u : Rˣ) (I : Ideal R), (∀ a, T a a - ((u ^ wt1 a : Rˣ) : R) ∈ I) →
      ∀ a, sgnAct 3 R ε T a a - ((u ^ wt1 a : Rˣ) : R) ∈ I := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [sgnAct_one]
    exact ⟨hT, fun _ _ h => h⟩
  rw [sgnAct_neg_one]
  have h1 : ∀ a b, theta T a b = (T⁻¹ : GL (Fin 3) R) b.rev a.rev := by
    intro a b
    rw [theta_val]
    generalize ((T⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = X
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  have h2 : ∀ i j, j < i → (T⁻¹ : GL (Fin 3) R) i j = 0 := by
    have := T.invertible
    have h3 : (T : Matrix (Fin 3) (Fin 3) R).BlockTriangular id := fun i j h => hT i j h
    have h4 := Matrix.blockTriangular_inv_of_blockTriangular h3
    intro i j h
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact h4 h
  refine ⟨fun i j h => by rw [h1, h2 _ _ (Fin.rev_lt_rev.2 h)], fun u I h a => ?_⟩
  have h5 := diag_mul _ _ hT h2 a.rev
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq] at h5
  have h6 : ((u ^ wt1 a : Rˣ) : R) * ((u ^ wt1 a.rev : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, ← _root_.zpow_add, show wt1 a + wt1 a.rev = 0 by fin_cases a <;> rfl, zpow_zero, Units.val_one]
  rw [h1]
  have h7 := I.mul_mem_left (-((T⁻¹ : GL (Fin 3) R) a.rev a.rev * ((u ^ wt1 a : Rˣ) : R))) (h a.rev)
  convert h7 using 1
  linear_combination (-((u ^ wt1 a : Rˣ) : R)) * h5 - (T⁻¹ : GL (Fin 3) R) a.rev a.rev * h6

private theorem unit_sep {R : Type} [CommRing R] [IsLocalRing R] (u : Rˣ) (hu : IsUnit ((u : R) ^ 2 - 1)) {i j : Fin 3}
    (hij : i ≠ j) : ((u ^ wt1 i : Rˣ) : R) - ((u ^ wt1 j : Rˣ) : R) ∉ maximalIdeal R := by
  intro h
  have h1 := (Ideal.Quotient.eq (I := maximalIdeal R)).2 h
  have h2 : Units.map (residue R).toMonoidHom u ^ wt1 i = Units.map (residue R).toMonoidHom u ^ wt1 j := by
    rw [← map_zpow, ← map_zpow]
    exact Units.ext h1
  have h3 : Units.map (residue R).toMonoidHom u ^ 2 = 1 := by
    generalize Units.map (residue R).toMonoidHom u = v at h2
    have h4 : v ^ (wt1 i - wt1 j) = 1 := by rw [_root_.zpow_sub, h2, mul_inv_cancel]
    have h5 : wt1 i - wt1 j ∣ 2 := by
      revert hij; fin_cases i <;> fin_cases j <;> simp [wt1] <;> decide
    obtain ⟨k, hk⟩ := h5
    rw [← zpow_natCast, Nat.cast_ofNat, hk, _root_.zpow_mul, h4, _root_.one_zpow]
  have h6 : residue R ((u : R) ^ 2 - 1) = 0 := by
    rw [map_sub, map_pow, map_one, sub_eq_zero]
    exact congrArg Units.val h3
  exact (residue_eq_zero_iff _).1 h6 hu

private theorem key {O K G Γ ι A : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] [Group G] [Group Γ]
    [TopologicalSpace Γ] (F : Frame O G Γ ι) (g₁ : Γ) (r : Γ →* GG 3 K) [CommRing A] [IsLocalRing A] [Algebra O A]
    [IsLocalHom (algebraMap O A)] (val : A →ₐ[O] K) (hval : Function.Injective val) (t : Kˣ) (r' : Γ →* GG 3 A)
    (hpt : F.IsPt g₁ r') (hpush : push val r' = conjBy (tor K t) r) (γ : Γ) :
    ∃ P : GL (Fin 3) K, ∀ d : F.D F.vl, F.ηv _ d = 1 → ∀ X, X = P * (r (γ * F.loc _ d * γ⁻¹)).left * P⁻¹ →
      (∀ i j, j < i → X i j = 0) ∧ (d ∈ F.Iv _ → ∀ a, X a a = algebraMap O K (psi (F.Ψv _) a d)) ∧
      (IsUnit ((F.Ψv _ d : O) ^ 2 - 1) → ∀ u : O, u - 1 ∈ maximalIdeal O → ∀ i j, i ≠ j →
        X i i ≠ X j j * algebraMap O K u) := by
  obtain ⟨h, hh, htri⟩ := (hpt.loc F.vl).1 rfl
  let f : GL (Fin 3) A →* GL (Fin 3) K := GeneralLinearGroup.map (val : A →+* K)
  let ε := (r' γ).right
  refine ⟨f (sgnAct 3 A ε h⁻¹ * (r' γ).left⁻¹) * tor K t, fun d hd X hX => ?_⟩
  have hd' : (r' (F.loc _ d)).right = 1 := (hpt.mult _).trans hd
  let T := (conjBy h⁻¹ (r'.comp (F.loc _)) d).left
  have hT : T = h⁻¹ * (r' (F.loc _ d)).left * h := by
    have := conjBy_left h⁻¹ (r'.comp (F.loc _)) d hd'
    rwa [inv_inv] at this
  have e1 : ∀ s, (r' s).right = 1 → f (r' s).left = tor K t * (r s).left * (tor K t)⁻¹ := fun s hs => by
    have h1 := DFunLike.congr_fun hpush s
    have h2 : (r s).right = 1 := by
      rw [← conjBy_right (tor K t), ← h1]; exact hs
    rw [← conjBy_left _ _ _ h2, ← h1]
    rfl
  have e2 : X = f (sgnAct 3 A ε T) := by
    have h1 := e1 (γ * F.loc _ d * γ⁻¹) (by simp [hd'])
    rw [map_mul, map_mul, map_inv, conj_left _ _ hd'] at h1
    have h2 : (r (γ * F.loc _ d * γ⁻¹)).left = (tor K t)⁻¹ * f ((r' γ).left * sgnAct 3 A ε (r' (F.loc _ d)).left *
      (r' γ).left⁻¹) * tor K t := by
      rw [h1]; group
    rw [hX, h2, hT]
    simp only [map_mul, map_inv]
    group
  have e3 : ∀ i j, X i j = val (sgnAct 3 A ε T i j) := fun i j => by rw [e2]; rfl
  have up : ∀ i j, j < i → T i j = 0 := fun i j hij => htri.tri d hd i j (by
    have : (j : ℕ) < i := hij
    simp only [wt, wt1]; omega)
  obtain ⟨s1, s2⟩ := tri_sgn ε T up
  let u₀ : Aˣ := Units.map (algebraMap O A).toMonoidHom (F.Ψv _ d)
  have hu : ∀ a, ((u₀ ^ wt1 a : Aˣ) : A) = algebraMap O A (psi (F.Ψv _) a d) := fun a => by
    rw [← map_zpow]; rfl
  refine ⟨fun i j hij => by rw [e3, s1 i j hij, map_zero], fun hI a => ?_, fun hun u hu1 i j hij he => ?_⟩
  · have := s2 u₀ ⊥ (fun a => by rw [Ideal.mem_bot, sub_eq_zero, hu]; exact htri.ine d hI hd a) a
    rw [Ideal.mem_bot, sub_eq_zero, hu] at this
    rw [e3, this, AlgHom.commutes]
  · have hres : ∀ a, T a a - ((u₀ ^ wt1 a : Aˣ) : A) ∈ maximalIdeal A := fun a => by
      have h1 : GeneralLinearGroup.map (residue A) h = 1 := by
        ext a b
        have := (residue_eq_zero_iff _).2 (hh a b)
        rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
        refine this.trans ?_
        simp [Matrix.one_apply, apply_ite (residue A)]
      have h2 : GeneralLinearGroup.map (residue A) T = GeneralLinearGroup.map (residue A) (r' (F.loc _ d)).left := by
        rw [hT, map_mul, map_mul, map_inv, h1, inv_one, one_mul, mul_one]
      have h3 : residue A (T a a) = residue A ((r' (F.loc _ d)).mat a a) :=
        congrArg (fun Y : GL (Fin 3) (ResidueField A) => Y a a) h2
      have h4 := hpt.red (F.loc _ d) a a
      have h5 : ((r0 F.η F.Ψ (F.loc _ d)).mat.map (algebraMap O A)) a a = ((u₀ ^ wt1 a : Aˣ) : A) := by
        rw [hu, Matrix.map_apply, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq]
        rfl
      rw [Matrix.sub_apply, h5, ← residue_eq_zero_iff, map_sub] at h4
      rw [← residue_eq_zero_iff, map_sub, h3, h4]
    have h6 := s2 u₀ _ hres
    have h7 : algebraMap O A u - 1 ∈ maximalIdeal A := by
      rw [← map_one (algebraMap O A), ← map_sub]
      exact map_nonunit _ _ hu1
    have h8 : sgnAct 3 A ε T i i = sgnAct 3 A ε T j j * algebraMap O A u := by
      rw [e3, e3] at he
      exact hval (by rw [he, map_mul, AlgHom.commutes])
    refine unit_sep u₀ (by simpa [u₀] using hun.map (algebraMap O A)) hij ?_
    have h9 := sub_mem (add_mem (h6 j) ((maximalIdeal A).mul_mem_left (sgnAct 3 A ε T j j) h7)) (h6 i)
    convert h9 using 1
    rw [h8]; ring

private theorem loc_hom {O K : Type} [CommRing O] [Field K] [Algebra O K] (hinj : Function.Injective (algebraMap O K))
    (A : Subalgebra O K) [Module.Finite O A] : IsLocalHom (algebraMap O A) := by
  have : FaithfulSMul O A := (faithfulSMul_iff_algebraMap_injective O A).2 fun x y hxy =>
    hinj (congrArg A.val hxy)
  exact Algebra.IsIntegral.isLocalHom O A

private theorem chr_conj {G C : Type} [Group G] [CommGroup C] (χ : G →* C) (u x : G) : χ (u⁻¹ * x * u) = χ x := by
  rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]

private theorem exists_diag {H k : Type} [Group H] [Field k] (X : H →* GL (Fin 3) k)
    (hX : ∀ s i j, j < i → X s i j = 0) : ∃ κ : Fin 3 → H →* kˣ, ∀ i s, X s i i = κ i s :=
  ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => X s i i
      map_one' := by simp
      map_mul' := fun s t => by rw [map_mul, Units.val_mul, diag_mul _ _ (hX s) (hX t)] }, fun _ _ => rfl⟩

open UpperTheory.V.Base in
theorem UpperTheory.V.UnitaryThreeInertia.levelAt_of_pt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω], IsQi K → ∀ (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r → ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), (∀ s : G K Ω, (ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)) = (r (toGS Ω _ (s.restrictScalars ℚ))).mat) → Af.LevelAt l N ![(e : ℤ), 0, -(e : ℤ)] ρ := by
  intro Ω _ _ _ l hl c N _ e ψ o₁ hD S A F hF K _ _ _ _ hK g₁ _ r hr ρ hρ w hw
  obtain ⟨A', _, _, t, r', hpt, hpush⟩ := hr
  have := loc_hom (O := c.O) Subtype.val_injective A'
  let B := placeOf Ω w
  have hB : IsPlaceOver B w := isPlaceOver_placeOf Ω w
  have hBl : B.valuation (l : Ω) < 1 := by
    have h := hB ((l : ℕ) : 𝓞 K)
    have e : algebraMap K Ω (((l : ℕ) : 𝓞 K) : K) = (l : Ω) := by simp
    rw [e] at h
    exact h.2 hw
  have hAl : (A F.vl).valuation (l : Ω) < 1 := by
    have h := hF.isOver F.vl ((l : ℕ) : 𝓞 ℚ)
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h
    exact h.2 hF.vl
  obtain ⟨u, hu, huI⟩ := (Chr.placesQ Ω).2.2 l B _ hl.out hBl hAl
  obtain ⟨u', hu', -⟩ := (Chr.placesQ Ω).2.2 l _ B hl.out hAl hBl
  have hrg := (gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1
  have hη : ∀ d : F.D F.vl, F.ηv _ d = eta4 Ω d := fun d => DFunLike.congr_fun hF.η d.1
  have hΨ : ∀ d : F.D F.vl, F.Ψv _ d = Chr.Psi l e (Chr.dirG ℚ Ω ψ) d := fun d => DFunLike.congr_fun hF.Ψ d.1
  have hDec : ∀ s : G K Ω, s ∈ Dec (F := K) B ↔ galEmb ℚ K Ω s ∈ Dec (F := ℚ) B := fun s => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  have hIne : ∀ s : G K Ω, s ∈ Ine (F := K) B ↔ galEmb ℚ K Ω s ∈ Ine (F := ℚ) B := fun s =>
    and_congr (hDec s) Iff.rfl
  obtain ⟨P, hP⟩ := key F g₁ r A'.val Subtype.val_injective t r' hpt hpush (F.π u)
  let d : Dec (F := K) B → F.D F.vl := fun s => ⟨u⁻¹ * galEmb ℚ K Ω s * u, hF.D _ ▸ hu _ ((hDec s).1 s.2)⟩
  have hd : ∀ s, F.ηv _ (d s) = 1 := fun s => by
    rw [hη, chr_conj, ← MonoidHom.mem_ker, ← hrg]
    exact ⟨_, rfl⟩
  have hP' := fun s : Dec (F := K) B => hP (d s) (hd s) (P * ρ s * P⁻¹) (by
    have h1 : F.π u * F.loc _ (d s) * (F.π u)⁻¹ = toGS Ω _ (galEmb ℚ K Ω s) := by
      show F.π u * F.π (u⁻¹ * galEmb ℚ K Ω s * u) * (F.π u)⁻¹ = _
      rw [← hF.π, map_mul, map_mul, map_inv]
      group
    rw [h1, show ρ s = (r (toGS Ω _ (galEmb ℚ K Ω s))).left from Units.ext (hρ s)])
  obtain ⟨κ, hκ⟩ := exists_diag ((MulAut.conj P).toMonoidHom.comp (ρ.comp (Dec (F := K) B).subtype))
    fun s => (hP' s).1
  replace hκ : ∀ i (s : Dec (F := K) B), (P * ρ s * P⁻¹ : GL (Fin 3) (Qbar l)) i i = κ i s := hκ
  let m : c.Oˣ →* (Qbar l)ˣ := Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom
  have hcyc : ∀ s : G K Ω, cycBar K Ω l s = m (chiO ℚ Ω l c.O (galEmb ℚ K Ω s)) := fun s => Units.ext rfl
  refine ⟨B, hB, fun i => (m.comp ((Chr.dirG ℚ Ω ψ).comp (galEmb ℚ K Ω))) ^ wt1 i, κ, fun i s hs => ?_,
    ⟨P, fun s => ⟨(hP' s).1, fun i => hκ i s⟩⟩, fun i s hs => ?_, Or.inl fun i j hij => ?_⟩
  · have h1 : Chr.cls ℚ Ω N (galEmb ℚ K Ω s) = 1 := (Chr.clsFacts ℚ Ω N).2.2.1 _ 1 fun x hx => by
      refine (hs x hx).trans ?_
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hx, pow_one]
    show m (ψ.toUnitHom (Chr.cls ℚ Ω N (galEmb ℚ K Ω s))) ^ wt1 i = 1
    rw [h1, map_one, map_one, _root_.one_zpow]
  · have h1 := (hP' s).2.1 (by
      rw [Subgroup.mem_subgroupOf, hF.I]
      exact huI _ ((hIne s).1 hs)) i
    have h2 : κ i s = m (F.Ψv _ (d s) ^ wt1 i) := Units.ext ((hκ i s).symm.trans h1)
    rw [h2, hΨ, chr_conj, hcyc, show ![(e : ℤ), 0, -(e : ℤ)] i = e * wt1 i by fin_cases i <;> simp [wt1]]
    show m ((chiO ℚ Ω l c.O _ ^ (e : ℤ) * Chr.dirG ℚ Ω ψ _) ^ wt1 i) = _ * m (Chr.dirG ℚ Ω ψ _) ^ wt1 i
    rw [mul_zpow, map_mul, map_zpow, map_zpow, map_zpow, _root_.zpow_mul]
  · by_cases h : i = j
    · subst h
      have hun : IsUnit (1 + (l : ℤ_[l])) := by
        rw [PadicInt.isUnit_iff]
        exact_mod_cast PadicInt.norm_natCast_eq_one_iff.2 (show l.Coprime (1 + l) by simp)
      obtain ⟨σ, hσ, h1⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B hBl hun.unit
      have h2 : σ ^ 2 ∈ (galEmb ℚ K Ω).range := by
        rw [hrg, MonoidHom.mem_ker, map_pow, Int.units_sq]
      obtain ⟨s, hs⟩ := h2
      have h3 := DFunLike.congr_fun hij ⟨s, (hDec s).2 (hs ▸ pow_mem hσ.1 2)⟩
      rw [MonoidHom.mul_apply, left_eq_mul] at h3
      have h4 : cycZ K Ω l s = 1 := by
        refine Units.ext (Subtype.val_injective ((algebraMap ℚ_[l] (Qbar l)).injective ?_))
        exact (congrArg Units.val h3).trans (map_one _).symm
      have h5 : cycZ ℚ Ω l (galEmb ℚ K Ω s) = 1 := h4
      rw [hs, map_pow, h1] at h5
      have h6 : (1 + (l : ℤ_[l])) ^ 2 = 1 := congrArg Units.val h5
      have h7 : (1 + l) ^ 2 = 1 := by exact_mod_cast h6
      have := hl.out.pos
      nlinarith
    · obtain ⟨x, hx1, hx2, hx3⟩ := exists_sigma Ω c e ψ o₁ hD S A F hF F.vl (Set.mem_insert _ _)
      have h2 : u'⁻¹ * x * u' ∈ (galEmb ℚ K Ω).range := by
        rw [hrg, MonoidHom.mem_ker, chr_conj, ← hη, hx1]
      obtain ⟨s, hs⟩ := h2
      have hs' : s ∈ Dec (F := K) B := (hDec s).2 (hs ▸ hu' _ (hF.D _ ▸ x.2))
      have h3 := congrArg Units.val (DFunLike.congr_fun hij ⟨s, hs'⟩)
      refine (hP' ⟨s, hs'⟩).2.2 ?_ (chiO ℚ Ω l c.O (galEmb ℚ K Ω s) : c.Oˣ) ?_ i j h ?_
      · rwa [hΨ, chr_conj, hs, chr_conj, ← hΨ]
      · rw [hs, chr_conj]
        have : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
        have h4 : PadicInt.toZModPow 1 ((cycZ ℚ Ω l x : ℤ_[l]) - 1) = 0 := by
          have := congrArg Units.val hx3
          rw [map_sub, map_one, sub_eq_zero]
          simpa [cycMod] using this
        have h5 : (cycZ ℚ Ω l x : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := by
          rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow]
          exact h4
        have h6 := map_nonunit (algebraMap ℤ_[l] c.O) _ h5
        rwa [map_sub, map_one] at h6
      · rw [hκ, hκ, h3, MonoidHom.mul_apply, Units.val_mul]
        rfl
