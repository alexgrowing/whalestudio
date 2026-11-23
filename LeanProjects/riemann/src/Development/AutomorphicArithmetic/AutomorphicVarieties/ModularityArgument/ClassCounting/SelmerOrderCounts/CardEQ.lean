import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.LatDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PermDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.UnitLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ValuationUnitNeZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem card_prod (E : Type) [AddCommGroup E] (δ : Module.End ℤ E) (m : ℕ) :
    Nonempty (((E × ℤ) ⧸ (LinearMap.range (δ.prodMap ((-(m : ℤ)) • LinearMap.id)) ⊔ Submodule.torsion ℤ (E × ℤ))) ≃
      (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) × ZMod m) := by
  let φ : (E × ℤ) →ₗ[ℤ] (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) × ZMod m :=
    (Submodule.mkQ _).prodMap (Int.castAddHom (ZMod m)).toIntLinearMap
  have hs : Function.Surjective φ := fun ⟨x, y⟩ => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨(x, y), rfl⟩
  have hk : LinearMap.ker φ =
      LinearMap.range (δ.prodMap ((-(m : ℤ)) • LinearMap.id)) ⊔ Submodule.torsion ℤ (E × ℤ) := by
    ext ⟨x, y⟩
    rw [LinearMap.mem_ker, Prod.ext_iff, Submodule.mem_sup]
    change (Submodule.Quotient.mk x = 0 ∧ (y : ZMod m) = 0) ↔ _
    rw [Submodule.Quotient.mk_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd, Submodule.mem_sup]
    constructor
    · rintro ⟨⟨_, ⟨a, rfl⟩, t, ⟨r, hr⟩, rfl⟩, k, rfl⟩
      exact ⟨_, ⟨(a, -k), rfl⟩, (t, 0), ⟨r, Prod.ext hr (by simp)⟩, by simp⟩
    · rintro ⟨_, ⟨⟨a, k⟩, rfl⟩, ⟨t, s⟩, ⟨r, hr⟩, h⟩
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
      obtain ⟨h3, h4⟩ := Prod.ext_iff.1 hr
      have hs : s = 0 := (mul_eq_zero.1 (show (r : ℤ) * s = 0 from h4)).resolve_left (nonZeroDivisors.coe_ne_zero r)
      refine ⟨⟨_, ⟨a, rfl⟩, t, ⟨r, h3⟩, h1⟩, -k, ?_⟩
      simpa [hs] using h2.symm
  exact ⟨((Submodule.quotEquivOfEq _ _ hk.symm).trans (φ.quotKerEquivOfSurjective hs)).toEquiv⟩

theorem UpperTheory.V.ZK.Ct.cardEQ :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsTotallyComplex L → IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → IsDat γ a D → Finite D.EQ ∧ Nat.card D.EQ * (a - 1) = (a ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L := by
  intro L F _ _ _ _ _ γ a D hL hG hγ hD
  classical
  obtain ⟨hF, hc, hfree⟩ := places L F γ hL hG hγ
  have ha : 2 ≤ a := hD.a_eq ▸ D.two_le
  have hn : 0 < orderOf γ := hD.n_eq ▸ D.n_pos
  let ι : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive Fˣ :=
    (MonoidHom.toAdditive (Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F))).toIntLinearMap
  have hι : Function.Injective ι := Units.map_injective RingOfIntegers.coe_injective
  have hr : LinearMap.range ι = LinearMap.ker D.d := by
    ext α
    obtain ⟨α, rfl⟩ := Additive.ofMul.surjective α
    have hv : D.d (Additive.ofMul α) = 0 ↔ ∀ P : HeightOneSpectrum (𝓞 F), P.valuation F (α : F) = 1 := by
      rw [Finsupp.ext_iff]
      refine forall_congr' fun P => ?_
      rw [hD.d_eq, valuation_eq_exp_ordP, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero]; rfl
    rw [LinearMap.mem_ker, hv]
    constructor
    · rintro ⟨u, hu⟩ P
      obtain rfl : Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u.toMul = α := hu
      refine le_antisymm (P.valuation_le_one (K := F) _) ?_
      have h1 := P.valuation_le_one (K := F) ((u.toMul⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
      have h2 : P.valuation F (algebraMap (𝓞 F) F (u.toMul : (𝓞 F)ˣ)) *
          P.valuation F (algebraMap (𝓞 F) F ((u.toMul⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) = 1 := by
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
      calc (1 : _) = _ := h2.symm
        _ ≤ _ * 1 := mul_le_mul_right h1 _
        _ = _ := mul_one _
    · intro h
      obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (α : F) fun P => (h P).le
      obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((α⁻¹ : Fˣ) : F) fun P => by
        rw [Units.val_inv_eq_inv_val, map_inv₀, h P, inv_one]
      have hxy : x * y = 1 := RingOfIntegers.coe_injective (by rw [map_mul, hx, hy, map_one, Units.mul_inv])
      exact ⟨Additive.ofMul (Units.mkOfMulEqOne x y hxy), Units.ext hx⟩
  let g : Module.End ℤ (Additive (𝓞 F)ˣ) := (MonoidHom.toAdditive (Units.map
    (RingOfIntegers.mapRingEquiv (γ⁻¹).toRingEquiv : 𝓞 F →* 𝓞 F))).toIntLinearMap
  let δ : Module.End ℤ (Additive (𝓞 F)ˣ) := g - (a : ℤ) • 1
  have hδ : ∀ u, ι (δ u) = D.del (ι u) := fun u => by
    have : ι (g u) = D.g (ι u) := by
      refine Eq.trans ?_ (hD.g_eq (ι u).toMul).symm
      exact congrArg Additive.ofMul (Units.ext rfl)
    simp only [δ, Dat.del, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_zsmul, this, hD.a_eq]
  let e : Additive (𝓞 F)ˣ ≃ₗ[ℤ] LinearMap.ker D.d := (LinearEquiv.ofInjective ι hι).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ u, (e u : Additive Fˣ) = ι u := fun _ => rfl
  have e2 : (Additive (𝓞 F)ˣ ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ _)) ≃ₗ[ℤ] D.EQ := by
    refine Submodule.Quotient.equiv _ _ e ?_
    ext y
    obtain ⟨u, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, e.symm_apply_apply, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, he,
      Submodule.mem_sup, Submodule.mem_sup]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, t, ⟨r, ht⟩, rfl⟩
      refine ⟨_, ⟨ι v, hr ▸ ⟨v, rfl⟩, rfl⟩, ι t, ⟨r, ?_⟩, by rw [map_add, hδ]⟩
      rw [Submonoid.smul_def] at ht ⊢
      rw [← map_smul, ht, map_zero]
    · rintro ⟨_, ⟨v, hv, rfl⟩, t, ⟨r, ht⟩, h⟩
      rw [← hr] at hv
      obtain ⟨v, rfl⟩ := hv
      refine ⟨_, ⟨v, rfl⟩, u - δ v, ⟨r, hι ?_⟩, by abel⟩
      rw [Submonoid.smul_def] at ht ⊢
      rw [map_smul, map_sub, hδ, ← h, add_sub_cancel_left, ht, map_zero]
  let lam : Additive (𝓞 F)ˣ × ℤ →ₗ[ℤ] (InfinitePlace F → ℝ) := AddMonoidHom.toIntLinearMap
    { toFun := fun x w => Real.log (w ((x.1.toMul : 𝓞 F) : F)) + x.2
      map_zero' := by ext w; simp
      map_add' := fun x y => by
        ext w
        simp only [Prod.fst_add, toMul_add, Units.val_mul, map_mul, Prod.snd_add, Int.cast_add, Pi.add_apply]
        rw [Real.log_mul (Units.pos_at_place _ _).ne' (Units.pos_at_place _ _).ne']; ring }
  obtain ⟨u1, u2, u3⟩ := unitLat F hF lam fun _ _ _ => rfl
  have hdet := permDet (InfinitePlace F) (MulAction.toPerm γ) (orderOf γ) _ (a : ℝ) hn (by exact_mod_cast (by omega : 1 ≤ a)) hc
    fun k w => by rw [← hfree, ← MulAction.toPermHom_apply, ← map_pow]; rfl
  have h1 : (1 : ℝ) < (a : ℝ) ^ orderOf γ := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < a)) hn.ne'
  obtain ⟨f1, f2⟩ := latDet _ _ lam (δ.prodMap ((-((a - 1 : ℕ) : ℤ)) • LinearMap.id))
    (LinearMap.funLeft ℝ ℝ (MulAction.toPerm γ : Equiv.Perm (InfinitePlace F)) - (a : ℝ) • LinearMap.id) (by
      rintro ⟨u, m⟩
      have h2 : lam (g u, m) = LinearMap.funLeft ℝ ℝ (MulAction.toPerm γ : Equiv.Perm (InfinitePlace F)) (lam (u, m)) := by
        ext w; rfl
      have h3 : (δ.prodMap ((-((a - 1 : ℕ) : ℤ)) • LinearMap.id)) (u, m) = (g u, m) - (a : ℤ) • (u, m) := by
        refine Prod.ext rfl ?_
        simp only [LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Prod.snd_sub, Prod.smul_snd]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [h3, map_sub, h2, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul,
        Nat.cast_smul_eq_nsmul]) u1 u2 u3
    (by rw [← abs_pos, hdet]; exact pow_pos (by linarith) _)
  obtain ⟨e3⟩ := card_prod _ δ (a - 1)
  haveI : NeZero (a - 1) := ⟨by omega⟩
  have f3 := (e3.finite_iff).1 f1
  refine ⟨e2.toEquiv.finite_iff.1 (Finite.prod_left (ZMod (a - 1))), ?_⟩
  rw [Nat.card_congr e3, Nat.card_prod, Nat.card_zmod, Nat.card_congr e2.toEquiv, hdet] at f2
  have h4 : 1 ≤ a ^ orderOf γ := Nat.one_le_pow _ _ (by omega)
  exact_mod_cast f2.trans (by rw [Nat.cast_pow, Nat.cast_sub h4]; push_cast; rfl :
    ((a : ℝ) ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L = (((a ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L : ℕ) : ℝ))
