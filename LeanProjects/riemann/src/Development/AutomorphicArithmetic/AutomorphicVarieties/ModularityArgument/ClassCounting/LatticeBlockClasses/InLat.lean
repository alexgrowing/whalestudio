import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlock

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem val_one {F : Type} [Field F] [NumberField F] (u : (𝓞 F)ˣ) (P : HeightOneSpectrum (𝓞 F)) :
    P.valuation F ((toF u : Fˣ) : F) = 1 := by
  show P.valuation F (algebraMap (𝓞 F) F (u : 𝓞 F)) = 1
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl, Ideal.mem_primeCompl_iff]
  exact fun hm => P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm u.isUnit)

theorem UpperTheory.V.ZK.Cl.cRep :
    UpperTheory.V.ZK.Cl.CRep := by
  intro L F _ _ _ _ _ q _ ζ h
  have hq := toF_pow h
  have hmod : ∀ n : ℕ, toF ζ ^ n = toF ζ ^ (n % q) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, hq, one_pow, one_mul]
  have hv1 : ∀ P : HeightOneSpectrum (𝓞 F), P.valuation F ((toF ζ : Fˣ) : F) = 1 :=
    fun P => val_one ζ P
  have hrep : ∀ (x : Cq q × Cq q) (y : ZMod q × ZMod q → F) (j : ZMod q × ZMod q)
      (P : HeightOneSpectrum (𝓞 F)), P.valuation F (repD L q ζ h x y j) = P.valuation F (y j) := by
    intro x y j P
    simp only [repD, MonoidHom.comp_apply, diag, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearEquiv.piCongrRight_apply, DistribMulAction.toLinearEquiv_apply, MonoidHom.pi_apply,
      MonoidHom.coprod_apply, chi, Units.smul_def, Units.val_mul, Units.val_pow_eq_pow_val,
      smul_eq_mul, map_mul, map_pow, hv1, one_pow, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t c
    simp only [repD, repC, dt, MonoidHom.comp_apply]
    congr 1
    funext j
    simp only [MonoidHom.pi_apply, MonoidHom.coprod_apply, MonoidHom.prod_apply, MonoidHom.id_apply,
      powMonoidHom_apply, chi, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← pow_add, hmod, hmod ((j.1 + (t : ZMod q) * j.2).val * _)]
    congr 1
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    push_cast [ZMod.natCast_val, ZMod.cast_id', toAdd_pow]
    simp only [id]
    ring
  · intro 𝔞 x
    show ∀ y, InLat 𝔞 y ↔ InLat 𝔞 (repD L q ζ h x y)
    intro y
    unfold InLat
    simp only [hrep]
  · intro b x
    show ∀ y, InLoc b y ↔ InLoc b (repD L q ζ h x y)
    intro y
    unfold InLoc
    simp only [hrep]
  · intro J _ χ 𝔟 δ g hC c
    obtain ⟨_, s, β, g', hB, hsβ, _⟩ := hC
    have hc := ((cBlock L F J (ZMod q) s β g').2 g hB).1
      (fun j => toF ζ ^ ((χ j).val * (Multiplicative.toAdd c).val))
      (fun x => toF ζ ^ (x.val * (Multiplicative.toAdd c).val))
      (by
        intro j
        rw [map_pow, pow_mul, hsβ j, ← pow_mul])
    exact hc
  · intro hp
    have hinj : Function.Injective (Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F)) :=
      Units.map_injective (IsFractionRing.injective (𝓞 F) F)
    have hp' : IsPrimitiveRoot (toF ζ) q := hp.map_of_injective hinj
    have hex : ∀ σ : Gal(F/L), ∃ i : ℕ, actU σ (toF ζ) = toF ζ ^ i := by
      intro σ
      have hσ : (actU σ (toF ζ)) ^ q = 1 := by rw [← map_pow, hq, map_one]
      obtain ⟨i, _, hi⟩ := hp'.eq_pow_of_mem_rootsOfUnity (ξ := actU σ (toF ζ))
        ((mem_rootsOfUnity _ _).2 hσ)
      exact ⟨i, hi.symm⟩
    choose kap hk using hex
    exact ⟨kap, hk⟩
