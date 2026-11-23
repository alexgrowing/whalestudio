import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.LogRootDiscChar

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private lemma unitsMap_eq_one_iff_modEq {d : ℕ} (h : d ∣ N) (x : (ZMod N)ˣ) :
    ZMod.unitsMap h x = 1 ↔ (x : ZMod N).val ≡ 1 [MOD d] := by
  rw [← Units.val_inj, ZMod.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val]
  simp

private lemma crt_fst (x : ZMod N) :
    (crtEquiv N l x).1 = ZMod.castHom (Nat.ordProj_dvd N l) (ZMod (ordProj[l] N)) x :=
  RingHom.congr_fun (RingHom.ext_zmod
    ((RingHom.fst _ _).comp (crtEquiv N l).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd N l) (ZMod (ordProj[l] N)))) x

private lemma crt_snd (x : ZMod N) :
    (crtEquiv N l x).2 = ZMod.castHom (Nat.ordCompl_dvd N l) (ZMod (ordCompl[l] N)) x :=
  RingHom.congr_fun (RingHom.ext_zmod
    ((RingHom.snd _ _).comp (crtEquiv N l).toRingHom)
    (ZMod.castHom (Nat.ordCompl_dvd N l) (ZMod (ordCompl[l] N)))) x

private lemma localUnits_val (u : (ZMod (ordProj[l] N))ˣ) :
    ((localUnits N l u : (ZMod N)ˣ) : ZMod N) =
      (crtEquiv N l).symm ((u : ZMod (ordProj[l] N)), 1) := rfl

private lemma proj_localUnits (u : (ZMod (ordProj[l] N))ˣ) :
    ZMod.unitsMap (Nat.ordProj_dvd N l) (localUnits N l u) = u := by
  apply Units.ext
  have h := crt_fst l ((localUnits N l u : (ZMod N)ˣ) : ZMod N)
  rw [localUnits_val, RingEquiv.apply_symm_apply] at h
  exact h.symm

private lemma compl_localUnits (u : (ZMod (ordProj[l] N))ˣ) :
    ZMod.unitsMap (Nat.ordCompl_dvd N l) (localUnits N l u) = 1 := by
  apply Units.ext
  have h := crt_snd l ((localUnits N l u : (ZMod N)ˣ) : ZMod N)
  rw [localUnits_val, RingEquiv.apply_symm_apply] at h
  exact h.symm

private lemma localUnits_proj (x : (ZMod N)ˣ)
    (hx : ZMod.unitsMap (Nat.ordCompl_dvd N l) x = 1) :
    localUnits N l (ZMod.unitsMap (Nat.ordProj_dvd N l) x) = x := by
  apply Units.ext
  rw [localUnits_val, RingEquiv.symm_apply_eq]
  apply Prod.ext
  · rw [crt_fst]; rfl
  · rw [crt_snd]; exact (congrArg Units.val hx).symm

theorem localUnits_spec :
    Function.Injective (localUnits N l) ∧ (localUnits N l).range = inertiaUnits N l ∧
      ∀ u, ZMod.unitsMap (Nat.ordProj_dvd N l) (localUnits N l u) = u := by
  refine ⟨Function.LeftInverse.injective (proj_localUnits l), ?_, proj_localUnits l⟩
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact compl_localUnits l u
  · intro hx
    exact ⟨_, localUnits_proj l x hx⟩

private lemma localPart_toUnitHom (ψ : DirichletCharacter ℂ N) :
    MulChar.toUnitHom (localPart N l ψ) = (MulChar.toUnitHom ψ).comp (localUnits N l) := by
  ext u
  simp [localPart]

private lemma unitsMap_trans {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (x : (ZMod c)ˣ) :
    ZMod.unitsMap hab (ZMod.unitsMap hbc x) = ZMod.unitsMap (hab.trans hbc) x := by
  rw [← ZMod.unitsMap_comp hab hbc]; rfl

private lemma conductor_localPart_dvd_iff (ψ : DirichletCharacter ℂ N) (t : ℕ)
    (ht : t ≤ N.factorization l) :
    (localPart N l ψ).conductor ∣ l ^ t ↔ condExp l ψ ≤ t := by
  have hl : l.Prime := Fact.out
  have hN : N ≠ 0 := NeZero.ne N
  have : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  have h1 : l ^ t ∣ ordProj[l] N := pow_dvd_pow l ht
  have h2 : l ^ t * ordCompl[l] N ∣ N := by
    conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N l]
    exact Nat.mul_dvd_mul_right h1 _
  have hcop : (l ^ t).Coprime (ordCompl[l] N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)
  have hker : ∀ x : (ZMod N)ˣ, ZMod.unitsMap h2 x = 1 ↔
      ZMod.unitsMap (h1.trans (Nat.ordProj_dvd N l)) x = 1 ∧
        ZMod.unitsMap (Nat.ordCompl_dvd N l) x = 1 := by
    intro x
    simp only [unitsMap_eq_one_iff_modEq]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).symm
  have key : (localPart N l ψ).conductor ∣ l ^ t ↔ ψ.conductor ∣ l ^ t * ordCompl[l] N := by
    rw [← mem_conductorSet_iff_conductor_dvd _ h1, ← mem_conductorSet_iff_conductor_dvd _ h2,
      mem_conductorSet_iff, mem_conductorSet_iff, factorsThrough_iff_ker_unitsMap h1,
      factorsThrough_iff_ker_unitsMap h2, localPart_toUnitHom]
    constructor
    · intro h x hx
      rw [MonoidHom.mem_ker, hker] at hx
      have := h (x := ZMod.unitsMap (Nat.ordProj_dvd N l) x)
        (by rw [MonoidHom.mem_ker, unitsMap_trans]; exact hx.1)
      rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, localUnits_proj l x hx.2] at this
    · intro h u hu
      rw [MonoidHom.mem_ker] at hu
      refine h (x := localUnits N l u) ?_
      rw [MonoidHom.mem_ker, hker]
      refine ⟨?_, compl_localUnits l u⟩
      rw [← unitsMap_trans h1 (Nat.ordProj_dvd N l), proj_localUnits, hu]
  rw [key, condExp]
  have hc : ψ.conductor ≠ 0 := conductor_ne_zero ψ
  have hcN : ψ.conductor ∣ N := conductor_dvd_level ψ
  have hN' : ordCompl[l] N ≠ 0 := (Nat.ordCompl_pos l hN).ne'
  have hlt : l ^ t ≠ 0 := pow_ne_zero _ hl.ne_zero
  constructor
  · intro h
    have := (Nat.factorization_le_iff_dvd hc (mul_ne_zero hlt hN')).2 h l
    rw [Nat.factorization_mul hlt hN', Nat.factorization_ordCompl, hl.factorization_pow] at this
    simpa using this
  · intro h
    rw [← Nat.ordProj_mul_ordCompl_eq_self ψ.conductor l]
    exact Nat.mul_dvd_mul (pow_dvd_pow l h) (Nat.ordCompl_dvd_ordCompl_of_dvd hcN l)

theorem localPart_eq_one_iff (ψ : DirichletCharacter ℂ N) :
    (localPart N l ψ = 1 ↔ ∀ u ∈ inertiaUnits N l, ψ (u : ZMod N) = 1) ∧
      (localPart N l ψ = 1 ↔ ¬ l ∣ ψ.conductor) := by
  have hl : l.Prime := Fact.out
  have : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  constructor
  · rw [← (localUnits_spec l).2.1]
    constructor
    · rintro h _ ⟨u, rfl⟩
      have := congrArg (fun χ : DirichletCharacter ℂ (ordProj[l] N) =>
        χ (u : ZMod (ordProj[l] N))) h
      simpa [localPart] using this
    · intro h
      ext u
      simpa [localPart] using h _ ⟨u, rfl⟩
  · have := conductor_localPart_dvd_iff l ψ 0 (Nat.zero_le _)
    rw [pow_zero, Nat.dvd_one, Nat.le_zero] at this
    rw [eq_one_iff_conductor_eq_one, this, condExp,
      hl.dvd_iff_one_le_factorization (conductor_ne_zero ψ)]
    omega

end KStar.Ram
