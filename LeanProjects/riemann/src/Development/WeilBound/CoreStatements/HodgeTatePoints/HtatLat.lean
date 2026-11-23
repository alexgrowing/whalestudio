import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

noncomputable section

namespace PositivityTheory.HtPt.Htat

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT

theorem inj_mod_of_surj_mod {M : Type} [AddCommGroup M] [Module.Finite ℤ M] (f : M →ₗ[ℤ] M) (q : ℕ)
    (hs : ∀ a, ∃ z b, a = f z + q • b) (z b : M) (h : f z = q • b) : ∃ z', z = q • z' := by
  let K : Submodule ℤ M := LinearMap.range (q • (LinearMap.id : M →ₗ[ℤ] M))
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = q • b := fun a =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hle : K ≤ K.comap f := by
    intro a ha
    obtain ⟨b, rfl⟩ := (hK a).1 ha
    exact (hK _).2 ⟨f b, map_nsmul f q b⟩
  let g := K.mapQ K f hle
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := K.mkQ_surjective a
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨K.mkQ z, ?_⟩
    show K.mkQ (f z) = _
    rw [map_add, show K.mkQ (q • b) = 0 from (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, rfl⟩), add_zero]
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hg
  have h0 : g (K.mkQ z) = g 0 := by
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, h⟩)
  exact (hK z).1 ((Submodule.Quotient.mk_eq_zero K).1 (hi h0))

theorem surj_mod_pow {M L : Type} [AddCommGroup M] [AddCommGroup L] (σ : M →+ L) (p : ℕ)
    (h : ∀ a, ∃ z b, a = σ z + p • b) (n : ℕ) (a : L) : ∃ z b, a = σ z + (p ^ n) • b := by
  induction n with
  | zero => exact ⟨0, a, by simp⟩
  | succ n ih =>
    obtain ⟨z, b, rfl⟩ := ih
    obtain ⟨z', b', rfl⟩ := h b
    exact ⟨z + (p ^ n) • z', b', by rw [map_add, map_nsmul, smul_add, pow_succ, mul_smul, add_assoc]⟩

theorem perfect_mod {M L : Type} [AddCommGroup M] [AddCommGroup L] [Module.Free ℤ L] (σ : M →ₗ[ℤ] L) (q : ℕ)
    (EF : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hE : Function.Bijective EF) (hs : ∀ a, ∃ z b, a = σ z + q • b)
    (hk : ∀ z b, σ z = q • b → ∃ z', z = q • z') :
    (∀ φ : M →+ ZMod q, ∃ y, ∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = φ z) ∧
      ∀ y, (∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = 0) → ∃ y', y = q • y' := by
  let B := Module.Free.chooseBasis ℤ L
  constructor
  · intro φ
    choose zz cc hzc using hs
    let s : L →ₗ[ℤ] M := B.constr ℤ fun i => zz (B i)
    let t : L →ₗ[ℤ] L := B.constr ℤ fun i => cc (B i)
    have hst : ∀ a, a = σ (s a) + q • t a := by
      have : (LinearMap.id : L →ₗ[ℤ] L) = σ ∘ₗ s + q • t := B.ext fun i => by
        simpa [s, t] using hzc (B i)
      intro a
      simpa using LinearMap.congr_fun this a
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => ((φ (zz (B i))).cast : ℤ)
    have hψ : ∀ a, ((ψ a : ℤ) : ZMod q) = φ (s a) := by
      have : (Int.castAddHom (ZMod q)).toIntLinearMap ∘ₗ ψ = φ.toIntLinearMap ∘ₗ s := B.ext fun i => by
        simp [ψ, s]
      intro a
      simpa using LinearMap.congr_fun this a
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine ⟨zz a₀, fun z => ?_⟩
    obtain ⟨z', hz'⟩ := hk (z - s (σ z)) (t (σ z)) (by
      rw [map_sub, sub_eq_iff_eq_add']
      exact hst (σ z))
    have h1 : φ z = φ (s (σ z)) := by
      rw [sub_eq_iff_eq_add.1 hz', map_add, map_nsmul]
      simp [← sub_eq_iff_eq_add.1 hz']
    have h2 : σ (zz a₀) = a₀ - q • cc a₀ := eq_sub_iff_add_eq.2 (hzc a₀).symm
    rw [h1, ← hψ, ← ha₀, h2]
    simp
  · intro y hy
    have hd : ∀ a, (q : ℤ) ∣ EF (σ y) a := by
      intro a
      obtain ⟨z, b, rfl⟩ := hs a
      rw [map_add, map_nsmul, nsmul_eq_mul]
      exact dvd_add ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hy z)) (dvd_mul_right _ _)
    choose d hd using hd
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => d (B i)
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine hk y a₀ (hE.1 (B.ext fun i => ?_))
    rw [map_nsmul, ha₀, hd]
    simp [ψ]

theorem exists_levPairing {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (p : ℕ) [Fact p.Prime] (n : ℕ)
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) {N : ℕ} (u : Fin N → La)
    (hu : IsPolLattice c p EF u) :
    ∃ (π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n)
      (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n)),
      (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) ∧
      (∀ z z', e z z' = ((EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) ∧
      (∀ a : La, ∃ (z : Fin N → 𝓞 E) (b : La), a = ∑ k, z k • u k + (p ^ n) • b) ∧
      Function.Surjective π ∧
      (∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ n) • y') ∧
      (∀ y, e y y = 0) ∧
      (∀ (a : 𝓞 E) (y z : Fin N → 𝓞 E), e (a • y) z = e y (RingOfIntegers.mapRingEquiv c a • z)) ∧
      (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ n), ∃ y, e y = φ) ∧
      (∀ y, e y = 0 → ∃ y', y = (p ^ n) • y') := by
  have := hu.free
  have := hu.finite
  let σ₀ : (Fin N → 𝓞 E) →ₗ[𝓞 E] La := Fintype.linearCombination (𝓞 E) u
  let σ : (Fin N → 𝓞 E) →ₗ[ℤ] La := σ₀.toAddMonoidHom.toIntLinearMap
  have hσ : ∀ z, σ z = ∑ k, z k • u k := fun z => Fintype.linearCombination_apply _ _ _
  have hσa : ∀ (a : 𝓞 E) z, σ (a • z) = a • σ z := fun a z => map_smul σ₀ a z
  have hs : ∀ a, ∃ z b, a = σ z + (p ^ n) • b :=
    surj_mod_pow σ.toAddMonoidHom p (fun a => by
      obtain ⟨z, b, h⟩ := hu.span a
      exact ⟨z, b, h.trans (by rw [← hσ]; rfl)⟩) n
  have hrk : Module.finrank ℤ La = Module.finrank ℤ (Fin N → 𝓞 E) := by
    rw [hu.rank, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  let φ := LinearEquiv.ofFinrankEq La (Fin N → 𝓞 E) hrk
  have hk : ∀ z b, σ z = (p ^ n) • b → ∃ z', z = (p ^ n) • z' := fun z b h =>
    inj_mod_of_surj_mod (φ.toLinearMap ∘ₗ σ) (p ^ n) (fun a => by
      obtain ⟨z, b, h⟩ := hs (φ.symm a)
      refine ⟨z, φ b, ?_⟩
      have := congrArg φ h
      rwa [φ.apply_symm_apply, map_add, map_nsmul] at this) z (φ b) (by
      show φ (σ z) = _
      rw [h, map_nsmul])
  obtain ⟨hsu, hin⟩ := perfect_mod σ (p ^ n) EF hu.unimod hs hk
  let K : Submodule ℤ La := LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))
  let π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n :=
    AddMonoidHom.toMultiplicative (K.mkQ ∘ₗ σ).toAddMonoidHom
  have hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p n (σ z) := fun z => rfl
  let e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n) :=
    { toFun := fun y => (Int.castAddHom (ZMod (p ^ n))).comp (EF (σ y) ∘ₗ σ).toAddMonoidHom
      map_zero' := by ext z; simp
      map_add' := fun y y' => by ext z; simp }
  have he : ∀ y z, e y z = ((EF (σ y) (σ z) : ℤ) : ZMod (p ^ n)) := fun y z => rfl
  have hone : ∀ a : La, lev p n a = 1 ↔ ∃ b, a = (p ^ n) • b := fun a => by
    show (Submodule.Quotient.mk a : La ⧸ K) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  refine ⟨π, e, fun z => by rw [hπ, hσ], fun z z' => by rw [he, hσ, hσ], fun a => ?_, fun t => ?_, fun y => ?_,
    fun y => ?_, fun a y z => ?_, fun ψ => ?_, fun y hy => ?_⟩
  · simpa only [hσ] using hs a
  · obtain ⟨a, ha⟩ := K.mkQ_surjective (Multiplicative.toAdd t)
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have h0 : K.mkQ ((p ^ n) • b) = 0 := (hone _).2 ⟨b, rfl⟩
    rw [map_add, h0, add_zero] at ha
    exact ha
  · rw [hπ, hone]
    exact ⟨fun ⟨b, hb⟩ => hk y b hb, fun ⟨y', hy'⟩ => ⟨σ y', by rw [hy', map_nsmul]⟩⟩
  · rw [he, hu.alt, Int.cast_zero]
  · rw [he, he, hσa, hσa, hu.adj]
  · obtain ⟨y, hy⟩ := hsu ψ
    exact ⟨y, AddMonoidHom.ext hy⟩
  · exact hin y fun z => (he y z).symm.trans (by rw [hy]; rfl)

end PositivityTheory.HtPt.Htat
