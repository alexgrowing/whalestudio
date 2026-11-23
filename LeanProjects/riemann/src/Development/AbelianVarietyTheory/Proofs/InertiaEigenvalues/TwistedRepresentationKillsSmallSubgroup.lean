import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.SmallActs

theorem toZModPow_cycZ_eq_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (n : ℕ) (σ : G F Ω) (hσ : ∀ ζ : Ω, ζ ^ (l ^ n) = 1 → σ ζ = ζ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec : σ ζ = ζ ^ (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one
  rw [hσ ζ hζ.pow_eq_one] at hspec
  set m := (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val with hm
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ 1 := Units.ext (by simpa using hspec.symm)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])), ← hm,
    (ZMod.natCast_eq_natCast_iff _ _ _).2 heq', Nat.cast_one]

theorem map_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (T : Matrix (Fin r) (Fin r) O)
    (h : ∀ a b, algebraMap O A ((T - 1) a b) = 0) : T.map (algebraMap O A) = 1 := by
  ext a b
  have := h a b
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem repOn_of_map_eq_one {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ) (Y : Type) [AddCommGroup Y] [Module A Y] (g : Γ)
    (h : (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A) = 1) (m : Fin r → Y) :
    repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m := by
  change (((κ g : Aˣ) : A) • matAct ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A))) m = _
  rw [h, matAct_one]
  rfl

theorem small_acts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y], ∀ g ∈ L, (∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m) ∧ (∀ m, repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m) ∧ cycMod D.host.E N.Om (X.l i) (nu X i + 1) g = 1 := by
  intro D N X i s _ M L z hM hS A _ _ κ ρ hK hρ Y _ _ g hg
  have hT : ∀ g ∈ L, (Tmat i s g).map (algebraMap (X.O0 i) A) = 1 := fun g hg =>
    map_eq_one _ fun a b => hK _ (hS.2.2 g hg a b)
  have hc : PadicInt.toZModPow (nu X i + 1) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = 1 := by
    refine toZModPow_cycZ_eq_one (nu X i + 1) g fun ζ hζ => hS.2.1 g hg ζ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hM
    have e : 2 * X.l i ^ M = X.l i ^ (nu X i + 1) * (2 * X.l i ^ k) := by rw [hk, pow_add (X.l i) (nu X i + 1) k]; ring
    rw [e, pow_mul, hζ, one_pow]
  refine ⟨repOn_of_map_eq_one _ κ Y g (by rw [Tgl_coe]; exact hT g hg), repOn_of_map_eq_one _ κ Y g ?_, Units.ext hc⟩
  have hmem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
    intro h
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
    have h1 : ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) - 1 ∈
        RingHom.ker (PadicInt.toZModPow (nu X i + 1) : ℤ_[X.l i] →+* ZMod (X.l i ^ (nu X i + 1))) := by
      rw [RingHom.mem_ker, map_sub, hc, map_one, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    obtain ⟨c, h1⟩ := h1
    change algebraMap (X.O0 i) A (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ)) = 1
    have h2 : algebraMap (X.O0 i) A ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i)) = 0 :=
      hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hmem)
    rw [sub_eq_iff_eq_add.1 h1, map_add, map_add, map_one, map_one, map_mul, map_pow, map_natCast, pow_succ, map_mul, h2,
      zero_mul, zero_add]
  have hinv : (Tmat i s g)⁻¹ = Tmat i s g⁻¹ := by
    rw [← Tgl_coe, ← Tgl_coe, map_inv, Matrix.coe_units_inv]
  rw [hρ g, Tdual, hinv]
  ext a b
  have := congrFun (congrFun (hT g⁻¹ (L.inv_mem hg)) b) a
  rw [Matrix.map_apply] at this
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, he, one_mul, Matrix.transpose_apply, this,
    Matrix.one_apply, Matrix.one_apply]
  simp only [eq_comm]

end GlobalTheory.NewPrime.SmallActs

end
