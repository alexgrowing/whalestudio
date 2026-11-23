import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]

private theorem kx_cls (n : ℕ) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1) : Chr.cls ℚ Ω (l ^ n) s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  refine (Chr.clsFacts ℚ Ω (l ^ n)).2.2.1 s _ fun ζ hζ => ?_
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) ζ hζ
  have h2 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) = 1 := h
  rw [h2, Units.val_one, map_one] at h1
  exact h1

variable {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N]

private theorem kx_kapL (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1) :
    kapL l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := by
  haveI : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  have h3 : proj l N (Chr.cls ℚ Ω N s) = 1 := by
    rw [← MonoidHom.mem_ker, (projFacts N l hl.out).2.2.2.2.2.2.1, MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      (Chr.clsFacts ℚ Ω N).2.1]
    exact kx_cls _ h
  have h4 : (kapL l ψ).toUnitHom (Chr.cls ℚ Ω N s) = 1 := by rw [kapL, (compAlg O N l hl.out).1, h3, map_one]
  exact congrArg Units.val h4

private theorem kx_pow (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1)
    (hk : Chr.dirG ℚ Ω (kapB l ψ) s = 1) : Chr.dirG ℚ Ω ψ s ^ orderOf (th0 l ψ) = 1 := by
  ext1
  show ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  have a1 : kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hk
  have a3 : ψ = th0 l ψ * (kapB l ψ * kapL l ψ) := by rw [kapB, inv_mul_cancel_right, dirichletPrimeToLPart_mul_lPowerPart]
  have a4 : ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = th0 l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) := by
    conv_lhs => rw [a3]
    rw [MulChar.mul_apply, MulChar.mul_apply, a1, kx_kapL ψ h, one_mul, mul_one]
  rw [a4, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]

private theorem kx_unr (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1)
    (hψ : Chr.dirG ℚ Ω ψ s = 1) : Chr.dirG ℚ Ω (kapB l ψ) s = 1 := by
  ext1
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1
  have a1 : ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hψ
  have a2 : kap l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [kap, lPart, MulChar.pow_apply_coe, a1, one_pow]
  have a3 : kap l ψ = kapB l ψ * kapL l ψ := by rw [kapB, inv_mul_cancel_right]
  rwa [a3, MulChar.mul_apply, kx_kapL ψ h, mul_one] at a2

private theorem kx_ord (ψ : DirichletCharacter O N) :
    Chr.dirG ℚ Ω (kapB l ψ) ^ l ^ (orderOf ψ).factorization l = 1 := by
  have h1 : kap l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [← (partOrd _ l hl.out ψ ψ.orderOf_pos).1]
    exact pow_orderOf_eq_one _
  obtain ⟨-, -, hone, -, hpow, -⟩ := compAlg O N l hl.out
  have h2 : kapB l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [kapB, kapL, mul_pow, inv_pow, ← hpow, h1, hone, inv_one, one_mul]
  refine MonoidHom.ext fun s => Units.ext ?_
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  rw [← MulChar.pow_apply_coe, h2, MulChar.one_apply_coe]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.kapEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N), D.ψ = Chr.dirG ℚ Ω ψ → ∃ κ, Kap D κ := by
  intro Ω _ _ _ l hl c D hD N _ ψ hψ
  have hnd : ¬ l ∣ orderOf (th0 l ψ) := (partOrd _ l hl.out ψ ψ.orderOf_pos).2.2.1
  refine ⟨Chr.dirG ℚ Ω (kapB l ψ), ?_, ⟨_, kx_ord ψ⟩, fun A hA g hg => ?_, fun A hA => ?_, fun A hA g hg hb hk => ?_,
    orderOf (th0 l ψ), (Nat.Prime.coprime_iff_not_dvd hl.out).2 hnd, fun g hg hk => hψ ▸ kx_pow ψ hg hk⟩
  · refine Subgroup.isOpen_mono (fun s hs => ?_) (Chr.clsFacts ℚ Ω N).1
    rw [MonoidHom.mem_ker] at hs ⊢
    rw [Chr.dirG, MonoidHom.comp_apply, hs, map_one]
  · exact kx_unr ψ ((places ℚ Ω l A).2.2.2 (hA l hD.l_mem) hg) (hψ ▸ hD.psi_unr A hA hg)
  · refine ((compIne Ω N l hl.out A hA).2 c.O _).2.2 ?_
    obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O N l hl.out
    rw [kapB, kapL, hmul, hinv, (h6 _).1, mul_inv_cancel]
  · have h1 : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 (hA l (Finset.mem_singleton_self l)) hg
    have h2 : chiO ℚ Ω l c.O g = 1 := by rw [chiO, MonoidHom.comp_apply, h1, map_one]
    have h3 : D.Psi g = D.ψ g := by
      rw [Raw.Psi, Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, h2, one_pow, one_mul]
    refine (congrFacts Ω l c).2.2.2.1 _ 1 _ hnd (hψ ▸ kx_pow ψ h1 hk) (one_pow _) ?_
    rw [← residue_eq_zero_iff, map_sub, Units.val_one, map_one, sub_eq_zero, ← h3]
    exact hb
