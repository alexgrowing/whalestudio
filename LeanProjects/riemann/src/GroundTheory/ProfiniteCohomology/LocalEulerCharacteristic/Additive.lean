import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveSnake
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u v

open Representation

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem toFun_prod {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y] (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) :
    d.toFun (X × Y) (ρ.prod σ) = d.toFun X ρ + d.toFun Y σ :=
  d.additive ρ _ σ (LinearMap.inl _ X Y) (LinearMap.snd _ X Y)
    ⟨fun _ _ => by ext <;> simp⟩ ⟨fun _ _ => rfl⟩ LinearMap.inl_injective
    Function.Exact.inl_snd LinearMap.snd_surjective

theorem toFun_pi {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    (ρ : Representation (ZMod l) Γ X) (n : ℕ) :
    d.toFun (Fin n → X) (piRep (Fin n) ρ) = n * d.toFun X ρ := by
  induction n with
  | zero => simp [d.toFun_eq_zero_of_subsingleton (X := Fin 0 → X)]
  | succ n ih =>
    rw [← d.toFun_congr (ρ.prod (piRep (Fin n) ρ)) (piRep (Fin (n + 1)) ρ)
      (Fin.consLinearEquiv (ZMod l) (fun _ => X)) ?_, d.toFun_prod, ih]
    · push_cast
      ring
    · intro γ x
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem g_eq_of_torsion_trivial (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    [Finite (ModN A l)] (hA : ∀ a : A, l • a = 0 → a = 0) :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) := by
  have : Subsingleton (TorsN A l) := ⟨fun x y => Subtype.ext (by
    rw [hA x ((mem_ker_lsmul_iff l (x : A)).1 x.2), hA y ((mem_ker_lsmul_iff l (y : A)).1 y.2)])⟩
  rw [d.g_eq A, d.toFun_eq_zero_of_subsingleton (X := TorsN A l), sub_zero]

theorem g_eq_zero_of_nsmul_eq_zero (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (hA : ∀ a : A, l • a = 0) : d.g A = 0 := by
  by_cases hfin : Finite (ModN A l) ∧ Finite (TorsN A l)
  · obtain ⟨_, _⟩ := hfin
    rw [d.g_eq A, sub_eq_zero]
    let φ : A →ₗ[ℤ] TorsN A l :=
      LinearMap.codRestrict _ LinearMap.id (fun a => (mem_ker_lsmul_iff l a).2 (hA a))
    let ψ := (LinearMap.range (LinearMap.lsmul ℤ A (l : ℤ))).liftQ φ (by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      exact Subtype.ext (by simpa [φ] using hA y))
    refine d.toFun_congr _ _ (LinearEquiv.ofBijective (ψ.toAddMonoidHom.toZModLinearMap l)
      ⟨fun x y hxy => ?_, fun t => ⟨Submodule.Quotient.mk (t : A), Subtype.ext rfl⟩⟩) ?_
    · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (congrArg Subtype.val hxy : (a : A) = b)
    · intro γ x
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
  · exact d.g_of_not_finite A hfin

theorem g_eq_zero_of_finite (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite A] :
    d.g A = 0 := by
  suffices H : ∀ (N : ℕ) (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite A],
      Nat.card A = N → d.g A = 0 from H _ A rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ _ _ hN
  by_cases hA : ∀ a : A, l • a = 0 → a = 0
  · have hs : Function.Surjective (fun a : A => l • a) :=
      Finite.injective_iff_surjective.1 (fun a b hab =>
        sub_eq_zero.1 (hA (a - b) (by rw [smul_sub, sub_eq_zero]; exact hab)))
    have : Subsingleton (ModN A l) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      rw [(modN_mk_eq_zero_iff l _).2 ⟨a', rfl⟩, (modN_mk_eq_zero_iff l _).2 ⟨b', rfl⟩]⟩
    rw [d.g_eq_of_torsion_trivial A hA, d.toFun_eq_zero_of_subsingleton (X := ModN A l)]
  · push Not at hA
    obtain ⟨a₀, ha₀, hne⟩ := hA
    let m : A →+ A := (LinearMap.lsmul ℤ A (l : ℤ)).toAddMonoidHom
    have hm : ∀ a, m a = l • a := fun a => by simp [m]
    have hK : ∀ (γ : Γ) (a : A), a ∈ m.ker → γ • a ∈ m.ker := fun γ a ha => by
      rw [AddMonoidHom.mem_ker, hm] at ha ⊢
      rw [← smul_comm γ l a, ha, smul_zero]
    have hH : ∀ (γ : Γ) (a : A), a ∈ m.range → γ • a ∈ m.range := by
      rintro γ _ ⟨b, rfl⟩
      exact ⟨γ • b, by rw [hm, hm, smul_comm]⟩
    let _ := subgroupDistribMulAction m.ker hK
    let _ := subgroupDistribMulAction m.range hH
    have hKl : ∀ x : m.ker, l • x = 0 := fun x =>
      Subtype.ext (by rw [AddSubgroup.coe_nsmul, ← hm]; exact x.2)
    have hcard : Nat.card m.range < N := by
      have h₁ : Nat.card A = Nat.card m.range * Nat.card m.ker := by
        rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.ker,
          Nat.card_congr (QuotientAddGroup.quotientKerEquivRange m).toEquiv]
      have h₂ : 1 < Nat.card m.ker := by
        have : Nontrivial m.ker :=
          ⟨⟨⟨a₀, by rw [AddMonoidHom.mem_ker, hm, ha₀]⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
        exact Finite.one_lt_card
      have h₃ : 0 < Nat.card m.range := Nat.card_pos
      rw [← hN, h₁]
      nlinarith
    have e := d.g_add m.ker.subtype m.rangeRestrict (fun _ _ => rfl)
      (fun γ a => Subtype.ext (show m (γ • a) = γ • m a by rw [hm, hm, smul_comm]))
      (AddSubgroup.subtype_injective _)
      (fun y => ⟨fun hy => ⟨⟨y, congrArg Subtype.val hy⟩, rfl⟩,
        by rintro ⟨x, rfl⟩; exact Subtype.ext (AddMonoidHom.mem_ker.1 x.2)⟩)
      m.rangeRestrict_surjective
    rw [e, d.g_eq_zero_of_nsmul_eq_zero _ hKl, ih _ hcard _ rfl, add_zero]

theorem g_eq_of_finite_cokernel {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN B l)] [Finite (TorsN B l)] : d.g A = d.g B := by
  have hR : ∀ (γ : Γ) (a : A), a ∈ f.range → γ • a ∈ f.range := by
    rintro γ _ ⟨b, rfl⟩
    exact ⟨γ • b, hfγ γ b⟩
  let _ := quotientDistribMulAction f.range hR
  rw [d.g_add f (QuotientAddGroup.mk' f.range) hfγ (fun _ _ => rfl) hf
    (fun y => by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl)
    (QuotientAddGroup.mk'_surjective _), d.g_eq_zero_of_finite (A ⧸ f.range), add_zero]

theorem g_eq_of_finite_cokernel' {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (f : B →+ A)
    (hfγ : ∀ (γ : Γ) (b : B), f (γ • b) = γ • f b) (hf : Function.Injective f)
    [Finite (A ⧸ f.range)] [Finite (ModN A l)] [Finite (TorsN A l)] : d.g A = d.g B := by
  have hfh : Function.Exact f (QuotientAddGroup.mk' f.range) :=
    fun y => by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  have hh := QuotientAddGroup.mk'_surjective f.range
  have := finite_torsN_of_injective (n := l) hf
  have : Finite (ModN B l) :=
    finite_of_exact (connecting hh hfh hf).toAddMonoidHom (modNMap l f).toAddMonoidHom
      (exact_connecting_modNMap hh hfh hf)
  exact d.g_eq_of_finite_cokernel f hfγ hf

theorem g_of_trivial_int [NeZero l] (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (htriv : ∀ (γ : Γ) (a : A), γ • a = a) (e : A ≃+ ℤ) : d.g A = d.one := by
  have hA : ∀ a : A, l • a = 0 → a = 0 := fun a ha => by
    have h := congrArg e ha
    rw [map_nsmul, map_zero, nsmul_eq_mul] at h
    have h' := (mul_eq_zero.1 h).resolve_left (by exact_mod_cast NeZero.ne l)
    exact e.injective (by rw [h', map_zero])
  let b : Module.Basis Unit ℤ A := (Module.Basis.singleton Unit ℤ).map e.symm.toIntLinearEquiv
  let E : ModN A l ≃ₗ[ZMod l] ULift.{u} (ZMod l) := (ModN.basis b).equivFun.trans
    ((LinearEquiv.funUnique Unit (ZMod l) (ZMod l)).trans ULift.moduleEquiv.symm)
  have : Finite (ModN A l) := Finite.of_equiv _ E.symm.toEquiv
  rw [d.g_eq_of_torsion_trivial A hA]
  refine d.toFun_congr _ _ E (fun γ x => ?_)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk, htriv]
  rfl

end AdditiveFunction

end GroundTheory.ProfCoh
