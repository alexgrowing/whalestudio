import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Formalism.GaloisCohomology.Statement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.MuTowerInj

section Abstract

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {R₁ R₂ R₃ M₁ M₂ M₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
  [DiscreteTopology M₁] [DiscreteTopology M₂] [DiscreteTopology M₃]

def twoCocycleMapOfEquivariantAdd (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) : Z2 ρ₁ →+ Z2 ρ₂ where
  toFun f := ⟨u ∘ f.1, (continuous_of_discreteTopology (f := u)).comp f.2.1, fun g h k => by
    simp only [Function.comp_apply, ← hu, ← map_sub, ← map_add, f.2.2 g h k, map_zero]⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero u)
  map_add' f f' := Subtype.ext (funext fun _ => map_add u _ _)

def secondCohomologyMapOfEquivariantAdd (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) : H2 ρ₁ →+ H2 ρ₂ :=
  QuotientAddGroup.map ((B2 ρ₁).comap (Z2 ρ₁).subtype).toAddSubgroup
    ((B2 ρ₂).comap (Z2 ρ₂).subtype).toAddSubgroup (twoCocycleMapOfEquivariantAdd ρ₁ ρ₂ u hu) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ₁ _).1 hf
    refine (separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨u ∘ c, (continuous_of_discreteTopology (f := u)).comp hc, ?_⟩
    funext p
    have e := congrFun hcf p
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 p)
    rw [← e]
    simp [d1, hu]

theorem mapH2Add_mk (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) (z : Z2 ρ₁) :
    secondCohomologyMapOfEquivariantAdd ρ₁ ρ₂ u hu (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (twoCocycleMapOfEquivariantAdd ρ₁ ρ₂ u hu z) := rfl

theorem ker_le_range [ContinuousMul Γ] (ρ₁ : Representation R₁ Γ M₁)
    (ρ₂ : Representation R₂ Γ M₂) (ρ₃ : Representation R₃ Γ M₃) (h₂ : ContAction ρ₂)
    (u : M₁ →+ M₂) (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m))
    (p : M₂ →+ M₃) (hp : ∀ g m, p (ρ₂ g m) = ρ₃ g (p m))
    (hinj : Function.Injective u) (hsurj : Function.Surjective p)
    (hex : ∀ m, p m = 0 → ∃ k, u k = m) :
    (secondCohomologyMapOfEquivariantAdd ρ₂ ρ₃ p hp).ker ≤ (secondCohomologyMapOfEquivariantAdd ρ₁ ρ₂ u hu).range := by
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [AddMonoidHom.mem_ker, mapH2Add_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ₃ _).1 hx

  have hsc : Continuous (Function.surjInv hsurj ∘ c) :=
    (continuous_of_discreteTopology (f := Function.surjInv hsurj)).comp hc
  have hb : d1 ρ₂ (Function.surjInv hsurj ∘ c) ∈ Z2 ρ₂ :=
    coboundaries2_le_cocycles2 ρ₂ h₂ ((separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨_, hsc, rfl⟩)
  have hf' : f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c) ∈ Z2 ρ₂ := (Z2 ρ₂).sub_mem f.2 hb

  have hker : ∀ q, p ((f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) q) = 0 := by
    rintro ⟨g, h⟩
    have e : ρ₃ g (c h) - c (g * h) + c g = p (f.1 (g, h)) := by
      have e0 := congrFun hcf (g, h)
      rw [d1_apply] at e0
      exact e0
    rw [Pi.sub_apply, d1_apply, map_sub, map_add, map_sub, hp]
    simp only [Function.comp_apply, Function.surjInv_eq hsurj]
    rw [e, sub_self]
  obtain ⟨k, hk⟩ : ∃ k : Γ × Γ → M₁, ∀ q, u (k q) = (f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) q :=
    ⟨fun q => Function.invFun u _, fun q => Function.invFun_eq (hex _ (hker q))⟩
  have hkc : Continuous k := by
    have hk' : k = Function.invFun u ∘ (f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) := by
      funext q
      rw [Function.comp_apply, ← hk q, Function.leftInverse_invFun hinj]
    rw [hk']
    exact (continuous_of_discreteTopology (f := Function.invFun u)).comp ((mem_cocycles2 ρ₂ _).1 hf').1
  have hkZ : k ∈ Z2 ρ₁ := by
    refine (mem_cocycles2 ρ₁ k).2 ⟨hkc, fun g h t => hinj ?_⟩
    rw [map_zero, map_sub, map_add, map_sub, hu, hk, hk, hk, hk]
    exact ((mem_cocycles2 ρ₂ _).1 hf').2 g h t
  refine AddMonoidHom.mem_range.2 ⟨Submodule.Quotient.mk ⟨k, hkZ⟩, ?_⟩
  rw [mapH2Add_mk, Submodule.Quotient.eq, Submodule.mem_comap]
  refine (separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨-(Function.surjInv hsurj ∘ c), hsc.neg, ?_⟩
  funext q
  rw [map_neg, Pi.neg_apply]
  show _ = u (k q) - f.1 q
  rw [hk q, Pi.sub_apply]
  abel

theorem injective_of_card {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] [Finite B] [Finite C] (f : A →+ B) (g : B →+ C) (h : g.ker ≤ f.range)
    (hc : Nat.card B = Nat.card A * Nat.card C) : Function.Injective f := by
  have eA : Nat.card f.ker * Nat.card f.range = Nat.card A := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index _
  have eB : Nat.card g.ker * Nat.card g.range = Nat.card B := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index _
  have h1 : Nat.card g.ker ≤ Nat.card f.range := AddSubgroup.card_le_of_le h
  have h2 : Nat.card g.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hpos : 0 < Nat.card f.range * Nat.card C := Nat.mul_pos Nat.card_pos Nat.card_pos

  have hk : Nat.card f.ker ≤ 1 := by
    by_contra hne
    rw [not_le] at hne
    have hlt : Nat.card f.range * Nat.card C < Nat.card f.range * Nat.card C :=
      calc Nat.card f.range * Nat.card C
          < Nat.card f.ker * (Nat.card f.range * Nat.card C) := lt_mul_of_one_lt_left hpos hne
        _ = Nat.card A * Nat.card C := by rw [← eA, mul_assoc]
        _ = Nat.card B := hc.symm
        _ = Nat.card g.ker * Nat.card g.range := eB.symm
        _ ≤ Nat.card f.range * Nat.card C := Nat.mul_le_mul h1 h2
    exact lt_irrefl _ hlt
  rw [AddSubgroup.card_le_one_iff_eq_bot] at hk
  exact (AddMonoidHom.ker_eq_bot_iff f).1 hk

end Abstract

section Cyclic

variable (l : ℕ) [Fact l.Prime] (n : ℕ)

omit [Fact l.Prime] in
theorem pow_mul_val (x : ℕ) :
    ((l ^ n * (x : ZMod (l ^ 1)).val : ℕ) : ZMod (l ^ (n + 1))) = ((l ^ n * x : ℕ) : _) := by
  rw [ZMod.val_natCast, pow_one]
  conv_rhs => rw [← Nat.mod_add_div x l]
  rw [mul_add, Nat.cast_add, ← mul_assoc, ← pow_succ, Nat.cast_mul (l ^ (n + 1)), ZMod.natCast_self,
    zero_mul, add_zero]

def iota : ZMod (l ^ 1) →+ ZMod (l ^ (n + 1)) :=
  AddMonoidHom.mk' (fun b => ((l ^ n * b.val : ℕ) : ZMod (l ^ (n + 1)))) fun a b => by
    obtain ⟨x, rfl⟩ := ZMod.natCast_zmod_surjective a
    obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective b
    rw [← Nat.cast_add, pow_mul_val, pow_mul_val, pow_mul_val, mul_add, Nat.cast_add]

theorem iota_apply (b : ZMod (l ^ 1)) :
    iota l n b = ((l ^ n * b.val : ℕ) : ZMod (l ^ (n + 1))) := rfl

theorem iota_natCast (x : ℕ) : iota l n x = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by
  rw [iota_apply, pow_mul_val]

theorem iota_injective : Function.Injective (iota l n) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  rw [iota_apply, CharP.cast_eq_zero_iff (ZMod (l ^ (n + 1))) (l ^ (n + 1)), pow_succ,
    Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : l.Prime).pos n)] at hb
  have hlt : b.val < l := by simpa using ZMod.val_lt b
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hb hlt

theorem iota_mul (u : ℤ_[l]) (b : ZMod (l ^ 1)) :
    iota l n (PadicInt.toZModPow 1 u * b) = PadicInt.toZModPow (n + 1) u * iota l n b := by
  obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective b
  set w := PadicInt.toZModPow (n + 1) u with hw

  have h1 : PadicInt.toZModPow 1 u = ((w.val : ℕ) : ZMod (l ^ 1)) := by
    rw [← PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), RingHom.comp_apply,
      ZMod.castHom_apply, ZMod.cast_eq_val]
  have h2 : ((w.val : ℕ) : ZMod (l ^ (n + 1))) = w := ZMod.natCast_zmod_val w
  rw [h1, ← Nat.cast_mul, iota_natCast, iota_natCast]
  conv_rhs => rw [← h2]
  push_cast
  ring

def red : ZMod (l ^ (n + 1)) →+* ZMod (l ^ n) :=
  ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))

theorem red_toZModPow (u : ℤ_[l]) :
    red l n (PadicInt.toZModPow (n + 1) u) = PadicInt.toZModPow n u := by
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) u

omit [Fact l.Prime] in
theorem red_surjective : Function.Surjective (red l n) := by
  exact ZMod.ringHom_surjective (red l n)

theorem exists_iota_of_red (m : ZMod (l ^ (n + 1))) (hm : red l n m = 0) :
    ∃ k, iota l n k = m := by
  have h0 : ((m.val : ℕ) : ZMod (l ^ n)) = 0 := by
    rw [← ZMod.cast_eq_val]
    exact hm
  rw [CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n)] at h0
  obtain ⟨t, ht⟩ := h0
  exact ⟨t, by rw [iota_natCast, ← ht, ZMod.natCast_zmod_val]⟩

end Cyclic

theorem card_H2_muLoc (hD : LocalTateDuality) (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hA : IsPlaceOver A v) (r : ℕ) :
    Nat.card (H2 (muLoc F l r A)) = l ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  ·
    have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    have : Subsingleton (H2 (muLoc F l 0 A)) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (Subtype.ext (funext fun _ => Subsingleton.elim _ _))⟩
    exact (Nat.card_of_subsingleton (0 : H2 (muLoc F l 0 A))).trans (pow_zero l).symm
  · obtain ⟨⟨e⟩, -⟩ := hD F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
      (GlobalTheory.TameQuot.contAction_muDec A l r)
    exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)

theorem mk_eq_zero_of_coboundary : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (n : ℕ) (w : Z2 (muLoc F l 1 A)) (a : Dec (F := F) A → ZMod (l ^ (n + 1))), Continuous a → (∀ g h : Dec (F := F) A, ((cycMod F Ω l (n + 1) g : (ZMod (l ^ (n + 1)))ˣ) : ZMod (l ^ (n + 1))) * a h - a (g * h) + a g = ((l ^ n * (w.1 (g, h)).val : ℕ) : ZMod (l ^ (n + 1)))) → (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  intro hD F Ω _ _ _ _ _ l _ A v hA n w a ha hrel

  have hu : ∀ (g : Dec (F := F) A) (m : ZMod (l ^ 1)),
      iota l n (muLoc F l 1 A g m) = muLoc F l (n + 1) A g (iota l n m) := fun g m =>
    iota_mul l n ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) m
  have hp : ∀ (g : Dec (F := F) A) (m : ZMod (l ^ (n + 1))),
      (red l n).toAddMonoidHom (muLoc F l (n + 1) A g m) =
        muLoc F l n A g ((red l n).toAddMonoidHom m) := by
    intro g m
    show red l n (PadicInt.toZModPow (n + 1) ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) * m) =
      PadicInt.toZModPow n ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) * red l n m
    rw [map_mul, red_toZModPow]
  have hcard : ∀ r, Nat.card (H2 (muLoc F l r A)) = l ^ r := card_H2_muLoc hD F Ω l A v hA
  have : ∀ r, Finite (H2 (muLoc F l r A)) := fun r =>
    Nat.finite_of_card_ne_zero (by rw [hcard r]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

  have hinj := injective_of_card
    (secondCohomologyMapOfEquivariantAdd (muLoc F l 1 A) (muLoc F l (n + 1) A) (iota l n) hu)
    (secondCohomologyMapOfEquivariantAdd (muLoc F l (n + 1) A) (muLoc F l n A) (red l n).toAddMonoidHom hp)
    (ker_le_range _ _ _ (GlobalTheory.TameQuot.contAction_muDec A l (n + 1)) _ hu _ hp
      (iota_injective l n) (red_surjective l n) (exists_iota_of_red l n))
    (by rw [hcard, hcard, hcard]; ring)
  apply hinj
  rw [map_zero, mapH2Add_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨a, ha, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply]
  exact (hrel g h).trans (iota_apply l n _).symm

end GlobalTheory.MuTowerInj
