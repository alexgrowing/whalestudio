import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UlZero

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

section SlopeTestRemainingChoices

variable {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N]

private theorem ul_top (I : Subgroup D) (φ : D) (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (S : Subgroup D) (hS : IsClosed (S : Set D)) (hI : I ≤ S) (hφ : φ ∈ S) (s : D) : s ∈ S := by
  have := Subgroup.topologicalClosure_minimal _ (sup_le hI ((Subgroup.zpowers_le).2 hφ)) hS
  rw [h] at this
  exact this (Subgroup.mem_top s)

private theorem ul_lc (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) : IsLocallyConstant ρ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' ρ.ker, ho.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have h : ρ (g⁻¹ * x) = 1 := hx
  calc ρ x = ρ (g * (g⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = ρ g := by rw [map_mul, h, mul_one]

omit [TopologicalSpace D] [IsTopologicalGroup D] in
private theorem ul_mul (ρ : Representation ℤ D N) (s t : D) (y : N) : ρ (s * t) y = ρ s (ρ t y) := by
  rw [map_mul]; rfl

private theorem ul_zero (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) (z : D → N) (hz : z ∈ Zc ρ) (hI : ∀ s ∈ I, z s = 0)
    (hφ : z φ = 0) (s : D) : z s = 0 :=
  _root_.UpperTheory.Reformulated.B.Rb1.ul_zero ρ I φ h z hz hI hφ s

private theorem ul_ex [Finite N] (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) (I : Subgroup D) [hn : I.Normal] (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (x : N) (hx : ∀ s ∈ I, ρ s x = x) : ∃ z ∈ Zc ρ, (∀ s ∈ I, z s = 0) ∧ z φ = x := by
  have inv1 : ∀ s y, ρ s (ρ s⁻¹ y) = y := fun s y => by rw [← ul_mul, mul_inv_cancel, map_one]; rfl
  have inv2 : ∀ s y, ρ s⁻¹ (ρ s y) = y := fun s y => by rw [← ul_mul, inv_mul_cancel, map_one]; rfl
  have stab : ∀ s y, (∀ j ∈ I, ρ j y = y) → ∀ j ∈ I, ρ j (ρ s y) = ρ s y := fun s y hy j hj => by
    have h1 := hy _ (hn.conj_mem j hj s⁻¹)
    rw [inv_inv, ul_mul, ul_mul] at h1
    have h2 := congrArg (ρ s) h1
    rwa [inv1] at h2
  let T : Equiv.Perm N :=
    { toFun := fun y => x + ρ φ y
      invFun := fun y => ρ φ⁻¹ (y - x)
      left_inv := fun y => by simp only [add_sub_cancel_left, inv2]
      right_inv := fun y => by simp only [inv1, add_sub_cancel] }
  have hg : ∀ u : Subgroup.zpowers T, u ∈ Subgroup.zpowers (⟨T, Subgroup.mem_zpowers T⟩ : Subgroup.zpowers T) := by
    rintro ⟨_, k, rfl⟩
    exact ⟨k, rfl⟩
  obtain ⟨d, hd1, hd2, hd3⟩ := hd (Nat.card (Subgroup.zpowers T)) Nat.card_pos
  obtain ⟨τ, t1, t2, t3⟩ : ∃ τ : D →* Equiv.Perm N, IsLocallyConstant τ ∧ (∀ s ∈ I, τ s = 1) ∧ τ φ = T := by
    let e := (Subgroup.zpowers T).subtype.comp (zmodMulEquivOfGenerator hg rfl).toMonoidHom
    refine ⟨e.comp d, hd1.comp e, fun s hs => ?_, ?_⟩
    · rw [MonoidHom.comp_apply, hd2 s hs, map_one]
    · rw [MonoidHom.comp_apply, hd3]
      exact congrArg Subtype.val (zmodMulEquivOfGenerator_apply_ofAdd_one hg rfl)
  let S : Subgroup D :=
    { carrier := {s | ∃ a, (∀ j ∈ I, ρ j a = a) ∧ ∀ y, (∀ j ∈ I, ρ j y = y) → τ s y = a + ρ s y}
      one_mem' := ⟨0, fun j _ => map_zero _, fun y _ => by simp⟩
      mul_mem' := fun {s t} ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ =>
        ⟨a + ρ s b, fun j hj => by rw [map_add, ha j hj, stab s b hb j hj], fun y hy => by
          rw [map_mul, Equiv.Perm.mul_apply, hb' y hy,
            ha' _ (fun j hj => by rw [map_add, hb j hj, stab t y hy j hj]), map_add, ul_mul, add_assoc]⟩
      inv_mem' := fun {s} ⟨a, ha, ha'⟩ =>
        ⟨-ρ s⁻¹ a, fun j hj => by rw [map_neg, stab _ a ha j hj], fun y hy => by
          rw [map_inv, Equiv.Perm.inv_eq_iff_eq,
            ha' _ (fun j hj => by rw [map_add, map_neg, stab _ a ha j hj, stab _ y hy j hj]),
            map_add, map_neg, inv1, inv1, add_neg_cancel_left]⟩ }
  have hS : ∀ s, s ∈ S := by
    refine ul_top I φ h S ?_ (fun s hs => ⟨0, fun j _ => map_zero _, fun y hy => ?_⟩) ⟨x, hx, fun y _ => ?_⟩
    · exact isOpen_compl_iff.1 (t1.prodMk (ul_lc ρ ho)
        {p | ∃ a, (∀ j ∈ I, ρ j a = a) ∧ ∀ y, (∀ j ∈ I, ρ j y = y) → p.1 y = a + p.2 y}ᶜ)
    · rw [t2 s hs, hy s hs, zero_add]; rfl
    · rw [t3]; rfl
  refine ⟨fun s => τ s 0, ⟨t1.comp fun p => p 0, fun s t => ?_⟩, fun s hs => ?_, ?_⟩
  · obtain ⟨a, -, ha'⟩ := hS s
    obtain ⟨b, hb, hb'⟩ := hS t
    have h0 : ∀ j ∈ I, ρ j 0 = 0 := fun j _ => map_zero _
    show τ (s * t) 0 = τ s 0 + ρ s (τ t 0)
    rw [map_mul, Equiv.Perm.mul_apply, hb' 0 h0, map_zero, add_zero, ha' b hb, ha' 0 h0, map_zero, add_zero]
  · show τ s 0 = 0
    rw [t2 s hs]; rfl
  · show τ φ 0 = x
    rw [t3]
    show x + ρ φ 0 = x
    rw [map_zero, add_zero]

private theorem ul_abs [Finite N] (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) (I : Subgroup D) [I.Normal] (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) :
    ∃ Z : AddSubgroup (D → N), Finite Z ∧ (Z : Set _) ⊆ Zc ρ ∧ (∀ Y : N, (fun s => ρ s Y - Y) ∈ Z) ∧
      (∀ z ∈ Z, ∃ Y : N, ∀ s ∈ I, z s = ρ s Y - Y) ∧ Nat.card N ≤ Nat.card Z := by
  have hsub : ∀ {a b : D → N}, a ∈ Zc ρ → b ∈ Zc ρ → a - b ∈ Zc ρ := fun {a b} ha hb =>
    ⟨ha.1.sub hb.1, fun s t => by
      simp only [Pi.sub_apply, ha.2 s t, hb.2 s t, map_sub]; abel⟩
  have h0 : (0 : D → N) ∈ Zc ρ := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  let Z : AddSubgroup (D → N) := AddSubgroup.ofSub {z | z ∈ Zc ρ ∧ ∃ Y : N, ∀ s ∈ I, z s = ρ s Y - Y}
    ⟨0, h0, 0, fun s _ => by simp⟩
    (fun a ⟨ha, Y, hY⟩ b ⟨hb, Y', hY'⟩ => by
      rw [← sub_eq_add_neg]
      refine ⟨hsub ha hb, Y - Y', fun s hs => ?_⟩
      rw [Pi.sub_apply, hY s hs, hY' s hs, map_sub]; abel)
  have hcob : ∀ Y : N, (fun s => ρ s Y - Y) ∈ Z := fun Y =>
    ⟨⟨(ul_lc ρ ho).comp fun p => p Y - Y, fun s t => by
      simp only [ul_mul, map_sub]; abel⟩, Y, fun _ _ => rfl⟩
  have hfin : Finite Z := by
    refine Finite.of_injective (fun z : Z => (z.2.2.choose, z.1 φ)) fun a b hab => Subtype.ext ?_
    obtain ⟨e1, e2⟩ := Prod.ext_iff.1 hab
    refine sub_eq_zero.1 (funext (ul_zero ρ I φ h _ (hsub a.2.1 b.2.1) (fun s hs => ?_) (sub_eq_zero.2 e2)))
    have e1' : a.2.2.choose = b.2.2.choose := e1
    rw [Pi.sub_apply, a.2.2.choose_spec s hs, b.2.2.choose_spec s hs, e1', sub_self]
  refine ⟨Z, hfin, fun z hz => hz.1, hcob, fun z hz => hz.2, ?_⟩
  let r : Z →+ (I → N) := AddMonoidHom.mk' (fun z s => z.1 s.1) fun _ _ => rfl
  let π : N →+ (I → N) := AddMonoidHom.mk' (fun Y s => ρ s.1 Y - Y) fun a b => funext fun s => by
    simp only [map_add, Pi.add_apply]; abel
  have hr : r.range = π.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨Y, hY⟩ := z.2.2
      exact ⟨Y, funext fun s => (hY s.1 s.2).symm⟩
    · rintro _ ⟨Y, rfl⟩
      exact ⟨⟨_, hcob Y⟩, rfl⟩
  have hk : Nat.card π.ker ≤ Nat.card r.ker := by
    have hex : ∀ x : π.ker, ∃ z : r.ker, z.1.1 φ = x.1 := fun x => by
      obtain ⟨z, z1, z2, z3⟩ := ul_ex ρ ho I φ h hd x.1 fun s hs => sub_eq_zero.1 (congrFun x.2 ⟨s, hs⟩)
      exact ⟨⟨⟨z, z1, 0, fun s hs => by rw [z2 s hs]; simp⟩, funext fun s => z2 s.1 s.2⟩, z3⟩
    choose f hf using hex
    exact Nat.card_le_card_of_injective f fun a b hab => Subtype.ext (by rw [← hf a, ← hf b, hab])
  rw [← π.ker.card_mul_index, ← r.ker.card_mul_index, AddSubgroup.index_ker, AddSubgroup.index_ker, hr]
  exact Nat.mul_le_mul_right _ hk

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.J.unrLow :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), IsPlaceOver A v → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ (Dec (F := F) A) N), IsOpen (ρ.ker : Set (Dec (F := F) A)) → ∃ Z : AddSubgroup (Dec (F := F) A → N), Finite Z ∧ (Z : Set _) ⊆ Zc ρ ∧ (∀ Y : N, (fun s => ρ s Y - Y) ∈ Z) ∧ (∀ z ∈ Z, ∃ Y : N, ∀ s : Dec (F := F) A, s.1 ∈ Ine (F := F) A → z s = ρ s Y - Y) ∧ Nat.card N ≤ Nat.card Z := by
  intro F Ω _ _ _ _ _ A v hA N _ _ ρ ho
  obtain ⟨φ, -, h1, h2⟩ := GC.decZhat F Ω v A hA
  haveI : ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).Normal := ⟨fun n hn g => conj_mem_Ine g.2 hn⟩
  exact ul_abs ρ ho _ φ h1 h2
