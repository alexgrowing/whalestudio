import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private def ZcA {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    AddSubgroup (D → N) where
  carrier := Zc ρ
  zero_mem' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
    simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add]; abel⟩
  neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
    simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩

private theorem card_ZcA {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    Nat.card (ZcA ρ) = (Zc ρ).ncard := Nat.card_coe_set_eq (Zc ρ)

private theorem idx_mul {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    f.range.index * Nat.card A = Nat.card B * Nat.card f.ker := by
  rw [← AddSubgroup.index_mul_card f.range, ← AddSubgroup.index_mul_card f.ker, AddSubgroup.index_ker]
  ring

private def ZcQ {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N)
    (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) : ZcA ρ →+ ZcA (ρ.quotient N' h) where
  toFun z := ⟨fun s => N'.mkQ (z.1 s), z.2.1.comp N'.mkQ, fun s t => by
    show N'.mkQ (z.1 (s * t)) = N'.mkQ (z.1 s + ρ s (z.1 t))
    rw [z.2.2 s t]⟩
  map_zero' := by ext s; rfl
  map_add' a b := by ext s; rfl

private theorem ker_le {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N)
    (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) (hf : (Zc (ρ.subrepresentation N' h)).Finite) :
    Nat.card (ZcQ ρ N' h).ker ≤ (Zc (ρ.subrepresentation N' h)).ncard := by
  have hm : ∀ z : (ZcQ ρ N' h).ker, ∀ s, z.1.1 s ∈ N' := fun z s => by
    have h1 : ZcQ ρ N' h z.1 = 0 := z.2
    have h2 : N'.mkQ (z.1.1 s) = 0 := congrFun (congrArg Subtype.val h1) s
    exact (Submodule.Quotient.mk_eq_zero N').1 h2
  haveI : Finite (Zc (ρ.subrepresentation N' h)) := hf
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective (fun z => ⟨fun s => ⟨z.1.1 s, hm z s⟩,
    IsLocallyConstant.desc _ (Subtype.val) z.1.2.1 Subtype.val_injective, fun s t => Subtype.ext (z.1.2.2 s t)⟩) ?_
  intro a b hab
  ext s
  exact congrArg Subtype.val (congrFun (congrArg Subtype.val hab) s)

private theorem homMu_le {D N : Type} [Group D] [AddCommGroup N] [Finite N] (l : ℕ) [Fact l.Prime] (k : ℕ) (ε : D →* ℤ_[l]ˣ)
    (ρ : Representation ℤ D N) (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) :
    (HomMu l k ε (ρ.quotient N' h)).ncard ≤ (HomMu l k ε ρ).ncard ∧ 0 < (HomMu l k ε ρ).ncard := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (N →+ ZMod (l ^ k)) := Finite.of_injective _ DFunLike.coe_injective
  refine ⟨Set.ncard_le_ncard_of_injOn (fun f => f.comp N'.mkQ.toAddMonoidHom) (fun f hf s x => hf s (N'.mkQ x)) ?_, ?_⟩
  · intro a _ b _ hab
    ext x
    obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
    exact DFunLike.congr_fun hab y
  · exact (Set.ncard_pos).2 ⟨0, fun s x => by simp⟩

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.lift :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ε : D →* ℤ_[l]ˣ) (d k : ℕ), 0 < k → LE l D ε d → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ D N), (∀ x : N, l ^ k • x = 0) → IsOpen (ρ.ker : Set D) → ∀ (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) (C : ℕ), (HomMu l k ε (ρ.subrepresentation N' h)).ncard ≤ C → ∀ z : D → N, IsLocallyConstant z → (∀ s s', z (s * s') - z s - ρ s (z s') ∈ N') → ∃ y ∈ Zc ρ, ∀ s, y s - C.factorial • z s ∈ N' := by
  intro l _ D _ _ _ ε d k hk hLE N _ _ ρ hN hρ N' h C hC z hz hz'
  haveI : Finite (N ⧸ N') := Finite.of_surjective _ N'.mkQ_surjective
  obtain ⟨-, e1⟩ := hLE k hk N ρ hN hρ
  obtain ⟨f2, e2⟩ := hLE k hk N' (ρ.subrepresentation N' h) (fun x => Subtype.ext (hN x.1))
    (Subgroup.isOpen_mono (H₁ := ρ.ker) (fun s hs => by
      have h1 : ρ s = 1 := hs
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ρ s x.1 = x.1
      rw [h1]; rfl) hρ)
  obtain ⟨f3, e3⟩ := hLE k hk (N ⧸ N') (ρ.quotient N' h) (fun x => by
      obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
      rw [← map_nsmul, hN, map_zero])
    (Subgroup.isOpen_mono (H₁ := ρ.ker) (fun s hs => by
      have h1 : ρ s = 1 := hs
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
      show N'.mkQ (ρ s y) = N'.mkQ y
      rw [h1]; rfl) hρ)
  have e4 := idx_mul (ZcQ ρ N' h)
  rw [card_ZcA, card_ZcA, e1, e3] at e4
  have e5 := ker_le ρ N' h f2
  rw [e2] at e5
  obtain ⟨e6, e7⟩ := homMu_le l k ε ρ N' h
  have e8 : Nat.card N = Nat.card N' * Nat.card (N ⧸ N') := Submodule.card_eq_card_quotient_mul_card N'
  have hpos : 0 < Nat.card N ^ (1 + d) * (HomMu l k ε ρ).ncard := Nat.mul_pos (pow_pos Nat.card_pos _) e7
  have hle : (ZcQ ρ N' h).range.index ≤ C := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [e4]
    calc _ ≤ Nat.card (N ⧸ N') ^ (1 + d) * (HomMu l k ε ρ).ncard * (Nat.card N' ^ (1 + d) * C) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ e6) (e5.trans (Nat.mul_le_mul_left _ hC))
      _ = _ := by rw [e8, mul_pow]; ring
  haveI : Finite (ZcA (ρ.quotient N' h)) := f3
  have hne : (ZcQ ρ N' h).range.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hne) hle
  let w : ZcA (ρ.quotient N' h) := ⟨fun s => N'.mkQ (z s), hz.comp N'.mkQ, fun s t => by
    show N'.mkQ (z (s * t)) = N'.mkQ (z s + ρ s (z t))
    refine (Submodule.Quotient.eq N').2 ?_
    rw [← sub_sub]; exact hz' s t⟩
  have hw : C.factorial • w ∈ (ZcQ ρ N' h).range := by
    rw [hc, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_index_mem _ w) c
  obtain ⟨y, hy⟩ := hw
  refine ⟨y.1, y.2, fun s => (Submodule.Quotient.eq N').1 ?_⟩
  have h2 : N'.mkQ (y.1 s) = C.factorial • N'.mkQ (z s) := congrFun (congrArg Subtype.val hy) s
  rw [← map_nsmul] at h2
  exact h2
