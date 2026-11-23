import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullLevel

section Abstract

variable {G L : Type} [CommGroup G] [AddCommGroup L] {r n : ℕ} {ev : L → G}

theorem ev_basis (add : ∀ a b, ev (a + b) = ev a * ev b) (bas : (Fin r → ℤ) ≃ₗ[ℤ] L) (c : Fin r → ℤ) :
    ev (bas c) = ∏ i, ev (bas (Pi.single i 1)) ^ c i := by
  let f : L →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ev a)) fun a b => by rw [add, ofMul_mul]
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin r → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : f (bas c) = ∑ i, c i • f (bas (Pi.single i 1)) := by
    conv_lhs => rw [hc]
    simp only [map_sum, map_zsmul]
  have h' := congrArg Additive.toMul h
  rw [toMul_sum] at h'
  simp only [toMul_zsmul] at h'
  exact h'

theorem card_torsion (hn : 0 < n) (add : ∀ a b, ev (a + b) = ev a * ev b) (ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b)
    (onto : ∀ x, x ^ n = 1 ↔ ∃ a, ev a = x) (bas : (Fin r → ℤ) ≃ₗ[ℤ] L) :
    Nat.card {x : G // x ^ n = 1} = n ^ r := by
  let f : (Fin r → Fin n) → {x : G // x ^ n = 1} := fun c => ⟨ev (bas fun i => (c i : ℕ)), (onto _).2 ⟨_, rfl⟩⟩
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hb : Function.Bijective f := by
    refine ⟨fun c c' h => ?_, fun x => ?_⟩
    · have h₁ : ev (bas fun i => (c i : ℕ)) = ev (bas fun i => (c' i : ℕ)) := congrArg Subtype.val h
      have h₂ := add (bas (fun i => (c i : ℕ)) - bas fun i => (c' i : ℕ)) (bas fun i => (c' i : ℕ))
      rw [sub_add_cancel, h₁] at h₂
      obtain ⟨b, hb⟩ := (ker _).1 (mul_eq_right.1 h₂.symm)
      obtain ⟨b, rfl⟩ := bas.surjective b
      rw [← map_sub, ← map_nsmul] at hb
      funext i
      have h₃ : ((c i : ℕ) : ℤ) - (c' i : ℕ) = n * b i := by simpa using congrFun (bas.injective hb) i
      have h₄ : ((c' i : ℕ) : ℤ) ≡ (c i : ℕ) [ZMOD n] := (Int.modEq_iff_dvd).2 ⟨_, h₃⟩
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.1 h₄) (c' i).2 (c i).2).symm
    · obtain ⟨a, ha⟩ := (onto _).1 x.2
      obtain ⟨a, rfl⟩ := bas.surjective a
      have h₀ : ∀ i, 0 ≤ a i % n := fun i => Int.emod_nonneg _ hn'.ne'
      refine ⟨fun i => ⟨(a i % n).toNat, by have := Int.emod_lt_of_pos (a i) hn'; have := h₀ i; omega⟩,
        Subtype.ext ?_⟩
      have e : a = (fun i => (((a i % n).toNat : ℕ) : ℤ)) + n • fun i => a i / n := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.toNat_of_nonneg (h₀ i)]
        exact (Int.emod_add_mul_ediv _ _).symm
      rw [← ha]
      conv_rhs => rw [e, map_add, add, map_nsmul, (ker _).2 ⟨_, rfl⟩, _root_.mul_one]
  rw [← Nat.card_eq_of_bijective f hb]
  simp

end Abstract

end GlobalTheory.FullLevel

namespace GlobalTheory

open FullLevel in

theorem exists_level_of_full : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), (∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = stdSymp g i j) → ∀ (K : Type) [Field K] [IsAlgClosed K] (o : Full D K) (M : ℕ), 0 < M → ∃ (hg : o.P.g = g) (lev : Out.Level o.P M (unitOn (o.I.ζ M))), (∀ i, levelBasis lev hg i = o.I.ev M (bas (Pi.single i 1))) ∧ ∀ c : Fin (2 * g) → ℤ, levelPoint lev hg (fun i => (c i : ZMod M)) = o.I.ev M (bas c) := by
  intro hL E _ _ _ H D g bas hb K _ _ o M hM
  have := o.charZero
  have := o.P.isAb.comm
  have : NeZero M := ⟨hM.ne'⟩
  have hg : o.P.g = g := by
    have h₁ := (hL.mulN _ o.P 2 one_le_two).2.2.2.2 K (𝟙 _) (by norm_num)
    have h₂ := card_torsion (G := baseOver (Sp K) ⟶ o.P.A) two_pos (o.I.add 2) (o.I.ker 2 two_pos)
      (o.I.onto 2 two_pos) bas
    have h₃ := Nat.pow_right_injective le_rfl (h₁.symm.trans h₂)
    omega
  subst hg
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : K →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom (o.I.ζ M)) M := fun φ =>
    (o.I.ζ_prim M hM).map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have tor : ∀ a, o.I.ev M a ^ M = 1 := fun a => (o.I.onto M hM _).2 ⟨a, rfl⟩
  obtain ⟨lev, hlev⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) o.P M (unitOn (o.I.ζ M))
    (by have := nt K; exact prim (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    (fun F _ s => by
      have := nt F
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)⟩
      have : CharZero F := charZero_of_injective_ringHom (Spec.preimage s).hom.injective
      exact Nat.cast_ne_zero.2 hM.ne')
    (fun i => o.I.ev M (bas (Pi.single i 1))) (fun i => tor _)
    (fun i j => by
      have h := o.I.isom M hM (bas (Pi.single i 1)) (bas (Pi.single j 1))
      rw [hb] at h
      have e : unitOn (o.I.ζ M ^ stdSymp o.P.g i j) = unitOn (o.I.ζ M) ^ stdSymp o.P.g i j := map_zpow _ _ _
      exact e ▸ h)
  refine ⟨rfl, lev, fun i => congrFun hlev i, fun c => ?_⟩
  rw [levelPoint_rfl, Level.toPt, hlev, ev_basis (G := baseOver (Sp K) ⟶ o.P.A) (o.I.add M) bas c, linComb,
    List.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' _ (tor _)]

end GlobalTheory
