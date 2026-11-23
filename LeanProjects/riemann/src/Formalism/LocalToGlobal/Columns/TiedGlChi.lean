import Formalism.LocalToGlobal.Columns.TiedGl
import Formalism.LocalToGlobal.HermitianForms.DefsChi

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV
open Formalism.L2.Forms (kv)

section Chi

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok)

theorem glc_extChi {κ K : Type} [CommRing κ] [Field K] {m : ℕ} (χ : Fin m → κˣ →* Kˣ) {a : ℕ} (ha : a < m) : extChi χ a = χ ⟨a, ha⟩ :=
  dif_pos ha

include hPr in
theorem glc_charP (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) : CharP (kP w) (Pr.g i) := by
  have : Nontrivial (kP w) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  rw [CharP.charP_iff_prime_eq_zero (hPr.g_prime i)]
  have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 X.E) ∈ w.asIdeal := Ideal.absNorm_mem _
  rw [hPr.vG_norm i w hw] at h1
  have := Ideal.Quotient.eq_zero_iff_mem.2 h1
  rwa [map_natCast] at this

theorem glc_order {g : ℕ} [Fact g.Prime] {K : Type} [Field K] (σ₀ : K →+* ℂ) (om₀ : (ZMod g)ˣ →* Kˣ) (hinj : Function.Injective om₀) :
    orderOf (MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀) : MulChar (ZMod g) ℂ) = g - 1 := by
  set om : MulChar (ZMod g) ℂ := MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀) with hom
  have hpow : ∀ k : ℕ, om ^ k = 1 ↔ ∀ x : (ZMod g)ˣ, x ^ k = 1 := by
    intro k
    constructor
    · intro h x
      have h1 := DFunLike.congr_fun h (x : ZMod g)
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hom, MulChar.ofUnitHom_coe] at h1
      have h2 : σ₀ ((om₀ (x ^ k) : Kˣ) : K) = σ₀ 1 := by
        rw [map_pow, Units.val_pow_eq_pow_val, map_pow, map_one]
        exact h1
      have h3 : om₀ (x ^ k) = om₀ 1 := by
        rw [map_one]
        exact Units.ext (σ₀.injective h2)
      exact hinj h3
    · intro h
      ext x
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hom, MulChar.ofUnitHom_coe, ← Units.val_pow_eq_pow_val, ← map_pow, h x, map_one,
        Units.val_one]
  have hcard : Monoid.exponent (ZMod g)ˣ = g - 1 := by
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units]
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, hpow]
    intro x
    rw [← hcard]
    exact Monoid.pow_exponent_eq_one x
  · rw [← hcard]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one ((hpow _).1 (pow_orderOf_eq_one om))

theorem glc_pow (i : Fin 2) : ∃ om : MulChar (ZMod (Pr.g i)) ℂ, orderOf om = Pr.g i - 1 ∧
    ∀ v h a (n : ℤ), a < m → (tieGLoc hPr S Ch σ₀ hCh).chiB i v h a (n : kv X.F v) = (om ^ (2 * (a + 1))) (n : ZMod (Pr.g i)) := by
  haveI : Fact (Pr.g i).Prime := ⟨hPr.g_prime i⟩
  obtain ⟨om₀, hinj, hom⟩ := hCh.chi_om i
  refine ⟨MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀), glc_order σ₀ om₀ hinj, ?_⟩
  intro v h a n ha
  haveI := glc_charP hPr i (gwOf_mem hc hPr i v h)
  have hcast : (n : kv X.F v) = S.eK hPr i v h (n : kP (gwOf hc hPr i v h).1) := (map_intCast _ n).symm
  show glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) a) (n : kv X.F v) = _
  by_cases hn : ((Pr.g i : ℕ) : ℤ) ∣ n
  · have h1 : (n : ZMod (Pr.g i)) = 0 := (CharP.intCast_eq_zero_iff _ (Pr.g i) n).2 hn
    have h2 : (n : kP (gwOf hc hPr i v h).1) = 0 := (CharP.intCast_eq_zero_iff _ (Pr.g i) n).2 hn
    rw [hcast, h1, h2, map_zero, MulChar.map_zero, MulChar.map_zero]
  · have h1 : (n : ZMod (Pr.g i)) ≠ 0 := fun h0 => hn ((CharP.intCast_eq_zero_iff _ (Pr.g i) n).1 h0)
    have h2 : (n : kP (gwOf hc hPr i v h).1) ≠ 0 := fun h0 => hn ((CharP.intCast_eq_zero_iff _ (Pr.g i) n).1 h0)
    have h3 : (n : kv X.F v) ≠ 0 := by
      rw [hcast]
      exact fun h0 => h2 ((map_eq_zero_iff _ (S.eK hPr i v h).injective).1 h0)
    let a' : (ZMod (Pr.g i))ˣ := Units.mk0 _ h1
    let x : (kP (gwOf hc hPr i v h).1)ˣ := Units.map (S.eK hPr i v h).symm.toRingHom.toMonoidHom (Units.mk0 _ h3)
    have hx : (x : kP (gwOf hc hPr i v h).1) = (n : kP (gwOf hc hPr i v h).1) := by
      show (S.eK hPr i v h).symm (n : kv X.F v) = _
      rw [hcast, RingEquiv.symm_apply_apply]
    have hval : (x : kP (gwOf hc hPr i v h).1) = (((a' : ZMod (Pr.g i)).val : ℕ) : kP (gwOf hc hPr i v h).1) := by
      rw [hx, ZMod.natCast_val]
      exact (map_intCast (ZMod.castHom (dvd_refl (Pr.g i)) (kP (gwOf hc hPr i v h).1)) n).symm
    have h4 := hom (gwOf hc hPr i v h) (gwOf_mem hc hPr i v h) ⟨a, ha⟩ a' x hval
    rw [hcast, ← hx, glmChi_apply, glc_extChi _ ha, h4]
    have h5 : (n : ZMod (Pr.g i)) = (a' : ZMod (Pr.g i)) := rfl
    rw [h5, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, Units.val_pow_eq_pow_val, map_pow]
    rfl

theorem tieGLoc_chiTied : Formalism.L2.Forms.CharacterCompatible (tieGLoc hPr S Ch σ₀ hCh) m where
  dist i v h a b ha hb e := by
    have h1 : Ch.chi ⟨a, ha⟩ (gwOf hc hPr i v h) = Ch.chi ⟨b, hb⟩ (gwOf hc hPr i v h) := by
      ext x
      have h2 := DFunLike.congr_fun e (S.eK hPr i v h (x : kP (gwOf hc hPr i v h).1))
      change glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) a) _ =
        glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) b) _ at h2
      rw [glmChi_apply, glmChi_apply, glc_extChi _ ha, glc_extChi _ hb] at h2
      exact σ₀.injective h2
    have h3 := hCh.chi_inj (gwOf hc hPr i v h) h1
    exact congrArg Fin.val h3
  same i v h v' h' a n ha := by
    obtain ⟨om, -, hom⟩ := glc_pow hPr S Ch σ₀ hCh i
    rw [hom v h a n ha, hom v' h' a n ha]
  pow i := glc_pow hPr S Ch σ₀ hCh i

end Chi

end Formalism.L2.Col
