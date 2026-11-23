import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfDegree
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions NumberField

theorem T_sub_one_ge (D : D7) (u : D.what₂.Word) :
    D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 ≤ (D.mem u).A.T - 1 := by
  set M : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 with hM
  obtain ⟨π, -, hπ, hπ1⟩ := D.T_norm u
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.mp hπ1
  set cj : D.host.E →+* D.host.E := (D.host.conj : D.host.E →+* D.host.E) with hcj
  let αb : 𝓞 D.host.E := ⟨cj (α : D.host.E), (α.2).map cj.toIntAlgHom⟩
  let b : 𝓞 D.host.E := α + αb + (M : 𝓞 D.host.E) * α * αb
  have hαE : (π : D.host.E) = 1 + (M : D.host.E) * (α : D.host.E) := by
    have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hα
    simp only [map_mul, map_sub, map_one, map_natCast, RingOfIntegers.coe_eq_algebraMap] at this ⊢
    rw [← hM] at this
    linear_combination -this
  have hcπ : cj (π : D.host.E) = 1 + (M : D.host.E) * cj (α : D.host.E) := by
    rw [hαE, map_add, map_mul, map_one, map_natCast]
  have hT : ((D.mem u).A.T : D.host.E) - 1 = (M : D.host.E) * (b : D.host.E) := by
    have hπ' : (π : D.host.E) * cj (π : D.host.E) = ((D.mem u).A.T : D.host.E) := hπ
    rw [← hπ', hcπ, hαE]
    simp only [b, αb, map_add, map_mul, map_natCast, RingOfIntegers.coe_eq_algebraMap]
    show _ = (M : D.host.E) * ((α : D.host.E) + cj (α : D.host.E) + (M : D.host.E) * (α : D.host.E) * cj (α : D.host.E))
    ring
  have hMpos : 0 < M := by
    have hq : 0 < D.host.q := by have := D.host.qd_big.1; omega
    have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
    have hg0 := (D.host.g_prime 0).pos
    have hg1 := (D.host.g_prime 1).pos
    have hn : 0 < D.host.QS := D.host.QS_pos
    rw [hM]; positivity
  have hME : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  set r : ℚ := (((D.mem u).A.T : ℚ) - 1) / (M : ℚ) with hr
  have hbr : (b : D.host.E) = algebraMap ℚ D.host.E r := by
    rw [hr, map_div₀, map_sub, map_natCast, map_one, map_natCast, hT]
    field_simp
  have hint : IsIntegral ℤ r := by
    have h1 : IsIntegral ℤ (algebraMap ℚ D.host.E r) := hbr ▸ RingOfIntegers.isIntegral_coe b
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ D.host.E) (algebraMap ℚ D.host.E).injective).mp h1
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hTq : ((D.mem u).A.T : ℚ) - 1 = (M : ℚ) * (z : ℚ) := by
    have : (z : ℚ) = r := hz
    rw [this, hr]; field_simp
  have hT2 := (D.mem u).A.T_prime.two_le
  have hTz : ((D.mem u).A.T : ℤ) - 1 = (M : ℤ) * z := by exact_mod_cast hTq
  have hz1 : 1 ≤ z := by
    by_contra hc
    push Not at hc
    have : (M : ℤ) * z ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  have : (M : ℤ) ≤ ((D.mem u).A.T : ℤ) - 1 := by nlinarith
  omega

theorem finrank_host_lt_T_sub_one (D : D7) (u : D.what₂.Word) : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1 := by
  have hf : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h := T_sub_one_ge D u
  have hq : 2 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 2 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hg0 := (D.host.g_prime 0).two_le
  have hg1 := (D.host.g_prime 1).two_le
  have hgg : 4 ≤ D.host.g 0 * D.host.g 1 := by nlinarith
  have hgg2 : 16 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := by nlinarith
  have hQ : 0 < D.host.QS := D.host.QS_pos
  have hN : 0 < D.host.QS * D.host.q * D.host.d := by positivity
  haveI : NeZero (D.host.QS * D.host.q * D.host.d) := ⟨hN.ne'⟩
  have hcard : Nat.card D.R.GG ≤ Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ :=
    Nat.card_le_card_of_surjective _ D.host.der.art_surj
  have hGG : Nat.card D.R.GG = 4 * D.R.ord := D.R.natCard_GG
  have hphi : Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ ≤ D.host.QS * D.host.q * D.host.d := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_le _
  have key : D.host.QS * D.host.q * D.host.d < D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
    nlinarith
  omega

theorem class_injective_of_self_dual
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramP D) (Tf.clsP.lat c) =
        (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E))) :
    ClassMapInjective :=
  classMapInjective_of_finrank_lt hSD (fun D u _ _ _ => finrank_host_lt_T_sub_one D u)

end Formalism.L2.GlobalTheoryTheory.Br
