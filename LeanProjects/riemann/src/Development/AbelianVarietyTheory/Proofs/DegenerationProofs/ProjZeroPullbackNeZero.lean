import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

namespace GlobalTheory.ThetaInvPart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem diag_eq [IsDomain o] {Q : Type} [AddCommGroup Q] [Fintype Q] (π : S.Gam →+ Q) (i₀ : S.J)
    (hc : Fintype.card S.J = Fintype.card Q)
    (hfix : ∀ a, π a = 0 → ∀ l, S.ρ a l i₀ = if l = i₀ then 1 else 0)
    (horb : ∀ i, ∃ a, ∃ e : ℕ, ∀ l, S.ρ a l i₀ = if l = i then S.ζ ^ e else 0) (a : S.Gam) :
    S.ρ a i₀ i₀ = if π a = 0 then 1 else 0 := by
  have hζ : S.ζ ≠ 0 := S.prim.ne_zero (pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega)
    (by have := S.N_ge; omega)))
  choose c e hce using horb
  have key : ∀ a b, π a = π b → ∃ k : ℕ, ∀ l, S.ρ b l i₀ = S.ζ ^ k * S.ρ a l i₀ := fun a b h => by
    obtain ⟨k, hk⟩ := S.ρ_mul b (a - b)
    refine ⟨k, fun l => ?_⟩
    have := congrFun (congrFun hk l) i₀
    rw [Matrix.mul_apply, add_sub_cancel, Matrix.smul_apply, smul_eq_mul] at this
    simpa [hfix (a - b) (by rw [map_sub, h, sub_self])] using this
  have inj : Function.Injective fun i => π (c i) := fun i j h => by
    obtain ⟨k, hk⟩ := key _ _ h
    by_contra hij
    have := hk j
    rw [hce, hce, if_pos rfl, if_neg (Ne.symm hij), mul_zero] at this
    exact pow_ne_zero _ hζ this
  have surj := ((Fintype.bijective_iff_injective_and_card _).2 ⟨inj, hc⟩).2
  have zero : ∀ a i, π (c i) = π a → i ≠ i₀ → S.ρ a i₀ i₀ = 0 := fun a i h hi => by
    obtain ⟨k, hk⟩ := key _ _ h
    rw [hk, hce, if_neg (Ne.symm hi), mul_zero]
  split_ifs with ha
  · rw [hfix a ha, if_pos rfl]
  · obtain ⟨i, hi⟩ := surj (π a)
    refine zero a i hi fun h => ?_
    obtain ⟨j, hj⟩ := surj (π 0)
    by_cases h' : j = i₀
    · exact ha (by rw [← hi, h, ← h', hj, map_zero])
    · have := zero 0 j hj h'
      rw [hfix 0 (map_zero π), if_pos rfl] at this
      exact one_ne_zero this

theorem rho_fix (hG : GlobalFnsSt) (hi : Function.Injective (algebraMap o Ω)) (ρ : S.Real) (a : S.Gam)
    (ha : (ρ.n ^ ρ.k) • S.r • a = 0) (l : S.J) : S.ρ a l ρ.i₀ = if l = ρ.i₀ then 1 else 0 := by
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hm : ρ.pt (S.r • a) ^ (ρ.n ^ ρ.k) = 1 := by rw [← hp, ha, h0]
  have hN : ρ.pt (S.r • a) ^ S.N = 1 :=
    (congrArg _ (ρ.N_eq.trans (sq _))).trans (by rw [pow_mul, hm, one_pow])
  obtain ⟨ν, hν⟩ := exists_gen_negLB hG _ ρ.P 1 (baseOver (Sp S.R))
  have hact := ThetaCoord.isActOf_self hG ρ.P.isAb ρ.P.isLB (q := S.N) (b := 1)
    (by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow) hν ρ.α_gen ρ.s_zero hm hN (ρ.U_sym a)
  have h₁ := ρ.U_act a ρ.i₀ _ hact
  have h₂ : ∀ j, (ρ.s ρ.i₀).f j = ∑ l, liftFun ρ.P.A _ (fn (algebraMap o S.R (if l = ρ.i₀ then 1 else 0))) *
      (ρ.s l).f j := fun j => by
    rw [Finset.sum_eq_single ρ.i₀ (fun b _ hb => by simp [hb, liftFun]) (by simp)]
    simp [liftFun]
  have h₃ := congrFun ((ρ.s_basis (ρ.s ρ.i₀)).unique h₁ h₂) l
  have h₄ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv).1 h₃
  exact hi (congrArg Subtype.val h₄)

end GlobalTheory.ThetaInvPart

namespace GlobalTheory

open ThetaInvPart

theorem proj_zero_pullback_ne_zero : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (k : Type) [Field k] (y : o →+* k) (T : AddSubgroup S.Gam), S.IsoFree T →
    ∃ j, y (S.proj T 0 j ρ.i₀) ≠ 0 := by
  intro hL o Ω _ _ _ hA S ρ k _ y T _
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero (ρ.n ^ ρ.k) := ⟨pow_ne_zero _ ρ.n_prime.ne_zero⟩
  have : IsDomain o := hA.inj.isDomain _
  have hd : ρ.n ^ ρ.k ∣ S.r * S.N := by
    rw [ρ.N_eq]; exact Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) _
  let π : S.Gam →+ (Fin S.g ⊕ Fin S.g → ZMod (ρ.n ^ ρ.k)) :=
    (ZMod.castHom hd (ZMod (ρ.n ^ ρ.k))).toAddMonoidHom.compLeft _
  have hdiag := diag_eq π ρ.i₀ (by
      rw [ρ.card, ρ.N_eq, ← pow_mul]
      simp [two_mul])
    (fun a ha => rho_fix hL.1.globalFns hA.inj ρ a (funext fun i => by
      have h : ZMod.castHom hd (ZMod (ρ.n ^ ρ.k)) (a i) = 0 := congrFun ha i
      rw [← ZMod.natCast_zmod_val (a i), map_natCast, ZMod.natCast_eq_zero_iff] at h
      obtain ⟨c, hc⟩ := h
      rw [Pi.smul_apply, Pi.smul_apply, ← ZMod.natCast_zmod_val (a i), hc, nsmul_eq_mul, nsmul_eq_mul,
        ← Nat.cast_mul, ← Nat.cast_mul, Pi.zero_apply, ZMod.natCast_eq_zero_iff]
      exact ⟨c, by rw [ρ.N_eq]; ring⟩)) ρ.orbit
  have hu : ∀ n : ℕ, n ∣ Nat.card S.Gam → IsUnit (n : o) := fun n hn => by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast hn) ?_
    rw [Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  refine ⟨ρ.i₀, (IsUnit.map y ?_).ne_zero⟩
  have := Fintype.ofFinite T
  have hT := AddSubgroup.card_addSubgroup_dvd_card T
  have hK := (AddSubgroup.card_addSubgroup_dvd_card (π.comp T.subtype).ker).trans hT
  have hs : ∑ t : T, S.ρ t ρ.i₀ ρ.i₀ = (Nat.card (π.comp T.subtype).ker : o) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hdiag]
    by_cases h : π t = 0 <;> simp [AddMonoidHom.mem_ker, h]
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [AddMonoidHom.zero_apply, neg_zero, ZMod.val_zero, pow_zero, one_smul]
  rw [hs]
  exact (hu _ hT).ringInverse.mul (hu _ hK)

end GlobalTheory
