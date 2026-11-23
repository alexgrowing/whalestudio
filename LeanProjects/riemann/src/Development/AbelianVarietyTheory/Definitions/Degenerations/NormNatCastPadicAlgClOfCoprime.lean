import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH
open Classical

section Form

variable {g n : ℕ}

theorem eStd_add_left (a a' b : Fin g ⊕ Fin g → ZMod n) : eStd g n (a + a') b = eStd g n a b + eStd g n a' b := by
  simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_add_right (a b b' : Fin g ⊕ Fin g → ZMod n) : eStd g n a (b + b') = eStd g n a b + eStd g n a b' := by
  simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_swap (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n b a = -eStd g n a b := by
  simp only [eStd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem eStd_self (a : Fin g ⊕ Fin g → ZMod n) : eStd g n a a = 0 :=
  Finset.sum_eq_zero fun i _ => by ring

@[simp] theorem eStd_zero_left (b : Fin g ⊕ Fin g → ZMod n) : eStd g n 0 b = 0 := by simp [eStd]

@[simp] theorem eStd_zero_right (a : Fin g ⊕ Fin g → ZMod n) : eStd g n a 0 = 0 := by simp [eStd]

theorem eStd_neg_left (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n (-a) b = -eStd g n a b := by
  simp only [eStd, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_neg_right (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n a (-b) = -eStd g n a b := by
  rw [eStd_swap, eStd_neg_left, neg_neg, eStd_swap]

def eStdBilin (g n : ℕ) : LinearMap.BilinForm (ZMod n) (Fin g ⊕ Fin g → ZMod n) :=
  LinearMap.mk₂ (ZMod n) (eStd g n) eStd_add_left
    (fun c a b => by
      simp only [eStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    eStd_add_right
    (fun c a b => by
      simp only [eStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

@[simp] theorem eStdBilin_apply (a b : Fin g ⊕ Fin g → ZMod n) : eStdBilin g n a b = eStd g n a b := rfl

theorem eStd_single_inr (a : Fin g ⊕ Fin g → ZMod n) (i : Fin g) :
    eStd g n a (Pi.single (.inr i) 1) = a (.inl i) := by
  simp [eStd, Pi.single_apply]

theorem eStd_single_inl (a : Fin g ⊕ Fin g → ZMod n) (i : Fin g) :
    eStd g n a (Pi.single (.inl i) 1) = -a (.inr i) := by
  simp [eStd, Pi.single_apply]

theorem eq_zero_of_eStd_eq_zero {a : Fin g ⊕ Fin g → ZMod n} (h : ∀ b, eStd g n a b = 0) : a = 0 := by
  funext k
  rcases k with i | i
  · exact (eStd_single_inr a i).symm.trans (h _)
  · exact neg_eq_zero.1 ((eStd_single_inl a i).symm.trans (h _))

theorem eStdBilin_bijective : Function.Bijective (eStdBilin g n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a h => eq_zero_of_eStd_eq_zero fun b => LinearMap.congr_fun h b,
    fun f => ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)), ?_⟩⟩
  refine (Pi.basisFun (ZMod n) _).ext fun k => ?_
  rcases k with i | i
  · simp [eStd_single_inl]
  · simp [eStd_single_inr]

theorem nsmul_eq_zero_iff_castHom {r N : ℕ} [NeZero (r * N)] (a : ZMod (r * N)) :
    r • a = 0 ↔ ZMod.castHom (dvd_mul_left N r) (ZMod N) a = 0 := by
  have hr : r ≠ 0 := left_ne_zero_of_mul (NeZero.ne (r * N))
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [map_natCast, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff,
    Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hr)]

end Form

namespace ThetaSys

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

instance instNeZeroExponent : NeZero S.N := ⟨by have := S.N_ge; omega⟩

instance instNeZeroLevel : NeZero (S.r * S.N) :=
  ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (NeZero.ne S.N)⟩

instance instNeZeroLevelSq : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩

variable {S}

theorem mem_perp {H : AddSubgroup S.Gam} {a : S.Gam} : a ∈ S.perp H ↔ ∀ h ∈ H, eStd S.g _ a h = 0 := Iff.rfl

theorem mem_perp' {H : AddSubgroup S.Gam} {a : S.Gam} : a ∈ S.perp H ↔ ∀ h ∈ H, eStd S.g _ h a = 0 :=
  forall₂_congr fun h _ => by rw [eStd_swap a h, neg_eq_zero]

theorem perp_anti {H H' : AddSubgroup S.Gam} (h : H ≤ H') : S.perp H' ≤ S.perp H :=
  fun _ ha x hx => ha x (h hx)

theorem le_perp_comm {H H' : AddSubgroup S.Gam} : H ≤ S.perp H' ↔ H' ≤ S.perp H :=
  ⟨fun h _ hx => mem_perp'.2 fun _ ha => h ha _ hx, fun h _ hx => mem_perp'.2 fun _ ha => h ha _ hx⟩

theorem le_perp_perp (H : AddSubgroup S.Gam) : H ≤ S.perp (S.perp H) := le_perp_comm.1 le_rfl

variable (S)

@[simp] theorem perp_bot : S.perp ⊥ = ⊤ := top_unique (le_perp_comm.1 bot_le)

@[simp] theorem perp_top : S.perp ⊤ = ⊥ :=
  bot_unique fun _ ha => eq_zero_of_eStd_eq_zero fun b => ha b trivial

@[simp] theorem perp_perp (H : AddSubgroup S.Gam) : S.perp (S.perp H) = H := by
  have h := (GlobalTheory.orthogonal_free_of_perfect_alt_zmod S.N S.r S.Gam (eStdBilin _ _) eStd_self
    eStdBilin_bijective).1 (AddSubgroup.toZModSubmodule _ H)
  refine le_antisymm (fun a ha => ?_) (le_perp_perp H)
  have h1 : a ∈ (eStdBilin S.g _).orthogonal ((eStdBilin S.g _).orthogonal (AddSubgroup.toZModSubmodule _ H)) :=
    fun b hb => mem_perp'.1 ha b (mem_perp'.2 hb)
  rwa [h] at h1

theorem bot_isoFree : S.IsoFree ⊥ := ⟨bot_le, 0, ⟨AddEquiv.ofUnique⟩⟩

theorem prim_ζN : IsPrimitiveRoot S.ζN S.N :=
  S.prim.pow (Nat.pos_of_ne_zero (NeZero.ne _)) (by ring)

def psi : AddChar (ZMod S.N) o := AddChar.zmodChar S.N S.prim_ζN.pow_eq_one

theorem psi_apply (a : ZMod S.N) : S.psi a = S.ζN ^ a.val := rfl

theorem psi_eq_one_iff {a : ZMod S.N} : S.psi a = 1 ↔ a = 0 := by
  rw [psi_apply, S.prim_ζN.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]

instance finite_hom (T : AddSubgroup S.Gam) : Finite (T →+ ZMod S.N) := DFunLike.finite _

theorem isUnit_natCard (T : AddSubgroup S.Gam) : IsUnit (Nat.card T : o) := by
  have h := T.card_addSubgroup_dvd_card
  rw [Nat.card_fun, Nat.card_zmod] at h
  refine isUnit_of_dvd_unit (Nat.cast_dvd_cast h) ?_
  rw [Nat.cast_pow]
  exact S.unit.pow _

@[simp] theorem ρ_zero : S.ρ 0 = 1 := S.ρ_one 0 (smul_zero _)

theorem ρ_add_of_eStd {a b : S.Gam} (h : eStd S.g _ a b = 0) : S.ρ a * S.ρ b = S.ρ (a + b) :=
  S.ρ_add a b (by rw [h, smul_zero])

theorem commute_ρ {a b : S.Gam} (h : eStd S.g _ a b = 0) : Commute (S.ρ a) (S.ρ b) := by
  rw [Commute, SemiconjBy, S.ρ_add_of_eStd h, S.ρ_add_of_eStd (by rw [eStd_swap, h, neg_zero]), add_comm]

theorem ρ_mul_ρ_neg (a : S.Gam) : S.ρ a * S.ρ (-a) = 1 := by
  rw [S.ρ_add_of_eStd (by rw [eStd_neg_right, eStd_self, neg_zero]), add_neg_cancel, ρ_zero]

theorem isUnit_ρ (a : S.Gam) : IsUnit (S.ρ a) :=
  ⟨⟨S.ρ a, S.ρ (-a), S.ρ_mul_ρ_neg a, by simpa using S.ρ_mul_ρ_neg (-a)⟩, rfl⟩

theorem nsmul_eq_zero_of_forall_hom {T : AddSubgroup S.Gam} {t : T} (h : ∀ c : T →+ ZMod S.N, c t = 0) :
    S.r • (t : S.Gam) = 0 := by
  funext k
  exact (nsmul_eq_zero_iff_castHom _).2 (h (((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
    (Pi.evalAddMonoidHom (fun _ => ZMod (S.r * S.N)) k)).comp T.subtype))

theorem sum_psi [IsDomain o] {A : Type} [AddCommGroup A] [Fintype A] (c : A →+ ZMod S.N) :
    ∑ a, S.psi (c a) = if c = 0 then (Fintype.card A : o) else 0 := by
  split_ifs with h
  · simp [h]
  · refine AddChar.sum_eq_zero_of_ne_one (ψ := S.psi.compAddMonoidHom c) fun h1 => h ?_
    ext a
    exact S.psi_eq_one_iff.1 (DFunLike.congr_fun h1 a)

theorem proj_eq_sum (T : AddSubgroup S.Gam) [Fintype T] (c : T →+ ZMod S.N) :
    S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, S.psi (-(c t)) • S.ρ t := by
  rw [proj, finsum_eq_sum_of_fintype]
  rfl

theorem proj_eq_one_of_eq_bot {T : AddSubgroup S.Gam} (h : T = ⊥) (c : T →+ ZMod S.N) : S.proj T c = 1 := by
  subst h
  rw [proj, finsum_unique, AddSubgroup.card_bot, Subsingleton.elim (default : (⊥ : AddSubgroup S.Gam)) 0]
  simp

variable {S}

theorem commute_ρ_proj {T : AddSubgroup S.Gam} (c : T →+ ZMod S.N) {h : S.Gam} (hh : h ∈ S.perp T) :
    Commute (S.ρ h) (S.proj T c) := by
  have := Fintype.ofFinite T
  rw [proj_eq_sum]
  exact (Commute.sum_right _ _ _ fun (t : T) _ => (S.commute_ρ (hh t t.2)).smul_right _).smul_right _

theorem ρ_mul_proj {T : AddSubgroup S.Gam} (hT : T ≤ S.perp T) (c : T →+ ZMod S.N) (t : T) :
    S.ρ t * S.proj T c = S.psi (c t) • S.proj T c := by
  have := Fintype.ofFinite T
  rw [proj_eq_sum, mul_smul_comm, smul_comm (S.psi (c t)), Finset.mul_sum, Finset.smul_sum (r := S.psi (c t))]
  congr 1
  refine Fintype.sum_equiv (Equiv.addLeft t) _ _ fun s => ?_
  rw [mul_smul_comm, S.ρ_add_of_eStd (hT t.2 s s.2), smul_smul, ← AddChar.map_add_eq_mul, Equiv.coe_addLeft,
    map_add c]
  congr 2
  ring

theorem proj_mul_ρ {T : AddSubgroup S.Gam} (hT : T ≤ S.perp T) (c : T →+ ZMod S.N) (t : T) :
    S.proj T c * S.ρ t = S.psi (c t) • S.proj T c :=
  (commute_ρ_proj c (hT t.2)).eq.symm.trans (ρ_mul_proj hT c t)

theorem proj_mul_of_weight [IsDomain o] {T : AddSubgroup S.Gam} (c c₀ : T →+ ZMod S.N) {K : Type}
    {B : Matrix S.J K o} (hB : ∀ t : T, S.ρ t * B = S.psi (c₀ t) • B) :
    S.proj T c * B = if c = c₀ then B else 0 := by
  have := Fintype.ofFinite T
  have h1 : ∀ t : T, (S.psi (-(c t)) • S.ρ t) * B = S.psi ((c₀ - c) t) • B := fun t => by
    rw [Matrix.smul_mul, hB, smul_smul, ← AddChar.map_add_eq_mul, AddMonoidHom.sub_apply, neg_add_eq_sub]
  rw [proj_eq_sum, Matrix.smul_mul, Matrix.sum_mul, Finset.sum_congr rfl fun t _ => h1 t, ← Finset.sum_smul,
    sum_psi, smul_smul]
  by_cases h : c = c₀
  · rw [if_pos h, if_pos (sub_eq_zero.2 h.symm), ← Nat.card_eq_fintype_card,
      Ring.inverse_mul_cancel _ (S.isUnit_natCard T), one_smul]
  · rw [if_neg h, if_neg fun h' => h (sub_eq_zero.1 h').symm, mul_zero, zero_smul]

theorem proj_mul_proj_of_le [IsDomain o] {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : T ≤ S.perp T)
    (c' : T' →+ ZMod S.N) (c : T →+ ZMod S.N) :
    S.proj T' c' * S.proj T c = if c' = c.comp (AddSubgroup.inclusion h) then S.proj T c else 0 :=
  proj_mul_of_weight c' _ fun t => ρ_mul_proj hT c (AddSubgroup.inclusion h t)

theorem proj_mul_proj [IsDomain o] {T : AddSubgroup S.Gam} (hT : T ≤ S.perp T) (c c' : T →+ ZMod S.N) :
    S.proj T c * S.proj T c' = if c = c' then S.proj T c else 0 := by
  rw [proj_mul_of_weight c c' (ρ_mul_proj hT c')]
  split_ifs with h
  · rw [h]
  · rfl

theorem proj_idem [IsDomain o] {T : AddSubgroup S.Gam} (hT : T ≤ S.perp T) (c : T →+ ZMod S.N) :
    S.proj T c * S.proj T c = S.proj T c := by
  rw [proj_mul_proj hT, if_pos rfl]

theorem proj_mul_proj_eq_zero [IsDomain o] {T : AddSubgroup S.Gam} (hT : T ≤ S.perp T) {c c' : T →+ ZMod S.N}
    (h : c ≠ c') : S.proj T c * S.proj T c' = 0 := by
  rw [proj_mul_proj hT, if_neg h]

variable (S) in

theorem sum_proj_eq_one [IsDomain o] (T : AddSubgroup S.Gam) [Fintype (T →+ ZMod S.N)] : ∑ c, S.proj T c = 1 := by
  have := Fintype.ofFinite T
  have h1 : ∀ t : T, ∑ c : T →+ ZMod S.N, S.psi (-(c t)) • S.ρ t =
      (∑ c : T →+ ZMod S.N, S.psi (-(c t))) • (1 : Matrix S.J S.J o) := fun t => by
    rw [← Finset.sum_smul]
    by_cases h : ∀ c : T →+ ZMod S.N, c t = 0
    · rw [S.ρ_one _ (S.nsmul_eq_zero_of_forall_hom h)]
    · have h2 := S.sum_psi (-(AddMonoidHom.eval t) : (T →+ ZMod S.N) →+ ZMod S.N)
      rw [if_neg fun h3 => h fun c => neg_eq_zero.1 (DFunLike.congr_fun h3 c)] at h2
      rw [show ∑ c : T →+ ZMod S.N, S.psi (-(c t)) = 0 from h2, zero_smul, zero_smul]
  have h2 : ∀ c : T →+ ZMod S.N, ∑ t : T, S.psi (-(c t)) = if c = 0 then (Nat.card T : o) else 0 := fun c => by
    have := S.sum_psi (-c)
    simpa only [neg_eq_zero, AddMonoidHom.neg_apply, Nat.card_eq_fintype_card] using this
  simp only [proj_eq_sum]
  rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun t _ => h1 t, ← Finset.sum_smul, Finset.sum_comm,
    Finset.sum_congr rfl fun c _ => h2 c, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), smul_smul,
    Ring.inverse_mul_cancel _ (S.isUnit_natCard T), one_smul]

variable (S) in

theorem finsum_proj_eq_one [IsDomain o] (T : AddSubgroup S.Gam) : ∑ᶠ c, S.proj T c = 1 := by
  have := Fintype.ofFinite (T →+ ZMod S.N)
  rw [finsum_eq_sum_of_fintype, sum_proj_eq_one]

theorem IsoFree.proj_spec [IsDomain o] {T : AddSubgroup S.Gam} (hT : S.IsoFree T) :
    (∀ c c', S.proj T c * S.proj T c' = if c = c' then S.proj T c else 0) ∧ ∑ᶠ c, S.proj T c = 1 ∧
      ∀ c, ∀ h ∈ S.perp T, S.ρ h * S.proj T c = S.proj T c * S.ρ h :=
  ⟨proj_mul_proj hT.1, S.finsum_proj_eq_one T, fun c _ hh => (commute_ρ_proj c hh).eq⟩

variable (S)

theorem FF_mem (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) :
    S.FF T c k ∈ S.R := by
  have := Fintype.ofFinite T
  rw [FF, finsum_eq_sum_of_fintype]
  exact sum_mem fun t _ => mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem map_FF {K : Type} [CommRing K] (y : S.R →+* K) (T : AddSubgroup S.Gam) [Fintype T] (c : T →+ ZMod S.N)
    (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) (hk : S.FF T c k ∈ S.R) :
    y ⟨S.FF T c k, hk⟩ = ∑ t : T, y (algebraMap o S.R S.ζ) ^ (k.2 t).val *
      ∑ j, y (algebraMap o S.R (S.proj T c j k.1)) * y ⟨S.ev t j, S.ev_mem t j⟩ := by
  simp only [← map_mul, ← map_sum, ← map_pow]
  congr 1
  apply Subtype.ext
  simp [FF, finsum_eq_sum_of_fintype]

theorem FF_eq_of_eq_bot {T : AddSubgroup S.Gam} (h : T = ⊥) (c : T →+ ZMod S.N)
    (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k = algebraMap o Ω (S.ζ ^ (k.2 0).val) * S.ev 0 k.1 := by
  rw [FF, S.proj_eq_one_of_eq_bot h]
  subst h
  rw [finsum_unique, Subsingleton.elim (default : (⊥ : AddSubgroup S.Gam)) 0]
  simp [Matrix.one_apply]

theorem norm_ζ {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p) : ‖y (algebraMap o S.R S.ζ)‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne ((S.r * S.N) ^ 2))).1 ?_
  rw [← norm_pow, ← map_pow, ← map_pow, S.prim.pow_eq_one, map_one, map_one, norm_one]

theorem norm_eq_one_of_isUnit {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p}
    (hy : ∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) {a : o} (ha : IsUnit a) : ‖y (algebraMap o S.R a)‖ = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h : ‖y (algebraMap o S.R a)‖ * ‖y (algebraMap o S.R b)‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, hb, map_one, map_one, norm_one]
  nlinarith [hy a, hy b, norm_nonneg (y (algebraMap o S.R a)), norm_nonneg (y (algebraMap o S.R b))]

namespace Test

variable {S} {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)

theorem q_pos {α : τ.X} (h : α ≠ 0) : 0 < τ.q α := by
  have hinj : Function.Injective fun n : ℤ => n • α := smul_left_injective ℤ h
  obtain ⟨n, hn⟩ := ((τ.pos.comp hinj.tendsto_cofinite).eventually_gt_atTop 0).exists
  rw [Function.comp_apply, QuadraticMap.map_smul, zsmul_eq_mul, Int.cast_mul] at hn
  by_contra h0
  nlinarith [mul_self_nonneg (n : ℝ)]

theorem q_nonneg (α : τ.X) : 0 ≤ τ.q α := by
  rcases eq_or_ne α 0 with rfl | h
  · rw [map_zero]
  · exact (τ.q_pos h).le

theorem exists_shortest (β : τ.X) : ∃ v : τ.X, ∀ v0, τ.q (β + S.N • v) ≤ τ.q (β + S.N • v + S.N • v0) := by
  have hinj : Function.Injective fun v : τ.X => β + S.N • v := fun v w h =>
    smul_right_injective τ.X (r := (S.N : ℤ)) (Int.natCast_ne_zero.2 (NeZero.ne S.N)) (by simpa using h)
  obtain ⟨v, hv⟩ := (τ.pos.comp hinj.tendsto_cofinite).exists_forall_le
  exact ⟨v, fun v0 => by simpa only [Function.comp_apply, smul_add, add_assoc] using hv (v + v0)⟩

theorem shortest_zero (v0 : τ.X) : τ.q 0 ≤ τ.q (0 + S.N • v0) := by
  rw [map_zero]
  exact τ.q_nonneg _

@[simp] theorem wt_nsmul (v : τ.X) : τ.wt (S.N • v) = 0 := by
  ext t
  rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddMonoidHom.zero_apply]

theorem perp_ker_le_ker : S.perp τ.yy.ker ≤ τ.yy.ker := τ.isoFree.1.trans (S.perp_perp _).le

theorem norm_th_le (x : S.Gam) : ‖y ⟨S.th x, S.th_mem x⟩‖ ≤ τ.δ := τ.δ_max.2 ⟨x, rfl⟩

theorem δ_eq (τ' : S.Test p y) : τ.δ = τ'.δ := τ.δ_max.unique τ'.δ_max

theorem ker_eq (τ' : S.Test p y) : τ.yy.ker = τ'.yy.ker := by
  rw [← τ.supp, ← τ'.supp, τ.δ_eq τ']

end Test

variable (M : RatModel o Ω)

theorem mem_supI {z : M.Z} {x : S.Gam} : x ∈ S.supI M z ↔ M.Div S.th x z := Iff.rfl

@[simp] theorem perp_TT (z : M.Z) : S.perp (S.TT M z) = S.HH M z := S.perp_perp _

theorem supI_mono {ξ z : M.Z} (h : ξ ⤳ z) : S.supI M z ⊆ S.supI M ξ := fun _ hx => RatModel.Div.of_specializes hx h

theorem HH_mono {ξ z : M.Z} (h : ξ ⤳ z) : S.HH M z ≤ S.HH M ξ := AddSubgroup.closure_mono (S.supI_mono M h)

theorem TT_anti {ξ z : M.Z} (h : ξ ⤳ z) : S.TT M ξ ≤ S.TT M z := perp_anti (S.HH_mono M h)

theorem TT_genericPoint : S.TT M (genericPoint M.Z) = ⊥ := by
  have h : S.supI M (genericPoint M.Z) = {x | S.th x ≠ 0} :=
    Set.ext fun _ => ⟨fun h => h.1, fun h => RatModel.div_genericPoint h⟩
  rw [TT, HH, h, S.supp, perp_top]

end ThetaSys

theorem ArithBase.isDomain (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] : IsDomain o :=
  h.inj.isDomain

theorem ArithBase.charZero (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] : CharZero o :=
  have := h.char
  (algebraMap o Ω).charZero

instance : ArithBase ℤ ℚ := ⟨inferInstance, inferInstance, inferInstance, IsFractionRing.injective ℤ ℚ⟩

namespace ThetaSys

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

def Test.good {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p) (δ : ℝ)
    (hmax : IsGreatest (Set.range fun x => ‖y ⟨S.th x, S.th_mem x⟩‖) δ) (hpos : 0 < δ)
    (hsupp : AddSubgroup.closure {x | ‖y ⟨S.th x, S.th_mem x⟩‖ = δ} = ⊤)
    (hev : ∀ h, IsGreatest (Set.range fun i => ‖y ⟨S.ev h i, S.ev_mem h i⟩‖) δ) : S.Test p y :=
  have hT : S.perp (0 : S.Gam →+ PUnit ⧸ (nsmulAddMonoidHom (S.r * S.N) : PUnit →+ PUnit).range).ker = ⊥ := by
    rw [AddMonoidHom.ker_zero, perp_top]
  have hs : ∀ c h i, ∑ j, y (algebraMap o S.R (S.proj _ c j i)) * y ⟨S.ev h j, S.ev_mem h j⟩ =
      y ⟨S.ev h i, S.ev_mem h i⟩ := fun c h i => by
    rw [S.proj_eq_one_of_eq_bot hT]
    simp [Matrix.one_apply, apply_ite]
  { X := PUnit
    q := 0
    pos := by
      rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
    yy := 0
    yy_onto := fun a => ⟨0, by
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
      rfl⟩
    isoFree := hT ▸ S.bot_isoFree
    wt := 0
    wt_eq := fun x α _ t => by
      rw [(AddSubgroup.mem_bot.1 (hT.le t.2) : (t : S.Gam) = 0), eStd_zero_left]
      exact (map_zero _).symm
    δ := δ
    δ_max := hmax
    δ_pos := hpos
    supp := hsupp.trans AddMonoidHom.ker_zero.symm
    tx := fun x _ => ⟨0, rfl, by simpa using hmax.2 ⟨x, rfl⟩⟩
    le := fun α _ h _ i => by
      rw [hs]
      simpa using (hev h).2 ⟨i, rfl⟩
    eq := fun α _ => by
      obtain ⟨i, hi⟩ := (hev 0).1
      refine ⟨(i, 0), S.FF_mem _ _ _, ?_⟩
      simp only [S.FF_eq_of_eq_bot hT]
      simpa using hi
    unit0 := fun h _ => by
      obtain ⟨i, hi⟩ := (hev h).1
      exact ⟨i, by rw [hs]; exact hi⟩ }

def Test.ofNormOne {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p) (hth : ∀ x, ‖y ⟨S.th x, S.th_mem x⟩‖ = 1)
    (hev : ∀ x i, ‖y ⟨S.ev x i, S.ev_mem x i⟩‖ = 1) : S.Test p y :=
  Test.good S y 1 (by simp [hth]) one_pos (by simp [hth]) fun h => by simp [hev]

theorem hasTests_of_eq_one (hth : ∀ x, S.th x = 1) (hev : ∀ x i, S.ev x i = 1) : S.HasTests := fun _ _ y _ =>
  ⟨Test.ofNormOne S y (fun x => by rw [show (⟨_, S.th_mem x⟩ : S.R) = 1 from Subtype.ext (hth x), map_one, norm_one])
    fun x i => by rw [show (⟨_, S.ev_mem x i⟩ : S.R) = 1 from Subtype.ext (hev x i), map_one, norm_one]⟩

variable {S} in

theorem Test.mem_E_iff_of_norm_eq_one {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    (hth : ∀ x, ‖y ⟨S.th x, S.th_mem x⟩‖ = 1) (hev : ∀ x i, ‖y ⟨S.ev x i, S.ev_mem x i⟩‖ = 1)
    (v : S.J → PadicAlgCl p) : v ∈ τ.E ↔ ∀ j, ‖v j‖ ≤ 1 := by
  have hδ : τ.δ = 1 := by
    obtain ⟨x, hx⟩ := τ.δ_max.1
    exact hx.symm.trans (hth x)
  have hT : S.perp τ.yy.ker = ⊥ := by
    rw [← τ.supp, hδ]
    simp [hth]
  have hq : ∀ α, (∀ v0, τ.q α ≤ τ.q (α + S.N • v0)) → Real.exp (τ.q α / S.N) = 1 := fun α hα => by
    obtain ⟨k, hk, h⟩ := τ.eq α hα
    have e : (⟨_, hk⟩ : S.R) = algebraMap o S.R S.ζ ^ (k.2 0).val * ⟨_, S.ev_mem 0 k.1⟩ :=
      Subtype.ext (by simpa using S.FF_eq_of_eq_bot hT _ k)
    rw [e, map_mul, map_pow, norm_mul, norm_pow, S.norm_ζ, hev, hδ, one_pow, _root_.one_mul, _root_.one_mul,
      Real.exp_neg] at h
    exact inv_eq_one.1 h.symm
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨α, l, i, hα, hl, rfl⟩ := h
      intro j
      rw [hq α hα] at hl
      simp only [S.proj_eq_one_of_eq_bot hT, Matrix.one_apply]
      split_ifs <;> simp [hl]
    | zero => simp
    | add a b _ _ ha hb => exact fun j => (mem_OO_iff _).1 (add_mem ((mem_OO_iff _).2 (ha j)) ((mem_OO_iff _).2 (hb j)))
    | smul c a _ ha => exact fun j => (mem_OO_iff _).1 (mul_mem c.2 ((mem_OO_iff _).2 (ha j)))
  · intro hv
    rw [← Finset.univ_sum_single v]
    refine sum_mem fun i _ => Submodule.subset_span ⟨0, v i, i, τ.shortest_zero, by simpa using hv i, ?_⟩
    funext j
    rw [S.proj_eq_one_of_eq_bot hT, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp

theorem isEE_const_of_eq_one (hth : ∀ x, S.th x = 1) (hev : ∀ x i, S.ev x i = 1) (M : RatModel o Ω)
    (U₀ : M.Z.Opens) : S.IsEE M U₀ (RatModel.Lat.const M S.J) := by
  refine ⟨fun _ _ => rfl, fun z p _ y y₀ τ hc _ => ?_⟩
  have hE := τ.mem_E_iff_of_norm_eq_one
    (fun x => by rw [show (⟨_, S.th_mem x⟩ : S.R) = 1 from Subtype.ext (hth x), map_one, norm_one])
    fun x i => by rw [show (⟨_, S.ev_mem x i⟩ : S.R) = 1 from Subtype.ext (hev x i), map_one, norm_one]
  refine le_antisymm (Submodule.span_le.2 ?_) fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact (hE _).2 fun j => hc.norm_val_le_one ((RatModel.Lat.mem_const_iff M).1 hv j)
  · rw [← Finset.univ_sum_single v]
    refine sum_mem fun i _ => ?_
    have e : (Pi.single i (v i) : S.J → PadicAlgCl p) = (⟨v i, (mem_OO_iff _).2 ((hE v).1 hv i)⟩ : OO p) •
        fun j => M.val (gPt p ≫ y) ((Pi.single i 1 : S.J → Ω) j) := by
      funext j
      rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
      split_ifs
      · rw [RatModel.val_one]
        exact (_root_.mul_one _).symm
      · rw [RatModel.val_zero, smul_zero]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩)

theorem exists_at_of_cen (M : RatModel o Ω) {U₀ : M.Z.Opens} (hle : S.R ≤ M.ringOn U₀) {z : M.Z} {p : ℕ} [Fact p.Prime]
    {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ z y) :
    ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := by
  have hw : S.R ≤ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint _)) :=
    fun x hx => RatModel.mem_ringOn.1 (hle hx) _ (hc.2 ⟨_, rfl⟩)
  exact ⟨(RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ _)).comp (Subalgebra.inclusion hw).toRingHom,
    fun _ => rfl, fun a => hc.norm_val_le_one ((M.O z).algebraMap_mem a)⟩

theorem finite_FF : Set.Finite {x : Ω | ∃ T c k, x = S.FF T c k} :=
  (Set.finite_range fun a : Σ T : AddSubgroup S.Gam, (T →+ ZMod S.N) × S.J × (T → ZMod ((S.r * S.N) ^ 2)) =>
    S.FF a.1 a.2.1 a.2.2).subset fun _ ⟨T, c, k, h⟩ => ⟨⟨T, c, k⟩, h.symm⟩

theorem exists_opens_inv_mem (M : RatModel o Ω) : ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧
    (∀ x, (S.th x)⁻¹ ∈ M.ringOn U) ∧ ∀ T c k, (S.FF T c k)⁻¹ ∈ M.ringOn U := by
  have hfin := (Set.finite_range S.th).union S.finite_FF
  refine ⟨⟨_, hfin.isOpen_biInter fun x _ => M.isOpen_setOf_mem_O x⁻¹⟩, ⟨genericPoint M.Z, ?_⟩,
    fun x => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter₂.1 hz _ (Or.inl ⟨x, rfl⟩),
    fun T c k => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter₂.1 hz _ (Or.inr ⟨T, c, k, rfl⟩)⟩
  exact Set.mem_iInter₂.2 fun x _ => M.O_genericPoint.ge Algebra.mem_top

end ThetaSys

theorem isProjOver_spMap_self (o : Type) [CommRing o] : IsProjOver (spMap (algebraMap o o)) := by
  have hid : spMap (algebraMap o o) = 𝟙 _ := Spec.map_id _
  have h : (spMap (MvPolynomial.eval fun _ => 0) ≫ GlobalTheory.ProjSpace.chartι o 0 0) ≫ PSpace.str o 0 = 𝟙 _ := by
    rw [Category.assoc, GlobalTheory.ProjSpace.chartι_str, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hid]
    exact congrArg (fun φ => spMap φ) (RingHom.ext fun a => MvPolynomial.eval_C a)
  have := isProper_str o 0
  have : IsClosedImmersion ((spMap (MvPolynomial.eval fun _ => 0) ≫ GlobalTheory.ProjSpace.chartι o 0 0) ≫ PSpace.str o 0) := by
    rw [h]
    infer_instance
  exact ⟨0, _, IsClosedImmersion.of_comp _ (PSpace.str o 0), h.trans hid.symm⟩

section Dedekind

variable (o Ω : Type) [CommRing o] [IsDedekindDomain o] [Field Ω] [Algebra o Ω] [IsFractionRing o Ω]

theorem isNormalScheme_ofAffine_self : IsNormalScheme (RatModel.ofAffine o Ω o).Z := fun z =>
  have := RatModel.isIntegrallyClosed_O_ofAffine (o := o) (Ω := Ω) z
  ⟨inferInstance, IsIntegrallyClosed.of_equiv ((RatModel.ofAffine o Ω o).stalkEquiv z).symm⟩

theorem mem_O_or_inv_mem_O (z : PrimeSpectrum o) (x : Ω) :
    x ∈ (RatModel.ofAffine o Ω o).O z ∨ x⁻¹ ∈ (RatModel.ofAffine o Ω o).O z := by
  let V := Localization.subalgebra.ofField Ω z.asIdeal.primeCompl z.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsDedekindDomain V := IsLocalization.isDedekindDomain o z.asIdeal.primeCompl_le_nonZeroDivisors V
  have : IsLocalRing V := IsLocalization.AtPrime.isLocalRing V z.asIdeal
  have : ValuationRing V := inferInstance
  have h : ∀ x : Ω, IsLocalization.IsInteger V x → x ∈ (RatModel.ofAffine o Ω o).O z := by
    rintro _ ⟨⟨_, a, s, hs, rfl⟩, rfl⟩
    exact RatModel.mem_O_ofAffine.2 ⟨a, s, hs, (div_eq_mul_inv _ _).symm⟩
  exact (ValuationRing.isInteger_or_isInteger V x).imp (h _) (h _)

theorem hasDiv_ofAffine_self {J : Type} [Finite J] {t : J → Ω} (ht : t ≠ 0) : (RatModel.ofAffine o Ω o).HasDiv t := by
  intro z
  let V := ValuationSubring.ofSubring ((RatModel.ofAffine o Ω o).O z).toSubring (mem_O_or_inv_mem_O o Ω z)
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 ht
  have : Nonempty J := ⟨j₀⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => V.valuation (t j)
  have hpos : 0 < V.valuation (t i) := ((Valuation.pos_iff _).2 hj₀).trans_le (hi j₀)
  refine ⟨i, (Valuation.pos_iff _).1 hpos, fun j => (V.valuation_le_one_iff _).1 ?_⟩
  rw [map_div₀, div_le_one₀ hpos]
  exact hi j

variable {o Ω}

theorem ThetaSys.exists_adm (S : ThetaSys o Ω) (h : S.R = ⊥) :
    ∃ U₀, S.admitted (RatModel.ofAffine o Ω o) U₀ := by
  obtain ⟨U, hU, h1, h2⟩ := S.exists_opens_inv_mem (RatModel.ofAffine o Ω o)
  exact ⟨U, ⟨isNormalScheme_ofAffine_self o Ω, isProjOver_spMap_self o,
    hasDiv_ofAffine_self o Ω (Function.ne_iff.2 S.th_ne), hU, h.trans_le bot_le, fun x _ => h1 x,
    fun T c k _ _ => h2 T c k⟩, fun _ _ _ h => hasDiv_ofAffine_self o Ω h⟩

theorem exists_cen_ofAffine_self {p : ℕ} [Fact p.Prime] (φ : o →+* PadicAlgCl p) (hφ : ∀ a, ‖φ a‖ ≤ 1)
    (hinj : Function.Injective φ) {U : (RatModel.ofAffine o Ω o).Z.Opens}
    (hU : (U : Set (RatModel.ofAffine o Ω o).Z).Nonempty) :
    ∃ (z : _) (y : Sp (OO p) ⟶ (RatModel.ofAffine o Ω o).Z), (RatModel.ofAffine o Ω o).Cen U z y := by
  let σ : o →+* OO p := φ.codRestrict (OO p).toSubring fun b => (mem_OO_iff _).2 (hφ b)
  refine ⟨_, spMap σ, rfl, ?_⟩
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := hU
  refine Specializes.mem_open ?_ U.isOpen hu
  refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
  have h1 : φ a ∈ w.asIdeal := ha
  rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal w.isPrime, Ideal.mem_bot, map_eq_zero_iff φ hinj] at h1
  exact h1 ▸ zero_mem _

theorem ThetaSys.exists_admissible_isEulerSystem (S : ThetaSys o Ω) (h : S.R = ⊥) (hth : ∀ x, S.th x = 1) (hev : ∀ x i, S.ev x i = 1) :
    ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ ∧ S.IsEE M U₀ EE ∧
      ∀ (p : ℕ) [Fact p.Prime], (∃ φ : o →+* PadicAlgCl p, (∀ a, ‖φ a‖ ≤ 1) ∧ Function.Injective φ) →
        ∃ (z : M.Z) (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p),
          M.Cen U₀ z y ∧ S.At M y y₀ ∧ (∀ a, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀) := by
  obtain ⟨U, hU⟩ := S.exists_adm h
  refine ⟨_, U, _, hU, S.isEE_const_of_eq_one hth hev _ U, fun p _ ⟨φ, hφ, hinj⟩ => ?_⟩
  obtain ⟨z, y, hc⟩ := exists_cen_ofAffine_self φ hφ hinj hU.1.ne
  obtain ⟨y₀, h1, h2⟩ := S.exists_at_of_cen _ hU.1.le hc
  exact ⟨z, y, y₀, hc, h1, h2, S.hasTests_of_eq_one hth hev p y₀ h2⟩

end Dedekind

section Heisenberg

variable {o : Type} [CommRing o] {N : ℕ} [NeZero N] (ψ : AddChar (ZMod N) o)

def heisMat (h u v : ZMod N) : Matrix (ZMod N) (ZMod N) o :=
  Matrix.of fun i j => if j = i + u then ψ (v * (i + h * u)) else 0

theorem heisMat_mul {h : ZMod N} (hh : 2 * h = 1) (u v u' v' : ZMod N) :
    heisMat ψ h u v * heisMat ψ h u' v' = ψ (h * (u * v' - v * u')) • heisMat ψ h (u + u') (v + v') := by
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (i + u) (fun j _ hj => by simp [heisMat, hj]) (by simp)]
  simp only [heisMat, Matrix.of_apply, if_true, Matrix.smul_apply, smul_eq_mul, add_assoc]
  split_ifs
  · rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    linear_combination (-(u * v')) * hh
  · simp

omit [NeZero N] in

theorem heisMat_zero_apply (h v i j : ZMod N) : heisMat ψ h 0 v i j = if j = i then ψ (v * i) else 0 := by
  simp [heisMat]

omit [NeZero N] in

theorem heisMat_zero_zero (h : ZMod N) {u : ZMod N} (v : ZMod N) (hu : u ≠ 0) : heisMat ψ h u v 0 0 = 0 := by
  simp [heisMat, hu.symm]

end Heisenberg

section Inhabitants

variable {o : Type} (Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsFractionRing o Ω]

variable (o) in

theorem exists_eq_div_bot (x : Ω) : ∃ a ∈ (⊥ : Subalgebra o Ω), ∃ b ∈ (⊥ : Subalgebra o Ω), x = a / b := by
  obtain ⟨a, b, -, h⟩ := IsFractionRing.div_surjective o x
  exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, h.symm⟩

variable {r N : ℕ} (hN : 2 ≤ N) (hr : 1 ≤ r) {ζ : o} (hζ : IsPrimitiveRoot ζ ((r * N) ^ 2))
  (hu : IsUnit ((r * N : ℕ) : o))

def pointSys : ThetaSys o Ω where
  g := 0
  N := N
  r := r
  N_ge := hN
  r_pos := hr
  ζ := ζ
  prim := hζ
  unit := hu
  J := Unit
  ρ _ := 1
  ρ_one _ _ := by convert rfl
  ρ_mul _ _ := ⟨0, by simp⟩
  ρ_add _ _ _ := by simp
  th _ := 1
  ev _ _ := 1
  R := ⊥
  fg := Subalgebra.fg_bot
  frac := exists_eq_div_bot o Ω
  th_mem _ := one_mem _
  ev_mem _ _ := one_mem _
  supp := by simp
  th_ne := ⟨0, one_ne_zero⟩

theorem hasTests_pointSys : (pointSys Ω hN hr hζ hu).HasTests :=
  ThetaSys.hasTests_of_eq_one _ (fun _ => rfl) fun _ _ => rfl

variable (hodd : Odd N) (ϖ : o) (hϖ : ϖ ≠ 0)

def heisSys : ThetaSys o Ω :=
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero (r * N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have h1 : (ζ ^ (r ^ 2 * N)) ^ N = 1 := by
    rw [← pow_mul, ← hζ.pow_eq_one]
    congr 1
    ring
  have hh : 2 * ((N / 2 + 1 : ℕ) : ZMod N) = 1 := by
    have : ((2 * (N / 2 + 1) : ℕ) : ZMod N) = ((N + 1 : ℕ) : ZMod N) := by
      congr 1
      have := Nat.odd_iff.1 hodd
      omega
    simpa using this
  { g := 1
    N := N
    r := r
    N_ge := hN
    r_pos := hr
    ζ := ζ
    prim := hζ
    unit := hu
    J := ZMod N
    ρ := fun a => heisMat (AddChar.zmodChar N h1) (N / 2 + 1 : ℕ)
      (ZMod.castHom (dvd_mul_left N r) (ZMod N) (a (.inl 0))) (ZMod.castHom (dvd_mul_left N r) (ZMod N) (a (.inr 0)))
    ρ_one := fun a ha => by
      rw [(nsmul_eq_zero_iff_castHom _).1 (congrFun ha (.inl 0)), (nsmul_eq_zero_iff_castHom _).1 (congrFun ha (.inr 0))]
      ext i j
      simp [heisMat_zero_apply, Matrix.one_apply, eq_comm]
    ρ_mul := fun a b => ⟨_, by
      rw [heisMat_mul _ hh, AddChar.zmodChar_apply, ← pow_mul, Pi.add_apply, Pi.add_apply, map_add, map_add]⟩
    ρ_add := fun a b h => by
      have h2 := (nsmul_eq_zero_iff_castHom _).1 h
      rw [eStd, Fin.sum_univ_one, map_sub, map_mul, map_mul] at h2
      rw [heisMat_mul _ hh, h2, mul_zero, AddChar.map_zero_eq_one, one_smul, Pi.add_apply, Pi.add_apply, map_add,
        map_add]
    th := fun x => algebraMap o Ω (ϖ ^ (x (.inl 0)).valMinAbs.natAbs ^ 2)
    ev := fun _ j => algebraMap o Ω (ϖ ^ (r ^ 2 * N * j.valMinAbs.natAbs ^ 2))
    R := ⊥
    fg := Subalgebra.fg_bot
    frac := exists_eq_div_bot o Ω
    th_mem := fun _ => ⟨_, rfl⟩
    ev_mem := fun _ _ => ⟨_, rfl⟩
    supp := by
      have h : algebraMap o Ω ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o Ω)).2 hϖ
      simp [h]
    th_ne := ⟨0, by simp⟩ }

section HeisTests

variable {p : ℕ} [Fact p.Prime] (y : (heisSys Ω hN hr hζ hu hodd ϖ hϖ).R →+* PadicAlgCl p)

local notation "𝐒" => heisSys Ω hN hr hζ hu hodd ϖ hϖ

theorem norm_th_heisSys (x : (𝐒).Gam) :
    ‖y ⟨(𝐒).th x, (𝐒).th_mem x⟩‖ = ‖y (algebraMap o _ ϖ)‖ ^ (x (.inl (0 : Fin 1))).valMinAbs.natAbs ^ 2 := by
  rw [← norm_pow, ← map_pow, ← map_pow]
  rfl

theorem norm_ev_heisSys (x : (𝐒).Gam) (j : ZMod N) :
    ‖y ⟨(𝐒).ev x j, (𝐒).ev_mem x j⟩‖ = ‖y (algebraMap o _ ϖ)‖ ^ (r ^ 2 * N * j.valMinAbs.natAbs ^ 2) := by
  rw [← norm_pow, ← map_pow, ← map_pow]
  rfl

def heisTestGood (h : ‖y (algebraMap o _ ϖ)‖ = 1) : (𝐒).Test p y :=
  ThetaSys.Test.ofNormOne _ y (fun x => by rw [norm_th_heisSys, h, one_pow])
    fun x i => (norm_ev_heisSys Ω hN hr hζ hu hodd ϖ hϖ y x i).trans (by rw [h, one_pow])

end HeisTests

theorem hasTests_heisSys_one [Nontrivial o] : (heisSys Ω hN hr hζ hu hodd 1 one_ne_zero).HasTests :=
  ThetaSys.hasTests_of_eq_one _ (fun _ => by simp [heisSys]) fun _ _ => by simp [heisSys]

theorem heisSys_ρ_ne_one [Nontrivial o] :
    (heisSys Ω hN hr hζ hu hodd ϖ hϖ).ρ (Pi.single (.inl (0 : Fin 1)) 1) ≠ 1 := fun h => by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  let i : (heisSys Ω hN hr hζ hu hodd ϖ hϖ).J := (0 : ZMod N)
  have h0 := (congrFun (congrFun h i) i).symm.trans (heisMat_zero_zero _ _ _
    fun e => one_ne_zero ((map_one (ZMod.castHom (dvd_mul_left N r) (ZMod N))).symm.trans e))
  exact one_ne_zero ((Matrix.one_apply_eq i).symm.trans h0)

end Inhabitants

section Away

open NumberField

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

abbrev AwayBase : Type := Localization.Away (n : 𝓞 K)

namespace AwayBase

variable [NeZero n]

theorem powers_le : Submonoid.powers (n : 𝓞 K) ≤ nonZeroDivisors _ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 (NeZero.ne n))

theorem injective : Function.Injective (algebraMap (𝓞 K) (AwayBase K n)) :=
  IsLocalization.injective _ (powers_le K n)

instance instIsDomain : IsDomain (AwayBase K n) := IsLocalization.isDomain_localization (powers_le K n)

instance instIsDedekindDomain : IsDedekindDomain (AwayBase K n) :=
  IsLocalization.isDedekindDomain _ (powers_le K n) _

instance instCharZero : CharZero (AwayBase K n) := charZero_of_injective_algebraMap (injective K n)

omit [NeZero n] in

theorem finiteType : Algebra.FiniteType ℤ (AwayBase K n) :=
  Algebra.FiniteType.trans (S := 𝓞 K) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (n : 𝓞 K)) (AwayBase K n))

instance instArithBase : ArithBase (AwayBase K n) (FractionRing (AwayBase K n)) :=
  ⟨inferInstance, by convert finiteType K n using 1 <;> first | rfl | exact Subsingleton.elim _ _, inferInstance,
    IsFractionRing.injective _ _⟩

omit [NumberField K] [NeZero n] in

theorem isUnit_natCast : IsUnit (n : AwayBase K n) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := AwayBase K n) (n : 𝓞 K)
  rwa [map_natCast] at this

theorem exists_isPrimitiveRoot (m : ℕ) [NeZero m] :
    ∃ ζ : AwayBase (CyclotomicField m ℚ) n, IsPrimitiveRoot ζ m :=
  haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) := CyclotomicField.isCyclotomicExtension m ℚ
  ⟨_, (IsCyclotomicExtension.zeta_spec m ℚ (CyclotomicField m ℚ)).toInteger_isPrimitiveRoot.map_of_injective
    (injective _ n)⟩

end AwayBase

theorem norm_natCast_padicAlgCl (p : ℕ) [Fact p.Prime] (m : ℕ) : ‖(m : PadicAlgCl p)‖ = ‖(m : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) m, norm_algebraMap']

theorem norm_natCast_padicAlgCl_of_coprime (p : ℕ) [Fact p.Prime] {m : ℕ} (h : p.Coprime m) :
    ‖(m : PadicAlgCl p)‖ = 1 := by
  rw [norm_natCast_padicAlgCl, Padic.norm_natCast_eq_one_iff.2 h]

theorem AwayBase.exists_point (p : ℕ) [Fact p.Prime] (hp : p.Coprime n) :
    ∃ φ : AwayBase K n →+* PadicAlgCl p, (∀ a, ‖φ a‖ ≤ 1) ∧ Function.Injective φ := by
  have hn := norm_natCast_padicAlgCl_of_coprime p hp
  let σ : K →ₐ[ℚ] PadicAlgCl p := IsAlgClosed.lift
  let ψ : 𝓞 K →+* PadicAlgCl p := σ.toRingHom.comp (algebraMap _ _)
  have hψ : ∀ a, ‖ψ a‖ ≤ 1 := fun a => by
    have h1 : IsIntegral ℤ (ψ a) := (RingOfIntegers.isIntegral a).map ψ.toIntAlgHom
    have h2 : IsIntegral (OO p) (ψ a) := h1.tower_top
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact hb ▸ (mem_OO_iff _).1 b.2
  have hu : IsUnit (ψ n) := by
    rw [map_natCast]
    exact isUnit_iff_ne_zero.2 (norm_pos_iff.1 (hn ▸ one_pos))
  refine ⟨IsLocalization.Away.lift (n : 𝓞 K) hu, fun a => ?_, (injective_iff_map_eq_zero _).2 fun a ha => ?_⟩
  · obtain ⟨k, b, hb⟩ := IsLocalization.Away.surj (n : 𝓞 K) a
    have h := congrArg (fun x => ‖IsLocalization.Away.lift (n : 𝓞 K) hu x‖) hb
    simp only [map_mul, map_pow, IsLocalization.Away.lift_eq, norm_mul, norm_pow] at h
    rw [map_natCast ψ, hn, one_pow, _root_.mul_one] at h
    exact h ▸ hψ b
  · obtain ⟨k, b, hb⟩ := IsLocalization.Away.surj (n : 𝓞 K) a
    have h := congrArg (IsLocalization.Away.lift (n : 𝓞 K) hu) hb
    rw [map_mul, ha, zero_mul, IsLocalization.Away.lift_eq] at h
    have hψi : Function.Injective ψ := σ.toRingHom.injective.comp RingOfIntegers.coe_injective
    rw [(map_eq_zero_iff ψ hψi).1 h.symm, map_zero] at hb
    exact ((IsLocalization.Away.algebraMap_isUnit (n : 𝓞 K)).pow k).mul_left_eq_zero.1 hb

theorem AwayBase.exists_point_bot [NeZero n] (p : ℕ) [Fact p.Prime] (hp : p.Coprime n) :
    ∃ y : (⊥ : Subalgebra (AwayBase K n) (FractionRing (AwayBase K n))) →+* PadicAlgCl p,
      ∀ a, ‖y (algebraMap (AwayBase K n) _ a)‖ ≤ 1 := by
  obtain ⟨φ, hφ, -⟩ := AwayBase.exists_point K n p hp
  exact ⟨φ.comp (Algebra.botEquivOfInjective (IsFractionRing.injective _ _)).toRingEquiv.toRingHom, fun a => hφ _⟩

end Away

theorem exists_thetaSys_dim_zero {r N : ℕ} (hN : 2 ≤ N) (hr : 1 ≤ r) :
    ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω),
      S.g = 0 ∧ S.N = N ∧ S.r = r ∧ S.HasTests ∧
      ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ ∧ S.IsEE M U₀ EE ∧
        ∀ (p : ℕ) [Fact p.Prime], p.Coprime (r * N) →
          ∃ (z : M.Z) (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p),
            M.Cen U₀ z y ∧ S.At M y y₀ ∧ (∀ a, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀) := by
  haveI : NeZero (r * N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨ζ, hζ⟩ := AwayBase.exists_isPrimitiveRoot (r * N) ((r * N) ^ 2)
  let S := pointSys (FractionRing (AwayBase (CyclotomicField ((r * N) ^ 2) ℚ) (r * N))) hN hr hζ
    (AwayBase.isUnit_natCast _ _)
  obtain ⟨M, U, EE, h1, h2, h3⟩ := S.exists_admissible_isEulerSystem rfl (fun _ => rfl) fun _ _ => rfl
  exact ⟨_, _, _, _, _, inferInstance, S, rfl, rfl, rfl, hasTests_pointSys _ _ _ _ _, M, U, EE, h1, h2,
    fun p _ hp => h3 p (AwayBase.exists_point _ _ p hp)⟩

theorem exists_thetaSys_dim_one {r N : ℕ} (hN : 2 ≤ N) (hr : 1 ≤ r) (hodd : Odd N) :
    ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω),
      S.g = 1 ∧ S.N = N ∧ S.r = r ∧ Nat.card S.J = N ∧ (∃ a, S.ρ a ≠ 1) ∧ S.HasTests ∧
      ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ ∧ S.IsEE M U₀ EE ∧
        ∀ (p : ℕ) [Fact p.Prime], p.Coprime (r * N) →
          ∃ (z : M.Z) (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p),
            M.Cen U₀ z y ∧ S.At M y y₀ ∧ (∀ a, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀) := by
  haveI : NeZero (r * N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨ζ, hζ⟩ := AwayBase.exists_isPrimitiveRoot (r * N) ((r * N) ^ 2)
  let S := heisSys (FractionRing (AwayBase (CyclotomicField ((r * N) ^ 2) ℚ) (r * N))) hN hr hζ
    (AwayBase.isUnit_natCast _ _) hodd 1 one_ne_zero
  obtain ⟨M, U, EE, h1, h2, h3⟩ := S.exists_admissible_isEulerSystem rfl (fun _ => by simp [S, heisSys])
    fun _ _ => by simp [S, heisSys]
  exact ⟨_, _, _, _, _, inferInstance, S, rfl, rfl, rfl, Nat.card_zmod N, ⟨_, heisSys_ρ_ne_one _ _ _ _ _ _ _ _⟩,
    hasTests_heisSys_one _ _ _ _ _ _, M, U, EE, h1, h2, fun p _ hp => h3 p (AwayBase.exists_point _ _ p hp)⟩

example : eStd 1 3 (Pi.single (.inl 0) 1) (Pi.single (.inr 0) 1) = 1 := by simp [eStd]

example : eStd 1 3 (Pi.single (.inr 0) 1) (Pi.single (.inl 0) 1) = -1 := by simp [eStd]

end GlobalTheory.ZH
end
