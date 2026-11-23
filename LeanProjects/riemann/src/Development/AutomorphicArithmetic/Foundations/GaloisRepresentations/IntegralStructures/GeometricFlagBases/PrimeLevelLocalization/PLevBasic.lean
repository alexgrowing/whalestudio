import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

theorem mulF_tmul (x : 𝓞 D.F) (a : AfP p) (y : D.La) :
    mulF D x (a ⊗ₜ ((1 : ℚ) ⊗ₜ y)) = a ⊗ₜ ((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O x • y)) := rfl

theorem mulF_mem (x : 𝓞 D.F) {v} (hv : v ∈ LaHat D) : mulF D x v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, y, ha, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a, _, ha, mulF_tmul x a y⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem end_ext {f g : AfP p ⊗[ℚ] VQ D →+ AfP p ⊗[ℚ] VQ D}
    (h : ∀ (a : AfP p) (r : ℚ) (y : D.La), f (a ⊗ₜ (r ⊗ₜ y)) = g (a ⊗ₜ (r ⊗ₜ y))) (v) : f v = g v := by
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a z =>
    induction z using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add b c hb hc => rw [TensorProduct.tmul_add, map_add, map_add, hb, hc]
    | tmul r y => exact h a r y

theorem mulF_nat_mul (N : ℕ) (x : 𝓞 D.F) (v) : mulF D ((N : 𝓞 D.F) * x) v = N • mulF D x v := by
  refine end_ext (f := (mulF D ((N : 𝓞 D.F) * x)).toAddMonoidHom) (g := (N • mulF D x).toAddMonoidHom) (fun a r y => ?_) v
  show a ⊗ₜ[ℚ] (r ⊗ₜ[ℤ] (algebraMap (𝓞 D.F) D.O ((N : 𝓞 D.F) * x) • y)) = N • a ⊗ₜ[ℚ] (r ⊗ₜ[ℤ] (algebraMap (𝓞 D.F) D.O x • y))
  rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
  exact (map_nsmul ((TensorProduct.mk ℚ _ _ a).toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ D.La r).toAddMonoidHom) N _)

theorem mulF_one (v) : mulF D 1 v = v := by
  refine end_ext (f := (mulF D 1).toAddMonoidHom) (g := AddMonoidHom.id _) (fun a r y => ?_) v
  show a ⊗ₜ[ℚ] (r ⊗ₜ[ℤ] (algebraMap (𝓞 D.F) D.O 1 • y)) = a ⊗ₜ[ℚ] (r ⊗ₜ[ℤ] y)
  rw [map_one, one_smul]

theorem actG_mulF (g : G.GAf) (x : 𝓞 D.F) (v) : L.actG g (mulF D x v) = mulF D x (L.actG g v) := by
  have key : ∀ c : AfP p ⊗[ℚ] G.C, actOn L.rep (AfP p) c * mulF D x = mulF D x * actOn L.rep (AfP p) c := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]
    | tmul a y =>
      have h := (L.rep_range (L.rep y)).1 ⟨y, rfl⟩ (algebraMap (𝓞 D.F) D.O x)
      have h2 : (L.rep y).baseChange (AfP p) * mulF D x = mulF D x * (L.rep y).baseChange (AfP p) := by
        unfold mulF
        rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h]
      have h3 : actOn L.rep (AfP p) (a ⊗ₜ y) = a • (L.rep y).baseChange (AfP p) := by
        rw [Algebra.smul_def]
        rfl
      rw [h3, smul_mul_assoc, mul_smul_comm, h2]
  exact LinearMap.congr_fun (key _) v

theorem mem_idHat_nat (N : ℕ) (z) : z ∈ idHat D (Ideal.span {(N : 𝓞 D.F)}) ↔ ∃ w ∈ LaHat D, z = N • w := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨x, hx, v, hv, rfl⟩ := hz
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 hx
      exact ⟨_, mulF_mem y hv, mulF_nat_mul N y v⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, rfl⟩ := ha
      obtain ⟨u', hu', rfl⟩ := hb
      exact ⟨u + u', add_mem hu hu', by rw [smul_add]⟩
    | neg a _ ha =>
      obtain ⟨u, hu, rfl⟩ := ha
      exact ⟨-u, neg_mem hu, by rw [smul_neg]⟩
  · rintro ⟨w, hw, rfl⟩
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.F) * 1, Ideal.mem_span_singleton.2 ⟨1, rfl⟩, w, hw, ?_⟩
    rw [mulF_nat_mul, mulF_one]

theorem Integ_idHat {g : G.GAf} (hg : Integ L g) {𝔟 : Ideal (𝓞 D.F)} {z} (hz : z ∈ idHat D 𝔟) : L.actG g z ∈ idHat D 𝔟 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, hv, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨x, hx, _, hg v hv, actG_mulF L g x v⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem actG_mul (g h : G.GAf) (v) : L.actG (g * h) v = L.actG g (L.actG h v) := by
  rw [map_mul, Module.End.mul_apply]

theorem actG_inv_act (g : G.GAf) (v) : L.actG g⁻¹ (L.actG g v) = v := by
  rw [← actG_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem actG_act_inv (g : G.GAf) (v) : L.actG g (L.actG g⁻¹ v) = v := by
  rw [← actG_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem CongId.inv {𝔟 : Ideal (𝓞 D.F)} {g : G.GAf} (hg : Integ L g⁻¹) (h : CongId L 𝔟 g) : CongId L 𝔟 g⁻¹ := fun v hv => by
  have := neg_mem (h _ (hg v hv))
  rwa [actG_act_inv, neg_sub] at this

theorem congOne_iff (N : ℕ) (g : G.GAf) : L.CongOne N g ↔ CongId L (Ideal.span {(N : 𝓞 D.F)}) g := by
  refine forall₂_congr fun v hv => ?_
  rw [mem_idHat_nat]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [sub_eq_iff_eq_add']

theorem congOne_conj {N c : ℕ} {h u : G.GAf} (hh : Integ L h) (hb : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = c • v) (hc : 0 < c)
    (hu : L.CongOne (N * c) u) : L.CongOne N (h * u * h⁻¹) := fun v hv => by
  obtain ⟨v', hv', e⟩ := hb v hv
  obtain ⟨w, hw, e'⟩ := hu v' hv'
  refine ⟨_, hh w hw, ?_⟩
  have e1 : v' = c • L.actG h⁻¹ v := by rw [← map_nsmul, ← e, actG_inv_act]
  have e2 : c • L.actG (h * u * h⁻¹) v = c • (v + N • L.actG h w) := by
    rw [actG_mul, actG_mul, ← map_nsmul, ← map_nsmul, ← e1, e', map_add, e, map_nsmul, smul_add, smul_smul, mul_comm]
  rw [← Nat.cast_smul_eq_nsmul ℚ c, ← Nat.cast_smul_eq_nsmul ℚ c] at e2
  exact smul_right_injective _ (by exact_mod_cast hc.ne') e2

end

theorem levBasic_holds : LevBasic := by
  intro p _ D G L
  refine ⟨fun 𝔟 => ⟨⟨⟨⟨{g | g ∈ L.KN 1 ∧ CongId L 𝔟 g}, ?_⟩, one_mem _, fun v _ => by simp⟩, ?_⟩, fun _ => Iff.rfl⟩,
    fun 𝔟 𝔟' K K' h h' hle g hg => ?_, fun N g => ⟨fun hg => ⟨KN_anti (one_dvd N) hg, (congOne_iff L N g).1 hg.1⟩, fun hg => ?_⟩,
    congOne_iff L, fun 𝔟 K h k hk u hu => ?_, fun N c h hh hb hc u hu => ⟨congOne_conj L hh hb hc hu.1, ?_⟩⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun v hv => ?_⟩
    have := add_mem (ha' _ (integ_of_mem hb v hv)) (hb' v hv)
    rwa [sub_add_sub_cancel, ← actG_mul] at this
  · rintro a ⟨ha, ha'⟩
    exact ⟨inv_mem ha, CongId.inv L (integ_of_mem (inv_mem ha)) ha'⟩
  · obtain ⟨h1, h2⟩ := (h g).1 hg
    refine (h' g).2 ⟨h1, fun v hv => AddSubgroup.closure_mono ?_ (h2 v hv)⟩
    rintro z ⟨x, hx, r⟩
    exact ⟨x, hle hx, r⟩
  · exact ⟨(congOne_iff L N g).2 hg.2, (congOne_iff L N _).2 (CongId.inv L (integ_of_mem (inv_mem hg.1)) hg.2)⟩
  · obtain ⟨h1, h2⟩ := (h u).1 hu
    refine (h _).2 ⟨mul_mem (mul_mem hk h1) (inv_mem hk), fun v hv => ?_⟩
    have := Integ_idHat L (integ_of_mem hk) (h2 _ (integ_of_mem (inv_mem hk) v hv))
    rwa [map_sub, actG_act_inv, ← actG_mul, ← actG_mul] at this
  · have := congOne_conj L hh hb hc hu.2
    rwa [show h * u⁻¹ * h⁻¹ = (h * u * h⁻¹)⁻¹ by group] at this

end UpperTheory.Gal.Int.Geo.Pl
