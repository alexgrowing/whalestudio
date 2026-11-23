import Mathlib
import GroundTheory.PAdicHodge.WAFracAnnCris
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

variable {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0}

section Res

variable {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) ≤ ρ0)
  (hs : (σ0 : ℝ) ≤ σ1) (hσ : (p : ℝ)⁻¹ ≤ σ0)

theorem annRes_awayToAnn (z : 𝔸) :
    (𝓣).annRes h hs (awayToAnn ρ0 σ0 z) = awayToAnn ρ1 σ1 z := by
  rw [awayToAnn, RingHom.comp_apply, (𝓣).annRes_coeAnn]
  rfl

theorem annRes_acrisToAnn (a : ACris ℂ_[p] p) :
    (𝓣).annRes h hs (acrisToAnn hσ a) = acrisToAnn (hσ.trans hs) a := by
  refine eq_acrisToAnn (hσ.trans hs) fun N => ⟨acrisApprox a N, acrisApprox_spec a N, fun r => ?_⟩
  rw [← annRes_awayToAnn h hs, ← map_sub, (𝓣).annNorm_annRes]
  exact (annNorm_acrisToAnn_sub_le hσ a (acrisApprox_spec a N) _).trans
    (pow_le_pow_left₀ (rad_pos' r).le r.2.2 N)

set_option maxHeartbeats 1600000 in
theorem annRes_bcrisToAnn (b : BCrisPlus ℂ_[p] p) :
    (𝓣).annRes h hs (bcrisToAnn hσ b) = bcrisToAnn (hσ.trans hs) b := by
  have e : ((𝓣).annRes h hs).comp (bcrisToAnn hσ) = bcrisToAnn (hσ.trans hs) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, bcrisToAnn_algebraMap, annRes_acrisToAnn])
  exact congrArg (fun f : BCrisPlus ℂ_[p] p →+* (𝓣).Ann ρ1 σ1 => f b) e

end Res

section Galois

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (hσ : (p : ℝ)⁻¹ ≤ σ0)

theorem annMap_awayToAnn (σ : Gal(PadicAlgCl p/K)) (z : 𝔸) :
    (galIso σ).annMap (awayToAnn ρ0 σ0 z) = awayToAnn ρ0 σ0 (ACris.galAway σ z) := by
  rw [awayToAnn, RingHom.comp_apply, TeichLift.TeichIso.annMap_coeAnn, RingHom.comp_apply]
  congr 1
  exact Subtype.ext (toB_galAway σ z).symm

set_option maxHeartbeats 1600000 in
theorem galCris_sub_mem {a : ACris ℂ_[p] p} {c : ACrisZero ℂ_[p] p} {N : ℕ} (σ : Gal(PadicAlgCl p/K))
    (hc : a - algebraMap _ (ACris ℂ_[p] p) c ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N}) :
    galCris σ a - algebraMap _ (ACris ℂ_[p] p) (σ • c) ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hc
  refine Ideal.mem_span_singleton'.2 ⟨galCris σ d, ?_⟩
  have e : algebraMap _ (ACris ℂ_[p] p) (σ • c) = galCris σ (algebraMap _ (ACris ℂ_[p] p) c) := by
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply, galCris_of]
  rw [e, ← map_sub, ← hd, map_mul, map_pow, map_natCast]

set_option maxHeartbeats 1600000 in
theorem annMap_acrisToAnn (σ : Gal(PadicAlgCl p/K)) (a : ACris ℂ_[p] p) :
    (galIso σ).annMap (acrisToAnn hσ a) = acrisToAnn hσ (galCris σ a) := by
  refine eq_acrisToAnn hσ fun N => ⟨σ • acrisApprox a N, galCris_sub_mem σ (acrisApprox_spec a N),
    fun r => ?_⟩
  rw [coe_gal_smul_zero, ← annMap_awayToAnn, ← map_sub, TeichLift.TeichIso.annNorm_annMap]
  exact (annNorm_acrisToAnn_sub_le hσ a (acrisApprox_spec a N) r).trans
    (pow_le_pow_left₀ (rad_pos' r).le r.2.2 N)

set_option maxHeartbeats 1600000 in
theorem annMap_bcrisToAnn (σ : Gal(PadicAlgCl p/K)) (b : BCrisPlus ℂ_[p] p) :
    (galIso σ).annMap (bcrisToAnn hσ b) = bcrisToAnn hσ (galPlus σ b) := by
  have e : ((galIso σ).annMap).comp (bcrisToAnn hσ) = (bcrisToAnn hσ).comp (galPlus σ) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, bcrisToAnn_algebraMap, galPlus_algebraMap, annMap_acrisToAnn])
  exact congrArg (fun f : BCrisPlus ℂ_[p] p →+* (𝓣).Ann ρ0 σ0 => f b) e

end Galois

section Frob

variable {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1}
  (h : (ρ1 : ℝ) ≤ (frob ℂ_[p] p).powRadius ρ0) (hs : (((frob ℂ_[p] p).powRad σ0 :
    Set.Ioc (0 : ℝ) ((frob ℂ_[p] p).powRadius ρ0)) : ℝ) ≤ σ1)
  (hσ : (p : ℝ)⁻¹ ≤ σ0) (hσ1 : (p : ℝ)⁻¹ ≤ σ1)

omit h hs hσ hσ1 in
set_option maxHeartbeats 1600000 in
theorem annFrob_awayToAnn (z : 𝔸) :
    (frob ℂ_[p] p).annFrob (awayToAnn ρ0 σ0 z) =
      awayToAnn ((frob ℂ_[p] p).powRadius ρ0) ((frob ℂ_[p] p).powRad σ0) (phiAway ℂ_[p] p z) := by
  rw [awayToAnn, RingHom.comp_apply, TeichLift.TeichFrob.annFrob_coeAnn, awayToAnn, RingHom.comp_apply]
  congr 1
  exact Subtype.ext (WAPeriodT.toB_phiAway z).symm

omit h hs hσ hσ1 in
set_option maxHeartbeats 1600000 in
theorem phi_sub_mem {a : ACris ℂ_[p] p} {c : ACrisZero ℂ_[p] p} {N : ℕ}
    (hc : a - algebraMap _ (ACris ℂ_[p] p) c ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N}) :
    phi ℂ_[p] p a - algebraMap _ (ACris ℂ_[p] p) (phiZero ℂ_[p] p c) ∈
      Ideal.span {(p : ACris ℂ_[p] p) ^ N} := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hc
  refine Ideal.mem_span_singleton'.2 ⟨phi ℂ_[p] p d, ?_⟩
  have e : algebraMap _ (ACris ℂ_[p] p) (phiZero ℂ_[p] p c) = phi ℂ_[p] p (algebraMap _ (ACris ℂ_[p] p) c) := by
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply, phi_of]
  rw [e, ← map_sub, ← hd, map_mul, map_pow, map_natCast]

omit hσ hσ1 in
include h hs in
theorem rad_rpow_mem (r : AnnRad ρ1 σ1) :
    (r : ℝ) ^ ((p : ℝ)⁻¹) ∈ Set.Icc (σ0 : ℝ) ρ0 := by
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hp.out.pos)
  have hr0 : (0 : ℝ) ≤ r := (σ1.2.1.trans_le r.2.1).le
  have e1 : (((σ0 : ℝ) ^ p) ^ ((p : ℝ)⁻¹)) = σ0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul σ0.2.1.le, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp.out.ne_zero),
      Real.rpow_one]
  have e2 : (((ρ0 : ℝ) ^ p) ^ ((p : ℝ)⁻¹)) = ρ0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ρ0.2.1.le, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp.out.ne_zero),
      Real.rpow_one]
  have h1 : (σ0 : ℝ) ^ p ≤ r := by
    have := hs.trans r.2.1
    simpa [TeichLift.TeichFrob.coe_powRad] using this
  have h2 : (r : ℝ) ≤ (ρ0 : ℝ) ^ p := by
    have := r.2.2.trans h
    simpa [TeichLift.TeichFrob.powRadius] using this
  constructor
  · rw [← e1]; exact Real.rpow_le_rpow (pow_nonneg σ0.2.1.le p) h1 hp0.le
  · rw [← e2]; exact Real.rpow_le_rpow hr0 h2 hp0.le

omit hσ hσ1 in
theorem annRadOf_eq_annPowRad (r : AnnRad ρ1 σ1) :
    annRadOf h hs r = (frob ℂ_[p] p).annPowRad (⟨(r : ℝ) ^ ((p : ℝ)⁻¹), rad_rpow_mem h hs r⟩ : AnnRad ρ0 σ0) := by
  apply Subtype.ext
  rw [coe_annRadOf, TeichLift.TeichFrob.coe_annPowRad, frob_a, pow_one]
  exact (Real.rpow_inv_natCast_pow (σ1.2.1.trans_le r.2.1).le hp.out.ne_zero).symm

set_option maxHeartbeats 1600000 in

theorem annRes_annFrob_acrisToAnn (a : ACris ℂ_[p] p) :
    (𝓣).annRes h hs ((frob ℂ_[p] p).annFrob (acrisToAnn hσ a)) = acrisToAnn hσ1 (phi ℂ_[p] p a) := by
  refine eq_acrisToAnn hσ1 fun N => ⟨phiZero ℂ_[p] p (acrisApprox a N), phi_sub_mem (acrisApprox_spec a N),
    fun r => ?_⟩
  rw [coe_phiZero, ← annRes_awayToAnn h hs, ← annFrob_awayToAnn, ← map_sub, ← map_sub,
    (𝓣).annNorm_annRes, annRadOf_eq_annPowRad h hs, TeichLift.TeichFrob.annNorm_annFrob, frob_a, pow_one]
  set s : AnnRad ρ0 σ0 := ⟨(r : ℝ) ^ ((p : ℝ)⁻¹), rad_rpow_mem h hs r⟩
  have h1 := annNorm_acrisToAnn_sub_le hσ a (acrisApprox_spec a N) s
  have hs0 : (0 : ℝ) ≤ s := (rad_pos' s).le
  calc (𝓣).annNorm ρ0 σ0 s (acrisToAnn hσ a - awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸)) ^ p
      ≤ ((s : ℝ) ^ N) ^ p := pow_le_pow_left₀ ((𝓣).annNorm_nonneg _ _) h1 p
    _ = (r : ℝ) ^ N := by
        rw [← pow_mul, mul_comm, pow_mul]
        congr 1
        exact Real.rpow_inv_natCast_pow (σ1.2.1.trans_le r.2.1).le hp.out.ne_zero
    _ ≤ (ρ1 : ℝ) ^ N := pow_le_pow_left₀ (rad_pos' r).le r.2.2 N

end Frob

section Pos

variable (hσ : (p : ℝ)⁻¹ ≤ σ0)

def radInvP : Set.Ioc (0 : ℝ) ρ0 := ⟨(p : ℝ)⁻¹, inv_pos.2 (Nat.cast_pos.2 hp.out.pos), hσ.trans σ0.2.2⟩

theorem coe_radInvP : ((radInvP hσ : Set.Ioc (0 : ℝ) ρ0) : ℝ) = (p : ℝ)⁻¹ := rfl

theorem radInvP_le : ((radInvP hσ : Set.Ioc (0 : ℝ) ρ0) : ℝ) ≤ σ0 := by rw [coe_radInvP]; exact hσ

theorem annNorm_acrisToAnn_pos_big {a : ACris ℂ_[p] p} (ha : a ≠ 0) :
    0 < (𝓣).annNorm ρ0 (radInvP hσ) (annIn ρ0 (radInvP hσ)) (acrisToAnn (le_refl _) a) := by
  obtain ⟨B, N₀, hB, hbound⟩ := exists_lower_bound (K := ℂ_[p]) ha
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt)
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hp.out.pos)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hB hp1
  set N := max N₀ n
  have hpN : ((p : ℝ)⁻¹) ^ N < B :=
    (pow_le_pow_of_le_one hp0.le hp1.le (le_max_right _ _)).trans_lt hn
  set c := acrisApprox a N
  have h1 : B < gn ℂ_[p] p ‖(p : ℂ_[p])‖ (c : 𝔸) := hbound N (le_max_left _ _) c (acrisApprox_spec a N)
  rw [norm_natCast_p] at h1
  have h2 := annNorm_acrisToAnn_sub_le (le_refl ((radInvP hσ : Set.Ioc (0 : ℝ) ρ0) : ℝ)) a
    (acrisApprox_spec a N) (annIn ρ0 (radInvP hσ))
  have h3 : (𝓣).annNorm ρ0 (radInvP hσ) (annIn ρ0 (radInvP hσ)) (awayToAnn ρ0 (radInvP hσ) (c : 𝔸)) =
      gn ℂ_[p] p (p : ℝ)⁻¹ (c : 𝔸) := annNorm_awayToAnn _ _
  have h4 := (𝓣).annNorm_sub_le (annIn ρ0 (radInvP hσ)) (acrisToAnn (le_refl _) a)
    (acrisToAnn (le_refl _) a - awayToAnn ρ0 (radInvP hσ) (c : 𝔸))
  rw [sub_sub_cancel, h3] at h4
  have h2' : (𝓣).annNorm ρ0 (radInvP hσ) (annIn ρ0 (radInvP hσ))
      (acrisToAnn (le_refl _) a - awayToAnn ρ0 (radInvP hσ) (c : 𝔸)) < B := h2.trans_lt hpN
  rcases le_max_iff.1 h4 with h | h
  · linarith
  · linarith

theorem annNorm_acrisToAnn_pos {a : ACris ℂ_[p] p} (ha : a ≠ 0) (r : AnnRad ρ0 σ0) :
    0 < (𝓣).annNorm ρ0 σ0 r (acrisToAnn hσ a) := by
  have hbig := (𝓣).annNorm_pos_of_annIn_pos (annNorm_acrisToAnn_pos_big hσ ha)
    (annRadOf (le_refl (ρ0 : ℝ)) (radInvP_le hσ) r)
  have hres := annRes_acrisToAnn (le_refl (ρ0 : ℝ)) (radInvP_le hσ) (le_refl _) a
  have hn := (𝓣).annNorm_annRes (le_refl (ρ0 : ℝ)) (radInvP_le hσ) r (acrisToAnn (le_refl _) a)
  rw [hres] at hn
  rw [← hn] at hbig
  exact hbig

theorem annNorm_bcrisToAnn_pos {b : BCrisPlus ℂ_[p] p} (hb : b ≠ 0) (r : AnnRad ρ0 σ0) :
    0 < (𝓣).annNorm ρ0 σ0 r (bcrisToAnn hσ b) := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hab⟩ := IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) b
  simp only at hab
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    have hu : IsUnit (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) ((p : ACris ℂ_[p] p) ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (p : ACris ℂ_[p] p)).pow n
    exact hb (hu.mul_left_eq_zero.1 hab)
  have e := congrArg (fun x => (𝓣).annNorm ρ0 σ0 r (bcrisToAnn hσ x)) hab
  simp only [map_mul, bcrisToAnn_algebraMap, map_pow, map_natCast, (𝓣).annNorm_mul, (𝓣).annNorm_pow,
    annNorm_awayToAnn_natCast_p] at e
  have hpos := annNorm_acrisToAnn_pos hσ ha r
  rw [← e] at hpos
  exact pos_of_mul_pos_left hpos (pow_nonneg (rad_pos' r).le n)

theorem bcrisToAnn_injective : Function.Injective (bcrisToAnn (ρ0 := ρ0) (σ0 := σ0) hσ) := by
  intro x y hxy
  by_contra hne
  have := annNorm_bcrisToAnn_pos hσ (sub_ne_zero.2 hne) (annIn ρ0 σ0)
  rw [map_sub, hxy, sub_self, (𝓣).annNorm_zero] at this
  exact lt_irrefl _ this

end Pos

end WAFrac

end GroundTheory.PAdicHodge
