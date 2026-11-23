import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HTLieRho

open GlobalTheory.Serre

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

theorem omega_quad (D : GlobalTheory.UPel.HT.Datum p) :
    D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
  rw [← D.tr_eq, ← D.nm_eq]; ring

theorem two_rho_sub_ne_zero (b : GlobalTheory.UPel.HT.Base D R) (β : R →+* k) :
    β b.ρ - ((D.tr : k) - β b.ρ) ≠ 0 := by
  have hcop : (Int.natAbs (D.tr ^ 2 - 4 * D.nm)).Coprime p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 fun h => D.disc_p ?_)
    exact Int.natCast_dvd.2 h
  have hu : IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
    have := b.unit _ hcop
    rcases Int.natAbs_eq (D.tr ^ 2 - 4 * D.nm) with e | e
    · rw [e]; simpa using this
    · rw [e]; simpa using this.neg
  have hk : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) ≠ 0 := by
    have := hu.map β
    rw [map_intCast] at this
    exact this.ne_zero
  have hr := congrArg β b.ρ_root
  simp only [map_add, map_sub, map_pow, map_mul, map_intCast, map_zero] at hr
  intro h0
  apply hk
  have : (β b.ρ - ((D.tr : k) - β b.ρ)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) := by
    push_cast; linear_combination 4 * hr
  rw [← this, h0]; ring

theorem nm_eq_mul (b : GlobalTheory.UPel.HT.Base D R) (β : R →+* k) :
    (D.nm : k) = β b.ρ * ((D.tr : k) - β b.ρ) := by
  have hr := congrArg β b.ρ_root
  simp only [map_add, map_sub, map_pow, map_mul, map_intCast, map_zero] at hr
  linear_combination hr

theorem exists_sep (b : GlobalTheory.UPel.HT.Base D R) (β : R →+* k) {i j : Fin D.a} (hij : i ≠ j) :
    ∃ c : 𝓞 D.F, β (b.t i c) ≠ β (b.t j c) := by
  by_contra h
  push_neg at h
  have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker β := by
    rw [Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    simp [RingHom.mem_ker, map_sub, h x]
  rw [b.comax i j hij, top_le_iff] at hle
  have h1 : (1 : R) ∈ RingHom.ker β := by rw [hle]; trivial
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

variable {b : GlobalTheory.UPel.HT.Base D R}

def eigOm (o₀ : GlobalTheory.UPel.HT.Obj b N t) (l : k) : Submodule k (Lie (o₀.act.toF D)) where
  carrier := {v | D.ω • v = l • v}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_setOf_eq] at *
    rw [smul_add, smul_add, hv, hw]
  zero_mem' := by simp
  smul_mem' r v hv := by
    simp only [Set.mem_setOf_eq] at *
    rw [smul_comm D.ω r v, hv, smul_comm r l v]

theorem mem_eigOm (o₀ : GlobalTheory.UPel.HT.Obj b N t) (l : k) (v : Lie (o₀.act.toF D)) :
    v ∈ eigOm o₀ l ↔ D.ω • v = l • v := Iff.rfl

theorem toLie_crys (o₀ : GlobalTheory.UPel.HT.Obj b N t) (HL : LieExact o₀.A) (c : 𝓞 D.F) (h : HdR o₀.A) :
    HL.toLie (o₀.act.toF D) (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O c) h) =
      c • HL.toLie (o₀.act.toF D) h :=
  HL.toLie_act _ c h

theorem toLie_crys' (o₀ : GlobalTheory.UPel.HT.Obj b N t) (HL : LieExact o₀.A) (c : 𝓞 D.F) (h : HdR o₀.A) :
    HL.toLie (o₀.act.toF D) (GlobalTheory.HTSummand.crysAct (dp0 k) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) h) =
      c • HL.toLie (o₀.act.toF D) h :=
  HL.toLie_act _ c h

theorem quad_lie (o₀ : GlobalTheory.UPel.HT.Obj b N t) (v : Lie (o₀.act.toF D)) :
    D.ω • D.ω • v - (D.tr : k) • D.ω • v + (D.nm : k) • v = 0 := by
  have := congrArg (· • v) (omega_quad D)
  simp only [zero_smul, add_smul, sub_smul, mul_smul] at this
  simp only [Int.cast_smul_eq_zsmul] at this ⊢
  exact this

end GlobalTheory.HTLieRho

namespace GlobalTheory.HTLieRho
open GlobalTheory.Serre
variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

theorem lie_rho_decomp (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) (ht : t = spMap β) (HL : LieExact o₀.A)
    (v : Lie (o₀.act.toF D)) (hv : D.ω • v = β b.ρ • v) :
    ∃ w : Fin D.a → Lie (o₀.act.toF D), (∀ j, w j ∈ Lie.eig (o₀.act.toF D) (β.comp (b.t j))) ∧
      v = ∑ j, w j := by
  obtain ⟨y, rfl⟩ := HL.toLie_surjective (o₀.act.toF D) v
  have hy : GlobalTheory.HTSummand.crysAct (dp0 k) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A := by
    rw [← HL.ker_toLie (o₀.act.toF D), LinearMap.mem_ker, map_sub, map_smul, toLie_crys', hv, sub_self]
  obtain ⟨w, hw, hs⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N k β t ht o₀ y hy
  refine ⟨fun j => HL.toLie (o₀.act.toF D) (w j), fun j => ?_, ?_⟩
  · rw [Lie.mem_eig_iff]
    intro c
    have := hw j c
    rw [← HL.ker_toLie (o₀.act.toF D), LinearMap.mem_ker, map_sub, map_smul, toLie_crys', sub_eq_zero] at this
    exact this
  · rw [← HL.ker_toLie (o₀.act.toF D), LinearMap.mem_ker, map_sub, map_sum, sub_eq_zero] at hs
    exact hs

theorem lie_decomp (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) (ht : t = spMap β) (HL : LieExact o₀.A)
    (v : Lie (o₀.act.toF D)) :
    ∃ u, D.ω • u = ((D.tr : k) - β b.ρ) • u ∧ ∃ w : Fin D.a → Lie (o₀.act.toF D),
      (∀ j, w j ∈ Lie.eig (o₀.act.toF D) (β.comp (b.t j))) ∧ v = u + ∑ j, w j := by
  have hd := two_rho_sub_ne_zero (D := D) b β
  set ρ := β b.ρ with hρ
  set ρ' := (D.tr : k) - ρ with hρ'
  set e := (ρ - ρ')⁻¹ with he'
  have he : e * (ρ - ρ') = 1 := inv_mul_cancel₀ hd
  have q := quad_lie o₀ v
  rw [nm_eq_mul b β] at q
  have hsplit : v = -(e • (D.ω • v - ρ • v)) + e • (D.ω • v - ρ' • v) := by
    rw [← sub_eq_neg_add, ← smul_sub, sub_sub_sub_cancel_left, ← sub_smul, smul_smul, he, one_smul]
  have hvr : D.ω • (e • (D.ω • v - ρ' • v)) = ρ • (e • (D.ω • v - ρ' • v)) := by
    rw [smul_comm D.ω e, smul_sub, smul_comm D.ω ρ']
    generalize D.ω • D.ω • v = Y at q ⊢
    generalize D.ω • v = X at q ⊢
    linear_combination (norm := module) e • q
  obtain ⟨w, hw, hs⟩ := lie_rho_decomp o₀ β ht HL _ hvr
  refine ⟨-(e • (D.ω • v - ρ • v)), ?_, w, hw, ?_⟩
  · rw [smul_neg, smul_comm D.ω e, smul_sub, smul_comm D.ω ρ]
    generalize D.ω • D.ω • v = Y at q ⊢
    generalize D.ω • v = X at q ⊢
    linear_combination (norm := module) (-e) • q
  · rw [← hs]; exact hsplit

theorem lift_rhobar (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) (HL : LieExact o₀.A)
    (u : Lie (o₀.act.toF D)) (hu : D.ω • u = ((D.tr : k) - β b.ρ) • u) :
    ∃ h, HL.toLie (o₀.act.toF D) ((GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) h) = u := by
  have hd := two_rho_sub_ne_zero (D := D) b β
  have hne : (D.tr : k) - β b.ρ - β b.ρ ≠ 0 := fun h => hd (by linear_combination -h)
  obtain ⟨h, hh⟩ := HL.toLie_surjective (o₀.act.toF D) (((D.tr : k) - β b.ρ - β b.ρ)⁻¹ • u)
  refine ⟨h, ?_⟩
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, toLie_crys, hh,
    smul_comm D.ω, hu, smul_smul, smul_smul, ← sub_smul]
  rw [show ((D.tr : k) - β b.ρ - β b.ρ)⁻¹ * ((D.tr : k) - β b.ρ) - β b.ρ * ((D.tr : k) - β b.ρ - β b.ρ)⁻¹ = 1 by
    rw [mul_comm (β b.ρ), ← mul_sub, inv_mul_cancel₀ hne], one_smul]

theorem mem_G_of (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) (HL : LieExact o₀.A) {z h : HdR o₀.A}
    (e : HL.toLie (o₀.act.toF D) z =
      HL.toLie (o₀.act.toF D) ((GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) h)) :
    z ∈ Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) := by
  have h1 : z - (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) h ∈ Fil o₀.A := by
    rw [← HL.ker_toLie (o₀.act.toF D), LinearMap.mem_ker, map_sub, e, sub_self]
  have := Submodule.add_mem_sup h1 (LinearMap.mem_range_self (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) h)
  rwa [sub_add_cancel] at this

end GlobalTheory.HTLieRho

namespace GlobalTheory.HTLieRho
open GlobalTheory.Serre
variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

theorem mem_G_of_rhobar (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) (HL : LieExact o₀.A) {z : HdR o₀.A}
    (hz : D.ω • HL.toLie (o₀.act.toF D) z = ((D.tr : k) - β b.ρ) • HL.toLie (o₀.act.toF D) z) :
    z ∈ Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) := by
  obtain ⟨h, hh⟩ := lift_rhobar o₀ β HL _ hz
  exact mem_G_of o₀ β HL hh.symm

theorem jSub_le (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) (ht : t = spMap β) (HL : LieExact o₀.A) :
    GlobalTheory.HTRho.jSub (GlobalTheory.HTCount.crysAct o₀) (fun i => β.comp (b.t i)) ⊤ ≤
      Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) := by
  rw [GlobalTheory.HTRho.jSub, Submodule.span_le]
  rintro _ ⟨r, lam, c, x, -, hc, rfl⟩
  have hc' : ∀ j, ∑ l, lam l * β (b.t j (c l)) = 0 := fun j => by simpa using hc j
  obtain ⟨u, hu, w, hw, hs⟩ := lie_decomp o₀ β ht HL (HL.toLie (o₀.act.toF D) x)
  have hT : HL.toLie (o₀.act.toF D) (∑ l, lam l • GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) x) =
      ∑ l, lam l • c l • u := by
    have h2 : ∑ l, lam l • ∑ j, β (b.t j (c l)) • w j = 0 := by
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hc', zero_smul, Finset.sum_const_zero]
    calc HL.toLie (o₀.act.toF D) (∑ l, lam l • GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) x)
        = ∑ l, lam l • c l • HL.toLie (o₀.act.toF D) x := by
          simp only [map_sum, map_smul, toLie_crys]
      _ = ∑ l, lam l • c l • u + ∑ l, lam l • ∑ j, β (b.t j (c l)) • w j := by
          rw [hs, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [smul_add, smul_add, Finset.smul_sum]
          congr 2
          refine Finset.sum_congr rfl fun j _ => ?_
          exact Lie.mem_eig_iff.1 (hw j) (c l)
      _ = ∑ l, lam l • c l • u := by rw [h2, add_zero]
  refine mem_G_of_rhobar o₀ β HL ?_
  rw [hT, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_comm D.ω (lam l), smul_comm D.ω (c l), hu, smul_comm (c l) ((D.tr : k) - β b.ρ),
    smul_comm (lam l) ((D.tr : k) - β b.ρ)]

end GlobalTheory.HTLieRho

namespace GlobalTheory.HTLieRho
open GlobalTheory.Serre
variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

theorem finrank_quot [IsAlgClosed k] (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) (ht : t = spMap β)
    (HL : LieExact o₀.A) (i : Fin D.a) :
    Module.finrank k (HdR o₀.A ⧸ ((Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) -
      β b.ρ • 1)) ⊔ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤)) = D.m := by
  set X := (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ⊔
    GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤ with hXdef
  set T := HL.toLie (o₀.act.toF D) with hTdef
  set K := X.map T with hKdef
  set E := Lie.eig (o₀.act.toF D) (β.comp (b.t i)) with hEdef
  have hd := two_rho_sub_ne_zero (D := D) b β
  have hX : X = K.comap T := by
    rw [hKdef, Submodule.comap_map_eq, hTdef, HL.ker_toLie]
    exact (sup_eq_left.2 (le_sup_left.trans le_sup_left)).symm
  have hmE : Module.finrank k E = D.m := by
    have h := o₀.lieRank k (𝟙 _) β (by rw [Category.id_comp, ht]) i
    obtain ⟨B⟩ := (Lie.lieMult_id_iff _ _ _).1 h
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  have hχ : Function.Injective (fun j : Fin D.a => β.comp (b.t j)) := by
    intro j j' h
    by_contra hne
    obtain ⟨c, hc⟩ := exists_sep b β hne
    exact hc (RingHom.congr_fun h c)
  have hEρ : ∀ j, Lie.eig (o₀.act.toF D) (β.comp (b.t j)) ≤ eigOm o₀ (β b.ρ) := fun j v hv => by
    rw [mem_eigOm, Lie.mem_eig_iff.1 hv D.ω, RingHom.comp_apply, b.t_ω]

  have hK : K ≤ eigOm o₀ ((D.tr : k) - β b.ρ) ⊔
      ⨆ j, ⨆ (_ : j ≠ i), Lie.eig (o₀.act.toF D) (β.comp (b.t j)) := by
    rw [hKdef, Submodule.map_le_iff_le_comap]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [← HL.ker_toLie (o₀.act.toF D)]
      exact LinearMap.ker_le_comap _
    · rintro _ ⟨h, rfl⟩
      rw [Submodule.mem_comap]
      apply Submodule.mem_sup_left
      rw [mem_eigOm]
      simp only [hTdef, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
        toLie_crys]
      have q := quad_lie o₀ (HL.toLie (o₀.act.toF D) h)
      rw [nm_eq_mul b β] at q
      rw [smul_sub, smul_comm D.ω (β b.ρ)]
      generalize D.ω • D.ω • HL.toLie (o₀.act.toF D) h = Y at q ⊢
      generalize D.ω • HL.toLie (o₀.act.toF D) h = Z at q ⊢
      linear_combination (norm := module) q
    · rw [GlobalTheory.HTRho.mSub, Submodule.span_le]
      rintro _ ⟨c, x, -, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      simp only [hTdef, map_sub, map_smul, toLie_crys]
      obtain ⟨u, hu, w, hw, hs⟩ := lie_decomp o₀ β ht HL (HL.toLie (o₀.act.toF D) x)
      rw [hs, smul_add, smul_add, Finset.smul_sum, Finset.smul_sum, add_sub_add_comm, ← Finset.sum_sub_distrib]
      refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (Submodule.sum_mem _ fun j _ => ?_))
      · rw [mem_eigOm, smul_sub, smul_sub, smul_comm D.ω ((β.comp (b.t i)) c),
          show D.ω • c • u = c • D.ω • u by rw [smul_smul, mul_comm, ← smul_smul], hu,
          smul_comm c ((D.tr : k) - β b.ρ), smul_comm ((β.comp (b.t i)) c) ((D.tr : k) - β b.ρ)]
      · by_cases hj : j = i
        · subst hj
          rw [Lie.mem_eig_iff.1 (hw j) c, sub_self]
          exact zero_mem _
        · refine Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (sub_mem ?_ (Submodule.smul_mem _ _ (hw j))))
          rw [Lie.mem_eig_iff.1 (hw j) c]
          exact Submodule.smul_mem _ _ (hw j)
  have hcompl : IsCompl K E := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hvK hvE
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hK hvK)
      have hzρ : z ∈ eigOm o₀ (β b.ρ) := (iSup_le fun j => iSup_le fun _ => hEρ j) hz
      have hvρ := hEρ i hvE
      rw [mem_eigOm] at hzρ hvρ hy
      have hyρ : D.ω • y = β b.ρ • y := by
        rw [smul_add, smul_add, hzρ] at hvρ
        exact add_right_cancel hvρ
      have h0 : (β b.ρ - ((D.tr : k) - β b.ρ)) • y = 0 := by
        rw [sub_smul, ← hyρ, hy, sub_self]
      obtain rfl := (smul_eq_zero.1 h0).resolve_left hd
      rw [zero_add] at hvE ⊢
      have hind := (Lie.iSupIndep_eig (o₀.act.toF D)).comp hχ
      exact Submodule.disjoint_def.1 (hind i) z hvE hz
    · rw [codisjoint_iff_le_sup]
      intro v _
      obtain ⟨u, hu, w, hw, rfl⟩ := lie_decomp o₀ β ht HL v
      refine add_mem (Submodule.mem_sup_left ?_) (Submodule.sum_mem _ fun j _ => ?_)
      · obtain ⟨h, hh⟩ := lift_rhobar o₀ β HL u hu
        rw [← hh]
        exact Submodule.mem_map_of_mem (Submodule.mem_sup_left (Submodule.mem_sup_right
          (LinearMap.mem_range_self (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) h)))
      · by_cases hj : j = i
        · subst hj
          exact Submodule.mem_sup_right (hw j)
        · apply Submodule.mem_sup_left
          obtain ⟨c, hc⟩ := exists_sep b β hj
          obtain ⟨h, hh⟩ := HL.toLie_surjective (o₀.act.toF D) ((β (b.t j c) - β (b.t i c))⁻¹ • w j)
          have key : T (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O c) h - (β.comp (b.t i)) c • h) = w j := by
            rw [hTdef, map_sub, map_smul, toLie_crys, hh, smul_comm c, Lie.mem_eig_iff.1 (hw j) c,
              RingHom.comp_apply, RingHom.comp_apply, smul_smul, smul_smul, ← sub_smul,
              mul_comm (β (b.t i c)), ← mul_sub, inv_mul_cancel₀ (sub_ne_zero.2 hc), one_smul]
          rw [← key]
          exact Submodule.mem_map_of_mem (Submodule.mem_sup_right (Submodule.subset_span ⟨c, h, trivial, rfl⟩))
  have e1 : (HdR o₀.A ⧸ X) ≃ₗ[k] (Lie (o₀.act.toF D) ⧸ K) :=
    (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ]; exact hX)).trans
      ((K.mkQ ∘ₗ T).quotKerEquivOfSurjective (K.mkQ_surjective.comp (HL.toLie_surjective _)))
  rw [e1.finrank_eq, (Submodule.quotientEquivOfIsCompl K E hcompl).finrank_eq, hmE]

end GlobalTheory.HTLieRho

namespace GlobalTheory.HTLieRho

theorem lie_rho_quot : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → GlobalTheory.HTRho.jSub (GlobalTheory.HTCount.crysAct o₀) (fun i => β.comp (b.t i)) ⊤ ≤ (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ∧ ∀ i, Module.finrank k (HdR o₀.A ⧸ ((Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ⊔ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤)) = D.m := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β ht
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o₀.A o₀.ab
  have HL : LieExact o₀.A := (GlobalTheory.abelianDeRham.2.1 k o₀.A g o₀.ab hg).1
  exact ⟨jSub_le o₀ β ht HL, fun i => finrank_quot o₀ β ht HL i⟩

end GlobalTheory.HTLieRho
