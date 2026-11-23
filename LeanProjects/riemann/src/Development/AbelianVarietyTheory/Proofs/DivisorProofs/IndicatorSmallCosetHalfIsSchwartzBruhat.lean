import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.CosSB

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV GlobalTheory.LatVac
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

section Small

variable {a b : ℕ}

theorem frAt_add (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x + y) = frAt w β' β x + frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_add _ (toEAf D).map_add, Comparison₂.fr_add, Matrix.map_add _ (cpt (D := D) w).map_add]

theorem frAt_sub (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x - y) = frAt w β' β x - frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_sub _ (toEAf D).map_sub, Comparison₂.fr_sub, Matrix.map_sub _ (cpt (D := D) w).map_sub]

theorem isSmall_add {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}
    {x y : Mx D b a} (hx : IsSmall P β' β n x) (hy : IsSmall P β' β n y) : IsSmall P β' β n (x + y) :=
  fun w hw i j => by
    rw [frAt_add, Matrix.add_apply]
    exact Valuation.map_add_le _ (hx w hw i j) (hy w hw i j)

theorem isSmall_sub {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}
    {x y : Mx D b a} (hx : IsSmall P β' β n x) (hy : IsSmall P β' β n y) : IsSmall P β' β n (x - y) :=
  fun w hw i j => by
    rw [frAt_sub, Matrix.sub_apply]
    exact Valuation.map_sub_le _ (hx w hw i j) (hy w hw i j)

theorem isHalf_add_nsmul {e : AE D} {t u : Mx D b a} (k : ℕ) (hu : IsHalf e u) : IsHalf e (t + k • u) ↔ IsHalf e t := by
  have h : ∀ i j, e * (t + k • u) i j = e * t i j + k • u i j := fun i j => by
    rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, mul_add, mul_left_comm, hu i j]
  unfold IsHalf
  refine forall₂_congr fun i j => ?_
  rw [h, Matrix.add_apply, Matrix.smul_apply, add_left_inj]

theorem v_unif_pow (w : Pl D.host.E) (n : ℕ) :
    Valued.v (((unifAt w ^ (n : ℤ) : (Kw w)ˣ)) : Kw w) = WithZero.exp (-(n : ℤ)) := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem val_le_unif_iff (w : Pl D.host.E) (n : ℕ) (x : Kw w) :
    valuation (Kw w) x ≤ valuation (Kw w) (((unifAt w ^ (n : ℤ) : (Kw w)ˣ)) : Kw w) ↔
      Valued.v x ≤ WithZero.exp (-(n : ℤ)) :=
  (Comparison₂.vEq w _ _).trans (by rw [v_unif_pow])

end Small

section Lat

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem nsmul_mem_hatMx {b : ℕ} (h2 : ∀ x ∈ latRat S T ΛS ΛT, b • x ∈ homLat ΛS ΛT) (𝔪 : Ideal (𝓞 D.host.E))
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) :
    (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
  refine latO_induction (p := fun u => (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) ?_ ?_ ?_ ?_ hu
  · intro α hα X hX
    rw [← WeilOver.finTens_nsmul]
    refine AddSubgroup.subset_closure ⟨α, hα, _, ?_, rfl⟩
    rw [mul_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]
    exact Submodule.smul_mem_smul (Ideal.absNorm_mem _) (h2 X hX)
  · rw [nsmul_zero]; exact zero_mem _
  · intro x y hx hy; rw [nsmul_add]; exact add_mem hx hy
  · intro x hx; rw [neg_nsmul]; exact neg_mem hx

theorem nsmul_mem_latO {a : ℕ} (h1 : ∀ x ∈ homLat ΛS ΛT, a • x ∈ latRat S T ΛS ΛT) (𝔪 : Ideal (𝓞 D.host.E))
    {u : WO S T} (hu : u ∈ hatMx (𝔪 • homLat ΛS ΛT)) : a • u ∈ latO S T ΛS ΛT fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    exact WeilOver.finTens_nsmul α a x ▸ finTens_mem_latO hα (h1 x (Submodule.smul_le_right hx))
  | zero => rw [nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem isSmall_of_mem_hatMx {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (P : Finset (Pl D.host.E)) (n : ℕ) {u : WO S T}
    (hu : u ∈ hatMx ((∏ w ∈ P, w.asIdeal ^ n) • homLat ΛS ΛT)) : IsSmall P βT βS n u := by
  intro w hw i j
  obtain ⟨s, hs, h⟩ := ((Comparison₂.mem_hatMx_iff hS hT _ u).1 hu).2 i j
  have h3 := Comparison₂.v_le_of_mem_idS (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ n) hw)) hs
  rw [val_le_unif_iff]
  change Valued.v (cpt w (Comparison₂.fr βT βS (u.map (toEAf D)) i j)) ≤ _
  rwa [← h]

end Lat

end GlobalTheory.FunObj.CosSB

namespace GlobalTheory.FunObj.CosSB

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV GlobalTheory.LatVac
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem prod_pow_ne_bot {D : D7} (P : Finset (Pl D.host.E)) (n : ℕ) : (∏ w ∈ P, w.asIdeal ^ n) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem isSBHalf_cosLoc : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ) (r : WO S T),
    Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT →
    IsIdemSum e P → IsHalf e r → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosLoc P e βT βS n r) := by
  intro D S T ΛS ΛT βS βT P e n r hS hT hFS hFT he _
  classical
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le hS hT
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom hS hT
  obtain ⟨e0, e1, e2⟩ := Comparison₂.cpt_idemSum he
  have hM : 0 < Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n) :=
    Nat.pos_of_ne_zero fun h => prod_pow_ne_bot P n (Ideal.absNorm_eq_zero_iff.1 h)

  set N : ℕ := Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ 1) with hNdef
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => prod_pow_ne_bot P 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNmem : ∀ w ∈ P, (N : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    have := Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
      (Ideal.absNorm_mem (∏ w ∈ P, w.asIdeal ^ 1))
    rw [pow_one] at this
    exact this

  have hc1 : ∀ p : Fin T.rank × Fin S.rank, ∃ k : ℕ, ∀ l, k ≤ l →
      ((N ^ l : ℕ) : Lev.EAf D) * (toEAf D e * Comparison₂.fr βT βS (r.map (toEAf D)) p.1 p.2) ∈ OA D :=
    fun p => exists_pow_mul_mem _ fun Q hQ => by
      have hQP : Q ∉ P := fun h => hQ (hNmem Q h)
      rw [map_mul, e2 Q hQP, zero_mul]
      exact zero_mem _
  choose kk hkk using hc1
  set c : ℕ := N ^ (Finset.univ.sup kk) with hcdef
  have hc0 : 0 < c := pow_pos hN _
  have hc : ∀ i j, (c : Lev.EAf D) * (toEAf D e * Comparison₂.fr βT βS (r.map (toEAf D)) i j) ∈ OA D :=
    fun i j => hkk (i, j) _ (Finset.le_sup (f := kk) (Finset.mem_univ (i, j)))
  refine ⟨fun t ht => ?_, (a * c) * (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n)), by positivity,
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by unfold cosLoc; rw [if_neg fun H => h H.1])
  · have hk : IsSmall P βT βS n (((a * c) * (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n))) • u) := by
      refine isSmall_of_mem_hatMx hFS hFT P n ?_
      rw [mul_nsmul']
      exact nsmul_mem (nsmul_mem_hatMx h2 _ hu) _
    unfold cosLoc
    refine if_congr (and_congr (isHalf_add_nsmul _ hh) ?_) rfl rfl
    rw [add_sub_right_comm]
    exact ⟨fun h => by simpa using isSmall_sub h hk, fun h => isSmall_add h hk⟩
  · obtain ⟨hth, hts⟩ : IsHalf e t ∧ IsSmall P βT βS n (t - r) := by
      by_contra h
      exact ht (by unfold cosLoc; rw [if_neg h])
    set X := Comparison₂.fr βT βS (t.map (toEAf D))
    set R := Comparison₂.fr βT βS (r.map (toEAf D))
    have hX : Comparison₂.fr βT βS ((c • t).map (toEAf D)) = (c : Lev.EAf D) • (toEAf D e • X) := by
      have : (c • t).map (toEAf D) = (c : Lev.EAf D) • (toEAf D e • t.map (toEAf D)) := by
        ext i j
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul,
          map_mul, map_natCast, smul_eq_mul, smul_eq_mul]
        conv_lhs => rw [← hth i j]
        rw [map_mul]
      rw [this, Comparison₂.fr_smul, Comparison₂.fr_smul]
    have hsm : ∀ i j, toEAf D e * (X - R) i j ∈ OA D := fun i j => by
      refine (mem_OA_iff _).2 fun Q => ?_
      rw [map_mul]
      by_cases hQ : Q ∈ P
      · rw [e1 Q hQ, one_mul]
        have h3 := (val_le_unif_iff Q n _).1 (hts Q hQ i j)
        rw [frAt_sub, Matrix.sub_apply] at h3
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, Matrix.sub_apply, map_sub]
        refine h3.trans ?_
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      · rw [e2 Q hQ, zero_mul]
        exact zero_mem _
    have hint : ∀ i j, Comparison₂.fr βT βS ((c • t).map (toEAf D)) i j ∈ OA D := fun i j => by
      have : Comparison₂.fr βT βS ((c • t).map (toEAf D)) i j =
          (c : Lev.EAf D) * (toEAf D e * (X - R) i j) + (c : Lev.EAf D) * (toEAf D e * R i j) := by
        rw [hX, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, smul_eq_mul, ← mul_add, ← mul_add,
          sub_add_cancel]
      rw [this]
      exact add_mem (mul_mem (natCast_mem _ _) (hsm i j)) (hc i j)
    have hmem : c • t ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat ΛS ΛT) := by
      refine (Comparison₂.mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i j => ?_, fun i j => ⟨⟨_, hint i j⟩, ?_, rfl⟩⟩
      · rw [Matrix.smul_apply, map_nsmul, ← hth i j, map_mul, e0, zero_mul, smul_zero]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n))
    convert this using 1
    rw [mul_comm (a * c), ← smul_smul, ← smul_smul a c t]

end GlobalTheory.FunObj.CosSB

end
