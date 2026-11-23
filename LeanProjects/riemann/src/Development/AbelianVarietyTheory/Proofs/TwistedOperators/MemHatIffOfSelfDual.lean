import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

theorem cpt_inc (Q : Pl D.host.E) (x : D.host.E) :
    cpt Q (inc D x) = algebraMap D.host.E (Q.adicCompletion D.host.E) x := by
  change toAd D (x ⊗ₜ[D.host.F] 1) Q = _
  rw [GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D)]
  rfl

theorem mem_OA (x : EAf D) : x ∈ OA D ↔ ∀ Q : Pl D.host.E, Valued.v (cpt Q x) ≤ 1 := mem_OA_iff x

theorem cjA_cjA (z : EAf D) : cjA D (cjA D z) = z := sg_sg z

theorem cjA_inc (x : D.host.E) : cjA D (inc D x) = inc D (star x) := rfl

theorem cjA_mem {z : EAf D} (h : z ∈ OA D) : cjA D z ∈ OA D := Formalism.UG.P.csDual_sig_mem _ h

theorem cjA_mem_iff {z : EAf D} : cjA D z ∈ OA D ↔ z ∈ OA D :=
  ⟨fun h => cjA_cjA z ▸ cjA_mem h, cjA_mem⟩

theorem inc_mem_iff (x : D.host.E) : inc D x ∈ OA D ↔ x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  GlobalTheory.NormSum.AdLattice.incl_mem_iff x

theorem exists_of_cpt (t : ∀ Q : Pl D.host.E, Q.adicCompletion D.host.E) (ht : ∀ Q, Valued.v (t Q) ≤ 1) :
    ∃ z ∈ OA D, ∀ Q : Pl D.host.E, cpt (D := D) Q z = t Q := by
  obtain ⟨z, hz⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
    (⟨t, Filter.Eventually.of_forall ht⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  have h : ∀ Q : Pl D.host.E, cpt Q z = t Q := fun Q => by
    change toAd D z Q = _
    rw [hz]
    rfl
  exact ⟨z, (mem_OA z).2 fun Q => h Q ▸ ht Q, h⟩

theorem resS_eq_zero_iff_cpt (w : Pl D.host.E) (s : OA D) :
    resS D.host.F w s = 0 ↔ Valued.v (cpt w (s : EAf D)) < 1 := by
  have hv : ∀ x : 𝓞 D.host.E, Valued.v (cpt w ((oToS D.host.F D.host.E x : OA D) : EAf D)) < 1 ↔ x ∈ w.asIdeal := by
    intro x
    have : ((oToS D.host.F D.host.E x : OA D) : EAf D) = inc D (x : D.host.E) := rfl
    rw [this, cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]
    exact w.valuation_lt_one_iff_mem (K := D.host.E) x
  have h1 : ∀ s : OA D, resS D.host.F w s = 0 → Valued.v (cpt w (s : EAf D)) < 1 := by
    intro s hs
    rw [resS_eq_zero_iff] at hs
    refine Submodule.span_induction (p := fun (s : OA D) _ => Valued.v (cpt w (s : EAf D)) < 1) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨x, hx, rfl⟩
      exact (hv x).2 hx
    · simp
    · intro a b _ _ ha hb
      rw [Subring.coe_add, RingHom.map_add]
      exact Valuation.map_add_lt _ ha hb
    · intro c a _ ha
      rw [smul_eq_mul, Subring.coe_mul, RingHom.map_mul, Valuation.map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right ((mem_OA _).1 c.2 w) zero_le' ha
  refine ⟨h1 s, fun h => ?_⟩
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (resS D.host.F w s)
  have h2 := h1 (s - oToS D.host.F D.host.E x) (by rw [RingHom.map_sub, resS_oToS, hx, sub_self])
  rw [← hx, Ideal.Quotient.eq_zero_iff_mem, ← hv]
  have h3 := Valuation.map_sub_lt _ h h2
  rwa [← RingHom.map_sub, AddSubgroupClass.coe_sub, sub_sub_cancel] at h3

theorem isPlIdem_iff (w : Pl D.host.E) (e : EAf D) :
    IsPlIdem w e ↔ cpt w e = 1 ∧ ∀ Q, Q ≠ w → cpt Q e = 0 := by
  constructor
  · rintro ⟨he, h1, h2, h3⟩
    have h4 : ∀ Q : Pl D.host.E, cpt Q e = 0 ∨ cpt Q e = 1 := fun Q => by
      have : cpt Q e * (cpt Q e - 1) = 0 := by rw [mul_sub, ← RingHom.map_mul, h1, mul_one, sub_self]
      simpa [sub_eq_zero] using this
    refine ⟨(h4 w).resolve_left fun h => ?_, fun Q hQ => (h4 Q).resolve_right fun h => ?_⟩
    · have := (resS_eq_zero_iff_cpt w ⟨e, he⟩).2 (by simp [h])
      exact one_ne_zero (h2.symm.trans this)
    · have := (resS_eq_zero_iff_cpt Q ⟨e, he⟩).1 (h3 Q hQ)
      simp [h] at this
  · rintro ⟨h1, h2⟩
    have he : e ∈ OA D := (mem_OA e).2 fun Q => by
      by_cases hQ : Q = w
      · rw [hQ, h1, Valuation.map_one]
      · rw [h2 Q hQ, Valuation.map_zero]; exact zero_le'
    refine ⟨he, cpt_ext fun Q => ?_, ?_, fun Q hQ => (resS_eq_zero_iff_cpt Q _).2 (by simp [h2 Q hQ])⟩
    · rw [RingHom.map_mul]
      by_cases hQ : Q = w
      · rw [hQ, h1, mul_one]
      · rw [h2 Q hQ, mul_zero]
    · rw [← sub_eq_zero, ← map_one (resS D.host.F w), ← RingHom.map_sub, resS_eq_zero_iff_cpt,
        AddSubgroupClass.coe_sub, RingHom.map_sub]
      simp [h1]

theorem plIdemSt (D : D7) : PlIdemSt D := by
  intro w
  obtain ⟨e, -, -, h1, h2⟩ := exists_idem ({w} : Set (Pl D.host.E))
  refine ⟨e, (isPlIdem_iff w e).2 ⟨h1 w rfl, h2⟩, fun e' he' => cpt_ext fun Q => ?_⟩
  replace he' := (isPlIdem_iff w e').1 he'
  by_cases hQ : Q = w
  · rw [hQ, he'.1, h1 w rfl]
  · rw [he'.2 Q hQ, h2 Q hQ]

def idem (w : Pl D.host.E) : EAf D := (plIdemSt D w).choose

theorem isPlIdem_idem (w : Pl D.host.E) : IsPlIdem w (idem w) := (plIdemSt D w).choose_spec.1

theorem eq_idem {w : Pl D.host.E} {e : EAf D} (h : IsPlIdem w e) : e = idem w := (plIdemSt D w).choose_spec.2 e h

theorem idem_mem (w : Pl D.host.E) : idem w ∈ OA D := (isPlIdem_idem w).1

theorem idem_mul_self (w : Pl D.host.E) : idem w * idem w = idem w := (isPlIdem_idem w).2.1

theorem cpt_idem_self (w : Pl D.host.E) : cpt w (idem w) = 1 := ((isPlIdem_iff _ _).1 (isPlIdem_idem w)).1

theorem cpt_idem_ne {w Q : Pl D.host.E} (h : Q ≠ w) : cpt Q (idem w) = 0 :=
  ((isPlIdem_iff _ _).1 (isPlIdem_idem w)).2 Q h

theorem idem_mul_eq_iff (w : Pl D.host.E) (a b : EAf D) : idem w * a = idem w * b ↔ cpt w a = cpt w b := by
  refine ⟨fun h => ?_, fun h => cpt_ext fun Q => ?_⟩
  · simpa only [RingHom.map_mul, cpt_idem_self, one_mul] using congrArg (cpt w) h
  · rw [RingHom.map_mul, RingHom.map_mul]
    by_cases hQ : Q = w
    · rw [hQ, h]
    · rw [cpt_idem_ne hQ, zero_mul, zero_mul]

theorem idem_mul_mem_iff (w : Pl D.host.E) (a : EAf D) : idem w * a ∈ OA D ↔ Valued.v (cpt w a) ≤ 1 := by
  refine ⟨fun h => ?_, fun h => (mem_OA _).2 fun Q => ?_⟩
  · simpa only [RingHom.map_mul, cpt_idem_self, one_mul] using (mem_OA _).1 h w
  · rw [RingHom.map_mul]
    by_cases hQ : Q = w
    · rwa [hQ, cpt_idem_self, one_mul]
    · rw [cpt_idem_ne hQ, zero_mul, Valuation.map_zero]; exact zero_le'

theorem mem_OA_iff_idem (a : EAf D) : a ∈ OA D ↔ ∀ w : Pl D.host.E, idem w * a ∈ OA D := by
  simp only [idem_mul_mem_iff]
  exact mem_OA a

theorem idem_mul_ne {w w' : Pl D.host.E} (h : w ≠ w') : idem w * idem w' = 0 := by
  rw [← mul_zero (idem w), idem_mul_eq_iff, cpt_idem_ne h, RingHom.map_zero]

theorem cjA_idem (w : Pl D.host.E) : cjA D (idem w) = idem (cP w) := by
  refine eq_idem ((isPlIdem_iff _ _).2 ⟨?_, fun Q hQ => cpt_sg_eq_zero (cpt_idem_ne fun h => hQ ?_)⟩)
  · have := cpt_sg_eq_zero (Q := cP w) (z := 1 - idem w) (by rw [cP_cP, RingHom.map_sub, cpt_idem_self, RingHom.map_one, sub_self])
    rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
    exact this.symm
  · rw [← h, cP_cP]

theorem cpt_cjA_le_iff (w : Pl D.host.E) (a : EAf D) :
    Valued.v (cpt (cP w) (cjA D a)) ≤ 1 ↔ Valued.v (cpt w a) ≤ 1 := by
  rw [← idem_mul_mem_iff, ← idem_mul_mem_iff, ← cjA_idem, ← RingHom.map_mul, cjA_mem_iff]

section Span

variable {F E ι R O : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R] {S : Subring (E ⊗[F] R)}
  [CommRing O] [Algebra O E] (Λ : Submodule O (ι → E))

theorem smul_mem_latS {a : E ⊗[F] R} (ha : a ∈ S) {x : ι → E ⊗[F] R} (hx : x ∈ Formalism.UG.latS R S Λ) :
    a • x ∈ Formalism.UG.latS R S Λ := (Formalism.UG.latS R S Λ).smul_mem (⟨a, ha⟩ : S) hx

theorem incl_mem_latS {x : ι → E} (hx : x ∈ Λ) : (fun i => Formalism.UG.inclE (F := F) R (x i)) ∈ Formalism.UG.latS R S Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem latS_induction {p : (ι → E ⊗[F] R) → Prop} (h1 : ∀ x ∈ Λ, p fun i => Formalism.UG.inclE (F := F) R (x i))
    (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) (hsm : ∀ a ∈ S, ∀ x, p x → p (a • x)) {y : ι → E ⊗[F] R}
    (hy : y ∈ Formalism.UG.latS R S Λ) : p y := by
  refine Submodule.span_induction (p := fun y _ => p y) ?_ h0 (fun x y _ _ => hadd x y)
    (fun (a : S) x _ => hsm a a.2 x) hy
  rintro _ ⟨x, hx, rfl⟩
  exact h1 x hx

end Span

theorem mem_hat {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Fin n → EAf D) :
    y ∈ hat Λ ↔ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := Iff.rfl

section Hat

variable {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}

theorem zero_mem_hat : (0 : Fin n → EAf D) ∈ hat Λ := (Formalism.L2.Herm.hatL (F := D.host.F) Λ).zero_mem

theorem add_mem_hat {x y : Fin n → EAf D} (hx : x ∈ hat Λ) (hy : y ∈ hat Λ) : x + y ∈ hat Λ :=
  (Formalism.L2.Herm.hatL (F := D.host.F) Λ).add_mem hx hy

theorem sub_mem_hat {x y : Fin n → EAf D} (hx : x ∈ hat Λ) (hy : y ∈ hat Λ) : x - y ∈ hat Λ :=
  (Formalism.L2.Herm.hatL (F := D.host.F) Λ).sub_mem hx hy

theorem smul_mem_hat {a : EAf D} (ha : a ∈ OA D) {x : Fin n → EAf D} (hx : x ∈ hat Λ) : a • x ∈ hat Λ :=
  smul_mem_latS Λ ha hx

theorem inc_mem_hat {x : Fin n → D.host.E} (hx : x ∈ Λ) : (fun i => inc D (x i)) ∈ hat Λ :=
  incl_mem_latS Λ hx

theorem hat_induction {p : (Fin n → EAf D) → Prop} (h1 : ∀ x ∈ Λ, p fun i => inc D (x i)) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hsm : ∀ a ∈ OA D, ∀ x, p x → p (a • x)) {y : Fin n → EAf D}
    (hy : y ∈ hat Λ) : p y :=
  latS_induction Λ h1 h0 hadd hsm hy

theorem hat_mono {Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ ≤ Λ') : hat Λ ⊆ hat (D := D) Λ' :=
  fun _ hy => hat_induction (fun _ hx => inc_mem_hat (h hx)) zero_mem_hat (fun _ _ => add_mem_hat)
    (fun _ ha _ => smul_mem_hat ha) hy

theorem mem_hat_of_idem (h : Λ.FG) {y : Fin n → EAf D} (hy : ∀ w : Pl D.host.E, idem w • y ∈ hat Λ) : y ∈ hat Λ := by
  obtain ⟨m, l, hl⟩ := Submodule.fg_iff_exists_fin_generating_family.1 h
  have h1 : ∀ y ∈ hat (D := D) Λ, ∃ c : Fin m → EAf D, (∀ j, c j ∈ OA D) ∧ y = ∑ j, c j • fun i => inc D (l j i) := by
    intro y hy
    refine hat_induction (p := fun y => ∃ c : Fin m → EAf D, (∀ j, c j ∈ OA D) ∧ y = ∑ j, c j • fun i => inc D (l j i))
      ?_ ⟨0, fun _ => zero_mem _, by simp⟩ ?_ ?_ hy
    · intro x hx
      rw [← hl] at hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
      refine ⟨fun j => inc D (c j), fun j => (inc_mem_iff _).2 ⟨c j, rfl⟩, funext fun i => ?_⟩
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul, ← RingHom.map_mul]
      rfl
    · rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      exact ⟨c + d, fun j => add_mem (hc j) (hd j), by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
    · rintro a ha _ ⟨c, hc, rfl⟩
      exact ⟨fun j => a * c j, fun j => mul_mem ha (hc j), by simp only [Finset.smul_sum, smul_smul]⟩
  choose c hc hy' using fun w => h1 _ (hy w)
  choose d hd hd' using fun j => exists_of_cpt (D := D) (fun Q => cpt Q (c Q j)) fun Q => (mem_OA _).1 (hc Q j) Q
  have : y = ∑ j, d j • fun i => inc D (l j i) := by
    funext i
    refine cpt_ext fun Q => ?_
    have := congrArg (cpt Q) (congrFun (hy' Q) i)
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul, RingHom.map_mul, cpt_idem_self, one_mul,
      hd'] at this ⊢
    exact this
  rw [this]
  exact (Formalism.L2.Herm.hatL (F := D.host.F) Λ).sum_mem fun j _ =>
    smul_mem_hat (hd j) (inc_mem_hat (hl ▸ Submodule.subset_span ⟨j, rfl⟩))

theorem mem_hat_lat (β : GL (Fin n) (EAf D)) (y : Fin n → EAf D) :
    y ∈ hat (lat β) ↔ ∀ i, ((β⁻¹).val *ᵥ y) i ∈ OA D := isFrame_lat β y

theorem exists_eq_lat (h : Submodule.IsLattice D.host.E Λ) : ∃ β : GL (Fin n) (EAf D), Λ = lat β := by
  obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ h.fg h.span_eq_top
  exact ⟨β, eq_lat hβ h⟩

theorem inc_mem_hat_iff (h : Submodule.IsLattice D.host.E Λ) (x : Fin n → D.host.E) :
    (fun i => inc D (x i)) ∈ hat Λ ↔ x ∈ Λ := by
  obtain ⟨β, rfl⟩ := exists_eq_lat h
  exact (mem_hat_lat β _).trans (GlobalTheory.NormSum.AdLattice.mem_lat β x).symm

theorem exists_sub_inc_mem (a : EAf D) : ∃ x : D.host.E, a - inc D x ∈ OA D := by
  obtain ⟨x, b, hb, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.E 1 one_pos).1 (toAd D a)
  refine ⟨x, (mem_OA_iff _).2 fun Q => ?_⟩
  have : cpt Q (a - inc D x) = b Q := by
    rw [RingHom.map_sub, cpt_inc, sub_eq_iff_eq_add']
    change toAd D a Q = _
    rw [e, one_smul]
    rfl
  rw [this]
  exact hb Q

theorem exists_sub_inc_mem_hat (h : Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤) (y : Fin n → EAf D) :
    ∃ x : Fin n → D.host.E, y - (fun i => inc D (x i)) ∈ hat Λ := by
  have h1 : ∀ x ∈ Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)), ∀ a : EAf D,
      ∃ x' : Fin n → D.host.E, (a • fun i => inc D (x i)) - (fun i => inc D (x' i)) ∈ hat Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro a
      obtain ⟨t, ht⟩ := exists_sub_inc_mem a
      refine ⟨t • x, ?_⟩
      convert smul_mem_hat ht (inc_mem_hat hx) using 1
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.map_mul, sub_mul]
    | zero => exact fun a => ⟨0, by convert zero_mem_hat (Λ := Λ) using 1; funext i; simp⟩
    | add x y _ _ hx hy =>
      intro a
      obtain ⟨x', hx'⟩ := hx a
      obtain ⟨y', hy'⟩ := hy a
      refine ⟨x' + y', ?_⟩
      convert add_mem_hat hx' hy' using 1
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.map_add]
      ring
    | smul c x _ hx =>
      intro a
      obtain ⟨x', hx'⟩ := hx (a * inc D c)
      refine ⟨x', ?_⟩
      convert hx' using 2
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, mul_assoc]
  choose x hx using fun j : Fin n => h1 (Pi.single j 1) (h ▸ Submodule.mem_top) (y j)
  refine ⟨∑ j, x j, ?_⟩
  convert (Formalism.L2.Herm.hatL (F := D.host.F) Λ).sum_mem (t := Finset.univ) fun j _ => hx j using 1
  refine iff_of_eq (congrArg (· ∈ hat Λ) ?_)
  funext i
  simp [Finset.sum_apply, Pi.single_apply, apply_ite (inc D), Finset.sum_sub_distrib]

end Hat

theorem hA_eq (V : HSp D) (x y : Fin V.rank → EAf D) :
    hA V x y = Formalism.UG.hform (cjA D) (V.gram.map (inc D)) y x := rfl

theorem isSelfDualC_lat {V : HSp D} {β : GL (Fin V.rank) (EAf D)} (h : Unimod (OA D) (gramOf V β)) :
    IsSelfDualC V (lat β) :=
  ⟨GlobalTheory.NormSum.AdLattice.lat_isLattice β, fun y => (mem_lat_iff_dual h y).trans
    ⟨fun H x hx => H x hx, fun H x hx => H x hx⟩⟩

theorem dualL_eq {V : HSp D} {Λ : Lat V} (h : IsSelfDualC V Λ) : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ := by
  unfold Formalism.L2.Herm.dualL
  conv_rhs => rw [← Submodule.span_eq Λ]
  congr 1
  ext y
  exact ((h.2 y).trans ⟨fun H x hx => H x hx, fun H x hx => H x hx⟩).symm

theorem exists_orth {V : HSp D} {Λ : Lat V} (h : IsSelfDualC V Λ) :
    ∃ β : GL (Fin V.rank) (EAf D), Λ = lat β ∧ gramOf V β = 1 := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨β, hβ⟩ := exists_eq_lat h.1
  obtain ⟨u, hu⟩ := GlobalTheory.AdelicOrthFrame.exists_orth (E := D.host.E) D.sp.cm (G := V.gram)
    (fun a b => V.herm.eq (V.frame a) (V.frame b)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
    ⟨h.1.fg, h.1.span_eq_top⟩ (GlobalTheory.AdelicOrthFrame.selfDual_iff D.sp.cm V (dualL_eq h)) (β := β) (hβ ▸ isFrame_lat β)
  refine ⟨β * intGL D.host.F D.host.E V.rank u, hβ.trans (le_antisymm
    (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_) (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_)), hu⟩
  · rw [_root_.mul_inv_rev, inv_mul_cancel_right, ← map_inv]
    exact ((u⁻¹).val i j).2
  · rw [inv_mul_cancel_left]
    exact (u.val i j).2

theorem unimod_one {n : ℕ} : Unimod (OA D) (1 : Matrix (Fin n) (Fin n) (EAf D)) :=
  ⟨one_entry_mem _, 1, one_entry_mem _, Matrix.one_mul _⟩

section Form

variable (V : HSp D)

theorem hA_add_left (x x' y : Fin V.rank → EAf D) : hA V (x + x') y = hA V x y + hA V x' y := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_add_right (x y y' : Fin V.rank → EAf D) : hA V x (y + y') = hA V x y + hA V x y' := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, RingHom.map_add, add_mul, Finset.sum_add_distrib]

theorem hA_smul_left (a : EAf D) (x y : Fin V.rank → EAf D) : hA V (a • x) y = a * hA V x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_smul_right (a : EAf D) (x y : Fin V.rank → EAf D) : hA V x (a • y) = cjA D a * hA V x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_sub_left (x x' y : Fin V.rank → EAf D) : hA V (x - x') y = hA V x y - hA V x' y := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hA_sub_right (x y y' : Fin V.rank → EAf D) : hA V x (y - y') = hA V x y - hA V x y' := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, RingHom.map_sub, sub_mul, Finset.sum_sub_distrib]

theorem cjA_hA (x y : Fin V.rank → EAf D) : cjA D (hA V x y) = hA V y x := by
  simp only [hA, Formalism.UG.hform, map_sum, RingHom.map_mul, cjA_cjA, Matrix.map_apply, cjA_inc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show star (V.gram j i) = V.gram i j from V.herm.eq _ _]
  ring

theorem hA_vA (x y : V.V) : hA V (vA V x) (vA V y) = inc D (V.hD x y) := by
  rw [HSpace.hD, Formalism.L2.Herm.hT_crd D.sp.cm]
  exact Formalism.UG.P.csDual_hform_incl D.sp.cm.sig V.gram _ _

theorem vA_mem_hat {L : Submodule (𝓞 D.host.E) V.V} {x : V.V} (hx : x ∈ L) : vA V x ∈ hat (Formalism.L2.Herm.crdLat V L) :=
  inc_mem_hat ⟨x, hx, rfl⟩

theorem vA_add (x y : V.V) : vA V (x + y) = vA V x + vA V y := by
  funext i; simp [vA]

theorem vA_smul (a : D.host.E) (x : V.V) : vA V (a • x) = inc D a • vA V x := by
  funext i; simp [vA]

theorem mA_mulVec_vA (X : HSp D) (ι : X.V →ₗ[D.host.E] V.V) (x : X.V) : mA V X ι *ᵥ vA X x = vA V (ι x) := by
  funext i
  have := congrArg (inc D) (congrFun (LinearMap.toMatrix_mulVec_repr X.frame V.frame ι x) i)
  rw [RingHom.map_mulVec] at this
  exact this

theorem exists_dual_frame (β : GL (Fin V.rank) (EAf D)) : ∃ β' : GL (Fin V.rank) (EAf D),
    Formalism.UG.cT (cjA D) β.val * V.gram.map (inc D) * β'.val = 1 ∧
      Formalism.UG.cT (cjA D) β'.val * V.gram.map (inc D) * β.val = 1 :=
  exists_dual (sg D) sg_sg _ (cT_gram V) (isUnit_gram V) β

variable {V}

theorem dual_frame_gen {A : Type} [CommRing A] (S : Subring A) (σ : A →+* A) (hσ : ∀ a ∈ S, σ a ∈ S) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) A} {β β' : GL (Fin n) A} (h : Formalism.UG.cT σ β.val * J * β'.val = 1) (y : Fin n → A) :
    (∀ x, (∀ i, ((β⁻¹).val *ᵥ x) i ∈ S) → Formalism.UG.hform σ J x y ∈ S) ↔ ∀ i, ((β'⁻¹).val *ᵥ y) i ∈ S := by
  have key : ∀ u, Formalism.UG.hform σ J (β.val *ᵥ u) y = ∑ i, σ (u i) * ((β'⁻¹).val *ᵥ y) i := by
    intro u
    have e : y = β'.val *ᵥ ((β'⁻¹).val *ᵥ y) := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    generalize (β'⁻¹).val *ᵥ y = v at e
    have e2 : ∀ a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
      intro a b
      simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
    have e3 : σ ∘ (β.val *ᵥ u) = (σ ∘ u) ᵥ* Formalism.UG.cT σ β.val := by
      funext i
      rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
    rw [e, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, one_mulVec]
    rfl
  constructor
  · intro H i
    have := H (β.val *ᵥ Pi.single i 1) fun k => by
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    rw [key] at this
    simpa [Pi.single_apply, apply_ite σ] using this
  · intro H x hx
    have e : x = β.val *ᵥ ((β⁻¹).val *ᵥ x) := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    rw [e, key]
    exact sum_mem fun i _ => mul_mem (hσ _ (hx i)) (H i)

theorem dual_hat_lat {β β' : GL (Fin V.rank) (EAf D)}
    (h : Formalism.UG.cT (cjA D) β.val * V.gram.map (inc D) * β'.val = 1) (y : Fin V.rank → EAf D) :
    (∀ x ∈ hat (lat β), hA V x y ∈ OA D) ↔ y ∈ hat (lat β') := by
  rw [mem_hat_lat, ← dual_frame_gen (OA D) (cjA D) (fun _ => cjA_mem) h]
  refine forall_congr' fun x => ?_
  rw [mem_hat_lat, ← cjA_mem_iff, cjA_hA, hA_eq]

theorem hA_mem_of_forall {Λ : Lat V} {y : Fin V.rank → EAf D} (h : ∀ x ∈ Λ, hA V (fun i => inc D (x i)) y ∈ OA D) :
    ∀ x ∈ hat Λ, hA V x y ∈ OA D := fun _ hx =>
  hat_induction (p := fun x => hA V x y ∈ OA D) h (by simp [hA, Formalism.UG.hform])
    (fun a b ha hb => by rw [hA_add_left]; exact add_mem ha hb)
    (fun a ha b hb => by rw [hA_smul_left]; exact mul_mem ha hb) hx

theorem dualL_lat_eq {β β' : GL (Fin V.rank) (EAf D)}
    (h : Formalism.UG.cT (cjA D) β.val * V.gram.map (inc D) * β'.val = 1) :
    Formalism.L2.Herm.dualL D.sp.cm V (lat β) = lat β' := by
  unfold Formalism.L2.Herm.dualL
  conv_rhs => rw [← Submodule.span_eq (lat β')]
  congr 1
  ext y
  have e : ∀ x : Fin V.rank → D.host.E, hA V (fun i => inc D (x i)) (fun i => inc D (y i)) ∈ OA D ↔
      Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro x
    rw [← cjA_mem_iff, cjA_hA, ← inc_mem_iff, ← Formalism.UG.P.csDual_hform_incl D.sp.cm.sig V.gram]
    rfl
  rw [SetLike.mem_coe, ← inc_mem_hat_iff (GlobalTheory.NormSum.AdLattice.lat_isLattice β'), ← dual_hat_lat h]
  exact ⟨fun H => hA_mem_of_forall fun x hx => (e x).2 (H x hx), fun H x hx => (e x).1 (H _ (inc_mem_hat hx))⟩

theorem mem_hat_dualL_iff {Λ : Lat V} (h : Submodule.IsLattice D.host.E Λ) (y : Fin V.rank → EAf D) :
    y ∈ hat (Formalism.L2.Herm.dualL D.sp.cm V Λ) ↔ ∀ x ∈ hat Λ, hA V x y ∈ OA D := by
  obtain ⟨β, rfl⟩ := exists_eq_lat h
  obtain ⟨β', h1, -⟩ := exists_dual_frame V β
  rw [dualL_lat_eq h1, dual_hat_lat h1]

theorem mem_hat_of_bidual {Λ : Lat V} (h : Submodule.IsLattice D.host.E Λ) {x : Fin V.rank → EAf D}
    (hx : ∀ y, (∀ x' ∈ hat Λ, hA V x' y ∈ OA D) → hA V y x ∈ OA D) : x ∈ hat Λ := by
  obtain ⟨β, rfl⟩ := exists_eq_lat h
  obtain ⟨β', h1, h2⟩ := exists_dual_frame V β
  exact (dual_hat_lat h2 x).1 fun y hy => hx y ((dual_hat_lat h1 y).2 hy)

theorem mem_hat_iff_of_selfDual {Λ : Lat V} (h : IsSelfDualC V Λ) (y : Fin V.rank → EAf D) :
    y ∈ hat Λ ↔ ∀ x ∈ hat Λ, hA V x y ∈ OA D := by
  rw [← mem_hat_dualL_iff h.1, dualL_eq h]

end Form

theorem Tu_ne_zero (u : D.what₂.Word) : Tu D u ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

theorem T_notMem_sq (u : D.what₂.Word) (w : Pl D.host.E) : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨π, -, h1, h2⟩ := D.T_norm u
  have h3 := (GlobalTheory.HalfGen.factors_of_ncard_places _ _ (D.mem u).A.T_prime
    (Formalism.MainNotions.Gaps.LevGap.T_split_E D.host _ π h1 h2 (D.mem u).A.T_prime)).2
  rw [← UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)] at h3
  intro h
  rw [← Ideal.dvd_span_singleton, sq] at h
  exact w.isPrime.ne_top (Ideal.isUnit_iff.1 (h3 _ h))

theorem pi_mul_cO {u : D.what₂.Word} {π : 𝓞 D.host.E} (h : IsPi u π) :
    π * cO D π = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := RingOfIntegers.ext (by
  simp only [map_mul, map_natCast]
  exact h.2)

theorem T_mem_iff {u : D.what₂.Word} {π : 𝓞 D.host.E} (h : IsPi u π) (w : Pl D.host.E) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ↔ π ∈ w.asIdeal ∨ π ∈ (cP w).asIdeal := by
  rw [← pi_mul_cO h, w.isPrime.mul_mem_iff_mem_or_mem]
  rfl

theorem pi_notMem_cP {u : D.what₂.Word} {π : 𝓞 D.host.E} (h : IsPi u π) {w : Pl D.host.E} (hw : π ∈ w.asIdeal) :
    π ∉ (cP w).asIdeal := fun h' => T_notMem_sq u w (by
  rw [← pi_mul_cO h, sq]
  exact Ideal.mul_mem_mul hw h')

theorem idem_mul_inv_mem_iff (u : D.what₂.Word) (w : Pl D.host.E) :
    idem w * inc D (Tu D u)⁻¹ ∈ OA D ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  rw [idem_mul_mem_iff, cpt_inc]
  exact GlobalTheory.IdemSupport.inv_mem_iff w (x := (((D.mem u).A.T : ℕ) : 𝓞 D.host.E))
    (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)

theorem exists_mul_eq_idem (u : D.what₂.Word) (w : Pl D.host.E) {a : EAf D} (ha : a ∈ OA D)
    (h : idem w * (inc D (Tu D u)⁻¹ * a) ∉ OA D) : ∃ b ∈ OA D, b * a = idem w := by
  classical
  rw [idem_mul_mem_iff, RingHom.map_mul, cpt_inc, Valuation.map_mul, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀,
    not_le] at h
  have h1 : ¬ w.valuation D.host.E (Tu D u) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    have := T_notMem_sq u w
    rw [← w.intValuation_le_pow_iff_mem, ← w.valuation_of_algebraMap (K := D.host.E)] at this
    simpa using this
  have h2 := (mem_OA a).1 ha w
  have h1' : w.valuation D.host.E (Tu D u) ≤ 1 := by
    simpa using w.valuation_le_one (K := D.host.E) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E)
  have h3 : Valued.v (cpt w a) = 1 := by
    have a0 : Valued.v (cpt w a) ≠ 0 := fun h0 => by simp [h0] at h
    have t0 : w.valuation D.host.E (Tu D u) ≠ 0 := (Valuation.ne_zero_iff _).2 (Tu_ne_zero u)
    rw [← WithZero.exp_log a0] at h h2 ⊢
    rw [← WithZero.exp_log t0] at h h1
    rw [← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp] at h1
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    rw [← WithZero.exp_zero, WithZero.exp_inj]
    omega
  have h4 : cpt w a ≠ 0 := fun h0 => by simp [h0] at h3
  obtain ⟨b, hb, hb'⟩ := exists_of_cpt (D := D) (fun Q => if Q = w then (cpt Q a)⁻¹ else 0) fun Q => by
    split_ifs with hQ
    · rw [hQ, map_inv₀, h3, inv_one]
    · simp
  refine ⟨b, hb, cpt_ext fun Q => ?_⟩
  rw [RingHom.map_mul, hb']
  split_ifs with hQ
  · rw [hQ, inv_mul_cancel₀ h4, cpt_idem_self]
  · rw [zero_mul, cpt_idem_ne hQ]

def glueLat (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (u : D.what₂.Word) (L₀ : Lat X) (x₀ : X.V) :
    Submodule (𝓞 D.host.E) Y.V :=
  (L₀.comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E))).map (ι.restrictScalars (𝓞 D.host.E)) ⊔
    Submodule.span (𝓞 D.host.E) {(Tu D u)⁻¹ • z + ι x₀}

structure IsGlueVec (X : HSp D) (u : D.what₂.Word) (L₀ : Lat X) (f : Fin X.rank → EAf D) : Prop where
  mul_mem : inc D (Tu D u) • f ∈ hat L₀
  int : ∀ x ∈ hat L₀, ∀ y ∈ hat L₀, hA X x y ∈ OA D
  pair : ∀ y ∈ hat L₀, hA X f y ∈ OA D
  norm : hA X f f - inc D (Tu D u)⁻¹ ∈ OA D
  dual : ∀ y, (∀ x ∈ hat L₀, hA X x y ∈ OA D) → ∃ a ∈ OA D, y - a • f ∈ hat L₀

end GlobalTheory.AdIsom

end
