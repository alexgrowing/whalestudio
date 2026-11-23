import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SecondFlagXsLeBigBlock
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CntNotInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.EqZeroOfMulVec

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.DualityBasisChange

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem iE_mem_LO (hA : ∀ p, Agree δ M p) (p : PlF D) (o : 𝓞 D.host.E) :
    (D.s.atP p).ιE (o : D.host.E) ∈ (M p).L.O := by
  rw [(hA p).2.2.2.1]
  exact PI.CntNotIntW.iE_mem_O D p o

theorem bc_smulO (L : LocSp D M) (p : PlF D) (o : 𝓞 D.host.E) (x : (VS D).V) :
    L.bc p (o • x) = (D.s.atP p).ιE (o : D.host.E) • L.bc p x := by
  rw [← L.bc_smul]
  congr 1
  exact (algebraMap_smul D.host.E o x).symm

theorem localLattice_span₂ (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) (S : Set (VS D).V) :
    lattice₂ L p (Submodule.span (𝓞 D.host.E) S) = Submodule.span (M p).L.O (L.bc p '' S) := by
  apply le_antisymm
  · rw [lattice₂, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_induction
      (p := fun x _ => L.bc p x ∈ Submodule.span (M p).L.O (L.bc p '' S)) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    · rw [map_zero]
      exact zero_mem _
    · intro y z _ _ hy hz
      rw [map_add]
      exact add_mem hy hz
    · intro o y _ hy
      rw [bc_smulO]
      exact Submodule.smul_mem _ (⟨_, iE_mem_LO hA p o⟩ : (M p).L.O) hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem localLattice_sup (L : LocSp D M) (p : PlF D) (A B : Submodule (𝓞 D.host.E) (VS D).V) :
    lattice₂ L p (A ⊔ B) = lattice₂ L p A ⊔ lattice₂ L p B := by
  apply le_antisymm
  · rw [lattice₂, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))
  · exact sup_le (Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (le_sup_left : A ≤ A ⊔ B))))
      (Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (le_sup_right : B ≤ A ⊔ B))))

def locDat (hA : ∀ p, Agree δ M p) : Formalism.L2.SG.TermLoc.LocDat D := ⟨δ, M, hA⟩

theorem latP_XS (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    lattice₂ L p (XS D F) =
      Submodule.span (M p).L.O (Set.range fun a : Fin D.R.rS => frFac δ p a.castSucc • L.bc p (F.e a)) := by
  have hdiff := Formalism.L2.SG.Pf.locDiffC_holds D (locDat hA) p
  rw [XS, localLattice_span₂ hA]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, ⟨a, x, hx, rfl⟩, rfl⟩
    rw [L.bc_smul]
    have hm : (D.s.atP p).ιE x ∈ Submodule.span (M p).L.O {frFac δ p a.castSucc} := by
      have h0 := hdiff a.castSucc
      simp only [locDat, Fin.val_castSucc] at h0
      have h1 : (D.s.atP p).ιE x ∈ Submodule.span (M p).L.O ((D.s.atP p).ιE ''
          ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) :
            FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) :=
        Submodule.subset_span ⟨x, hx, rfl⟩
      exact h0 ▸ h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    rw [← hc, Subring.smul_def, smul_eq_mul, mul_smul]
    have := Submodule.smul_mem (Submodule.span (M p).L.O
      (Set.range fun a : Fin D.R.rS => frFac δ p a.castSucc • L.bc p (F.e a))) c (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at this
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : frFac δ p a.castSucc ∈ Submodule.span (M p).L.O ((D.s.atP p).ιE ''
        ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) := by
      have h0 := hdiff a.castSucc
      simp only [locDat, Fin.val_castSucc] at h0
      have h1 : frFac δ p a.castSucc ∈ Submodule.span (M p).L.O {frFac δ p a.castSucc} :=
        Submodule.mem_span_singleton_self _
      exact h0.symm ▸ h1
    let f : (D.s.atP p).Ep →ₗ[(M p).L.O] L.V p :=
      (LinearMap.toSpanSingleton (D.s.atP p).Ep (L.V p) (L.bc p (F.e a))).restrictScalars (M p).L.O
    have h2 := Submodule.apply_mem_span_image_of_mem_span f hm
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x • F.e a, ⟨a, x, ?_, rfl⟩, ?_⟩
    · simpa using hx
    · simp [f, L.bc_smul]

section Scal

theorem phi_inv_mem (hA : ∀ p, Agree δ M p) (p : PlF D) (a : Fin (D.R.rS + 1)) :
    ∃ w ∈ (M p).L.O, w * frFac δ p a = 1 := by
  refine ⟨(Formalism.L2.SG.Pf.BBTie.btT (locDat hA) p) ^ (D.R.rS - a.val), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (D.R.rS - a.val) with h | h
    · rw [h, pow_zero]; exact (M p).L.O.one_mem
    · exact (M p).L.O.pow_mem (Formalism.L2.SG.Pf.BBTie.bt_T_mem (locDat hA) p
        (Formalism.L2.SG.Pf.locDiffC_holds D (locDat hA)) (by omega)) _
  · unfold frFac
    exact Ring.mul_inverse_cancel _ ((Formalism.L2.SG.Pf.BBTie.bt_T_unit (locDat hA) p).pow _)

theorem split_some_typed (hA : ∀ p, Agree δ M p) (p : PlF D) {g : Loc.SplitG (M p).L}
    (hs : (M p).split = some g) : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (PI.CntNotIntW.split_ell δ hA p g hs).2

theorem split_none_untyped (hA : ∀ p, Agree δ M p) (p : PlF D) (hs : (M p).split = none) :
    Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
  intro h
  have h2 := (D.s_split p).2 h
  have hm := (hA p).2.2.2.2.2
  rw [hs] at hm
  rcases hsp : (D.s.atP p).split with _ | sg
  · rw [hsp] at h2; exact absurd h2 (by simp)
  · rw [hsp] at hm; exact hm.elim

theorem q_eq_ell (hA : ∀ p, Agree δ M p) (p : PlF D) {g : Loc.SplitG (M p).L} (hs : (M p).split = some g) :
    ((g.q : (D.s.atP p).Fp)) = ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) := by
  exact (PI.CntNotIntW.split_ell δ hA p g hs).1

theorem inv_unique {R : Type} [CommRing R] {x w n : R} (hx : x * n = 1) (hw : w * n = 1) : x = w := by
  calc x = x * (w * n) := by rw [hw, mul_one]
    _ = w * (x * n) := by ring
    _ = w := by rw [hx, mul_one]

theorem gS_ne : ((Lat.gS D : ℕ) : D.host.E) ≠ 0 := by
  refine Nat.cast_ne_zero.2 ?_
  show D.host.g 0 * D.host.g 1 ≠ 0
  exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem iE_gS_inv_mul (p : PlF D) :
    (D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ * ((Lat.gS D : ℕ) : (D.s.atP p).Ep) = 1 := by
  rw [← map_natCast (D.s.atP p).ιE (Lat.gS D), ← map_mul, inv_mul_cancel₀ gS_ne, map_one]

theorem gS_inv_mem (hA : ∀ p, Agree δ M p) (p : PlF D) (hs : (M p).split = none) :
    (D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ ∈ (M p).L.O := by
  have hun := split_none_untyped hA p hs
  have hℓ : (Loc.resChar p).Prime := (D.s.atP p).ellPrime.out
  have hnd : ¬ Loc.resChar p ∣ Lat.gS D := by
    intro hd
    rcases (Nat.Prime.dvd_mul hℓ).1 hd with h | h
    · have h' := (Nat.prime_dvd_prime_iff_eq hℓ (D.host.g_prime 0)).1 h
      exact hun (by simp [h'])
    · have h' := (Nat.prime_dvd_prime_iff_eq hℓ (D.host.g_prime 1)).1 h
      exact hun (by simp [h'])
  obtain ⟨w, hw⟩ := Formalism.L2.SG.Pf.BBTie.bt_natF_unit p (Lat.gS D) hnd
  have e : (D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) :=
    inv_unique (iE_gS_inv_mul p) (by
      rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, hw, map_one])
  rw [e, (hA p).2.2.2.1]
  exact PI.CntNotIntW.algMap_mem_O D p _ w.2

def gj (p : PlF D) : ℕ := Lat.gS D / Loc.resChar p

theorem typed_cases (hA : ∀ p, Agree δ M p) (p : PlF D) {g : Loc.SplitG (M p).L} (hs : (M p).split = some g) :
    Loc.resChar p * gj p = Lat.gS D ∧ ¬ Loc.resChar p ∣ gj p ∧ gpart p = Loc.resChar p := by
  have hmem := split_some_typed hA p hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have h0 := D.host.g_prime 0
  have h1 := D.host.g_prime 1
  have hne := D.host.g_ne
  rcases hmem with h | h
  · refine ⟨?_, ?_, ?_⟩
    · simp only [gj, Lat.gS, h]
      exact Nat.mul_div_cancel' (dvd_mul_right _ _)
    · simp only [gj, Lat.gS, h, Nat.mul_div_cancel_left _ h0.pos]
      exact fun hd => hne ((Nat.prime_dvd_prime_iff_eq h0 h1).1 hd)
    · simp only [gpart, h, if_true]
  · refine ⟨?_, ?_, ?_⟩
    · simp only [gj, Lat.gS, h]
      exact Nat.mul_div_cancel' (dvd_mul_left _ _)
    · simp only [gj, Lat.gS, h, Nat.mul_div_cancel _ h1.pos]
      exact fun hd => hne ((Nat.prime_dvd_prime_iff_eq h1 h0).1 hd).symm
    · simp only [gpart, h, if_neg (Ne.symm hne), if_true]

theorem q_gS_inv_mem (hA : ∀ p, Agree δ M p) (p : PlF D) {g : Loc.SplitG (M p).L} (hs : (M p).split = some g) :
    (D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)
      ∈ (M p).L.O := by
  obtain ⟨h1, h2, -⟩ := typed_cases hA p hs
  obtain ⟨w, hw⟩ := Formalism.L2.SG.Pf.BBTie.bt_natF_unit p (gj p) h2
  have hu := iE_gS_inv_mul (D := D) p
  have hw' : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * ((gj p : ℕ) : (D.s.atP p).Ep) = 1 := by
    rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, hw, map_one]
  have hgs : ((Lat.gS D : ℕ) : (D.s.atP p).Ep) =
      ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) * ((gj p : ℕ) : (D.s.atP p).Ep) := by
    rw [← h1, Nat.cast_mul]
  have key : (D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) := by
    rw [q_eq_ell hA p hs, map_natCast]
    calc _ = (D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ * ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) *
          (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * ((gj p : ℕ) : (D.s.atP p).Ep)) := by
          rw [hw', mul_one]
      _ = ((D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ *
          (((Loc.resChar p : ℕ) : (D.s.atP p).Ep) * ((gj p : ℕ) : (D.s.atP p).Ep))) *
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) := by ring
      _ = _ := by rw [← hgs, hu, one_mul]
  rw [key, (hA p).2.2.2.1]
  exact PI.CntNotIntW.algMap_mem_O D p _ w.2

theorem qinv_gS_mem (hA : ∀ p, Agree δ M p) (p : PlF D) {g : Loc.SplitG (M p).L} (hs : (M p).split = some g) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) * (D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E)
      ∈ (M p).L.O := by
  have hq0 : (g.q : (D.s.atP p).Fp) ≠ 0 := by
    intro h
    apply g.q_irr.ne_zero
    exact Subtype.ext h
  have hℓ : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ≠ 0 := by
    rw [← q_eq_ell hA p hs]
    exact hq0
  obtain ⟨h1, -, -⟩ := typed_cases hA p hs
  rw [q_eq_ell hA p hs, ← h1, Nat.cast_mul, map_mul, map_natCast, map_natCast,
    ← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) (Loc.resChar p), ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hℓ, map_one, one_mul]
  exact natCast_mem _ _

theorem phi_mem_typed (hA : ∀ p, Agree δ M p) (p : PlF D) {g : Loc.SplitG (M p).L} (hs : (M p).split = some g)
    (a : Fin (D.R.rS + 1)) : frFac δ p a ∈ (M p).L.O := by
  obtain ⟨e1, -, e3⟩ := typed_cases hA p hs
  have hδ := PI.CntNotIntW.deltaInvG_of
    (PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
      (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
      PI.CntNotIntW.small_powers_bound) PI.CntNotIntW.different_lattice_index D δ M hA p g hs
  have hδ0 : δ p ≠ 0 := (hA p).2.1
  set x := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * (((gj p : ℕ) : (D.s.atP p).Ep)) with hx
  have hxO : x ∈ (M p).L.O := (M p).L.O.mul_mem (algebraMap_mem_LO _ hδ) (natCast_mem _ _)
  have hj : ((gj p : ℕ) : D.host.E) ≠ 0 := by
    have : gj p ≠ 0 := by
      intro h0; rw [h0, mul_zero] at e1
      exact gS_ne (by rw [← e1]; simp)
    exact_mod_cast this
  have hl : ((Loc.resChar p : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.s.atP p).ellPrime.out.ne_zero
  have huP : ((gj p : ℕ) : D.host.E) * (uP p : D.host.E) = 1 := by
    unfold uP
    rw [e3, ← e1]
    push_cast
    field_simp
  have hxT : x * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) = 1 := by
    rw [hx]
    calc algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * ((gj p : ℕ) : (D.s.atP p).Ep) *
          (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E))
        = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((δ p)⁻¹ * δ p) *
            (D.s.atP p).ιE (((gj p : ℕ) : D.host.E) * (uP p : D.host.E)) := by
          rw [map_mul, map_mul, map_natCast]; ring
      _ = 1 := by rw [inv_mul_cancel₀ hδ0, huP, map_one, map_one, one_mul]
  have hu : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
      (D.R.rS - a.val)) := (Formalism.L2.SG.Pf.BBTie.bt_T_unit (locDat hA) p).pow _
  have hinv : frFac δ p a = x ^ (D.R.rS - a.val) := by
    unfold frFac
    calc Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
          (D.R.rS - a.val))
        = (x ^ (D.R.rS - a.val) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) *
            (D.s.atP p).ιE (uP p : D.host.E)) ^ (D.R.rS - a.val)) *
          Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
            (D.R.rS - a.val)) := by rw [← mul_pow, hxT, one_pow, one_mul]
      _ = x ^ (D.R.rS - a.val) := by rw [mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
  rw [hinv]
  exact (M p).L.O.pow_mem hxO _

end Scal

section Span

theorem smul_mem_O {p : PlF D} {V : Type} [AddCommGroup V] [Module (D.s.atP p).Ep V]
    {S : Submodule (M p).L.O V} {c : (D.s.atP p).Ep} (hc : c ∈ (M p).L.O) {v : V} (hv : v ∈ S) : c • v ∈ S := by
  exact S.smul_mem ⟨c, hc⟩ hv

theorem frame_g_zero_inl (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (a : Fin (D.R.rS + 1)) :
    g0 L δ p F0 F' (Sum.inl a) = frFac δ p a • L.bc p (F0.fvec a) := rfl

theorem frame_g_zero_inr (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (a : Fin (D.R.rS + 1)) :
    g0 L δ p F0 F' (Sum.inr a) = frFac δ p a • L.bc p (F'.fl.fvec a) := rfl

theorem locFam_none (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (hs : (M p).split = none) : locFam L δ p F0 F' = g0 L δ p F0 F' := by
  simp only [locFam, hs]

theorem amat_inl (p : PlF D) (g : Loc.SplitG (M p).L) {V : Type} [AddCommGroup V] [Module (D.s.atP p).Ep V]
    (v : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → V) (a : Fin (D.R.rS + 1)) :
    ∑ d, amat p g d (Sum.inl a) • v d = v (Sum.inl a) := by
  simp only [amat, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
    Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_smul, one_smul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem amat_inr (p : PlF D) (g : Loc.SplitG (M p).L) {V : Type} [AddCommGroup V] [Module (D.s.atP p).Ep V]
    (v : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → V) (a : Fin (D.R.rS + 1)) :
    ∑ d, amat p g d (Sum.inr a) • v d =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • (v (Sum.inr a) - v (Sum.inl a)) := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ x, amat p g (Sum.inl x) (Sum.inr a) • v (Sum.inl x) = -(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • v (Sum.inl a)) := by
    rw [Finset.sum_eq_single a]
    · show ((-algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) a a • v (Sum.inl a) = _
      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, neg_smul]
    · intro b _ hb
      show ((-algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) b a • v (Sum.inl b) = 0
      rw [Matrix.smul_apply, Matrix.one_apply_ne hb, smul_zero, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have h2 : ∑ x, amat p g (Sum.inr x) (Sum.inr a) • v (Sum.inr x) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • v (Sum.inr a) := by
    rw [Finset.sum_eq_single a]
    · show (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) a a • v (Sum.inr a) = _
      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    · intro b _ hb
      show (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) b a • v (Sum.inr b) = 0
      rw [Matrix.smul_apply, Matrix.one_apply_ne hb, smul_zero, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [h1, h2, smul_sub]
  abel

theorem locFam_some_inl (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') {g : Loc.SplitG (M p).L} (hs : (M p).split = some g) (a : Fin (D.R.rS + 1)) :
    locFam L δ p F0 F' (Sum.inl a) = g0 L δ p F0 F' (Sum.inl a) := by
  simp only [locFam, hs]
  exact amat_inl p g _ a

theorem locFam_some_inr (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') {g : Loc.SplitG (M p).L} (hs : (M p).split = some g) (a : Fin (D.R.rS + 1)) :
    locFam L δ p F0 F' (Sum.inr a) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
      (g0 L δ p F0 F' (Sum.inr a) - g0 L δ p F0 F' (Sum.inl a)) := by
  simp only [locFam, hs]
  exact amat_inr p g _ a

end Span

section SpanMain

theorem fvec_cast {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : F.fvec a.castSucc = F.e a := by
  simp [FlagG.fvec]

def NG (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Submodule (M p).L.O (L.V p) :=
  Submodule.span (M p).L.O (L.bc p '' (Set.range F0.fvec ∪
    Set.range fun b => (((Lat.gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)))

def NX (δ : ∀ p : PlF D, (D.s.atP p).Fp) (L : LocSp D M) (p : PlF D) {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    Submodule (M p).L.O (L.V p) :=
  Submodule.span (M p).L.O (Set.range fun a : Fin D.R.rS => frFac δ p a.castSucc • L.bc p (F.e a))

set_option maxHeartbeats 1000000 in
theorem latP_MMof (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    lattice₂ L p (MMof D F0 F') = NG L p F0 F' ⊔ NX δ L p F0 ⊔ NX δ L p F'.fl := by
  have e1 : lattice₂ L p (MMg D F0 F') = NG L p F0 F' := by
    unfold MMg NG; exact localLattice_span₂ hA L p _
  have e2 : lattice₂ L p (XS D F0) = NX δ L p F0 := latP_XS hA L p F0
  have e3 : lattice₂ L p (XS D F'.fl) = NX δ L p F'.fl := latP_XS hA L p F'.fl
  rw [R3.MMof_eq, R3.BB, localLattice_sup, localLattice_sup]
  exact congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) e1 e2) e3

theorem hf'_eq (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    L.bc p (F'.fl.fvec b) - L.bc p (F0.fvec b) = (D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E) •
      L.bc p ((((Lat.gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) := by
  rw [L.bc_smul, smul_smul, ← map_mul, mul_inv_cancel₀ gS_ne, map_one, one_smul, map_sub]

theorem hd_eq (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    L.bc p ((((Lat.gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) =
      (D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ • (L.bc p (F'.fl.fvec b) - L.bc p (F0.fvec b)) := by
  rw [L.bc_smul, map_sub]

theorem gS_mem_O (p : PlF D) : (D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E) ∈ (M p).L.O := by
  rw [map_natCast]
  exact natCast_mem _ _

theorem mem_NG_f (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (a : Fin (D.R.rS + 1)) : L.bc p (F0.fvec a) ∈ NG L p F0 F' := Submodule.subset_span ⟨F0.fvec a, Or.inl ⟨a, rfl⟩, rfl⟩

theorem mem_NG_d (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    L.bc p ((((Lat.gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) ∈ NG L p F0 F' := Submodule.subset_span ⟨_, Or.inr ⟨b, rfl⟩, rfl⟩

theorem mem_NG_f' (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (b : Fin (D.R.rS + 1)) : L.bc p (F'.fl.fvec b) ∈ NG L p F0 F' := by
  have h := hf'_eq L p F0 F' b
  have e : L.bc p (F'.fl.fvec b) = L.bc p (F0.fvec b) + (D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E) •
      L.bc p ((((Lat.gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) := by
    rw [← h]; abel
  rw [e]
  exact add_mem (mem_NG_f L p F0 F' b)
    (Submodule.smul_mem _ (⟨_, gS_mem_O (M := M) p⟩ : (M p).L.O) (mem_NG_d L p F0 F' b))

theorem mem_NX (L : LocSp D M) (p : PlF D) {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) :
    frFac δ p a.castSucc • L.bc p (F.e a) ∈ NX δ L p F := Submodule.subset_span ⟨a, rfl⟩

theorem locFam_inl (L : LocSp D M) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (a : Fin (D.R.rS + 1)) :
    locFam L δ p F0 F' (Sum.inl a) = frFac δ p a • L.bc p (F0.fvec a) := by
  rcases h : (M p).split with _ | g
  · rw [locFam_none L p F0 F' h]
    exact frame_g_zero_inl L p F0 F' a
  · rw [locFam_some_inl L p F0 F' h]
    exact frame_g_zero_inl L p F0 F' a

theorem bc_f_eq (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (a : Fin (D.R.rS + 1)) :
    ∃ w ∈ (M p).L.O, L.bc p (F0.fvec a) = w • locFam L δ p F0 F' (Sum.inl a) := by
  obtain ⟨w, hw, hw1⟩ := phi_inv_mem hA p a
  exact ⟨w, hw, by rw [locFam_inl, smul_smul, hw1, one_smul]⟩

set_option maxHeartbeats 1000000 in

theorem span_le_none (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (hs : (M p).split = none) :
    Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) ≤ NG L p F0 F' ⊔ NX δ L p F0 ⊔ NX δ L p F'.fl := by
  have hlast : frFac δ p (Fin.last D.R.rS) = 1 := by simp [frFac]
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [locFam_none L p F0 F' hs]
  rcases i with a | a
  · rw [frame_g_zero_inl]
    cases a using Fin.lastCases with
    | last =>
      rw [hlast, one_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (mem_NG_f L p F0 F' _))
    | cast b =>
      rw [fvec_cast]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (mem_NX L p F0 b))
  · rw [frame_g_zero_inr]
    cases a using Fin.lastCases with
    | last =>
      rw [hlast, one_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (mem_NG_f' L p F0 F' _))
    | cast b =>
      rw [fvec_cast]
      exact Submodule.mem_sup_right (mem_NX L p F'.fl b)

set_option maxHeartbeats 1000000 in

theorem le_span_none (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (hs : (M p).split = none) :
    NG L p F0 F' ⊔ NX δ L p F0 ⊔ NX δ L p F'.fl ≤ Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) := by
  have hF0 : ∀ b, L.bc p (F0.fvec b) ∈ Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) := by
    intro b
    obtain ⟨w, hw, e⟩ := bc_f_eq hA L p F0 F' b
    rw [e]
    exact Submodule.smul_mem _ (⟨w, hw⟩ : (M p).L.O) (Submodule.subset_span ⟨_, rfl⟩)
  have hF' : ∀ b, L.bc p (F'.fl.fvec b) ∈ Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) := by
    intro b
    obtain ⟨w, hw, hw1⟩ := phi_inv_mem hA p b
    have e : L.bc p (F'.fl.fvec b) = w • locFam L δ p F0 F' (Sum.inr b) := by
      rw [locFam_none L p F0 F' hs, frame_g_zero_inr, smul_smul, hw1, one_smul]
    rw [e]
    exact Submodule.smul_mem _ (⟨w, hw⟩ : (M p).L.O) (Submodule.subset_span ⟨_, rfl⟩)
  refine sup_le (sup_le ?_ ?_) ?_
  · unfold NG
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact hF0 a
    · rw [hd_eq]
      exact Submodule.smul_mem _ (⟨_, gS_inv_mem hA p hs⟩ : (M p).L.O) (sub_mem (hF' b) (hF0 b))
  · unfold NX
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    beta_reduce
    rw [← fvec_cast, ← locFam_inl]
    exact Submodule.subset_span ⟨_, rfl⟩
  · unfold NX
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have e : frFac δ p a.castSucc • L.bc p (F'.fl.e a) = locFam L δ p F0 F' (Sum.inr a.castSucc) := by
      rw [locFam_none L p F0 F' hs, frame_g_zero_inr, fvec_cast]
    beta_reduce
    rw [e]
    exact Submodule.subset_span ⟨_, rfl⟩

end SpanMain

section SpanG

set_option maxHeartbeats 1000000 in

theorem span_le_some (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {g : Loc.SplitG (M p).L} (hs : (M p).split = some g) :
    Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) ≤ NG L p F0 F' ⊔ NX δ L p F0 ⊔ NX δ L p F'.fl := by
  have hlast : frFac δ p (Fin.last D.R.rS) = 1 := by simp [frFac]
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rcases i with a | a
  · rw [locFam_inl]
    cases a using Fin.lastCases with
    | last =>
      rw [hlast, one_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (mem_NG_f L p F0 F' _))
    | cast b =>
      rw [fvec_cast]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (mem_NX L p F0 b))
  · rw [locFam_some_inr L p F0 F' hs, frame_g_zero_inr, frame_g_zero_inl, ← smul_sub, hf'_eq, smul_smul, smul_smul]
    have hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) * frFac δ p a * (D.s.atP p).ιE ((Lat.gS D : ℕ) : D.host.E) ∈ (M p).L.O := by
      rw [mul_comm (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)), mul_assoc]
      exact mul_mem (phi_mem_typed hA p hs a) (qinv_gS_mem hA p hs)
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.smul_mem _ (⟨_, hc⟩ : (M p).L.O) (mem_NG_d L p F0 F' a)))

set_option maxHeartbeats 1000000 in

theorem le_span_some (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {g : Loc.SplitG (M p).L} (hs : (M p).split = some g) :
    NG L p F0 F' ⊔ NX δ L p F0 ⊔ NX δ L p F'.fl ≤ Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) := by
  have hq0 : (g.q : (D.s.atP p).Fp) ≠ 0 := by
    intro h
    apply g.q_irr.ne_zero
    exact Subtype.ext h
  have hq : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have haq : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) ∈ (M p).L.O := by
    rw [(hA p).2.2.2.1]
    exact PI.CntNotIntW.algMap_mem_O D p _ g.q.2
  have hF0 : ∀ b, L.bc p (F0.fvec b) ∈ Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) := by
    intro b
    obtain ⟨w, hw, e⟩ := bc_f_eq hA L p F0 F' b
    rw [e]
    exact Submodule.smul_mem _ (⟨w, hw⟩ : (M p).L.O) (Submodule.subset_span ⟨_, rfl⟩)
  refine sup_le (sup_le ?_ ?_) ?_
  · unfold NG
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact hF0 a
    · obtain ⟨w, hw, hw1⟩ := phi_inv_mem hA p b
      have e : L.bc p (F'.fl.fvec b) - L.bc p (F0.fvec b) = (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w) • locFam L δ p F0 F' (Sum.inr b) := by
        rw [locFam_some_inr L p F0 F' hs, frame_g_zero_inr, frame_g_zero_inl, ← smul_sub, smul_smul, smul_smul]
        have h2 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) * frFac δ p b = 1 := by
          calc _ = (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) * (w * frFac δ p b) := by ring
            _ = 1 := by rw [hq, hw1, one_mul]
        rw [h2, one_smul]
      have hc : (D.s.atP p).ιE (((Lat.gS D : ℕ) : D.host.E))⁻¹ * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w) ∈ (M p).L.O := by
        rw [← mul_assoc]
        exact mul_mem (q_gS_inv_mem hA p hs) hw
      rw [hd_eq, e, smul_smul]
      exact Submodule.smul_mem _ (⟨_, hc⟩ : (M p).L.O) (Submodule.subset_span ⟨_, rfl⟩)
  · unfold NX
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    beta_reduce
    rw [← fvec_cast, ← locFam_inl]
    exact Submodule.subset_span ⟨_, rfl⟩
  · unfold NX
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    beta_reduce
    have e : frFac δ p a.castSucc • L.bc p (F'.fl.e a) =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • locFam L δ p F0 F' (Sum.inr a.castSucc) + locFam L δ p F0 F' (Sum.inl a.castSucc) := by
      rw [locFam_some_inr L p F0 F' hs, smul_smul, hq, one_smul, frame_g_zero_inr, frame_g_zero_inl, locFam_inl, fvec_cast,
        fvec_cast, sub_add_cancel]
    rw [e]
    exact add_mem (Submodule.smul_mem _ (⟨_, haq⟩ : (M p).L.O) (Submodule.subset_span ⟨_, rfl⟩))
      (Submodule.subset_span ⟨_, rfl⟩)

theorem span_locFam (hA : ∀ p, Agree δ M p) (L : LocSp D M) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) = lattice₂ L p (MMof D F0 F') := by
  rw [latP_MMof hA]
  rcases h : (M p).split with _ | g
  · exact le_antisymm (span_le_none hA L p F0 F' h) (le_span_none hA L p F0 F' h)
  · exact le_antisymm (span_le_some hA L p F0 F' h) (le_span_some hA L p F0 F' h)

end SpanG

section Indep

theorem linIndep_of_gram_unit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → V)
    (hdet : IsUnit (Matrix.of fun a b => H.h (g b) (g a)).det) : LinearIndependent M.L.O g := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hzero : ∀ y, H.h 0 y = 0 := fun y => by
    have e := H.h_add_left 0 0 y
    rw [add_zero] at e
    linear_combination -e
  have e : ∀ a, ∑ b, (c b : E) * H.h (g b) (g a) = 0 := by
    intro a
    let φ : V →+ E := ⟨⟨fun x => H.h x (g a), hzero _⟩, fun x y => H.h_add_left x y _⟩
    calc ∑ b, (c b : E) * H.h (g b) (g a) = ∑ b, H.h (c b • g b) (g a) :=
          Finset.sum_congr rfl fun b _ => (H.h_smul_left (c b : E) (g b) (g a)).symm
      _ = φ (∑ b, c b • g b) := (map_sum φ _ _).symm
      _ = 0 := by rw [hc]; exact hzero _
  have hmv : Matrix.mulVec (Matrix.of fun a b => H.h (g b) (g a)) (fun b => (c b : E)) = 0 := by
    funext a
    change ∑ b, H.h (g b) (g a) * (c b : E) = 0
    rw [← e a]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have h0 : (fun b => (c b : E)) = 0 := by
    have h1 := congrArg (Matrix.mulVec (Matrix.of fun a b => H.h (g b) (g a))⁻¹) hmv
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  exact Subtype.ext (congrFun h0 i)

theorem gaLoc_eq_diag (p : PlF D) (T T' : D.host.E) (Z : MatZ D) :
    GaLoc M δ p T T' Z = Matrix.diagonal (fun a => (M p).L.cj (phi δ p a)) * (Ga T T' Z).map (D.s.atP p).ιE *
      Matrix.diagonal (phi δ p) := by
  ext a b
  simp only [GaLoc, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  ring

theorem phi_unit (hA : ∀ p, Agree δ M p) (p : PlF D) (i : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    IsUnit (phi δ p i) := by
  have hg : gpart p ≠ 0 := by
    unfold gpart
    split_ifs
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact one_ne_zero
  have hgS : Lat.gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hu : (uP p : D.host.E) ≠ 0 := by
    rw [Rat.cast_ne_zero]
    exact div_ne_zero (Nat.cast_ne_zero.2 hg) (Nat.cast_ne_zero.2 hgS)
  have hx : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) :=
    ((hA p).2.1.isUnit.map _).mul (hu.isUnit.map _)
  have hk : ∀ k : ℕ, IsUnit (Ring.inverse
      ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ k)) := by
    intro k
    obtain ⟨u, hu'⟩ := hx.pow k
    rw [← hu', Ring.inverse_unit]
    exact (u⁻¹).isUnit
  rcases i with a | a
  · exact hk _
  · exact hk _

theorem prod_unit {ι R : Type} [CommMonoid R] (s : Finset ι) (f : ι → R) (h : ∀ i, IsUnit (f i)) :
    IsUnit (∏ i ∈ s, f i) := Finset.prod_induction f IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one fun i _ => h i

theorem gaPlus_det_unit (hA : ∀ p, Agree δ M p) (p : PlF D) (T T' : D.host.E) (Z : MatZ D)
    (hdet : (Ga T T' Z).det ≠ 0) : IsUnit (GaPlus M δ p T T' Z).det := by
  have hmap : ((Ga T T' Z).map (D.s.atP p).ιE).det = (D.s.atP p).ιE (Ga T T' Z).det :=
    (RingHom.map_det _ _).symm
  have hGL : IsUnit (GaLoc M δ p T T' Z).det := by
    rw [gaLoc_eq_diag, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hmap]
    exact ((prod_unit _ _ fun i => (phi_unit hA p i).map (M p).L.cj).mul ((Ne.isUnit hdet).map _)).mul
      (prod_unit _ _ fun i => phi_unit hA p i)
  rcases h : (M p).split with _ | g
  · simp only [GaPlus, h]
    exact hGL
  · have hq0 : (g.q : (D.s.atP p).Fp) ≠ 0 := by
      intro hh
      apply g.q_irr.ne_zero
      exact Subtype.ext hh
    have hqi : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) := (inv_ne_zero hq0).isUnit.map _
    simp only [GaPlus, h]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have hAd : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)
        (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
        ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep))).det := by
      rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_smul, Matrix.det_one, mul_one, one_mul]
      exact hqi.pow _
    have hmc : ∀ N : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
        (N.map (M p).L.cj).det = (M p).L.cj N.det := fun N =>
      (RingHom.map_det ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) N).symm
    rw [hmc]
    exact ((hAd.map (M p).L.cj).mul hGL).mul hAd

end Indep

section Final

theorem ga_det_ne {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (hG : Gflag F0 F'.fl ≠ 0) (hC : IsCompl (UPair D F0 F') (orthK (VS D).hT (UPair D F0 F'))) :
    (Ga T T' (ZhatL (lf D F0) F')).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [ga_eq] at hc
  set w : (VS D).V := ∑ b, c b • vfam F0 F' b with hw
  have hvU : ∀ b, vfam F0 F' b ∈ UPair D F0 F' := fun b => by
    rcases b with a | a
    · exact Submodule.subset_span (Or.inl ⟨a, rfl⟩)
    · exact Submodule.subset_span (Or.inr ⟨a, rfl⟩)
  have hwU : w ∈ UPair D F0 F' := Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hvU b)
  have hperp : ∀ a, (VS D).hT (vfam F0 F' a) w = 0 := fun a => by
    have := congrFun hc a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, brS] at this
    rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]; exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hwO : w ∈ orthK (VS D).hT (UPair D F0 F') := by
    simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact hperp (Sum.inl a)
      · exact hperp (Sum.inr a)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
    | smul s y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]
  have hw0 : w = 0 := by
    have := hC.disjoint
    rw [Submodule.disjoint_def] at this
    exact this w hwU hwO
  have hli := PI.PairCorankPos.W.linIndep F0 F'.fl hG
  apply hc0
  funext b
  exact Fintype.linearIndependent_iff.1 hli c (by rw [← hw0, hw]; rfl) b

theorem frameBasisL_holds : FrameBasisL := by
  intro D δ M hA L u u' hT F0 what₂ hR F' hz hP p
  refine ⟨?_, span_locFam hA L p F0 F'⟩
  have hG : Gflag F0 F'.fl ≠ 0 := PairSpanDimension.totPos_ne_zero hP
  obtain ⟨hC, -, -, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR _ F' hz rfl hP
  apply linIndep_of_gram_unit (L.H p)
  rw [← gaPlus_eq_gram L δ p F0 F']
  exact gaPlus_det_unit hA p _ _ _ (ga_det_ne F0 F' hG hC)

end Final

end Formalism.L2.SG.Pf.Cnt.DualityBasisChange
