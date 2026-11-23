import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FramePrim

section Quad

open ValuativeRel Polynomial

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E)

theorem exists_quad (L : Formalism.MainNotions.S.Loc.LocE F E) (d : E) : ∃ t n : F, d * d - algebraMap F E t * d + algebraMap F E n = 0 := by
  haveI := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  set f : E →ₗ[F] E := Algebra.lmul F E d with hf
  have hmon : f.charpoly.Monic := LinearMap.charpoly_monic f
  have hdeg : f.charpoly.natDegree = 2 := by rw [LinearMap.charpoly_natDegree, L.rank]
  have h0 : aeval d f.charpoly = 0 := by
    have h1 := LinearMap.aeval_self_charpoly f
    have h2 : aeval f f.charpoly = Algebra.lmul F E (aeval d f.charpoly) := by
      rw [hf, Polynomial.aeval_algHom_apply]
    rw [h2] at h1
    have h3 := LinearMap.congr_fun h1 1
    simpa using h3
  have hs := hmon.as_sum
  rw [hdeg] at hs
  rw [hs] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_zero, pow_one, mul_one] at h0
  refine ⟨-f.charpoly.coeff 1, f.charpoly.coeff 0, ?_⟩
  rw [map_neg]
  linear_combination h0

theorem mem_O_of_quad (x : E) (a b : F) (h : x * x - algebraMap F E a * x + algebraMap F E b = 0)
    (ha : valuation F a ≤ 1) (hb : valuation F b ≤ 1) : x ∈ L.O := by
  rw [L.O_def]
  set a' : (valuation F).integer := ⟨a, (Valuation.mem_integer_iff _ _).2 ha⟩
  set b' : (valuation F).integer := ⟨b, (Valuation.mem_integer_iff _ _).2 hb⟩
  refine ⟨X ^ 2 - C a' * X + C b', ?_, ?_⟩
  · monicity!
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
    have ea : algebraMap (valuation F).integer E a' = algebraMap F E a := rfl
    have eb : algebraMap (valuation F).integer E b' = algebraMap F E b := rfl
    rw [ea, eb]
    linear_combination h

theorem inv_mem_O_of_quad (u : E) (t n : F) (h : u * u - algebraMap F E t * u + algebraMap F E n = 0)
    (hn : 1 ≤ valuation F n) (ht : valuation F t ≤ valuation F n) : ∃ w ∈ L.O, u * w = 1 := by
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0, map_zero] at hn; exact absurd hn (not_le.2 zero_lt_one)
  have hvn : valuation F n ≠ 0 := by rw [Ne, map_eq_zero]; exact hn0
  refine ⟨algebraMap F E n⁻¹ * (algebraMap F E t - u), ?_, ?_⟩
  · refine mem_O_of_quad L _ (t * n⁻¹) n⁻¹ ?_ ?_ ?_
    · have e : algebraMap F E n * algebraMap F E n⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hn0, map_one]
      simp only [map_mul]
      linear_combination (algebraMap F E n⁻¹ * algebraMap F E n⁻¹) * h - algebraMap F E n⁻¹ * e
    · rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ ht zero_le'
    · rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn
  · have e : algebraMap F E n * algebraMap F E n⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hn0, map_one]
    linear_combination (-(algebraMap F E n⁻¹)) * h + e

theorem exists_shift_inv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (d : E), d ∉ L.O →
    ∃ s ∈ L.O, ∃ w ∈ L.O, (d + s) * w = 1 := by
  intro F _ _ _ E _ _ _ L d hd
  obtain ⟨t, n, h⟩ := exists_quad L d
  have hnot : ¬ (valuation F t ≤ 1 ∧ valuation F n ≤ 1) := fun hh => hd (mem_O_of_quad L d t n h hh.1 hh.2)
  by_cases hc : 1 ≤ valuation F n ∧ valuation F t ≤ valuation F n
  · obtain ⟨w, hw, hdw⟩ := inv_mem_O_of_quad L d t n h hc.1 hc.2
    exact ⟨0, L.O.zero_mem, w, hw, by rw [add_zero]; exact hdw⟩
  · have ht1 : 1 < valuation F t ∧ valuation F n < valuation F t := by
      by_cases h1 : 1 ≤ valuation F n
      · have h2 : valuation F n < valuation F t := not_le.1 (fun hh => hc ⟨h1, hh⟩)
        exact ⟨not_le.1 (fun hh => hnot ⟨hh, le_trans h2.le hh⟩), h2⟩
      · have h1' : valuation F n < 1 := not_le.1 h1
        have h3 : 1 < valuation F t := not_le.1 (fun hh => hnot ⟨hh, h1'.le⟩)
        exact ⟨h3, lt_trans h1' h3⟩
    have hv2 : valuation F (2 : F) ≤ 1 := by
      have : (2 : F) = 1 + 1 := by norm_num
      rw [this]
      exact le_trans (Valuation.map_add _ _ _) (by simp)
    have hn1 : valuation F (n + 1) < valuation F t :=
      lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ht1.2 (by simpa using ht1.1))
    have hn' : valuation F (t + (n + 1)) = valuation F t := Valuation.map_add_eq_of_lt_left _ hn1
    have ht' : valuation F (t + 2) ≤ valuation F t :=
      le_trans (Valuation.map_add _ _ _) (max_le le_rfl (le_trans hv2 ht1.1.le))
    have hq : (d + 1) * (d + 1) - algebraMap F E (t + 2) * (d + 1) + algebraMap F E (t + (n + 1)) = 0 := by
      simp only [map_add, map_one, map_ofNat]
      linear_combination h
    obtain ⟨w, hw, hdw⟩ := inv_mem_O_of_quad L (d + 1) (t + 2) (t + (n + 1)) hq
      (by rw [hn']; exact ht1.1.le) (by rw [hn']; exact ht')
    exact ⟨1, L.O.one_mem, w, hw, hdw⟩

end Quad

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V]
  [Module E V] (H : HermSp M V)

theorem h_add_right' (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem h_smul_right' (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_zero_right' (x : V) : H.h x 0 = 0 := by
  rw [H.h_herm 0 x, H.h_zero_left, map_zero]

end Herm

theorem mkW_mem_of_mem_img : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)) (n : V ≃ₗ[E] V), n ∈ Fr.N →
    ∀ v : ↥(H.perp (H.X Fr.f)), (v : V) ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L) → H.mkW Fr.f v ∈ L := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr L n hn v hv
  obtain ⟨u, hu, hnu⟩ := Submodule.mem_map.1 hv
  have hnu' : n u = v := hnu
  have hnS := Formalism.MainNotions.BridgeLemma.NSet_inv Fr (Formalism.MainNotions.BridgeLemma.mem_NSet_of_mem_N Fr hn)
  have h1 : n.symm (v : V) - v ∈ H.X Fr.f := hnS.2.2 v v.2
  rw [← hnu', LinearEquiv.symm_apply_apply, hnu'] at h1
  have hprF_add : ∀ a b : V, Fr.prF (a + b) = Fr.prF a + Fr.prF b := by
    intro a b
    unfold FrameD.prF
    simp only [H.h_add_left, add_smul, Finset.sum_add_distrib]
    abel
  have hprF_smul : ∀ (c : E) (a : V), Fr.prF (c • a) = c • Fr.prF a := by
    intro c a
    unfold FrameD.prF
    simp only [H.h_smul_left, smul_sub, Finset.smul_sum, mul_smul]
  have hes_e : ∀ c b : Fin r, H.h (Fr.es c) (Fr.e b) = if b = c then 1 else 0 := by
    intro c b
    rw [H.h_herm (Fr.e b) (Fr.es c)]
    show M.L.cj (H.h (Fr.f b.castSucc) (Fr.es c)) = _
    rw [Fr.h_es]
    split_ifs <;> simp
  have hprF_perp : ∀ a : V, Fr.prF a ∈ H.perp (H.X Fr.f) := by
    intro a y hy
    unfold HermSp.X at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      show H.h (Fr.prF a) (Fr.e b) = 0
      unfold FrameD.prF
      rw [Formalism.MainNotions.BridgeLemma.h_sub_left, Formalism.MainNotions.BridgeLemma.h_sub_left, Formalism.MainNotions.BridgeLemma.h_sum_left,
        Formalism.MainNotions.BridgeLemma.h_sum_left]
      have z1 : ∑ i, H.h a (Fr.es i) * H.h (Fr.e i) (Fr.e b) = 0 :=
        Finset.sum_eq_zero (fun i _ => by
          rw [show H.h (Fr.e i) (Fr.e b) = 0 from Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last i).ne), mul_zero])
      have z2 : ∑ i, H.h a (Fr.e i) * H.h (Fr.es i) (Fr.e b) = H.h a (Fr.e b) := by
        simp only [hes_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [Finset.sum_ite_eq]; simp
      rw [z1, z2]; ring
    | zero => exact h_zero_right' H _
    | add y y' _ _ ih ih' => rw [h_add_right', ih, ih', add_zero]
    | smul t y _ ih => rw [h_smul_right', ih, mul_zero]
  have hcls : ∀ a ∈ Fr.LamStd L, ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF a ∧ H.mkW Fr.f w ∈ L := by
    intro a ha
    unfold FrameD.LamStd at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact ha.2.2
    | zero =>
      refine ⟨0, ?_, by rw [map_zero]; exact L.zero_mem⟩
      unfold FrameD.prF; simp [H.h_zero_left]
    | add a b _ _ iha ihb =>
      obtain ⟨w, hw, hwL⟩ := iha
      obtain ⟨w', hw', hwL'⟩ := ihb
      exact ⟨w + w', by rw [Submodule.coe_add, hw, hw', hprF_add], by rw [map_add]; exact L.add_mem hwL hwL'⟩
    | smul c a _ iha =>
      obtain ⟨w, hw, hwL⟩ := iha
      refine ⟨(c : E) • w, ?_, ?_⟩
      · rw [Submodule.coe_smul, hw]
        exact (hprF_smul (c : E) a).symm
      · rw [map_smul]
        exact L.smul_mem c hwL
  obtain ⟨w, hw, hwL⟩ := hcls u hu
  have hup : u ∈ H.perp (H.X Fr.f) := by
    have e : u = (u - v) + v := by abel
    rw [e]
    exact Submodule.add_mem _ (Formalism.MainNotions.BridgeLemma.X_le_perp Fr h1) v.2
  have h2 : u - Fr.prF u ∈ H.X Fr.f := by
    have e : u - Fr.prF u = ∑ a, H.h u (Fr.es a) • Fr.e a := by
      unfold FrameD.prF
      have : ∑ a, H.h u (Fr.e a) • Fr.es a = 0 :=
        Finset.sum_eq_zero (fun a _ => by
          rw [show H.h u (Fr.e a) = 0 from hup _ (Submodule.subset_span ⟨a, rfl⟩), zero_smul])
      rw [this]; abel
    rw [e]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  have hvw : H.mkW Fr.f v = H.mkW Fr.f w := by
    unfold HermSp.mkW
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show (v : V) - w ∈ H.X Fr.f
    have e : (v : V) - w = -(u - v) + (u - Fr.prF u) := by rw [hw]; abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.neg_mem _ h1) h2
  rw [hvw]
  exact hwL

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V]
  [Module E V] {H : HermSp M V} {r : ℕ}

theorem coef_mem_O (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L)
    (n : V ≃ₗ[E] V) (hn : n ∈ Fr.N) (d : E) (x : V) (hx : x ∈ H.X Fr.f)
    (h : d • Fr.z + x ∈ img n (Fr.LamStd L)) : d ∈ M.L.O := by
  obtain ⟨xz, hxz, hxzL, hprim⟩ := hL.2.2
  have hvp : d • Fr.z + x ∈ H.perp (H.X Fr.f) :=
    Submodule.add_mem _ (Submodule.smul_mem _ d (Formalism.MainNotions.BridgeLemma.z_mem_perp Fr))
      (Formalism.MainNotions.BridgeLemma.X_le_perp Fr hx)
  have hB := mkW_mem_of_mem_img Fr L n hn ⟨_, hvp⟩ h
  have e : H.mkW Fr.f ⟨_, hvp⟩ = d • H.mkW Fr.f xz := by
    rw [← map_smul]
    unfold HermSp.mkW
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((d • Fr.z + x) - d • (xz : V)) ∈ H.X Fr.f
    rw [hxz, add_sub_cancel_left]
    exact hx
  by_contra hd
  obtain ⟨s, hs, w, hw, hsw⟩ := exists_shift_inv M.L d hd
  have hyL : H.mkW Fr.f ((d + s) • xz) ∈ L := by
    rw [map_smul, add_smul, ← e]
    exact L.add_mem hB (L.smul_mem (⟨s, hs⟩ : M.L.O) hxzL)
  have hmk : H.mkW Fr.f xz = ((⟨w, hw⟩ : M.L.O) : E) • H.mkW Fr.f ((d + s) • xz) := by
    rw [map_smul, smul_smul, mul_comm, hsw, one_smul]
  obtain ⟨b, hb⟩ := (hprim ⟨w, hw⟩ ((d + s) • xz) hyL hmk).exists_right_inv
  have hb' : w * (b : E) = 1 := by simpa using congrArg Subtype.val hb
  have hds : d + s = (b : E) := by
    calc d + s = (d + s) * (w * (b : E)) := by rw [hb', mul_one]
      _ = ((d + s) * w) * (b : E) := by ring
      _ = (b : E) := by rw [hsw, one_mul]
  apply hd
  have : d = (b : E) - s := by rw [← hds]; ring
  rw [this]
  exact M.L.O.sub_mem b.2 hs

end Local

theorem coef_integral : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∀ c : D.host.E, c • G.fl.z ∈ Lsub Λ G → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  intro D T G Z A hA Λ _ hloc c hc
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 hc).1
  have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
  have hxX : x ∈ Xsp G := hx
  have key : ∀ p, (D.s.atP p).ιE c ∈ (D.s.atP p).O := by
    intro p
    obtain ⟨n, hn, L, hL, hlat⟩ := hloc p
    have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
    have hf : (A p).f = GlobalTheory.LocOver.scaled Z p (frame G) := hA p
    have hz : (A p).z = baseChange₂ D p G.fl.z := by
      show (A p).f (Fin.last D.R.rS) = _
      rw [hA p]
      simp [frFac, frame, FlagG.fvec]
    have hxp : baseChange₂ D p x ∈ (locH Z p).X (A p).f := by
      rw [hf]; exact GlobalTheory.LocExt.bcP_Xsp_mem Z p G hxX
    have hmem : (D.s.atP p).ιE c • (A p).z + -(baseChange₂ D p x) ∈ img n ((A p).LamStd L) := by
      rw [← hlat, hz, ← baseChange_smul₂, ← hlx, map_add]
      have : baseChange₂ D p l + baseChange₂ D p x + -(baseChange₂ D p x) = baseChange₂ D p l := by abel
      rw [this]
      exact Submodule.subset_span ⟨l, hlΛ, rfl⟩
    rw [← hO]
    exact coef_mem_O (A p) L hL n hn _ _ (Submodule.neg_mem _ hxp) hmem
  exact ⟨⟨c, Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc c key⟩, rfl⟩

end GlobalTheory.FramePrim
