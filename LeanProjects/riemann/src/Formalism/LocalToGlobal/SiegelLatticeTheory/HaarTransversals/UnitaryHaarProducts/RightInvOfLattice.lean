import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianCombinationZ
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NinfConjIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfSteps

noncomputable section

open MeasureTheory Measure NumberField Topology Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped ENNReal Pointwise
open Matrix

namespace Formalism.L2.SG.Pf.Sinf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf

section Abs

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem rightInv_of_lattice (N : Subgroup G) (hN : IsClosed (N : Set G)) (μ : Measure G) (hσ : SigmaFinite μ)
    (h0 : μ ≠ 0) (hc : μ (N : Set G)ᶜ = 0) (hinv : ∀ s ∈ N, μ.map (fun x => s * x) = μ)
    (Γ : Subgroup G) (hΓN : Γ ≤ N) (hΓc : (Γ : Set G).Countable) [DiscreteTopology Γ]
    (C : Set G) (hC : IsCompact C) (hcov : ∀ x ∈ N, ∃ s ∈ Γ, ∃ c ∈ C, x = s * c) :
    ∀ t ∈ N, μ.map (fun x => x * t) = μ := by
  obtain ⟨hHaar, -, -⟩ := haarOnSet_isHaar N hN μ hσ h0 hc hinv
  have hcl : IsClosedEmbedding ((↑) : N → G) := hN.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace N := hcl.locallyCompactSpace
  haveI : SecondCountableTopology N := inferInstanceAs (SecondCountableTopology (N : Set G))
  haveI := hHaar
  let Γ' : Subgroup N := Γ.comap N.subtype
  let ι : Γ' → Γ := fun g => ⟨((g : N) : G), g.2⟩
  have hιinj : Function.Injective ι := by
    intro a b h
    have h1 : ((a : N) : G) = ((b : N) : G) := congrArg (fun y : Γ => (y : G)) h
    exact Subtype.ext (Subtype.ext h1)
  have hιc : Continuous ι := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  haveI : Countable Γ := hΓc.to_subtype
  haveI : Countable Γ' := hιinj.countable
  haveI : DiscreteTopology Γ' := DiscreteTopology.of_continuous_injective hιc hιinj
  have hK' : IsCompact (((↑) : N → G) ⁻¹' C) := hcl.isCompact_preimage hC
  have hcov' : ∀ x : N, ∃ s ∈ Γ', s * x ∈ ((↑) : N → G) ⁻¹' C := by
    intro x
    obtain ⟨s, hs, c, hcC, hx⟩ := hcov x x.2
    refine ⟨⟨s⁻¹, N.inv_mem (hΓN hs)⟩, Γ.inv_mem hs, ?_⟩
    show s⁻¹ * (x : G) ∈ C
    rw [hx, inv_mul_cancel_left]; exact hcC
  intro t ht
  have hR := Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice (μ.comap ((↑) : N → G)) Γ' hK' hcov' ⟨t, ht⟩
  have hmap : (μ.comap ((↑) : N → G)).map ((↑) : N → G) = μ := map_comap_subgroup N hN μ hc
  have hmeas : Measurable ((↑) : N → G) := measurable_subtype_coe
  calc μ.map (fun x => x * t) = ((μ.comap ((↑) : N → G)).map ((↑) : N → G)).map (fun x => x * t) := by rw [hmap]
    _ = (μ.comap ((↑) : N → G)).map ((fun x => x * t) ∘ ((↑) : N → G)) :=
        Measure.map_map (measurable_mul_const t) hmeas
    _ = (μ.comap ((↑) : N → G)).map (((↑) : N → G) ∘ (· * (⟨t, ht⟩ : N))) := rfl
    _ = ((μ.comap ((↑) : N → G)).map (· * (⟨t, ht⟩ : N))).map ((↑) : N → G) :=
        (Measure.map_map hmeas (measurable_mul_const _)).symm
    _ = μ := by rw [hR, hmap]

end Abs

section Grp

theorem isClosed_inN {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | InN ε e z M} := by
  have hc : ∀ (x : Fin n → ℂ) (S : Submodule ℂ (Fin n → ℂ)),
      IsClosed {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ x ∈ S} := fun x S =>
    (Submodule.closed_of_finiteDimensional S).preimage
      ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)
  have e2 : {M : Matrix (Fin n) (Fin n) ℂ | InN ε e z M} = {M | InS e z M} ∩
      ⋂ y, ⋂ (_ : ∀ a, hJ ε (e a) y = 0), {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ y ∈ spanLt e r} := by
    ext M; simp [InN]
  rw [e2]
  exact (WuDecayPf.isClosed_inS e z).inter (isClosed_iInter fun y => isClosed_iInter fun _ => hc _ _)

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem isClosed_ninfU : IsClosed (X.NinfU u) := by
  have : X.NinfU u = ⋂ v, (fun s : X.B.I.Ginf => uMat (s v)) ⁻¹'
      {M | InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) M} := by
    ext s; simp [HidaSetting.NinfU, Ninf]
  rw [this]
  exact isClosed_iInter fun v =>
    (isClosed_inN _ _ _).preimage (WuDecayPf.continuous_uMat.comp (continuous_apply v))

theorem conj_ninf {h : X.B.I.Ginf} (hh : h ∈ Hinf X u) {n : X.B.I.Ginf} (hn : n ∈ X.NinfU u) :
    h * n * h⁻¹ ∈ X.NinfU u := by
  have hi : h⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hh
  have hfix : ∀ v, ∀ x ∈ fixSet X u, uMat (h⁻¹ v) *ᵥ rv X.B.I v x = rv X.B.I v x := hi
  have := Formalism.L2.SG.CovariantRepresentation.ninf_conj X u h⁻¹ (fun v a => hfix v _ (Or.inl (Or.inl ⟨a, rfl⟩)))
    (fun v => hfix v _ (Or.inr rfl)) hn
  simpa using this

open PI.SchurPlaces.LeviLA in

theorem frameAt (v : InfinitePlace X.B.I.F) :
    Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u))
      (X.wfr u v) where
  ee a b := by
    simp only [HidaSetting.eR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ee, map_zero]
  ef a b := by
    simp only [HidaSetting.eR, HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ef]; split_ifs <;> simp
  ff a b := by
    simp only [HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ff, map_zero]
  ez a := by
    simp only [HidaSetting.eR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).1, map_zero]
  fz a := by
    simp only [HidaSetting.fR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).2, map_zero]
  ew a b := ((X.wfr_perp u v b).1 a).1
  fw a b := ((X.wfr_perp u v b).1 a).2
  zw b := (X.wfr_perp u v b).2
  ww := X.wfr_on u v
  zz := by
    simp only [HidaSetting.zR]
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.zu_norm, map_neg, map_natCast]
    exact neg_ne_zero.2 (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)
  card := by
    have h1 := X.n_eq; have h2 := D.R.r_eq; have h3 := D.R.rS_two; omega

open PI.SchurPlaces.LeviLA in

theorem levi {t : X.B.I.Ginf} (ht : t ∈ X.SinfU u) : ∃ h ∈ Hinf X u, ∃ n ∈ X.NinfU u, t = h * n := by
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat (t v)) := ht
  choose V hVu hVe hVf hVz hVw hVN using fun v =>
    levi_place (frameAt X u v) ((t v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
      (t v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hnN : s0⁻¹ * t ∈ X.NinfU u := fun v => by
    have e : uMat ((s0⁻¹ * t) v) =
        (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          uMat (t v) := rfl
    rw [e]; exact hVN v
  have hs0H : s0 ∈ Hinf X u := by
    show ∀ v, ∀ x ∈ fixSet X u, uMat (s0 v) *ᵥ rv X.B.I v x = rv X.B.I v x
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp; subst hp; exact hVz v
  exact ⟨s0, hs0H, s0⁻¹ * t, hnN, by rw [mul_inv_cancel_left]⟩

end Grp

section Meas

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem muN_compact {K : Set X.B.I.Ginf} (hK : IsCompact K) : X.muN u K < ⊤ :=
  (haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (isClosed_ninfU X u) (X.muN u) (X.muN_haar u)).2.1 K hK

theorem muN_right (hNO : NOCocompact X u) :
    ∀ t ∈ X.NinfU u, (X.muN u).map (fun y => y * t) = X.muN u := by
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  haveI := NOsub_discrete X u hK
  obtain ⟨C, hC, hcov⟩ := hNO
  have hle : NOsub X u hK ≤ NinfSub X.eR (X.zR u) := by
    intro s hs
    have h' : s ∈ NOinf X u := by rw [← NOsub_coe X u hK]; exact hs
    obtain ⟨γ, -, rfl, h1, -⟩ := h'
    exact h1
  have hcount : ((NOsub X u hK : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf).Countable := by
    rw [NOsub_coe]; exact noCount_holds X u
  refine rightInv_of_lattice (NinfSub X.eR (X.zR u)) (isClosed_ninfU X u) (X.muN u) (X.muN_haar u).1
    (X.muN_haar u).2.1 (X.muN_haar u).2.2.1 (X.muN_haar u).2.2.2 (NOsub X u hK) hle hcount C hC ?_
  intro x hx
  obtain ⟨s, hs, c, hc, rfl⟩ := hcov x hx
  refine ⟨s, ?_, c, hc, rfl⟩
  rw [← SetLike.mem_coe, NOsub_coe]; exact hs

end Meas

section Sec

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem sinf_mul' {a b : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (hb : b ∈ X.SinfU u) : a * b ∈ X.SinfU u :=
  (SinfSub X.B.I X.eR (X.zR u)).mul_mem ha hb

theorem sinf_inv' {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) : a⁻¹ ∈ X.SinfU u :=
  (SinfSub X.B.I X.eR (X.zR u)).inv_mem ha

theorem sinf_one' : (1 : X.B.I.Ginf) ∈ X.SinfU u := (SinfSub X.B.I X.eR (X.zR u)).one_mem

end Sec

end Formalism.L2.SG.Pf.Sinf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Sinf

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem sinfSection_of (hNO : NOCocompact X u) : SinfSection X u := by
  intro C hC
  classical
  have : SigmaFinite (X.muN u) := (X.muN_haar u).1
  have : SigmaFinite (X.muH u) := (X.muH_haar u).1
  have hSc : IsClosed (X.SinfU u) := WuDecayPf.isClosed_sinfU X u
  set C' := C ∩ X.SinfU u with hC'def
  have hC' : IsCompact C' := hC.inter_right hSc
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : X.B.I.Ginf)
  have hUo : IsOpen (interior V) := isOpen_interior
  have hU1 : (1 : X.B.I.Ginf) ∈ interior V := mem_interior_iff_mem_nhds.2 hV1
  have hUV : interior V ⊆ V := interior_subset

  obtain ⟨T, hTc, hTcov⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun g : X.B.I.Ginf => {y | y * g⁻¹ ∈ interior V}) (fun g => hUo.preimage (continuous_mul_const g⁻¹))
  have hall : ∀ x : X.B.I.Ginf, x ∈ ⋃ g ∈ T, {y : X.B.I.Ginf | y * g⁻¹ ∈ interior V} := by
    intro x
    rw [hTcov]
    exact Set.mem_iUnion.2 ⟨x, by simpa using hU1⟩
  have hTne : T.Nonempty := by
    obtain ⟨g, hg, -⟩ := Set.mem_iUnion₂.1 (hall 1)
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hTc.exists_eq_range hTne
  have hcov : ∀ x : X.B.I.Ginf, ∃ i, x * (g i)⁻¹ ∈ interior V := by
    intro x
    obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 (hall x)
    rw [hg] at hyT
    obtain ⟨i, rfl⟩ := hyT
    exact ⟨i, hy⟩

  set W : ℕ → Set X.B.I.Ginf := fun i => {y | y * (g i)⁻¹ ∈ interior V} with hWdef
  set O : ℕ → Set X.B.I.Ginf := fun i => {y | ∃ s ∈ X.SinfU u, s * y ∈ W i} with hOdef
  set P : ℕ → Set X.B.I.Ginf := fun i => {y | ∃ c ∈ C', c⁻¹ * y ∈ W i} with hPdef
  set A : Set X.B.I.Ginf := ⋃ i, (P i \ ⋃ j, ⋃ (_ : j < i), O j) with hAdef
  have hWo : ∀ i, IsOpen (W i) := fun i => hUo.preimage (continuous_mul_const _)
  have hOo : ∀ i, IsOpen (O i) := by
    intro i
    have e : O i = ⋃ s ∈ X.SinfU u, (fun y => s * y) ⁻¹' W i := by
      ext y; simp [hOdef]
    rw [e]; exact isOpen_biUnion fun s _ => (hWo i).preimage (continuous_const_mul s)
  have hPo : ∀ i, IsOpen (P i) := by
    intro i
    have e : P i = ⋃ c ∈ C', (fun y => c⁻¹ * y) ⁻¹' W i := by
      ext y; simp [hPdef]
    rw [e]; exact isOpen_biUnion fun c _ => (hWo i).preimage (continuous_const_mul c⁻¹)
  have hAm : MeasurableSet A :=
    MeasurableSet.iUnion fun i => (hPo i).measurableSet.diff
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hOo j).measurableSet

  have hOinv : ∀ j (y s : X.B.I.Ginf), s ∈ X.SinfU u → s * y ∈ O j → y ∈ O j := by
    rintro j y s hs ⟨s', hs', h⟩
    exact ⟨s' * s, sinf_mul' X u hs' hs, by simpa [mul_assoc] using h⟩

  have hkey : ∀ x, ∃ i, ∃ t ∈ X.SinfU u, t * x ∈ W i ∧ ∀ j < i, x ∉ O j := by
    intro x
    have hex : ∃ i, x ∈ O i := by
      obtain ⟨i, hi⟩ := hcov x
      exact ⟨i, 1, sinf_one' X u, by simpa [hWdef] using hi⟩
    obtain ⟨t, ht, htx⟩ := Nat.find_spec hex
    exact ⟨Nat.find hex, t, ht, htx, fun j hj => Nat.find_min hex hj⟩

  set KN : Set X.B.I.Ginf := (C' * V * V⁻¹ * (Hinf X u : Set X.B.I.Ginf)) ∩ X.NinfU u with hKNdef
  have hKN : IsCompact KN :=
    (((hC'.mul hVc).mul hVc.inv).mul (hinf_compact X u)).inter_right (isClosed_ninfU X u)
  have hKNm : MeasurableSet KN := hKN.isClosed.measurableSet
  have hHae : ∀ᵐ h ∂(X.muH u), h ∈ (Hinf X u : Set X.B.I.Ginf) :=
    ae_iff.2 (show (X.muH u) ((Hinf X u : Set X.B.I.Ginf))ᶜ = 0 from (X.muH_haar u).2.2.1)
  refine ⟨A.indicator 1, X.muN u KN * X.muH u Set.univ, measurable_one.indicator hAm, fun x => ?_,
    ENNReal.mul_lt_top (muN_compact X u hKN) (hFinite_holds X u), fun x => ?_, fun x => ?_⟩
  · by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  ·
    obtain ⟨i, t, ht, htx, hmin⟩ := hkey x
    obtain ⟨ht', hht, nt, hnt, rfl⟩ := levi X u ht
    have hpt : ∀ n ∈ X.NinfU u, ∀ h ∈ (Hinf X u : Set X.B.I.Ginf),
        A.indicator 1 (n * h * x) ≤ KN.indicator (1 : X.B.I.Ginf → ℝ≥0∞) (n * (h * nt⁻¹ * h⁻¹)) := by
      intro n hn h hh
      by_cases hA : n * h * x ∈ A
      · obtain ⟨j, ⟨c, ⟨hcC, hcS⟩, hcw⟩, hnot⟩ := Set.mem_iUnion.1 hA
        have hnhS : n * h ∈ X.SinfU u := sinf_mul' X u (ninf_sinf X u hn) (hinf_le_sinf X u h hh)
        have hxj : x ∈ O j := ⟨c⁻¹ * (n * h), sinf_mul' X u (sinf_inv' X u hcS) hnhS, by
          simpa [mul_assoc] using hcw⟩
        have hij : i ≤ j := by
          by_contra hlt
          exact hmin j (not_le.1 hlt) hxj
        have hji : j = i := by
          by_contra hne
          have hlt : i < j := lt_of_le_of_ne hij (Ne.symm hne)
          apply hnot
          refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hlt, ?_⟩⟩
          refine ⟨ht' * nt * (n * h)⁻¹, sinf_mul' X u ht (sinf_inv' X u hnhS), ?_⟩
          have e : ht' * nt * (n * h)⁻¹ * (n * h * x) = ht' * nt * x := by group
          rw [e]; exact htx
        subst hji
        have hu1 : c⁻¹ * (n * h * x) * (g j)⁻¹ ∈ interior V := hcw
        have hu2 : ht' * nt * x * (g j)⁻¹ ∈ interior V := htx
        have hmem : n * (h * nt⁻¹ * h⁻¹) ∈ KN := by
          refine ⟨?_, ?_⟩
          · have e : n * (h * nt⁻¹ * h⁻¹) = c * (c⁻¹ * (n * h * x) * (g j)⁻¹) *
                (ht' * nt * x * (g j)⁻¹)⁻¹ * (ht' * h⁻¹) := by group
            rw [e]
            exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ⟨hcC, hcS⟩ (hUV hu1))
              (Set.inv_mem_inv.2 (hUV hu2))) ((Hinf X u).mul_mem hht ((Hinf X u).inv_mem hh))
          · exact (NinfSub X.eR (X.zR u)).mul_mem hn
              (conj_ninf X u hh ((NinfSub X.eR (X.zR u)).inv_mem hnt))
        simp [Set.indicator, hA, hmem]
      · simp [Set.indicator, hA]
    have hFm : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf =>
        KN.indicator (1 : X.B.I.Ginf → ℝ≥0∞) (p.1 * (p.2 * nt⁻¹ * p.2⁻¹)) :=
      (measurable_one.indicator hKNm).comp
        (measurable_fst.mul ((measurable_snd.mul_const _).mul measurable_snd.inv))
    calc ∫⁻ p, A.indicator 1 (p.1 * p.2 * x) ∂((X.muN u).prod (X.muH u))
        ≤ ∫⁻ p, KN.indicator (1 : X.B.I.Ginf → ℝ≥0∞) (p.1 * (p.2 * nt⁻¹ * p.2⁻¹))
            ∂((X.muN u).prod (X.muH u)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_NH X u] with p hp
          exact hpt p.1 hp.1 p.2 hp.2
      _ = ∫⁻ h, ∫⁻ n, KN.indicator (1 : X.B.I.Ginf → ℝ≥0∞) (n * (h * nt⁻¹ * h⁻¹)) ∂(X.muN u) ∂(X.muH u) :=
          lintegral_prod_symm _ hFm.aemeasurable
      _ ≤ ∫⁻ _h, X.muN u KN ∂(X.muH u) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hHae] with h hh
          have hm : h * nt⁻¹ * h⁻¹ ∈ X.NinfU u :=
            conj_ninf X u hh ((NinfSub X.eR (X.zR u)).inv_mem hnt)
          rw [← lintegral_map (measurable_one.indicator hKNm) (measurable_mul_const _),
            muN_right X u hNO _ hm, lintegral_indicator_one hKNm]
      _ = X.muN u KN * X.muH u Set.univ := lintegral_const _
  ·
    obtain ⟨i, t, ht, htx, hmin⟩ := hkey x
    refine ⟨t, ht, fun c hcC hcS => ?_⟩
    have hmem : c * t * x ∈ A := by
      refine Set.mem_iUnion.2 ⟨i, ⟨c, ⟨hcC, hcS⟩, ?_⟩, ?_⟩
      · have e : c⁻¹ * (c * t * x) = t * x := by group
        rw [e]; exact htx
      · simp only [Set.mem_iUnion, not_exists]
        intro j hj hO
        exact hmin j hj (hOinv j x (c * t) (sinf_mul' X u hcS ht) (by simpa [mul_assoc] using hO))
    simp [Set.indicator, hmem]

def FinLevi : Prop := ∀ y ∈ SfinU X u, ∃ h : Hfin X u, ∃ n ∈ X.NfinU u, y = (h : X.B.I.Gf) * n

def FinLeviC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), FinLevi X u

def NDenseAt : Prop :=
  ∀ n ∈ X.NfinU u, ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
    ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

theorem nDenseAt_of (h : Formalism.L2.SG.Pf.SlabCoverPf.NDense) : NDenseAt X u := h D X u

theorem sCompact_of (hFL : FinLevi X u) (hNO : NOCocompact X u) (hND : NDenseAt X u) : SCompact X u := by
  classical
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hCF := Formalism.L2.SG.Closed.ClassFin_holds X u hK
  unfold Cut.ClassFin at hCF
  have hsurj : ∀ c : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK),
      ∃ g : Hfin X u, DoubleCoset.mk (iotaF X u).range (Ku X u hK) g = c := by
    intro c
    induction c using Quotient.inductionOn' with
    | h g => exact ⟨g, rfl⟩
  choose sr hsr using hsurj
  haveI := Fintype.ofFinite (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK))
  obtain ⟨CN, hCN, hNcov⟩ := hNO
  have hK2c : IsCompact X.K2 := (level_subgroup_compact_open X).2
  have hK2o : IsOpen X.K2 := (level_subgroup_compact_open X).1
  set KK : Set X.B.I.Gf := (fun k => X.xu u * k * (X.xu u)⁻¹) '' X.K2 with hKKdef
  have hKK : IsCompact KK :=
    hK2c.image ((continuous_const_mul _).mul continuous_const)
  set CH : Set X.B.I.Gf := ⋃ c, (fun k => ((sr c : Hfin X u) : X.B.I.Gf) * k) '' KK with hCHdef
  have hCH : IsCompact CH := isCompact_iUnion fun c => hKK.image (continuous_const_mul _)
  have hKKmem : ∀ k, (X.xu u)⁻¹ * k * X.xu u ∈ X.K2 → k ∈ KK := by
    intro k hk
    exact ⟨_, hk, by group⟩
  refine ⟨(CN * (Hinf X u : Set X.B.I.Ginf)) ×ˢ (KK * CH), (hCN.mul (hinf_compact X u)).prod (hKK.mul hCH), ?_⟩
  intro y hy1 hy2
  obtain ⟨hi, hhi, ni, hni, hyi⟩ := Sinf.levi X u hy1
  obtain ⟨hf, nf, hnf, hyf⟩ := hFL y.2 hy2
  obtain ⟨⟨γ', κ⟩, hrep⟩ := Formalism.UG.P.exists_rep (iotaF X u).range (Ku X u hK) sr hsr hf
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 γ'.2
  set c := DoubleCoset.mk (iotaF X u).range (Ku X u hK) hf with hc
  set g0 : X.B.I.GA := (γ : X.B.I.GA) with hg0
  have hg0G : g0 ∈ Gam X u := γ.2
  have hg0F : g0 ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I := (Subgroup.mem_inf.1 hg0G).1
  have hg0H := Subgroup.mem_prod.1 (Subgroup.mem_inf.1 hg0G).2
  have hhf : (hf : X.B.I.Gf) = g0.2 * ((sr c : Hfin X u) : X.B.I.Gf) * ((κ : Hfin X u) : X.B.I.Gf) := by
    have e := congrArg Subtype.val hrep
    rw [← hγ] at e
    exact e

  set ai : X.B.I.Ginf := g0.1⁻¹ * hi with hai
  have hai_H : ai ∈ Hinf X u := (Hinf X u).mul_mem ((Hinf X u).inv_mem hg0H.1) hhi
  set mi : X.B.I.Ginf := ai * ni * ai⁻¹ with hmi
  have hmi_N : mi ∈ X.NinfU u := Sinf.conj_ninf X u hai_H hni
  set af : Hfin X u := sr c * (κ : Hfin X u) with haf
  set mf : X.B.I.Gf := (af : X.B.I.Gf) * nf * (af : X.B.I.Gf)⁻¹ with hmf
  have hmf_N : mf ∈ X.NfinU u := (Cut.nfinConj_holds X u af nf hnf).1

  set U : Set X.B.I.Gf := {w | (X.xu u)⁻¹ * (w⁻¹ * mf) * X.xu u ∈ X.K2} with hUdef
  have hUo : IsOpen U :=
    hK2o.preimage ((continuous_const.mul (continuous_inv.mul continuous_const)).mul continuous_const)
  have hmfU : mf ∈ U := by
    show (X.xu u)⁻¹ * (mf⁻¹ * mf) * X.xu u ∈ X.K2
    simpa using hK.1
  obtain ⟨ν, hνF, hν1, hν2, hνU⟩ := hND mf hmf_N U hUo hmfU

  have hνm : ν.1⁻¹ * mi ∈ X.NinfU u :=
    (NinfSub X.eR (X.zR u)).mul_mem ((NinfSub X.eR (X.zR u)).inv_mem hν1) hmi_N
  obtain ⟨s, hs, cN, hcN, hsc⟩ := hNcov _ hνm
  obtain ⟨γs, hγsF, hγs1, hγsN, hγsNf, hγsK⟩ := hs

  refine ⟨g0 * ν * γs, ?_, (cN * ai, (γs.2⁻¹ * ν.2⁻¹ * mf) * (af : X.B.I.Gf)), ⟨?_, ?_⟩, ?_⟩
  · refine Subgroup.mem_inf.2 ⟨(Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem
      ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem hg0F hνF) hγsF, ?_⟩
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_))
      (Subgroup.subset_closure ?_)
    · exact ⟨hinf_le_sinf X u _ hg0H.1, hfin_sfin X u ⟨g0.2, hg0H.2⟩⟩
    · exact ⟨ninf_sinf X u hν1, nfin_sfin X u hν2⟩
    · exact ⟨ninf_sinf X u (hγs1 ▸ hγsN), nfin_sfin X u hγsNf⟩
  · exact Set.mul_mem_mul hcN hai_H
  · refine Set.mul_mem_mul (hKKmem _ ?_) ?_
    · have e : (X.xu u)⁻¹ * (γs.2⁻¹ * ν.2⁻¹ * mf) * X.xu u =
          ((X.xu u)⁻¹ * γs.2 * X.xu u)⁻¹ * ((X.xu u)⁻¹ * (ν.2⁻¹ * mf) * X.xu u) := by group
      rw [e]
      exact hK.2.1 _ (hK.2.2.1 _ hγsK) _ hνU
    · refine Set.mem_iUnion.2 ⟨c, (κ : Hfin X u), hKKmem _ κ.2, ?_⟩
      simp [haf]
  · have hsc' : ν.1⁻¹ * mi = γs.1 * cN := by rw [hsc, hγs1]
    refine Prod.ext ?_ ?_
    · show y.1 = g0.1 * ν.1 * γs.1 * (cN * ai)
      have e : g0.1 * ν.1 * γs.1 * (cN * ai) = g0.1 * ν.1 * (γs.1 * cN) * ai := by group
      rw [e, ← hsc', hyi, hmi, hai]
      group
    · show y.2 = g0.2 * ν.2 * γs.2 * (γs.2⁻¹ * ν.2⁻¹ * mf * (af : X.B.I.Gf))
      rw [hyf, hhf, hmf, haf]
      simp only [Subgroup.coe_mul]
      group

theorem psiUnit_holds : PsiUnit X u := fun n _ =>
  le_of_eq (Formalism.L2.SG.TermOp.KExpCut.psiUnit X _)

theorem iUnfold_of_NO (hK : X.LevelSubgroupCharacter) (hFL : FinLevi X u) (hNO : NOCocompact X u) (hND : NDenseAt X u) :
    Cut.IUnfold X u hK :=
  iUnfold_holds_of' X u hK (sCompact_of X u hFL hNO hND) (psiUnit_holds X u)
    (Formalism.L2.SG.Closed.ColBound_holds X u hK) (sinfSection_of X u hNO)

theorem iUnfoldAll_of (hFL : FinLeviC) (hNO : NOCocompactC) (hND : Formalism.L2.SG.Pf.SlabCoverPf.NDense) :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), Cut.IUnfold X u hK :=
  fun D X u hK => iUnfold_of_NO X u hK (hFL D X u) (hNO D X u) (nDenseAt_of X u hND)

end Formalism.L2.SG.Pf
