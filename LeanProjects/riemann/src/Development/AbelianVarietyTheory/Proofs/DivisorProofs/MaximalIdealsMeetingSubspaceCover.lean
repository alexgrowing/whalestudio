import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuesMemOfLocal
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpCover

private theorem latD_of {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (y : NablaT (PadicAlgCl l) N lam)
    (h : ∃ x ∈ tensSub (deltaIn F.O N lam), GlobalTheory.LatBC.bc F.emb N lam x = y) : y ∈ F.latD lam := by
  obtain ⟨x, ⟨z, rfl⟩, rfl⟩ := h
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, PiTensorProduct.map_tprod, LinearMap.map_smulₛₗ, GlobalTheory.LatBC.bc_tprod]
    exact AddSubgroup.subset_closure ⟨r, fun τ => GlobalTheory.LatBC.dwMap F.emb N _ (m τ),
      fun τ => ⟨((m τ : Formalism.GradedWeylDivisibility.dualWeyl F.O N N (res N (lam τ))) : MvPolynomial (Fin N × Fin N) F.O), (m τ).2, rfl⟩, rfl⟩
  | add a b ha hb =>
    rw [map_add, map_add]
    exact add_mem ha hb

end GlobalTheory.ExpCover

namespace GlobalTheory.ExpCover

section Glue

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  (B : BlockDat K G0 Pl0) (ℓ : Lvl K G0) (Z : Submodule K B.S.Forms)

private theorem toF_coe (z : Fin (B.dZ ℓ Z) → K) :
    ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) = B.S.I ((B.fE ℓ Z).mulVec z) := by
  simp [BlockDat.toF, BlockDat.fE, CSD.I, Matrix.mulVec_mulVec]

private theorem toF_mem (z : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z z ∈ Z := by
  have h1 : (B.zE ℓ Z).mulVec z ∈ B.Z0 ℓ Z := by
    rw [BlockDat.zE, subE_mulVec]; exact Submodule.coe_mem _
  have h2 : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec z) ∈ B.coord Z := h1
  obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.1 h2
  have : B.toF ℓ Z z = f := by
    simp only [BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [← hfe]; simp
  rw [this]; exact hf

private theorem mem_cutZ (z : Fin (B.dZ ℓ Z) → K) :
    z ∈ B.cutZ ℓ Z ↔ ∀ c, ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Nab c := by
  rw [toF_coe]
  simp [BlockDat.cutZ, Formalism.DivisionValues.cutLat, CSD.nabLat, Formalism.DivisionValues.valLatF, Submodule.mem_pi]

private theorem mem_delZ (z : Fin (B.dZ ℓ Z) → K) :
    z ∈ B.delZ ℓ Z ↔ ∀ c, ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Del c := by
  rw [toF_coe]
  simp [BlockDat.delZ, Formalism.DivisionValues.cutLat, CSD.delLat, Formalism.DivisionValues.valLatF, Submodule.mem_pi]

private theorem final_step (w : HeightOneSpectrum (𝓞 K)) (L : 𝓞 K) (z : Fin (B.dZ ℓ Z) → K)
    (h : ∃ s : 𝓞 K, s ∉ w.asIdeal ∧
      ∀ c, s • (((algebraMap (𝓞 K) K L) • B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Del c) :
    L • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z) := by
  obtain ⟨s, hs, hc⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [mem_delZ]
  intro c
  have e : B.toF ℓ Z (s • L • z) = (algebraMap (𝓞 K) K s) • (algebraMap (𝓞 K) K L) • B.toF ℓ Z z := by
    rw [← map_smul, ← map_smul, algebraMap_smul, algebraMap_smul]
  rw [e]
  simpa [algebraMap_smul] using hc c

end Glue

end GlobalTheory.ExpCover

namespace GlobalTheory.ExpCover

private theorem isForm_of_span {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
    (A : Set (F.G → NablaT (PadicAlgCl l) N lam)) (hA : ∀ f ∈ A, F.IsForm lam f) :
    ∀ f ∈ Submodule.span (PadicAlgCl l) A, F.IsForm lam f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hA f hf
  | zero => exact ⟨fun _ _ _ => rfl, fun κ g => by rw [Pi.zero_apply, Pi.zero_apply, map_zero, smul_zero]⟩
  | add f f' _ _ h h' =>
    refine ⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, h.1 γ hγ, h'.1 γ hγ], fun κ g => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add, smul_add, h.2, h'.2]
  | smul a f _ h =>
    refine ⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, h.1 γ hγ], fun κ g => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, smul_comm, h.2]

private theorem span_stable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
    {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type} {B : BlockDat K G0 Pl0}
    {w : HeightOneSpectrum (𝓞 K)} (R : Reads F lam B w) (Z : Submodule K B.S.Forms) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) (i : F.I) :
    ∀ u ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z),
      transOp (F.emb (F.cst i)) (F.tr i) u ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z) := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f, hf, rfl⟩ := hu
    exact Submodule.subset_span ⟨B.op (R.ix i) f, hZ (R.ix i) hf, funext fun g => R.hecke i f g⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
  | smul a _ _ h => rw [map_smul]; exact Submodule.smul_mem _ a h

private theorem forms_fin : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ)
    (jK : F.K →* alg F.O N lam), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) := by
  intro l _ ι _ _ N F lam jK hF
  haveI : Module.Finite F.O (NablaT F.O N lam) := GlobalTheory.NablaFin.nablaT_finite F.O N ι lam
  obtain ⟨S, hS⟩ := hF.classes
  haveI : Finite (Formalism.UG.ClassSet F.Γ F.K) := by
    refine Finite.of_surjective (fun s : S => (DoubleCoset.mk F.Γ F.K (s : F.G) : Formalism.UG.ClassSet F.Γ F.K)) ?_
    intro c
    obtain ⟨γ, hγ, s, hs, κ, hκ, e⟩ := hS (Quotient.out c)
    refine ⟨⟨s, hs⟩, ?_⟩
    show DoubleCoset.mk F.Γ F.K s = c
    rw [← DoubleCoset.out_eq' F.Γ F.K c]
    exact (DoubleCoset.eq F.Γ F.K s _).2 ⟨γ, hγ, κ, hκ, e⟩
  exact Formalism.UG.P.automorphic_forms_level_finite_holds F.G F.Γ F.K F.O (NablaT F.O N lam) _ ‹_›

private theorem emb_norm : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok →
    (∀ c, ‖F.emb c‖ ≤ 1) ∧ ∀ c, ‖F.emb c‖ = 1 → IsUnit c := by
  intro l _ ι N F hF
  obtain ⟨hinj, L, _, hL⟩ := hF.ring
  have hmem : ∀ c, F.emb c ∈ L ∧ ‖F.emb c‖ ≤ 1 := by
    intro c
    have : F.emb c ∈ Set.range F.emb := ⟨c, rfl⟩
    rw [hL] at this
    exact this
  refine ⟨fun c => (hmem c).2, fun c hc => ?_⟩
  have hne : F.emb c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hinvL : (F.emb c)⁻¹ ∈ L := inv_mem (hmem c).1
  have hinvn : ‖(F.emb c)⁻¹‖ ≤ 1 := by rw [norm_inv, hc, inv_one]
  have : (F.emb c)⁻¹ ∈ Set.range F.emb := by rw [hL]; exact ⟨hinvL, hinvn⟩
  obtain ⟨d, hd⟩ := this
  have hcd : c * d = 1 := hinj (by rw [map_mul, map_one, hd, mul_inv_cancel₀ hne])
  exact IsUnit.of_mul_eq_one d hcd

private theorem form_lift : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (b : NablaT F.O N lam →ₛₗ[F.emb] NablaT (PadicAlgCl l) N lam), Function.Injective b → (∀ g x, b (grp F.O N lam g x) = grp (PadicAlgCl l) N lam (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x)) → F.IsJ lam jK → ∀ f : F.G → NablaT (PadicAlgCl l) N lam, F.IsForm lam f → (∀ g, ∃ y, b y = f g) → ∃ x : Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam), ∀ g, b ((x : F.G → NablaT F.O N lam) g) = f g := by
  intro l _ ι _ _ N F lam jK b hb hgrp hJ f hf hex
  choose x hx using hex
  refine ⟨⟨x, ?_⟩, hx⟩
  intro γ g κ
  apply hb
  rw [hx]
  change f _ = b ((jK κ⁻¹ : alg F.O N lam) • x g)
  have e1 : (jK κ⁻¹ : alg F.O N lam) • x g = ((F.chi κ⁻¹ : F.Oˣ) : F.O) • grp F.O N lam (F.kap κ⁻¹) (x g) := by
    rw [hJ κ⁻¹, smul_assoc]
    rfl
  rw [e1, LinearMap.map_smulₛₗ, hgrp, hx]
  have h2 := hf.2 κ⁻¹ (g * κ)
  simp only [Subgroup.coe_inv, mul_inv_cancel_right] at h2
  rw [h2, mul_assoc, hf.1 γ γ.2]

end GlobalTheory.ExpCover

open GlobalTheory.ExpCover in
set_option maxHeartbeats 600000 in

theorem _root_.GlobalTheory.T.maximalIdeals_meeting_subspace_cover : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type) (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [hm : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] [@IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) _ hm.toSMul _], F.Ok → F.IsJ lam jK → F.IsHecke lam jK (NablaT F.O N lam) → ∀ (R : Reads F lam B w) (ℓ : Lvl K G0) (Z : Submodule K B.S.Forms), (∀ i, Z ≤ Z.comap (B.op i)) → Covers B ℓ Z w fun m : {m : MaximalSpectrum F.T // ∃ θ, R.Occurs Z θ ∧ F.Over θ m.asIdeal} => haveI := m.1.isMaximal.isPrime; F.setting lam jK m.1.asIdeal := by
  intro K _ _ _ G0 _ _ Pl0 B w _ ι _ _ N F lam jK hm hst hOk hJ hH R ℓ Z hZ J hInc z hz
  have hfZ : B.toF ℓ Z z ∈ Z := toF_mem B ℓ Z z
  have hfN := (mem_cutZ B ℓ Z z).1 hz
  apply final_step
  apply R.del
  obtain ⟨hbinj, hbli, -⟩ := GlobalTheory.LatBC.bc_props F.emb N lam hOk.ring.1
  have hnorm := emb_norm _ ι N F hOk
  obtain ⟨x, hx⟩ := form_lift _ ι N F lam jK (GlobalTheory.LatBC.bc F.emb N lam) hbinj (GlobalTheory.LatBC.bc_grp F.emb N lam) hJ
    (R.rd (B.toF ℓ Z z)) (R.form _) (fun g => (GlobalTheory.LatBC.latN_iff F lam _).1 (R.nab _ hfN g))
  have hfin := forms_fin _ ι N F lam jK hOk
  have hfinV : Module.Finite F.O (NablaT F.O N lam) := GlobalTheory.NablaFin.nablaT_finite F.O N ι lam
  have hxS : (fun g => GlobalTheory.LatBC.bc F.emb N lam ((x : F.G → NablaT F.O N lam) g)) ∈
      Submodule.span (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (R.rd '' Z) := by
    have e : (fun g => GlobalTheory.LatBC.bc F.emb N lam ((x : F.G → NablaT F.O N lam) g)) = R.rd (B.toF ℓ Z z) := funext hx
    rw [e]
    exact Submodule.subset_span (Set.mem_image_of_mem _ hfZ)
  have hloc : ∀ (m : Ideal (MvPolynomial F.I F.O)) (hmax : m.IsMaximal) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ i, ‖θ i‖ ≤ 1) →
      (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ F.emb θ p‖ < 1) →
      (∃ v ∈ Submodule.span (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (R.rd '' Z), v ≠ 0 ∧
        ∀ i g, F.emb (F.cst i) • ∑ s ∈ F.tr i, v (g * s) = θ i • v g) →
      (haveI := hmax.isPrime; F.setting lam jK m).Incl (Formalism.EigenvalueLevelCeiling.plc w) J := by
    rintro m hmax θ h1 h2 ⟨v, hvS, hv0, hv⟩
    have h5 := hInc ⟨⟨m, hmax⟩, θ,
      ⟨v, hvS, hv0, isForm_of_span F lam _ (by rintro _ ⟨f, -, rfl⟩; exact R.form f) v hvS, hv⟩, h1, h2⟩
    exact h5
  have k1 := @values_mem_of_local (Formalism.EigenvalueLevelCeiling.plc w) _ F.O F.I F.G (NablaT F.O N lam) (NablaT (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) N lam)
    _ _ _ _ _ _ hfinV _ _ (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))
  have k1b := @k1 hm
  have k2 := @k1b hst hfin F.emb hOk.ring.1 hnorm.1 hnorm.2 (GlobalTheory.LatBC.bc F.emb N lam) hbinj hbli F.tr F.cst
  have k3 := k2 hH.2
  have k3b := k3 (tensSub (deltaIn F.O N lam)) (Submodule.span _ (R.rd '' Z)) (span_stable R Z hZ) x hxS ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : F.O) J
  have k4 := k3b {y | ∀ g, (y : F.G → NablaT F.O N lam) g ∈ tensSub (deltaIn F.O N lam)} (fun _ hy => hy)
  clear k1 k1b k2 k3 k3b
  have k5 := k4 (fun m hmax θ h1 h2 h3 y => by
    have h7 := hloc m hmax θ h1 h2 h3
    unfold HidaSetting.Incl TopIncl locSet at h7
    obtain ⟨x', hx', s, hs⟩ := h7 y
    exact ⟨x', fun g => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hx').2) g (Set.mem_univ _), s, hs⟩)
  have key : ∀ g, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : F.O) ^ J • (x : F.G → NablaT F.O N lam) g ∈ tensSub (deltaIn F.O N lam) := by
    intro g
    have h7 := k5 g
    rw [Submodule.coe_smul, Pi.smul_apply] at h7
    exact h7
  intro g
  apply latD_of F lam
  refine ⟨_, key g, ?_⟩
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx, Pi.smul_apply]
  simp only [map_pow, map_natCast]

end
