import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatAnn
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio.SphCoset

theorem isSelfDualC_of_gram_one {D : D7} {V : HSp D} (hV : V.gram = 1) {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : IsSDLat D.host.E V.rank L) : IsSelfDualC V L := by
  refine ⟨⟨hL.1, hL.2.1⟩, fun y => ?_⟩
  rw [hL.2.2 y]
  refine forall₂_congr fun x _ => ?_
  have e : ∑ i, ∑ j, star (x i) * V.gram i j * y j = stdH D.host.E V.rank x y := by
    rw [hV, stdH]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq, mul_one]
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩

theorem psi_symplO_std {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E) (hX : IsExact P X r)
    (LB : Lat X.B) (hLB : IsSelfDualC X.B LB)
    (hiff : ∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True)
    (z : Matrix (Fin P.d) (Fin P.a) D.host.E) (hz : z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d))
    (Pl : FinPl D → Prop) (u : WO X.A X.B) (hu : u ∈ latO X.A X.B (stdLat X.A) LB Pl) :
    X.ψ (symplO X.A X.B (finPt X.rkA X.rkB r z) u) = 1 := by
  have hA : IsSelfDualC X.A (stdLat X.A) :=
    isSelfDualC_of_gram_one hX.std.frame.gramA (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D _)
  refine Formalism.IndefR.Fin.lat_ann hX.weil.std X.A X.B hA hLB ((hiff z).1 hz) ?_
  refine AddSubgroup.closure_mono ?_ hu
  rintro _ ⟨α, hαi, _, rest⟩
  exact ⟨α, hαi, fun v hv => (hv trivial).elim, rest⟩

theorem unitBlock_mem (D : D7) (o a d : ℕ) :
    unitBlock D o a d ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun x hx i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, unitBlock D o a d i j * x j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      have := hx j trivial
      by_cases h : i.1 = o + j.1
      · simpa [unitBlock, h] using this
      · simp [unitBlock, h]
    exact this

theorem isLatVac_span {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Γ : AddSubgroup (WO S T)} {s : Set (WO S T → ℂ)}
    (hs : ∀ g ∈ s, IsLatVac (heisO ψ S T) Γ g) {φ : WO S T → ℂ} (hφ : φ ∈ Submodule.span ℂ s) :
    IsLatVac (heisO ψ S T) Γ φ := by
  induction hφ using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero => exact ⟨fun u _ => by funext w; simp [heisO], fun e _ u _ _ => by funext w; simp [heisO]⟩
  | add f g _ _ hf hg =>
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · have h1 := hf.1 u hu; have h2 := hg.1 u hu
      funext w; have e1 := congrFun h1 w; have e2 := congrFun h2 w
      simp only [heisO, Pi.add_apply] at e1 e2 ⊢; rw [mul_add, e1, e2]
    · have h1 := hf.2 e he u hu hh; have h2 := hg.2 e he u hu hh
      funext w; have e1 := congrFun h1 w; have e2 := congrFun h2 w
      simp only [heisO, Pi.add_apply] at e1 e2 ⊢; rw [mul_add, e1, e2]
  | smul c f _ hf =>
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · have h1 := hf.1 u hu
      funext w; have e1 := congrFun h1 w
      simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1 ⊢; rw [mul_left_comm, e1]
    · have h1 := hf.2 e he u hu hh
      funext w; have e1 := congrFun h1 w
      simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1 ⊢; rw [mul_left_comm, e1]

set_option synthInstance.maxHeartbeats 200000 in

theorem exists_sum_eq {D : D7} (𝔫 : Ideal (𝓞 D.host.F)) {α : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F)
    (h0 : ∀ v : FinPl D, 𝔫 ≤ v.asIdeal → evalV D.host.F v α = 0) :
    ∃ (s : Finset (𝓞 D.host.F)) (β : 𝓞 D.host.F → Af D.host.F), (∀ n ∈ s, n ∈ 𝔫) ∧ (∀ n, β n ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) ∧
      α = ∑ n ∈ s, (n : D.host.F) • β n := by
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian 𝔫
  have hg : ∀ v : FinPl D, ∃ n : 𝓞 D.host.F, ¬ 𝔫 ≤ v.asIdeal → n ∈ s ∧ n ∉ v.asIdeal := fun v => by
    by_contra h
    push_neg at h
    exact (h 0).1 (hs ▸ Submodule.span_le.2 fun n hn => (h n).2 hn)
  choose g hg using hg
  refine ⟨s, fun n => ((n : D.host.F)⁻¹) • (GlobalTheory.SelfDualAt.indP (fun v => ¬ 𝔫 ≤ v.asIdeal ∧ g v = n) * α),
    fun n hn => hs ▸ Submodule.subset_span hn, fun n v => ?_, ?_⟩
  · rw [map_smul, map_mul, GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs with h
    · have h1 : n ∉ v.asIdeal := h.2 ▸ (hg v h.1).2
      have h2 : v.valuation D.host.F (n : D.host.F) = 1 := (v.valuation_eq_one_iff_notMem).2 h1
      rw [one_mul, Algebra.smul_def]
      refine mul_mem ?_ (hα v)
      refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      have h3 := v.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((n : D.host.F)⁻¹)
      exact (h3.trans ((map_inv₀ _ _).trans (by rw [h2, inv_one]))).le
    · rw [zero_mul, smul_zero]; exact zero_mem _
  · refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun v => ?_
    show evalV D.host.F v α = evalV D.host.F v _
    rw [map_sum]
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes, GlobalTheory.SelfDualAt.evalV_indP]
    by_cases h : 𝔫 ≤ v.asIdeal
    · rw [h0 v h]
      exact (Finset.sum_eq_zero fun n _ => by rw [mul_zero, mul_zero, mul_zero]).symm
    · have hn : (g v : D.host.F) ≠ 0 := fun e => (hg v h).2 (by
        rw [show g v = 0 from by exact_mod_cast e]; exact zero_mem _)
      rw [Finset.sum_eq_single (g v) (fun n _ hn => by rw [if_neg fun h => hn h.2.symm, zero_mul, mul_zero, mul_zero])
        (fun h' => absurd (hg v h).1 h'), if_pos ⟨h, rfl⟩, one_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn, map_one, one_mul]

theorem smul_mem_std {D : D7} {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) {b : 𝓞 D.host.E} (hb : b ∈ D.host.conj • 𝔪) {a d : ℕ}
    {z : Matrix (Fin d) (Fin a) D.host.E} (hz : z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (skewLat D 𝔪 d)) :
    b • z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hc : (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) ≠ ⊥ := fun h => hm (by
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
    simpa using this)
  have h1 : ∀ A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (skewLat D 𝔪 d),
      b • A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      refine Submodule.subset_span fun x hx i _ => ?_
      have h2 := (FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc)).1
        (FractionalIdeal.mem_coe.1 (hA x hx i trivial)) _ (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
      have h3 := FractionalIdeal.coeIdeal_le_one h2
      rw [Matrix.smul_mulVec, Pi.smul_apply, Algebra.smul_def, mul_comm]
      exact Submodule.mem_one.2 ((FractionalIdeal.mem_one_iff _).1 h3)
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  induction hz using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA, rfl⟩ := hB
    exact Submodule.subset_span ⟨c, hc, _, h1 A hA, smul_comm _ _ _⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem exists_pt {D : D7} (δ : ℂ) {a d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) {x : Formalism.MainNotions.TaylorLogMetric.VC D a d}
    (hx : x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) L L') :
    ∃ z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D L L', x = Formalism.MainNotions.StandardLatticesGL3.pt D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) δ z := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  let K : AddSubgroup (Formalism.MainNotions.TaylorLogMetric.VC D a d) :=
    { carrier := {x | ∃ z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D L L', x = Formalism.MainNotions.StandardLatticesGL3.pt D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) δ z}
      zero_mem' := ⟨0, zero_mem _, by funext τ i j; simp [Formalism.MainNotions.StandardLatticesGL3.pt, Formalism.MainNotions.TaylorLogMetric.embV, Formalism.MainNotions.TaylorLogMetric.tor0]⟩
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨z + w, add_mem hz hw, by funext τ i j; simp [Formalism.MainNotions.StandardLatticesGL3.pt, Formalism.MainNotions.TaylorLogMetric.embV, Formalism.MainNotions.TaylorLogMetric.tor0, mul_add]⟩
      neg_mem' := by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨-z, neg_mem hz, by funext τ i j; simp [Formalism.MainNotions.StandardLatticesGL3.pt, Formalism.MainNotions.TaylorLogMetric.embV, Formalism.MainNotions.TaylorLogMetric.tor0]⟩ }
  refine (AddSubgroup.closure_le K).2 ?_ hx
  rintro _ ⟨w, hw, A, hA, rfl⟩
  change w ∈ Formalism.MainNotions.TaylorLogMetric.lamOf D ⊤ δ at hw
  show _ ∈ K
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, -, rfl⟩ := hw
    refine ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c • A, Submodule.smul_mem _ _ hA, ?_⟩
    funext τ i j
    have e := hG.1 τ (c : D.host.K)
    have e2 : (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c • A) i j = ((c : D.host.K) : D.host.E) * A i j := rfl
    simp only [Formalism.MainNotions.StandardLatticesGL3.pt, Formalism.MainNotions.TaylorLogMetric.embV, Formalism.MainNotions.TaylorLogMetric.tor0, Pi.smul_apply, smul_eq_mul, e2, map_mul]
    rw [e, mul_assoc]
  | zero => rw [zero_smul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_smul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_smul]; exact neg_mem hu

theorem reads_sum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type} (s : Finset ι) {G : ι → Formalism.MainNotions.TaylorLogMetric.VC D a d → ℂ}
    {f : ι → WO S T → ℂ} (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

theorem heisO_sum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) : heisO ψ S T x (∑ q ∈ s, c q • f q) = ∑ q ∈ s, c q • heisO ψ S T x (f q) := by
  funext w
  simp only [heisO, Finset.sum_apply, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun q _ => mul_left_comm _ _ _

set_option maxHeartbeats 800000 in

theorem mem_span : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ) (f₀ φ : WO X.A X.B → ℂ), Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
    φ ∈ Submodule.span ℂ {g | ∃ z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (skewLat D 𝔪 P.d),
      g = heisO X.ψ X.A X.B (finPt X.rkA X.rkB r (unitBlock D o P.a P.d)) (heisO X.ψ X.A X.B (finPt X.rkA X.rkB r z) f₀)} := by
  intro D δ t0 Q P X r hX 𝔪 o f₀ φ hf₀ hφ
  set Tr := Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ with hTr
  set L₁ := Formalism.MainNotions.TaylorLogMetric.La D Tr (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (skewLat D 𝔪 P.d) with hL₁
  set L₀ := Formalism.MainNotions.StandardLatticesGL3.La0 D Tr P.a P.d with hL₀
  choose z hz hzx using fun q : L₁ ⧸ L₀.addSubgroupOf L₁ => exists_pt δ _ _ (Quotient.out q : L₁).2
  have hU := fun G f (h : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r G f) =>
    GlobalTheory.NormExact.heisO_finPt_reads X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r hX.setup G f h
  obtain ⟨s, c, hs⟩ : ∃ (s : Finset (L₁ ⧸ L₀.addSubgroupOf L₁)) (c : L₁ ⧸ L₀.addSubgroupOf L₁ → ℂ),
      Formalism.MainNotions.TaylorLogMetric.Iop D Tr L₀ L₁ P.e0 = ∑ q ∈ s, c q • Formalism.MainNotions.TaylorLogMetric.U D Tr (Formalism.MainNotions.StandardLatticesGL3.pt D Tr δ (z q)) P.e0 := by
    by_cases hfin : Finite (L₁ ⧸ L₀.addSubgroupOf L₁)
    · have := Fintype.ofFinite (L₁ ⧸ L₀.addSubgroupOf L₁)
      refine ⟨Finset.univ, fun q => ((Real.sqrt ((L₀.addSubgroupOf L₁).index : ℝ))⁻¹ : ℂ) *
        Formalism.MainNotions.TaylorLogMetric.al D Tr ((Quotient.out q : L₁) : Formalism.MainNotions.TaylorLogMetric.VC D P.a P.d), funext fun y => ?_⟩
      rw [Formalism.MainNotions.TaylorLogMetric.Iop, finsum_eq_sum_of_fintype, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, ← hzx q, mul_assoc]
    · refine ⟨∅, 0, funext fun y => ?_⟩
      have : (L₀.addSubgroupOf L₁).index = 0 := by
        have : Infinite (L₁ ⧸ L₀.addSubgroupOf L₁) := not_finite_iff_infinite.1 hfin
        exact Nat.card_eq_zero_of_infinite
      simp [Formalism.MainNotions.TaylorLogMetric.Iop, this]
  have h1 := reads_sum s fun q => (hU _ _ hf₀ (z q)).smul (c q)
  rw [← hs] at h1
  have h2 := ((hU _ _ h1 (unitBlock D o P.a P.d)).smul
    (Formalism.MainNotions.StandardLatticesGL3.wdPh D Tr (Formalism.MainNotions.StandardLatticesGL3.pt D Tr δ (unitBlock D o P.a P.d)))).smul
    ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹
  rw [Reads.unique hφ h2]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
  rw [heisO_sum]
  exact sum_mem fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨z q, hz q, rfl⟩)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem smul_finPt {D : D7} {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (n : 𝓞 D.host.F)
    (z : Matrix (Fin d) (Fin a) D.host.E) : algebraMap D.host.F (AF D.host.F) n • finPt hS hT r z =
      finPt hS hT r (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) n • z) := by
  funext i j
  show algebraMap D.host.F (AF D.host.F) n • ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] (-(r⁻¹ * z (Fin.cast hT i) (Fin.cast hS j))) : AE D) =
    (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (-(r⁻¹ * (((n : D.host.F) : D.host.E) * z (Fin.cast hT i) (Fin.cast hS j))))
  rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul]
  congr 1
  show ((n : D.host.F) : D.host.E) * _ = _
  ring

set_option maxHeartbeats 800000 in

theorem psi_symplO_skew : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (skewLat D 𝔪 P.d),
  ∀ u ∈ latO X.A X.B (stdLat X.A) LB (fun v => v ∉ Sf), X.ψ (symplO X.A X.B (finPt X.rkA X.rkB r z) u) = 1 := by
  intro D δ t0 Q P X r hX 𝔪 Sf hm LB hLB hiff z hz u hu
  induction hu using AddSubgroup.closure_induction with
  | zero => rw [Formalism.IndefR.Fin.symplO_zero_right, AddChar.map_zero_eq_one]
  | add u1 u2 _ _ h1 h2 => rw [Formalism.IndefR.Fin.symplO_add_right, AddChar.map_add_eq_mul, h1, h2, one_mul]
  | neg u' _ h => rw [Formalism.IndefR.Fin.symplO_neg_right, AddChar.map_neg_eq_inv, h, inv_one]
  | mem u hu =>
    obtain ⟨α, hα, h0, c, hc, s, hs, t, ht, rfl⟩ := hu
    obtain ⟨N, β, hN, hβ, rfl⟩ := exists_sum_eq (𝔪.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) hα fun v hv => by
      refine h0 v (not_not.2 ((hm.2.2.2 v).2 ?_))
      have := v.isPrime
      obtain ⟨w, h1, h2, h3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal 𝔪 hv
      exact ⟨⟨w, h2, fun h => hm.1 (le_bot_iff.1 (h ▸ h1))⟩, h1, HeightOneSpectrum.ext h3⟩
    clear hα h0
    generalize hm' : (fun i j => c * t i * ∑ k, star (s k) * X.A.gram k j) = m
    have hgen : ∀ n, (Matrix.of fun i j => (pairA D.host.F 0 (β n)) ⊗ₜ[D.host.F] m i j : WO X.A X.B) ∈
        latO X.A X.B (stdLat X.A) LB fun _ => True := fun n =>
      AddSubgroup.subset_closure ⟨β n, hβ n, fun v h => (h trivial).elim, c, hc, s, hs, t, ht, by rw [← hm']⟩
    have e0 : (Matrix.of fun i j => (pairA D.host.F 0 (∑ n ∈ N, (n : D.host.F) • β n)) ⊗ₜ[D.host.F]
        (c * t i * ∑ k, star (s k) * X.A.gram k j) : WO X.A X.B) =
        Matrix.of fun i j => (pairA D.host.F 0 (∑ n ∈ N, (n : D.host.F) • β n)) ⊗ₜ[D.host.F] m i j := by rw [← hm']
    rw [e0]
    clear e0
    induction N using Finset.induction_on with
    | empty =>
      have : (Matrix.of fun i j => (pairA D.host.F 0 (∑ n ∈ (∅ : Finset (𝓞 D.host.F)), (n : D.host.F) • β n)) ⊗ₜ[D.host.F] m i j :
          WO X.A X.B) = 0 := by
        funext i j
        rw [Finset.sum_empty]
        exact TensorProduct.zero_tmul _ _
      rw [this, Formalism.IndefR.Fin.symplO_zero_right, AddChar.map_zero_eq_one]
    | insert n N hn ih =>
      have e1 : (Matrix.of fun i j => (pairA D.host.F 0 (∑ n ∈ insert n N, (n : D.host.F) • β n)) ⊗ₜ[D.host.F] m i j :
          WO X.A X.B) = algebraMap D.host.F (AF D.host.F) n •
            (Matrix.of fun i j => (pairA D.host.F 0 (β n)) ⊗ₜ[D.host.F] m i j : WO X.A X.B) +
          Matrix.of fun i j => (pairA D.host.F 0 (∑ n ∈ N, (n : D.host.F) • β n)) ⊗ₜ[D.host.F] m i j := by
        funext i j
        rw [Finset.sum_insert hn, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply,
          TensorProduct.smul_tmul', ← TensorProduct.add_tmul, smul_eq_mul]
        congr 1
        refine Prod.ext ?_ ?_
        · show (0 : Ainf D.host.F) = _ * 0 + 0
          rw [mul_zero, add_zero]
        · show _ = algebraMap D.host.F (Af D.host.F) n * β n + _
          rw [← Algebra.smul_def]
          rfl
      have hb : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) n ∈ D.host.conj • 𝔪 := by
        have h1 := Ideal.smul_mem_pointwise_smul D.host.conj _ 𝔪 (hN n (Finset.mem_insert_self _ _))
        have h2 : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) n = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) n :=
          RingOfIntegers.ext ((D.host.conjE_mem_hostF_iff _).1 (n : D.host.F).2)
        rwa [h2] at h1
      rw [e1, Formalism.IndefR.Fin.symplO_add_right, AddChar.map_add_eq_mul, ih fun k hk => hN k (Finset.mem_insert_of_mem hk), mul_one,
        GlobalTheory.SelfDualAt.symplO_smul_swap, smul_finPt]
      exact psi_symplO_std P X r hX LB hLB hiff _ (smul_mem_std hm.1 hb hz) _ _ (hgen n)

theorem sph : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
    IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf φ := by
  intro D δ t0 Q P X r hX 𝔪 Sf o hm LB hLB hiff f₀ φ hf₀ hsph hφ
  have hstd : IsStdChar D X.ψ (-1) := hX.weil.std
  set Γ := latO X.A X.B (stdLat X.A : Set (Fin X.A.rank → D.host.E)) (LB : Set (Fin X.B.rank → D.host.E))
    (fun v => v ∉ Sf) with hΓ
  have hle : Γ ≤ latO X.A X.B (stdLat X.A : Set (Fin X.A.rank → D.host.E)) (LB : Set (Fin X.B.rank → D.host.E))
      (fun v => v ∉ (∅ : Finset (FinPl D))) :=
    AddSubgroup.closure_mono fun _ ⟨α, hαi, _, rest⟩ =>
      ⟨α, hαi, fun v hv => (hv (Finset.notMem_empty v)).elim, rest⟩
  have hv0 : GlobalTheory.Asc.VacG X.ψ X.A X.B Γ f₀ :=
    ⟨hf₀.1, fun u hu => hsph.1 u (hle hu), fun e he u hu hh => hsph.2 e he u (hle hu) hh⟩
  have toAnn : ∀ w : WO X.A X.B, (∀ u ∈ Γ, X.ψ (symplO X.A X.B w u) = 1) → w ∈ GlobalTheory.Asc.Ann X.ψ X.A X.B Γ :=
    fun w h => ⟨fun u hu => h _ (Γ.nsmul_mem hu 2), fun e _ u hu _ => h u hu⟩
  have key := (GlobalTheory.Asc.annVac D X.ψ hstd X.A X.B Γ).1
  have hgen : ∀ g ∈ {g | ∃ z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (skewLat D 𝔪 P.d),
      g = heisO X.ψ X.A X.B (finPt X.rkA X.rkB r (unitBlock D o P.a P.d)) (heisO X.ψ X.A X.B (finPt X.rkA X.rkB r z) f₀)},
      IsLatVac (heisO X.ψ X.A X.B) Γ g := by
    rintro g ⟨z, hz, rfl⟩
    exact (key _ (key _ hv0 _ (toAnn _ (psi_symplO_skew P X r hX 𝔪 Sf hm LB hLB hiff z hz))) _
      (toAnn _ (psi_symplO_std P X r hX LB hLB hiff _ (unitBlock_mem D o P.a P.d) _))).2
  exact isLatVac_span hgen (mem_span P X r hX 𝔪 o f₀ φ hf₀ hφ)

end GlobalTheory.NormRatio.SphCoset
