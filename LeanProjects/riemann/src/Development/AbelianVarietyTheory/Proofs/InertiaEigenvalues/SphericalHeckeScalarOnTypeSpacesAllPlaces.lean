import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSphericalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.HeckeScalarAll

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem trivOutside_mono {T T' : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (h : T ⊆ T') {x : GAf L n}
    (hx : TrivOutside T x) : TrivOutside T' x := fun v hv => hx v (fun h' => hv (h h'))

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GAf L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have e : (((x * y : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [e, Matrix.map_mul, hx v hv, hy v hv, one_mul]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GAf L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro v hv
  have e : (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := Units.inv_mul x.1
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) (AL L) => M.map (compAt L v)) e
  simp only [Matrix.map_mul, hx v hv, mul_one] at h2
  rw [h2]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end Gen

open Classical in
theorem finsum_cosets_eq {G W : Type} [Group G] [AddCommGroup W] (J U : Subgroup G) (Dset : Set G) (F : G → W)
    (hJU : ∀ x ∈ Dset, ∀ x' ∈ Dset, (x⁻¹ * x' ∈ J ↔ x⁻¹ * x' ∈ U))
    (hF : ∀ x ∈ Dset, ∀ x' ∈ Dset, x⁻¹ * x' ∈ U → F x = F x') :
    (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ Dset, (x : G ⧸ J) = c then F hc.choose else 0) =
    ∑ᶠ c : G ⧸ U, if hc : ∃ x ∈ Dset, (x : G ⧸ U) = c then F hc.choose else 0 := by
  set φ := fun c : G ⧸ J => if hc : ∃ x ∈ Dset, (x : G ⧸ J) = c then F hc.choose else 0 with hφdef
  set ψ := fun c : G ⧸ U => if hc : ∃ x ∈ Dset, (x : G ⧸ U) = c then F hc.choose else 0 with hψdef
  have hφ : Function.support φ ⊆ (fun x : G => (x : G ⧸ J)) '' Dset := by
    intro c hc
    by_contra hn
    apply hc
    simp only [φ]
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  have hψ : Function.support ψ ⊆ (fun x : G => (x : G ⧸ U)) '' Dset := by
    intro c hc
    by_contra hn
    apply hc
    simp only [ψ]
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [← Set.indicator_eq_self.2 hφ, ← Set.indicator_eq_self.2 hψ, ← finsum_mem_def, ← finsum_mem_def]
  let e : G ⧸ J → G ⧸ U := fun c => if hc : ∃ x ∈ Dset, (x : G ⧸ J) = c then (hc.choose : G ⧸ U) else ((1 : G) : G ⧸ U)
  refine finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_
  · rintro c ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J) := ⟨x, hx, rfl⟩
    simp only [e, dif_pos hc]
    exact ⟨_, hc.choose_spec.1, rfl⟩
  · rintro c ⟨x, hx, rfl⟩ c' ⟨x', hx', rfl⟩ h
    have hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J) := ⟨x, hx, rfl⟩
    have hc' : ∃ y ∈ Dset, (y : G ⧸ J) = (x' : G ⧸ J) := ⟨x', hx', rfl⟩
    simp only [e, dif_pos hc, dif_pos hc'] at h
    rw [QuotientGroup.eq] at h
    show (x : G ⧸ J) = (x' : G ⧸ J)
    rw [← hc.choose_spec.2, ← hc'.choose_spec.2, QuotientGroup.eq]
    exact (hJU _ hc.choose_spec.1 _ hc'.choose_spec.1).2 h
  · rintro d ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J) := ⟨x, hx, rfl⟩
    refine ⟨(x : G ⧸ J), ⟨x, hx, rfl⟩, ?_⟩
    simp only [e, dif_pos hc]
    rw [QuotientGroup.eq]
    have h1 := hc.choose_spec.2
    rw [QuotientGroup.eq] at h1
    exact (hJU _ hc.choose_spec.1 _ hx).1 h1
  · rintro c ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Dset, (y : G ⧸ J) = (x : G ⧸ J) := ⟨x, hx, rfl⟩
    have he : e x = (hc.choose : G ⧸ U) := by simp only [e, dif_pos hc]
    have hd : ∃ y ∈ Dset, (y : G ⧸ U) = e x := ⟨_, hc.choose_spec.1, he.symm⟩
    simp only [φ, ψ, dif_pos hc, dif_pos hd]
    apply hF _ hc.choose_spec.1 _ hd.choose_spec.1
    rw [← QuotientGroup.eq, hd.choose_spec.2, he]

end GlobalTheory.HeckeScalarAll

namespace GlobalTheory.HeckeScalarAll

section Hk

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

open Classical in

theorem heckeD_eq_sum (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f : GAf L n → W) :
    NG.heckeD J Dset f = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = c then NG.rt L n hc.choose f else 0) := by
  funext g
  have hsub : Function.support (fun cc : GAf L n ⧸ J =>
      if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = cc then f (g * hc.choose) else 0) ⊆
      (hfin.toFinset : Set (GAf L n ⧸ J)) := by
    intro cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  simp only [NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> rfl

theorem heckeD_add' (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (y z : GAf L n → W) :
    NG.heckeD J Dset (y + z) = NG.heckeD J Dset y + NG.heckeD J Dset z := by
  rw [heckeD_eq_sum _ _ hfin, heckeD_eq_sum _ _ hfin, heckeD_eq_sum _ _ hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem heckeD_zero (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) :
    NG.heckeD J Dset (0 : GAf L n → W) = 0 := by
  rw [heckeD_eq_sum _ _ hfin]
  refine Finset.sum_eq_zero fun d _ => ?_
  split_ifs <;> simp

theorem heckeD_eq_of_fixed (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) (hJ : NG.HypOutside J χ B)
    (s : SplitPlace L) (hs : s.v ∉ B) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ) (f : GAf L n → W)
    (hf : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) :
    NG.heckeD J (tSet L n s ϖ k) f = NG.heckeD (Umax L n) (tSet L n s ϖ k) f := by
  funext g
  simp only [NG.heckeD]
  refine finsum_cosets_eq J (Umax L n) _ (fun x => f (g * x)) ?_ ?_
  · intro x hx x' hx'
    have ht : TrivOutside Bᶜ (x⁻¹ * x') :=
      trivOutside_mono (Set.singleton_subset_iff.2 hs) (trivOutside_mul (trivOutside_inv hx.1) hx'.1)
    exact (hJ _ ht).1
  · intro x hx x' hx' hu
    have ht := trivOutside_mul (trivOutside_inv hx.1) hx'.1
    have h1 := congrFun (hf _ hu ht) (g * x)
    simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at h1
    rw [mul_assoc, mul_inv_cancel_left] at h1
    exact h1.symm

theorem tN_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f)
    (f' : GAf L n → W) (hf' : f' ∈ S') (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f' = f') :
    NG.tN (Umax L n) s ϖ k f' = c • f' := by
  classical
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : GAf L n, ((T ⟨NG.rt L n h f, hS.stable h _ f.2⟩ : S') : GAf L n → W) = NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (f : GAf L n → W) = f := by
    intro κ hκ ht
    have h1 := hrt κ
    rw [hfix κ hκ ht] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ d ∈ hfin.toFinset, (if hd : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ Umax L n) = d then
      (⟨NG.rt L n hd.choose f, hS.stable _ _ f.2⟩ : S) else 0)
  have hσ : (σ : GAf L n → W) = NG.heckeD (Umax L n) (tSet L n s ϖ k) f := by
    rw [heckeD_eq_sum _ _ hfin, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> rfl
  have hTσ : ((T σ : S') : GAf L n → W) = NG.heckeD (Umax L n) (tSet L n s ϖ k) f' := by
    rw [heckeD_eq_sum _ _ hfin, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs
    · exact hrt _
    · simp
  simp only [NG.tN] at hcf ⊢
  have key : ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • σ = c • f := Subtype.ext (by
    rw [Submodule.coe_smul, hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

end Hk

end GlobalTheory.HeckeScalarAll

namespace GlobalTheory.HeckeScalarAll

section Iso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem iSup_finset_stable' (t : Finset (Submodule ℂ (GAf L n → W)))
    (ht : ∀ i ∈ t, ∀ h, ∀ f ∈ i, NG.rt L n h f ∈ i) (h : GAf L n) :
    ∀ f ∈ (⨆ i ∈ t, i), NG.rt L n h f ∈ (⨆ i ∈ t, i) := by
  have hle : (⨆ i ∈ t, i) ≤ (⨆ i ∈ t, i).comap (NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ t) => i) i hi) (ht i hi h f hf)
  exact fun f hf => hle hf

theorem tN_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f)
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp only [NG.tN, heckeD_zero _ _ hfin, smul_zero]
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add, hyfix κ hκ hκt] at e
        exact add_left_cancel e
      have e1 := tN_iso hS.1 haF.2 s ϖ k hfin c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [NG.tN] at e1 e2 ⊢
      rw [heckeD_add' _ _ hfin, smul_add, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

theorem tN_isoTyp {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f)
    (f : GAf L n → W) (hf : f ∈ NG.isoTyp ρ S)
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) : NG.tN (Umax L n) s ϖ k f = c • f := by
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact tN_finset_sum hS s ϖ k hfin c hc t ht f hft hfix

end Iso

end GlobalTheory.HeckeScalarAll

namespace GlobalTheory.HeckeScalarAll

open Formalism.L2.NG

theorem host_conj_eq' (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem isConjPl_symm' {D : D7} {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hxy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hxy, host_conj_eq', host_conj_eq', IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

theorem not_bad {D : D7} {M : MtFam D} (HT : HeckeTied D M) (i : D.nd.Loc) {w : PlE D.host}
    (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E) (hc : IsConjPl D.host w s.w) : s.v ∉ badPl D i := by
  rintro ⟨w', hover, hw'⟩
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by rw [host_conj_eq']; simp)).2 h3
  obtain ⟨hsp, hl, hS, hQ⟩ := hw
  rcases hw' with hQ' | ⟨kk, hg⟩ | hpd
  · rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w' (hover.trans s.w_under.symm) with e | e
    · subst e
      exact hQ (HT.Q_conj i s.w w (isConjPl_symm' hc) hQ')
    · have ew : GlobalTheory.SplitConjPlace.conjPlE s.w = w := by
        ext1; ext x
        rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
        refine (hc x _ ?_).symm
        rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']
      rw [e, ew] at hQ'
      exact hQ hQ'
  · apply hS
    refine (D.nd.S_def i w).2 ⟨?_, hl⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · exact hS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr (hp _ hpd)), hl⟩)

theorem heckeScalar_all : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ i : D.nd.Loc, HeckeScalar M i := by
  intro D M HT A i P w k s ϖ hw hcw hu _ _
  have hsB : s.v ∉ badPl D i := not_bad HT i hw s hcw
  obtain ⟨c, hc⟩ := GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical D.host.E D.R.nV (M.loc i).wt (A.S i P) (A.irr i P) s ϖ k hu
  have hfinU := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (Umax D.host.E D.R.nV) 1 ∅
    (fun κ _ => ⟨Iff.rfl, fun _ => rfl⟩) s ϖ k (by simp) hu
  refine ⟨c, fun y hy => ?_⟩
  have hfT : (M.loc i).real y ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := by
    rw [← (M.loc i).real_range]; exact ⟨y, rfl⟩
  have hfI : (M.loc i).real y ∈ NG.isoTyp (M.loc i).wt.ρ (A.S i P) := by
    rw [A.typeV] at hy; exact hy
  have hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      NG.rt D.host.E D.R.nV κ ((M.loc i).real y) = (M.loc i).real y := by
    intro κ hκ ht
    have ht' : TrivOutside (badPl D i)ᶜ κ := trivOutside_mono (Set.singleton_subset_iff.2 hsB) ht
    obtain ⟨h1, h2⟩ := HT.J_hyp i κ ht'
    have hJ : κ ∈ (M.loc i).J := h1.2 hκ
    have e := hfT.2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  have e1 : NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = NG.tN (Umax D.host.E D.R.nV) s ϖ k ((M.loc i).real y) := by
    simp only [NG.tN]
    rw [heckeD_eq_of_fixed (M.loc i).J (M.loc i).χ (badPl D i) (HT.J_hyp i) s hsB ϖ k _ hfix]
  rw [e1]
  exact tN_isoTyp (A.irr i P) s ϖ k hfinU c hc _ hfI hfix

end GlobalTheory.HeckeScalarAll
