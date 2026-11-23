import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem latO_tgt_le {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT LT' : Set (Fin T.rank → D.host.E)}
    (v : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ v.asIdeal)
    (h : ∀ t ∈ LT, (((c : D.host.F) : D.host.E)) • t ∈ LT') :
    latO S T LS LT (· = v) ≤ latO S T LS LT' (· = v) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨GlobalTheory.IdeleAA.gam v c * α, GlobalTheory.IdeleAA.gam_mul_int v c hc hα,
    GlobalTheory.IdeleAA.gam_mul_supp v c α, a, ha, s, hs, _, h t ht, ?_⟩
  ext i j
  simp only [Matrix.of_apply]
  rw [← GlobalTheory.IdeleAA.pair_scale v c α hsupp]
  congr 1
  have h0 := GlobalTheory.IdeleAA.coe_ne_zero v c hc
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem coe_alg (c : 𝓞 D.host.F) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) = ((c : D.host.F) : D.host.E) := rfl

theorem exists_c {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modulBar sc := by
  classical
  set J : Ideal (𝓞 D.host.F) := ∏ v' ∈ P.S0, v'.asIdeal ^ P.depth sc v' with hJdef
  have hJ : ¬ J ≤ v.asIdeal := by
    intro h
    obtain ⟨v', hv', hle⟩ := (Ideal.IsPrime.prod_le v.isPrime).1 h
    have h1 : v'.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le (hP := v.isPrime) hle
    have : v' = v := HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top h1)
    exact hv (this ▸ hv')
  obtain ⟨c, hcJ, hcv⟩ := Set.not_subset.1 hJ
  have hmap : J.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.modul sc := by
    rw [hJdef]
    change Ideal.mapHom (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [map_prod]
    refine Finset.prod_le_prod' fun v' hv' => ?_
    rw [map_pow]
    refine pow_le_pow_left' ?_ _
    refine Ideal.map_le_iff_le_comap.2 (le_of_eq ?_)
    have := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    exact this.symm
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc := hmap (Ideal.mem_map_of_mem _ hcJ)
  refine ⟨c, hcv, hmod, ?_⟩
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [Formalism.L2.Pj.algebraMap_conj_smul, coe_alg]
    exact GlobalTheory.IdeleAA.conj_F c
  unfold Places.modulBar
  rw [← hfix]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hmod

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem smul_mem_idLat (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hc : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modul sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {y : Fin n → D.host.E} (hy : y ∈ Λ) : ((c : D.host.F) : D.host.E) • y ∈ idLat (shiftId G) Λ := by
  refine Submodule.subset_span ⟨_, ?_, y, hy, rfl⟩
  unfold shiftId
  rw [← mul_one ((c : D.host.F) : D.host.E)]
  exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hc, coe_alg c⟩)
    (FractionalIdeal.one_mem_inv_coe_ideal hne)

theorem smul_idLat_mem (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hcb : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modulBar sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {z : Fin n → D.host.E} (hz : z ∈ idLat (shiftId G) Λ) : ((c : D.host.F) : D.host.E) • z ∈ Λ := by
  refine Submodule.span_induction (p := fun z _ => ((c : D.host.F) : D.host.E) • z ∈ Λ) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨s, hs, y, hy, rfl⟩
    have hm : ((c : D.host.F) : D.host.E) * s ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hcb, coe_alg c⟩) hs
      have h0 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
      rwa [shiftId, mul_left_comm, mul_inv_cancel₀ h0, mul_one] at this
    obtain ⟨o, -, ho⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 hm
    rw [smul_smul, ← ho, algebraMap_smul]
    exact Λ.smul_mem o hy
  · simp
  · intro x y _ _ hx hy; rw [smul_add]; exact add_mem hx hy
  · intro a x _ hx; rw [smul_comm]; exact Λ.smul_mem a hx

end GlobalTheory.BigLoc

theorem GlobalTheory.BigLoc.latBig_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0,
    ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u →
      (u ∈ latBig G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  obtain ⟨c, hcv, hc, hcb⟩ := GlobalTheory.BigLoc.exists_c G.pl sc hv
  have hne : G.pl.modulBar sc ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hcb
    apply GlobalTheory.IdeleAA.coe_ne_zero v c hcv
    rw [← GlobalTheory.BigLoc.coe_alg, hcb, map_zero]
  unfold latBig
  rw [GlobalTheory.AscFinWit.mem_latO_at hu]
  exact ⟨fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_idLat_mem G hcb hne ht) h,
    fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_mem_idLat G hc hne ht) h⟩
