import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqCut

section Cosets

variable {Γ : Type} [Group Γ] {H J : Subgroup Γ}

theorem isDC_sub_iff (hJ : J ≤ H) (a : H) (R : Finset H) :
    Bridge.IsDC (J.subgroupOf H) a R ↔ Bridge.IsDC J (a : Γ) (R.map (Function.Embedding.subtype _)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      obtain ⟨k₁, k₂, e⟩ := h1 b' hb'
      exact ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, congrArg Subtype.val e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, rfl⟩
      refine ⟨b.1, ⟨Finset.mem_map.2 ⟨b, hb, rfl⟩, hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
      exact congrArg Subtype.val (hu y' ⟨hy', hy2⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨k₁, k₂, e⟩ := h1 b.1 (Finset.mem_map.2 ⟨b, hb, rfl⟩)
      exact ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, Subtype.ext e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, rfl⟩
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      refine ⟨b', ⟨hb', hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      exact Subtype.ext (hu y.1 ⟨Finset.mem_map.2 ⟨y, hy, rfl⟩, hy2⟩)

theorem exists_lift_of_isDC (hJ : J ≤ H) (a : H) (R' : Finset Γ) (h : Bridge.IsDC J (a : Γ) R') :
    ∃ R : Finset H, R.map (Function.Embedding.subtype _) = R' := by
  classical
  refine ⟨R'.subtype (· ∈ H), Finset.subtype_map_of_mem fun b hb => ?_⟩
  obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
  exact H.mul_mem (H.mul_mem (hJ k₁.2) a.2) (hJ k₂.2)

end Cosets

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem levChi_flag {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  have hs' : (flagL L).s = 0 := hs
  have hQ' : (flagL L).Q = ∅ := hQ
  unfold levChi levFn
  rw [h2, hs', hQ']
  simp

theorem levChi_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flag1L L) κ = 1 := by
  rw [← levChi_flag (β := β) hs hQ κ]
  unfold levChi
  rw [levFn_flag1]

theorem hasType_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (P : LevelP L.Pg L.r ℂ)
    {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) : HasType V β (flag1L L) F := by
  intro κ hκ h
  have e : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  have hm : κ ∈ levG V β (withP L P) := by
    refine ⟨hκ.1, hκ.2.1, ?_⟩
    show rTup β L (finE V κ) ∈ P.H
    rw [e]; exact P.H.one_mem
  rw [hF κ hm h]
  unfold levChi
  rw [levFn_withP, e, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem gaL_apply {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) (κ : G → GA D V) (hκ : ∀ g, IsLevelLift V β L (eG g) (κ g)) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * F (h * κ g) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  have := level_action_spec hF ⟨κ g, hκ g⟩ (κ g) (hκ g) h
  rw [levChi_flag hs hQ, inv_one, one_mul] at this
  rw [← this]
  rfl

theorem alg_sum (M : DSModel V S) {ι : Type} (s : Finset ι) (κ : ι → GfC V) (c : ι → ℂ) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (∑ i ∈ s, MonoidAlgebra.single (κ i) (c i) - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, ∑ i ∈ s, c i * T v (x * (κ i : GA D V)) = a * T v x := by
  rw [map_sub, map_sum, LinearMap.sub_apply, sub_eq_zero, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, map_one, LinearMap.smul_apply, Module.End.one_apply]
  rw [MultilinearMap.ext_iff]
  refine forall_congr' fun v => ?_
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  rw [MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem alg_one (M : DSModel V S) (k : GfC V) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (MonoidAlgebra.single k 1 - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, T v (x * (k : GA D V)) = a * T v x := by
  have := alg_sum M (Finset.univ : Finset Unit) (fun _ => k) (fun _ => 1) a T
  simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using this

theorem mem_hPart (M : DSModel V S) (J : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (T : MMap M) :
    T ∈ hPart M J ok pl q Sg ↔ ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α, IsHeckeAt V (pl P) k α → ∀ R, Bridge.IsDC J α⁻¹ R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T v x := by
  unfold hPart
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_hecke_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ hPart M (levG V β (flag1L L)) ok pl q Sg = allMaps θ M ⊓ killed (finRep M) (eqSet V β L eG c P ok pl q Sg) := by
  intro D V S θ M β L G _ _ eG c P Pl0 ok pl q Sg hs hQ hlift
  have hJ : levG V β (flag1L L) ≤ GfC V := fun _ h => h.1
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_goodPart, mem_killed, mem_hPart, GlobalTheory.MultMem.mem_mult_iff,
    GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · rintro ⟨⟨hm, hg⟩, hh⟩
    refine ⟨⟨hm.aut, hm.cusp, fun _ _ h => h.elim, hm.equiv, hm.cont⟩, ?_⟩
    rintro x ((⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩)
    · exact (alg_one M k _ T).2 fun v x => hm.lev v k hk x
    · refine (alg_sum M _ κ c 1 T).2 fun v x => ?_
      have hF : HasType V β (flag1L L) (T v) := hasType_flag1 P fun k hk h => hm.lev v k hk h
      rw [← gaL_apply hs hQ eG c hF (fun g => κ g) hκ x, hg v, one_mul]
    · refine (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
      have := hh P0 hP0 k hk α hα _ ((isDC_sub_iff hJ α⁻¹ R).1 hR) v x
      rw [Finset.sum_map] at this
      simp only [one_mul]
      exact this
  · rintro ⟨hm, hk⟩
    have hlev : ∀ v, HasType V β (withP L P) (T v) := fun v k hkk x =>
      (alg_one M ⟨k, hkk.1⟩ _ T).1 (hk _ (Or.inl (Or.inl ⟨⟨k, hkk.1⟩, hkk, rfl⟩))) v x
    refine ⟨⟨⟨hm.aut, hm.cusp, fun v k hkk x => hlev v k hkk x, hm.equiv, hm.cont⟩, fun v => ?_⟩, ?_⟩
    · choose κ hκ using fun g => hlift (eG g)
      funext x
      rw [gaL_apply hs hQ eG c (hasType_flag1 P (hlev v)) κ hκ x]
      have := (alg_sum M Finset.univ (fun g => (⟨κ g, (hκ g).1⟩ : GfC V)) c 1 T).1
        (hk _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))) v x
      rw [one_mul] at this
      exact this
    · intro P0 hP0 k hkr α hα R' hR' v x
      have hαf : α ∈ GfC V := by
        obtain ⟨e, ϖ, -, -, -, h⟩ := hα
        exact h.1
      obtain ⟨R, rfl⟩ := exists_lift_of_isDC hJ (⟨α, hαf⟩ : GfC V)⁻¹ R' hR'
      have hR := (isDC_sub_iff hJ (⟨α, hαf⟩ : GfC V)⁻¹ R).2 hR'
      have := (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).1
        (hk _ (Or.inr ⟨P0, hP0, k, hkr, ⟨α, hαf⟩, R, hα, hR, rfl⟩)) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.EqCut

end
