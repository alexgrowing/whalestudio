import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.ExistsDenLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentMulNatPowOfMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpFullImp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinAdIdent

variable {D : D7}

theorem mem_iff_of_image {A : Type} [CommRing A] {m n : ℕ} {j : Matrix (Fin m) (Fin n) A} (hj : Function.Injective j.mulVec)
    {H : Set (Fin n → A)} {H' : Set (Fin m → A)} (h : j.mulVec '' H = H') (y : Fin n → A) : y ∈ H ↔ j.mulVec y ∈ H' := by
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rwa [← hj hzy]

theorem level_conj {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (ψ : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ψ.comp σ = τ.comp ψ) {S : Subring B} (H : Submodule S (Fin n → B)) (H' : Submodule S (Fin m → B))
    {j : Matrix (Fin m) (Fin n) A} (hb : Function.Bijective (j.map ψ).mulVec)
    (hl : (j.map ψ).mulVec '' (H : Set _) = (H' : Set _)) {J : Matrix (Fin n) (Fin n) A} {J' : Matrix (Fin m) (Fin m) A}
    {x : GL (Fin n) A} {x' : GL (Fin m) A} (hx : x ∈ Formalism.UG.UJ σ J) (hx' : x' ∈ Formalism.UG.UJ σ J') (hc : x'.val * j = j * x.val) :
    Formalism.UG.bc ψ x ∈ Formalism.UG.level τ (J.map ψ) H ↔ Formalism.UG.bc ψ x' ∈ Formalism.UG.level τ (J'.map ψ) H' := by
  have hu : ∀ {k : ℕ} {K : Matrix (Fin k) (Fin k) A} {z : GL (Fin k) A}, z ∈ Formalism.UG.UJ σ K →
      Formalism.UG.bc ψ z ∈ Formalism.UG.UJ τ (K.map ψ) := by
    intro k K z hz
    have hz' : Formalism.UG.cT σ (z : Matrix (Fin k) (Fin k) A) * K * z = K := hz
    show Formalism.UG.cT τ ((z : Matrix (Fin k) (Fin k) A).map ψ) * K.map ψ * (z : Matrix (Fin k) (Fin k) A).map ψ = K.map ψ
    conv_rhs => rw [← hz']
    simp only [Matrix.map_mul]
    congr 2
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    exact (RingHom.congr_fun h _).symm
  obtain ⟨j', hj1, -⟩ := exists_inv hb
  have hcψ : x'.val.map ψ * j.map ψ = j.map ψ * x.val.map ψ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hc]
  have key := stab_pred (p := fun y => y ∈ H) (p' := fun y => y ∈ H') hj1 hcψ (mem_iff_of_image hb.1 hl)
  have e1 : Formalism.UG.bc ψ x ∈ Formalism.UG.level τ (J.map ψ) H ↔ Formalism.UG.bc ψ x ∈ Formalism.UG.UJ τ (J.map ψ) ∧
      ∀ y, y ∈ H ↔ (x.val.map ψ).mulVec y ∈ H := Iff.rfl
  have e2 : Formalism.UG.bc ψ x' ∈ Formalism.UG.level τ (J'.map ψ) H' ↔ Formalism.UG.bc ψ x' ∈ Formalism.UG.UJ τ (J'.map ψ) ∧
      ∀ y, y ∈ H' ↔ (x'.val.map ψ).mulVec y ∈ H' := Iff.rfl
  rw [e1, e2]
  exact ⟨fun a => ⟨hu hx', key.1 a.2⟩, fun a => ⟨hu hx, key.2 a.2⟩⟩

theorem levelVL_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (Λ' : Submodule (𝓞 E) (Fin m → E))
    (G : Matrix (Fin n) (Fin n) E) (G' : Matrix (Fin m) (Fin m) E) (j : Matrix (Fin m) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hb : Function.Bijective (j.map (Formalism.UG.prV (E := E) v)).mulVec)
    (hl : (j.map (Formalism.UG.prV (E := E) v)).mulVec '' (Formalism.L2.Herm.locL v Λ : Set _) = (Formalism.L2.Herm.locL v Λ' : Set _))
    {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {x' : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ Formalism.UG.UPts σ G (Formalism.L2.Herm.Af F)) (hx' : x' ∈ Formalism.UG.UPts σ G' (Formalism.L2.Herm.Af F))
    (hc : x'.val * j = j * x.val) :
    Formalism.UG.bc (Formalism.UG.prV v) x ∈ Formalism.UG.levelVL σ G v Λ ↔ Formalism.UG.bc (Formalism.UG.prV v) x' ∈ Formalism.UG.levelVL σ G' v Λ' := by
  have h1 := level_conj (Formalism.UG.prV (E := E) v) (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) (Formalism.UG.sigR σ (v.adicCompletion F))
    (Formalism.UG.P.afsplit_prV_comp_sigR σ v) (Formalism.L2.Herm.locL v Λ) (Formalism.L2.Herm.locL v Λ') hb hl hx hx' hc
  have hG : ∀ {k : ℕ} (K : Matrix (Fin k) (Fin k) E),
      (K.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))).map (Formalism.UG.prV (E := E) v) =
        K.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) := by
    intro k K
    ext a b
    simp only [Matrix.map_apply]
    exact Formalism.UG.P.afsplit_prV_inclE v (K a b)
  rw [hG, hG] at h1
  exact h1

open GlobalTheory.HeckeTrans in
set_option maxHeartbeats 800000 in
theorem link_of_isLatIsom {V V' : HSp D} (h : V.rank = V'.rank)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)}
    {β : GL (Fin V.rank) (EAf D)} {β' : GL (Fin V'.rank) (EAf D)} {N N' : ℕ}
    (hβ : IsSDFrame V β Λ N) (hβ' : IsSDFrame V' β' Λ' N') {j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)}
    {j' : Matrix (Fin V.rank) (Fin V'.rank) (EAf D)} (hj : IsLatIsom V V' Λ Λ' j) (h1 : mmul j j' = 1) (h2 : mmul j' j = 1)
    {φ : GfC V ≃ₜ* GfC V'} (hφ : IsConjBy V V' j φ) :
    Link V V' (N * N') φ.toMulEquiv (j.map (unswap D)) (j'.map (unswap D)) := by
  obtain ⟨c, hB⟩ := hβ
  obtain ⟨c', hB'⟩ := hβ'
  have himg : ∀ x, x ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) ↔
      j.mulVec x ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ' : Set _) :=
    mem_iff_of_image hj.1.1.1 hj.2
  have hvec : ∀ (f : Af D.host.F ⊗[D.host.F] D.host.E) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E),
      (fun a => swapAE D (f * ((j.map (unswap D)).mulVec y) a)) = j.mulVec (fun b => swapAE D (f * y b)) := by
    intro f y
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, swap_unswap]
    exact Finset.sum_congr rfl fun b _ => by ring
  have gN : ∀ f, Good (D := D) (N * N') f → Good (N ^ c) f := fun f hf => hf.pow c
  have gN' : ∀ f, Good (D := D) (N * N') f → Good (N' ^ c') f := by
    intro f hf
    rw [mul_comm] at hf
    exact hf.pow c'
  refine ⟨h, GlobalTheory.HeckeTrans.map_mul_one _ h1, GlobalTheory.HeckeTrans.map_mul_one _ h2, ?_, ?_, ?_, ?_⟩
  · intro g
    have := congrArg (fun X => X.map (unswap D)) (hφ g)
    simp only [mmul, Matrix.map_mul, finE_unswap] at this
    exact this
  · intro f hf y
    rw [(lamHat_good hB (gN f hf)).2, (lamHat_good hB' (gN' f hf)).2, hvec]
    exact himg _
  · intro f hf y hy
    exact (lamHat_good hB (gN f hf)).1 y hy
  · intro f hf y hy
    exact (lamHat_good hB' (gN' f hf)).1 y hy

theorem corr_inA {V V' : HSp D} (φ : GfC V ≃ₜ* GfC V') (R : Finset (GfC V)) :
    Corr φ.toMulEquiv (inA V R : Set (GA D V)) (imA φ R : Set (GA D V')) := by
  refine ⟨?_, ?_, fun g => ?_⟩
  · intro g hg
    simp only [inA, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hg
    obtain ⟨a, -, rfl⟩ := hg
    exact a.2
  · intro g hg
    simp only [imA, inA, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hg
    obtain ⟨a, -, rfl⟩ := hg
    exact a.2
  · simp [inA, imA]
    exact ⟨fun hg => ⟨g.1, g.2, hg, rfl⟩, fun ⟨a, ha, hR, hag⟩ => hag ▸ hR⟩

theorem chi_symm {G G' : Type} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'} {φ : H ≃* H'} {K : Set G} {K' : Set G'}
    (hK : Corr φ K K') {χ : G → ℂ} {χ' : G' → ℂ} (hχ : ∀ g : H, (g : G) ∈ K → χ' (φ g : G') = χ g) (g : H')
    (hg : (g : G') ∈ K') : χ (φ.symm g : G) = χ' g := by
  have h1 : ((φ.symm g : H) : G) ∈ K := (hK.2.2 (φ.symm g)).2 (by simpa using hg)
  have h2 := hχ (φ.symm g) h1
  simpa using h2.symm

private theorem finE_mem_UPts (V : HSp D) (g : GA D V) :
    finE V g ∈ Formalism.UG.UPts D.sp.cm.sig V.gram (Formalism.L2.Herm.Af D.host.F) := by
  have hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) ((matHom V g : GL _ _) : Matrix _ _ _) *
      JR (AF D.host.F) V.gram * ((matHom V g : GL _ _) : Matrix _ _ _) = JR (AF D.host.F) V.gram := g.2
  show Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ((finE V g : GL _ _) : Matrix _ _ _) *
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * ((finE V g : GL _ _) : Matrix _ _ _) =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  have := congrArg (fun X => X.map (GlobalTheory.FinIsoGrp.qFin D)) hg
  simp only [Matrix.map_mul] at this
  rw [GlobalTheory.FinIsoGrp.finE_val, ← GlobalTheory.FinIsoGrp.gram_map, ← this]
  congr 2
  ext a b
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.FinIsoGrp.qFin_sig]

set_option maxHeartbeats 1600000 in
theorem inducedIso (D : D7) : InducedIso D := by
  intro V V' h Λ Λ' β β' N N' hβ hβ' T j hj hm
  obtain ⟨j', h1, h2⟩ := exists_inv hj.1.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.FinIsoGrp.exists_finIso V V' j j' h1 h2 hj.1.2
  have hφ' : IsConjBy V V' j φ := hφ
  have L := link_of_isLatIsom h hβ hβ' hj h1 h2 hφ'
  obtain ⟨c, hB⟩ := id hβ
  obtain ⟨c', hB'⟩ := id hβ'
  obtain ⟨u, hu, hT⟩ := hm
  have hl : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ', j'.mulVec y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    ((image_iff h1 h2 _ _).1 hj.2).2
  have e : ∀ {W : HSp D} (γ : GL (Fin W.rank) (EAf D)) (L1 : Formalism.L2.DIV.LevDat D.host.E ℂ W.rank) (κ : GA D W),
      κ ∈ levG W γ L1 ↔ κ ∈ GfC W ∧ finE W κ ∈ Formalism.L2.DIV.parLev D.sp.cm W.gram γ L1 ∧
        Formalism.L2.DIV.rTup γ L1 (finE W κ) ∈ L1.P.H := fun _ _ _ => Iff.rfl
  have hle := fun (L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hL0 : ReadIn L0 T) (g : GfC V) =>
    lev_eq h V.gram V'.gram Λ Λ' β (finE V g) β' (finE V' (φ g)) hB.1 hB'.1 j j' h1 h2 hl u hu T hT (hφ g)
      (finE_mem_UPts V g) (finE_mem_UPts V' (φ g)) L0 hL0
  have hlev : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T → ∀ g : GfC V,
      (g : GA D V) ∈ levG V β L0 ↔ (φ g : GA D V') ∈ levG V' β' (castDat h L0) := by
    intro L0 hL0 g
    have H := hle L0 hL0 g
    rw [e, e]
    constructor
    · rintro ⟨-, hp, hr⟩
      exact ⟨(φ g).2, H.1.1 hp, (H.2 hp).1 ▸ hr⟩
    · rintro ⟨-, hp', hr'⟩
      have hp := H.1.2 hp'
      exact ⟨g.2, hp, (H.2 hp).1 ▸ hr'⟩
  have hchi : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T → ∀ g : GfC V, (g : GA D V) ∈ levS V β L0 →
      levChi V' β' (castDat h L0) (φ g : GA D V') = levChi V β L0 (g : GA D V) := by
    intro L0 hL0 g hg
    have hp := ((e β L0 g).1 hg).2.1
    have H := (hle L0 hL0 g).2 hp
    unfold levChi
    rw [H.2]
  have hK : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T →
      Corr φ.toMulEquiv (levS V β L0) (levS V' β' (castDat h L0)) := fun L0 hL0 =>
    ⟨fun g hg => ((e β L0 g).1 hg).1, fun g hg => ((e β' (castDat h L0) g).1 hg).1, fun g => hlev L0 hL0 g⟩
  refine ⟨φ, hφ', ?_⟩
  exact {
    stabLoc := fun v g => by
      obtain ⟨hb, hl'⟩ := loc_gen D.sp.cm.sig v Λ Λ' V.gram V'.gram j hj.1.1 hj.1.2 hj.2
      exact levelVL_conj D.sp.cm.sig v Λ Λ' V.gram V'.gram j hb.1 hl' (finE_mem_UPts V g) (finE_mem_UPts V' (φ g)) (hφ g)
    supp := fun f g => L.supp f g
    det := fun g => L.det g
    lev := hlev
    chi := hchi
    lift := fun L0 hL0 g0 g => by
      have H := hle L0 hL0 g
      unfold IsLevelLift
      constructor
      · rintro ⟨-, hp, hr⟩
        exact ⟨(φ g).2, H.1.1 hp, (H.2 hp).1.trans hr⟩
      · rintro ⟨-, hp', hr'⟩
        have hp := H.1.2 hp'
        exact ⟨g.2, hp, (H.2 hp).1.symm.trans hr'⟩
    sph := fun S hS g => ⟨L.sph_imp S hS g, fun hg => by simpa using L.symm.sph_imp S hS (φ g) hg⟩
    heckeElt := fun P e ϖ k hM he g =>
      ⟨L.hecke_imp he hM g, fun hg => by simpa using L.symm.hecke_imp he hM (φ g) hg⟩
    heckeAt := fun P k hM g => by
      unfold IsHeckeAt
      constructor
      · rintro ⟨e, ϖ, he, h1', h2', h3⟩
        exact ⟨e, ϖ, he, h1', h2', L.hecke_imp he hM g h3⟩
      · rintro ⟨e, ϖ, he, h1', h2', h3⟩
        exact ⟨e, ϖ, he, h1', h2', by simpa using L.symm.hecke_imp he hM (φ g) h3⟩
    divAt := fun P e f ϖ d hM hP g =>
      ⟨L.div_imp hP hM g, fun hg => by simpa using L.symm.div_imp hP hM (φ g) hg⟩
    opAt := fun L0 hL0 S P k hM R =>
      ⟨fun H => L.opAt_imp (hK L0 hL0) (hchi L0 hL0) (corr_inA φ R) S hM H,
        fun H => L.symm.opAt_imp (hK L0 hL0).symm (chi_symm (hK L0 hL0) (hchi L0 hL0)) (corr_inA φ R).symm S hM H⟩
    opFull := fun L0 hL0 S P d hM R =>
      ⟨fun H => L.opFull_imp (hK L0 hL0) (hchi L0 hL0) (corr_inA φ R) S hM H,
        fun H => L.symm.opFull_imp (hK L0 hL0).symm (chi_symm (hK L0 hL0) (hchi L0 hL0)) (corr_inA φ R).symm S hM H⟩ }

end GlobalTheory.FinAdIdent

end
