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

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinAdIdent

section Groups

variable {G G' : Type} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'}

def Corr (φ : H ≃* H') (A : Set G) (A' : Set G') : Prop :=
  (∀ g ∈ A, g ∈ H) ∧ (∀ g ∈ A', g ∈ H') ∧ ∀ g : H, (g : G) ∈ A ↔ (φ g : G') ∈ A'

theorem Corr.symm {φ : H ≃* H'} {A : Set G} {A' : Set G'} (h : Corr φ A A') : Corr φ.symm A' A := by
  refine ⟨h.2.1, h.1, fun g => ?_⟩
  rw [h.2.2 (φ.symm g), MulEquiv.apply_symm_apply]

theorem Corr.lift {φ : H ≃* H'} {A : Set G} {A' : Set G'} (h : Corr φ A A') {x : G'} (hx : x ∈ A') :
    ∃ g : H, (g : G) ∈ A ∧ (φ g : G') = x := by
  refine ⟨φ.symm ⟨x, h.2.1 x hx⟩, ?_, by simp⟩
  rw [h.2.2, MulEquiv.apply_symm_apply]
  exact hx

theorem Corr.cosets {φ : H ≃* H'} {K R : Set G} {K' R' : Set G'} (hK : Corr φ K K') (hR : Corr φ R R') (α : H)
    (h : (∀ γ ∈ R, γ ∈ H ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    (∀ γ ∈ R', γ ∈ H' ∧ ∃ k₁ ∈ K', ∃ k₂ ∈ K', γ = k₁ * φ α * k₂) ∧
      ∀ x : G', (∃ k₁ ∈ K', ∃ k₂ ∈ K', x = k₁ * φ α * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ K' := by
  obtain ⟨h₁, h₂⟩ := h
  have memK : ∀ g : H, (g : G) ∈ K ↔ (φ g : G') ∈ K' := hK.2.2
  refine ⟨fun γ' hγ' => ?_, fun x' hx' => ?_⟩
  · obtain ⟨γ, hγR, rfl⟩ := hR.lift hγ'
    obtain ⟨-, k₁, hk₁, k₂, hk₂, heq⟩ := h₁ γ hγR
    have e : γ = ⟨k₁, hK.1 k₁ hk₁⟩ * α * ⟨k₂, hK.1 k₂ hk₂⟩ := Subtype.ext heq
    refine ⟨hR.2.1 _ hγ', _, (memK ⟨k₁, hK.1 k₁ hk₁⟩).mp hk₁, _, (memK ⟨k₂, hK.1 k₂ hk₂⟩).mp hk₂, ?_⟩
    rw [e, map_mul, map_mul]
    rfl
  · obtain ⟨k₁', hk₁', k₂', hk₂', rfl⟩ := hx'
    obtain ⟨k₁, hk₁, rfl⟩ := hK.lift hk₁'
    obtain ⟨k₂, hk₂, rfl⟩ := hK.lift hk₂'
    obtain ⟨γ, ⟨hγR, hγK⟩, huniq⟩ := h₂ ((k₁ * α * k₂ : H) : G) ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have key : ∀ c : H, (c : G)⁻¹ * ((k₁ * α * k₂ : H) : G) ∈ K ↔
        (φ c : G')⁻¹ * ((φ k₁ : G') * (φ α : G') * (φ k₂ : G')) ∈ K' := by
      intro c
      have := memK (c⁻¹ * (k₁ * α * k₂))
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this
    let g : H := ⟨γ, (h₁ γ hγR).1⟩
    refine ⟨φ g, ⟨(hR.2.2 g).mp hγR, (key g).mp hγK⟩, ?_⟩
    rintro y' ⟨hy'R, hy'K⟩
    obtain ⟨c, hcR, rfl⟩ := hR.lift hy'R
    have hc : c = g := Subtype.ext (huniq c ⟨hcR, (key c).mpr hy'K⟩)
    rw [hc]

end Groups

variable {D : D7}

structure Link (V V' : HSp D) (M : ℕ) (φ : GfC V ≃* GfC V')
    (J : Matrix (Fin V'.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (J' : Matrix (Fin V.rank) (Fin V'.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Prop where
  rank : V.rank = V'.rank
  h1 : mmul J J' = 1
  h2 : mmul J' J = 1
  hc : ∀ g : GfC V, mmul (finMat D.sp.cm.sig V'.gram (φ g : GA D V')) J = mmul J (finMat D.sp.cm.sig V.gram (g : GA D V))
  lat : ∀ f, Good (D := D) M f → ∀ y, f • y ∈ Formalism.L2.NTheta.LamHat V ↔ f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V'
  loc : ∀ f, Good (D := D) M f → ∀ y ∈ Formalism.L2.NTheta.LamHat V, f • y ∈ Formalism.L2.NTheta.LamHat V
  loc' : ∀ f, Good (D := D) M f → ∀ y ∈ Formalism.L2.NTheta.LamHat V', f • y ∈ Formalism.L2.NTheta.LamHat V'

theorem suppF_iff (f : Formalism.L2.Theta.AE D) {V : HSp D} {α : GA D V} (hα : α ∈ GfC V) :
    SuppF V f α ↔ finPart D f • (finMat D.sp.cm.sig V.gram α - 1) = finMat D.sp.cm.sig V.gram α - 1 := by
  rw [GlobalTheory.HeckeTrans.finMat_eq, GlobalTheory.HeckeTrans.supp_map_iff]
  refine ⟨fun hs i j => by rw [hs i j], fun hs i j => ?_⟩
  refine GlobalTheory.FinIsoGrp.proj_inj D _ _ ?_ (congrArg (swapAE D) ?_)
  · show infPart D _ = infPart D _
    have hij := congrFun (congrFun (GlobalTheory.HeckeTrans.inf_eq hα) i) j
    rw [Matrix.map_apply] at hij
    have h0 : infPart D ((mt V α - 1) i j) = 0 := by
      rw [Matrix.sub_apply, map_sub, hij]
      by_cases hh : i = j <;> simp [Matrix.one_apply, hh]
    rw [map_mul, h0, mul_zero]
  · exact hs i j

namespace Link

variable {V V' : HSp D} {M : ℕ} {φ : GfC V ≃* GfC V'}
  {J : Matrix (Fin V'.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
  {J' : Matrix (Fin V.rank) (Fin V'.rank) (Af D.host.F ⊗[D.host.F] D.host.E)} (h : Link V V' M φ J J')
include h

theorem symm : Link V' V M φ.symm J' J where
  rank := h.rank.symm
  h1 := h.h2
  h2 := h.h1
  hc := fun g => by
    have e := h.hc (φ.symm g)
    rw [MulEquiv.apply_symm_apply] at e
    have e' : finMat D.sp.cm.sig V'.gram (g : GA D V') * J = J * finMat D.sp.cm.sig V.gram (φ.symm g : GA D V) := e
    have h1' : J * J' = 1 := h.h1
    have h2' : J' * J = 1 := h.h2
    show finMat D.sp.cm.sig V.gram (φ.symm g : GA D V) * J' = J' * finMat D.sp.cm.sig V'.gram (g : GA D V')
    calc finMat D.sp.cm.sig V.gram (φ.symm g : GA D V) * J'
        = (J' * J) * finMat D.sp.cm.sig V.gram (φ.symm g : GA D V) * J' := by rw [h2', Matrix.one_mul]
      _ = J' * (J * finMat D.sp.cm.sig V.gram (φ.symm g : GA D V)) * J' := by simp only [Matrix.mul_assoc]
      _ = J' * (finMat D.sp.cm.sig V'.gram (g : GA D V') * J) * J' := by rw [← e']
      _ = J' * finMat D.sp.cm.sig V'.gram (g : GA D V') * (J * J') := by simp only [Matrix.mul_assoc]
      _ = J' * finMat D.sp.cm.sig V'.gram (g : GA D V') := by rw [h1', Matrix.mul_one]
  lat := fun f hf y => by
    have h1' : J * J' = 1 := h.h1
    rw [h.lat f hf (J'.mulVec y), Matrix.mulVec_mulVec, h1', Matrix.one_mulVec]
  loc := h.loc'
  loc' := h.loc

theorem supp (f : Formalism.L2.Theta.AE D) (g : GfC V) : SuppF V f (g : GA D V) ↔ SuppF V' f (φ g : GA D V') := by
  have h1' : J * J' = 1 := h.h1
  have h2' : J' * J = 1 := h.h2
  have hc : finMat D.sp.cm.sig V'.gram (φ g : GA D V') * J = J * finMat D.sp.cm.sig V.gram (g : GA D V) := h.hc g
  rw [suppF_iff f g.2, suppF_iff f (φ g).2]
  exact ⟨fun hs => GlobalTheory.HeckeTrans.supp_conj h1' hc hs,
    fun hs => GlobalTheory.HeckeTrans.supp_conj h2' (GlobalTheory.HeckeTrans.conj_inv h1' h2' hc) hs⟩

theorem det (g : GfC V) : (Formalism.L2.Theta.mt V' (φ g : GA D V')).det = (Formalism.L2.Theta.mt V (g : GA D V)).det := by
  have h1' : J * J' = 1 := h.h1
  have h2' : J' * J = 1 := h.h2
  have hc : finMat D.sp.cm.sig V'.gram (φ g : GA D V') * J = J * finMat D.sp.cm.sig V.gram (g : GA D V) := h.hc g
  refine GlobalTheory.FinIsoGrp.proj_inj D _ _ ?_ (congrArg (swapAE D) ?_)
  · show infPart D _ = infPart D _
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      GlobalTheory.HeckeTrans.inf_eq (φ g).2, GlobalTheory.HeckeTrans.inf_eq g.2, Matrix.det_one, Matrix.det_one]
  · show finPart D _ = finPart D _
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      ← GlobalTheory.HeckeTrans.finMat_eq, ← GlobalTheory.HeckeTrans.finMat_eq]
    exact GlobalTheory.HeckeTrans.det_conj h1' h2' hc

theorem stab {f : Af D.host.F ⊗[D.host.F] D.host.E} (hf : Good M f) (g : GfC V)
    (hs : f • (finMat D.sp.cm.sig V.gram (g : GA D V) - 1) = finMat D.sp.cm.sig V.gram (g : GA D V) - 1) :
    (∀ y, y ∈ Formalism.L2.NTheta.LamHat V ↔ (finMat D.sp.cm.sig V.gram (g : GA D V)).mulVec y ∈ Formalism.L2.NTheta.LamHat V) ↔
    ∀ y, y ∈ Formalism.L2.NTheta.LamHat V' ↔
      (finMat D.sp.cm.sig V'.gram (φ g : GA D V')).mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  have h1' : J * J' = 1 := h.h1
  have hc : finMat D.sp.cm.sig V'.gram (φ g : GA D V') * J = J * finMat D.sp.cm.sig V.gram (g : GA D V) := h.hc g
  rw [stab_part (h.loc f hf) hs, stab_part (h.loc' f hf) (GlobalTheory.HeckeTrans.supp_conj h1' hc hs)]
  exact stab_pred (p := fun y => f • y ∈ Formalism.L2.NTheta.LamHat V) (p' := fun y => f • y ∈ Formalism.L2.NTheta.LamHat V')
    h1' hc (h.lat f hf)

theorem sph_imp (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (M : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S) (g : GfC V)
    (hg : (g : GA D V) ∈ KsphC V S) : (φ g : GA D V') ∈ KsphC V' S := by
  obtain ⟨f₀, hf₀, hev⟩ := good_away S M hS
  have hs := supp_away S hev (finMat D.sp.cm.sig V.gram (g : GA D V)) hg.2.2
  refine ⟨(φ g).2, (h.stab hf₀ g hs).mp hg.2.1, fun v hv => ?_⟩
  let ψ := (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e1 := GlobalTheory.HeckeTrans.map_conj ψ (h.hc g)
  have e2 : J.map ψ * J'.map ψ = 1 := GlobalTheory.HeckeTrans.map_mul_one ψ h.h1
  have e3 : (finMat D.sp.cm.sig V.gram (g : GA D V)).map ψ = 1 := hg.2.2 v hv
  rw [e3, Matrix.mul_one] at e1
  show (finMat D.sp.cm.sig V'.gram (φ g : GA D V')).map ψ = 1
  calc (finMat D.sp.cm.sig V'.gram (φ g : GA D V')).map ψ
      = (finMat D.sp.cm.sig V'.gram (φ g : GA D V')).map ψ * (J.map ψ * J'.map ψ) := by rw [e2, Matrix.mul_one]
    _ = J.map ψ * J'.map ψ := by rw [← Matrix.mul_assoc, e1]
    _ = 1 := e2

theorem sphLoc {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal)
    (g : GfC V) (hs : SuppF V f (g : GA D V)) : (g : GA D V) ∈ KsphC V ∅ ↔ (φ g : GA D V') ∈ KsphC V' ∅ := by
  obtain ⟨-, hfg, -⟩ := good_of_primeIdem hP hM
  have key := h.stab hfg g ((suppF_iff f g.2).mp hs)
  constructor
  · rintro ⟨-, hl, -⟩
    exact ⟨(φ g).2, key.mp hl, fun v hv => by simp at hv⟩
  · rintro ⟨-, hl, -⟩
    exact ⟨g.2, key.mpr hl, fun v hv => by simp at hv⟩

theorem hecke_imp {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e P)
    (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal) {ϖ : D.host.E} {k : ℕ} (g : GfC V)
    (hg : Formalism.L2.NTheta.IsHeckeElt V e ϖ k (g : GA D V)) : Formalism.L2.NTheta.IsHeckeElt V' e ϖ k (φ g : GA D V') := by
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨hge, -, -⟩ := good_of_primeIdem hP hM
  exact GlobalTheory.HeckeTrans.transfer he.1 J J' h.h1 h.h2 (φ g).2 (h.hc g) (h.lat _ hge) (h.loc _ hge) (h.loc' _ hge) hg

theorem div_imp {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal)
    {ϖ : D.host.E} {d : List ℤ} (g : GfC V) (hg : DivAt V e ϖ d (g : GA D V)) : DivAt V' e ϖ d (φ g : GA D V') := by
  obtain ⟨hge, -, -⟩ := good_of_primeIdem hP hM
  obtain ⟨hlen, hdiv⟩ := hg
  have H : HasDiv (finPart D e) (intAE D) (fun i => finPart D (incA D (ϖ ^ d.getD i 0))) (Formalism.L2.NTheta.LamHat V)
      (finMat D.sp.cm.sig V.gram (g : GA D V)) := hdiv
  obtain ⟨B, b1, b2, b3, b4⟩ := H.conj h.rank hge.1 h.h1 (h.hc g) (h.lat _ hge) (h.loc _ hge) (h.loc' _ hge)
  exact ⟨hlen.trans h.rank, B, b1, b2, b3, b4⟩

variable {K : Set (GA D V)} {K' : Set (GA D V')} {χ : GA D V → ℂ} {χ' : GA D V' → ℂ} (hK : Corr φ K K')
  (hχ : ∀ g : GfC V, (g : GA D V) ∈ K → χ' (φ g : GA D V') = χ g)
include hK hχ

theorem level_imp {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal)
    (a : ∀ g, SuppF V f g → (g ∈ K ↔ g ∈ KsphC V ∅)) (b : ∀ g ∈ K, SuppF V f g → χ g = 1) :
    (∀ g, SuppF V' f g → (g ∈ K' ↔ g ∈ KsphC V' ∅)) ∧ (∀ g ∈ K', SuppF V' f g → χ' g = 1) ∧
      Corr φ {k | k ∈ K ∧ SuppF V f k} {k | k ∈ K' ∧ SuppF V' f k} := by
  refine ⟨fun g' hs' => ?_, fun g' hg' hs' => ?_,
    ⟨fun g hg => hK.1 g hg.1, fun g hg => hK.2.1 g hg.1, fun g => and_congr (hK.2.2 g) (h.supp f g)⟩⟩
  · by_cases hG : g' ∈ GfC V'
    · obtain ⟨g, rfl⟩ : ∃ g : GfC V, (φ g : GA D V') = g' := ⟨φ.symm ⟨g', hG⟩, by simp⟩
      have hs : SuppF V f (g : GA D V) := (h.supp f g).mpr hs'
      rw [← hK.2.2 g, a _ hs]
      exact h.sphLoc hP hM g hs
    · exact iff_of_false (fun h' => hG (hK.2.1 _ h')) (fun h' => hG h'.1)
  · obtain ⟨g, hgK, rfl⟩ := hK.lift hg'
    rw [hχ g hgK]
    exact b _ hgK ((h.supp f g).mpr hs')

variable {R : Finset (GA D V)} {R' : Finset (GA D V')} (hR : Corr φ (R : Set (GA D V)) (R' : Set (GA D V')))
include hR

theorem opAt_imp (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {P : Pl D.host.E} (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal) {k : ℕ}
    (H : IsHeckeOpAt V K χ S P k R) : IsHeckeOpAt V' K' χ' S P k R' := by
  obtain ⟨e, ϖ, α, hS, he, h1, h2, hk, hJ, hχ1, hα, hRs, hcos⟩ := H
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨l1, l2, l3⟩ := h.level_imp hK hχ hP hM hJ hχ1
  have hαG : α ∈ GfC V := hα.1
  have hc := Corr.cosets l3 hR (⟨α, hαG⟩⁻¹) hcos
  rw [map_inv] at hc
  refine ⟨e, ϖ, (φ ⟨α, hαG⟩ : GA D V'), hS, he, h1, h2, hk.trans_eq h.rank, l1, l2,
    h.hecke_imp he hM ⟨α, hαG⟩ hα, ?_, hc⟩
  intro γ hγ
  obtain ⟨g, hgR, rfl⟩ := hR.lift hγ
  exact (h.supp _ g).mp (hRs _ hgR)

theorem opFull_imp (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {P : Pl D.host.E} (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal)
    {d : List ℤ} (H : Hecke₂ V K χ S P d R) : Hecke₂ V' K' χ' S P d R' := by
  obtain ⟨e, f, ϖ, α, hS, hP, h1, h2, hd, hJ, hχ1, hαs, hdiv, hRs, hcos⟩ := H
  obtain ⟨l1, l2, l3⟩ := h.level_imp hK hχ hP hM hJ hχ1
  have hs1 : SuppF V f (1 : GA D V) := by
    intro i j
    simp [Formalism.L2.Theta.mt]
  have h1K : (1 : GA D V) ∈ K := by
    rw [hJ 1 hs1]
    refine ⟨one_mem _, fun y => ?_, fun v hv => by simp at hv⟩
    rw [GlobalTheory.HeckeTrans.finMat_eq]
    simp [Formalism.L2.Theta.mt]
  have hαG : α ∈ GfC V := by
    obtain ⟨γ, ⟨hγR, hγK⟩, -⟩ := hcos.2 α ⟨1, ⟨h1K, hs1⟩, 1, ⟨h1K, hs1⟩, by simp⟩
    have hm := mul_mem (hcos.1 γ hγR).1 (hK.1 _ hγK.1)
    rwa [mul_inv_cancel_left] at hm
  have hc := Corr.cosets l3 hR ⟨α, hαG⟩ hcos
  refine ⟨e, f, ϖ, (φ ⟨α, hαG⟩ : GA D V'), hS, hP, h1, h2, hd, l1, l2, (h.supp f ⟨α, hαG⟩).mp hαs,
    h.div_imp hP hM ⟨α, hαG⟩ hdiv, ?_, hc⟩
  intro γ hγ
  obtain ⟨g, hgR, rfl⟩ := hR.lift hγ
  exact (h.supp _ g).mp (hRs _ hgR)

end Link

end GlobalTheory.FinAdIdent

end
