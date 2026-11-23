import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLevFnPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpFrame

open Formalism.CohomologicalDescent.DepthNonnegative

def Embeds (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam mu : ι → ℕ → ℕ) (ϖ : O) (Gm : Type) [AddCommGroup Gm]
    [Module (alg O N lam) Gm] : Prop :=
  ∃ ψ : Gm →+ (NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))), Function.Injective ψ ∧
    (∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = c • ψ z) ∧
    (∀ g z y, ψ z = Submodule.Quotient.mk y → ψ (grpA O N lam g • z) = Submodule.Quotient.mk (grp O N mu g y)) ∧
    ∀ τ w (a : alg O N lam) (a' : Module.End O (NablaT O N mu)), IsProj O N lam τ w a → IsProj O N mu τ w a' →
      ∀ z y, ψ z = Submodule.Quotient.mk y → ψ (a • z) = Submodule.Quotient.mk (a' y)

def SubQ (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O) (Gm : Type) [AddCommGroup Gm]
    [Module (alg O N lam) Gm] : Prop :=
  ∃ (U : Submodule (alg O N lam) (NablaT O N lam)) (π : U →ₗ[alg O N lam] Gm), Function.Surjective π ∧
    ∀ (x : U) (y : NablaT O N lam), (x : NablaT O N lam) = ϖ • y → π x = 0

section Tests

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O)

def redKer : Submodule (alg O N lam) (NablaT O N lam) where
  carrier := (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N lam))
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  smul_mem' c x hx := by
    refine Submodule.smul_induction_on (p := fun x => c • x ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N lam))) hx
      (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · show (c : Module.End O (NablaT O N lam)) (r • y) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem_smul hr trivial
    · show (c : Module.End O (NablaT O N lam)) (x + y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ hx hy

local instance algRing : Ring (alg O N lam) := Subalgebra.toRing _

set_option synthInstance.maxHeartbeats 200000 in

theorem subQ_red : SubQ O N lam ϖ (NablaT O N lam ⧸ redKer O N lam ϖ) := by
  refine ⟨⊤, (redKer O N lam ϖ).mkQ ∘ₗ (⊤ : Submodule (alg O N lam) (NablaT O N lam)).subtype, fun z => ?_, fun x y h => ?_⟩
  · obtain ⟨x, rfl⟩ := (redKer O N lam ϖ).mkQ_surjective z
    exact ⟨⟨x, trivial⟩, rfl⟩
  · refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    show (x : NablaT O N lam) ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N lam))
    rw [h]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) trivial

set_option synthInstance.maxHeartbeats 200000 in

theorem embeds_red [Fintype ι] : Embeds O N lam lam ϖ (NablaT O N lam ⧸ redKer O N lam ϖ) := by
  let ψ : (NablaT O N lam ⧸ redKer O N lam ϖ) →+ (NablaT O N lam ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N lam))) :=
    QuotientAddGroup.map (redKer O N lam ϖ).toAddSubgroup (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N lam)).toAddSubgroup
      (AddMonoidHom.id _) fun _ h => h
  have hψ : ∀ x, ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun _ => rfl
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun z hz => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.Quotient.mk_eq_zero _).2 ((Submodule.Quotient.mk_eq_zero _).1 ((hψ x).symm.trans hz))
  have hact : ∀ (a : alg O N lam) z y, ψ z = Submodule.Quotient.mk y →
      ψ (a • z) = Submodule.Quotient.mk ((a : Module.End O (NablaT O N lam)) y) := fun a z y h => by
    rw [hinj (h.trans (hψ y).symm)]
    rfl
  refine ⟨ψ, hinj, fun c z => ?_, fun g z y h => hact _ z y h, fun τ w a a' ha ha' z y h => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [hact _ _ x (hψ x), hψ, ← Submodule.Quotient.mk_smul]
    rfl
  · obtain ⟨b, -, hb⟩ := exists_unique_isProj O N ι lam τ w
    rw [hact a z y h, hb _ ha, hb _ ha']

set_option synthInstance.maxHeartbeats 200000 in

theorem nontrivial_red (h : ¬ IsUnit ϖ) :
    Nontrivial (NablaT O N (fun (_ : Unit) _ => 0) ⧸ redKer O N (fun (_ : Unit) _ => 0) ϖ) := by
  have h1 : (1 : MvPolynomial (Fin N × Fin N) O) ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N (Formalism.CohomologicalDescent.LD.res N fun _ : ℕ => 0) := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · exact MvPolynomial.isWeightedHomogeneous_one (R := O) (Formalism.GradedWeylDivisibility.colW N N)
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro a b _
      simp
  let f : NablaT O N (fun (_ : Unit) _ => 0) →ₗ[O] O := (MvPolynomial.lcoeff O 0) ∘ₗ (Submodule.subtype _) ∘ₗ
    (PiTensorProduct.subsingletonEquiv (R := O)
      (s := fun _ : Unit => Formalism.GradedWeylDivisibility.dualWeyl O N N (Formalism.CohomologicalDescent.LD.res N fun _ : ℕ => 0)) ()).toLinearMap
  refine Submodule.Quotient.nontrivial_iff.2 fun ht => h ?_
  have h2 : (PiTensorProduct.tprod O fun _ : Unit => ⟨1, h1⟩ : NablaT O N (fun (_ : Unit) _ => 0)) ∈
      redKer O N (fun (_ : Unit) _ => 0) ϖ := ht ▸ Submodule.mem_top
  have h3 : ∀ x ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (fun (_ : Unit) _ => 0))), f x ∈ Ideal.span {ϖ} := fun x hx =>
    Submodule.smul_induction_on (p := fun x => f x ∈ Ideal.span {ϖ}) hx
      (fun r hr y _ => by rw [map_smul]; exact Ideal.mul_mem_right _ _ hr) fun x y hx hy => by rw [map_add]; exact add_mem hx hy
  have h4 := h3 _ h2
  simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.subsingletonEquiv_apply_tprod] at h4
  exact isUnit_of_dvd_one (by simpa [Ideal.mem_span_singleton] using h4)

end Tests

theorem exists_levelAction {l : ℕ} [Fact l.Prime] {J : Type} [Group J] {ι : Type} [Fintype ι] {n : ℕ} {A : Type} [CommRing A] (S : Subring A)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (ev : ι → (A →+* PadicAlgCl l)) (h2 : ∀ τ z, ev τ z ∈ K)
    (h3 : ∀ τ, ∀ z ∈ S, ‖ev τ z‖ ≤ 1) (y : J →* GL (Fin n) S) (χ : J →* ℂˣ) {M : ℕ} (hM : 0 < M) (hχ : ∀ κ, χ κ ^ M = 1)
    (hK : ∀ z : PadicAlgCl l, z ^ M = 1 → z ∈ K) (io : PadicAlgCl l ≃+* ℂ) (sh : ι → ℤ) :
    ∃ (kap : J →* (ι → GL (Fin n) (integralClosure ℤ_[l] K))) (chi : J →* (integralClosure ℤ_[l] K)ˣ),
      (∀ κ τ a b, GlobalTheory.AdeleEv.embInt K ((kap κ τ).val a b) = ev τ ((y κ).val a b)) ∧
      ∀ κ, io (GlobalTheory.AdeleEv.embInt K (chi κ) * ∏ τ, GlobalTheory.AdeleEv.embInt K (kap κ τ).val.det ^ sh τ) * ((χ κ : ℂˣ) : ℂ) = 1 := by
  have hmem : ∀ {x : PadicAlgCl l}, x ∈ K → ‖x‖ ≤ 1 → x ∈ (GlobalTheory.AdeleEv.embInt K).range := fun h1 h2 => by
    rw [← SetLike.mem_coe, RingHom.coe_range, GlobalTheory.AdeleEv.range_embInt]; exact ⟨h1, h2⟩
  let eR : integralClosure ℤ_[l] K ≃+* (GlobalTheory.AdeleEv.embInt K).range :=
    RingEquiv.ofBijective (GlobalTheory.AdeleEv.embInt K).rangeRestrict
      ⟨fun _ _ h => GlobalTheory.AdeleEv.embInt_injective K (congrArg (fun w : (GlobalTheory.AdeleEv.embInt K).range => (w : PadicAlgCl l)) h), (GlobalTheory.AdeleEv.embInt K).rangeRestrict_surjective⟩
  have heR : ∀ y, GlobalTheory.AdeleEv.embInt K (eR.symm y) = y := fun y => congrArg Subtype.val (eR.apply_symm_apply y)
  let φ : ι → (S →+* integralClosure ℤ_[l] K) := fun τ =>
    eR.symm.toRingHom.comp (((ev τ).comp S.subtype).codRestrict _ fun z => hmem (h2 τ _) (h3 τ _ z.2))
  let kap : J →* (ι → GL (Fin n) (integralClosure ℤ_[l] K)) := MonoidHom.pi fun τ => (Formalism.UG.bc (φ τ)).comp y
  have hz : ∀ κ, io.symm ((χ κ : ℂˣ) : ℂ) ^ M = 1 := fun κ => by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hχ, Units.val_one, map_one]
  let z : J →* integralClosure ℤ_[l] K := eR.symm.toMonoidHom.comp
    ((io.symm.toMonoidHom.comp ((Units.coeHom ℂ).comp χ)).codRestrict (GlobalTheory.AdeleEv.embInt K).range.toSubmonoid
      fun κ => hmem (hK _ (hz κ)) (by
        have := congrArg norm (hz κ)
        rw [norm_pow, norm_one] at this
        exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hM.ne').1 this).le))
  have hzv : ∀ κ, GlobalTheory.AdeleEv.embInt K (z κ) = io.symm ((χ κ : ℂˣ) : ℂ) := fun κ => heR _
  refine ⟨kap, z.toHomUnits⁻¹ * ∏ τ, ((Matrix.GeneralLinearGroup.det.comp ((Pi.evalMonoidHom _ τ).comp kap)) ^ sh τ)⁻¹,
    fun κ τ a b => heR _, fun κ => ?_⟩
  let u : (integralClosure ℤ_[l] K)ˣ →* (PadicAlgCl l)ˣ := Units.map (GlobalTheory.AdeleEv.embInt K).toMonoidHom
  have h1 : u ((z.toHomUnits⁻¹ * ∏ τ, ((Matrix.GeneralLinearGroup.det.comp ((Pi.evalMonoidHom _ τ).comp kap)) ^ sh τ)⁻¹) κ) *
      ∏ τ, u (Matrix.GeneralLinearGroup.det (kap κ τ)) ^ sh τ = (u (z.toHomUnits κ))⁻¹ := by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.finset_prod_apply, MonoidHom.zpow_apply, map_mul, map_inv,
      map_prod, map_zpow, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Finset.prod_inv_distrib, inv_mul_cancel_right]
  have h4 := congrArg Units.val h1
  rw [Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val] at h4
  simp only [Units.val_zpow_eq_zpow_val] at h4
  rw [show ((u (z.toHomUnits κ) : (PadicAlgCl l)ˣ) : PadicAlgCl l) = io.symm ((χ κ : ℂˣ) : ℂ) from hzv κ] at h4
  refine (congrArg (fun x => io x * ((χ κ : ℂˣ) : ℂ)) h4).trans ?_
  show io (io.symm _)⁻¹ * _ = 1
  rw [map_inv₀, io.apply_symm_apply, inv_mul_cancel₀ (Units.ne_zero _)]

theorem exists_intHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {J : Type} [Group J]
    (x : J →* GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) {β : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))} (hβ : β = 1)
    (h : ∀ κ, x κ ∈ Formalism.L2.DIV.St β) :
    ∃ y : J →* GL (Fin n) (Formalism.L2.Herm.intAf F E), ∀ κ a b, ((y κ).val a b : TensorProduct F E (Formalism.L2.Herm.Af F)) = (x κ).val a b := by
  subst hβ
  choose y hy using h
  have h2 : ∀ κ, Formalism.L2.DIV.intGL F E n (y κ) = x κ := fun κ => by simpa [Formalism.L2.DIV.frGL] using hy κ
  refine ⟨MonoidHom.mk' y fun κ κ' => Formalism.L2.DIV.intGL_injective (by rw [map_mul, h2, h2, h2, map_mul]), fun κ a b => ?_⟩
  exact congrArg (fun g : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)) => g.val a b) (h2 κ)

end GlobalTheory.ExpFrame

end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
open GlobalTheory.ExpFrame

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev presJ {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K]
    [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (_ : Bridge.ClassPres ι S σ ρ J χ) : Subgroup G := J

abbrev presChi {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K]
    [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) : presJ P →* ℂˣ := χ

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def hkA (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ) : Finset (Bridge.Gf (Vc D j)) := (p.R.B.L j t).hecke.hA i

def levJ (j : Fin D.R.m) (t : p.P.T) : Subgroup (Bridge.Gf (Vc D j)) := presJ (p.R.B.L j t).pres

def levChi (j : Fin D.R.m) (t : p.P.T) : levJ p j t →* ℂˣ := presChi (p.R.B.L j t).pres

def plOf (j : Fin D.R.m) (t : p.P.T) (P : (blk p j t).Pl) : HeightOneSpectrum (𝓞 D.host.E) := p.R.pl ((blk p j t).pl P)

def matOf (j : Fin D.R.m) (g : Bridge.Gf (Vc D j)) :
    Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E) := g.1.val

set_option maxHeartbeats 1600000 in

structure Tied (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (F : Frame l D.what₂.Tau N) (e0 : D.what₂.LL →+* PadicAlgCl l)
    (ix : F.I → (blk p j t).Pl × ℕ) (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) where

  rk : Fin N ≃o Fin (Vc D j).rank

  e : F.G ≃* Bridge.Gf (Vc D j)

  io : PadicAlgCl l ≃+* ℂ

  ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)

  bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)

  sh : D.what₂.Tau → ℤ

  liftFrame_embedding_base : ∀ x, io (e0 x) = D.what₂.embLL x

  half : IsHalf inc

  lab : ∀ τ, inc τ = e0.comp (Links.labLL D τ) ∨ inc τ = cj (e0.comp (Links.labLL D τ))

  ev_rat : ∀ τ x, ev τ (1 ⊗ₜ[D.host.F] x) = inc τ x

  ev_int : ∀ τ (a : FiniteAdeleRing (𝓞 D.host.F) D.host.F), (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
    ‖ev τ (a ⊗ₜ[D.host.F] 1)‖ ≤ 1

  rat : ∀ g, g ∈ F.Γ ↔ e g ∈ (Bridge.ratF (Vc D j)).range

  lev : ∀ g, g ∈ F.K ↔ e g ∈ levJ p j t

  kap : ∀ (κ : F.K) τ, (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)).val =
    ((bs τ)⁻¹).val * ((matOf j (e κ)).map (ev τ)).submatrix rk rk * (bs τ).val

  chi : ∀ (κ : F.K) (h : e κ ∈ levJ p j t),
    io (F.emb (F.chi κ) * ∏ τ, F.emb (F.kap κ τ).val.det ^ sh τ) * ((levChi p j t ⟨e κ, h⟩ : ℂˣ) : ℂ) = 1

  ix_inj : Function.Injective ix

  ix_range : ∀ i, i ∈ Set.range ix ↔ 1 ≤ i.2 ∧ i.2 ≤ N ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal

  tr : ∀ i g, g ∈ F.tr i ↔ e g ∈ hkA p j t (ix i)

  cst : ∀ i, F.cst i = 1

theorem blk_op_zero (j : Fin D.R.m) (t : p.P.T) (P : (blk p j t).Pl) : (blk p j t).op (P, 0) = 1 :=
  (p.charW.base.fam.degL j t P).1

theorem isHalf_lab {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) : IsHalf fun τ => e0.comp (Links.labLL D τ) := by
  let s : D.R.GG → (D.host.E →+* PadicAlgCl l) := fun g =>
    (e0.comp D.embE).comp (D.host.sigmaOf g : D.host.E →+* D.host.E)
  have hinj : Function.Injective s := fun g g' h =>
    (D.host.gal).symm.injective
      (AlgEquiv.ext fun x => (e0.comp D.embE).injective (RingHom.congr_fun h x))
  have hsurj : Function.Surjective s := by
    haveI := D.host.hostE_isGalois
    haveI : Finite (D.R.GG) := Finite.of_equiv _ (D.host.gal).toEquiv
    refine ((Nat.bijective_iff_injective_and_card s).2 ⟨hinj, ?_⟩).2
    rw [← Nat.card_congr (D.host.gal).toEquiv, IsGalois.card_aut_eq_finrank,
      Nat.card_eq_fintype_card, NumberField.Embeddings.card]
  have hcj : ∀ g, GlobalTheory.ExpFrame.cj (s g) = s (g * D.R.cc) := fun g => by
    ext x
    have h1 : IsCMField.complexConj D.host.E x = D.host.sigmaOf (D.R.cc) x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.conjE_apply D.host.φ₀ x).symm
    show (e0.comp D.embE) (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = (e0.comp D.embE) (D.host.sigmaOf (g * _) x)
    rw [h1, Formalism.BasicNotions.Host.sigmaOf, Formalism.BasicNotions.Host.sigmaOf, Formalism.BasicNotions.Host.sigmaOf, map_mul]
    rfl
  refine ⟨fun τ τ' h => D.eTau.injective (Subtype.ext (hinj h)), fun τ τ' h => ?_, fun i => ?_⟩
  · have h1 := hinj ((hcj (D.eTau τ).1).symm.trans h)
    have hi := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
    have hj := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ').2
    have h2 : (D.eTau τ').1.1.2 = (D.eTau τ).1.1.2 * (-1) := by rw [← h1]; rfl
    rw [hi, hj] at h2
    exact absurd h2 (by decide)
  · obtain ⟨g, rfl⟩ := hsurj i
    rcases Int.units_eq_one_or g.1.2 with hg | hg
    · refine ⟨D.eTau.symm ⟨g, (Formalism.HC.Frame.mem_Psi_iff _).2 hg⟩, Or.inl ?_⟩
      show s g = s (D.eTau (D.eTau.symm _)).1
      rw [Equiv.apply_symm_apply]
    · have hm : g * (D.R.cc)⁻¹ ∈ D.R.Psi := by
        refine (Formalism.HC.Frame.mem_Psi_iff _).2 ?_
        show g.1.2 * (-1)⁻¹ = 1
        rw [hg]; decide
      refine ⟨D.eTau.symm ⟨_, hm⟩, Or.inr ?_⟩
      show s g = GlobalTheory.ExpFrame.cj (s (D.eTau (D.eTau.symm _)).1)
      rw [Equiv.apply_symm_apply, hcj, inv_mul_cancel_right]

theorem levJ_eq (j : Fin D.R.m) (t : p.P.T) : levJ p j t = (levEnv (Vc D j) (p.R.βV j) (p.R.datVt j t)).J := rfl

theorem levChi_apply (j : Fin D.R.m) (t : p.P.T) (κ : levJ p j t) :
    levChi p j t κ = levFn (p.R.βV j) (Formalism.IndefR.Lev.flag1L (p.R.datVt j t)) (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) κ.1.1) := by
  unfold levChi
  rfl

omit p in

theorem exists_levEnv_pow (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∃ M : ℕ, 0 < M ∧ ∀ κ, (levEnv V β Lv).χ κ ^ M = 1 :=
  (GlobalTheory.AdeleEv.exists_levFn_pow β (Formalism.IndefR.Lev.flag1L Lv)).imp fun _ h => ⟨h.1, fun κ => h.2 (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) κ.1.1)⟩

theorem exists_levChi_pow (j : Fin D.R.m) (t : p.P.T) : ∃ M : ℕ, 0 < M ∧ ∀ κ, levChi p j t κ ^ M = 1 :=
  exists_levEnv_pow (Vc D j) (p.R.βV j) (p.R.datVt j t)

omit p in

theorem mem_St_of_levEnv {V : Formalism.BasicNotions.TH.HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    {g : Bridge.Gf V} (h : g ∈ (levEnv V β Lv).J) : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) g.1 ∈ St β := parLev_St h.1

omit p in

theorem exists_intHom_of {V : Formalism.BasicNotions.TH.HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} (hβ : β = 1) (J : Subgroup (Bridge.Gf V))
    (h : ∀ g ∈ J, Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) g.1 ∈ St β) :
    ∃ y : J →* GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∀ κ a b, ((y κ).val a b : Formalism.IndefR.Lev.EAf D) = Formalism.IndefR.Lev.swapAE D (κ.1.1.val a b) :=
  exists_intHom ((Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)).comp ((Bridge.Gf V).subtype.comp J.subtype)) hβ fun κ => h κ.1 κ.2

theorem exists_levInt (j : Fin D.R.m) (t : p.P.T) :
    ∃ y : levJ p j t →* GL (Fin (Vc D j).rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∀ κ a b, ((y κ).val a b : Formalism.IndefR.Lev.EAf D) = Formalism.IndefR.Lev.swapAE D (matOf j κ.1 a b) :=
  exists_intHom_of (p.betaStd.1 j) (levJ p j t) fun _ h => mem_St_of_levEnv ((levJ_eq p j t).le h)

set_option maxHeartbeats 1600000 in

theorem exists_tied (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : N = (Vc D j).rank)
    (e0 : D.what₂.LL →+* PadicAlgCl l) (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (half : IsHalf inc)
    (lab : ∀ τ, inc τ = e0.comp (Links.labLL D τ) ∨ inc τ = GlobalTheory.ExpFrame.cj (e0.comp (Links.labLL D τ))) (sh : D.what₂.Tau → ℤ) :
    ∃ (F : Frame l D.what₂.Tau N) (ix : F.I → (blk p j t).Pl × ℕ) (T : Tied p j t F e0 ix inc),
      T.sh = sh ∧ (∀ τ, T.bs τ = 1) ∧ (∀ x : 𝓞 D.what₂.LL, e0 x ∈ Set.range F.emb) ∧ Function.Injective F.emb ∧
      ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ Set.range F.emb = {x | x ∈ K ∧ ‖x‖ ≤ 1} := by
  subst hN
  obtain ⟨io, hio⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq l D.what₂.LL e0 D.what₂.embLL
  obtain ⟨M, hM, hpow⟩ := exists_levChi_pow p j t
  obtain ⟨y, hy⟩ := exists_levInt p j t
  obtain ⟨K, hK, hKe, hKM⟩ := GlobalTheory.AdeleEv.exists_field D.what₂.LL e0 hM
  choose ev hev1 hev2 hev3 using fun τ => GlobalTheory.AdeleEv.exists_ev D.host.F D.host.E (inc τ) K fun x => by
    rcases lab τ with h | h <;> rw [h] <;> exact hKe _
  obtain ⟨kap, chi, hkap, hchi⟩ := exists_levelAction _ K ev hev2 hev3 y (levChi p j t) hM hpow hKM io sh
  let F : Frame l D.what₂.Tau (Vc D j).rank :=
    { O := integralClosure ℤ_[l] K, emb := GlobalTheory.AdeleEv.embInt K, G := Bridge.Gf (Vc D j), Γ := (Bridge.ratF (Vc D j)).range,
      K := levJ p j t, kap := kap, chi := chi,
      I := {i : (blk p j t).Pl × ℕ // 1 ≤ i.2 ∧ i.2 ≤ (Vc D j).rank ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal},
      tr := fun i => hkA p j t i.1, cst := fun _ => 1 }
  let e : F.G ≃* Bridge.Gf (Vc D j) := MulEquiv.refl (Bridge.Gf (Vc D j))
  have he : ∀ g, e g = g := fun _ => rfl
  refine ⟨F, Subtype.val,
    { rk := OrderIso.refl _, e := e, io := io, ev := fun τ => (ev τ).comp (Formalism.IndefR.Lev.swapAE D), bs := fun _ => 1,
      sh := sh, liftFrame_embedding_base := fun x => RingHom.congr_fun hio x, half := half, lab := lab,
      ev_rat := fun τ x => hev1 τ x,
      ev_int := fun τ a ha => hev3 τ _ (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)),
      rat := fun g => ?_, lev := fun g => ?_, kap := fun κ τ => ?_, chi := fun κ h => ?_,
      ix_inj := Subtype.val_injective, ix_range := fun i => ⟨?_, fun h => ⟨⟨i, h⟩, rfl⟩⟩,
      tr := fun i g => ?_, cst := fun _ => rfl },
    rfl, fun _ => rfl, fun x => ?_, GlobalTheory.AdeleEv.embInt_injective K, K, hK, GlobalTheory.AdeleEv.range_embInt K⟩
  · rw [he]
  · rw [he]
  · rw [he, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    ext a b
    exact (hkap κ τ a b).trans (congrArg (ev τ) (hy κ a b))
  · exact hchi κ
  · rintro ⟨k, rfl⟩
    exact k.2
  · rw [he]
  · show e0 x ∈ Set.range (GlobalTheory.AdeleEv.embInt K)
    rw [GlobalTheory.AdeleEv.range_embInt]
    exact ⟨hKe _, GlobalTheory.AdeleEv.norm_int_le e0 x⟩

theorem nonempty_tied (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) :
    ∃ (F : Frame l D.what₂.Tau (Vc D j).rank) (ix : F.I → (blk p j t).Pl × ℕ),
      Nonempty (Tied p j t F e0 ix fun τ => e0.comp (Links.labLL D τ)) := by
  obtain ⟨F, ix, T, -⟩ := exists_tied p j t rfl e0 _ (isHalf_lab e0) (fun _ => Or.inl rfl) 0
  exact ⟨F, ix, ⟨T⟩⟩

open Classical in

def FrameAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime], ∃ (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))), F.Ok ∧ Nonempty (Tied p j (p.R.mu w) F R.e0 R.ix inc)

open Classical in

def GalAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))), F.Ok → Tied p j (p.R.mu w) F R.e0 R.ix inc →
    GalSide (AlgebraicClosure D.host.E) inc P W F R.HasBlock

def SmallAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  (Formalism.EigenvalueLevelCeiling.plc w).Prime ∧ P.Nr + 1 < Formalism.EigenvalueLevelCeiling.plc w ∧ ¬ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : ℤ) ∣ NumberField.discr D.host.E ∧
    (∀ i, subZ p j (p.R.mu w) ≤ (subZ p j (p.R.mu w)).comap ((blk p j (p.R.mu w)).op i)) ∧
    subZ p j (p.R.mu w) ≤ (blk p j (p.R.mu w)).ZH

def InRange (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i) (_ : Fin (Fm.D x i).R.m) (_ : Par)
    (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop) : Prop :=
  AtPts fun Fm x hx i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → Q Fm x hx i p j P W w

def FrameSt : Prop := InRange fun _ _ _ _ p j P W w => FrameAt p j P W w

def GalSt : Prop := InRange fun _ _ _ _ p j P W w => GalAt p j P W w

def SmallSt : Prop := InRange fun _ _ _ _ p j P _ w => SmallAt p j P w

end GlobalTheory.ExpTie

end
