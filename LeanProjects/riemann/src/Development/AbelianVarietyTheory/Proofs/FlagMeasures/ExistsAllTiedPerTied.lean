import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaKernelInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrability
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentConjugation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentActionCocycle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.Per.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Iterated

variable {G N : Type} [MeasurableSpace G] [MeasurableSpace N] {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N}
  {P P' R : G → N → ℂ}

theorem iterated_add (h : (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ)
    (h' : (∀ g, IntegrableOn (P' g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P' g n ∂ν) 𝓕 μ)
    (hR : ∀ g n, R g n = P g n + P' g n) :
    ∫ g in 𝓕, ∫ n in 𝓝, R g n ∂ν ∂μ = ∫ g in 𝓕, ∫ n in 𝓝, P g n ∂ν ∂μ + ∫ g in 𝓕, ∫ n in 𝓝, P' g n ∂ν ∂μ := by
  rw [← integral_add h.2 h'.2]
  congr 1
  funext g
  rw [← integral_add (h.1 g) (h'.1 g)]
  simp only [hR]

theorem iterated_mul (c : ℂ) (hR : ∀ g n, R g n = c * P g n) :
    ∫ g in 𝓕, ∫ n in 𝓝, R g n ∂ν ∂μ = c * ∫ g in 𝓕, ∫ n in 𝓝, P g n ∂ν ∂μ := by
  simp only [hR, integral_const_mul]

end Iterated

variable {D : D7}

theorem flag_topology (B : HSp D) {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) :
    LocallyCompactSpace (NFlag B e) ∧ SecondCountableTopology (NFlag B e) ∧ BorelSpace (NFlag B e) ∧
      Countable (NFlagQ B e) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  haveI : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
    DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
  have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
  have h2 : IsClosed (NFlag B e : Set (GA D B)) := by
    convert h1.mul_right_of_isCompact (hK.image continuous_subtype_val) using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  refine ⟨h2.locallyCompactSpace,
    (inferInstance : SecondCountableTopology (NFlag B e : Set (GA D B))), inferInstance, ?_⟩
  exact Function.Injective.countable (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))

section Invariant

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}

structure IsRatInv (ι : A.V →ₗ[D.host.E] B.V) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E)
    (Q : GA D A → GA D B → ℂ) : Prop where
  norm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e
  left : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ NFlag B e, γ ∈ GQ B → Q g (γ * n) = Q g n
  conj : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → Q (γ * g) (δ * n * δ⁻¹) = Q g n

variable {Q : GA D A → GA D B → ℂ}

theorem IsRatInv.integral_eq (hQ : IsRatInv ι e Q) (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : A.SigOK)
    {μ 𝓕 μ' 𝓕'} (hv : IsVolPair D A μ 𝓕) (hv' : IsVolPair D A μ' 𝓕') {ν 𝓝 ν' 𝓝'} (hN : IsUnitN B e ν 𝓝)
    (hN' : IsUnitN B e ν' 𝓝') :
    ∫ g in 𝓕, ∫ n in 𝓝, Q g n ∂ν ∂μ = ∫ g in 𝓕', ∫ n in 𝓝', Q g n ∂ν' ∂μ' := by
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨_, _, _, _⟩ := flag_topology B he
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  have hl : ∀ g, ∀ γ ∈ NFlagQ B e, ∀ n : NFlag B e, Q g (γ * n : NFlag B e) = Q g n :=
    fun g γ hγ n => hQ.left g n n.2 γ γ.2 hγ
  have e1 : ∀ g, ∫ n in 𝓝', Q g n ∂ν' = ∫ n in 𝓝, Q g n ∂ν := fun g =>
    GlobalTheory.Mem.TrueRecord.integral_unit _ hN'.1 hN'.2.1 hN'.2.2 hN.1 hN.2.1 hN.2.2 _ (hl g)
  simp only [e1]
  obtain rfl : μ = μ' := (GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D A hA).unique hv.1 hv'.1
  haveI := hv.1.1
  refine hv.2.setIntegral_eq hv'.2 fun γ g => ?_
  have r1 : EmbRel B A ι (s γ) γ := (hs _ _).2 rfl
  have r2 : EmbRel B A ι (s γ)⁻¹ (γ : GA D A)⁻¹ := (hs _ _).2 (map_inv s _).symm
  let c : NFlag B e ≃ₜ* NFlag B e :=
    { toFun := fun n => ⟨s γ * n * (s γ)⁻¹, hQ.norm _ _ r1 n n.2⟩
      invFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, hQ.norm _ _ r2 n n.2⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ B e ↔ n ∈ NFlagQ B e := fun n => by
    change s γ * (n : GA D B) * (s γ)⁻¹ ∈ GQ B ↔ (n : GA D B) ∈ GQ B
    rw [Subgroup.mul_mem_cancel_right _ (inv_mem (hq _ γ.2)), Subgroup.mul_mem_cancel_left _ (hq _ γ.2)]
  refine (GlobalTheory.Mem.TrueRecord.integral_aut _ hN.1 hN.2.1 hN.2.2 c hc _ (hl ((γ : GA D A) * g))).symm.trans ?_
  congr 1
  funext n
  exact hQ.conj g n n.2 γ γ.2 _ r1

theorem IsRatInv.integrable (hQ : IsRatInv ι e Q) (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hc : Continuous fun q : GA D A × NFlag B e => Q q.1 q.2) {μ 𝓕} (hv : IsVolPair D A μ 𝓕) {ν 𝓝} (hN : IsUnitN B e ν 𝓝) :
    (∀ g, IntegrableOn (fun n : NFlag B e => Q g n) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, Q g n ∂ν) 𝓕 μ := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  haveI := hv.1.1
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ A) hK hcov μ hv.2
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hc.continuousOn
  refine FJConv.iterated_integrableOn hfin.ne (by rw [hN.2.2]; exact ENNReal.one_ne_top) hc (M := M) fun g n => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hQ.norm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine le_trans (le_of_eq ?_) (hM (k, k') ⟨hk, hk'⟩)
  rw [e1, hQ.conj k _ (mul_mem γ'.2 k'.2) γ hγ _ ((hs _ _).2 rfl), hQ.left k _ k'.2 _ γ'.2 hγ']

end Invariant

section Integrands

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {s : GA D A → GA D B} {φ : GA D A → ℂ} {F : GA D B → ℂ}

theorem conj_arg (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) (hF : IsAutFun B F) {γ δ}
    (hγ : γ ∈ GQ A) (hδ : EmbRel B A ι δ γ) (g n y) : F (δ * n * δ⁻¹ * s (γ * g) * y) = F (n * s g * y) := by
  obtain ⟨s₀, -, hrel, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  rw [(hrel _ _).1 hδ, ← hF.left _ (hq γ hγ) (n * s₀ g * y)]
  simp only [map_mul, mul_assoc, inv_mul_cancel_left]

theorem emb_continuous (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) : Continuous s := by
  obtain ⟨s₀, hc, hrel, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  exact hc

theorem emb_unique (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) {s' : GA D A → GA D B}
    (hs' : ∀ h, EmbRel B A ι (s' h) h) : s = s' := by
  obtain ⟨s₀, -, hrel, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  exact funext fun h => ((hrel h _).1 (hs h)).trans ((hrel h _).1 (hs' h)).symm

theorem bes_inv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hι : HSpace.IsIsomEmb A B ι) (d : BesDat A B ι)
    (hs : ∀ h, EmbRel B A ι (s h) h) (hφ : IsAutFun A φ) (hF : IsAutFun B F) :
    IsRatInv ι d.e fun h n => star (φ h) * F (n * s h * (d.y : GA D B)) * star (besChar ψ d n) where
  norm δ γ h n hn := (BesselChar.besChar_conj ψ d δ γ h n hn).1
  left g n hn γ hγ hq := by
    rw [BesselChar.besChar_mul ψ d γ n hγ hn, BesselChar.besChar_rat ψ hψ.1 d γ hγ hq, one_mul, mul_assoc γ, mul_assoc γ,
      hF.left γ hq]
  conj g n hn γ hγ δ hδ := by
    rw [(BesselChar.besChar_conj ψ d δ γ hδ n hn).2, conj_arg hι hs hF hγ hδ, hφ.left γ hγ]

theorem besConv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (d : BesDat A B ι) {μ 𝓕} (hv : IsVolPair D A μ 𝓕) {ν 𝓝} (hN : IsUnitN B d.e ν 𝓝)
    (hs : ∀ h, EmbRel B A ι (s h) h) (hφ : IsAutFun A φ) (hF : IsAutFun B F) : BesConv ψ d μ 𝓕 ν 𝓝 s φ F := by
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  refine (bes_inv hψ hι d hs hφ hF).integrable d.e_iso hι hA ?_ hv hN
  exact ((hφ.cont.comp continuous_fst).star.mul (hF.cont.comp (((continuous_subtype_val.comp continuous_snd).mul
    ((emb_continuous hι hs).comp continuous_fst)).mul continuous_const))).mul
    ((BesselChar.besChar_continuous ψ hψ.1 d).comp continuous_snd).star

theorem fj_inv {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {L : HSp D} (d : FJDat L A B ι) (hr : 1 < A.rank)
    (Φ : X.Sch L A) (hs : ∀ h, EmbRel B A ι (s h) h) (hφ : IsAutFun A φ) (hF : IsAutFun B F) :
    IsRatInv ι d.eM fun g n =>
      star (φ g) * F (n * s g) * d.theta Wl.ψ (omZ Wl L A Φ) n g * star (d.chr Wl.ψ n) where
  norm δ γ h n hn := HeisCoord.conj_mem d h hn
  left g n hn γ hγ hq := by
    rw [HeisLaw.chr_mul d hγ hn, HeisCoord.chr_rat d Wl.ψ_std.1 hq, one_mul, mul_assoc γ, hF.left γ hq,
      (GlobalTheory.T.theta_kernel_invariance D X T Wl L A B ι d hr Φ g n hn).1 γ hγ hq]
  conj g n hn γ hγ δ hδ := by
    have h := conj_arg d.isom hs hF hγ hδ g n 1
    rw [mul_one, mul_one] at h
    rw [h, hφ.left γ hγ, (GlobalTheory.T.theta_kernel_invariance D X T Wl L A B ι d hr Φ g n hn).2 γ hγ δ hδ,
      ((HeisCoord.coords_laws D L A B ι d).2.2.2 δ γ hδ n hn).2.2.2]

end Integrands

section Periods

variable {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

structure IsGood (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Prop where
  sigOK : A.SigOK
  aniso : IsAniso A
  rank : 1 < A.rank
  isom : HSpace.IsIsomEmb A B ι

theorem isGood_step (T : ThetaTied D X) (t : ℕ) {j : ℕ} (hj : j < D.R.m) : IsGood (X.Xs t j) (X.Ys t j) (X.iXYs t j) :=
  ⟨(X.Xs_sig t j hj.le).1, isAniso_Xs T t hj.le, one_lt_rank_Xs X t hj.le, X.iXYs_isom t j hj⟩

theorem isGood_member (T : ThetaTied D X) : IsGood (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) := by
  have h0 := Nat.zero_le D.R.m
  refine ⟨?_, ?_, ?_, D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)⟩ <;> rw [← X.Xs_rec 0 h0]
  exacts [(X.Xs_sig _ 0 h0).1, isAniso_Xs T _ h0, one_lt_rank_Xs X _ h0]

structure Frame (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) where
  μ : Measure (GA D A)
  𝓕 : Set (GA D A)
  ν : Measure (NFlag B e)
  𝓝 : Set (NFlag B e)
  s : GA D A → GA D B
  vol : IsVolPair D A μ 𝓕
  unit : IsUnitN B e ν 𝓝
  emb : ∀ h, EmbRel B A ι (s h) h

theorem frame_nonempty (hg : IsGood A B ι) {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) :
    Nonempty (Frame A B ι e) := by
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D A hg.sigOK
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A μ hμ.1
  obtain ⟨ν, 𝓝, hN⟩ := UnitN.exists_isUnitN D B ρ e he
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hg.isom
  exact ⟨⟨μ, 𝓕, ν, 𝓝, s, ⟨hμ, h𝓕⟩, hN, fun h => (hs h _).2 rfl⟩⟩

open Classical in

def atFrame {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (f : Frame A B ι e → ℂ) : ℂ :=
  if h : Nonempty (Frame A B ι e) then f h.some else 0

section

variable {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} {f f' f'' : Frame A B ι e → ℂ}

theorem atFrame_add (h : ∀ c, f'' c = f c + f' c) : atFrame f'' = atFrame f + atFrame f' := by
  unfold atFrame; split_ifs
  exacts [h _, (add_zero _).symm]

theorem atFrame_mul (a : ℂ) (h : ∀ c, f' c = a * f c) : atFrame f' = a * atFrame f := by
  unfold atFrame; split_ifs
  exacts [h _, (mul_zero _).symm]

theorem atFrame_eq (c : Frame A B ι e) (h : ∀ c', f c' = f c) : atFrame f = f c := by
  unfold atFrame; rw [dif_pos ⟨c⟩, h]

end

def besVal (d : BesDat A B ι) (φ : X.AF A) (F : X.AF B) : ℂ :=
  atFrame fun c : Frame A B ι d.e => besPer Wl.ψ d c.μ c.𝓕 c.ν c.𝓝 c.s (T.ev A φ) (T.ev B F)

def fjVal {L : HSp D} (d : FJDat L A B ι) (Φ : X.Sch L A) (φ : X.AF A) (F : X.AF B) : ℂ :=
  atFrame fun c : Frame A B ι d.eM => d.per Wl.ψ (omZ Wl L A Φ) c.μ c.𝓕 c.ν c.𝓝 c.s (T.ev A φ) (T.ev B F)

variable (hg : IsGood A B ι)

include hg

theorem besVal_eq (d : BesDat A B ι) (c : Frame A B ι d.e) (φ F) :
    besVal Wl d φ F = besPer Wl.ψ d c.μ c.𝓕 c.ν c.𝓝 c.s (T.ev A φ) (T.ev B F) := by
  refine atFrame_eq c fun c' => ?_
  rw [emb_unique hg.isom c'.emb c.emb]
  exact (bes_inv Wl.ψ_std hg.isom d c.emb (T.ev_aut A φ) (T.ev_aut B F)).integral_eq d.e_iso hg.isom hg.sigOK
    c'.vol c.vol c'.unit c.unit

theorem fjVal_eq {L : HSp D} (d : FJDat L A B ι) (c : Frame A B ι d.eM) (Φ φ F) :
    fjVal Wl d Φ φ F = d.per Wl.ψ (omZ Wl L A Φ) c.μ c.𝓕 c.ν c.𝓝 c.s (T.ev A φ) (T.ev B F) := by
  refine atFrame_eq c fun c' => ?_
  rw [emb_unique hg.isom c'.emb c.emb]
  exact (fj_inv Wl d hg.rank Φ c.emb (T.ev_aut A φ) (T.ev_aut B F)).integral_eq d.isIsoSub hg.isom hg.sigOK
    c'.vol c.vol c'.unit c.unit

theorem bes_conv (d : BesDat A B ι) (c : Frame A B ι d.e) (φ F) :
    BesConv Wl.ψ d c.μ c.𝓕 c.ν c.𝓝 c.s (T.ev A φ) (T.ev B F) :=
  besConv Wl.ψ_std hg.isom hg.aniso d c.vol c.unit c.emb (T.ev_aut A φ) (T.ev_aut B F)

theorem fj_conv {L : HSp D} (d : FJDat L A B ι) (c : Frame A B ι d.eM) (Φ φ F) :
    d.Conv Wl.ψ (omZ Wl L A Φ) c.μ c.𝓕 c.ν c.𝓝 c.s (T.ev A φ) (T.ev B F) :=
  GlobalTheory.T.theta_convolution_anisotropic D X T Wl L A B ι d hg.rank hg.aniso _ _ c.vol.1.1 c.vol.2 _ _ c.unit _ c.emb Φ _ _
    (T.ev_aut A φ) (T.ev_aut B F)

theorem besVal_add_left (d : BesDat A B ι) (φ φ' F) :
    besVal Wl d (φ + φ') F = besVal Wl d φ F + besVal Wl d φ' F :=
  atFrame_add fun c => iterated_add (bes_conv Wl hg d c φ F) (bes_conv Wl hg d c φ' F) fun g n => by
    simp only [besFun, map_add, Pi.add_apply, star_add]; ring

theorem besVal_add_right (d : BesDat A B ι) (φ F F') :
    besVal Wl d φ (F + F') = besVal Wl d φ F + besVal Wl d φ F' :=
  atFrame_add fun c => iterated_add (bes_conv Wl hg d c φ F) (bes_conv Wl hg d c φ F') fun g n => by
    simp only [besFun, map_add, Pi.add_apply]; ring

theorem fjVal_add_left {L : HSp D} (d : FJDat L A B ι) (Φ φ φ' F) :
    fjVal Wl d Φ (φ + φ') F = fjVal Wl d Φ φ F + fjVal Wl d Φ φ' F :=
  atFrame_add fun c => iterated_add (fj_conv Wl hg d c Φ φ F) (fj_conv Wl hg d c Φ φ' F) fun g n => by
    simp only [FJDat.perFun, map_add, Pi.add_apply, star_add]; ring

theorem fjVal_add_right {L : HSp D} (d : FJDat L A B ι) (Φ φ F F') :
    fjVal Wl d Φ φ (F + F') = fjVal Wl d Φ φ F + fjVal Wl d Φ φ F' :=
  atFrame_add fun c => iterated_add (fj_conv Wl hg d c Φ φ F) (fj_conv Wl hg d c Φ φ F') fun g n => by
    simp only [FJDat.perFun, map_add, Pi.add_apply]; ring

omit hg

theorem besVal_smul (d : BesDat A B ι) (a b : ℂ) (φ F) :
    besVal Wl d (a • φ) (b • F) = star a * b * besVal Wl d φ F :=
  atFrame_mul _ fun c => iterated_mul _ fun g n => by
    simp only [besFun, map_smul, Pi.smul_apply, smul_eq_mul, star_mul']; ring

theorem fjVal_smul {L : HSp D} (d : FJDat L A B ι) (a b : ℂ) (Φ φ F) :
    fjVal Wl d Φ (a • φ) (b • F) = star a * b * fjVal Wl d Φ φ F :=
  atFrame_mul _ fun c => iterated_mul _ fun g n => by
    simp only [FJDat.perFun, map_smul, Pi.smul_apply, smul_eq_mul, star_mul']; ring

end Periods

section Record

variable {X : ThetaX D} {T : ThetaTied D X}

abbrev Dat (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type :=
  {d : BesDat A B ι // (d.y : GA D B) = 1} ⊕ FJDat (negLine D) A B ι

def Pos (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type := {_d : Dat A B ι // IsGood A B ι}

def period (Wl : WeilTied D X T) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (p : Pos A B ι) (Φ : X.Sch (negLine D) A)
    (φ : X.AF A) (F : X.cusp B) : ℂ :=
  (T.petC A : ℂ) * p.1.elim (fun d => besVal Wl d.1 φ F) fun d => fjVal Wl d Φ φ F

theorem period_smul (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (p : Pos A B ι) (Φ) (a b : ℂ) (φ F) :
    period Wl A B ι p Φ (a • φ) (b • F) = star a * b * period Wl A B ι p Φ φ F := by
  obtain ⟨d | d, hg⟩ := p <;>
    simp only [period, Sum.elim_inl, Sum.elim_inr, Submodule.coe_smul, besVal_smul, fjVal_smul] <;> ring

def memberPos (T : ThetaTied D X) (u : D.what₂.Word) : Pos (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) :=
  ⟨.inl ⟨BesselCompare.toBes (IndefiniteRowSideFullHecke.BesselData.memberDatum D u), rfl⟩, isGood_member T⟩

def record (Wl : WeilTied D X T) : ThetaX D :=
  { X with
    fact := factSet Wl
    Pos := Pos
    FJd := fun A _ _ => X.Sch (negLine D) A
    fjAdd := fun _ _ _ => inferInstance
    fjMod := fun _ _ _ => inferInstance
    Bper := period Wl
    Bper_right := fun A B ι p Φ φ => by
      refine ⟨fun F F' => ?_, fun b F => ?_⟩
      · obtain ⟨d | d, hg⟩ := p <;> simp only [period, Sum.elim_inl, Sum.elim_inr, Submodule.coe_add,
          besVal_add_right Wl hg, fjVal_add_right Wl hg, mul_add]
      · have := period_smul Wl p Φ 1 b φ F
        rwa [one_smul, star_one, one_mul] at this
    Bper_add_left := fun A B ι p Φ φ φ' F => by
      obtain ⟨d | d, hg⟩ := p <;> simp only [period, Sum.elim_inl, Sum.elim_inr,
        besVal_add_left Wl hg, fjVal_add_left Wl hg, mul_add]
    Bper_smul_left := fun A B ι p Φ a φ F => by
      have := period_smul Wl p Φ a 1 φ F
      rwa [one_smul, mul_one] at this
    Bper_odd := fun A B ι p ho Φ Φ' φ F => by
      obtain ⟨d | d, hg⟩ := p
      · rfl
      · exact absurd d.even_codim (Nat.not_even_iff_odd.2 ho)
    pos1 := memberPos T
    posSym := memberPos T }

def recordT (Wl : WeilTied D X T) : ThetaTied D (record Wl) := { T with }

def recordW (Wl : WeilTied D X T) : WeilTied D (record Wl) (recordT Wl) :=
  { Wl with om_tw := ⟨Wl.om_tw.1, Wl.om_tw.2, Wl.om_tw.3, Wl.om_tw.4⟩ }

variable (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem isBesPos_record (hg : IsGood A B ι) (d : BesDat A B ι) (hy : (d.y : GA D B) = 1) :
    IsBesPos (recordW Wl) d (⟨.inl ⟨d, hy⟩, hg⟩ : Pos A B ι) :=
  fun μ 𝓕 hv ν 𝓝 hN s hs _ φ F _ =>
    congrArg ((T.petC A : ℂ) * ·) (besVal_eq Wl hg d ⟨μ, 𝓕, ν, 𝓝, s, hv, hN, hs⟩ φ F.1)

theorem isFJPos_record (hg : IsGood A B ι) (d : FJDat (negLine D) A B ι) :
    IsFJPos (recordW Wl) (L := negLine D) (LinearEquiv.refl ℂ (X.Sch (negLine D) A)) d (⟨.inr d, hg⟩ : Pos A B ι) :=
  fun μ 𝓕 hv ν 𝓝 hN s hs Φ φ F _ =>
    congrArg ((T.petC A : ℂ) * ·) (fjVal_eq Wl hg d ⟨μ, 𝓕, ν, 𝓝, s, hv, hN, hs⟩ Φ φ F.1)

theorem rank_step (X : ThetaX D) (t : ℕ) {j : ℕ} (hj : j < D.R.m) :
    (X.Ys t j).rank + j + 1 = (X.Xs t j).rank + D.R.m := by
  rw [X.Ys_rank t j hj.le, X.Xs_rank t j hj.le, mul_add, mul_one, Ranks.r]
  omega

def perTied : PerTied (recordW Wl) where
  line := negLine D
  line_neg := isNegLine_negLine D
  eFJ t j _ _ := LinearEquiv.refl ℂ (X.Sch (negLine D) (X.Xs t j))
  bes t _ hj _ d hy := ⟨_, isBesPos_record Wl (isGood_step T t hj) d hy⟩
  fj t _ hj _ d := ⟨_, isFJPos_record Wl (isGood_step T t hj) d⟩
  bes_all t j hj he p := by
    obtain ⟨d | d, hg⟩ := p
    · exact ⟨d.1, d.2, _, isBesPos_record Wl hg d.1 d.2, isTranslSum_refl _⟩
    · have h1 : (X.Xs t j).rank + 2 * d.ρ = (X.Ys t j).rank := d.codim
      have h2 := rank_step X t hj
      have h3 := Nat.even_iff.1 D.R.m_even
      have h4 := Nat.even_iff.1 he
      omega
  fj_only t j hj ho p := by
    obtain ⟨d | d, hg⟩ := p
    · have h1 : (X.Xs t j).rank + 2 * d.1.ρ + 1 = (X.Ys t j).rank := d.1.codim
      have h2 := rank_step X t hj
      have h3 := Nat.even_iff.1 D.R.m_even
      have h4 := Nat.odd_iff.1 ho
      omega
    · exact ⟨d, isFJPos_record Wl hg d⟩
  fact _ _ _ := rfl

def besOf (ho : Odd (B.rank - A.rank)) (p : Pos A B ι) : {d : BesDat A B ι // (d.y : GA D B) = 1} :=
  p.1.elim id fun d => absurd d.even_codim (Nat.not_even_iff_odd.2 ho)

def recordB : BesselTied D (record Wl) (recordT Wl) (recordW Wl) where
  dat _ _ _ ho p := (besOf ho p).1
  dat_y _ _ _ ho p := (besOf ho p).2
  besC _ _ _ _ := 1
  besC_pos _ _ _ _ := one_pos
  besC_one _ _ _ _ := rfl
  bper A B ι ho _ _ _ p _ σ μ 𝓕 hv ν 𝓝 h1 h2 h3 s hs φ F hφ := by
    obtain ⟨d | d, hg⟩ := p
    · rw [one_mul]
      exact isBesPos_record Wl hg d.1 d.2 μ 𝓕 hv ν 𝓝 ⟨h1, h2, h3⟩ s hs σ φ F hφ
    · exact absurd d.even_codim (Nat.not_even_iff_odd.2 ho)

end Record

def SameOffPeriods (X X' : ThetaX D) : Prop :=
  ∃ fact Pos FJd fjAdd fjMod Bper h₁ h₂ h₃ h₄ pos1 posSym,
    X' = { X with
      fact := fact, Pos := Pos, FJd := FJd, fjAdd := fjAdd, fjMod := fjMod, Bper := Bper, Bper_right := h₁,
      Bper_add_left := h₂, Bper_smul_left := h₃, Bper_odd := h₄, pos1 := pos1, posSym := posSym }

def SameTies {X X' : ThetaX D} {T : ThetaTied D X} {T' : ThetaTied D X'} (Wl : WeilTied D X T)
    (Wl' : WeilTied D X' T') : Prop :=
  HEq T'.ev T.ev ∧ HEq T'.eGf T.eGf ∧ T'.petF = T.petF ∧ T'.petR = T.petR ∧ HEq T'.eChr T.eChr ∧
    Wl'.ψ = Wl.ψ ∧ HEq Wl'.evS Wl.evS ∧ HEq Wl'.om Wl.om

theorem sameOffPeriods_record {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) :
    SameOffPeriods X (record Wl) :=
  ⟨_, _, _, _, _, _, (record Wl).Bper_right, (record Wl).Bper_add_left, (record Wl).Bper_smul_left,
    (record Wl).Bper_odd, _, _, rfl⟩

theorem sameTies_record {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) : SameTies Wl (recordW Wl) :=
  ⟨.rfl, .rfl, rfl, rfl, .rfl, rfl, .rfl, .rfl⟩

theorem exists_allTied_perTied (D : D7) (X : ThetaX D) (P : TH.ProvA) (a : AllTied D X P) :
    ∃ (X' : ThetaX D) (a' : AllTied D X' P), Nonempty (PerTied a'.W) ∧ SameOffPeriods X X' ∧ SameTies a.W a'.W ∧
      HEq a'.kf.cpt a.kf.cpt ∧ HEq a'.kf.bas a.kf.bas ∧
      ∀ u, IsBesPos a'.W (BesselCompare.toBes (IndefiniteRowSideFullHecke.BesselData.memberDatum D u)) (X'.posSym u) :=
  ⟨record a.W, ⟨recordT a.W, a.sm, a.ty, recordW a.W, a.unr, { a.kf with }, a.phiUp, recordB a.W, a.real, a.prov⟩,
    ⟨perTied a.W⟩, sameOffPeriods_record _, sameTies_record _, .rfl, .rfl,
    fun _ => isBesPos_record a.W (isGood_member a.T) _ rfl⟩

theorem exists_perTied (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) :
    ∃ (X' : ThetaX D) (T' : ThetaTied D X') (Wl' : WeilTied D X' T'), Nonempty (PerTied Wl') ∧ SameOffPeriods X X' ∧
      SameTies Wl Wl' ∧ ∀ u, IsBesPos Wl' (BesselCompare.toBes (IndefiniteRowSideFullHecke.BesselData.memberDatum D u)) (X'.posSym u) :=
  ⟨record Wl, recordT Wl, recordW Wl, ⟨perTied Wl⟩, sameOffPeriods_record Wl, sameTies_record Wl,
    fun _ => isBesPos_record Wl (isGood_member T) _ rfl⟩

end GlobalTheory.Per.Inhab

end
