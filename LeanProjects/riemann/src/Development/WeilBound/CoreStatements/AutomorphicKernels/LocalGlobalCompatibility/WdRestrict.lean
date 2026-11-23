import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.Pst

open scoped Pointwise Topology

namespace PositivityTheory.Pf1.CLGD.WdRestrict

section Groups

variable {E E' Ω : Type} [Field E] [Field E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω]

variable (E) in

def resG : G E' Ω →* G E Ω := AlgEquiv.restrictScalarsHom E

@[simp] theorem resG_apply (σ : G E' Ω) (x : Ω) : resG E σ x = σ x := rfl

variable [NumberField E] [NumberField E'] {A : ValuationSubring Ω}

theorem resG_mem_Dec {σ : G E' Ω} (hσ : σ ∈ Dec (F := E') A) : resG E σ ∈ Dec (F := E) A := by
  have h1 : σ • A = A := hσ
  show resG E σ • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  rfl

variable (E A) in

def resDec : ↥(Dec (F := E') A) →* ↥(Dec (F := E) A) where
  toFun σ := ⟨resG E (σ : G E' Ω), resG_mem_Dec σ.2⟩
  map_one' := Subtype.ext (map_one (resG E))
  map_mul' σ τ := Subtype.ext (map_mul (resG E) (σ : G E' Ω) τ)

@[simp] theorem coe_resDec (σ : ↥(Dec (F := E') A)) : ((resDec E A σ : ↥(Dec (F := E) A)) : G E Ω) = resG E (σ : G E' Ω) :=
  rfl

variable {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}

theorem exists_normV_pow (h : IsPlaceOver A w) (h' : IsPlaceOver A w') : ∃ f : ℕ, normV w' = normV w ^ f := by
  classical
  have hcomap : w.asIdeal = w'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) := by
    ext x
    rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 E) (𝓞 E') x)]
    have e : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') x : 𝓞 E') : E') = algebraMap E Ω (x : E) := by
      rw [IsScalarTower.algebraMap_apply E E' Ω]
      rfl
    rw [e]
  have := w.isMaximal
  have := w'.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  letI := Ideal.Quotient.field w'.asIdeal
  have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  have : Finite (𝓞 E' ⧸ w'.asIdeal) := w'.asIdeal.finiteQuotientOfFreeOfNeBot w'.ne_bot
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  letI := Fintype.ofFinite (𝓞 E' ⧸ w'.asIdeal)
  letI : Algebra (𝓞 E ⧸ w.asIdeal) (𝓞 E' ⧸ w'.asIdeal) :=
    (Ideal.quotientMap w'.asIdeal (algebraMap (𝓞 E) (𝓞 E')) hcomap.le).toAlgebra
  refine ⟨Module.finrank (𝓞 E ⧸ w.asIdeal) (𝓞 E' ⧸ w'.asIdeal), ?_⟩
  rw [normV, normV, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

def resF (h : IsPlaceOver A w) (h' : IsPlaceOver A w') : ℕ := (exists_normV_pow h h').choose

theorem normV_eq_pow_resF (h : IsPlaceOver A w) (h' : IsPlaceOver A w') : normV w' = normV w ^ resF h h' :=
  (exists_normV_pow h h').choose_spec

theorem actsAs_resG {f : ℕ} (hf : normV w' = normV w ^ f) {σ : G E' Ω} {a b : ℕ}
    (hσ : ActsAs A (normV w') σ a b) : ActsAs A (normV w) (resG E σ) (f * a) (f * b) := by
  refine ⟨resG_mem_Dec hσ.1, fun x hx => ?_⟩
  have h1 := hσ.2 x hx
  rw [hf, ← pow_mul, ← pow_mul] at h1
  exact h1

variable (h : IsPlaceOver A w) (h' : IsPlaceOver A w')

theorem resG_mem_Weil (σ : ↥(Weil h')) : resG E (σ : G E' Ω) ∈ Weil h := by
  obtain ⟨a, b, hσ⟩ := σ.2
  exact ⟨_, _, actsAs_resG (normV_eq_pow_resF h h') hσ⟩

def resW : ↥(Weil h') →* ↥(Weil h) where
  toFun σ := ⟨resG E (σ : G E' Ω), resG_mem_Weil h h' σ⟩
  map_one' := Subtype.ext (map_one (resG E))
  map_mul' σ τ := Subtype.ext (map_mul (resG E) (σ : G E' Ω) τ)

@[simp] theorem coe_resW (σ : ↥(Weil h')) : ((resW h h' σ : ↥(Weil h)) : G E Ω) = resG E (σ : G E' Ω) := rfl

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω]

theorem deg_resW (σ : ↥(Weil h')) : deg (resW h h' σ) = (resF h h' : ℤ) * deg σ := by
  obtain ⟨a, b, hσ⟩ := σ.2
  rw [deg_eq (σ := resW h h' σ) (actsAs_resG (normV_eq_pow_resF h h') hσ), deg_eq hσ]
  push_cast; ring

theorem resG_mem_Ine {σ : G E' Ω} (hσ : σ ∈ Ine (F := E') A) : resG E σ ∈ Ine (F := E) A :=
  ⟨resG_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

omit [NumberField E] [NumberField E'] [IsAlgClosure E Ω] in

theorem continuous_resG : Continuous (resG E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (resG E) ?_
  intro s hs
  rw [map_one] at hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).mp hs
  let b := Module.finBasis E L
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  refine ⟨IntermediateField.adjoin E' (Set.range fun i => (b i : Ω)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun σ hσ => hLs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  have hb : ∀ i, σ (b i : Ω) = b i := fun i => hσ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  have hx' := congrArg (fun y : L => (y : Ω)) (b.sum_repr ⟨x, hx⟩)
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at hx'
  rw [← hx']
  show (resG E σ) _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, resG_apply, hb]

theorem IsSmooth.resW {M : Type*} [Monoid M] {φ : ↥(Weil h) →* M} (hφ : IsSmooth φ) :
    IsSmooth (φ.comp (resW h h')) := by
  have hc : Continuous fun σ : ↥(Ine (F := E') A) =>
      (⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩ : ↥(Ine (F := E) A)) :=
    (continuous_resG.comp continuous_subtype_val).subtype_mk _
  exact hφ.preimage hc

end Groups

section FSS

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {W W' : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

def IsFSS (ρ : Representation ℂ ↥(Weil h) W) (N : End ℂ W) (a : WDRep h W) : Prop :=
  ∃ u : (End ℂ W)ˣ, a.N = N ∧ IsNilpotent ((u : End ℂ W) - 1) ∧ Commute (u : End ℂ W) N ∧
    (∀ σ, Commute (u : End ℂ W) (ρ σ)) ∧ ∀ σ, ρ σ = a.ρ σ * ((u ^ deg σ : (End ℂ W)ˣ) : End ℂ W)

variable (h) in

theorem exists_deg_eq_one : ∃ φ : ↥(Weil h), deg φ = 1 := by
  obtain ⟨σ, hσ⟩ := exists_isFrob h
  refine ⟨⟨σ, mem_Weil_of_isFrob h hσ⟩, ?_⟩
  rw [deg_eq (actsAs_one_iff.mpr hσ)]
  norm_num

theorem IsFSS.ρ_eq {ρ : Representation ℂ ↥(Weil h) W} {N : End ℂ W} {a b : WDRep h W}
    (ha : IsFSS ρ N a) (hb : IsFSS ρ N b) : a.ρ = b.ρ := by
  obtain ⟨u, -, hu, -, huρ, ha⟩ := ha
  obtain ⟨v, -, hv, -, hvρ, hb⟩ := hb
  obtain ⟨φ, hφ⟩ := exists_deg_eq_one h
  have ea := ha φ
  have eb := hb φ
  rw [hφ, zpow_one] at ea eb
  have hsa : Commute (a.ρ φ) (u : End ℂ W) := by
    have e2 : a.ρ φ = ρ φ * ((u⁻¹ : (End ℂ W)ˣ) : End ℂ W) := by rw [ea, mul_assoc, Units.mul_inv, mul_one]
    rw [e2]
    exact (huρ φ).symm.mul_left (Commute.refl (u : End ℂ W)).units_inv_left
  have hsb : Commute (b.ρ φ) (v : End ℂ W) := by
    have e2 : b.ρ φ = ρ φ * ((v⁻¹ : (End ℂ W)ˣ) : End ℂ W) := by rw [eb, mul_assoc, Units.mul_inv, mul_one]
    rw [e2]
    exact (hvρ φ).symm.mul_left (Commute.refl (v : End ℂ W)).units_inv_left
  have hca : Commute (a.ρ φ) ((u : End ℂ W) - 1) := hsa.sub_right (Commute.one_right _)
  have hcb : Commute (b.ρ φ) ((v : End ℂ W) - 1) := hsb.sub_right (Commute.one_right _)
  have hsum : a.ρ φ * ((u : End ℂ W) - 1) + a.ρ φ = b.ρ φ * ((v : End ℂ W) - 1) + b.ρ φ := by
    rw [mul_sub, mul_one, sub_add_cancel, mul_sub, mul_one, sub_add_cancel, ← ea, ← eb]
  have hs := (Module.End.isNilpotent_isSemisimple_unique (hca.isNilpotent_mul_left hu) (a.semisimple φ)
    (hcb.isNilpotent_mul_left hv) (b.semisimple φ) ((Commute.refl _).mul_left hca.symm)
    ((Commute.refl _).mul_left hcb.symm) hsum).2
  have hinv : a.ρ φ⁻¹ * a.ρ φ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have huv : (u : End ℂ W) = v := by
    calc (u : End ℂ W) = a.ρ φ⁻¹ * (a.ρ φ * u) := by rw [← mul_assoc, hinv, one_mul]
      _ = a.ρ φ⁻¹ * (b.ρ φ * v) := by rw [← ea, eb]
      _ = v := by rw [← hs, ← mul_assoc, hinv, one_mul]
  have huv' : u = v := Units.ext huv
  refine MonoidHom.ext fun σ => ?_
  have e1 := (ha σ).symm.trans (hb σ)
  rw [huv'] at e1
  exact (Units.mul_left_inj _).mp e1

theorem IsFSS.iso {ρ : Representation ℂ ↥(Weil h) W} {N : End ℂ W} {a b : WDRep h W}
    (ha : IsFSS ρ N a) (hb : IsFSS ρ N b) : a.Iso b := by
  have hρ := ha.ρ_eq hb
  obtain ⟨_, hNa, -⟩ := ha
  obtain ⟨_, hNb, -⟩ := hb
  exact ⟨LinearEquiv.refl ℂ W, fun σ v => by rw [hρ]; rfl, fun v => by rw [hNa, hNb]; rfl⟩

theorem IsFSS.transport {ρ : Representation ℂ ↥(Weil h) W} {N : End ℂ W} {a : WDRep h W} (ha : IsFSS ρ N a)
    (e : W ≃ₗ[ℂ] W') {ρ' : Representation ℂ ↥(Weil h) W'} {N' : End ℂ W'}
    (hρ : ∀ σ, ρ' σ = e.conjAlgEquiv ℂ (ρ σ)) (hN : N' = e.conjAlgEquiv ℂ N) : IsFSS ρ' N' (a.transport e) := by
  obtain ⟨u, hN0, hu, huN, huρ, hρa⟩ := ha
  let c : End ℂ W ≃ₐ[ℂ] End ℂ W' := e.conjAlgEquiv ℂ
  refine ⟨Units.map (c : End ℂ W →* End ℂ W') u, ?_, ?_, ?_, ?_, ?_⟩
  · show c a.N = N'
    rw [hN0, hN]
  · have := hu.map c
    rwa [map_sub, map_one] at this
  · rw [hN]
    exact huN.map c
  · intro σ
    rw [hρ]
    exact (huρ σ).map c
  · intro σ
    rw [hρ, hρa σ, map_mul, ← map_zpow]
    rfl

end FSS

section WDRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def resRep (a : WDRep h V) : WDRep h' V where
  ρ := a.ρ.comp (resW h h')
  N := a.N
  smooth := IsSmooth.resW h h' a.smooth
  semisimple σ := a.semisimple _
  nilpotent := a.nilpotent
  comm σ := by
    have e : ((normV w' : ℕ) : ℂ) ^ deg σ = ((normV w : ℕ) : ℂ) ^ deg (resW h h' σ) := by
      rw [deg_resW, normV_eq_pow_resF h h', Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    rw [e]
    exact a.comm _

@[simp] theorem resRep_ρ (a : WDRep h V) (σ : ↥(Weil h')) : (resRep h h' a).ρ σ = a.ρ (resW h h' σ) := rfl

@[simp] theorem resRep_N (a : WDRep h V) : (resRep h h' a).N = a.N := rfl

theorem iso_resRep {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : (resRep h h' a).Iso (resRep h h' b) := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e, fun σ v => h1 _ v, h2⟩

def WD.res : WD h → WD h' :=
  Quotient.map (fun a => ⟨a.1, resRep h h' a.2⟩) (fun _ _ hab => iso_resRep h h' hab)

theorem WD.res_mk (a : WDRep h V) : WD.res h h' (WD.mk a) = WD.mk (resRep h h' a) := by
  show Quotient.mk _ (⟨_, resRep h h' (WD.std a).2⟩ : Σ n : ℕ, WDRep h' (Fin n → ℂ)) = _
  rw [WD.quotientMk_eq]
  exact WD.sound (iso_resRep h h' (WD.iso_std a).symm)

theorem IsFSS.res {ρ : Representation ℂ ↥(Weil h) V} {N : End ℂ V} {a : WDRep h V} (ha : IsFSS ρ N a) :
    IsFSS (ρ.comp (resW h h')) N (resRep h h' a) := by
  obtain ⟨u, hN0, hu, huN, huρ, hρa⟩ := ha
  refine ⟨u ^ resF h h', hN0, ?_, ?_, fun σ => ?_, fun σ => ?_⟩
  · rw [Units.val_pow_eq_pow_val, ← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    exact Commute.sum_left _ _ _ fun i _ =>
      ((Commute.refl (u : End ℂ V)).sub_right (Commute.one_right _)).pow_left i
  · rw [Units.val_pow_eq_pow_val]
    exact huN.pow_left _
  · rw [Units.val_pow_eq_pow_val]
    exact (huρ _).pow_left _
  · show ρ (resW h h' σ) = a.ρ (resW h h' σ) * _
    rw [hρa, deg_resW, ← zpow_natCast, ← zpow_mul]

end WDRes

section LetterMaps

variable {LL U D₁ D₂ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁] [AddCommGroup D₂] [Module LL D₂]
  (m₁ : U →+* End LL D₁) (m₂ : U →+* End LL D₂) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)

def letterHom (T : D₁ →ₗ[LL] D₂) (hT : ∀ c x, T (m₁ c x) = m₂ c (T x)) :
    Letter m₁ F τ →ₗ[F] Letter m₂ F τ :=
  Submodule.mapQ _ _ (T.baseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_iSup_of_mem c ⟨T.baseChange F y, ?_⟩
    have e : (m₂ c).comp T = T.comp (m₁ c) := LinearMap.ext fun x => (hT c x).symm
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) e) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this])

@[simp] theorem letterHom_mk (T : D₁ →ₗ[LL] D₂) (hT : ∀ c x, T (m₁ c x) = m₂ c (T x)) (x : D₁) :
    letterHom m₁ m₂ F τ T hT (letterMk m₁ F τ x) = letterMk m₂ F τ (T x) := rfl

def letterEquiv (T : D₁ ≃ₗ[LL] D₂) (hT : ∀ c x, T (m₁ c x) = m₂ c (T x)) :
    Letter m₁ F τ ≃ₗ[F] Letter m₂ F τ :=
  have hT' : ∀ c x, T.symm (m₂ c x) = m₁ c (T.symm x) := fun c x => by
    rw [LinearEquiv.symm_apply_eq, hT, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinear (letterHom m₁ m₂ F τ T hT) (letterHom m₂ m₁ F τ T.symm hT')
    (letter_hom_ext m₂ F τ fun x => by simp)
    (letter_hom_ext m₁ F τ fun x => by simp)

@[simp] theorem letterEquiv_mk (T : D₁ ≃ₗ[LL] D₂) (hT : ∀ c x, T (m₁ c x) = m₂ c (T x)) (x : D₁) :
    letterEquiv m₁ m₂ F τ T hT (letterMk m₁ F τ x) = letterMk m₂ F τ (T x) := rfl

@[simp] theorem letterEquiv_symm_mk (T : D₁ ≃ₗ[LL] D₂) (hT : ∀ c x, T (m₁ c x) = m₂ c (T x)) (x : D₂) :
    (letterEquiv m₁ m₂ F τ T hT).symm (letterMk m₂ F τ x) = letterMk m₁ F τ (T.symm x) := rfl

end LetterMaps

section Intertwine

theorem zpow_intertwine {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂]
    [Module R M₂] (T : M₁ →ₗ[R] M₂) (u : (End R M₁)ˣ) (u' : (End R M₂)ˣ)
    (hu : ∀ x, (u' : End R M₂) (T x) = T ((u : End R M₁) x)) (n : ℤ) (x : M₁) :
    ((u' ^ n : (End R M₂)ˣ) : End R M₂) (T x) = T (((u ^ n : (End R M₁)ˣ) : End R M₁) x) := by
  have hpow : ∀ (v : (End R M₁)ˣ) (v' : (End R M₂)ˣ), (∀ x, (v' : End R M₂) (T x) = T ((v : End R M₁) x)) →
      ∀ (k : ℕ) x, ((v' ^ k : (End R M₂)ˣ) : End R M₂) (T x) = T (((v ^ k : (End R M₁)ˣ) : End R M₁) x) := by
    intro v v' hv k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, hv, ih]
  have hinv : ∀ x, ((u'⁻¹ : (End R M₂)ˣ) : End R M₂) (T x) = T (((u⁻¹ : (End R M₁)ˣ) : End R M₁) x) := by
    intro x
    have e1 := hu (((u⁻¹ : (End R M₁)ˣ) : End R M₁) x)
    rw [← End.mul_apply (u : End R M₁), Units.mul_inv, End.one_apply] at e1
    rw [← e1, ← End.mul_apply, Units.inv_mul, End.one_apply]
  cases n with
  | ofNat k => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]; exact hpow u u' hu k x
  | negSucc k => rw [zpow_negSucc, zpow_negSucc, ← inv_pow, ← inv_pow]; exact hpow _ _ hinv (k + 1) x

end Intertwine

section Bridges

variable {l : ℕ} [Fact l.Prime] {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']

def IsResBridge (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E' Ω (Dec (F := E') A) O') : Prop :=
  ∀ g : ↥(Dec (F := E') A), ((Bw'.e g : ↥(GK Bw'.Kw)) : GQ l) = ((Bw.e (resDec E A g) : ↥(GK Bw.Kw)) : GQ l)

theorem IsResBridge.Kw_le {Bw : LocBridge l E Ω (Dec (F := E) A) O} {Bw' : LocBridge l E' Ω (Dec (F := E') A) O'}
    (hc : IsResBridge Bw Bw') : Bw.Kw.1 ≤ Bw'.Kw.1 := by
  intro x hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup Bw'.Kw.1]
  intro g'
  obtain ⟨d, hd⟩ := Bw'.e.surjective ⟨g'.1, g'.2⟩
  have e1 : (g'.1 : GQ l) = ((Bw.e (resDec E A d) : ↥(GK Bw.Kw)) : GQ l) := by
    rw [← hc d, hd]
  show (g'.1 : GQ l) x = x
  rw [e1]
  exact (Bw.e (resDec E A d)).2 ⟨x, hx⟩

end Bridges

section Enlarge

open GlobalTheory.Pst.EnlargeCoeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)

theorem wdRep_iso_of_equiv {L₁ L₂ : FinExt l}
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
    [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
    {ρ₁ : Representation ↥L₁.1 ↥(GK Bw.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK Bw.Kw) V₂}
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]
    (e : WDSpace P ι ρ₁ ≃ₗ[ℂ] WDSpace P ι ρ₂)
    (hΦρ : ∀ σ y, e (wdRho P ι Bw h hj ρ₁ σ y) = wdRho P ι Bw h hj ρ₂ σ (e y))
    (hΦN : ∀ y, e (wdN P ι ρ₁ y) = wdN P ι ρ₂ (e y)) :
    (wdRep P ι Bw h hj ρ₁).Iso (wdRep P ι Bw h hj ρ₂) := by
  have hρ : ∀ σ, wdRho P ι Bw h hj ρ₂ σ = e.conjAlgEquiv ℂ (wdRho P ι Bw h hj ρ₁ σ) := fun σ => by
    ext1 y
    rw [LinearEquiv.conjAlgEquiv_apply]
    show _ = e (wdRho P ι Bw h hj ρ₁ σ (e.symm y))
    conv_lhs => rw [← e.apply_symm_apply y]
    exact (hΦρ σ _).symm
  have hN : wdN P ι ρ₂ = e.conjAlgEquiv ℂ (wdN P ι ρ₁) := by
    ext1 y
    rw [LinearEquiv.conjAlgEquiv_apply]
    show _ = e (wdN P ι ρ₁ (e.symm y))
    conv_lhs => rw [← e.apply_symm_apply y]
    exact (hΦN _).symm
  have h1 : IsFSS (wdRho P ι Bw h hj ρ₂) (wdN P ι ρ₂) (wdRep P ι Bw h hj ρ₂) := wdRep_spec P ι Bw h hj ρ₂
  have h2 : IsFSS (wdRho P ι Bw h hj ρ₁) (wdN P ι ρ₁) (wdRep P ι Bw h hj ρ₁) := wdRep_spec P ι Bw h hj ρ₁
  exact ((h1.iso (h2.transport e hρ hN)).trans (WDRep.iso_transport _ _).symm).symm

theorem wdRep_iso_of_coord {L₁ L₂ : FinExt l}
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
    [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
    {ρ₁ : Representation ↥L₁.1 ↥(GK Bw.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK Bw.Kw) V₂}
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]
    (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = (a : Om l))
    {f : V₁ →ₗ[ℚ_[l]] V₂} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v)) (hfs : ∀ (a : ↥L₁.1) v, f (a • v) = s a • f v)
    {n : ℕ} (b : Fin n → ↥L₂.1) (π : Fin n → V₂ →ₗ[ℚ_[l]] V₁) (hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v))
    (hsum : ∀ v, ∑ j, b j • f (π j v) = v)
    (hdim : finrank ℂ (WDSpace P ι ρ₁) = finrank ℂ (WDSpace P ι ρ₂)) :
    (wdRep P ι Bw h hj ρ₁).Iso (wdRep P ι Bw h hj ρ₂) := by
  have hT : ∀ (a : ↥L₁.1) (x : ↥(Dpst P ρ₁)), dQ P hf (a • x) = s a • dQ P hf x := fun a x =>
    Subtype.ext (tensQ_smul P s hfs a x.1)
  letI := algC ι L₁
  letI := algC ι L₂
  obtain ⟨Φ, hΦmk, hΦρ, hΦN⟩ : ∃ Φ : WDSpace P ι ρ₁ →ₗ[ℂ] WDSpace P ι ρ₂,
      (∀ x, Φ (wdMk P ι ρ₁ x) = wdMk P ι ρ₂ (dQ P hf x)) ∧
      (∀ σ y, Φ (wdRho P ι Bw h hj ρ₁ σ y) = wdRho P ι Bw h hj ρ₂ σ (Φ y)) ∧
      (∀ y, Φ (wdN P ι ρ₁ y) = wdN P ι ρ₂ (Φ y)) :=
    ⟨chg (mulD P ρ₁) (mulD P ρ₂) ℂ (urC ι) s (fun a => congrArg ι (hs a)) (dQ P hf) hT (dQ_mulD P hf),
      fun x => chg_mk _ _ _ _ _ _ _ _ _ x,
      fun σ y => chg_letterMap _ _ _ _ _ _ _ _ _ _ (weilD_mulD Bw h P ρ₁ hj σ) _ (weilD_mulD Bw h P ρ₂ hj σ)
        (dQ_weilD P Bw h hf σ) y,
      fun y => chg_letterMap _ _ _ _ _ _ _ _ _ _ (monD_mulD P ρ₁) _ (monD_mulD P ρ₂)
        (fun x => Subtype.ext (tensQ_onB P f _ x.1)) y⟩
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ₂, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ j, b j • dQ P hf (dQ P (hπ j) x) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, coe_dQ]
      exact (sum_tensQ P b π hsum x.1).symm
    have hms := map_sum (AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂))
      (fun j => b j • dQ P hf (dQ P (hπ j) x)) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hms
    rw [hx, hms]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [wdMk_smul]
    exact Submodule.smul_mem _ _ ⟨wdMk P ι ρ₁ (dQ P (hπ j) x), hΦmk _⟩
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact wdRep_iso_of_equiv P ι Bw h hj (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩) hΦρ hΦN

theorem wdPst_enlarge {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1)
    (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1) (hV₁ : IsPst P (Bw.repE L₁ r₁)) :
    wdPst P ι Bw h hj (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁)) =
      wdPst P ι Bw h hj (Bw.repE L₁ r₁) := by
  have hV₂ := GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hV₁
  haveI := hV₁.finite
  haveI := hV₂.finite
  obtain ⟨n, b, π, hπ, hsum⟩ := exists_decomp hL (m := m)
  have hf : ∀ g v, incV hL m (Bw.repE L₁ r₁ g v) =
      Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g (incV hL m v) :=
    fun g v => incV_mulVec hL _ v
  have hπ' : ∀ (j : Fin n) (g : ↥(GK Bw.Kw)) (v : Fin m → ↥L₂.1),
      π j (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g v) =
        Bw.repE L₁ r₁ g (π j v) :=
    fun j g v => hπ j (r₁ (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L₁.1) v
  have hdim : finrank ℂ (WDSpace P ι (Bw.repE L₁ r₁)) =
      finrank ℂ (WDSpace P ι (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :=
    (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₁ _ _ hV₁).trans ((Module.finrank_fin_fun _).trans
      ((Module.finrank_fin_fun _).symm.trans (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₂ _ _ hV₂).symm))
  rw [wdPst_of_isPst ι Bw h hj hV₂, wdPst_of_isPst ι Bw h hj hV₁]
  exact (WD.sound (wdRep_iso_of_coord P ι Bw h hj (IntermediateField.inclusion hL).toRingHom (fun _ => rfl) hf
    (incV_smul hL) b π hπ' hsum hdim)).symm

end Enlarge

section Main

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E' Ω (Dec (F := E') A) O')
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (hj : Induces Bw) (hj' : Induces Bw')

section Res

variable (hc : IsResBridge Bw Bw') {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V)

def dpstRes : ↥(Dpst P ρ) ≃ₗ[↥LL.1] ↥(Dpst P (resTo ρ hc.Kw_le)) :=
  LinearEquiv.ofEq _ _ (Dpst_resTo P ρ hc.Kw_le).symm

@[simp] theorem coe_dpstRes (x : ↥(Dpst P ρ)) : ((dpstRes P Bw Bw' hc ρ x : ↥(Dpst P (resTo ρ hc.Kw_le))) :
    V ⊗[ℚ_[l]] Bst P) = x := rfl

theorem dpstRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    dpstRes P Bw Bw' hc ρ (mulD P ρ c x) = mulD P (resTo ρ hc.Kw_le) c (dpstRes P Bw Bw' hc ρ x) := rfl

def wdRes : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (resTo ρ hc.Kw_le) :=
  letI := algC ι LL
  letterEquiv (mulD P ρ) (mulD P (resTo ρ hc.Kw_le)) ℂ (urC ι) (dpstRes P Bw Bw' hc ρ) (dpstRes_mulD P Bw Bw' hc ρ)

@[simp] theorem wdRes_mk (x : ↥(Dpst P ρ)) :
    wdRes P ι Bw Bw' hc ρ (wdMk P ι ρ x) = wdMk P ι (resTo ρ hc.Kw_le) (dpstRes P Bw Bw' hc ρ x) := rfl

@[simp] theorem wdRes_symm_mk (x : ↥(Dpst P (resTo ρ hc.Kw_le))) :
    (wdRes P ι Bw Bw' hc ρ).symm (wdMk P ι (resTo ρ hc.Kw_le) x) =
      wdMk P ι ρ ((dpstRes P Bw Bw' hc ρ).symm x) := rfl

theorem wdN_res : wdN P ι (resTo ρ hc.Kw_le) = (wdRes P ι Bw Bw' hc ρ).conjAlgEquiv ℂ (wdN P ι ρ) := by
  refine wd_ext P ι (resTo ρ hc.Kw_le) fun x => ?_
  rw [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

include hc in

theorem weilToGK_res (σ : ↥(Weil h')) :
    ((weilToGK Bw' h' σ : ↥(GK Bw'.Kw)) : GQ l) = ((weilToGK Bw h (resW h h' σ) : ↥(GK Bw.Kw)) : GQ l) := by
  have e : resDec E A (Subgroup.inclusion (Weil_le_Dec h') σ) = Subgroup.inclusion (Weil_le_Dec h) (resW h h' σ) :=
    rfl
  show ((Bw'.e _ : ↥(GK Bw'.Kw)) : GQ l) = ((Bw.e _ : ↥(GK Bw.Kw)) : GQ l)
  rw [hc, e]

include hj in

theorem alpha_resW (σ : ↥(Weil h')) : alpha l (resW h h' σ) = alpha l σ := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have e : resDeg l w' = resDeg l w * resF h h' := by
    rw [resDeg, normV_eq_pow_resF h h', normV_eq_pow (hj.mem_placesOver h), ← pow_mul, Nat.log_pow hl]
  rw [alpha, alpha, deg_resW, e]
  push_cast; ring

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (resTo ρ hc.Kw_le))]

theorem phiU_zpow_res (n : ℤ) (x : ↥(Dpst P ρ)) :
    ((phiU P (resTo ρ hc.Kw_le) ^ n : (End ↥LL.1 ↥(Dpst P (resTo ρ hc.Kw_le)))ˣ) :
        End ↥LL.1 ↥(Dpst P (resTo ρ hc.Kw_le))) (dpstRes P Bw Bw' hc ρ x) =
      dpstRes P Bw Bw' hc ρ (((phiU P ρ ^ n : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x) :=
  zpow_intertwine (dpstRes P Bw Bw' hc ρ).toLinearMap (phiU P ρ) (phiU P (resTo ρ hc.Kw_le))
    (fun _ => Subtype.ext rfl) n x

include hj in

theorem weilD_res (σ : ↥(Weil h')) (x : ↥(Dpst P ρ)) :
    weilD Bw' h' P (resTo ρ hc.Kw_le) σ (dpstRes P Bw Bw' hc ρ x) =
      dpstRes P Bw Bw' hc ρ (weilD Bw h P ρ (resW h h' σ) x) := by
  apply Subtype.ext
  have e2 := congrArg Subtype.val (phiU_zpow_res P Bw Bw' hc ρ (-alpha l σ) x)
  have e3 := alpha_resW Bw h h' hj σ
  have e : Subgroup.inclusion (GK_le hc.Kw_le) (weilToGK Bw' h' σ) = weilToGK Bw h (resW h h' σ) :=
    Subtype.ext (weilToGK_res Bw Bw' h h' hc σ)
  calc ((weilD Bw' h' P (resTo ρ hc.Kw_le) σ (dpstRes P Bw Bw' hc ρ x) : ↥(Dpst P (resTo ρ hc.Kw_le))) :
        V ⊗[ℚ_[l]] Bst P)
      = stRep P (resTo ρ hc.Kw_le) (weilToGK Bw' h' σ)
          ((((phiU P (resTo ρ hc.Kw_le) ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P (resTo ρ hc.Kw_le)))ˣ) :
            End ↥LL.1 ↥(Dpst P (resTo ρ hc.Kw_le))) (dpstRes P Bw Bw' hc ρ x) :
              ↥(Dpst P (resTo ρ hc.Kw_le))) : V ⊗[ℚ_[l]] Bst P) := rfl
    _ = stRep P ρ (Subgroup.inclusion (GK_le hc.Kw_le) (weilToGK Bw' h' σ))
          ((((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x :
            ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) := by
        rw [e2]; rfl
    _ = stRep P ρ (weilToGK Bw h (resW h h' σ))
          ((((phiU P ρ ^ (-alpha l (resW h h' σ)) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x :
            ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) := by
        rw [e, e3]
    _ = _ := rfl

theorem wdRho_res (σ : ↥(Weil h')) :
    wdRho P ι Bw' h' hj' (resTo ρ hc.Kw_le) σ =
      (wdRes P ι Bw Bw' hc ρ).conjAlgEquiv ℂ (wdRho P ι Bw h hj ρ (resW h h' σ)) := by
  refine wd_ext P ι (resTo ρ hc.Kw_le) fun x => ?_
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [wdRes_symm_mk, wdRho_mk, wdRho_mk, wdRes_mk, ← weilD_res P Bw Bw' h h' hj hc,
    LinearEquiv.apply_symm_apply]

end Res

theorem wdPst_resTo (hc : IsResBridge Bw Bw') {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) :
    wdPst P ι Bw' h' hj' (resTo ρ hc.Kw_le) = WD.res h h' (wdPst P ι Bw h hj ρ) := by
  have hV' : IsPst P (resTo ρ hc.Kw_le) := (GlobalTheory.PstLaws.isPst_resTo_iff P ρ hc.Kw_le).mpr hV
  haveI := hV.finite
  haveI := hV'.finite
  rw [wdPst_of_isPst ι Bw' h' hj' hV', wdPst_of_isPst ι Bw h hj hV, WD.res_mk]
  refine WD.sound ?_
  have h1 : IsFSS (wdRho P ι Bw' h' hj' (resTo ρ hc.Kw_le)) (wdN P ι (resTo ρ hc.Kw_le))
      (wdRep P ι Bw' h' hj' (resTo ρ hc.Kw_le)) := wdRep_spec P ι Bw' h' hj' (resTo ρ hc.Kw_le)
  have h2 : IsFSS ((wdRho P ι Bw h hj ρ).comp (resW h h')) (wdN P ι ρ) (resRep h h' (wdRep P ι Bw h hj ρ)) :=
    IsFSS.res h h' (wdRep_spec P ι Bw h hj ρ)
  have h3 := h2.transport (wdRes P ι Bw Bw' hc ρ) (wdRho_res P ι Bw Bw' h h' hj hj' hc ρ)
    (wdN_res P ι Bw Bw' hc ρ)
  exact (h1.iso h3).trans (WDRep.iso_transport _ _).symm

theorem wdPst_model_eq {a : ℕ} {r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)} {LL₁ LL₂ : FinExt l}
    {r₁ : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL₁.1} {r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL₂.1}
    (m₁ : IsModel Bw r LL₁ r₁) (m₂ : IsModel Bw r LL₂ r₂) (p₁ : IsPst P (Bw.repE LL₁ r₁))
    (p₂ : IsPst P (Bw.repE LL₂ r₂)) :
    wdPst P ι Bw h hj (Bw.repE LL₁ r₁) = wdPst P ι Bw h hj (Bw.repE LL₂ r₂) := by
  have l₁ : LL₁.1 ≤ (supExt LL₁ LL₂).1 := le_sup_left
  have l₂ : LL₂.1 ≤ (supExt LL₁ LL₂).1 := le_sup_right
  have e := IsModel.unique Bw r (m₁.enlarge l₁) (m₂.enlarge l₂)
  rw [← wdPst_enlarge P ι Bw h hj l₁ r₁ p₁,
    ← wdPst_enlarge P ι Bw h hj l₂ r₂ p₂, e]

theorem wdAt_res (hc : IsResBridge Bw Bw') {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l))
    (hr : IsPstAt P Bw r) :
    IsPstAt P Bw' (r.comp (resDec E A)) ∧
      wdAt P ι Bw' h' hj' (r.comp (resDec E A)) = WD.res h h' (wdAt P ι Bw h hj r) := by
  obtain ⟨LL₁, r₁, hm₁, hp₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hr
  have l₁ : LL₁.1 ≤ (supExt LL₁ Bw'.LL).1 := le_sup_left
  have l₂ : Bw'.LL.1 ≤ (supExt LL₁ Bw'.LL).1 := le_sup_right
  obtain ⟨r₃, hr₃⟩ : ∃ r₃, r₃ = Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ := ⟨_, rfl⟩
  have hm₃ : IsModel Bw r (supExt LL₁ Bw'.LL) r₃ := hr₃ ▸ hm₁.enlarge l₁
  have hp₃ : IsPst P (Bw.repE (supExt LL₁ Bw'.LL) r₃) := hr₃ ▸ GlobalTheory.PstExt.isPst_enlarge P Bw l₁ r₁ hp₁

  have key : ∀ g' : ↥(GK Bw'.Kw),
      resDec E A (Bw'.e.symm g') = Bw.e.symm (Subgroup.inclusion (GK_le hc.Kw_le) g') := by
    intro g'
    apply Bw.e.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [← hc (Bw'.e.symm g'), MulEquiv.apply_symm_apply]
    rfl
  have heq : Bw'.repE (supExt LL₁ Bw'.LL) (r₃.comp (resDec E A)) =
      resTo (Bw.repE (supExt LL₁ Bw'.LL) r₃) hc.Kw_le := by
    refine MonoidHom.ext fun g' => ?_
    simp only [LocBridge.repE, resTo, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [key]
  have hm' : IsModel Bw' (r.comp (resDec E A)) (supExt LL₁ Bw'.LL) (r₃.comp (resDec E A)) :=
    ⟨l₂, by rw [← hm₃.2]; rfl⟩
  have hp' : IsPst P (Bw'.repE (supExt LL₁ Bw'.LL) (r₃.comp (resDec E A))) := by
    rw [heq]
    exact (GlobalTheory.PstLaws.isPst_resTo_iff P _ hc.Kw_le).mpr hp₃
  have hr' : IsPstAt P Bw' (r.comp (resDec E A)) := ⟨_, _, hm', hp'⟩
  refine ⟨hr', ?_⟩
  obtain ⟨LL₄, r₄, hm₄, hp₄, e₄⟩ := wdAt_of_isPstAt ι Bw' h' hj' hr'
  rw [e₄, e₁, wdPst_model_eq P ι Bw' h' hj' hm₄ hm' hp₄ hp', heq,
    wdPst_resTo P ι Bw Bw' h h' hj hj' hc _ hp₃, hr₃,
    wdPst_enlarge P ι Bw h hj l₁ r₁ hp₁]

end Main

end PositivityTheory.Pf1.CLGD.WdRestrict
