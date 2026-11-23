import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CoefModel

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem exists_onb {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    ∃ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * B = 1 := by
  obtain ⟨B, hB, e⟩ := ps_factor hG
  have hB' : IsUnit (Bᴴ).det := by rw [Matrix.det_conjTranspose]; exact hB.star
  refine ⟨(Matrix.nonsingInvUnit _ hB')⁻¹, ?_⟩
  show ((Bᴴ)⁻¹)ᴴ * G * (Bᴴ)⁻¹ = 1
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose, e, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hB, Matrix.one_mul, Matrix.mul_nonsing_inv _ hB']

theorem eq_bot_or_top_of_conj {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ : Γ →* Module.End ℂ W)
    (S T : Γ → Prop) (B : Γ) (hS : ∀ U : Submodule ℂ W, (∀ g, S g → ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hT : ∀ g, S g → T (B * g * B⁻¹)) (U : Submodule ℂ W) (hU : ∀ g, T g → ∀ x ∈ U, ρ g x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  have hinv : ∀ x, ρ B (ρ B⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h := hS (U.comap (ρ B)) fun g hg x hx => by
    have h1 := hU _ (hT g hg) _ hx
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul] at h1
    exact h1
  rcases h with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : ρ B⁻¹ x ∈ U.comap (ρ B) := by rw [Submodule.mem_comap, hinv]; exact hx
    rw [h, Submodule.mem_bot] at this
    rw [← hinv x, this, map_zero]
    exact zero_mem _
  · right
    rw [eq_top_iff]
    intro x _
    have : ρ B⁻¹ x ∈ U.comap (ρ B) := by rw [h]; trivial
    rwa [Submodule.mem_comap, hinv] at this

theorem conj_unitary {G : Matrix (Fin n) (Fin n) ℂ} {B u : GL (Fin n) ℂ}
    (hB : (B : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * B = 1)
    (hu : (u : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ((B * u * B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * (B * u * B⁻¹ : GL (Fin n) ℂ) = G := by
  have e : G = ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * (B⁻¹ : GL (Fin n) ℂ) := by
    have := congrArg (fun M => ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * M * (B⁻¹ : GL (Fin n) ℂ)) hB
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one,
      Matrix.one_mul] at this
    exact this
  have hu' : (u : Matrix (Fin n) (Fin n) ℂ)ᴴ * u = 1 := hu.1
  simp only [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((u : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((B : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * B) * u) * (B⁻¹ : GL (Fin n) ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = G := by rw [hB, Matrix.mul_one, hu', Matrix.mul_one, ← e]

theorem eq_bot_or_top (lam : ι → DomWeight n) {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, (G τ).PosDef)
    (U : Submodule ℂ (VV ℂ lam))
    (hU : ∀ g : ι → GL (Fin n) ℂ, (∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ)ᴴ * G τ * g τ = G τ) →
      ∀ x ∈ U, rhoK lam g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  choose B hB using fun τ => exists_onb (hG τ)
  exact eq_bot_or_top_of_conj (rhoK lam) _ _ B (GlobalTheory.CoefIrred.vv_irreducible_unitary ι n lam)
    (fun g hg τ => conj_unitary (hB τ) (hg τ)) U hU

section BaseChange

variable {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n)

def mapVV : VV K lam →ₛₗ[φ] VV ℂ lam where
  toFun x := ⟨map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (by simp [smul_eq_C_mul])

theorem mapVV_coe (x : VV K lam) : (mapVV φ lam x : Pol ℂ ι n) = map φ x.1 := rfl

theorem mapVV_rhoK (g : ι → GL (Fin n) K) (x : VV K lam) :
    mapVV φ lam (rhoK lam g x) = rhoK lam (fun τ => Formalism.UG.bc φ (g τ)) (mapVV φ lam x) :=
  Subtype.ext (GlobalTheory.ValCmp.use₂ φ lam g x.1)

theorem linearIndependent_mapVV : LinearIndependent ℂ fun i => mapVV φ lam (bVV K lam i) := by
  refine LinearIndependent.of_comp (VV ℂ lam).subtype ?_
  convert Formalism.L2.Col.linearIndependent_map φ (bVVfun K lam) (bVVfun_spec K lam).1 using 1
  funext i
  simp [mapVV_coe, bVV_coe]

theorem span_mapVV : Submodule.span ℂ (Set.range fun i => mapVV φ lam (bVV K lam i)) = ⊤ :=
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  (linearIndependent_mapVV φ lam).span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis (bVV ℂ lam)).symm

variable [StarRing K] (hφ : ∀ x, φ (star x) = starRingEnd ℂ (φ x))
include hφ

theorem fockS_map {σ : Type} (f g : MvPolynomial σ K) : fockS (map φ f) (map φ g) = φ (fockS f g) := by
  rw [fockS_eq_sum _ _ f.support (support_map_subset _ _), fockS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map, hφ]

theorem pairK_mapVV (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) :
    pairK lam (fun τ => (G τ).map φ) (mapVV φ lam x) (mapVV φ lam y) = φ (pairK lam G x y) := by
  have h1 : (map φ).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).toRingHom =
      (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) fun τ => ((G τ).map φ)ᵀ).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp [blockAct_X]
  have h2 : map φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((G τ).map φ)ᵀ) (map φ y.1) :=
    congrArg (fun ψ : Pol K ι n →+* Pol ℂ ι n => ψ y.1) h1
  have h3 : φ (gramTw lam G) = gramTw lam fun τ => (G τ).map φ := by
    unfold gramTw
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  have h4 : φ (extNorm K lam) = extNorm ℂ lam := by
    unfold extNorm
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← fockS_map φ hφ, map_extremal]
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, mapVV_coe, mapVV_coe, ← h2, fockL_apply, fockL_apply,
    fockS_map φ hφ, map_mul, map_div₀, h3, h4]

end BaseChange

theorem pairK_pos (lam : ι → DomWeight n) {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, (G τ).PosDef)
    (x : VV ℂ lam) (hx : x ≠ 0) : 0 < pairK lam G x x := by
  classical
  have h := pairingPositive_holds ℂ ι n lam G (RingHom.id ℂ) (fun τ => hG τ)
  have h1 := h.dotProduct_mulVec_pos (x := fun i => (bVV ℂ lam).repr x i) (fun h0 => hx
    ((bVV ℂ lam).repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun h0 i)))
  have h2 : ∀ (P : VV ℂ lam →ₗ⋆[ℂ] VV ℂ lam →ₗ[ℂ] ℂ) (c : VVIdx lam → ℂ) (b : VVIdx lam → VV ℂ lam),
      P (∑ i, c i • b i) (∑ i, c i • b i) = star c ⬝ᵥ (Matrix.of fun i j => P (b i) (b j)) *ᵥ c := by
    intro P c b
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 := h2 (pairK lam G) (fun i => (bVV ℂ lam).repr x i) (bVV ℂ lam)
  rw [(bVV ℂ lam).sum_repr x] at h3
  rw [h3]
  exact h1

def Hilb (lam : ι → DomWeight n) {G : ι → Matrix (Fin n) (Fin n) ℂ} (_hG : ∀ τ, (G τ).PosDef) : Type := VV ℂ lam

section Hilb

variable (lam : ι → DomWeight n) {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, (G τ).PosDef)

instance : AddCommGroup (Hilb lam hG) := inferInstanceAs (AddCommGroup (VV ℂ lam))

instance : Module ℂ (Hilb lam hG) := inferInstanceAs (Module ℂ (VV ℂ lam))

def toHilb : VV ℂ lam ≃ₗ[ℂ] Hilb lam hG := LinearEquiv.refl ℂ (VV ℂ lam)

@[reducible] def core : InnerProductSpace.Core ℂ (Hilb lam hG) where
  inner x y := pairK lam G ((toHilb lam hG).symm x) ((toHilb lam hG).symm y)
  conj_inner_symm x y := (pairSymm ℂ ι n lam G fun τ => (hG τ).isHermitian).eq _ _
  re_inner_nonneg x := by
    by_cases hx : (toHilb lam hG).symm x = 0
    · simp [hx]
    · exact (Complex.le_def.1 (pairK_pos lam hG _ hx).le).1
  add_left x y z := by rw [map_add, map_add, LinearMap.add_apply]
  smul_left x y r := by rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  definite x hx := by
    by_contra h
    exact (pairK_pos lam hG _ (mt (toHilb lam hG).symm.map_eq_zero_iff.1 h)).ne' hx

instance : NormedAddCommGroup (Hilb lam hG) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core lam hG)

instance : InnerProductSpace ℂ (Hilb lam hG) := InnerProductSpace.ofCore (core lam hG).toCore

instance : FiniteDimensional ℂ (Hilb lam hG) := Module.Finite.of_basis ((bVV ℂ lam).map (toHilb lam hG))

theorem inner_toHilb (x y : VV ℂ lam) : inner ℂ (toHilb lam hG x) (toHilb lam hG y) = pairK lam G x y := rfl

theorem nontrivial_Hilb : Nontrivial (Hilb lam hG) := by
  refine ⟨⟨toHilb lam hG ⟨ten fun τ => extremal ℂ n (lam τ), GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ =>
    Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (natW_antitone (lam τ))⟩, 0, fun h => ?_⟩⟩
  exact GlobalTheory.Proof.TensorMapDescent.ten_ne_zero _ (fun τ => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _)
    (congrArg Subtype.val ((toHilb lam hG).map_eq_zero_iff.1 h))

def rhoH : (ι → GL (Fin n) ℂ) →* Module.End ℂ (Hilb lam hG) :=
  ((toHilb lam hG).conjRingEquiv : Module.End ℂ (VV ℂ lam) →* Module.End ℂ (Hilb lam hG)).comp (rhoK lam)

theorem rhoH_toHilb (g : ι → GL (Fin n) ℂ) (x : VV ℂ lam) :
    rhoH lam hG g (toHilb lam hG x) = toHilb lam hG (rhoK lam g x) := by
  simp [rhoH]

omit [Fintype ι] in
theorem continuous_coeff_blockAct {X : Type} [TopologicalSpace X] (M : X → ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, Continuous fun x => M x τ) (F : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    ∀ m, Continuous fun x => coeff m (Formalism.GradedWeylDivisibility.blockAct ℂ (M x) F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => intro m; simp only [algHom_C]; exact continuous_const
  | add p q hp hq => intro m; simp only [map_add, coeff_add]; exact (hp m).add (hq m)
  | mul_X p v hp =>
    intro m
    simp only [map_mul, coeff_mul]
    refine continuous_finsetSum _ fun a _ => (hp _).mul ?_
    simp only [Formalism.GradedWeylDivisibility.blockAct, aeval_X, coeff_sum, coeff_C_mul]
    exact continuous_finsetSum _ fun b _ => ((hM _).matrix_elem _ _).mul continuous_const

theorem continuous_rhoH {X : Type} [TopologicalSpace X] (A : X → ι → GL (Fin n) ℂ)
    (hA : ∀ τ, Continuous fun x => (A x τ : Matrix (Fin n) (Fin n) ℂ)) (v : Hilb lam hG) :
    Continuous fun x => rhoH lam hG (A x) v := by
  obtain ⟨v, rfl⟩ := (toHilb lam hG).surjective v
  let L : Hilb lam hG →ₗ[ℂ] ((ι × Fin n × Fin n →₀ ℕ) → ℂ) :=
    LinearMap.pi fun m => lcoeff ℂ m ∘ₗ (VV ℂ lam).subtype ∘ₗ (toHilb lam hG).symm.toLinearMap
  have hL : ∀ y m, L (toHilb lam hG y) m = coeff m (y : Pol ℂ ι n) := fun _ _ => rfl
  have hk : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨y, rfl⟩ := (toHilb lam hG).surjective y
    have : y = 0 := Subtype.ext (MvPolynomial.ext _ _ fun m => (hL y m).symm.trans (congrFun hy m))
    rw [this, map_zero]
  rw [(LinearMap.isClosedEmbedding_of_injective hk).isInducing.continuous_iff]
  refine continuous_pi fun m => ?_
  simp only [Function.comp_apply, rhoH_toHilb, hL, rhoK_coe, actP, LinearMap.smul_apply, coeff_smul, smul_eq_mul,
    detTw_eq, AlgHom.toLinearMap_apply, trAct]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => (hA τ).matrix_det.zpow₀ _ fun x => Or.inl ?_)
    (continuous_coeff_blockAct _ (fun τ => (hA τ).matrix_transpose) _ m)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (A x τ).isUnit).ne_zero

end Hilb

theorem invTr_unitary {G : Matrix (Fin n) (Fin n) ℂ} {g : GL (Fin n) ℂ}
    (hg : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * g = G) :
    (inside₂ ℂ n g : Matrix (Fin n) (Fin n) ℂ)ᴴ * (G⁻¹)ᵀ * inside₂ ℂ n g = (G⁻¹)ᵀ := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M⁻¹)ᵀ) hg
  simp only [Matrix.mul_inv_rev, Matrix.transpose_mul] at h
  show (((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ)ᴴ * (G⁻¹)ᵀ *
    ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = (G⁻¹)ᵀ
  rw [conjTranspose_transpose', Matrix.coe_units_inv, Matrix.conjTranspose_nonsing_inv]
  exact h

theorem invTr_invTr (g : GL (Fin n) ℂ) : inside₂ ℂ n (inside₂ ℂ n g) = g := Units.ext (Matrix.transpose_transpose _)

end GlobalTheory.CoefModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefModel

variable {D : D7}

def realGL (θ : InfFam D) (V : HSp D) : GA D V →* (D.what₂.Tau → GL (Fin V.rank) ℂ) :=
  MonoidHom.pi fun τ => (Formalism.UG.bc (θ τ)).comp (infHom V)

theorem realGL_coe (θ : InfFam D) (V : HSp D) (h : GA D V) (τ : D.what₂.Tau) :
    (realGL θ V h τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = archM V (θ τ) h := rfl

theorem realGL_laws {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) :
    (∀ τ, Continuous (archM V (θ τ))) ∧ ∀ g : D.what₂.Tau → GL (Fin V.rank) ℂ,
      (∀ τ, (g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * V.gram.map (tauE D τ) * g τ = V.gram.map (tauE D τ)) →
      ∃ h, realGL θ V h = g := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  have hsurj : ∀ ρ, r ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩ = ρ := fun ρ => GlobalTheory.PointAtPlace.tauE_injective (hr _)
  obtain ⟨-, -, h1, h2⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact GlobalTheory.PointAtPlace.tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  refine ⟨fun τ => ?_, fun g hg => ?_⟩
  · have := h1 ⟨tauE D τ, (hmem _).2 ⟨τ, rfl⟩⟩
    rwa [hsurj] at this
  · obtain ⟨h, -, hu⟩ := h2 (fun σ => g (r σ)) (fun σ => by rw [← hr σ]; exact hg _)
    refine ⟨h, funext fun τ => Units.ext ?_⟩
    have := hu ⟨tauE D τ, (hmem _).2 ⟨τ, rfl⟩⟩
    rwa [hsurj] at this

theorem realGL_rat {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E)
    (h : Bridge.IsRatMat V γ γE) (τ : D.what₂.Tau) : realGL θ V γ τ = Formalism.UG.bc (tauE D τ) γE := by
  refine Units.ext ?_
  have e1 : (matHom V γ).1 = (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (AF D.host.F)) :=
    congrArg Units.val h
  have e2 : ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Ainf D.host.F))).map (θ τ) =
      (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D τ) := by
    ext i j
    exact (hθ τ).1 _
  rw [bc_coe, ← e2, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← e1]
  rfl

def coefOf {V : HSp D} (lam : D.what₂.Tau → DomWeight V.rank) {G : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hG : ∀ τ, (G τ).PosDef) (A : GA D V →* (D.what₂.Tau → GL (Fin V.rank) ℂ)) : CoefA V where
  W := Hilb lam hG
  ρ := (rhoH lam hG).comp A

theorem coefOf_is {V : HSp D} (lam : D.what₂.Tau → DomWeight V.rank)
    {G : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hG : ∀ τ, (G τ).PosDef)
    (A : GA D V →* (D.what₂.Tau → GL (Fin V.rank) ℂ)) (h1 : ∀ h ∈ GfC V, A h = 1)
    (h2 : ∀ h τ, (A h τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * G τ * A h τ = G τ)
    (h3 : ∀ τ, Continuous fun h => (A h τ : Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (h4 : ∀ g : D.what₂.Tau → GL (Fin V.rank) ℂ,
      (∀ τ, (g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * G τ * g τ = G τ) → ∃ h, A h = g) :
    (coefOf lam hG A).Is := by
  refine ⟨fun h hh => ?_, fun h x y => ?_, continuous_rhoH lam hG A h3, nontrivial_Hilb lam hG, fun U hU => ?_⟩
  · show rhoH lam hG (A h) = 1
    rw [h1 h hh, map_one]
  · obtain ⟨x, rfl⟩ := (toHilb lam hG).surjective x
    obtain ⟨y, rfl⟩ := (toHilb lam hG).surjective y
    show inner ℂ (rhoH lam hG (A h) _) (rhoH lam hG (A h) _) = _
    rw [rhoH_toHilb, rhoH_toHilb, inner_toHilb]
    exact pairInv ℂ _ _ lam G (A h) (h2 h) x y
  · have h := eq_bot_or_top lam hG (Submodule.comap (toHilb lam hG).toLinearMap U) fun g hg x hx => by
      obtain ⟨h, rfl⟩ := h4 g hg
      have := hU h ⟨_, hx, rfl⟩
      exact (congrArg (· ∈ U) (rhoH_toHilb lam hG (A h) x)).mp this
    refine h.imp (fun e => ?_) fun e => ?_
    · exact Submodule.comap_injective_of_surjective (toHilb lam hG).surjective
        (e.trans (LinearEquiv.ker (toHilb lam hG)).symm)
    · exact Submodule.comap_injective_of_surjective (toHilb lam hG).surjective e

theorem exists_coef_round (V : HSp D) (hV : ∀ τ, (V.gram.map (tauE D τ)).PosDef)
    (lam : D.what₂.Tau → DomWeight V.rank) :
    ∃ (c : CoefA V) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W), c.Is ∧
      Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) _) ∧
      ∀ x y, inner ℂ (c0 x) (c0 y) = D.what₂.embLL (pairVr (labLL D) _ V.gram x y) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨hc, hs⟩ := realGL_laws hθ V
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hG : ∀ τ, (((V.gram.map (tauE D τ))⁻¹)ᵀ).PosDef := fun τ => (hV τ).inv.transpose
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  refine ⟨coefOf lam hG (invTrK.comp (realGL θ V)),
    (toHilb lam hG).toLinearMap.comp (mapVV D.what₂.embLL lam), coefOf_is lam hG _ (fun h hh => ?_) (fun h τ => ?_)
      (fun τ => ?_) (fun g hg => ?_), ⟨fun γ γE hγ v => ?_, ?_, ?_⟩, fun x y => ?_⟩
  · have : realGL θ V h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom V h) = 1
      rw [show infHom V h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, this, map_one]
  · exact invTr_unitary (g := realGL θ V h τ) (GlobalTheory.RecDictModel.archM_unitary V (hθ τ) h)
  · refine ((hc τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (invTrK g) fun τ => by
      have := invTr_unitary (hg τ)
      rwa [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (hV τ).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, e]
    exact funext fun τ => invTr_invTr _
  · show toHilb lam hG (mapVV _ lam (rhoK lam (invTrK (embGL (labLL D) γE)) v)) =
      rhoH lam hG (invTrK (realGL θ V γ)) (toHilb lam hG (mapVV _ lam v))
    have e : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    rw [rhoH_toHilb, mapVV_rhoK, e]
  · exact (linearIndependent_mapVV D.what₂.embLL lam).map' (toHilb lam hG).toLinearMap (LinearEquiv.ker _)
  · exact span_mapVV D.what₂.embLL lam
  · show inner ℂ (toHilb lam hG (mapVV D.what₂.embLL lam x)) (toHilb lam hG (mapVV D.what₂.embLL lam y)) =
      D.what₂.embLL (pairK lam (gramKd (labLL D) V.gram) x y)
    rw [inner_toHilb, ← pairK_mapVV _ _ D.starLL_cx]
    have e : (fun τ => ((V.gram.map (tauE D τ))⁻¹)ᵀ) = fun τ => (gramKd (labLL D) V.gram τ).map D.what₂.embLL := by
      funext τ
      have e1 : V.gram.map (tauE D τ) = (V.gram.map (labLL D τ)).map D.what₂.embLL := by
        ext a b
        exact (hlab _ _).symm
      have hu : IsUnit (V.gram.map (labLL D τ)).det := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact ((_root_.map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)).isUnit
      rw [gramKd, Matrix.transpose_map, e1]
      congr 1
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg (fun G => pairK lam G (mapVV D.what₂.embLL lam x) (mapVV D.what₂.embLL lam y)) e

theorem exists_coef_lift : ∀ (D : D7) (i : Fin D.R.m), (Vc D i).IsPosDef → ∃ (c : CoefA (Vc D i)) (c0 : VV D.what₂.LL (lamV D i) →ₛₗ[D.what₂.embLL] c.W), c.Is ∧ Bridge.CoefMapTie (Vc D i) c.coef c0 (rhoVr (labLL D) _) ∧ ∀ x y, inner ℂ (c0 x) (c0 y) = D.what₂.embLL (pairVr (labLL D) _ (if D.sp.Vneg ((i : ℕ) + 1) then -(Vc D i).gram else (Vc D i).gram) x y) := by
  intro D i h
  rw [GlobalTheory.StdFrame.neg_eq_false_of_posDef D i h, if_neg Bool.false_ne_true]
  refine exists_coef_round (Vc D i) (fun τ => ?_) _
  have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
  rw [h (tauE D τ)] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

end GlobalTheory.CoefModel
