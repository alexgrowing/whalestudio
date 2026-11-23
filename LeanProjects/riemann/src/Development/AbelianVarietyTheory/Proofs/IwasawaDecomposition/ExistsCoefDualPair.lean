import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHCTypeUConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP

noncomputable section

namespace GlobalTheory.CoefSpace

section Local

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Matrix

theorem exists_dual_model {n : ℕ} (lam : DomWeight n) (u : Fin n → ℝ)
    (hu : ∀ i, u i = -((lam.w (Fin.rev i) : ℝ) + ((rhoVec n (Fin.rev i) : ℚ) : ℝ)))
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (h : IsHCTypeU n u π) :
    ∃ A : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ, Function.Injective A ∧ (∀ x, A x ∈ nablaSq ℂ n lam) ∧
      ∀ k : GL (Fin n) ℂ, (k : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∀ x, A (π (k : Matrix (Fin n) (Fin n) ℂ) x) = sqAct ℂ n lam (inside₂ ℂ n k) (A x) := by
  obtain ⟨H', _, _, π', e, h1, h2, h3, h4⟩ := GlobalTheory.NablaType.exists_isHCTypeU_nablaSq n lam
  have h5 := Conj.isHCTypeU_conj h1
  rw [← funext hu] at h5
  obtain ⟨A, hA⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU n u H H' π _ h h5
  refine ⟨e ∘ₗ A.toLinearMap, h2.comp A.injective, fun x => h3 _, fun k hk x => ?_⟩
  have hk' : (inside₂ ℂ n k : Matrix (Fin n) (Fin n) ℂ) = (k : Matrix (Fin n) (Fin n) ℂ).map star := by
    have : ((k⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (k : Matrix (Fin n) (Fin n) ℂ)ᴴ :=
      Units.inv_eq_of_mul_eq_one_left (Matrix.mem_unitaryGroup_iff'.1 hk)
    show ((k⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = _
    rw [this]
    rfl
  have hk2 : (inside₂ ℂ n k : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [hk']
    exact Matrix.transpose_mem_unitaryGroup_iff.2 (Unitary.star_mem hk)
  show e (A (π k x)) = sqAct ℂ n lam (inside₂ ℂ n k) (e (A x))
  rw [hA _ hk, ← h4 _ hk2, hk']

theorem enum_dual {n : ℕ} {lam : DomWeight n} {S : SPar} (h : Bridge.IsWtOfPar lam S) {u : Fin n → ℝ} {ε : Fin n → Bool}
    (he : IsEnum (dualPar S) u ε) (i : Fin n) :
    u i = -((lam.w (Fin.rev i) : ℝ) + ((rhoVec n (Fin.rev i) : ℚ) : ℝ)) := by
  obtain ⟨-, c, hc, hm, hw⟩ := h
  obtain ⟨hu, q, hq, hS⟩ := he
  have hq' : StrictAnti q := fun a b hab => by
    have := hu hab
    rw [hq, hq] at this
    exact_mod_cast this
  have hc' : StrictAnti fun a => -c (Fin.rev a) := fun a b hab => neg_lt_neg (hc (Fin.rev_lt_rev.2 hab))
  have hsub : Finset.univ.image (fun a => -c (Fin.rev a)) ⊆ Finset.univ.image q := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨s, hs⟩ := hm (Fin.rev a)
    have : (-c (Fin.rev a), s) ∈ dualPar S := Finset.mem_image.2 ⟨_, hs, rfl⟩
    rw [hS] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, congrArg Prod.fst hb⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injective _ hq'.injective, Finset.card_image_of_injective _ hc'.injective])
  have hr : Set.range (fun a => -c (Fin.rev a)) = Set.range q := by
    simpa using congrArg (fun s : Finset ℚ => (s : Set ℚ)) heq
  have := congrFun ((hc'.range_inj hq').1 hr) i
  have h2 : c (Fin.rev i) = lam.w (Fin.rev i) + rhoVec n (Fin.rev i) := by rw [hw]; ring
  rw [hq, ← this, h2]
  push_cast
  rfl

theorem sign_last {D : D7} (P : TPar D) (τ : D.what₂.Tau) {x : ℚ × Bool} (hx : x ∈ parB P D.R.m τ) : x.2 = true := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hz
  rcases hz with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, w, -, rfl⟩
  · rfl
  · exact decide_eq_true (Or.inl i.2.le)
  · rfl

theorem conj_unitary {n : ℕ} {B g : GL (Fin n) ℂ}
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) ∈
      Formalism.QuantumDeterminants.UH ((B : Matrix (Fin n) (Fin n) ℂ)ᴴ * (B : Matrix (Fin n) (Fin n) ℂ))) :
    ((B * g * B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have h : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((B : Matrix (Fin n) (Fin n) ℂ)ᴴ * B) * g =
    (B : Matrix (Fin n) (Fin n) ℂ)ᴴ * B := hg
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((B : Matrix (Fin n) (Fin n) ℂ)ᴴ * B) * g) * (B⁻¹ : GL (Fin n) ℂ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [h, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one, Matrix.one_mul,
        Units.mul_inv]

theorem conj_UH {n : ℕ} {B k : GL (Fin n) ℂ}
    (hk : (k : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ((B⁻¹ * k * B : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈
      Formalism.QuantumDeterminants.UH ((B : Matrix (Fin n) (Fin n) ℂ)ᴴ * (B : Matrix (Fin n) (Fin n) ℂ)) := by
  have h : (k : Matrix (Fin n) (Fin n) ℂ)ᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have e : (B : Matrix (Fin n) (Fin n) ℂ) * ((B⁻¹ * k * B : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = k * B := by
    rw [← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, Units.val_mul]
  show _ * _ * _ = _
  rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, e, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (k : Matrix (Fin n) (Fin n) ℂ), h, Matrix.one_mul]

theorem rhoK_mul {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g h : ι → GL (Fin n) ℂ) (x : VV ℂ lam) :
    rhoK lam g (rhoK lam h x) = rhoK lam (g * h) x := by
  rw [map_mul, Module.End.mul_apply]

theorem rhoK_one {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (x : VV ℂ lam) : rhoK lam 1 x = x := by
  rw [map_one, Module.End.one_apply]

theorem irred_gram {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ)
    (U : Submodule ℂ (VV ℂ lam))
    (hU : ∀ g : ι → GL (Fin n) ℂ, (∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramOf B τ)) →
      ∀ x ∈ U, rhoK lam g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  have hinv : ∀ x : VV ℂ lam, rhoK lam B⁻¹ (rhoK lam B x) = x := fun x => by
    rw [rhoK_mul, inv_mul_cancel, rhoK_one]
  have hst := GlobalTheory.CoefIrred.vv_irreducible_unitary _ _ lam (U.comap (rhoK lam B⁻¹)) fun k hk x hx => by
    have := hU (B⁻¹ * k * B) (fun τ => conj_UH (B := B τ) (hk τ)) _ (Submodule.mem_comap.1 hx)
    rw [rhoK_mul, mul_inv_cancel_right, ← rhoK_mul] at this
    exact Submodule.mem_comap.2 this
  rcases hst with h | h
  · left
    refine eq_bot_iff.2 fun x hx => ?_
    have h1 : rhoK lam B x ∈ U.comap (rhoK lam B⁻¹) := by
      rw [Submodule.mem_comap, hinv]
      exact hx
    rw [h, Submodule.mem_bot] at h1
    have h2 := hinv x
    rw [h1, map_zero] at h2
    exact (Submodule.mem_bot ℂ).2 h2.symm
  · right
    refine eq_top_iff.2 fun x _ => ?_
    have h1 : rhoK lam B x ∈ U.comap (rhoK lam B⁻¹) := by
      rw [h]
      exact Submodule.mem_top
    rwa [Submodule.mem_comap, hinv] at h1

end Local

section Global

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
  Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : InfFam D) (V : HSp D)

def infGL : GA D V →* (D.what₂.Tau → GL (Fin V.rank) ℂ) :=
  (MonoidHom.pi fun τ => Formalism.UG.bc (θ τ)).comp (infHom V)

theorem infGL_coe (h : GA D V) (τ : D.what₂.Tau) :
    (infGL θ V h τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = infMat D.sp.cm.sig V.gram (θ τ) h := rfl

variable (lam : D.what₂.Tau → DomWeight V.rank) (B : D.what₂.Tau → GL (Fin V.rank) ℂ)

def coefA : CoefA V where
  W := HV lam B
  ρ := (rhoK lam).comp (infGL θ V)

variable {θ V}

theorem coefA_fin {h : GA D V} (hh : h ∈ GfC V) : (coefA θ V lam B).ρ h = 1 := by
  have h1 : infHom V h = 1 := hh
  have h2 : infGL θ V h = 1 := by
    rw [infGL, MonoidHom.comp_apply, h1, map_one]
  have h3 : rhoK lam (infGL θ V h) = 1 := by rw [h2, map_one]
  exact h3

theorem coefA_unitary (hθ : IsInfFam θ) (hB : ∀ τ, gramOf B τ = gramAt D V τ) (h : GA D V) (x y : HV lam B) :
    inner ℂ ((coefA θ V lam B).ρ h x) ((coefA θ V lam B).ρ h y) = inner ℂ x y := by
  refine pairInv ℂ _ _ lam (gramOf B) (infGL θ V h) (fun τ => ?_) x y
  rw [hB, infGL_coe]
  exact GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V h τ

theorem coefA_cont (hθ : IsInfFam θ) (x : HV lam B) : Continuous fun h => (coefA θ V lam B).ρ h x :=
  continuous_HV lam B (infGL θ V) (fun τ => by
    simp only [infGL_coe]
    exact GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)) x

theorem coefA_irred (hθ : IsInfFam θ) (hB : ∀ τ, gramOf B τ = gramAt D V τ) (U : Submodule ℂ (VV ℂ lam))
    (hU : ∀ h, ∀ x ∈ U, rhoK lam (infGL θ V h) x ∈ U) : U = ⊥ ∨ U = ⊤ :=
  irred_gram lam B U fun g hg x hx => by
    obtain ⟨h, -, hh⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 (fun τ => g τ) fun τ => hB τ ▸ hg τ
    have e : infGL θ V h = g := funext fun τ => Units.ext ((infGL_coe θ V h τ).trans (hh τ))
    exact e ▸ hU h x hx

theorem coefA_is (hθ : IsInfFam θ) (hB : ∀ τ, gramOf B τ = gramAt D V τ) : (coefA θ V lam B).Is :=
  ⟨fun _ hh => coefA_fin lam B hh, coefA_unitary lam B hθ hB, coefA_cont lam B hθ,
    inferInstanceAs (Nontrivial (HV lam B)),
    fun U hU => coefA_irred lam B hθ hB U fun h x hx => hU h ⟨x, hx, rfl⟩⟩

theorem embLL_labLL (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem coefA_tie (hθ : IsInfFam θ) :
    Bridge.CoefMapTie V (coefA θ V lam B).coef (bcVV D.what₂.embLL lam) (rhoV (labLL D) lam) := by
  refine ⟨fun γ γE hγ v => Subtype.ext ?_, bcVV_indep _ lam, bcVV_span _ lam⟩
  have e : infGL θ V γ = fun τ => Formalism.UG.bc D.what₂.embLL (embGL (labLL D) γE τ) := by
    funext τ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h1 : ((matHom V (γ : GA D V)).1 a b) = incA D (γE.1 a b) := by
      rw [show matHom V (γ : GA D V) = _ from hγ]
      rfl
    show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((matHom V (γ : GA D V)).1 a b)) = D.what₂.embLL (labLL D τ (γE.1 a b))
    rw [h1, embLL_labLL, ← (hθ τ).1]
    exact congrArg (θ τ) ((Algebra.TensorProduct.map_tmul _ _ _ _).trans (by rw [map_one]; rfl))
  show MvPolynomial.map D.what₂.embLL (actP lam (embGL (labLL D) γE) v.1) =
    actP lam (infGL θ V γ) (MvPolynomial.map D.what₂.embLL v.1)
  rw [map_actP, e]

theorem coefA_inner (hB : ∀ τ, gramOf B τ = gramAt D V τ) (x y : VV D.what₂.LL lam) :
    inner ℂ (E := HV lam B) (bcVV D.what₂.embLL lam x) (bcVV D.what₂.embLL lam y) =
      D.what₂.embLL (pairV (labLL D) lam V.gram x y) := by
  have e : gramOf B = fun τ => (gramK (labLL D) V.gram τ).map D.what₂.embLL := by
    funext τ
    rw [hB]
    exact Matrix.ext fun a b => (embLL_labLL τ _).symm
  refine (inner_HV lam B _ _).trans ?_
  rw [pairV, pairK_apply, pairK_apply, map_pairP _ D.starLL_cx, e]
  rfl

theorem coefA_dual (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (hB : ∀ τ, (B τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = M.fr τ) (hG : ∀ τ, gramOf B τ = gramAt D V τ)
    (A : ∀ τ, M.H τ →ₗ[ℂ] MvPolynomial (Fin V.rank × Fin V.rank) ℂ) (h1 : ∀ τ, Function.Injective (A τ))
    (h2 : ∀ τ x, A τ x ∈ nablaSq ℂ _ (lam τ))
    (h3 : ∀ τ, ∀ k : GL (Fin V.rank) ℂ, (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Matrix.unitaryGroup _ ℂ →
      ∀ x, A τ (M.σ τ (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) x) = sqAct ℂ _ (lam τ) (inside₂ ℂ _ k) (A τ x)) :
    ∃ pr, IsDualPair θ M (coefA θ V lam B) pr := by
  classical
  let T : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau _).compLinearMap fun τ =>
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ).toLinearMap ∘ₗ A τ ∘ₗ (M.sm τ).subtype)
  have hT : ∀ v : M.Vec, T (PiTensorProduct.tprod ℂ v) = ten fun τ => A τ (v τ) := fun v => by
    simp [T, ten]
  let pr : VV ℂ lam →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ := (pairB lam).flip.compl₁₂ (actP lam B ∘ₗ (VV ℂ lam).subtype) T
  have hpr : ∀ w t, pr w t = pairB lam (T t) (actP lam B w.1) := fun _ _ => rfl
  refine ⟨pr, fun h0 => ?_, fun τ g hg (w : VV ℂ lam) v u hu => ?_⟩
  · have hv : ∀ τ, ∃ v : M.sm τ, (v : M.H τ) ≠ 0 := fun τ => by
      have := (M.ds τ).1
      have := (M.ds τ).2.1
      obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_smoothVec (M.ds τ).2.2.1 (M.fr_unit τ) (M.fr_gram τ)
      exact ⟨⟨v, Submodule.subset_span hs⟩, hv⟩
    choose v hv using hv
    refine GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => A τ (v τ)) (fun τ h => hv τ (h1 τ (h.trans (map_zero _).symm))) ?_
    refine congrArg Subtype.val ((pairingBNondegenerate_holds ℂ _ _ lam).1
      ⟨_, GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => h2 τ (v τ)⟩ fun y => ?_)
    have h4 : pr (rhoK lam B⁻¹ y) (PiTensorProduct.tprod ℂ v) = 0 := by
      rw [show pr = 0 from h0]
      rfl
    have h5 : rhoK lam B (rhoK lam B⁻¹ y) = y := by
      rw [rhoK_mul, mul_inv_cancel, rhoK_one]
    rw [hpr, hT, ← rhoK_coe, h5] at h4
    rw [pairBK_apply]
    exact h4
  · have ha : IsAtTau θ V τ g (atTau θ V τ g) := by
      have hex := (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ g hg).exists
      rw [atTau, dif_pos hex]
      exact hex.choose_spec
    set G := infGL θ V (atTau θ V τ g) with hGd
    let k := B * G * B⁻¹
    have hk : ∀ ρ, (k ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Matrix.unitaryGroup _ ℂ := fun ρ =>
      conj_unitary (by
        have := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (atTau θ V τ g) ρ
        rwa [← hG] at this)
    have hup : ∀ ρ, (Function.update v τ u ρ : M.H ρ) = M.σ ρ (k ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v ρ) := by
      intro ρ
      by_cases hρ : ρ = τ
      · subst hρ
        have e : (k ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = M.fr ρ * g * (M.fr ρ)⁻¹ := by
          show ((B ρ * G ρ * (B ρ)⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = _
          rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hB, infGL_coe, ha.2.1]
        rw [Function.update_self, hu, e]
        rfl
      · have e : k ρ = 1 := by
          have : G ρ = 1 := Units.ext (ha.2.2 ρ hρ)
          show B ρ * G ρ * (B ρ)⁻¹ = 1
          rw [this, mul_one, mul_inv_cancel]
        rw [Function.update_of_ne hρ, e, Units.val_one, (M.ds ρ).2.2.1.1.1]
        rfl
    have e1 : T (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
        actP lam (invTrK k) (T (PiTensorProduct.tprod ℂ v)) := by
      rw [hT, hT, actTen]
      congr 1
      funext ρ
      rw [hup, h3 ρ _ (hk ρ)]
      rfl
    have e2 : rhoK lam B (rhoK lam G w) = rhoK lam k (rhoK lam B w) := by
      rw [rhoK_mul, rhoK_mul, inv_mul_cancel_right]
    show pr (rhoK lam G w) _ = pr w _
    rw [hpr, hpr, ← rhoK_coe, e2, e1]
    exact pairingBInvariantK_holds ℂ _ _ lam k _ _

theorem exists_coef_dualPair : ∀ (D : D7) (θ : InfFam D) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), IsInfFam θ → ∃ (c : CoefA D.sp.X') (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (c0 : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] c.W) (g : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E), c.Is ∧ IsDualPair θ M c pr ∧ (g = D.sp.X'.gram ∨ g = -D.sp.X'.gram) ∧ Bridge.CoefMapTie D.sp.X' c.coef c0 (rhoV (labLL D) _) ∧ ∀ x y, inner ℂ (c0 x) (c0 y) = D.what₂.embLL (pairV (labLL D) _ g x y) := by
  intro D θ M hθ
  have hε : ∀ τ, M.ε τ = fun _ => true := fun τ => funext fun a => by
    obtain ⟨-, q, -, hS⟩ := M.enum τ
    exact sign_last (Ptw D) τ (x := (q a, M.ε τ a)) (hS ▸ Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  let B : D.what₂.Tau → GL (Fin D.sp.X'.rank) ℂ := fun τ => (M.fr_unit τ).unit
  have hG : ∀ τ, gramOf B τ = gramAt D D.sp.X' τ := fun τ => by
    rw [← M.fr_gram τ, hε]
    simp [gramOf, B, Formalism.REAL.Jm]
  have hds : ∀ τ, IsHCTypeU _ (M.lam τ) (M.σ τ) := fun τ =>
    (GlobalTheory.RealPar.isDS_const_iff true _ _).1 (hε τ ▸ M.ds τ)
  choose A h1 h2 h3 using fun τ => exists_dual_model (Bridge.lamRdef (Ptw D) τ) (M.lam τ)
    (enum_dual ((GlobalTheory.ForcedWeights.lam_forced D).1 τ) (M.enum τ)) (hds τ)
  obtain ⟨pr, hpr⟩ := coefA_dual (fun τ => Bridge.lamRdef (Ptw D) τ) B hθ M (fun _ => rfl) hG A h1 h2 h3
  exact ⟨coefA θ _ _ B, pr, bcVV D.what₂.embLL _, _, coefA_is _ B hθ hG, hpr, Or.inl rfl, coefA_tie _ B hθ,
    coefA_inner _ B hG⟩

end Global

end GlobalTheory.CoefSpace
