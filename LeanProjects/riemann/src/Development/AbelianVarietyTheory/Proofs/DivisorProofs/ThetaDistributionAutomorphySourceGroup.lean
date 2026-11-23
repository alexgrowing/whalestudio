import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualGOfGQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTargetStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DualSwap

variable {D : D7}

def trF {m n : ℕ} : (Mx D m n → ℂ) ≃ₗ[ℂ] (Mx D n m → ℂ) where
  toFun f x := f xᵀ
  invFun f x := f xᵀ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem trF_trF {m n : ℕ} (f : Mx D m n → ℂ) : trF (trF f) = f := rfl

theorem sum_sum_sum_sum_comm {M : Type} [AddCommMonoid M] {m n : ℕ} (F : Fin m → Fin m → Fin n → Fin n → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
  calc _ = ∑ b, ∑ a, ∑ d, ∑ c, F a b c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c, ∑ a, F a b c d := by
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

variable (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
  (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)

theorem hO_tr (x y : WO S T) : hO (dualSp T ΛT hT) (dualSp S ΛS hS) xᵀ yᵀ = hO S T x y := by
  unfold hO
  rw [dualSp_gram_inv, dualSp_gram, sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  simp only [Matrix.transpose_apply]
  ring

theorem symplOH_tr (x y : WO S T) : symplOH (dualSp T ΛT hT) (dualSp S ΛS hS) xᵀ yᵀ = symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_tr]

theorem trF_heis (w : WO (dualSp T ΛT hT) (dualSp S ΛS hS)) (f : WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ) :
    trF (heisO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) w f) = heisO ψ S T wᵀ (trF f) := by
  funext x
  change ψ (symplOH (dualSp T ΛT hT) (dualSp S ΛS hS) xᵀ wᵀᵀ) * f (xᵀ + w) = ψ (symplOH S T x wᵀ) * f (xᵀ + w)
  rw [symplOH_tr]

theorem trF_heis' (w : WO S T) (f : WO S T → ℂ) :
    trF (heisO ψ S T w f) = heisO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) wᵀ (trF f) := by
  funext x
  change ψ (symplOH S T xᵀ w) * f (xᵀ + w) = ψ (symplOH (dualSp T ΛT hT) (dualSp S ΛS hS) xᵀᵀ wᵀ) * f (xᵀ + w)
  rw [symplOH_tr]

def trA {m n : ℕ} : Mx D m n →+ Mx D n m where
  toFun x := xᵀ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_tr {m n : ℕ} : Continuous (fun x : Mx D m n => (xᵀ : Mx D n m)) := continuous_id.matrix_transpose

theorem theta_trF {f : WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ} (h : IsThetaFunO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) f) :
    IsThetaFunO ψ S T (trF f) where
  quasi γ w := by
    have := h.quasi γᵀ wᵀ
    rw [← symplOH_tr S T ΛS ΛT hS hT]
    exact this
  level := by
    obtain ⟨U, hU, hU'⟩ := h.level
    refine ⟨U.comap trA, hU.preimage continuous_tr, fun u hu hu' => ?_⟩
    have := congrArg trF (hU' uᵀ hu (congrArg Matrix.transpose hu'))
    rwa [trF_heis] at this
  cont := h.cont.comp continuous_tr
  smooth k L hL hL' w := h.smooth k (trA.comp L) (continuous_tr.comp hL) (fun t => congrArg Matrix.transpose (hL' t)) wᵀ

theorem theta_trF' {f : WO S T → ℂ} (h : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) (trF f) where
  quasi γ w := by
    have := h.quasi γᵀ wᵀ
    rw [← symplOH_tr S T ΛS ΛT hS hT] at this
    exact this
  level := by
    obtain ⟨U, hU, hU'⟩ := h.level
    refine ⟨U.comap trA, hU.preimage continuous_tr, fun u hu hu' => ?_⟩
    have := congrArg trF (hU' uᵀ hu (congrArg Matrix.transpose hu'))
    rwa [trF_heis' ψ S T ΛS ΛT hS hT] at this
  cont := h.cont.comp continuous_tr
  smooth k L hL hL' w := h.smooth k (trA.comp L) (continuous_tr.comp hL) (fun t => congrArg Matrix.transpose (hL' t)) wᵀ

theorem actO_tr (g : GA D (dualSp T ΛT hT)) (h : GA D (dualSp S ΛS hS)) (x : WO (dualSp T ΛT hT) (dualSp S ΛS hS)) :
    actO S T (dualG S ΛS hS h) (dualG T ΛT hT g) xᵀ = (actO (dualSp T ΛT hT) (dualSp S ΛS hS) g h x)ᵀ := by
  unfold actO
  rw [mt_dualG, mt_dualG_inv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]

def swapOm (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D (dualSp T ΛT hT) × GA D (dualSp S ΛS hS) →* Module.End ℂ (WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ) where
  toFun p := (trF : (WO S T → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ om (dualG S ΛS hS p.2, dualG T ΛT hT p.1) ∘ₗ
    (trF : _ ≃ₗ[ℂ] (WO S T → ℂ)).toLinearMap
  map_one' := by
    refine LinearMap.ext fun f => ?_
    have : ((dualG S ΛS hS 1, dualG T ΛT hT 1) : GA D S × GA D T) = 1 := by rw [map_one, map_one]; rfl
    change trF (om (dualG S ΛS hS 1, dualG T ΛT hT 1) (trF f)) = f
    rw [this, map_one]; rfl
  map_mul' p q := by
    refine LinearMap.ext fun f => ?_
    have : ((dualG S ΛS hS (p.2 * q.2), dualG T ΛT hT (p.1 * q.1)) : GA D S × GA D T) =
      (dualG S ΛS hS p.2, dualG T ΛT hT p.1) * (dualG S ΛS hS q.2, dualG T ΛT hT q.1) := by rw [map_mul, map_mul]; rfl
    change trF (om (dualG S ΛS hS (p.2 * q.2), dualG T ΛT hT (p.1 * q.1)) (trF f)) =
      trF (om (dualG S ΛS hS p.2, dualG T ΛT hT p.1) (om (dualG S ΛS hS q.2, dualG T ΛT hT q.1) (trF f)))
    rw [this, map_mul]; rfl

theorem swapOm_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D (dualSp T ΛT hT))
    (h : GA D (dualSp S ΛS hS)) (f : WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ) :
    swapOm S T ΛS ΛT hS hT om (g, h) f = trF (om (dualG S ΛS hS h, dualG T ΛT hT g) (trF f)) := rfl

theorem swap_unitary {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (h : IsUnitaryOnTheta ψ S T om) :
    IsUnitaryOnTheta ψ (dualSp T ΛT hT) (dualSp S ΛS hS) (swapOm S T ΛS ΛT hS hT om) where
  pres p f hf := theta_trF' ψ S T ΛS ΛT hS hT (h.pres _ _ (theta_trF ψ S T ΛS ΛT hS hT hf))
  cont f hf w := (h.cont _ (theta_trF ψ S T ΛS ΛT hS hT hf) wᵀ).comp
    (((continuous_dualG S ΛS hS).comp continuous_snd).prodMk ((continuous_dualG T ΛT hT).comp continuous_fst))
  unit μ 𝓕 hμ h𝓕 p f hf := by
    have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
    have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    have : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
    have : IsTopologicalAddGroup (WO (dualSp T ΛT hT) (dualSp S ΛS hS)) := Pi.topologicalAddGroup
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : BorelSpace (WO (dualSp T ΛT hT) (dualSp S ΛS hS)) := ⟨rfl⟩
    let e : WO (dualSp T ΛT hT) (dualSp S ΛS hS) ≃ₜ+ WO S T :=
      { toFun := fun x => xᵀ, invFun := fun x => xᵀ, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, continuous_toFun := continuous_tr, continuous_invFun := continuous_tr }
    let m : WO (dualSp T ΛT hT) (dualSp S ΛS hS) ≃ᵐ WO S T := e.toHomeomorph.toMeasurableEquiv
    have hH : (μ.map m).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
    have hp : MeasurePreserving m.symm (μ.map m) μ := (m.measurable.measurePreserving μ).symm m
    have hF : IsAddFundamentalDomain (ratL T S) (m.symm ⁻¹' 𝓕) (μ.map m) := by
      refine h𝓕.preimage_of_equiv hp.quasiMeasurePreserving
        (e := fun γ => (⟨γ.1ᵀ, by obtain ⟨γ, δ, rfl⟩ := γ; exact ⟨δᵀ, rfl⟩⟩ : ratL T S)) ?_ fun γ x => rfl
      constructor
      · intro a b hab
        exact Subtype.ext (congrArg Matrix.transpose (congrArg Subtype.val hab))
      · rintro ⟨_, δ, rfl⟩
        exact ⟨⟨_, δᵀ, rfl⟩, rfl⟩
    have key := h.unit (μ.map m) _ hH hF (dualG S ΛS hS p.2, dualG T ΛT hT p.1) _ (theta_trF ψ S T ΛS ΛT hS hT hf)
    have e1 := hp.setLIntegral_comp_preimage_emb m.symm.measurableEmbedding
      (fun w => ‖swapOm S T ΛS ΛT hS hT om p f w‖ₑ ^ 2) 𝓕
    have e2 := hp.setLIntegral_comp_preimage_emb m.symm.measurableEmbedding (fun w => ‖f w‖ₑ ^ 2) 𝓕
    exact e1.symm.trans (key.trans e2)

theorem supp_inv {A : Type} [CommRing A] {n : ℕ} (ε : A) (g : GL (Fin n) A)
    (h : ∀ i j, ε * ((g : Matrix (Fin n) (Fin n) A) - 1) i j = ((g : Matrix (Fin n) (Fin n) A) - 1) i j) (i j : Fin n) :
    ε * (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ - 1) i j =
      (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ - 1) i j := by
  have h1 : ε • ((g : Matrix (Fin n) (Fin n) A) - 1) = (g : Matrix (Fin n) (Fin n) A) - 1 := Matrix.ext h
  have h2 : ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 =
      -(((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * ((g : Matrix (Fin n) (Fin n) A) - 1)) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, neg_sub]
  have h3 : ε • (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) =
      ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 := by
    rw [h2, smul_neg, ← Matrix.mul_smul, h1]
  have h4 := congrArg Matrix.transpose h3
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one] at h4
  exact congrFun (congrFun h4 i) j

theorem det_inv_at {A : Type} [CommRing A] {n : ℕ} {e : A} (he : e * e = e) (g : GL (Fin n) A) (x : Aˣ)
    (h : (x : A) = e * (g : Matrix (Fin n) (Fin n) A).det + (1 - e)) :
    ((x⁻¹ : Aˣ) : A) = e * (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ).det + (1 - e) := by
  have h1 : (g : Matrix (Fin n) (Fin n) A).det * ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [h, Matrix.det_transpose]
  generalize (g : Matrix (Fin n) (Fin n) A).det = a at h1
  generalize ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).det = b at h1
  linear_combination (e * e) * h1 + (2 - a - b) * he

theorem mem_latO_tr (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO (dualSp T ΛT hT) (dualSp S ΛS hS)) :
    u ∈ latO (dualSp T ΛT hT) (dualSp S ΛS hS) (formLat T.gram ΛT) (formLat S.gram ΛS) P ↔
      (uᵀ : WO S T) ∈ latO S T ΛS ΛT P := by
  have key : ∀ (t : Fin T.rank → D.host.E) (j : Fin T.rank),
      ∑ k, star ((star t ᵥ* T.gram) k) * (dualSp T ΛT hT).gram k j = t j := by
    intro t j
    have : star (star t ᵥ* T.gram) ᵥ* (dualSp T ΛT hT).gram = t := by
      rw [dualSp_gram, Matrix.vecMul_transpose, Matrix.star_vecMul, star_star, gram_herm, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit T), Matrix.one_mulVec]
    exact congrFun this j
  constructor
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, _, ⟨t, ht, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, Matrix.ext fun i j => ?_⟩
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      rw [key, mul_right_comm]
      rfl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hu
    have : ∀ w ∈ latO S T ΛS ΛT P,
        (wᵀ : WO (dualSp T ΛT hT) (dualSp S ΛS hS)) ∈
          latO (dualSp T ΛT hT) (dualSp S ΛS hS) (formLat T.gram ΛT) (formLat S.gram ΛS) P := by
      intro w hw
      induction hw using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
        refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, _, ⟨t, ht, rfl⟩, _, ⟨s, hs, rfl⟩, Matrix.ext fun i j => ?_⟩
        simp only [Matrix.transpose_apply, Matrix.of_apply]
        rw [key, mul_right_comm]
        rfl
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx
    exact this _ hu

theorem swap_fin {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (h : IsFinWeil ψ S T ΛS ΛT χS χT om) :
    IsFinWeil ψ (dualSp T ΛT hT) (dualSp S ΛS hS) (formLat T.gram ΛT) (formLat S.gram ΛS) χT χS
      (swapOm S T ΛS ΛT hS hT om) where
  toIsUnitaryOnTheta := swap_unitary ψ S T ΛS ΛT hS hT h.toIsUnitaryOnTheta
  triv g hg k hk f hf := by
    rw [swapOm_apply, h.triv _ (dualG_mem_GinfC S ΛS hS hk) _ (dualG_mem_GinfC T ΛT hT hg) _
      (theta_trF ψ S T ΛS ΛT hS hT hf), trF_trF]
  Heisenberg₂ g hg k hk w f hf := by
    rw [swapOm_apply, swapOm_apply, trF_heis, h.Heisenberg₂ _ (dualG_mem_GfC S ΛS hS hk) _ (dualG_mem_GfC T ΛT hT hg) _ _
      (theta_trF ψ S T ΛS ΛT hS hT hf), trF_heis' ψ S T ΛS ΛT hS hT, actO_tr, Matrix.transpose_transpose]
  split e he g k hg hk x y hx hy := by
    obtain ⟨r, hr, H⟩ := h.split e he (dualG S ΛS hS k) (dualG T ΛT hT g)
      (supp_inv _ (matHom (dualSp S ΛS hS) k) hk) (supp_inv _ (matHom (dualSp T ΛT hT) g) hg) y⁻¹ x⁻¹
      (det_inv_at he.1 (matHom (dualSp S ΛS hS) k) y hy) (det_inv_at he.1 (matHom (dualSp T ΛT hT) g) x hx)
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have := H (ℓ ∘ₗ (trF : (WO S T → ℂ) ≃ₗ[ℂ] _).toLinearMap) (fun u hu f hf => by
      change ℓ (trF (heisO ψ S T u f)) = ℓ (trF f)
      rw [trF_heis' ψ S T ΛS ΛT hS hT]
      exact hℓ _ (fun i j => hu j i) _ (theta_trF' ψ S T ΛS ΛT hS hT hf)) _ (theta_trF ψ S T ΛS ΛT hS hT hf)
    have e1 : splitFacO χS χT y⁻¹ x⁻¹ = splitFacO χT χS x y := by
      rw [splitFacO, splitFacO, map_inv, map_inv, inv_inv, mul_comm]
    rw [e1] at this
    exact this
  inert v ε hv g k hg hk hL f hf hfix := by
    have := h.inert v ε hv (dualG S ΛS hS k) (dualG T ΛT hT g)
      (supp_inv _ (matHom (dualSp S ΛS hS) k) hk) (supp_inv _ (matHom (dualSp T ΛT hT) g) hg)
      (fun u => by
        have h1 := hL uᵀ
        rw [mem_latO_tr, mem_latO_tr, ← actO_tr] at h1
        exact h1)
      _ (theta_trF ψ S T ΛS ΛT hS hT hf) (fun u hu => by
        have h1 := congrArg trF (hfix uᵀ ((mem_latO_tr S T ΛS ΛT hS hT _ _).2 hu))
        rw [trF_heis] at h1
        exact h1)
    rw [swapOm_apply, this, trF_trF]

theorem cartan_tr {k : ℕ} {G G' s : Matrix (Fin k) (Fin k) ℂ} (hG : G'ᵀ * G = 1) (h : IsCartanInv G' s) :
    IsCartanInv G sᵀ := by
  obtain ⟨h1, h2, h3⟩ := h
  have hG' : G * G'ᵀ = 1 := mul_eq_one_comm.1 hG
  have e1 : sᵀ * sᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have e2 : sᵀᴴ * sᵀᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have e3 : sᵀ * G'ᵀ * sᵀᴴ = G'ᵀ := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc] at this
    exact this
  refine ⟨e1, ?_, ?_⟩
  · have e4 : sᵀᴴ * G * sᵀ * G'ᵀ = 1 := by
      rw [← e3]
      calc _ = sᵀᴴ * (G * (sᵀ * sᵀ) * G'ᵀ) * sᵀᴴ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e1, Matrix.mul_one, hG', Matrix.mul_one, e2]
    calc _ = sᵀᴴ * G * sᵀ * G'ᵀ * G := by rw [Matrix.mul_assoc _ G'ᵀ, hG, Matrix.mul_one]
      _ = G := by rw [e4, Matrix.one_mul]
  · have e5 : ((G' * s)ᵀ)⁻¹ = G * sᵀ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.transpose_mul]
      calc _ = G * (sᵀ * sᵀ) * G'ᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e1, Matrix.mul_one, hG']
    rw [← e5]
    exact h3.transpose.inv

theorem detPlus_tr {m n : ℕ} (sS a : Matrix (Fin n) (Fin n) ℂ) (sT b : Matrix (Fin m) (Fin m) ℂ) :
    detPlus sTᵀ sSᵀ bᵀ aᵀ = detPlus sS sT a b := by
  unfold detPlus
  have hk : ∀ (x : Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin m) (Fin m) ℂ),
      Matrix.kroneckerMap (· * ·) x y =
        (Matrix.kroneckerMap (· * ·) y x).submatrix (Equiv.prodComm (Fin n) (Fin m)) (Equiv.prodComm (Fin n) (Fin m)) :=
    fun x y => Matrix.ext fun _ _ => mul_comm _ _
  rw [← Matrix.det_submatrix_equiv_self (Equiv.prodComm (Fin n) (Fin m)) (_ + _), hk sSᵀ, hk aᵀ,
    ← Matrix.submatrix_one_equiv (Equiv.prodComm (Fin n) (Fin m))]
  congr 1
  exact congrArg₂ (· + ·) (congrArg ((1 / 2 : ℂ) • ·) (Matrix.submatrix_mul_equiv
    (1 + Matrix.kroneckerMap (· * ·) sT sSᵀ) (Matrix.kroneckerMap (· * ·) b aᵀ) _ (Equiv.prodComm (Fin n) (Fin m)) _)) rfl

theorem lineAt_tr {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ zᵀ t = (lineAt θ τ z t)ᵀ := by
  have h1 : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec ((GlobalTheory.RealLineAt.lineAt_exists_unique D).1 θ hθ m n τ z)
  have h2 : IsLineAt θ τ zᵀ (lineAt θ τ zᵀ) :=
    Classical.epsilon_spec ((GlobalTheory.RealLineAt.lineAt_exists_unique D).1 θ hθ n m τ zᵀ)
  have h3 : IsLineAt θ τ zᵀ (trA.comp (lineAt θ τ z)) := by
    refine ⟨continuous_tr.comp h1.1, fun t => congrArg Matrix.transpose (h1.2.1 t), fun t τ' => ?_⟩
    have := congrArg Matrix.transpose (h1.2.2 t τ')
    refine Eq.trans this ?_
    split_ifs <;> rfl
  rw [(GlobalTheory.RealLineAt.lineAt_exists_unique D).2 θ hθ n m τ zᵀ _ _ h2 h3]
  rfl

theorem dRho_tr {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (f : WO (dualSp T ΛT hT) (dualSp S ΛS hS) → ℂ) :
    dRho (heisO ψ S T) θ τ z (trF f) = trF (dRho (heisO ψ (dualSp T ΛT hT) (dualSp S ΛS hS)) θ τ zᵀ f) := by
  funext x
  change deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (trF f) x) 0 =
    deriv (fun t : ℝ => trF (heisO ψ (dualSp T ΛT hT) (dualSp S ΛS hS) (lineAt θ τ zᵀ t) f) x) 0
  congr 1
  funext t
  rw [trF_heis, lineAt_tr hθ, Matrix.transpose_transpose]

theorem swap_inf {θ : InfFam D} (hθ : IsInfFam θ) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (h : IsInfWeil ψ θ S T om) :
    IsInfWeil ψ θ (dualSp T ΛT hT) (dualSp S ΛS hS) (swapOm S T ΛS ΛT hS hT om) where
  toIsUnitaryOnTheta := swap_unitary ψ S T ΛS ΛT hS hT h.toIsUnitaryOnTheta
  triv g hg k hk f hf := by
    rw [swapOm_apply, h.triv _ (dualG_mem_GfC S ΛS hS hk) _ (dualG_mem_GfC T ΛT hT hg) _
      (theta_trF ψ S T ΛS ΛT hS hT hf), trF_trF]
  Heisenberg₂ g hg k hk w f hf := by
    rw [swapOm_apply, swapOm_apply, trF_heis, h.Heisenberg₂ _ (dualG_mem_GinfC S ΛS hS hk) _ (dualG_mem_GinfC T ΛT hT hg) _ _
      (theta_trF ψ S T ΛS ΛT hS hT hf), trF_heis' ψ S T ΛS ΛT hS hT, actO_tr, Matrix.transpose_transpose]
  vac sT sS hsT hsS g hg k hk cg ck f hf hv := by
    have gS : ∀ τ, (gramAt D (dualSp S ΛS hS) τ)ᵀ * gramAt D S τ = 1 := fun τ => by
      rw [gramAt, gramAt, ← Matrix.transpose_map, ← Matrix.map_mul, gram_dual_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have gT : ∀ τ, (gramAt D (dualSp T ΛT hT) τ)ᵀ * gramAt D T τ = 1 := fun τ => by
      rw [gramAt, gramAt, ← Matrix.transpose_map, ← Matrix.map_mul, gram_dual_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have comm : ∀ (V : HSp D) (τ : D.what₂.Tau) (s : Matrix (Fin V.rank) (Fin V.rank) ℂ) (a : GA D V),
        s * compAt θ τ (Formalism.L2.Theta.mt V a) = compAt θ τ (Formalism.L2.Theta.mt V a) * s →
        sᵀ * (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹))ᵀ = (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹))ᵀ * sᵀ := by
      intro V τ s a ha
      let u : GL (Fin V.rank) ℂ := Formalism.UG.bc ((θ τ).comp (infPart D)) (matHom V a)
      have hc : Commute s (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) := ha
      have hc' : s * ((u⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = _ := hc.units_inv_right
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
      exact congrArg Matrix.transpose hc'.symm
    have := h.vac (fun τ => (sS τ)ᵀ) (fun τ => (sT τ)ᵀ) (fun τ => cartan_tr (gS τ) (hsS τ))
      (fun τ => cartan_tr (gT τ) (hsT τ)) _ (dualG_mem_GinfC S ΛS hS hk) _ (dualG_mem_GinfC T ΛT hT hg)
      (fun τ => comm (dualSp S ΛS hS) τ (sS τ) k (ck τ)) (fun τ => comm (dualSp T ΛT hT) τ (sT τ) g (cg τ))
      _ (theta_trF ψ S T ΛS ΛT hS hT hf) (fun τ z => by
        have h1 := congrArg trF (hv τ zᵀ)
        have h2 : (cplxO (sS τ)ᵀ (sT τ)ᵀ z)ᵀ = cplxO (sT τ) (sS τ) zᵀ := by
          rw [cplxO, cplxO, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
            Matrix.transpose_transpose, Matrix.mul_assoc]
        rw [annih, map_add, map_smul, map_zero] at h1
        rw [annih, dRho_tr ψ S T ΛS ΛT hS hT hθ, dRho_tr ψ S T ΛS ΛT hS hT hθ, h2]
        exact h1)
    rw [swapOm_apply, this, map_smul, trF_trF]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => detPlus_tr (sT τ) _ (sS τ) _

theorem automorphy_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∀ (of oi : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of → IsInfWeil ψ θ S T oi → ∀ γ ∈ GQ S, ∀ f, IsThetaFunO ψ S T f → of (γ, 1) (oi (γ, 1) f) 0 = f 0 := by
  intro D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ hγ f hth
  obtain ⟨γ', hγ', rfl⟩ := exists_dualG_of_GQ S ΛS hS hγ
  have := GlobalTheory.T.thetaDistribution_invariant_rationalTarget D ψ hψ (dualSp T ΛT hT) (dualSp S ΛS hS) θ hθ _ _ (dualSp_selfDual T ΛT hT)
    (dualSp_selfDual S ΛS hS) η hη _ _ (swap_fin ψ S T ΛS ΛT hS hT hf) (swap_inf ψ S T ΛS ΛT hS hT hθ hi) γ' hγ' _
    (theta_trF' ψ S T ΛS ΛT hS hT hth)
  rw [swapOm_apply, swapOm_apply, map_one] at this
  exact this

end GlobalTheory.DualSwap

end
