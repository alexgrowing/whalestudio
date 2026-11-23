import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatLinearFunctional

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LagrInvForm

open MeasureTheory

def symp (k : Type) [Field k] (κ : Type) [Fintype κ] : LinearMap.BilinForm k ((κ → k) × (κ → k)) :=
  LinearMap.mk₂ k (fun a b => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
    (fun a a' b => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    (fun a b b' => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)

theorem symp_apply {k : Type} [Field k] {κ : Type} [Fintype κ] (a b : (κ → k) × (κ → k)) :
    symp k κ a b = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := rfl

theorem symp_nondeg (k : Type) [Field k] (κ : Type) [Fintype κ] : (symp k κ).Nondegenerate := by
  classical
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · ext i
    · simpa [symp_apply] using hm (0, Pi.single i 1)
    · simpa [symp_apply] using hm (Pi.single i 1, 0)
  · ext i
    · simpa [symp_apply] using hm (0, Pi.single i 1)
    · simpa [symp_apply] using hm (Pi.single i 1, 0)

theorem mem_of_orth {k : Type} [Field k] {κ : Type} [Fintype κ] (Λ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hdim : Module.finrank k Λ = Fintype.card κ)
    (w : (κ → k) × (κ → k)) (hw : ∀ a ∈ Λ, a.1 ⬝ᵥ w.2 = w.1 ⬝ᵥ a.2) : w ∈ Λ := by
  have hnd := symp_nondeg k κ
  have hle : Λ ≤ (symp k κ).orthogonal Λ := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [symp_apply, hiso n hn x hx, sub_self]
  have hdim' : Module.finrank k Λ = Module.finrank k ((symp k κ).orthogonal Λ) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, hdim]
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle hdim'
  rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  rw [symp_apply, hw n hn, sub_self]

theorem exists_coord {k : Type} [Field k] {κ : Type} [Fintype κ] (Λ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hdim : Module.finrank k Λ = Fintype.card κ) :
    ∃ (n m : ℕ) (e : ((Fin n → k) × (Fin m → k)) ≃ₗ[k] (κ → k)) (s : (Fin m → k) →ₗ[k] (κ → k)),
      (∀ a, (e (0, a), s a) ∈ Λ) ∧
      ∀ b : Fin n → k, ∃ b' : κ → k, (0, b') ∈ Λ ∧ ∀ x, x ⬝ᵥ b' = b ⬝ᵥ (e.symm x).1 := by
  classical
  let π : Λ →ₗ[k] (κ → k) := (LinearMap.fst k (κ → k) (κ → k)).comp Λ.subtype
  let P := LinearMap.range π
  obtain ⟨Q, hPQ⟩ := Submodule.exists_isCompl P
  let bQ := Module.finBasis k Q
  let bP := Module.finBasis k P
  let e : ((Fin (Module.finrank k Q) → k) × (Fin (Module.finrank k P) → k)) ≃ₗ[k] (κ → k) :=
    ((LinearEquiv.prodCongr bQ.equivFun.symm bP.equivFun.symm).trans (LinearEquiv.prodComm k Q P)).trans
      (Submodule.prodEquivOfIsCompl P Q hPQ)
  have he : ∀ a, e (0, a) = (bP.equivFun.symm a : κ → k) := fun a => by
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  obtain ⟨σ, hσ⟩ := π.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict π)
  let s : (Fin (Module.finrank k P) → k) →ₗ[k] (κ → k) :=
    (LinearMap.snd k (κ → k) (κ → k)).comp (Λ.subtype.comp (σ.comp bP.equivFun.symm.toLinearMap))
  refine ⟨_, _, e, s, fun a => ?_, fun b => ?_⟩
  · have h1 : π.rangeRestrict (σ (bP.equivFun.symm a)) = bP.equivFun.symm a := by
      rw [← LinearMap.comp_apply, hσ, LinearMap.id_apply]
    have h2 : ((σ (bP.equivFun.symm a) : Λ) : (κ → k) × (κ → k)).1 = (bP.equivFun.symm a : κ → k) :=
      congrArg Subtype.val h1
    have h3 : (e (0, a), s a) = ((σ (bP.equivFun.symm a) : Λ) : (κ → k) × (κ → k)) := by
      refine Prod.ext ?_ rfl
      rw [he, h2]
    rw [h3]
    exact (σ (bP.equivFun.symm a)).2
  · let f : (κ → k) →ₗ[k] k :=
      { toFun := fun x => b ⬝ᵥ (e.symm x).1
        map_add' := fun x y => by simp [dotProduct_add]
        map_smul' := fun c x => by simp [dotProduct_smul] }
    let b' : κ → k := fun i => f (fun j => if i = j then 1 else 0)
    have hx : ∀ x, x ⬝ᵥ b' = f x := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      simp only [dotProduct, smul_eq_mul]
      try rfl
    refine ⟨b', ?_, fun x => hx x⟩
    apply mem_of_orth Λ hiso hdim
    intro a ha
    simp only [zero_dotProduct]
    rw [hx]
    have hp : a.1 ∈ P := ⟨⟨a, ha⟩, rfl⟩
    have h4 : e.symm a.1 = (0, bP.equivFun ⟨a.1, hp⟩) := by
      rw [LinearEquiv.symm_apply_eq, he]
      simp
    show b ⬝ᵥ (e.symm a.1).1 = 0
    rw [h4]
    simp

private theorem lc_lemma {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hU : {h : k | ‖ψ h - 1‖ < 1 / 2} ∈ nhds (0 : k) := by
    have hc : Continuous fun h => ‖ψ h - 1‖ := by fun_prop
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff.mp hU
  have hsub : ∀ z, ValuativeRel.valuation k z < γ → ‖ψ z - 1‖ < 1 / 2 := fun z hz => by
    have := hγ ⟨z, hz, zero_add z⟩
    exact this
  have hnsm : ∀ z, ValuativeRel.valuation k z < γ → ∀ n : ℕ, ValuativeRel.valuation k (n • z) < γ := by
    intro z hz n
    induction n with
    | zero =>
      rw [zero_smul, map_zero]
      exact zero_lt_iff.mpr γ.ne_zero
    | succ n ih =>
      rw [succ_nsmul]
      exact (ValuativeRel.valuation k).map_add_lt ih hz
  have hker : ∀ h, ValuativeRel.valuation k h < γ → ψ h = 1 := by
    intro h hh
    by_contra hne
    have hn : ∀ n : ℕ, ‖ψ h ^ n - 1‖ < 1 / 2 := fun n => by
      have := hsub _ (hnsm h hh n)
      rwa [AddChar.map_nsmul_eq_pow] at this
    have hz : ‖ψ h‖ = 1 := GlobalTheory.norm_addChar_nonarch ψ hψ h
    have hd : 0 < ‖ψ h - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖ψ h - 1‖)
    have hNpos : 0 < N := by
      have : (0:ℝ) < N := lt_trans (by positivity) hN
      exact_mod_cast this
    have hre : ∀ i : ℕ, (1:ℝ) / 2 < (ψ h ^ i).re := fun i => by
      have h1 := hn i
      have h2 := Complex.abs_re_le_norm (ψ h ^ i - 1)
      have h3 : (ψ h ^ i - 1).re = (ψ h ^ i).re - 1 := by simp
      rw [h3] at h2
      have h4 := (abs_le.mp h2).1
      linarith
    have hsum_re : (N:ℝ) / 2 < (∑ i ∈ Finset.range N, ψ h ^ i).re := by
      rw [Complex.re_sum]
      have := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hNpos.ne') (fun i _ => hre i)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      linarith
    have hbound : ‖∑ i ∈ Finset.range N, ψ h ^ i‖ ≤ 2 / ‖ψ h - 1‖ := by
      rw [geom_sum_eq hne N, norm_div]
      gcongr
      calc ‖ψ h ^ N - 1‖ ≤ ‖ψ h ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz]; norm_num
    have hre_le := Complex.re_le_norm (∑ i ∈ Finset.range N, ψ h ^ i)
    have e1 : 2 / ‖ψ h - 1‖ = (4 / ‖ψ h - 1‖) / 2 := by ring
    linarith
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  apply IsValuativeTopology.mem_nhds_iff.mpr
  refine ⟨γ, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  show ψ (x + z) = ψ x
  rw [AddChar.map_add_eq_mul, hker z hz, mul_one]

private theorem isLocallyConstant_hasCompactSupport_comp_linearEquiv {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {A B : Type} [AddCommGroup A] [Module k A] [TopologicalSpace A] [IsModuleTopology k A]
    [ContinuousAdd A] [ContinuousSMul k A]
    [AddCommGroup B] [Module k B] [TopologicalSpace B] [IsModuleTopology k B] [ContinuousAdd B] [ContinuousSMul k B]
    (G : A ≃ₗ[k] B) (φ : B → ℂ) (hφ : IsLocallyConstant φ ∧ HasCompactSupport φ) :
    IsLocallyConstant (fun a => φ (G a)) ∧ HasCompactSupport (fun a => φ (G a)) := by
  have h1 : Continuous G := IsModuleTopology.continuous_of_linearMap G.toLinearMap
  have h2 : Continuous G.symm := IsModuleTopology.continuous_of_linearMap G.symm.toLinearMap
  let H : A ≃ₜ B := { toEquiv := G.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact ⟨hφ.1.comp_continuous h1, hφ.2.comp_homeomorph H⟩

private theorem isLocallyConstant_hasCompactSupport_mul_left {A : Type} [TopologicalSpace A] (g : A → ℂ) (hg : IsLocallyConstant g) (φ : A → ℂ)
    (hφ : IsLocallyConstant φ ∧ HasCompactSupport φ) :
    IsLocallyConstant (fun a => g a * φ a) ∧ HasCompactSupport (fun a => g a * φ a) :=
  ⟨hg.mul hφ.1, hφ.2.mul_left⟩

private theorem isLocallyConstant_hasCompactSupport_schr {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Invertible (2 : k)]
    (ψ : AddChar k ℂ) (hψ : IsLocallyConstant ψ) {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k))
    (φ : (κ → k) → ℂ) (hφ : IsLocallyConstant φ ∧ HasCompactSupport φ) :
    IsLocallyConstant (schr ψ w φ) ∧ HasCompactSupport (schr ψ w φ) := by
  have hg : Continuous fun x : κ → k => x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2) :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  exact isLocallyConstant_hasCompactSupport_mul_left _ (hψ.comp_continuous hg) _
    ⟨hφ.1.comp_continuous (continuous_id.add continuous_const), hφ.2.comp_homeomorph (Homeomorph.addRight w.1)⟩

theorem proportional (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Invertible (2 : k)] (ψ : AddChar k ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (Λ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hdim : Module.finrank k Λ = Fintype.card κ)
    (l₁ l₂ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (h₁ : ∀ w ∈ Λ, ∀ φ ∈ SB (κ → k), l₁ (schr ψ w φ) = l₁ φ)
    (h₂ : ∀ w ∈ Λ, ∀ φ ∈ SB (κ → k), l₂ (schr ψ w φ) = l₂ φ)
    (hne : ∃ φ ∈ SB (κ → k), l₂ φ ≠ 0) : ∃ c : ℂ, ∀ φ ∈ SB (κ → k), l₁ φ = c * l₂ φ := by
  classical
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨n, m, e, s, hs, hb⟩ := exists_coord Λ hiso hdim
  have hlc : IsLocallyConstant ψ := lc_lemma ψ hψ
  have hn1 : ∀ t, ‖ψ t‖ = 1 := GlobalTheory.norm_addChar_nonarch ψ hψ
  have hce : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hcs : Continuous s := IsModuleTopology.continuous_of_linearMap s
  let q : (Fin m → k) → k := fun z => ⅟(2 : k) * (e (0, z) ⬝ᵥ s z)
  have hq : Continuous q :=
    continuous_const.mul ((hce.comp (continuous_const.prodMk continuous_id)).dotProduct hcs)
  have hsym : ∀ z a, e (0, a) ⬝ᵥ s z = e (0, z) ⬝ᵥ s a := fun z a => hiso _ (hs a) _ (hs z)
  let G : (κ → k) ≃ₗ[k] ((Fin 0 → k) × (Fin n → k) × (Fin m → k)) :=
    (LinearEquiv.uniqueProd.trans e).symm
  have hGe : ∀ p, G (e p) = (0, p) := fun p => by
    rw [LinearEquiv.symm_apply_eq]
    simp [LinearEquiv.uniqueProd]
  let Tinv : (((Fin 0 → k) × (Fin n → k) × (Fin m → k)) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) :=
    { toFun := fun Φ x => ψ (-q (e.symm x).2) * Φ (G x)
      map_add' := fun Φ Ψ => by funext x; simp [mul_add]
      map_smul' := fun c Φ => by funext x; simp; ring }
  let Tf : ((κ → k) → ℂ) → (((Fin 0 → k) × (Fin n → k) × (Fin m → k)) → ℂ) :=
    fun φ p => ψ (q p.2.2) * φ (G.symm p)
  have hTT : ∀ φ, Tinv (Tf φ) = φ := fun φ => by
    funext x
    obtain ⟨p, rfl⟩ := e.surjective x
    simp only [Tinv, Tf, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, hGe]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
    congr 1
  have hTf : ∀ φ ∈ SB (κ → k), Tf φ ∈ GlobalTheory.SplitWeil.SB ((Fin 0 → k) × (Fin n → k) × (Fin m → k)) :=
    fun φ hφ => isLocallyConstant_hasCompactSupport_mul_left (fun p : (Fin 0 → k) × (Fin n → k) × (Fin m → k) => ψ (q p.2.2))
      (hlc.comp_continuous (hq.comp (continuous_snd.comp continuous_snd))) _ (isLocallyConstant_hasCompactSupport_comp_linearEquiv G.symm φ hφ)
  have hTinv : ∀ Φ ∈ GlobalTheory.SplitWeil.SB ((Fin 0 → k) × (Fin n → k) × (Fin m → k)), Tinv Φ ∈ SB (κ → k) :=
    fun Φ hΦ => isLocallyConstant_hasCompactSupport_mul_left (fun x : κ → k => ψ (-q (e.symm x).2))
      (hlc.comp_continuous (hq.comp (continuous_snd.comp
        (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap))).neg) _ (isLocallyConstant_hasCompactSupport_comp_linearEquiv G Φ hΦ)
  let ψc : AddChar k Circle :=
    { toFun := fun t => (⟨ψ t, by
        show ψ t ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm]; exact hn1 t⟩ : Submonoid.unitSphere ℂ)
      map_zero_eq_one' := Subtype.ext (by show ψ 0 = 1; exact AddChar.map_zero_eq_one ψ)
      map_add_eq_mul' := fun a b => Subtype.ext (by show ψ (a + b) = ψ a * ψ b; exact AddChar.map_add_eq_mul ψ a b) }
  have hψc : ∀ t, (ψc t : ℂ) = ψ t := fun t => rfl
  have hψcc : Continuous ψc := Continuous.subtype_mk hψ _
  have hψc1 : ψc ≠ 1 := by
    intro h
    apply hψ1
    ext t
    have := congrArg (fun c : AddChar k Circle => (c t : ℂ)) h
    simpa [hψc] using this
  let ν : Measure k := Measure.addHaar
  have key : ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ SB (κ → k), l φ = c * ∫ a, Tf φ (0, 0, a) ∂(Measure.pi fun _ => ν) := by
    intro l hl
    let L : GlobalTheory.SplitWeil.SB ((Fin 0 → k) × (Fin n → k) × (Fin m → k)) →ₗ[ℂ] ℂ :=
      (l.comp Tinv).comp (GlobalTheory.SplitWeil.SB _).subtype
    have hc1 : ∀ (b : Fin n → k) (Φ Φ' : GlobalTheory.SplitWeil.SB ((Fin 0 → k) × (Fin n → k) × (Fin m → k))),
        (∀ x, Φ'.1 x = (ψc (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → L Φ' = L Φ := by
      intro b Φ Φ' hΦ
      obtain ⟨b', hb'Λ, hb'⟩ := hb b
      have hmem := hTinv Φ.1 Φ.2
      have h1 : Tinv Φ'.1 = schr ψ (0, b') (Tinv Φ.1) := by
        funext x
        show ψ (-q (e.symm x).2) * Φ'.1 (G x) = ψ (x ⬝ᵥ b' + ⅟(2 : k) * ((0 : κ → k) ⬝ᵥ b')) *
          (ψ (-q (e.symm (x + 0)).2) * Φ.1 (G (x + 0)))
        rw [hΦ, hψc, add_zero, zero_dotProduct, mul_zero, add_zero, hb' x]
        obtain ⟨p, rfl⟩ := e.surjective x
        rw [hGe, LinearEquiv.symm_apply_apply]
        dsimp only
        ring
      show l (Tinv Φ'.1) = l (Tinv Φ.1)
      rw [h1]
      exact hl _ hb'Λ _ hmem
    have hc2 : ∀ (a : Fin m → k) (Φ Φ' : GlobalTheory.SplitWeil.SB ((Fin 0 → k) × (Fin n → k) × (Fin m → k))),
        (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → L Φ' = L Φ := by
      intro a Φ Φ' hΦ
      let f' : (Fin n → k) →ₗ[k] k :=
        { toFun := fun y => e (y, 0) ⬝ᵥ s a
          map_add' := fun y y' => by
            rw [← add_dotProduct, ← map_add, Prod.mk_add_mk, add_zero]
          map_smul' := fun c y => by
            simp only [RingHom.id_apply, smul_eq_mul]
            rw [← smul_eq_mul, ← smul_dotProduct, ← map_smul, Prod.smul_mk, smul_zero] }
      let β : Fin n → k := fun i => f' (fun j => if i = j then 1 else 0)
      have hβ : ∀ y, β ⬝ᵥ y = e (y, 0) ⬝ᵥ s a := fun y => by
        have h0 := LinearMap.pi_apply_eq_sum_univ f' y
        rw [dotProduct_comm]
        show ∑ i, y i * β i = f' y
        rw [h0]
        simp only [smul_eq_mul]
        try rfl
      obtain ⟨b', hb'Λ, hb'⟩ := hb (-β)
      have hmem := hTinv Φ.1 Φ.2
      have hmem2 : schr ψ (e (0, a), s a) (Tinv Φ.1) ∈ SB (κ → k) := isLocallyConstant_hasCompactSupport_schr ψ hlc _ _ hmem
      have h1 : Tinv Φ'.1 = schr ψ (0, b') (schr ψ (e (0, a), s a) (Tinv Φ.1)) := by
        funext x
        obtain ⟨⟨y, z⟩, rfl⟩ := e.surjective x
        have hx : e (y, z) + e (0, a) = e (y, z + a) := by rw [← map_add]; simp
        have hphase : -(β ⬝ᵥ y) + (e (y, z) ⬝ᵥ s a + ⅟(2 : k) * (e (0, a) ⬝ᵥ s a)) + -q (z + a) = -q z := by
          have h1 : e (y, z) = e (y, 0) + e (0, z) := by rw [← map_add]; simp
          have h2 : e (0, z + a) = e (0, z) + e (0, a) := by rw [← map_add]; simp
          have h3 := hsym z a
          have h4 : ⅟(2 : k) + ⅟(2 : k) = 1 := invOf_two_add_invOf_two
          simp only [q, hβ, h1, h2, map_add, add_dotProduct, dotProduct_add]
          linear_combination (-⅟(2 : k)) * h3 - (e (0, z) ⬝ᵥ s a) * h4
        have e1 : Tinv Φ'.1 (e (y, z)) = ψ (-q z) * Φ.1 ((0, y, z) + (0, 0, a)) := by
          simp only [Tinv, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, hGe, hΦ]
        have e2 : schr ψ (0, b') (schr ψ (e (0, a), s a) (Tinv Φ.1)) (e (y, z)) =
            ψ (-(β ⬝ᵥ y)) * (ψ (e (y, z) ⬝ᵥ s a + ⅟(2 : k) * (e (0, a) ⬝ᵥ s a)) *
              (ψ (-q (z + a)) * Φ.1 (0, y, z + a))) := by
          show ψ (e (y, z) ⬝ᵥ b' + ⅟(2 : k) * ((0 : κ → k) ⬝ᵥ b')) *
            (ψ ((e (y, z) + 0) ⬝ᵥ s a + ⅟(2 : k) * (e (0, a) ⬝ᵥ s a)) *
              (ψ (-q (e.symm (e (y, z) + 0 + e (0, a))).2) * Φ.1 (G (e (y, z) + 0 + e (0, a))))) = _
          rw [add_zero, zero_dotProduct, mul_zero, add_zero, hb', LinearEquiv.symm_apply_apply, neg_dotProduct, hx, hGe,
            LinearEquiv.symm_apply_apply]
          try dsimp only
          try rfl
        rw [e1, e2, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hphase]
        simp
      show l (Tinv Φ'.1) = l (Tinv Φ.1)
      rw [h1, hl _ hb'Λ _ hmem2, hl _ (hs a) _ hmem]
    obtain ⟨l₀, hl₀, -⟩ := GlobalTheory.CoinvSB.coinvariants k ψc ν hψcc hψc1 inferInstance (Fin 0) (Fin n) (Fin m) ℂ L hc1 hc2
    let one : GlobalTheory.SplitWeil.SB (Fin 0 → k) := ⟨fun _ => 1, IsLocallyConstant.const 1, (Set.toFinite _).isCompact⟩
    refine ⟨l₀ one, fun φ hφ => ?_⟩
    obtain ⟨Ψ, hΨ, hLΨ⟩ := hl₀ ⟨Tf φ, hTf φ hφ⟩
    have hΨ1 : Ψ = (Ψ.1 0) • one := by
      ext x
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, one, mul_one]
      rw [Subsingleton.elim x 0]
    have hl : l φ = L ⟨Tf φ, hTf φ hφ⟩ := by
      show l φ = l (Tinv (Tf φ))
      rw [hTT]
    rw [hl, hLΨ, hΨ1, map_smul, smul_eq_mul, hΨ 0, mul_comm]
  obtain ⟨c₁, hc₁⟩ := key l₁ h₁
  obtain ⟨c₂, hc₂⟩ := key l₂ h₂
  obtain ⟨φ₀, hφ₀, hne0⟩ := hne
  have hc2ne : c₂ ≠ 0 := by
    intro h
    apply hne0
    rw [hc₂ φ₀ hφ₀, h, zero_mul]
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  rw [hc₁ φ hφ, hc₂ φ hφ, ← mul_assoc, div_mul_cancel₀ c₁ hc2ne]

theorem proportional_at_place : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (κ : Type) [Fintype κ] (Λ : Submodule (Fv F v) ((κ → Fv F v) × (κ → Fv F v))),
    (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank (Fv F v) Λ = Fintype.card κ →
    ∀ l₁ l₂ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₁ (schr ψv w φ) = l₁ φ) →
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₂ (schr ψv w φ) = l₂ φ) →
    (∃ φ ∈ SB (κ → Fv F v), l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), l₁ φ = c * l₂ φ := by
  intro F _ _ v ψv hc hne κ _ Λ hiso hdim l₁ l₂ h₁ h₂ hne'
  letI : ValuativeRel (Fv F v) := GlobalTheory.LocalData.complRel v
  haveI : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v
  exact proportional (Fv F v) ψv hc hne κ Λ hiso hdim l₁ l₂ h₁ h₂ hne'

end GlobalTheory.LagrInvForm
