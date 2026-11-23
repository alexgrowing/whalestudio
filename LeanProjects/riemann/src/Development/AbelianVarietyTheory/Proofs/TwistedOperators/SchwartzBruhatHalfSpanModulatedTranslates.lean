import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfWaves

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

theorem isSBHalf_trans {a : AE D} {Λ : AddSubgroup (WO S T)} {x : WO S T} (hx : IsHalf a x) {k : ℕ} (hk : 0 < k)
    (hkx : k • x ∈ Λ) : IsSBHalf a Λ fun t => halfInd a Λ (t + x) := by
  have hx' := (isHalf_iff S T).1 hx
  refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have h : t + x ∈ Λ ∧ IsHalf a (t + x) := by
      by_contra h
      exact ht (if_neg h)
    refine (isHalf_iff S T).2 ?_
    exact (add_mem_cancel_right hx').1 ((isHalf_iff S T).1 h.2)
  · have hm : k • u ∈ Λ ⊓ half S T a :=
      nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k
    rw [halfInd_eq_ind]
    change ind _ (t + k • u + x) = ind _ (t + x)
    rw [add_right_comm]
    exact ind_add _ _ hm
  · have h : t + x ∈ Λ ∧ IsHalf a (t + x) := by
      by_contra h
      exact ht (if_neg h)
    have e : k • t = k • (t + x) - k • x := by rw [nsmul_add, add_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem h.1 k) hkx

theorem isSBHalf_modul (ψ : AddChar (AF D.host.F) ℂ) {a : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T u y) = 1)
    {y : WO S T} (hy : IsHalf (cA D a) y) {k : ℕ} (hk : 0 < k) (hky : k • y ∈ Λ) {Φ : WO S T → ℂ}
    (hΦ : IsSBHalf a Λ Φ) : IsSBHalf a Λ fun t => ψ (symplO S T t y) * Φ t := by
  have hb := isBichar_symplO S T ψ
  obtain ⟨a1, k', hk1, a2, a3⟩ := hΦ
  refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_nsmul]
      exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
    have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
      rw [mul_nsmul']
      exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _
        ⟨hky, nsmul_mem ((isHalf_iff S T).1 hy) k⟩)
    simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
  · rw [mul_nsmul']
    exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k

end GlobalTheory.HalfWaves

namespace GlobalTheory.PlaceTensor

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.HalfWaves

theorem halfWaves_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → a * cA D a = 0 → infPart D a = 0 → (∀ x y : WO S T, IsHalf a x → IsHalf (cA D a) y → IsSBHalf a (latO S T ΛS ΛT fun _ => True) (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Tm (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) = heisO ψ S T y (heisO ψ S T x f₀)) ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → Φ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧ Ψ = fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)} := by
  intro D ψ S T ΛS ΛT hψ hS hT e he _ hinf
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin0 := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin0 k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hsb : ∀ x, IsHalf e x → IsSBHalf e (latO S T ΛS ΛT fun _ => True)
      fun t => halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := fun x hx => by
    obtain ⟨k, hk, hk'⟩ := exists_nsmul_mem_latO' hS.1 hT.1 x (infPart_of_half hinf hx)
    exact isSBHalf_trans hx hk hk'
  have hmod : ∀ x y, IsHalf e x → IsHalf (cA D e) y → IsSBHalf e (latO S T ΛS ΛT fun _ => True)
      fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := fun x y hx hy => by
    obtain ⟨k, hk, hk'⟩ := exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_of_half (infPart_cA hinf) hy)
    exact isSBHalf_modul ψ hLL' hy hk hk' (hsb x hx)
  refine ⟨fun x y hx hy => ⟨hmod x y hx hy, fun f₀ Tm hTm => ?_⟩, fun Φ hΦ => ?_⟩
  · have v := hTm.vac
    rw [one_smul] at v
    rw [hTm.modul _ (hsb x hx) y hy, hTm.trans _ (GlobalTheory.isSBHalf_halfInd e _) x hx, v]
  · have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
        ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
      obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
      exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
        (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
        fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
    refine (Submodule.span_le.2 ?_) hm
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        ψ (symplO S T x y) • fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := by
      funext t
      simp only [wave, Pi.smul_apply, smul_eq_mul, halfInd_eq_ind, symplO_add_left, AddChar.map_add_eq_mul]
      ring
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, y, (isHalf_iff S T).2 hx, (isHalf_iff S T).2 hy, rfl⟩)

end GlobalTheory.PlaceTensor

end
