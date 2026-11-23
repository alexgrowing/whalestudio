import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.StepVac

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

section Abstract

variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}

theorem ind_mem_of_stable (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1)
    (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (M : Submodule ℂ (G → ℂ)) (Mt : ∀ Φ ∈ M, ∀ x ∈ X, (fun t => Φ (t + x)) ∈ M)
    (Mm : ∀ Φ ∈ M, ∀ y ∈ Y, (fun t => χ t y * Φ t) ∈ M)
    (Φ : G → ℂ) (hΦ : Φ ∈ M) (h0 : Φ 0 ≠ 0) (h1 : ∀ t, Φ t ≠ 0 → t ∈ X) (k : ℕ) (hk : 0 < k)
    (h2 : ∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t) (h3 : ∀ t, Φ t ≠ 0 → k • t ∈ L) : ind L ∈ M := by
  classical
  set K := L.map (nsmulAddMonoidHom k) with hK
  have hKL : K ≤ L := by
    rintro _ ⟨u, hu, rfl⟩
    exact nsmul_mem hu k
  have key : ∀ R : Finset G, ∃ Ψ ∈ M, (∀ t ∈ K, Ψ t = Φ 0) ∧ (∀ t, Φ t = 0 → Ψ t = 0) ∧
      ∀ r ∈ R, r ∈ X → r ∉ K → ∀ u ∈ K, Ψ (r + u) = 0 := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      refine ⟨Φ, hΦ, ?_, fun t ht => ht, by simp⟩
      rintro _ ⟨u, hu, rfl⟩
      simpa using h2 u hu 0
    | insert r R _ ih =>
      obtain ⟨Ψ, hΨ, a1, a2, a3⟩ := ih
      by_cases hr : r ∈ X ∧ r ∉ K
      · obtain ⟨r', hr', rfl⟩ := dX k hk r hr.1
        have : ¬ ∀ y ∈ L', χ r' y = 1 := fun hh => hr.2 ⟨r', hX r' hr' hh, rfl⟩
        push Not at this
        obtain ⟨y, hy, hne⟩ := this
        obtain ⟨y', hy', rfl⟩ := dY k hk y (hL' hy)
        rw [← h.nsmul] at hne
        have hK1 : ∀ u ∈ K, χ u y' = 1 := by
          rintro _ ⟨u, hu, rfl⟩
          exact (h.nsmul k u y').trans (hLL' u hu _ hy)
        have hne' : χ (k • r') y' - 1 ≠ 0 := sub_ne_zero.2 hne
        refine ⟨(χ (k • r') y' - 1)⁻¹ • (χ (k • r') y' • Ψ - fun t => χ t y' * Ψ t),
          Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ hΨ) (Mm _ hΨ _ hy')), fun t ht => ?_,
          fun t ht => ?_, fun s hs hsL hsK u hu => ?_⟩
        · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, a1 t ht, hK1 t ht]
          field_simp
        · simp [a2 t ht]
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · simp [h.left, hK1 u hu]
          · simp [a3 s hs hsL hsK u hu]
      · refine ⟨Ψ, hΨ, a1, a2, fun s hs hsL hsK u hu => ?_⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact absurd ⟨hsL, hsK⟩ hr
        · exact a3 s hs hsL hsK u hu
  obtain ⟨R, hR, hR'⟩ := hfin k hk
  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : G => k • t) ⁻¹' R2).Finite := hR2.preimage (tf k hk).injOn
  obtain ⟨Ψ, hΨ, a1, a2, a3⟩ := key hP.toFinset
  have hKM : ind K ∈ M := by
    convert M.smul_mem (Φ 0)⁻¹ hΨ using 1
    funext t
    by_cases ht : t ∈ K
    · simp [ind, ht, a1 t ht, h0]
    · rw [ind, if_neg ht, Pi.smul_apply]
      by_cases hz : Φ t = 0
      · rw [a2 t hz, smul_zero]
      · obtain ⟨r, hr, u, hu, e⟩ := hR2' _ (h3 t hz)
        have huK : k • u ∈ K := ⟨u, hu, rfl⟩
        have := a3 (t - k • u) (hP.mem_toFinset.2 (by
          change k • (t - k • u) ∈ R2
          rwa [smul_sub, e, smul_smul, add_sub_cancel_right])) (sub_mem (h1 t hz) (hL (hKL huK)))
          (fun hh => ht (by simpa using add_mem hh huK)) _ huK
        rw [sub_add_cancel] at this
        rw [this, smul_zero]
  have hle : waveSpan χ X Y K ≤ M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact Mt _ (Mm _ hKM y hy) x hx
  refine hle (mem_of_finite_cosets (K := K)
    (Submodule.subset_span ⟨0, zero_mem _, 0, zero_mem _, (wave_zero h).symm⟩) hR.toFinset _ (fun t ht => ?_)
    (fun u hu t => ind_add L t (hKL hu)) fun t ht => ?_)
  · exact hL (by by_contra hh; exact ht (if_neg hh))
  · obtain ⟨r, hr, u, hu, e⟩ := hR' t (by by_contra hh; exact ht (if_neg hh))
    exact ⟨r, hR.mem_toFinset.2 hr, k • u, ⟨u, hu, rfl⟩, e⟩

theorem equivariant_of_wave {V : Type} [AddCommGroup V] [Module ℂ V] (h : IsBichar χ)
    (ρ : G → V →ₗ[ℂ] V) (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ f, ρ x (ρ x' f) = ρ (x + x') f)
    (ρY : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ f, ρ y (ρ y' f) = ρ (y + y') f)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Y, ∀ f, ρ x (ρ y f) = χ x y • ρ y (ρ x f)) (f₀ : V) (T : (G → ℂ) →ₗ[ℂ] V)
    (hT : ∀ x ∈ X, ∀ y ∈ Y, T (wave χ L x y) = ρ x (ρ y f₀)) {Φ : G → ℂ} (hΦ : Φ ∈ waveSpan χ X Y L) :
    (∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ) := by
  induction hΦ using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hh
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rw [wave_trans, hT _ (add_mem hx ha) _ hb, hT _ ha _ hb, ρX _ hx _ ha]
    · rw [wave_modul h, map_smul, hT _ ha _ (add_mem hy hb), hT _ ha _ hb, ← ρY _ hy _ hb, ρXY _ ha _ hy, smul_smul,
        h.neg_mul, one_smul]
  | zero =>
    refine ⟨fun x _ => ?_, fun y _ => ?_⟩
    · rw [map_zero, map_zero]; exact map_zero T
    · rw [map_zero, map_zero, ← map_zero T]; congr 1; funext t; simp
  | add f g _ _ hf hg =>
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rw [map_add, map_add, ← hf.1 x hx, ← hg.1 x hx, ← map_add]; rfl
    · rw [map_add, map_add, ← hf.2 y hy, ← hg.2 y hy, ← map_add]; congr 1; funext t; simp [mul_add]
  | smul c f _ hf =>
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rw [map_smul, map_smul, ← hf.1 x hx, ← map_smul]; rfl
    · rw [map_smul, map_smul, ← hf.2 y hy, ← map_smul]; congr 1; funext t; simp [mul_left_comm]

theorem ne_zero_of_wave {V : Type} [AddCommGroup V] [Module ℂ V] (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y)
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (ρ : G → V →ₗ[ℂ] V) (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ f, ρ x (ρ x' f) = ρ (x + x') f)
    (ρY : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ f, ρ y (ρ y' f) = ρ (y + y') f)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Y, ∀ f, ρ x (ρ y f) = χ x y • ρ y (ρ x f)) (f₀ : V) (T : (G → ℂ) →ₗ[ℂ] V)
    (hT : ∀ x ∈ X, ∀ y ∈ Y, T (wave χ L x y) = ρ x (ρ y f₀)) (hv : T (ind L) = f₀) (hf : f₀ ≠ 0)
    (Φ : G → ℂ) (hΦ0 : Φ ≠ 0) (h1 : ∀ t, Φ t ≠ 0 → t ∈ X) (k : ℕ) (hk : 0 < k)
    (h2 : ∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t) (h3 : ∀ t, Φ t ≠ 0 → k • t ∈ L) : T Φ ≠ 0 := by
  intro hz
  have hm : Φ ∈ waveSpan χ X Y L := mem_waveSpan h hL hL' hLL' hX dX dY tf hfin Φ h1 k hk h2 h3
  have heq := fun Ψ hΨ => equivariant_of_wave (Φ := Ψ) h ρ ρX ρY ρXY f₀ T hT hΨ
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, Φ t₀ ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hΦ0 (funext hh)
  have Mt : ∀ Ψ ∈ waveSpan χ X Y L ⊓ LinearMap.ker T, ∀ x ∈ X,
      (fun t => Ψ (t + x)) ∈ waveSpan χ X Y L ⊓ LinearMap.ker T := fun Ψ hΨ x hx =>
    ⟨trans_mem hΨ.1 hx, by
      rw [SetLike.mem_coe, LinearMap.mem_ker, (heq Ψ hΨ.1).1 x hx, show T Ψ = 0 from hΨ.2, LinearMap.map_zero]⟩
  have := ind_mem_of_stable h hL hL' hLL' hX dX dY tf hfin
    _ Mt (fun Ψ hΨ y hy => ⟨modul_mem h hΨ.1 hy, by
      rw [SetLike.mem_coe, LinearMap.mem_ker, (heq Ψ hΨ.1).2 y hy, show T Ψ = 0 from hΨ.2, LinearMap.map_zero]⟩)
    _ (Mt Φ ⟨hm, hz⟩ t₀ (h1 t₀ ht₀)) (by simpa using ht₀)
    (fun t ht => (add_mem_cancel_right (h1 t₀ ht₀)).1 (h1 _ ht)) k hk
    (fun u hu t => by rw [add_right_comm, h2 u hu])
    (fun t ht => (add_mem_cancel_right (h3 t₀ ht₀)).1 (by rw [← nsmul_add]; exact h3 _ ht))
  exact hf (hv.symm.trans this.2)

end Abstract

variable {D : D7} {S T : HSp D}

theorem placeModel_wave (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) :
    ∀ x ∈ half S T e, ∀ y ∈ half S T (cA D e),
      Tm (wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y) = heisL S T ψ x (heisL S T ψ y f₀) := by
  intro x hx y hy
  have hb := isBichar_symplO S T ψ
  have s0 := GlobalTheory.isSBHalf_halfInd e Λ
  have s1 : IsSBHalf e Λ fun t => ψ (symplO S T t y) * halfInd e Λ t := by
    obtain ⟨k, hk, hk'⟩ := hden y hy
    obtain ⟨a1, k', hk1, a2, a3⟩ := s0
    refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
      fun t ht => ?_⟩
    · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
        rw [mul_nsmul]
        exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
      have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
        rw [mul_nsmul']
        exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _
          ⟨hk', nsmul_mem hy k⟩)
      simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
    · rw [mul_nsmul']
      exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
  have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
      fun t => (fun t => ψ (symplO S T t y) * halfInd e Λ t) (t + x) := by
    rw [halfInd_eq_ind]; rfl
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [e1, h₁.trans _ s1 x ((isHalf_iff S T).2 hx), h₁.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
  rfl

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem placeModel_span_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {e : AE D} (he : e * e = e) (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    {f₀ Φ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    Tm Φ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) ∧
      (f₀ ≠ 0 → Φ ≠ 0 → Tm Φ ≠ 0) := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin0 := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hden0 := fun t ht => exists_nsmul_mem_latO' hS.1 hT.1 t ht
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  generalize (latO S T ΛS ΛT fun _ => True) = Λ at *
  have fX : ∀ x ∈ half S T e, x.map (infPart D) = 0 := fun x hx => infPart_of_half hinf ((isHalf_iff S T).2 hx)
  have fY : ∀ x ∈ half S T (cA D e), x.map (infPart D) = 0 := fun x hx =>
    infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hx)
  have hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (fX u hu.2)).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e :=
    fun x hx h => by
      refine ⟨(hdual x (fX x hx)).2 fun u hu => ?_, hx⟩
      have := h _ (hsm _ he' u hu)
      rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u := fun k hk => by
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
  have hw := placeModel_wave ψ Λ hLL' (fun y hy => hden0 y (fY y hy)) hTm
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  have h1' : ∀ t, Φ t ≠ 0 → t ∈ half S T e := fun t ht => (isHalf_iff S T).1 (h1 t ht)
  have h2' : ∀ u ∈ Λ ⊓ half S T e, ∀ t, Φ (t + k • u) = Φ t := fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2)
  have h3' : ∀ t, Φ t ≠ 0 → k • t ∈ Λ ⊓ half S T e := fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem (h1' t ht) _⟩
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e)) (Λ ⊓ half S T e) :=
    mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ h1' k hk h2' h3'
  refine ⟨?_, fun hf hΦ0 => ?_⟩
  · refine Submodule.mem_comap.1 (Submodule.span_le.2 ?_ hm)
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hw x hx y hy, heisL_heisL]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x + y, ?_⟩, rfl⟩)
    ext i j
    change infPart D (x i j + y i j) = 0
    rw [RingHom.map_add, show infPart D (x i j) = 0 from congrFun (congrFun (fX x hx) i) j,
      show infPart D (y i j) = 0 from congrFun (congrFun (fY y hy) i) j, add_zero]
  · have c1 : cA D e * e = 0 := by rw [mul_comm, hec]
    have c2 : cA D (cA D e) * cA D e = 0 := by rw [cA_cA, hec]
    have v1 := hTm.vac
    rw [one_smul, halfInd_eq_ind] at v1
    exact ne_zero_of_wave hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin
      (heisL S T ψ) (heisL_half S T ψ c1) (heisL_half S T ψ c2) (fun x _ y _ => heisL_comm S T ψ x y) f₀ Tm hw v1 hf
      Φ hΦ0 h1' k hk h2' h3'

end GlobalTheory.Chain.StepVac

end
