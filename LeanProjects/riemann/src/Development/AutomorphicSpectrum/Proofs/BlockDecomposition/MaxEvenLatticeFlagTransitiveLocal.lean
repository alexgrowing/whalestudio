import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.Iwasawa

section Abstract

variable {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R)

theorem isEvenInt_map {V : Type} [AddCommGroup V] [Module R V] {h : V → V → R} (e : V ≃ₗ[R] V)
    (he : ∀ x y, h (e x) (e y) = h x y) {L : Submodule 𝔬 V} (hL : IsEvenInt c 𝔬 h L) :
    IsEvenInt c 𝔬 h (L.map (e.toLinearMap.restrictScalars 𝔬)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change h (e x) (e y) ∈ 𝔬
    rw [he]
    exact hL.1 x hx y hy
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, e'⟩ := hL.2 x hx
    refine ⟨a, ha, ?_⟩
    change h (e x) (e x) = _
    rw [he, e']

theorem isMaxEven_map {V : Type} [AddCommGroup V] [Module R V] {h : V → V → R} (e : V ≃ₗ[R] V)
    (he : ∀ x y, h (e x) (e y) = h x y) {L : Submodule 𝔬 V} (hL : IsMaxEven c 𝔬 h L) :
    IsMaxEven c 𝔬 h (L.map (e.toLinearMap.restrictScalars 𝔬)) := by
  obtain ⟨⟨hfg, hsp⟩, hev, hmax⟩ := hL
  refine ⟨⟨hfg.map _, ?_⟩, isEvenInt_map c 𝔬 e he hev, fun L' hL' hle => ?_⟩
  · have h1 : ((L.map (e.toLinearMap.restrictScalars 𝔬) : Submodule 𝔬 V) : Set V) =
        e.toLinearMap '' (L : Set V) := by
      ext z
      rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    exact e.surjective
  · have hs : ∀ x y, h (e.symm x) (e.symm y) = h x y := fun x y => by
      rw [← he (e.symm x), e.apply_symm_apply, e.apply_symm_apply]
    have h1 := isEvenInt_map c 𝔬 e.symm hs hL'
    have h2 : L ≤ L'.map (e.symm.toLinearMap.restrictScalars 𝔬) := fun y hy =>
      ⟨e y, hle ⟨y, hy, rfl⟩, by simp⟩
    intro z hz
    exact ⟨e.symm z, hmax _ h1 h2 ⟨z, hz, rfl⟩, by simp⟩

variable {n r : ℕ}

theorem hform_eq (Jm : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform c Jm x y = (fun i => c (x i)) ⬝ᵥ (Jm *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cT_mul_apply (Jm : Matrix (Fin n) (Fin n) R) {k l : ℕ} (M : Matrix (Fin n) (Fin k) R)
    (N : Matrix (Fin n) (Fin l) R) (i : Fin k) (j : Fin l) :
    (cT c M * Jm * N) i j = Formalism.UG.hform c Jm (fun a => M a i) (fun a => N a j) := by
  simp only [Matrix.mul_apply, cT, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem isHerm_hform (hc : ∀ a, c (c a) = a) (Jm : Matrix (Fin n) (Fin n) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) : IsHerm c (Formalism.UG.hform c Jm) where
  add_right x y z := by
    simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right a x y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  symm x y := by
    simp only [Formalism.UG.hform, map_sum, map_mul, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ]
    ring

theorem isPerfect_hform (hc : ∀ a, c (c a) = a) (Jm : Matrix (Fin n) (Fin n) R)
    (hd : IsUnit Jm.det) : IsPerfect (Formalism.UG.hform c Jm) where
  nondeg x hx := by
    have h1 : (fun i => c (x i)) ᵥ* Jm = 0 := by
      funext j
      have h2 := hx (Pi.single j 1)
      rw [hform_eq, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h2
      exact h2
    have h2 : (fun i => c (x i)) = 0 := by
      have h3 := congrArg (fun w => w ᵥ* Jm⁻¹) h1
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd] using h3
    funext i
    have h3 := congrFun h2 i
    have h4 : c (x i) = 0 := h3
    rw [← hc (x i), h4, map_zero]
    rfl
  repr f := by
    let w : Fin n → R := fun j => f (fun k => if j = k then 1 else 0)
    let u : Fin n → R := w ᵥ* Jm⁻¹
    refine ⟨fun i => c (u i), fun y => ?_⟩
    rw [hform_eq]
    have h1 : (fun i => c (c (u i))) = u := funext fun i => hc _
    rw [h1, Matrix.dotProduct_mulVec]
    have h2 : u ᵥ* Jm = w := by
      simp only [u, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hd, Matrix.vecMul_one]
    rw [h2, LinearMap.pi_apply_eq_sum_univ f y]
    simp only [dotProduct, smul_eq_mul, w]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hform_mulVec (Jm g : Matrix (Fin n) (Fin n) R) (hg : cT c g * Jm * g = Jm) (x y : Fin n → R) :
    Formalism.UG.hform c Jm (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform c Jm x y := by
  have h1 : (fun i => c ((g *ᵥ x) i)) = (fun i => c (x i)) ᵥ* cT c g := by
    funext i
    simp only [mulVec, vecMul, dotProduct, cT, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hform_eq, hform_eq, h1, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hg]

theorem exists_mat (Jm : Matrix (Fin n) (Fin n) R) (p : (Fin n → R) ≃ₗ[R] (Fin n → R))
    (hp : ∀ x y, Formalism.UG.hform c Jm (p x) (p y) = Formalism.UG.hform c Jm x y) :
    ∃ P : GL (Fin n) R, P ∈ Formalism.UG.UJ c Jm ∧ ∀ y, (P : Matrix (Fin n) (Fin n) R) *ᵥ y = p y := by
  let P : GL (Fin n) R := ⟨LinearMap.toMatrix' p.toLinearMap, LinearMap.toMatrix' p.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨P, ?_, fun y => LinearMap.toMatrix'_mulVec _ _⟩
  change cT c (LinearMap.toMatrix' p.toLinearMap) * Jm * LinearMap.toMatrix' p.toLinearMap = Jm
  ext i j
  rw [cT_mul_apply]
  simp only [LinearMap.toMatrix'_apply]
  have h1 := hp (Pi.single i 1) (Pi.single j 1)
  refine h1.trans ?_
  simp [Formalism.UG.hform, Pi.single_apply]

theorem exists_coeff {V : Type} [AddCommGroup V] [Module R V] (x : Fin r → V) (j : Fin r) {w : V}
    (hw : w ∈ Submodule.span R (x '' {i | i ≤ j})) :
    ∃ b : Fin r → R, (∀ i, j < i → b i = 0) ∧ w = ∑ i, b i • x i := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    refine ⟨Pi.single i 1, fun k hk => ?_, ?_⟩
    · exact Pi.single_eq_of_ne (ne_of_gt (lt_of_le_of_lt hi hk)) _
    · simp [Pi.single_apply]
  | zero => exact ⟨0, by simp, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨b₁, h₁, rfl⟩ := ha
    obtain ⟨b₂, h₂, rfl⟩ := hb
    refine ⟨b₁ + b₂, fun i hi => by simp [h₁ i hi, h₂ i hi], ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | smul t a _ ha =>
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨t • b, fun i hi => by simp [hb i hi], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem cT_mul_map {A B : Type} [CommRing A] [CommRing B] (s : A →+* A) (c : B →+* B) (f : A →+* B)
    (h : ∀ t, c (f t) = f (s t)) {k l : ℕ} (M : Matrix (Fin n) (Fin k) A) (Jm : Matrix (Fin n) (Fin n) A)
    (N : Matrix (Fin n) (Fin l) A) :
    cT c (M.map f) * Jm.map f * N.map f = (cT s M * Jm * N).map f := by
  have h1 : cT c (M.map f) = (cT s M).map f := by
    ext i j
    simp [cT, h]
  rw [h1, Matrix.map_mul, Matrix.map_mul]

theorem iwasawa_abs (hc : ∀ a, c (c a) = a) (Jm : Matrix (Fin n) (Fin n) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (hd : IsUnit Jm.det) (Xm Ym : Matrix (Fin n) (Fin r) R)
    (hxx : cT c Xm * Jm * Xm = 0) (hyy : cT c Ym * Jm * Ym = 0) (hxy : cT c Xm * Jm * Ym = 1)
    (hFT : FlagTransitive c 𝔬) (Λ : Submodule 𝔬 (Fin n → R))
    (hΛ : IsMaxEven c 𝔬 (Formalism.UG.hform c Jm) Λ) (g : GL (Fin n) R) (hg : g ∈ Formalism.UG.UJ c Jm) :
    ∃ P : GL (Fin n) R, P ∈ Formalism.UG.UJ c Jm ∧
      (∀ y, y ∈ Λ ↔ ((P⁻¹ * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ y ∈ Λ) ∧
      ∃ B : Matrix (Fin r) (Fin r) R, B.BlockTriangular id ∧
        (P : Matrix (Fin n) (Fin n) R) * Xm = Xm * B := by
  have hgm : cT c (g : Matrix (Fin n) (Fin n) R) * Jm * (g : Matrix (Fin n) (Fin n) R) = Jm := hg
  let e : (Fin n → R) ≃ₗ[R] (Fin n → R) := Matrix.toLinearEquiv' (g : Matrix (Fin n) (Fin n) R)
    ⟨((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R), by simp, by simp⟩
  have heIso : ∀ a b, Formalism.UG.hform c Jm (e a) (e b) = Formalism.UG.hform c Jm a b := fun a b =>
    hform_mulVec c Jm _ hgm a b
  let x : Fin r → Fin n → R := fun i a => Xm a i
  let y : Fin r → Fin n → R := fun i a => Ym a i
  have hFr : IsFrame (Formalism.UG.hform c Jm) x y :=
    ⟨fun i j => by rw [← cT_mul_apply, hxx]; rfl, fun i j => by rw [← cT_mul_apply, hyy]; rfl,
      fun i j => by rw [← cT_mul_apply, hxy, Matrix.one_apply]⟩
  obtain ⟨p, ⟨hpi, hpL⟩, hpf⟩ := hFT _ (Formalism.UG.hform c Jm) (isHerm_hform c hc Jm hJ)
    (isPerfect_hform c hc Jm hd) r x y hFr Λ (Λ.map (e.toLinearMap.restrictScalars 𝔬)) hΛ
    (isMaxEven_map c 𝔬 e heIso hΛ)
  obtain ⟨P, hP, hPy⟩ := exists_mat c Jm p hpi
  refine ⟨P, hP, fun w => ?_, ?_⟩
  · have hz : p (((P⁻¹ * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w) = e w := by
      rw [← hPy, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
      rfl
    rw [hpL (((P⁻¹ * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w), hz]
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w', hw', h'⟩
      have h2 : w' = w := e.injective h'
      exact h2 ▸ hw'
  · choose b hb0 hb using fun j => exists_coeff x j (hpf j)
    refine ⟨Matrix.of fun i j => b j i, fun i j hij => hb0 j i hij, ?_⟩
    ext a j
    have h1 := congrFun (hb j) a
    rw [← hPy] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mul_apply, Matrix.of_apply]
    refine h1.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end Abstract

section Place

theorem sigR_sigR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (K : Type) [CommRing K] [Algebra F K] (t : K ⊗[F] E) :
    sigR K σ (sigR K σ t) = t := by
  have hs : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hs]
  | add a b ha hb => simp only [map_add, ha, hb]

end Place

theorem iwasawa_loc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), FlagTransitive (sigR (Fv F v) σ) (intLoc F E v) → ∀ Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → ∀ g : GLoc σ J v, ∃ p : GLoc σ J v, ∃ k ∈ stabLat σ J Λ, g = p * k ∧ ∃ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id ∧ (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW v hFT Λ hΛ g
  have hs : ∀ t : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) t) = inclR (F := F) (Fv F v) (σ t) := by
    intro t
    simp [sigR, inclR]
  have hJm : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) J j i) = JR (Fv F v) J i j := by
    intro i j
    simp only [JR, Matrix.map_apply, hs, hJ.1]
  have hdet : IsUnit (JR (F := F) (Fv F v) J).det := by
    have h1 : (JR (F := F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det :=
      (RingHom.map_det _ _).symm
    rw [h1]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hg : matHom _ σ J g ∈ Formalism.UG.UJ (sigR (Fv F v) σ) (JR (Fv F v) J) := Subtype.property _
  obtain ⟨P, hP, hk, B, hB, hPB⟩ := iwasawa_abs (sigR (Fv F v) σ) (intLoc F E v) (sigR_sigR hCM (Fv F v))
    (JR (Fv F v) J) hJm hdet (X.map (inclR (F := F) (Fv F v))) (Y.map (inclR (F := F) (Fv F v)))
    ((cT_mul_map (σ : E →+* E) (sigR (Fv F v) σ) (inclR (F := F) (Fv F v)) hs X J X).trans (by rw [hW.xx]; simp))
    ((cT_mul_map (σ : E →+* E) (sigR (Fv F v) σ) (inclR (F := F) (Fv F v)) hs Y J Y).trans (by rw [hW.yy]; simp))
    ((cT_mul_map (σ : E →+* E) (sigR (Fv F v) σ) (inclR (F := F) (Fv F v)) hs X J Y).trans (by rw [hW.xy]; simp))
    hFT Λ hΛ _ hg
  let p : GLoc σ J v := (⟨P, hP⟩ : HR (Fv F v) σ J)
  have hp : matHom _ σ J p = P := rfl
  refine ⟨p, p⁻¹ * g, ?_, (mul_inv_cancel_left p g).symm, B, hB, hPB⟩
  rw [mem_stabLat]
  intro w
  rw [map_mul, map_inv, hp]
  exact hk w

end GlobalTheory.CompanionTheory.KFin.Iwasawa

end
