import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.ImgVB

theorem exists_col_comb {R : Type} [CommRing R] [IsDomain R] {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) R) (J : Fin r → Fin m) (hd : (A.submatrix id J).det ≠ 0)
    (hdiv : ∀ K : Fin r → Fin m, (A.submatrix id J).det ∣ (A.submatrix id K).det) (j : Fin m) :
    ∃ c : Fin r → R, ∀ i, A i j = ∑ k, c k * A i (J k) := by
  classical
  set B := A.submatrix id J with hB
  have hc : ∀ k, B.det ∣ B.cramer (fun i => A i j) k := by
    intro k
    rw [Matrix.cramer_apply]
    have : B.updateCol k (fun i => A i j) = A.submatrix id (Function.update J k j) := by
      ext i l
      by_cases hl : l = k
      · subst hl; simp [B, Matrix.updateCol_self]
      · simp [B, Matrix.updateCol_ne hl, Function.update_of_ne hl]
    rw [this]; exact hdiv _
  choose c hc using hc
  refine ⟨c, fun i => ?_⟩
  have h1 := Matrix.mulVec_cramer B (fun i => A i j)
  have h2 : B.cramer (fun i => A i j) = B.det • c := funext fun k => by simp [hc k]
  rw [h2, Matrix.mulVec_smul] at h1
  have h3 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  have h4 := mul_left_cancel₀ hd h3
  rw [← h4, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem eq_zero_of_comb {R : Type} [CommRing R] [IsDomain R] {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) R) (J : Fin r → Fin m) (hd : (A.submatrix id J).det ≠ 0)
    (x : Fin r → R) (hx : ∀ i, ∑ k, x k * A i (J k) = 0) : x = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun i => by
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hx i)

end GlobalTheory.ImgVB

namespace GlobalTheory.ImgVB

theorem isFrame_of_inj_of_local {Y : Scheme.{0}} {M : Y.Modules} {ι : Type} [Fintype ι]
    {U : Y.Opens} {e : ι → Γ(M, U)}
    (inj : ∀ (W : Y.Opens) (h : W ≤ U),
      Function.Injective (Fintype.linearCombination Γ(Y, W) fun i => resM M h (e i)))
    (loc : ∀ (W : Y.Opens) (h : W ≤ U) (s : Γ(M, W)) (x : Y), x ∈ W →
      ∃ (W' : Y.Opens) (h' : W' ≤ W), x ∈ W' ∧ ∃ a : ι → Γ(Y, W'),
        Fintype.linearCombination Γ(Y, W') (fun i => resM M (h'.trans h) (e i)) a = resM M h' s) :
    GlobalTheory.VB.IsFrame e := by
  refine fun V h => ⟨inj V h, fun s => ?_⟩
  choose W hW hx a ha using fun x : V => loc V h s x x.2
  have hc : V ≤ iSup W := fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
  have key (x y : V) : (fun i => resG Y (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG Y (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← GlobalTheory.VB.resM_linearCombination e ((hW x).trans h),
      ← GlobalTheory.VB.resM_linearCombination e ((hW y).trans h), ha, ha, resM_resM, resM_resM]
  choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (key x y) i
  refine ⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [GlobalTheory.VB.resM_linearCombination, ← ha x]
  exact congrArg _ (funext fun i => hb' i x)

end GlobalTheory.ImgVB

namespace GlobalTheory.ImgVB

theorem isVB_image_of_minor (Y : Scheme.{0}) [IsIntegral Y] (F E : Y.Modules) (φ : F ⟶ E)
    (r m : ℕ)
    (H : ∀ y : Y, ∃ (V : Y.Opens) (eF : Fin m → Γ(F, V)) (eE : Fin r → Γ(E, V))
      (a : Matrix (Fin r) (Fin m) Γ(Y, V)) (J : Fin r → Fin m), y ∈ V ∧ GlobalTheory.VB.IsFrame eF ∧
      GlobalTheory.VB.IsFrame eE ∧ (∀ j, φ.app V (eF j) = ∑ k, a k j • eE k) ∧
      (a.submatrix id J).det ≠ 0 ∧
      ∀ K : Fin r → Fin m, (a.submatrix id J).det ∣ (a.submatrix id K).det) :
    GlobalTheory.VB.IsVB (Limits.image φ) r := by
  intro y
  obtain ⟨V, eF, eE, a, J, hy, hF, hE, hφ, hd, hdiv⟩ := H y
  haveI : Nonempty V := ⟨⟨y, hy⟩⟩
  choose c hc using exists_col_comb a J hd hdiv
  have hι : ∀ (W : Y.Opens) (s : Γ(F, W)),
      (image.ι φ).app W ((factorThruImage φ).app W s) = φ.app W s := fun W s => by
    rw [GlobalTheory.QCoh.app_app, image.fac]
  have hinj : ∀ W : Y.Opens, Function.Injective ((image.ι φ).app W) :=
    fun W => GlobalTheory.QCoh.app_injective_of_mono _ W
  let t : Fin r → Γ(Limits.image φ, V) := fun k => (factorThruImage φ).app V (eF (J k))
  have hιt : ∀ (W : Y.Opens) (h : W ≤ V) (k : Fin r),
      (image.ι φ).app W (resM _ h (t k)) = ∑ i, resG Y h (a i (J k)) • resM E h (eE i) := by
    intro W h k
    rw [app_resM, hι, hφ, map_sum]
    simp only [resM_smul]
  have hpt : ∀ j, (factorThruImage φ).app V (eF j) = ∑ k, c j k • t k := by
    intro j
    apply hinj
    rw [hι, hφ, map_sum]
    simp only [Scheme.Modules.Hom.app_smul, t, hι, hφ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, hc j i]
  refine ⟨V, t, hy, isFrame_of_inj_of_local (fun W h => ?_) (fun W h s x hx => ?_)⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h1 := congrArg ((image.ι φ).app W) hx
    rw [map_zero, Fintype.linearCombination_apply, map_sum] at h1
    simp only [Scheme.Modules.Hom.app_smul, hιt, Finset.smul_sum, smul_smul] at h1
    rw [Finset.sum_comm] at h1
    simp only [← Finset.sum_smul] at h1
    have h2 := (hE W h).1 (a₁ := fun i => ∑ k, x k * resG Y h (a i (J k))) (a₂ := 0)
      (by rw [Fintype.linearCombination_apply, h1, map_zero])
    funext k
    refine fun_ext_of_cover (fun _ : W => W) (fun _ => le_rfl)
      (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz⟩) fun p => ?_
    haveI : Nonempty W := ⟨p⟩
    rw [resG_self, resG_self]
    have hd' : ((a.map (resG Y h)).submatrix id J).det ≠ 0 := by
      rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact fun h0 => hd (map_injective_of_isIntegral Y (homOfLE h) (h0.trans (map_zero _).symm))
    have := eq_zero_of_comb (a.map (resG Y h)) J hd' x fun i => by
      simpa using congrFun h2 i
    exact congrFun this k
  · obtain ⟨W', h', hxW', f, hf⟩ := GlobalTheory.VB.exists_app_eq_of_epi (factorThruImage φ) s hx
    obtain ⟨b, rfl⟩ := (hF W' (h'.trans h)).2 f
    refine ⟨W', h', hxW', fun k => ∑ j, b j * resG Y (h'.trans h) (c j k), ?_⟩
    rw [← hf, Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
    simp only [Scheme.Modules.Hom.app_smul, app_resM, hpt, map_sum, resM_smul, Finset.smul_sum,
      smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

end GlobalTheory.ImgVB
