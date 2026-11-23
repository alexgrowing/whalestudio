import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TangentOrigin
open GlobalTheory.Twist (resM resM_resM resM_smul)

namespace GlobalTheory.BcLie

variable {X X' : Scheme.{0}} {M : X.Modules} {r : ℕ} {K K' : Type} [CommRing K] [CommRing K']

def trS (c c' : Chart M r) : Matrix (Fin r) (Fin r) Γ(X, c.U ⊓ c'.U) :=
  Matrix.of fun a b => (c.isFrame.basis inf_le_left).repr (resM M inf_le_right (c'.e b)) a

open Classical in

def trAt (x : Sp K ⟶ X) (c c' : Chart M r) : Matrix (Fin r) (Fin r) K :=
  if h : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U) then (trS c c').map (evalPt x _ h) else 0

def IsCo (ξ : Sp K ⟶ X) (A : Chart M r → Matrix (Fin r) (Fin r) K) : Prop :=
  (∀ c : Chart M r, ⊤ ≤ ξ ⁻¹ᵁ c.U → IsUnit (A c).det) ∧
    ∀ c c' : Chart M r, ⊤ ≤ ξ ⁻¹ᵁ c.U → ⊤ ≤ ξ ⁻¹ᵁ c'.U → A c' = A c * trAt ξ c c'

def IsAdapted (fl : Vert.Flag M r) (c : Chart M r) : Prop :=
  ∀ i : Fin r, ∃ s : Γ(fl.F i.succ, c.U), (fl.ι i.succ).app c.U s = c.e i

def IsTri (T : Matrix (Fin r) (Fin r) K) : Prop := ∀ a i, i < a → T a i = 0

def pos (dual : Bool) (i : Fin r) : Fin r := cond dual i.rev i

def lieMat (dual : Bool) (A : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K := cond dual (A⁻¹)ᵀ A

theorem le_inf_pre {x : Sp K ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun p hp => ⟨h hp, h' hp⟩

theorem trAt_eq {x : Sp K ⟶ X} (c c' : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U)) :
    trAt x c c' = (trS c c').map (evalPt x _ h) := dif_pos h

theorem trAt_apply {x : Sp K ⟶ X} (c c' : Chart M r) {W : X.Opens} (h₁ : W ≤ c.U) (h₂ : W ≤ c'.U) (h : ⊤ ≤ x ⁻¹ᵁ W)
    (a b : Fin r) : trAt x c c' a b = evalPt x W h ((c.isFrame.basis h₁).repr (resM M h₂ (c'.e b)) a) := by
  have hW : W ≤ c.U ⊓ c'.U := le_inf h₁ h₂
  have h' : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U) := fun p hp => hW (h hp)
  rw [trAt_eq c c' h', map_apply, trS, of_apply, ← evalPt_res x hW h' h, ← c.isFrame.repr_resM, resM_resM]

theorem trAt_self {x : Sp K ⟶ X} (c : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ c.U) : trAt x c c = 1 := by
  ext a b
  rw [trAt_apply c c le_rfl le_rfl h, ← c.isFrame.basis_apply, Module.Basis.repr_self, Finsupp.single_apply, one_apply]
  simp only [eq_comm (a := a)]
  split_ifs <;> simp

theorem trAt_mul {x : Sp K ⟶ X} (c c' c'' : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (h'' : ⊤ ≤ x ⁻¹ᵁ c''.U) : trAt x c c' * trAt x c' c'' = trAt x c c'' := by
  have hW := le_inf_pre (le_inf_pre h h') h''
  have l₁ : c.U ⊓ c'.U ⊓ c''.U ≤ c.U := inf_le_left.trans inf_le_left
  have l₂ : c.U ⊓ c'.U ⊓ c''.U ≤ c'.U := inf_le_left.trans inf_le_right
  have l₃ : c.U ⊓ c'.U ⊓ c''.U ≤ c''.U := inf_le_right
  ext a b
  rw [mul_apply, trAt_apply c c'' l₁ l₃ hW, ← (c'.isFrame.basis l₂).sum_repr (resM M l₃ (c''.e b))]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_mul,
    IsFrame.basis_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [trAt_apply c c' l₁ l₂ hW, trAt_apply c' c'' l₂ l₃ hW, mul_comm]

theorem isUnit_det_trAt {x : Sp K ⟶ X} (c c' : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) :
    IsUnit (trAt x c c').det :=
  isUnit_det_of_right_inverse ((trAt_mul c c' c h h' h).trans (trAt_self c h))

theorem trAt_spMap (φ : K →+* K') {x : Sp K ⟶ X} (c c' : Chart M r) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U) :
    trAt (spMap φ ≫ x) c c' = (trAt x c c').map φ := by
  have hW := le_inf_pre h h'
  have hW' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ (c.U ⊓ c'.U) := fun p _ => hW (x := spMap φ p) trivial
  rw [trAt_eq c c' hW, trAt_eq c c' hW']
  ext a b
  exact evalPt_spMap_comp φ x _ hW hW' _

theorem evalPt_appLE (x : Sp K ⟶ X') (π : X' ⟶ X) {U : X.Opens} {T : X'.Opens} (hT : T ≤ π ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ T)
    (h' : ⊤ ≤ (x ≫ π) ⁻¹ᵁ U) (s : Γ(X, U)) : evalPt x T h (π.appLE U T hT s) = evalPt (x ≫ π) U h' s := by
  have := congrArg (fun φ => ((φ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom s))
    (Scheme.Hom.appLE_comp_appLE x π U T ⊤ hT h)
  exact this

theorem trAt_pull (hM : IsVB M r) (π : X' ⟶ X) {x : Sp K ⟶ X'} (c c' : Chart M r) (h : ⊤ ≤ (x ≫ π) ⁻¹ᵁ c.U)
    (h' : ⊤ ≤ (x ≫ π) ⁻¹ᵁ c'.U) : trAt x (c.pull hM π) (c'.pull hM π) = trAt (x ≫ π) c c' := by
  have := hM.isQuasicoherent
  have hW := le_inf_pre h h'
  have hW' : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ (c.U ⊓ c'.U)) := hW
  have l₁ : π ⁻¹ᵁ (c.U ⊓ c'.U) ≤ (c.pull hM π).U := fun p hp => hp.1
  have l₂ : π ⁻¹ᵁ (c.U ⊓ c'.U) ≤ (c'.pull hM π).U := fun p hp => hp.2
  ext a b
  rw [trAt_apply _ _ l₁ l₂ hW', trAt_apply c c' inf_le_left inf_le_right hW, ← evalPt_appLE x π le_rfl hW' hW,
    ← c.isFrame.pullback_basis_repr π inf_le_left le_rfl]
  refine congrArg (fun t => evalPt x _ hW' (((c.isFrame.pullback π).basis l₁).repr t a)) ?_
  exact (QCoh.res_pullbackSections π M le_rfl l₂ _).trans (QCoh.pullbackSections_res π M le_rfl inf_le_right _).symm

theorem trAt_cx {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ} (z : CxPts p σ) (c c' : Chart M r)
    (h : z ∈ CxPts.ptsIn p σ c.U) (h' : z ∈ CxPts.ptsIn p σ c'.U) : trAt z.1 c c' = c.tr p σ c' z := by
  have hW := CxPts.mem_ptsIn_inf.2 ⟨h, h'⟩
  have hW' : ⊤ ≤ z.1 ⁻¹ᵁ (c.U ⊓ c'.U) := fun q _ => by
    rw [show q = IsLocalRing.closedPoint ℂ from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
    exact CxPts.mem_ptsIn.1 hW
  ext a b
  rw [trAt_apply c c' inf_le_left inf_le_right hW', Chart.tr, of_apply, c.crd_eq _ inf_le_right inf_le_left hW,
    CxPts.ev_eq hW]
  rfl

theorem lieMat_mul (dual : Bool) (A B : Matrix (Fin r) (Fin r) K) : lieMat dual (A * B) = lieMat dual A * lieMat dual B := by
  cases dual
  · rfl
  · simp only [lieMat, cond_true, Matrix.mul_inv_rev, transpose_mul]

theorem isUnit_det_lieMat (dual : Bool) {A : Matrix (Fin r) (Fin r) K} (h : IsUnit A.det) : IsUnit (lieMat dual A).det := by
  cases dual
  · exact h
  · simp only [lieMat, cond_true, det_transpose]
    exact isUnit_nonsing_inv_det A h

theorem lieMat_lieMat (dual : Bool) {A : Matrix (Fin r) (Fin r) K} (h : IsUnit A.det) : lieMat dual (lieMat dual A) = A := by
  cases dual
  · rfl
  · simp only [lieMat, cond_true]
    rw [← transpose_nonsing_inv, transpose_transpose, nonsing_inv_nonsing_inv _ h]

theorem lieMat_map (dual : Bool) (φ : K →+* K') {A : Matrix (Fin r) (Fin r) K} (h : IsUnit A.det) :
    lieMat dual (A.map φ) = (lieMat dual A).map φ := by
  cases dual
  · rfl
  · simp only [lieMat, cond_true]
    rw [transpose_map]
    congr 1
    refine inv_eq_left_inv ?_
    rw [← Matrix.map_mul, nonsing_inv_mul _ h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem pos_pos (dual : Bool) (i : Fin r) : pos dual (pos dual i) = i := by
  cases dual <;> simp [pos]

theorem IsCo.exists_pull {F F' : Type} [Field F] [Field F'] (hM : IsVB M r) {ξ : Sp F ⟶ X}
    {A : Chart M r → Matrix (Fin r) (Fin r) F} (hA : IsCo ξ A) (π : X' ⟶ X) (ξ' : Sp F' ⟶ X') (φ : F →+* F')
    (hξ : ξ' ≫ π = spMap φ ≫ ξ) (D : Matrix (Fin r) (Fin r) F') (hD : IsUnit D.det) :
    ∃ A' : Chart ((Scheme.Modules.pullback π).obj M) r → Matrix (Fin r) (Fin r) F', IsCo ξ' A' ∧
      ∀ c : Chart M r, ⊤ ≤ ξ ⁻¹ᵁ c.U → A' (c.pull hM π) = D * (A c).map φ := by
  obtain ⟨U, e, hx, he⟩ := hM (ξ (IsLocalRing.closedPoint F))
  let c₀ : Chart M r := ⟨U, e, he⟩
  have h₀ : ⊤ ≤ ξ ⁻¹ᵁ c₀.U := fun q _ => by
    rw [show q = IsLocalRing.closedPoint F from Subsingleton.elim (α := PrimeSpectrum F) _ _]
    exact hx
  have up : ∀ c : Chart M r, ⊤ ≤ ξ ⁻¹ᵁ c.U → ⊤ ≤ (ξ' ≫ π) ⁻¹ᵁ c.U := fun c h => by
    rw [hξ]; exact fun p _ => h (x := spMap φ p) trivial
  have h₀' : ⊤ ≤ ξ' ⁻¹ᵁ (c₀.pull hM π).U := up c₀ h₀
  refine ⟨fun c' => D * (A c₀).map φ * trAt ξ' (c₀.pull hM π) c', ⟨fun c' h => ?_, fun c' c'' h h' => ?_⟩, fun c h => ?_⟩
  · rw [det_mul, det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hD.mul ((hA.1 c₀ h₀).map φ)).mul (isUnit_det_trAt _ _ h₀' h)
  · rw [Matrix.mul_assoc (D * _), trAt_mul _ _ _ h₀' h h']
  · beta_reduce
    rw [trAt_pull hM π c₀ c (up c₀ h₀) (up c h), hξ, trAt_spMap φ c₀ c h₀ h, Matrix.mul_assoc, ← Matrix.map_mul,
      ← hA.2 c₀ c h₀ h]

end GlobalTheory.BcLie

end
