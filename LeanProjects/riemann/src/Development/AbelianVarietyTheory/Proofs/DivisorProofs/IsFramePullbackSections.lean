import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramesTriangularChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChangeSpansFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagSpannedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellFrameOfSpans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectivePointFlagHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagHomKeepsRadical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.Cartier
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.LB (resG_resG)

namespace GlobalTheory.FlagOverField

section Columns

variable {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ}

theorem spans_res {X : Scheme.{0}} {F : X.Modules} {fl : Vert.Flag F m} {V W : X.Opens}
    {v : Fin m → Γ(F, V)} (hv : Spans fl V v) (h : W ≤ V) : Spans fl W fun j => resM F h (v j) := by
  intro l
  obtain ⟨s, hs, hsv⟩ := hv l
  exact ⟨fun j => resM _ h (s j), hs.res h, fun j => by rw [app_resM, hsv]⟩

theorem res_pullCol (e : Fin m → Γ(E, U)) {V W : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) (h : W ≤ V)
    (M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    resM _ h (pullCol π e hV M j) = pullCol π e (h.trans hV) (M.map (resG Y h)) j := by
  simp only [pullCol, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact QCoh.res_pullbackSections π E hV h (e l)

theorem spans_pullCol_res {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) m} (e : Fin m → Γ(E, U))
    {V W : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) (h : W ≤ V) {M : Matrix (Fin m) (Fin m) Γ(Y, V)}
    (hM : Spans fl V (pullCol π e hV M)) : Spans fl W (pullCol π e (h.trans hV) (M.map (resG Y h))) := by
  have := spans_res hM h
  rwa [funext (res_pullCol π e hV h M)] at this

theorem sum_smul_pullCol (e : Fin m → Γ(E, U)) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    (N M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    ∑ k, M k j • pullCol π e hV N k = pullCol π e hV (N * M) j := by
  simp only [pullCol, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem isFrame_pullbackSections [E.IsQuasicoherent] {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens}
    (hV : V ≤ π ⁻¹ᵁ U) : IsFrame fun l => QCoh.pullbackSections π E hV (e l) := by
  have := (he.pullback π).res hV
  rwa [funext fun i => QCoh.res_pullbackSections π E le_rfl hV (e i)] at this

theorem exists_pullCol [E.IsQuasicoherent] {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens}
    (hV : V ≤ π ⁻¹ᵁ U) (v : Fin m → Γ((Scheme.Modules.pullback π).obj E, V)) :
    ∃ M : Matrix (Fin m) (Fin m) Γ(Y, V), ∀ j, v j = pullCol π e hV M j := by
  have hb := isFrame_pullbackSections π he hV V le_rfl
  choose c hc using fun j => hb.2 (v j)
  refine ⟨Matrix.of fun l j => c j l, fun j => ?_⟩
  rw [← hc j, Fintype.linearCombination_apply]
  simp only [pullCol, Matrix.of_apply, resM_self]

theorem pullCol_injective [E.IsQuasicoherent] {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens}
    (hV : V ≤ π ⁻¹ᵁ U) {M N : Matrix (Fin m) (Fin m) Γ(Y, V)}
    (h : ∀ j, pullCol π e hV M j = pullCol π e hV N j) : M = N := by
  have hb := isFrame_pullbackSections π he hV V le_rfl
  ext l j
  have := hb.1 (a₁ := fun l => M l j) (a₂ := fun l => N l j) (by
    simp only [Fintype.linearCombination_apply, resM_self]
    exact h j)
  exact congrFun this l

theorem exists_upper_of_spans [E.IsQuasicoherent] {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens}
    (hV : V ≤ π ⁻¹ᵁ U) {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) m} {M N : Matrix (Fin m) (Fin m) Γ(Y, V)}
    (hM : Spans fl V (pullCol π e hV M)) (hN : Spans fl V (pullCol π e hV N)) :
    ∃ T : Matrix (Fin m) (Fin m) Γ(Y, V), T.BlockTriangular id ∧ IsUnit T.det ∧ N = M * T := by
  obtain ⟨T, h₁, h₂, h₃⟩ := spans_change _ _ _ fl V _ _ hM hN
  exact ⟨T, h₁, h₂, pullCol_injective π he hV fun j => (h₃ j).trans (sum_smul_pullCol π e hV M T j)⟩

theorem spans_pullCol_mul (e : Fin m → Γ(E, U)) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) m} {M T : Matrix (Fin m) (Fin m) Γ(Y, V)}
    (hM : Spans fl V (pullCol π e hV M)) (h₁ : T.BlockTriangular id) (h₂ : IsUnit T.det) :
    Spans fl V (pullCol π e hV (M * T)) := by
  have := Spans.mul_upper _ _ _ fl V _ T hM h₁ h₂
  rwa [funext (sum_smul_pullCol π e hV M T)] at this

theorem isUnit_det_of_spans [E.IsQuasicoherent] {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens}
    (hV : V ≤ π ⁻¹ᵁ U) {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) m} {M : Matrix (Fin m) (Fin m) Γ(Y, V)}
    (hM : Spans fl V (pullCol π e hV M)) : IsUnit M.det := by
  obtain ⟨b, hb⟩ := hM.exists_basis
  have h (j : Fin m) : pullCol π e hV (M * Matrix.of fun k j => b.repr (pullCol π e hV 1 j) k) j = pullCol π e hV 1 j := by
    rw [← sum_smul_pullCol]
    simp only [Matrix.of_apply, ← hb]
    exact b.sum_repr _
  exact Matrix.isUnit_det_of_right_inverse (pullCol_injective π he hV h)

end Columns

variable {F : Type} [Field F] {Y : Var F} {ι : Type} {r : ι → ℕ} {E : ι → (Sp F).Modules}

def AdFrame (e : ∀ a, Fin (r a) → Γ(E a, ⊤))
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)) (y : Y.X) (A : Mat r Y.Fn) : Prop :=
  ∀ a, ∃ (U : Y.X.Opens) (hy : y ∈ U) (M : Matrix (Fin (r a)) (Fin (r a)) Γ(Y.X, U)),
    Spans (fl a) U (pullCol Y.str (e a) le_top M) ∧ A a = (M.map (fnOf U (gen_mem hy))).transpose

variable (F) in

def ptF : Sp F ⟶ PSpace F 0 :=
  GlobalTheory.ProjSpace.pt (RingHom.id F) (fun _ => 1) (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one)

variable (F) in

def spToPt : Sp F ⟶ (proj F 0).X := ptF F ≫ @inv _ _ _ _ (proj F 0).ι (isIso_proj_ι F 0)

def toPt (Y : Var F) : Y.X ⟶ (proj F 0).X := Y.str ≫ spToPt F

variable (F r) in

def triv : Fr (ratOf (proj F 0)) r 0 := Fr.ofBasis _ 0 1 fun _ => by simp

end GlobalTheory.FlagOverField
