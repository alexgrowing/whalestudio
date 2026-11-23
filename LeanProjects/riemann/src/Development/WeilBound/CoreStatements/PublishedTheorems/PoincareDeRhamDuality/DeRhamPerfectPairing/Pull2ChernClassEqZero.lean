import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RestrictTrivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

section Alg

theorem key₁ {B B' : Type} [CommRing B] [CommRing B'] {n : ℕ} (ρ : B →+* B') (fφ : B) (fc fψ : B')
    (aφ gm : Fin n → B) (ac aψ bψ gm' : Fin n → B') (h1 : ρ fφ - fc + fψ = ∑ k, ρ (aφ k) * bψ k)
    (h2 : ∀ k, ac k = ρ (aφ k) + aψ k) (h3 : ∀ k, gm' k = ρ (gm k) + bψ k) :
    fc + ∑ k, ac k * gm' k = ρ (fφ + ∑ k, aφ k * gm k) + (fψ + ∑ k, aψ k * gm' k) := by
  have e : ∀ k, ac k * gm' k = ρ (aφ k) * ρ (gm k) + ρ (aφ k) * bψ k + aψ k * gm' k := by
    intro k
    linear_combination gm' k * h2 k + ρ (aφ k) * h3 k
  have hs := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => e k)
  simp only [Finset.sum_add_distrib] at hs
  rw [map_add, map_sum]
  simp only [map_mul]
  linear_combination hs - h1

theorem key₂ {B B' : Type} [CommRing B] [CommRing B'] {n : ℕ} (ρ : B →+* B') (fθ : B) (fc f₂ f₁ fθ' : B')
    (aθ gm₀ : Fin n → B) (b₂ a₁ bθ' a₂ aθ' gm₂ gm₁ t : Fin n → B')
    (h1 : ρ fθ - fc + f₂ = ∑ k, ρ (aθ k) * b₂ k) (h2 : f₁ - fc + fθ' = ∑ k, a₁ k * bθ' k)
    (h3 : ∀ k, ρ (aθ k) + a₂ k = a₁ k + aθ' k) (h4 : ∀ k, gm₂ k = ρ (gm₀ k) + b₂ k)
    (h5 : ∀ k, t k + gm₂ k = gm₁ k + bθ' k) :
    (fθ' + ∑ k, aθ' k * gm₂ k) - ρ (fθ + ∑ k, aθ k * gm₀ k) =
      (f₂ + ∑ k, a₂ k * gm₂ k) - (f₁ + ∑ k, a₁ k * gm₁ k) + ∑ k, t k * a₁ k := by
  have e : ∀ k, aθ' k * gm₂ k - ρ (aθ k) * ρ (gm₀ k) - a₂ k * gm₂ k + a₁ k * gm₁ k - t k * a₁ k
      = ρ (aθ k) * b₂ k - a₁ k * bθ' k := by
    intro k
    linear_combination (-gm₂ k) * h3 k + ρ (aθ k) * h4 k - a₁ k * h5 k
  have hs := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => e k)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs
  rw [map_add, map_sum]
  simp only [map_mul]
  linear_combination hs + h2 - h1

theorem exists_factor' {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) (x : M →ₗ[R] R)
    (h : ∀ m, f m = 0 → x m = 0) : ∃ x' : N →ₗ[R] R, ∀ m, x' (f m) = x m := by
  have hk : LinearMap.ker f ≤ LinearMap.ker x := fun m hm => h m hm
  refine ⟨(LinearMap.ker f).liftQ x hk ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap, fun m => ?_⟩
  have hm : (f.quotKerEquivOfSurjective hf).symm (f m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp [hm]

end Alg

section Cochain

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

def v1 (f : C1 (FP s)) {S S' : Pt s} (φ : S ⟶ S') : S'.B := f S S' φ

theorem cocycle_value_comp (f : Z1 (FP s)) {S S' S'' : Pt s} (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S ⟶ S'')
    (e : ∀ b, χ.ρ b = ψ.ρ (φ.ρ b)) : v1 f.1 χ = ψ.ρ (v1 f.1 φ) + v1 f.1 ψ := by
  have hχ : χ = φ ≫ ψ := by
    obtain ⟨ρχ, hχpt⟩ := χ
    have hρ : ρχ = (φ ≫ ψ).ρ := AlgHom.ext e
    subst hρ
    rfl
  subst hχ
  exact f.2 φ ψ

theorem cocycle_value_sum {n : ℕ} (t : Fin n → R) (z : Fin n → Z1 (FP s)) {S S' : Pt s} (φ : S ⟶ S') :
    v1 (∑ k, t k • z k).1 φ = ∑ k, algebraMap R S'.B (t k) * v1 (z k).1 φ := by
  unfold v1
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Algebra.smul_def _ _

theorem pull2_chern_class_eq_zero {L : LB X} (hL : L.IsLB) {z : SecondDeRham s} (hz : IsChern (dp0 R) s L z) :
    (toPC s).pull2 z = 0 := by
  have hT : ∀ P : Pt s, IsTriv s ((toPC s).G.obj P) := fun P => rfl
  let n : CoefMap (RingHom.id R) ((IsTriv s).ι ⋙ O (dp0 R) s) (FP s) :=
    { G := ObjectProperty.lift (IsTriv s) (toPC s).G hT
      α := fun P => RingHom.id P.B
      naturality := fun φ b => (toPC s).naturality φ b
      smul := fun P r b => (toPC s).smul P r b }
  have he : toPC s = (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).comp n := rfl
  rw [he, CoefMap.pullCohomologyTwo_comp, GlobalTheory.CompanionTheory.PdChern.restrict_triv_eq_zero R X s L hL z hz, map_zero]

variable {W Y : Scheme.{0}} {sW : W ⟶ Sp R} {sY : Y ⟶ Sp R} {p : W ⟶ Y}
  (hp : p ≫ sY = sW ≫ spMap (RingHom.id R)) {n : ℕ} (α : Fin n → Z1 (FP sW)) (β : Fin n → Z1 (FP sY))
  (f : C1 (FP sW))

def Bounds : Prop := ∀ (S S' S'' : Pt sW) (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S ⟶ S''),
  (∀ b, χ.ρ b = ψ.ρ (φ.ρ b)) →
    ψ.ρ (v1 f φ) - v1 f χ + v1 f ψ = ∑ k, ψ.ρ (v1 (α k).1 φ) * v1 (β k).1 (pushHom hp ψ)

theorem exists_bounds
    (h : ∑ k, cup (FP sW) (H1.mk _ (α k)) (pullP hp (H1.mk _ (β k))) = 0) : ∃ f, Bounds hp α β f := by
  have hpull : ∀ k, pullP hp (H1.mk _ (β k)) = H1.mk (FP sW) ((pushC hp).pullbackOneCocycle (β k)) :=
    fun k => CoefMap.pullCohomologyOne_class _ _
  simp only [hpull, cup_mk] at h
  rw [← map_sum] at h
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.mp h
  refine ⟨f, fun S S' S'' φ ψ χ e => ?_⟩
  have hχ : χ = φ ≫ ψ := by
    obtain ⟨ρχ, hχpt⟩ := χ
    have hρ : ρχ = (φ ≫ ψ).ρ := AlgHom.ext e
    subst hρ
    rfl
  subst hχ
  have hz := congrFun (congrFun (congrFun (congrFun (congrFun hf S) S') S'') φ) ψ
  simp only [d1_apply, Submodule.coe_sum, Finset.sum_apply, cupZ_apply, CoefMap.pullCocycleOne_apply] at hz
  exact hz

variable {T : Pt sY} {X' : Scheme.{0}} {s' : X' ⟶ Sp T.B} {w : X' ⟶ W}
  (hw : w ≫ sW = s' ≫ spMap (algebraMap R T.B)) (hw₂ : w ≫ p = s' ≫ T.x)

def eHom (S : Pt s') : T ⟶ pushPt hp (pushPt hw S) where
  ρ := { algebraMap T.B S.B with commutes' := fun _ ↦ rfl }
  pt := by
    change spMap (algebraMap T.B S.B) ≫ T.x = (S.x ≫ w) ≫ p
    rw [← S.w, Category.assoc, Category.assoc, hw₂]

variable {α β f}

def hZ (H : Bounds hp α β f) : Z1 (FP s') :=
  ⟨fun S S' φ ↦ (show S'.B from v1 f (pushHom hw φ)) +
      ∑ k, (show S'.B from v1 (α k).1 (pushHom hw φ)) * (show S'.B from v1 (β k).1 (eHom hp hw hw₂ S')),
    fun S S' S'' φ ψ ↦ key₁ (ψ.ρ : S'.B →+* S''.B) _ _ _ _ _ _ _ _ _
      (H _ _ _ (pushHom hw φ) (pushHom hw ψ) (pushHom hw (φ ≫ ψ)) fun _ ↦ rfl)
      (fun k ↦ cocycle_value_comp (α k) (pushHom hw φ) (pushHom hw ψ) (pushHom hw (φ ≫ ψ)) fun _ ↦ rfl)
      (fun k ↦ cocycle_value_comp (β k) (eHom hp hw hw₂ S') (pushHom hp (pushHom hw ψ)) (eHom hp hw hw₂ S'')
        fun b ↦ (ψ.ρ.commutes b).symm)⟩

theorem hZ_rel (H : Bounds hp α β f) {T' : Pt sY} (τ : T ⟶ T') {X'' : Scheme.{0}} {s'' : X'' ⟶ Sp T'.B}
    {w' : X'' ⟶ W} (hw' : w' ≫ sW = s'' ≫ spMap (algebraMap R T'.B)) (hw₂' : w' ≫ p = s'' ≫ T'.x)
    {j : X'' ⟶ X'} (hj : j ≫ s' = s'' ≫ spMap (τ.ρ : T.B →+* T'.B)) (e : j ≫ w = w') :
    H1.mk _ (hZ hp hw' hw₂' H) - pullP hj (H1.mk _ (hZ hp hw hw₂ H)) +
      ∑ k, v1 (β k).1 τ • pullP hj (pullP hw (H1.mk _ (α k))) = 0 := by
  have e1 : ∀ z, pullP hj (H1.mk (FP s') z) = H1.mk (FP s'') ((pushC hj).pullbackOneCocycle z) :=
    fun z => CoefMap.pullCohomologyOne_class _ _
  have e2 : ∀ z, pullP hw (H1.mk (FP sW) z) = H1.mk (FP s') ((pushC hw).pullbackOneCocycle z) :=
    fun z => CoefMap.pullCohomologyOne_class _ _
  simp only [e1, e2]
  simp only [← LinearMap.map_smul, ← map_sum, ← map_sub, ← map_add]
  rw [H1.mk_eq_zero]
  let u : ∀ S : Pt s'', pushPt hw (pushPt hj S) ⟶ pushPt hw' S := fun S =>
    { ρ := { RingHom.id S.B with commutes' := fun r => congrArg (algebraMap T'.B S.B) (τ.ρ.commutes r) }
      pt := by
        show Spec.map (CommRingCat.ofHom (RingHom.id S.B)) ≫ (S.x ≫ j) ≫ w = S.x ≫ w'
        rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.assoc, e] }
  refine ⟨fun S => v1 f (u S) + ∑ k, v1 (α k).1 (u S) * v1 (β k).1 (eHom hp hw' hw₂' S), ?_⟩
  funext S S' φ
  rw [amitsur_d0_apply]
  have hR : (↑(hZ hp hw' hw₂' H - (pushC hj).pullbackOneCocycle (hZ hp hw hw₂ H) +
      ∑ x : Fin n, v1 (β x).1 τ • (pushC hj).pullbackOneCocycle ((pushC hw).pullbackOneCocycle (α x))) : C1 (FP s'')) S S' φ
      = (v1 f (pushHom hw' φ) + ∑ k, v1 (α k).1 (pushHom hw' φ) * v1 (β k).1 (eHom hp hw' hw₂' S'))
        - (v1 f (pushHom hw (pushHom hj φ)) + ∑ k, v1 (α k).1 (pushHom hw (pushHom hj φ)) *
            v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S')))
        + ∑ k, algebraMap T'.B S'.B (v1 (β k).1 τ) * v1 (α k).1 (pushHom hw (pushHom hj φ)) := by
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def]
    rfl
  rw [hR]
  rw [map_add, map_sum]
  simp only [map_mul]
  have B1 : mp (FP s'') φ (v1 f (u S)) - v1 f (u S ≫ pushHom hw' φ) + v1 f (pushHom hw' φ)
      = ∑ k, mp (FP s'') φ (v1 (α k).1 (u S)) * v1 (β k).1 (pushHom hp (pushHom hw' φ)) :=
    H _ _ _ (u S) (pushHom hw' φ) (u S ≫ pushHom hw' φ) (fun _ => rfl)
  have B2 : v1 f (pushHom hw (pushHom hj φ)) - v1 f (u S ≫ pushHom hw' φ) + v1 f (u S')
      = ∑ k, v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (pushHom hp (u S')) :=
    H _ _ _ (pushHom hw (pushHom hj φ)) (u S') (u S ≫ pushHom hw' φ) (fun _ => rfl)
  have Ek : ∀ k, v1 (α k).1 (u S') * v1 (β k).1 (eHom hp hw' hw₂' S')
      - mp (FP s'') φ (v1 (α k).1 (u S)) * mp (FP s'') φ (v1 (β k).1 (eHom hp hw' hw₂' S))
      - v1 (α k).1 (pushHom hw' φ) * v1 (β k).1 (eHom hp hw' hw₂' S')
      + v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S'))
      - algebraMap T'.B S'.B (v1 (β k).1 τ) * v1 (α k).1 (pushHom hw (pushHom hj φ))
      - mp (FP s'') φ (v1 (α k).1 (u S)) * v1 (β k).1 (pushHom hp (pushHom hw' φ))
      + v1 (α k).1 (pushHom hw (pushHom hj φ)) * v1 (β k).1 (pushHom hp (u S')) = 0 := by
    intro k
    have A1 : v1 (α k).1 (u S ≫ pushHom hw' φ)
        = mp (FP s'') φ (v1 (α k).1 (u S)) + v1 (α k).1 (pushHom hw' φ) :=
      cocycle_value_comp (α k) (u S) (pushHom hw' φ) (u S ≫ pushHom hw' φ) (fun _ => rfl)
    have A2 : v1 (α k).1 (u S ≫ pushHom hw' φ)
        = v1 (α k).1 (pushHom hw (pushHom hj φ)) + v1 (α k).1 (u S') :=
      cocycle_value_comp (α k) (pushHom hw (pushHom hj φ)) (u S') (u S ≫ pushHom hw' φ) (fun _ => rfl)
    have C1 : v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S'))
        = algebraMap T'.B S'.B (v1 (β k).1 τ) + v1 (β k).1 (eHom hp hw' hw₂' S') :=
      cocycle_value_comp (β k) τ (eHom hp hw' hw₂' S') (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S')) (fun _ => rfl)
    have C2 : v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S'))
        = v1 (β k).1 (eHom hp hw hw₂ (pushPt hj S')) + v1 (β k).1 (pushHom hp (u S')) :=
      cocycle_value_comp (β k) (eHom hp hw hw₂ (pushPt hj S')) (pushHom hp (u S'))
        (eHom hp hw hw₂ (pushPt hj S') ≫ pushHom hp (u S')) (fun _ => rfl)
    have D : v1 (β k).1 (eHom hp hw' hw₂' S')
        = mp (FP s'') φ (v1 (β k).1 (eHom hp hw' hw₂' S)) + v1 (β k).1 (pushHom hp (pushHom hw' φ)) :=
      cocycle_value_comp (β k) (eHom hp hw' hw₂' S) (pushHom hp (pushHom hw' φ)) (eHom hp hw' hw₂' S')
        (fun b => (φ.ρ.commutes b).symm)
    linear_combination (v1 (β k).1 (eHom hp hw' hw₂' S') : S'.B) * (A1 - A2)
      + (mp (FP s'') φ (v1 (α k).1 (u S)) : S'.B) * D
      + (v1 (α k).1 (pushHom hw (pushHom hj φ)) : S'.B) * (C1 - C2)
  have hs := Finset.sum_eq_zero (fun k (_ : k ∈ Finset.univ) => Ek k)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  linear_combination B2 - B1 + hs

end Cochain

section Fun

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem exists_fun (hF : AbelianDeRham.Free) (hB : AbelianDeRham.BaseChange) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {x : HdR A} (hx : x ∈ Fil A) {C : Type} [CommRing C] [Algebra R C]
    {A' : Over (Sp C)} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap R C)) φ)
    (hS : Function.Surjective (toP (A'.hom ≫ 𝟙 _)))
    (hφ : φ ≫ A.hom ≫ 𝟙 _ = (A'.hom ≫ 𝟙 _) ≫ spMap (algebraMap R C)) :
    (∃ X : H1OnPoints (A'.hom ≫ 𝟙 _) →ₗ[C] C, ∀ c : primDR A, X (pullP hφ (toP _ c.1)) = algebraMap R C (x c)) ∧
      ∀ u : H1OnPoints (A'.hom ≫ 𝟙 _), u ∈ Submodule.span C (Set.range fun c : primDR A ↦ pullP hφ (toP _ c.1)) := by
  obtain ⟨hbc, hF1⟩ := hB R A g hA hg C A' φ h
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' : SmoothOfRelativeDimension g A'.hom := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback h.1 hg
  have hall : prim (dp0 C) (𝟙 (Sp C)) A' = ⊤ := (hF C A' g hA' hg').1
  set m := AbelianDeRham.bcMor h with hm
  have hpt : ∀ c : primDR A, pullP hφ (toP _ c.1) = toP _ (m.pull c).1 := fun c => pullP_toP m.isMor c.1
  set x' := hbc.bcMap x with hxe
  have hx' : ∀ c, x' (m.pull c) = algebraMap R C (x c) := hbc.corr_iff.mpr rfl
  let e : FirstDeRham (A'.hom ≫ 𝟙 _) →ₗ[C] primDR A' :=
    LinearMap.codRestrict (primDR A') LinearMap.id (fun d => by
      show d ∈ prim (dp0 C) (𝟙 (Sp C)) A'
      rw [hall]
      exact Submodule.mem_top)
  have hle : Submodule.span C (m.pull '' (PrimitiveSubmodule A)) ≤ LinearMap.ker x' := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hx', (Submodule.mem_dualAnnihilator x).mp hx c hc, map_zero]
  obtain ⟨X, hX⟩ := exists_factor' (toP (A'.hom ≫ 𝟙 _)) hS (x'.comp e) (by
    intro d hd
    rw [toP_eq_zero_iff] at hd
    have hmem : e d ∈ PrimitiveSubmodule A' := hd
    rw [hF1] at hmem
    exact hle hmem)
  refine ⟨⟨X, fun c => ?_⟩, fun u => ?_⟩
  · rw [hpt, hX]
    have he : e (m.pull c).1 = m.pull c := Subtype.ext rfl
    simp only [LinearMap.comp_apply, he, hx']
  · obtain ⟨d, rfl⟩ := hS u
    obtain ⟨t, ht⟩ := hbc.2 (e d)
    have hd : d = (liftSemi m.pull t).1 := by rw [ht]; rfl
    rw [hd]
    clear ht hd
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      have hl : liftSemi m.pull (r ⊗ₜ c) = r • m.pull c := by
        first
        | rfl
        | simp [liftSemi]
      rw [hl, Submodule.coe_smul, map_smul, ← hpt]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    | add a b ha hb =>
      rw [map_add, Submodule.coe_add, map_add]
      exact Submodule.add_mem _ ha hb

end Fun

open scoped CategoryTheory.Obj in
theorem exists_grpPullback {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    ∃ (G' : Over S') (_ : GrpObj G') (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ := by
  letI : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  letI iP : GrpObj (Over.mk (Limits.pullback.snd G.hom f)) := Over.grpObjMkPullbackSnd
  refine ⟨Over.mk (Limits.pullback.snd G.hom f), iP, Limits.pullback.fst G.hom f,
    ⟨IsPullback.of_hasPullback _ _, ?_⟩⟩
  intro T x y x₀ y₀ hx hy
  rw [Hom.mul_def, Hom.mul_def, Over.grpObjMkPullbackSnd_mul]
  simp only [Over.comp_left, Category.assoc]
  have hm : ((Over.pullback f).map (μ : Over.mk G.hom ⊗ Over.mk G.hom ⟶ Over.mk G.hom)).left ≫
      Limits.pullback.fst G.hom f = Limits.pullback.fst _ f ≫ (μ : Over.mk G.hom ⊗ Over.mk G.hom ⟶ Over.mk G.hom).left := by
    simp only [Over.pullback_map_left]
    exact Limits.pullback.lift_fst _ _ _
  rw [hm]
  have key : (lift x y).left ≫ (Functor.LaxMonoidal.μ (Over.pullback f) (Over.mk G.hom) (Over.mk G.hom)).left ≫
      Limits.pullback.fst _ f = (lift x₀ y₀).left := by
    apply Limits.pullback.hom_ext
    · simp
      erw [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst]
      exact hx.symm
    · simp
      erw [Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd]
      exact hy.symm
  rw [← key]
  simp only [Category.assoc]

set_option maxHeartbeats 1000000 in
theorem orth_of_surj (hF : AbelianDeRham.Free) (hB : AbelianDeRham.BaseChange) {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hS : ∀ (C : Type) [CommRing C] [Algebra R C] (A' : Over (Sp C)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap R C)) φ → Function.Surjective (toP (A'.hom ≫ 𝟙 _))) {P : LB (A ⊗ B).left} (hP : P.IsLB) {φ : HdR A →ₗ[R] HdR B →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) A B P φ) : ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro x hx y hy
  obtain ⟨n, a, b, hCh, hform⟩ := hφ
  rw [hform]
  have hp : (snd A B).left ≫ B.hom ≫ 𝟙 (Sp R) = ((A ⊗ B).hom ≫ 𝟙 (Sp R)) ≫ spMap (RingHom.id R) := by
    rw [← Category.assoc, Over.w]
    simp [spMap]
  have hq : (fst A B).left ≫ A.hom ≫ 𝟙 (Sp R) = ((A ⊗ B).hom ≫ 𝟙 (Sp R)) ≫ spMap (RingHom.id R) := by
    rw [← Category.assoc, Over.w]
    simp [spMap]
  have h0 := pull2_chern_class_eq_zero hP hCh
  rw [map_sum] at h0
  simp only [CoefMap.pullCohomologyTwo_cup] at h0
  have eA : ∀ k, (toPC _).pull1 (pullOver (dp0 R) (𝟙 (Sp R)) (fst A B) (a k).1) = pullP hq (toP _ (a k).1) :=
    fun k => (pullP_toP (IsMor.of_dividedPowersZeroIdeal (dp0 R) hq) _).symm
  have eB : ∀ k, (toPC _).pull1 (pullOver (dp0 R) (𝟙 (Sp R)) (snd A B) (b k).1) = pullP hp (toP _ (b k).1) :=
    fun k => (pullP_toP (IsMor.of_dividedPowersZeroIdeal (dp0 R) hp) _).symm
  simp only [eA, eB] at h0
  obtain ⟨α, hα⟩ : ∃ α : Fin n → Z1 (FP ((A ⊗ B).hom ≫ 𝟙 (Sp R))),
      ∀ k, H1.mk _ (α k) = pullP hq (toP _ (a k).1) :=
    ⟨fun k => (H1.mk_surjective _ (pullP hq (toP _ (a k).1))).choose,
      fun k => (H1.mk_surjective _ (pullP hq (toP _ (a k).1))).choose_spec⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin n → Z1 (FP (B.hom ≫ 𝟙 (Sp R))), ∀ k, H1.mk _ (β k) = toP _ (b k).1 :=
    ⟨fun k => (H1.mk_surjective _ (toP _ (b k).1)).choose,
      fun k => (H1.mk_surjective _ (toP _ (b k).1)).choose_spec⟩
  simp only [← hα, ← hβ] at h0
  obtain ⟨f, H⟩ := exists_bounds hp α β h0
  have hex : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), ∃ (A' : Over (Sp T.B)) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsGrpPullback A' A (spMap (algebraMap R T.B)) φ := fun T => exists_grpPullback A _
  choose A' iA φT hT using hex
  have hcond : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), φT T ≫ A.hom = ((A' T).hom ≫ T.x) ≫ B.hom := by
    intro T
    rw [(hT T).1.w, Category.assoc]
    congr 1
    simpa using T.w.symm
  let w : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), (A' T).left ⟶ (A ⊗ B).left :=
    fun T => Limits.pullback.lift (φT T) ((A' T).hom ≫ T.x) (hcond T)
  have hwf : ∀ T, w T ≫ (fst A B).left = φT T := fun T => Limits.pullback.lift_fst _ _ _
  have hws : ∀ T, w T ≫ (snd A B).left = (A' T).hom ≫ T.x := fun T => Limits.pullback.lift_snd _ _ _
  have hw : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), w T ≫ (A ⊗ B).hom ≫ 𝟙 (Sp R) =
      ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ spMap (algebraMap R T.B) := by
    intro T
    rw [← Over.w (fst A B), ← Category.assoc, ← Category.assoc, hwf, (hT T).1.w]
    simp
  have hw₂ : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), w T ≫ (snd A B).left = ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ T.x := by
    intro T
    rw [hws]
    simp
  have hφ' : ∀ T : Pt (B.hom ≫ 𝟙 (Sp R)), φT T ≫ A.hom ≫ 𝟙 (Sp R) =
      ((A' T).hom ≫ 𝟙 (Sp T.B)) ≫ spMap (algebraMap R T.B) := by
    intro T
    simpa using (hT T).1.w
  have hE := fun T => exists_fun hF hB hA hg hx (hT T) (hS T.B (A' T) (φT T) (hT T)) (hφ' T)
  choose X hXc using fun T => (hE T).1
  let g : C0 (FP (B.hom ≫ 𝟙 (Sp R))) := fun T => X T (H1.mk _ (hZ hp (hw T) (hw₂ T) H))
  have key : ∀ (T T' : Pt (B.hom ≫ 𝟙 (Sp R))) (τ : T ⟶ T'),
      g T' - τ.ρ (g T) + ∑ k, v1 (β k).1 τ * algebraMap R T'.B (x (a k)) = 0 := by
    intro T T' τ
    have hsp : spMap (algebraMap R T'.B) = spMap (τ.ρ : T.B →+* T'.B) ≫ spMap (algebraMap R T.B) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      exact (τ.ρ.commutes r).symm
    have hjc : φT T' ≫ A.hom = ((A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B)) ≫ spMap (algebraMap R T.B) := by
      rw [(hT T').1.w, Category.assoc, hsp]
    let j : (A' T').left ⟶ (A' T).left := (hT T).1.lift (φT T') ((A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B)) hjc
    have hjf : j ≫ φT T = φT T' := (hT T).1.lift_fst _ _ _
    have hjs : j ≫ (A' T).hom = (A' T').hom ≫ spMap (τ.ρ : T.B →+* T'.B) := (hT T).1.lift_snd _ _ _
    have hj : j ≫ (A' T).hom ≫ 𝟙 (Sp T.B) = ((A' T').hom ≫ 𝟙 (Sp T'.B)) ≫ spMap (τ.ρ : T.B →+* T'.B) := by
      rw [Category.comp_id (A' T).hom, Category.comp_id (A' T').hom, hjs]
    have he : j ≫ w T = w T' := by
      apply Limits.pullback.hom_ext
      · change (j ≫ w T) ≫ (fst A B).left = w T' ≫ (fst A B).left
        rw [Category.assoc, hwf, hwf, hjf]
      · change (j ≫ w T) ≫ (snd A B).left = w T' ≫ (snd A B).left
        rw [Category.assoc, hws, hws, ← Category.assoc, hjs, Category.assoc, τ.pt]
    have hrel := hZ_rel hp (hw T) (hw₂ T) H τ (hw T') (hw₂ T') hj he
    have hi : ∀ u, X T' (pullP hj u) = τ.ρ (X T u) := by
      intro u
      refine Submodule.span_induction (p := fun u _ => X T' (pullP hj u) = τ.ρ (X T u)) ?_ ?_ ?_ ?_ ((hE T).2 u)
      · rintro _ ⟨c, rfl⟩
        rw [pullP_pullP (hφ' T) hj (hφ' T') (fun r => τ.ρ.commutes r) hjf, hXc, hXc]
        exact (τ.ρ.commutes _).symm
      · simp
      · intro u v _ _ hu hv
        simp only [map_add, hu, hv]
      · intro c u _ hu
        simp only [map_smulₛₗ, smul_eq_mul, map_mul, hu]
        rfl
    have hii : ∀ k, X T' (pullP hj (pullP (hw T) (H1.mk _ (α k)))) = algebraMap R T'.B (x (a k)) := by
      intro k
      rw [hα k, pullP_pullP hq (hw T) (hφ' T) (fun r => rfl) (hwf T),
        pullP_pullP (hφ' T) hj (hφ' T') (fun r => τ.ρ.commutes r) hjf, hXc]
    have h1 := congrArg (X T') hrel
    simp only [map_add, map_sub, map_sum, map_smul, smul_eq_mul, hii, map_zero] at h1
    simp only [hi] at h1
    exact h1
  have hcob : ∃ g : C0 (FP (B.hom ≫ 𝟙 (Sp R))), d0 _ g = ↑(∑ k, x (a k) • β k) := by
    refine ⟨-g, ?_⟩
    funext T T' τ
    rw [amitsur_d0_apply]
    show -g T' - τ.ρ (-g T) = v1 (∑ k, x (a k) • β k).1 τ
    rw [cocycle_value_sum, map_neg]
    have hs : ∑ k, algebraMap R T'.B (x (a k)) * v1 (β k).1 τ = ∑ k, v1 (β k).1 τ * algebraMap R T'.B (x (a k)) :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hs]
    linear_combination -key T T' τ
  have hmk : H1.mk _ (∑ k, x (a k) • β k) = 0 := H1.mk_eq_zero.mpr hcob
  have hc : toP (B.hom ≫ 𝟙 (Sp R)) (∑ k, x (a k) • (b k).1) = 0 := by
    simpa only [map_sum, map_smul, hβ] using hmk
  have hF1 := (toP_eq_zero_iff _).mp hc
  have hcF : (∑ k, x (a k) • b k) ∈ PrimitiveSubmodule B := by
    show (primDR B).subtype (∑ k, x (a k) • b k) ∈ F1 _
    simpa using hF1
  have hy0 := (Submodule.mem_dualAnnihilator _).mp hy _ hcF
  simpa [map_sum, map_smul] using hy0

end CrystallinePoints.Pd
