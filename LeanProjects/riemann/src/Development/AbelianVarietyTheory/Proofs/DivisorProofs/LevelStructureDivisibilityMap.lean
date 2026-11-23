import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairingFunctorialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOfLocalPrime
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.LevMap

section Push

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem comp_pow_of_isMonHom (f : G ⟶ G) [IsMonHom f] {Z : Over (Sp R)} (t : Z ⟶ G) (n : ℕ) :
    (t ≫ f) ^ n = (t ^ n) ≫ f := by
  induction n with
  | zero => simp only [pow_zero]; exact (MonObj.one_comp f).symm
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

def torsPush {N N' : ℕ} (h : N ∣ N') (f : G ⟶ G) [IsMonHom f] {B : Type} [CommRing B] [Algebra R B]
    (z : Tors G N B) : Tors G N' B :=
  ⟨z.1 ≫ f, by obtain ⟨m, rfl⟩ := h; rw [pow_mul, comp_pow_of_isMonHom, z.2, MonObj.one_comp, one_pow]⟩

variable {N N' : ℕ} (h : N ∣ N') (f : G ⟶ G) [IsMonHom f]

@[simp] theorem torsPush_val {B : Type} [CommRing B] [Algebra R B] (z : Tors G N B) :
    (torsPush h f z).1 = z.1 ≫ f := rfl

theorem torsPush_mul {B : Type} [CommRing B] [Algebra R B] (x y : Tors G N B) :
    torsPush h f (x * y) = torsPush h f x * torsPush h f y :=
  Subtype.ext (by simp [MonObj.mul_comp])

theorem torsPush_one {B : Type} [CommRing B] [Algebra R B] :
    torsPush h f (1 : Tors G N B) = 1 :=
  Subtype.ext (by simp [MonObj.one_comp])

theorem torsPush_map {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (z : Tors G N B) : torsPush h f (torsMap φ z) = torsMap φ (torsPush h f z) :=
  Subtype.ext (by simp)

end Push

section Pt

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}
  {A : Type} [CommRing A] [HopfAlgebra R A]

theorem antipode_conv_mul {B : Type} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) :
    toConv (f.comp (HopfAlgebra.antipodeAlgHom R A)) * toConv f = 1 := by
  have H : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f f) =
      f.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
  trans toConv <| ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f f)).comp
    ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
  · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f f),
      ← Algebra.TensorProduct.map_comp]; rfl
  rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
  change f.toLinearMap.comp (toConv (HopfAlgebra.antipode R (A := A)) * toConv LinearMap.id).ofConv =
    ofConv (1 : WithConv <| A →ₗ[R] B)
  rw [LinearMap.antipode_mul_id]
  ext
  simp

theorem pt_one (θ : TorsPt G N A) (B : Type) [CommRing B] [Algebra R B] : toConv (θ.pt B 1) = 1 := by
  have h1 : toConv (θ.pt B 1) * toConv (θ.pt B 1) = toConv (θ.pt B 1) := by
    rw [← θ.mul, _root_.mul_one]
  have h2 := congrArg (fun F => toConv ((θ.pt B 1).comp (HopfAlgebra.antipodeAlgHom R A)) * F) h1
  simp only [← _root_.mul_assoc, antipode_conv_mul, _root_.one_mul] at h2
  exact h2

theorem pt_one_apply (θ : TorsPt G N A) (B : Type) [CommRing B] [Algebra R B] (x : A) :
    θ.pt B 1 x = algebraMap R B (counit x) := by
  have := congrArg (fun F : WithConv (A →ₐ[R] B) => (ofConv F) x) (pt_one θ B)
  simpa [AlgHom.convOne_def] using this

end Pt

end GlobalTheory.GroupBplus.Aff.LevMap

namespace GlobalTheory.GroupBplus.Aff.LevMap

section Main

variable {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K]
  [Algebra R K] [IsFractionRing R K] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N N' : ℕ}
  {A : Type} [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A]
  {A' : Type} [CommRing A'] [HopfAlgebra R A'] [IsCocomm R A'] [Module.Finite R A'] [Module.Projective R A']

include R K in
theorem eq_of_pts {θ : TorsPt G N A} (hθ : IsLevel K θ) {x y : A}
    (hxy : ∀ z : Tors G N K, θ.pt K z x = θ.pt K z y) : x = y := by
  rw [← sub_eq_zero]
  apply (GlobalTheory.T.finite_hopf_points_separate R K A).2.1
  intro ψ
  obtain ⟨z, rfl⟩ := hθ.gen.2 ψ
  rw [map_sub, hxy, sub_self]

theorem exists_val (hG : IsSemiAbelian G) (hN : N ≠ 0) (h : N ∣ N') (f : G ⟶ G) [IsMonHom f]
    (θ : TorsPt G N A) (θ' : TorsPt G N' A') (hθ : IsLevel K θ) (a' : A') :
    ∃ a : A, ∀ z : Tors G N K, θ.pt K z a = θ'.pt K (torsPush h f z) a' := by
  classical
  haveI : Finite (A →ₐ[R] K) := (GlobalTheory.T.finite_hopf_points_separate R K A).1
  haveI : Finite (A' →ₐ[R] K) := (GlobalTheory.T.finite_hopf_points_separate R K A').1
  let e := Equiv.ofBijective _ hθ.gen
  have he : ∀ z, e.symm (θ.pt K z) = z := fun z => e.symm_apply_apply z
  let fn : (A →ₐ[R] K) → K := fun ψ => θ'.pt K (torsPush h f (e.symm ψ)) a'
  have hloc : ∀ (P : Ideal A) [P.IsPrime], (1 : A) ∉ P → ∃ c : Localization.AtPrime P,
      ∀ ψ : Localization.AtPrime P →ₐ[R] K,
        ψ c = fn (ψ.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime P))) := by
    intro P _ _
    obtain ⟨z, s, hzs⟩ := GlobalTheory.T.level_structure_local_points R K G hG N hN A θ hθ (Localization.AtPrime P)
      (IsScalarTower.toAlgHom R A _)
    obtain ⟨w, hw⟩ := hθ.gen.2 ((Algebra.ofId R K).comp s)
    obtain ⟨s', hs'⟩ := GlobalTheory.finiteAlg_fieldPoint_factors_through_base R K A' (GlobalTheory.T.finite_hopf_points_separate R K A').2.1 K
      (θ'.pt K (torsPush h f w))
    let c0 : A' →ₐ[R] Localization.AtPrime P :=
      ofConv (toConv (θ'.pt (Localization.AtPrime P) (torsPush h f z)) *
        toConv ((Algebra.ofId R (Localization.AtPrime P)).comp s'))
    refine ⟨c0 a', fun ψ => ?_⟩
    have hψid : ψ.comp (Algebra.ofId R (Localization.AtPrime P)) = Algebra.ofId R K :=
      AlgHom.ext fun r => ψ.commutes r
    have L : ψ.comp c0 =
        θ'.pt K (torsPush h f (torsMap ψ z * w)) := by
      rw [AlgHom.comp_convMul_distrib, ofConv_toConv, ofConv_toConv, ← θ'.nat, ← torsPush_map,
        ← AlgHom.comp_assoc, hψid, ← hs', ← θ'.mul, torsPush_mul, ofConv_toConv]
    have Rt : ψ.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime P)) = θ.pt K (torsMap ψ z * w) := by
      rw [← ofConv_toConv (IsScalarTower.toAlgHom R A (Localization.AtPrime P)), hzs,
        AlgHom.comp_convMul_distrib, ofConv_toConv, ofConv_toConv, ← θ.nat, ← AlgHom.comp_assoc, hψid, ← hw,
        ← θ.mul, ofConv_toConv]
    rw [Rt]
    rw [← AlgHom.comp_apply, L]
    simp only [fn, he]
  obtain ⟨k, a, ha⟩ := GlobalTheory.AlgPointsLocal.exists_pow_mul_of_locally_integral R K A 1 fn hloc
  refine ⟨a, fun z => ?_⟩
  rw [ha, map_one, one_pow, _root_.one_mul]
  simp only [fn, he]

end Main

end GlobalTheory.GroupBplus.Aff.LevMap

namespace GlobalTheory.GroupBplus.Aff.LevMap

theorem existsUnique_bialgHom_of_levels : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N N' : ℕ), N ≠ 0 → N ∣ N' → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (A' : Type) [CommRing A'] [HopfAlgebra R A'] [IsCocomm R A'] [Module.Finite R A'] [Module.Projective R A'] (θ : TorsPt G N A) (θ' : TorsPt G N' A'), IsLevel K θ → IsLevel K θ' → ∀ f : G ⟶ G, IsMonHom f → ∃! g : A' →ₐc[R] A, ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (z' : Tors G N' B), z'.1 = z.1 ≫ f → θ'.pt B z' = (θ.pt B z).comp (g : A' →ₐ[R] A) := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N N' hN h A _ _ _ _ _ A' _ _ _ _ _ θ θ' hθ hθ' f hf
  haveI : IsMonHom f := hf
  classical
  choose gfun hg using exists_val (K := K) hG hN h f θ θ' hθ
  let gA : A' →ₐ[R] A :=
    { toFun := gfun
      map_one' := eq_of_pts (K := K) hθ fun z => by rw [hg, map_one, map_one]
      map_mul' := fun x y => eq_of_pts (K := K) hθ fun z => by rw [hg, map_mul, map_mul, hg, hg]
      map_zero' := eq_of_pts (K := K) hθ fun z => by rw [hg, map_zero, map_zero]
      map_add' := fun x y => eq_of_pts (K := K) hθ fun z => by rw [hg, map_add, map_add, hg, hg]
      commutes' := fun r => eq_of_pts (K := K) hθ fun z => by rw [hg, AlgHom.commutes, AlgHom.commutes] }
  have hgA : ∀ (a' : A') (z : Tors G N K), θ.pt K z (gA a') = θ'.pt K (torsPush h f z) a' := hg
  have hB : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (a' : A'),
      θ'.pt B (torsPush h f z) a' = θ.pt B z (gA a') := by
    intro B _ _ z a'
    have := GlobalTheory.T.torsion_pairing_functorial R K G hG N N hN hN
      (fun B _ _ x _ => θ'.pt B (torsPush h f x) a' - θ.pt B x (gA a'))
      (fun B C _ _ _ _ φ x y => by simp only [torsPush_map, θ'.nat, θ.nat, AlgHom.comp_apply, map_sub])
      (fun x y => by simp only [hgA, sub_self]) B z z
    exact sub_eq_zero.mp this
  have hcounit : (counitAlgHom R A).comp gA = counitAlgHom R A' := by
    ext a'
    apply IsFractionRing.injective R K
    change algebraMap R K (counit (gA a')) = algebraMap R K (counit a')
    rw [← pt_one_apply θ K, hgA, torsPush_one, pt_one_apply]
  have hcomul : (Algebra.TensorProduct.map gA gA).comp (comulAlgHom R A') = (comulAlgHom R A).comp gA := by
    ext a'
    change Algebra.TensorProduct.map gA gA (comul a') = comul (gA a')
    rw [← sub_eq_zero]
    apply (GlobalTheory.T.finite_hopf_points_separate R K (A ⊗[R] A)).2.1
    intro ψ
    let ψ1 : A →ₐ[R] K := ψ.comp Algebra.TensorProduct.includeLeft
    let ψ2 : A →ₐ[R] K := ψ.comp Algebra.TensorProduct.includeRight
    have hψ : ψ = (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map ψ1 ψ2) := by
      apply Algebra.TensorProduct.ext <;> ext x <;> simp [ψ1, ψ2, ← Algebra.TensorProduct.one_def]
    clear_value ψ1 ψ2
    obtain ⟨z1, hz1⟩ := hθ.gen.2 ψ1
    obtain ⟨z2, hz2⟩ := hθ.gen.2 ψ2
    have e1 : ψ1.comp gA = θ'.pt K (torsPush h f z1) :=
      AlgHom.ext fun a' => by rw [AlgHom.comp_apply, ← hz1, hgA]
    have e2 : ψ2.comp gA = θ'.pt K (torsPush h f z2) :=
      AlgHom.ext fun a' => by rw [AlgHom.comp_apply, ← hz2, hgA]
    have E1 : ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map ψ1 ψ2))
        (Algebra.TensorProduct.map gA gA (comul a')) =
        (ofConv (toConv (θ'.pt K (torsPush h f z1)) * toConv (θ'.pt K (torsPush h f z2))) : A' →ₐ[R] K) a' := by
      rw [← e1, ← e2, AlgHom.convMul_def, ofConv_toConv, Algebra.TensorProduct.map_comp]; rfl
    have E2 : ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map ψ1 ψ2)) (comul (gA a')) =
        (ofConv (toConv ψ1 * toConv ψ2) : A →ₐ[R] K) (gA a') := by
      rw [AlgHom.convMul_def, ofConv_toConv]; rfl
    rw [map_sub, sub_eq_zero, hψ, E1, E2, ← hz1, ← hz2, ← θ.mul, ← θ'.mul, ← torsPush_mul, ofConv_toConv,
      ofConv_toConv, hgA]
  let gB : A' →ₐc[R] A := BialgHom.ofAlgHom gA hcounit hcomul
  refine ⟨gB, fun B _ _ z z' hz' => ?_, fun g' hg' => ?_⟩
  · have hzz : z' = torsPush h f z := Subtype.ext hz'
    subst hzz
    ext a'
    exact hB B z a'
  · ext a'
    apply eq_of_pts (K := K) hθ
    intro z
    have := congrArg (fun F : A' →ₐ[R] K => F a') (hg' K z (torsPush h f z) rfl)
    exact this.symm.trans (hgA a' z).symm

end GlobalTheory.GroupBplus.Aff.LevMap
