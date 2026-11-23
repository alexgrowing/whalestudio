import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt GlobalTheory.CartierDual WithConv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilHom

section Alg

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

section Values

variable [Algebra R A] [Algebra R B] {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]

def ev (x : A →ₐ[R] D) (z : B →ₐ[R] D) : A ⊗[R] B →ₐ[R] D :=
  Algebra.TensorProduct.lift x z fun _ _ => Commute.all _ _

@[simp] theorem ev_tmul (x : A →ₐ[R] D) (z : B →ₐ[R] D) (a : A) (b : B) : ev x z (a ⊗ₜ b) = x a * z b := rfl

theorem ev_comp_left (x : A →ₐ[R] D) (z : B →ₐ[R] D) : (ev x z).comp Algebra.TensorProduct.includeLeft = x :=
  AlgHom.ext fun a => by simp

theorem ev_comp_right (x : A →ₐ[R] D) (z : B →ₐ[R] D) : (ev x z).comp Algebra.TensorProduct.includeRight = z :=
  AlgHom.ext fun a => by simp

theorem tensorToHom_ev (f : A →ₐ[R] D) (g : B →ₐ[R] E) (u : A ⊗[R] B) (φ : CartierDual R E) :
    tensorToHom R D E (ev (Algebra.TensorProduct.includeLeft.comp f) (Algebra.TensorProduct.includeRight.comp g) u) φ =
      f (tensorToHom R A B u (transpose g.toLinearMap φ)) := by
  induction u with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul a b => simp

theorem tensorToHom_mul_right (u v : A ⊗[R] B) (φ ψ : CartierDual R B) :
    tensorToHom R A (B ⊗[R] B)
      (ev Algebra.TensorProduct.includeLeft
          (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft) u *
        ev Algebra.TensorProduct.includeLeft
          (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight) v : A ⊗[R] (B ⊗[R] B))
      (toConv (pair R B B (φ ⊗ₜ ψ))) = tensorToHom R A B u φ * tensorToHom R A B v ψ := by
  induction u with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, add_mul, hs, ht]
  | tmul a b =>
    induction v with
    | zero => simp
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, mul_add, hs, ht]
    | tmul a' b' => simp [mul_smul, smul_comm (φ.ofConv b)]

theorem tensorToHom_mul_left [Module.Finite R B] [Module.Projective R B] (u v : A ⊗[R] B) (φ : CartierDual R B) :
    tensorToHom R (A ⊗[R] A) B
      (ev (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft)
          Algebra.TensorProduct.includeRight u *
        ev (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight)
          Algebra.TensorProduct.includeRight v : (A ⊗[R] A) ⊗[R] B) φ =
      TensorProduct.map (tensorToHom R A B u) (tensorToHom R A B v) (Coalgebra.comul φ) := by
  induction u with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, add_mul, hs, ht, TensorProduct.map_add_left]
  | tmul a b =>
    induction v with
    | zero => simp
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, mul_add, hs, ht, TensorProduct.map_add_right]
    | tmul a' b' =>
      have key : ∀ t : CartierDual R B ⊗[R] CartierDual R B,
          TensorProduct.map (tensorToHom R A B (a ⊗ₜ b)) (tensorToHom R A B (a' ⊗ₜ b')) t =
            pair R B B t (b ⊗ₜ b') • (a ⊗ₜ a') := fun t => by
        induction t with
        | zero => simp
        | add s t hs ht => simp only [map_add, LinearMap.add_apply, add_smul, hs, ht]
        | tmul f g => simp [← smul_tmul', smul_smul, mul_comm]
      rw [key, pair_comul_tmul]
      simp

end Values

variable [Bialgebra R A] [Bialgebra R B]

structure IsBimul (u : A ⊗[R] B) : Prop where

  isUnit : IsUnit u

  mul_left : ∀ (D : Type) [CommRing D] [Algebra R D] (x x' : WithConv (A →ₐ[R] D)) (z : B →ₐ[R] D),
    ev (x * x').ofConv z u = ev x.ofConv z u * ev x'.ofConv z u

  mul_right : ∀ (D : Type) [CommRing D] [Algebra R D] (x : A →ₐ[R] D) (z z' : WithConv (B →ₐ[R] D)),
    ev x (z * z').ofConv u = ev x z.ofConv u * ev x z'.ofConv u

theorem conv_incl {D : Type} [CommRing D] [Algebra R D] (j : A ⊗[R] A →ₐ[R] D) :
    (toConv (j.comp Algebra.TensorProduct.includeLeft) * toConv (j.comp Algebra.TensorProduct.includeRight)).ofConv =
      j.comp (Bialgebra.comulAlgHom R A) := AlgHom.ext fun a => by
  rw [AlgHom.convMul_apply]
  refine DFunLike.congr_fun (g := j) ?_ _
  ext <;> simp

variable [Module.Finite R B] [Module.Projective R B] {u : A ⊗[R] B} (h : IsBimul u)

def IsBimul.hom : CartierDual R B →ₐc[R] A where
  __ := tensorToHom R A B u
  counit_comp := LinearMap.ext fun φ => by
    have e := h.mul_left B 1 1 (AlgHom.id R B)
    rw [_root_.mul_one] at e
    have e' := (h.isUnit.map _).mul_eq_left.1 e.symm
    have k : ∀ v : A ⊗[R] B, Coalgebra.counit (tensorToHom R A B v φ) =
        φ (ev (1 : WithConv (A →ₐ[R] B)).ofConv (AlgHom.id R B) v) := fun v => by
      induction v with
      | zero => simp
      | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
      | tmul a b =>
        have : φ.ofConv (algebraMap R B (Coalgebra.counit a) * b) = Coalgebra.counit a * φ.ofConv b := by
          rw [← Algebra.smul_def, map_smul, smul_eq_mul]
        simpa [mul_comm] using this.symm
    exact (k u).trans (congrArg φ.ofConv e')
  map_comp_comul := LinearMap.ext fun φ => by
    have e := h.mul_left ((A ⊗[R] A) ⊗[R] B)
      (toConv (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft))
      (toConv (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight))
      Algebra.TensorProduct.includeRight
    rw [conv_incl] at e
    exact (tensorToHom_mul_left u u φ).symm.trans ((congrArg (tensorToHom R _ B · φ) e.symm).trans
      (tensorToHom_ev (Bialgebra.comulAlgHom R A) (AlgHom.id R B) u φ))
  map_one' := by
    have e := h.mul_right A (AlgHom.id R A) 1 1
    rw [_root_.mul_one] at e
    have e' := (h.isUnit.map _).mul_eq_left.1 e.symm
    have k : ∀ v : A ⊗[R] B, tensorToHom R A B v 1 =
        ev (AlgHom.id R A) (1 : WithConv (B →ₐ[R] A)).ofConv v := fun v => by
      induction v with
      | zero => simp
      | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
      | tmul a b => simp [Algebra.smul_def, mul_comm]
    exact (k u).trans e'
  map_mul' φ ψ := by
    have e := h.mul_right (A ⊗[R] (B ⊗[R] B)) Algebra.TensorProduct.includeLeft
      (toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft))
      (toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight))
    rw [conv_incl] at e
    refine Eq.trans ?_ ((congrArg (tensorToHom R A _ · _) e).trans (tensorToHom_mul_right u u φ ψ))
    refine Eq.trans ?_ (tensorToHom_ev (AlgHom.id R A) (Bialgebra.comulAlgHom R B) u _).symm
    exact congrArg (tensorToHom R A B u) (ext_apply fun a => mul_apply φ ψ a)

theorem exists_hom {p : ℕ} (G H : PDivGroup p R) (u : ∀ n, G.A n ⊗[R] H.A n) (h : ∀ n, IsBimul (u n))
    (hl : ∀ (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (x : G.A n →ₐ[R] D) (z : H.A (n + 1) →ₐ[R] D),
      ev (x.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) z (u (n + 1)) =
        ev x (z.comp (H.mulP n : H.A n →ₐ[R] H.A (n + 1))) (u n)) :
    ∃ w : G ⟶ H.dual, ∀ n χ, w.app n χ = tensorToHom R _ _ (u n) χ :=
  ⟨⟨fun n => (h n).hom, fun n => BialgHom.ext fun χ =>
    (tensorToHom_ev (G.res n : G.A (n + 1) →ₐ[R] G.A n) (AlgHom.id R _) (u (n + 1)) χ).symm.trans
      ((congrArg (tensorToHom R _ _ · χ) (hl n (G.A n ⊗[R] H.A (n + 1)) Algebra.TensorProduct.includeLeft
        Algebra.TensorProduct.includeRight)).trans
        (tensorToHom_ev (AlgHom.id R _) (H.mulP n : H.A n →ₐ[R] H.A (n + 1)) (u n) χ))⟩, fun _ _ => rfl⟩

end Alg

section Geo

variable {S : Scheme.{0}}

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    (hL : L.IsLB) : ∃ t : LB.Gen (Theta A L), t.IsGen := by
  have := hA.comm
  obtain ⟨t, ht⟩ := hC S A hA L hL _ (x3 A 0) (x3 A 1) (x3 A 2)
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun U _ h => by
    have e := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) h
    have i : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 _ := by ext <;> simp [x3]
    rw [i] at e
    simp only [Over.id_left, Category.id_comp] at e
    rw [e, Fin.prod_univ_eight]
    simp only [Matrix.cons_val, zpow_one, zpow_neg]) t ht
  exact ⟨t', ht'⟩

theorem cubWeil_level {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {L : RigLB A}
    {c : CubicalStr A L} {k l : ℕ} {T : Over S} {x z : T ⟶ A} {ζ ζ' : Γ(T.left, ⊤)ˣ}
    (h : UU.CubWeil c (k * l) x z ζ) (h' : UU.CubWeil c k x (z ^ l) ζ') : ζ = ζ' := by
  have a := (UU.cubWeil_iff_weilIs globalFns_holds hA h.2.1 h.1 _).1 h.symm
  have b := (UU.cubWeil_iff_weilIs globalFns_holds hA h'.2.1 h'.1 _).1 h'.symm
  rw [Nat.cast_mul] at a
  exact inv_injective (PairingLevels.weilIs_value_eq globalFns_holds hA L.isLB c.isGen a b)

variable {p : ℕ} {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem exists_of_cubical [IsCommMonObj (A ⊗ B)] (hAB : IsAbelianScheme (A ⊗ B)) {M : RigLB (A ⊗ B)}
    (c : CubicalStr (A ⊗ B) M) {𝒜 ℬ : PDivGroup p R} (t : 𝒜.TorsionTower A) (s : ℬ.TorsionTower B) :
    ∃ w : 𝒜 ⟶ ℬ.dual, IsWeilHom t s M.L w := by
  let X : ∀ (n : ℕ) (D : Type) [CommRing D] [Algebra R D], WithConv (𝒜.A n →ₐ[R] D) →* (SpAlg R D ⟶ A ⊗ B) :=
    fun n D _ _ => MonoidHom.mk' (fun x => CartesianMonoidalCategory.lift (spOver x.ofConv ≫ t.y n) 1) fun x x' => by
      ext1 <;> simp [MonObj.mul_comp, t.mul]
  let Z : ∀ (n : ℕ) (D : Type) [CommRing D] [Algebra R D], WithConv (ℬ.A n →ₐ[R] D) →* (SpAlg R D ⟶ A ⊗ B) :=
    fun n D _ _ => MonoidHom.mk' (fun z => CartesianMonoidalCategory.lift 1 (spOver z.ofConv ≫ s.y n)) fun x x' => by
      ext1 <;> simp [MonObj.mul_comp, s.mul]
  have ex : ∀ n, ∃ U : (𝒜.A n ⊗[R] ℬ.A n)ˣ, UU.CubWeil c (p ^ n)
      (X n _ (toConv Algebra.TensorProduct.includeLeft)) (Z n _ (toConv Algebra.TensorProduct.includeRight))
      (unitOn U) := fun n => by
    obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c (N := p ^ n)
      (x := X n (𝒜.A n ⊗[R] ℬ.A n) (toConv Algebra.TensorProduct.includeLeft))
      (y := Z n _ (toConv Algebra.TensorProduct.includeRight))
      (by rw [← map_pow, 𝒜.pts_pow_self, map_one]) (by rw [← map_pow, ℬ.pts_pow_self, map_one])
    obtain ⟨U, rfl⟩ := EpsWeil.unitOn_bijective.2 ζ
    exact ⟨U, hζ⟩
  choose U hU using ex
  have at' : ∀ (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (x : WithConv (𝒜.A n →ₐ[R] D))
      (z : WithConv (ℬ.A n →ₐ[R] D)), UU.CubWeil c (p ^ n) (X n D x) (Z n D z)
        (unitOn (Units.map (ev x.ofConv z.ofConv).toRingHom.toMonoidHom (U n))) := fun n D _ _ x z => by
    have h := (hU n).comp (spOver (ev x.ofConv z.ofConv))
    have e₁ : spOver (ev x.ofConv z.ofConv) ≫ X n _ (toConv Algebra.TensorProduct.includeLeft) = X n D x := by
      simp only [X, MonoidHom.mk'_apply, comp_lift, MonObj.comp_one, ← Category.assoc, spOver_comp, ev_comp_left]
    have e₂ : spOver (ev x.ofConv z.ofConv) ≫ Z n _ (toConv Algebra.TensorProduct.includeRight) = Z n D z := by
      simp only [Z, MonoidHom.mk'_apply, comp_lift, MonObj.comp_one, ← Category.assoc, spOver_comp, ev_comp_right]
    rw [e₁, e₂] at h
    exact EpsWeil.map_unitOn (ev x.ofConv z.ofConv).toRingHom (U n) ▸ h
  have um : ∀ {D : Type} [CommRing D] {a : Dˣ} (b d : Dˣ), unitOn a = unitOn b * unitOn d → a.val = b.val * d.val := by
    intro D _ a b d h
    have e : unitOn (b * d) = unitOn b * unitOn d :=
      Units.ext (_root_.map_mul (Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom b.val d.val)
    exact congrArg Units.val ((EpsWeil.unitOn_bijective (D := D)).1 (h.trans e.symm))
  obtain ⟨w, hw⟩ := exists_hom 𝒜 ℬ (fun n => (U n).val)
    (fun n => ⟨(U n).isUnit, fun D _ _ x x' z => by
        have := (at' n D x (toConv z)).mul_left (at' n D x' (toConv z))
        rw [← map_mul] at this
        exact um _ _ ((at' n D (x * x') (toConv z)).unique this),
      fun D _ _ x z z' => by
        have := ((at' n D (toConv x) z).symm.mul_left (at' n D (toConv x) z').symm).symm
        rw [← map_mul, ← mul_inv, inv_inv] at this
        exact um _ _ ((at' n D (toConv x) (z * z')).unique this)⟩)
    fun n D _ _ x z => by
      have a := at' (n + 1) D (toConv (x.comp (𝒜.res n : 𝒜.A (n + 1) →ₐ[R] 𝒜.A n))) (toConv z)
      have b := at' n D (toConv x) (toConv (z.comp (ℬ.mulP n : ℬ.A n →ₐ[R] ℬ.A (n + 1))))
      have e₁ : X (n + 1) D (toConv (x.comp (𝒜.res n : 𝒜.A (n + 1) →ₐ[R] 𝒜.A n))) = X n D (toConv x) := by
        simp only [X, MonoidHom.mk'_apply, ← spOver_comp, Category.assoc, t.res]
      have e₂ : Z n D (toConv (z.comp (ℬ.mulP n : ℬ.A n →ₐ[R] ℬ.A (n + 1)))) = Z (n + 1) D (toConv z) ^ p := by
        ext1 <;> simp only [Z, MonoidHom.mk'_apply, ← spOver_comp, Category.assoc, s.mulP_y, MonObj.pow_comp,
          lift_fst, lift_snd, one_pow, MonObj.comp_pow]
      rw [e₁, pow_succ] at a
      rw [e₂] at b
      exact congrArg Units.val (EpsWeil.unitOn_bijective.1 (cubWeil_level hAB a b))
  exact ⟨w, fun n => ⟨U n, (UU.cubWeil_iff_weilIs globalFns_holds hAB (hU n).1 (hU n).2.1 _).1 (hU n),
    fun χ => (hw n χ).trans (tensorToHom_apply _ _)⟩⟩

theorem exists_of_isDual (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hP : IsDual A B P) {𝒜 ℬ : PDivGroup p R} (t : 𝒜.TorsionTower A)
    (s : ℬ.TorsionTower B) : ∃ w : 𝒜 ⟶ ℬ.dual, IsWeilHom t s P w := by
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have := hAB.comm
  obtain ⟨r, hr⟩ : AbLaw.Triv (P.pull (eSec (A ⊗ B))) := by
    have e := (AbDual.triv_ev_iff hP.isLB _ _).2
      (AbDual.evc_one_right hP.isLB hP.zero (1 : 𝟙_ (Over (Sp R)) ⟶ A))
    have e' : CartesianMonoidalCategory.lift (1 : 𝟙_ (Over (Sp R)) ⟶ A) (1 : 𝟙_ (Over (Sp R)) ⟶ B) = η[A ⊗ B] := by
      ext <;> simp [Hom.one_def]
    rw [AbDual.ev, e'] at e
    exact e
  obtain ⟨τ, hτ⟩ := triv_theta hC hAB hP.isLB
  obtain ⟨τ', hτ', hn⟩ := AbLaw.Cube.exists_normalised hP.isLB τ hτ
  exact exists_of_cubical hAB
    (AbLaw.Cube.cubicalOfNormalised globalFns_holds hAB ⟨P, r, hP.isLB, hr⟩ τ' hτ' hn) t s

end Geo

theorem exists_isWeilHom : GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (A : Over (Sp K))
    [GrpObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), IsDual A A P →
    ∀ (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A), ∃ w : 𝒜 ⟶ 𝒜.dual, IsWeilHom t t P w :=
  fun hC _ _ _ _ _ _ hA _ hP _ t => exists_of_isDual hC hA hA hP t t

end GlobalTheory.WeilHom
