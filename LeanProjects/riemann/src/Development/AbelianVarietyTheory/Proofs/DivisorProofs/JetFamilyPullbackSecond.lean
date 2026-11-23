import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismIsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFiltrationSpannedCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondenceStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetBCGen

section Coeff

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Type} [Fintype I] {n : ℕ}

theorem repr_algebraMap (J : JetRing R I n) (r : R) (ν : Idx I n) :
    J.b.repr (algebraMap R J.B r) ν = if (⟨0, by simp⟩ : Idx I n) = ν then r else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, J.b.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

open scoped Classical in

theorem repr_t_eq_ite_single (J : JetRing R I n) (i : I) (ν : Idx I n) :
    J.b.repr (J.t i) ν = if (⟨Pi.single i 1, by simp⟩ : Idx I n) = ν then 1 else 0 := by
  rw [JetRing.t, J.b.repr_self, Finsupp.single_apply]

variable (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
  (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν))
include hτ

theorem map_algebraMap (r : R) : τ (algebraMap R J.B r) = algebraMap R' J'.B (σ r) :=
  J'.b.ext_elem fun ν ↦ by rw [hτ, repr_algebraMap, repr_algebraMap]; split_ifs <;> simp

theorem map_t (i : I) : τ (J.t i) = J'.t i :=
  J'.b.ext_elem fun ν ↦ by rw [hτ, repr_t_eq_ite_single, repr_t_eq_ite_single]; split_ifs <;> simp

theorem map_π (x : J.B) : J'.π (τ x) = σ (J.π x) := by rw [J'.π_eq, J.π_eq, hτ]

end Coeff

section Crys

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {S S' : Scheme.{0}} {I : Ideal R}
  {I' : Ideal R'} {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'}
  {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ}

theorem ext_of_isBC (hm : m.IsBC) {d d' : Crys κ' t' A'} (h : ∀ c, d (m.pull c) = d' (m.pull c)) :
    d = d' := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

end Crys

section Jet

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type}
  [Fintype I] {n : ℕ} (J : JetRing R I n) {X : Obj F 𝔠 (Sp R)}
  {m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))}
  (hm : m.IsBC) (N : I → Module.End R (HdR X.A))

def jet (x : HdR X.A) : Crys J.κ (spMap J.π) X.A :=
  hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x)

theorem isJetElt_jet (x : HdR X.A) : IsJetElt J X N m x (jet J hm N x) := fun c ↦ by
  have e : ∀ y, hm.bcMap y (m.pull c) = algebraMap R J.B (y c) := fun y ↦ (hm.corr_iff.2 rfl) c
  simp only [jet, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, e]

theorem eq_jet_of_isJetElt {x : HdR X.A} {d : Crys J.κ (spMap J.π) X.A} (h : IsJetElt J X N m x d) :
    d = jet J hm N x :=
  ext_of_isBC hm fun c ↦ (h c).trans (isJetElt_jet J hm N x c).symm

theorem jet_add (x y : HdR X.A) : jet J hm N (x + y) = jet J hm N x + jet J hm N y := by
  simp only [jet, map_add, smul_add, Finset.sum_add_distrib]
  abel

theorem jet_smul (r : R) (x : HdR X.A) : jet J hm N (r • x) = algebraMap R J.B r • jet J hm N x := by
  simp only [jet, map_smul, LinearMap.map_smulₛₗ, smul_add, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

end Jet

def compMulti {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {M L : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup L] [Module B L] {K : Type} (δ : L [⋀^K]→ₗ[B] B) (Λ : M → L)
    (hadd : ∀ a b, Λ (a + b) = Λ a + Λ b) (hsmul : ∀ (r : R) a, Λ (r • a) = algebraMap R B r • Λ a) :
    MultilinearMap R (fun _ : K ↦ M) B where
  toFun x := δ (fun j ↦ Λ (x j))
  map_update_add' x j a b := by
    have e : ∀ y, (fun k ↦ Λ (Function.update x j y k)) = Function.update (fun k ↦ Λ (x k)) j (Λ y) :=
      fun y ↦ funext fun k ↦ Function.apply_update (fun _ ↦ Λ) x j y k
    simp only [e, hadd, δ.map_update_add]
  map_update_smul' x j r a := by
    have e : ∀ y, (fun k ↦ Λ (Function.update x j y k)) = Function.update (fun k ↦ Λ (x k)) j (Λ y) :=
      fun y ↦ funext fun k ↦ Function.apply_update (fun _ ↦ Λ) x j y k
    simp only [e, hsmul, δ.map_update_smul, smul_eq_mul, Algebra.smul_def]

end GlobalTheory.JetBCGen

namespace GlobalTheory.JetBCGen

theorem detGen_baseChange : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ (δ₁ : X₁.DetGen), Obj.DetCorr σ p δ₀.1 δ₁.1 → ∀ (δ' : Z'.DetGen), Obj.DetCorr τ q Y.δ'.1 δ'.1 →
    ∀ (x : Fin (Module.finrank ℚ F) → HdR X₁.A) (d : Fin (Module.finrank ℚ F) → Crys J'.κ (spMap J'.π) X₁.A)
      (v : Fin (Module.finrank ℚ F) → X₁.Lie) (v' : Fin (Module.finrank ℚ F) → Z'.Lie),
      (∀ j, IsJetElt J' X₁ N₁ mor' (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧
        IsLieImage (crysToDR J'.κ hi'.grp (d j)) (v' j).hom) →
      δ'.1 v' = algebraMap R' J'.B (δ₁.1 v) := by
  intro H F _ _ 𝔠 R R' _ _ σ I _ n J J' X₀ δ₀ N Y X₁ N₁ p hp m hN τ hτ hτdp Z' q hq i' hi' hcomm mor' δ₁
    hδ₁ δ' hδ' x d v v' hx
  classical
  have hBC' : mor'.IsBC := GlobalTheory.T.jet_morphism_is_base_change H J' X₁ mor'
  have hBC0 : Y.mor.IsBC := GlobalTheory.T.jet_morphism_is_base_change H J X₀ Y.mor
  have L₁ : LieExact X₁.A := (H.2.1 R' X₁.A _ X₁.ab X₁.dim).1
  have L₀ : LieExact X₀.A := (H.2.1 R X₀.A _ X₀.ab X₀.dim).1
  have LY : LieExact Y.X'.A := (H.2.1 J.B Y.X'.A _ Y.X'.ab Y.X'.dim).1
  have LZ : LieExact Z'.A := (H.2.1 J'.B Z'.A _ Z'.ab Z'.dim).1
  have hτa := map_algebraMap σ J J' τ hτ
  have hτt := map_t σ J J' τ hτ
  have hbase : spMap σ ≫ spMap J.π = spMap J'.π ≫ spMap τ := by
    rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    ext y
    exact (map_π σ J J' τ hτ y).symm
  have M : GrpMor J.κ (spMap J.π) X₀.A J'.κ (spMap J'.π) X₁.A τ (spMap σ) p :=
    GrpMor.of_isGrpPullback hτdp hbase hp.grp
  have nq : GrpMor (dp0 J.B) (𝟙 _) Y.X'.A (dp0 J'.B) (𝟙 _) Z'.A τ (spMap τ) q :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) hq.grp
  have K := Y.mor.comp M
  have key : ∀ c₀, M.pull (Y.mor.pull c₀) = mor'.pull (m.pull c₀) := fun c₀ ↦
    (GrpMor.pull_pull Y.mor M K (fun _ ↦ rfl) rfl c₀).trans
      (GrpMor.pull_pull m mor' K (fun r ↦ (hτa r).symm) (by simp) c₀).symm

  have hM : ∀ x₀ y, m.Corr x₀ y → M.Corr (jet J hBC0 N x₀) (jet J' hBC' N₁ y) := by
    intro x₀ y hy c
    obtain ⟨z, rfl⟩ := hBC0.2 c
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b c₀ =>
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, key,
        isJetElt_jet J' hBC' N₁ y (m.pull c₀), isJetElt_jet J hBC0 N x₀ c₀]
      have e : ∀ i, N₁ i y (m.pull c₀) = σ (N i x₀ c₀) := fun i ↦ hN i x₀ y hy c₀
      simp only [e, hy c₀, map_add, map_sum, map_mul, hτa, hτt]

  let Λ : HdR X₁.A → Z'.Lie := fun y ↦ LZ.toLie Z'.rm (crysToDR J'.κ hi'.grp (jet J' hBC' N₁ y))
  have hΛadd : ∀ a b, Λ (a + b) = Λ a + Λ b := fun a b ↦ by
    simp only [Λ, jet_add, map_add]
  have hΛsmul : ∀ (r : R') a, Λ (r • a) = algebraMap R' J'.B r • Λ a := fun r a ↦ by
    simp only [Λ, jet_smul, map_smul]
  let Φ₁ := compMulti δ'.1 Λ hΛadd hΛsmul
  let Φ₂ : MultilinearMap R' (fun _ : Fin (Module.finrank ℚ F) ↦ HdR X₁.A) J'.B :=
    (Algebra.linearMap R' J'.B).compMultilinearMap
      (δ₁.1.toMultilinearMap.compLinearMap fun _ ↦ L₁.toLie X₁.rm)
  have hΦ : Φ₁ = Φ₂ := by
    obtain ⟨hspan, -, -⟩ := GlobalTheory.T.lie_filtration_spanned_correspondence H σ hp m
    refine MultilinearMap.ext_of_span_eq_top
      (g := fun (_ : Fin (Module.finrank ℚ F)) (y : {y : HdR X₁.A // ∃ y₀, m.Corr y₀ y}) ↦ y.1)
      (fun _ ↦ ?_) fun s ↦ ?_
    · change Submodule.span R' (Set.range Subtype.val) = ⊤
      rw [Subtype.range_coe_subtype]
      exact hspan
    choose x₀ hx₀ using fun j ↦ (s j).2
    let v₀ := fun j ↦ L₀.toLie X₀.rm (x₀ j)
    let w := fun j ↦ LY.toLie Y.X'.rm (crysToDR J.κ Y.pull.grp (jet J hBC0 N (x₀ j)))
    have hgen := Y.gen x₀ (fun j ↦ jet J hBC0 N (x₀ j)) v₀ w fun j ↦
      ⟨isJetElt_jet J hBC0 N (x₀ j), (L₀.toLie_eq_iff _).1 rfl, (LY.toLie_eq_iff _).1 rfl⟩
    have hl₁ : ∀ j, Obj.LieCorr σ p (v₀ j) (L₁.toLie X₁.rm (s j).1) := fun j ↦
      GlobalTheory.T.lie_image_correspondence H σ hp m (hx₀ j) ((L₀.toLie_eq_iff _).1 rfl) ((L₁.toLie_eq_iff _).1 rfl)
    have hlZ : ∀ j, Obj.LieCorr τ q (w j) (Λ (s j).1) := fun j ↦
      GlobalTheory.T.lie_image_correspondence H τ hq nq (crysToDR_corr J.κ Y.pull.grp hi'.grp M nq hcomm (hM _ _ (hx₀ j)))
        ((LY.toLie_eq_iff _).1 rfl) ((LZ.toLie_eq_iff _).1 rfl)
    change δ'.1 (fun j ↦ Λ (s j).1) = algebraMap R' J'.B (δ₁.1 fun j ↦ L₁.toLie X₁.rm (s j).1)
    rw [hδ' w _ hlZ, hgen, hτa, hδ₁ v₀ _ hl₁]
  have hv' : v' = fun j ↦ Λ (x j) := funext fun j ↦
    ((LZ.toLie_eq_iff Z'.rm).2 (by rw [← eq_jet_of_isJetElt J' hBC' N₁ (hx j).1]; exact (hx j).2.2)).symm
  have hv : v = fun j ↦ L₁.toLie X₁.rm (x j) := funext fun j ↦ ((L₁.toLie_eq_iff X₁.rm).2 (hx j).2.1).symm
  subst hv hv'
  exact DFunLike.congr_fun hΦ x

end GlobalTheory.JetBCGen
