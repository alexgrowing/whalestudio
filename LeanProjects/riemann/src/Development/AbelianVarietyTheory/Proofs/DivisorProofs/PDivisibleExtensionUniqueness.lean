import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry NumberField MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Rigid

section Transport

variable {Z : Scheme.{0}} {T : Over Z} [GrpObj T]

def down {S : Scheme.{0}} {T' : Over S} [GrpObj T'] {f : S ⟶ Z} {φ : T'.left ⟶ T.left} (h : IsGrpPullback T' T f φ)
    (Y : Over S) (b : Y.left ⟶ Z) (hb : Y.hom ≫ f = b) : (Y ⟶ T') →* (Over.mk b ⟶ T) :=
  MonoidHom.mk' (fun z => Over.homMk (z.left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; exact hb))
    fun x y => by
      subst hb
      exact Over.OverMorphism.ext (h.2 Y x y _ _ rfl rfl).symm

theorem down_bijective {S : Scheme.{0}} {T' : Over S} [GrpObj T'] {f : S ⟶ Z} {φ : T'.left ⟶ T.left}
    (h : IsGrpPullback T' T f φ) (Y : Over S) (b : Y.left ⟶ Z) (hb : Y.hom ≫ f = b) :
    Function.Bijective (down h Y b hb) := by
  refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg Over.Hom.left e)
    ((Over.w x).trans (Over.w y).symm)), fun z => ?_⟩
  have e : z.left ≫ T.hom = Y.hom ≫ f := (Over.w z).trans hb.symm
  exact ⟨Over.homMk (h.1.lift _ _ e) (h.1.lift_snd _ _ e), Over.OverMorphism.ext (h.1.lift_fst _ _ e)⟩

theorem exists_tors {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {T₁ : Over (Sp R₁)} [GrpObj T₁] {T₂ : Over (Sp R₂)} [GrpObj T₂]
    {f₁ : Sp R₁ ⟶ Z} {f₂ : Sp R₂ ⟶ Z} {φ₁ : T₁.left ⟶ T.left} {φ₂ : T₂.left ⟶ T.left}
    (h₁ : IsGrpPullback T₁ T f₁ φ₁) (h₂ : IsGrpPullback T₂ T f₂ φ₂) (B : Type) [CommRing B] [Algebra R₁ B] [Algebra R₂ B]
    (hB : spMap (algebraMap R₁ B) ≫ f₁ = spMap (algebraMap R₂ B) ≫ f₂) (N : ℕ) (z : Tors T₁ N B) :
    ∃ z' : Tors T₂ N B, z.1.left ≫ φ₁ = z'.1.left ≫ φ₂ := by
  obtain ⟨y, hy⟩ := (down_bijective h₂ (SpAlg R₂ B) _ hB.symm).2 (down h₁ (SpAlg R₁ B) _ rfl z.1)
  refine ⟨⟨y, (down_bijective h₂ (SpAlg R₂ B) _ hB.symm).1 ?_⟩, (congrArg Over.Hom.left hy).symm⟩
  rw [map_pow, hy, ← map_pow, z.2, map_one, map_one]

end Transport

def push {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {N : ℕ} {B C : Type} [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (z : Tors G N B) : Tors G N C :=
  ⟨spOver φ ≫ z.1, by rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩

theorem range_subset_of_local {B : Type} [CommRing B] [IsLocalRing B] {Y : Scheme.{0}} (f : Sp B ⟶ Y) (V : Y.Opens)
    (h : f (IsLocalRing.closedPoint B) ∈ V) : Set.range f ⊆ V := by
  rintro _ ⟨x, rfl⟩
  have h1 : f ⁻¹ᵁ V = ⊤ := (IsLocalRing.closedPoint_mem_iff (R := B) (f ⁻¹ᵁ V)).1 h
  have : x ∈ f ⁻¹ᵁ V := h1 ▸ trivial
  exact this

theorem exists_flat {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) {N : ℕ}
    (hN : N ≠ 0) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (z : Tors G N B) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra R D) (_ : Module.Flat R D) (w : Tors G N D) (φ : D →ₐ[R] B),
      z.1 = spOver φ ≫ w.1 := by
  have hf := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG N hN).1
  let ml := ((𝟙 G) ^ N : G ⟶ G).left
  let η₀ : Sp R ⟶ G.left := (η[G]).left
  let P := pullback ml η₀
  have key : ∀ (Y : Over (Sp R)) (y : Y ⟶ G), y ^ N = 1 ↔ y.left ≫ ml = Y.hom ≫ η₀ := fun Y y => by
    have h1 : y ^ N = y ≫ (𝟙 G) ^ N := by rw [MonObj.comp_pow, Category.comp_id]
    rw [h1, Over.OverMorphism.ext_iff]
    have h2 : (1 : Y ⟶ G).left = Y.hom ≫ η₀ := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [h2]
    rfl
  let l : Sp B ⟶ P := pullback.lift z.1.left (spMap (algebraMap R B)) ((key _ _).1 z.2)
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ := P.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (l (IsLocalRing.closedPoint B))) isOpen_univ
  have hW : IsAffineOpen W := hW
  have hr : Set.range l ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]; exact range_subset_of_local l W hx
  let k : Sp B ⟶ Spec Γ(P, W) := IsOpenImmersion.lift hW.fromSpec l hr
  have hk : k ≫ hW.fromSpec = l := IsOpenImmersion.lift_fac _ _ _
  let q : Spec Γ(P, W) ⟶ Sp R := hW.fromSpec ≫ pullback.snd ml η₀
  have hq : Flat q := inferInstance
  obtain ⟨a, ha⟩ := Spec.map_surjective q
  obtain ⟨c, hc⟩ := Spec.map_surjective k
  letI : Algebra R Γ(P, W) := a.hom.toAlgebra
  have hfl : Module.Flat R Γ(P, W) := by
    rw [← ha, Flat.SpecMap_iff] at hq
    exact hq
  have hac : a ≫ c = CommRingCat.ofHom (algebraMap R B) := Spec.map_injective (by
    rw [Spec.map_comp, ha, hc, ← Category.assoc, hk]
    exact pullback.lift_snd _ _ _)
  have hη : η₀ ≫ G.hom = 𝟙 _ := Over.w η[G]
  have hml : ml ≫ G.hom = G.hom := Over.w _
  have hw : (hW.fromSpec ≫ pullback.fst ml η₀) ≫ G.hom = spMap (algebraMap R Γ(P, W)) := by
    rw [← hml, Category.assoc, pullback.condition_assoc, hη, Category.comp_id]
    exact ha.symm
  refine ⟨Γ(P, W), inferInstance, inferInstance, hfl, ⟨Over.homMk (hW.fromSpec ≫ pullback.fst ml η₀) hw, (key _ _).2 ?_⟩,
    { c.hom with commutes' := fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hac) r }, ?_⟩
  · change (hW.fromSpec ≫ pullback.fst ml η₀) ≫ ml = Spec.map a ≫ η₀
    rw [ha, Category.assoc, pullback.condition, Category.assoc]
  · refine Over.OverMorphism.ext ?_
    change z.1.left = Spec.map c ≫ hW.fromSpec ≫ pullback.fst ml η₀
    rw [hc, ← Category.assoc, hk]
    exact (pullback.lift_fst _ _ _).symm

theorem exists_section {S K B C : Type} [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Field K] [IsAlgClosed K] [Algebra S K]
    [IsFractionRing S K] [CommRing B] [Algebra S B] [Algebra.IsIntegral S B] [CommRing C] [Algebra S C] [Algebra K C]
    [IsScalarTower S K C] (j : B →ₐ[S] C) (hj : Function.Injective j) (m : Ideal B) [m.IsPrime] :
    ∃ σ : B →ₐ[S] S, RingHom.ker σ ≤ m := by
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : q.IsPrime := hq.1.1
  have hinj : Function.Injective (algebraMap S (B ⧸ q)) := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    by_contra h0
    have h1 : algebraMap S B s ∈ q := Ideal.Quotient.eq_zero_iff_mem.1 hs
    refine Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h1 ?_
    refine mem_nonZeroDivisors_iff_right.2 fun x hx => hj ?_
    have hu : IsUnit (algebraMap S C s) := by
      rw [IsScalarTower.algebraMap_apply S K C]
      exact (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective S K)).2 h0)).map _
    have h2 := congrArg j hx
    rw [map_mul, j.commutes, map_zero] at h2
    rw [map_zero]
    exact hu.mul_left_eq_zero.1 h2
  haveI : FaithfulSMul S (B ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  obtain ⟨g, -⟩ := exists_algHom_comp_eq (A := S) (K := K) (IsAlgClosed.lift (R := S) (S := B ⧸ q) (M := K))
  have hg : RingHom.ker g = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := S) (by
    rw [eq_bot_iff]
    intro s hs
    have : g (algebraMap S _ s) = 0 := hs
    rw [g.commutes] at this
    exact this)
  refine ⟨g.comp (Ideal.Quotient.mkₐ S q), fun b hb => hqm ?_⟩
  have h3 : Ideal.Quotient.mk q b ∈ RingHom.ker g := hb
  rw [hg] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

section Key

variable {p : ℕ} [Fact p.Prime] {La : Type} [AddCommGroup La]

theorem tatePt_add {R : Type} [CommRing R] {G : PDivGroup p R} (τ : La →+ G.Tate) (n : ℕ) (B : Type) [CommRing B] [Algebra R B]
    (x : La) : toConv (tatePt (τ (-x)) n B) * toConv (tatePt (τ x) n B) = 1 := by
  have h := map_mul (ptsPush (G.A n) (Algebra.ofId R B)) ((τ (-x)).conv n) ((τ x).conv n)
  rw [← TateOver.add_conv, ← map_add, neg_add_cancel, map_zero, TateOver.zero_conv, map_one] at h
  exact h.symm

theorem exists_pt_eq {R : Type} [CommRing R] {T : Over (Sp R)} [GrpObj T] {G : PDivGroup p R} {θ : TorsionMap T G}
    (hθ : θ.IsOpenNearZero) (n : ℕ) (L : Type) [CommRing L] [IsLocalRing L] [Algebra R L] (w : G.A n →ₐ[R] L)
    (hw : ptsPush (G.A n) (IsScalarTower.toAlgHom R L (IsLocalRing.ResidueField L)) (toConv w) = 1) :
    ∃ z, θ.pt n L z = w := by
  obtain ⟨U, V, hU, hb⟩ := hθ n
  let k := IsLocalRing.ResidueField L
  have h1 := (hb k).mapsTo (x := ⟨1, one_pow _⟩) (by
    change Set.range (1 : SpAlg R k ⟶ T).left ⊆ U
    rw [Hom.one_def, Over.comp_left]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨_, rfl⟩)
  have h2 : θ.pt n k ⟨1, one_pow _⟩ = (IsScalarTower.toAlgHom R L k).comp w :=
    congrArg ofConv ((θ.pt_one n k (Fact.out : p.Prime).ne_zero).trans hw.symm)
  rw [h2] at h1
  have h3 : Set.range (spMap (w : G.A n →+* L)) ⊆ V := range_subset_of_local _ V (by
    rw [← IsLocalRing.comap_closedPoint (IsLocalRing.residue L)]
    exact h1 ⟨IsLocalRing.closedPoint k, rfl⟩)
  obtain ⟨z, -, hz⟩ := (hb L).surjOn h3
  exact ⟨z, hz⟩

variable {R₁ R₂ K : Type} [CommRing R₁] [CommRing R₂] [Field K] [Algebra R₁ K] [Algebra R₂ K]
  {Z : Scheme.{0}} {T : Over Z} [GrpObj T] {T₁ : Over (Sp R₁)} [GrpObj T₁] {T₂ : Over (Sp R₂)} [GrpObj T₂]
  {T₀ : Over (Sp K)} [GrpObj T₀] {f₁ : Sp R₁ ⟶ Z} {f₂ : Sp R₂ ⟶ Z} {f₀ : Sp K ⟶ Z}
  {φ₁ : T₁.left ⟶ T.left} {φ₂ : T₂.left ⟶ T.left} {φ₀ : T₀.left ⟶ T.left}
  {G₁ : PDivGroup p R₁} {G₂ : PDivGroup p R₂} {G₀ : PDivGroup p K}
  {θ₁ : TorsionMap T₁ G₁} {θ₂ : TorsionMap T₂ G₂} {θ₀ : TorsionMap T₀ G₀}
  {τ₁ : La →+ G₁.Tate} {τ₂ : La →+ G₂.Tate} {τ₀ : La →+ G₀.Tate}

def Link (φ₁ : T₁.left ⟶ T.left) (θ₁ : TorsionMap T₁ G₁) (τ₁ : La →+ G₁.Tate) (φ₀ : T₀.left ⟶ T.left) (θ₀ : TorsionMap T₀ G₀)
    (τ₀ : La →+ G₀.Tate) (s : SemiHom (algebraMap R₁ K) G₀ G₁) : Prop :=
  (∀ x n a, (τ₀ x).pt n (s.app n a) = algebraMap R₁ K ((τ₁ x).pt n a)) ∧
    ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R₁ B] [Algebra K B] [IsScalarTower R₁ K B]
      (z : Tors T₁ (p ^ n) B) (z' : Tors T₀ (p ^ n) B), z.1.left ≫ φ₁ = z'.1.left ≫ φ₀ →
        ∀ a, θ₁.pt n B z a = θ₀.pt n B z' (s.app n a)

theorem Link.mul {s : SemiHom (algebraMap R₁ K) G₀ G₁} (l : Link φ₁ θ₁ τ₁ φ₀ θ₀ τ₀ s) (n : ℕ) (L C : Type) [CommRing L]
    [Algebra R₁ L] [CommRing C] [Algebra R₁ C] [Algebra K C] [IsScalarTower R₁ K C] (κ : L →ₐ[R₁] C)
    (z : Tors T₁ (p ^ n) L) (z' : Tors T₀ (p ^ n) C) (h : spMap (κ : L →+* C) ≫ z.1.left ≫ φ₁ = z'.1.left ≫ φ₀) (x : La)
    (a : G₁.A n) : κ ((toConv (θ₁.pt n L z) * toConv (tatePt (τ₁ x) n L)).ofConv a) =
      (toConv (θ₀.pt n C z') * toConv (tatePt (τ₀ x) n C)).ofConv (s.app n a) := by
  have h1 := map_mul (ptsPush (G₁.A n) κ) (toConv (θ₁.pt n L z)) (toConv (tatePt (τ₁ x) n L))
  have h2 := map_mul ((s.app n).pts C (IsScalarTower.algebraMap_apply R₁ K C)) (toConv (θ₀.pt n C z'))
    (toConv (tatePt (τ₀ x) n C))
  have h3 : ptsPush (G₁.A n) κ (toConv (θ₁.pt n L z)) =
      (s.app n).pts C (IsScalarTower.algebraMap_apply R₁ K C) (toConv (θ₀.pt n C z')) :=
    ofConv_injective (AlgHom.ext fun a => (DFunLike.congr_fun (θ₁.nat n L C κ z (push κ z) rfl) a).symm.trans
      (l.2 n C (push κ z) z' ((Category.assoc ..).trans h) a))
  have h4 : ptsPush (G₁.A n) κ (toConv (tatePt (τ₁ x) n L)) =
      (s.app n).pts C (IsScalarTower.algebraMap_apply R₁ K C) (toConv (tatePt (τ₀ x) n C)) :=
    ofConv_injective (AlgHom.ext fun a => (κ.commutes _).trans ((IsScalarTower.algebraMap_apply R₁ K C _).trans
      (congrArg (algebraMap K C) (l.1 x n a).symm)))
  rw [h3, h4, ← h2] at h1
  exact DFunLike.congr_fun (congrArg ofConv h1) a

variable (h₁ : IsGrpPullback T₁ T f₁ φ₁) (h₂ : IsGrpPullback T₂ T f₂ φ₂) (h₀ : IsGrpPullback T₀ T f₀ φ₀)
  (hf : spMap (algebraMap R₁ K) ≫ f₁ = f₀) {s₁ : SemiHom (algebraMap R₁ K) G₀ G₁} {s₂ : SemiHom (algebraMap R₂ K) G₀ G₂}
  (l₁ : Link φ₁ θ₁ τ₁ φ₀ θ₀ τ₀ s₁) (l₂ : Link φ₂ θ₂ τ₂ φ₀ θ₀ τ₀ s₂) (hθ : θ₁.IsOpenNearZero) (n : ℕ)
  (hs : Function.Surjective (s₁.lift.app n))

include h₁ h₂ h₀ hf l₁ l₂ hθ hs in

theorem local_step (L C : Type) [CommRing L] [IsLocalRing L] [Algebra R₁ L] [Algebra R₂ L]
    (hL : spMap (algebraMap R₁ L) ≫ f₁ = spMap (algebraMap R₂ L) ≫ f₂) [CommRing C] [Algebra K C] (κ : L →+* C)
    (hκ₁ : ∀ r, κ (algebraMap R₁ L r) = algebraMap K C (algebraMap R₁ K r))
    (hκ₂ : ∀ r, κ (algebraMap R₂ L r) = algebraMap K C (algebraMap R₂ K r))
    (u : G₁.A n →ₐ[R₁] L) (x : La) (hx : ∀ a, u a - algebraMap R₁ L ((τ₁ x).pt n a) ∈ IsLocalRing.maximalIdeal L)
    (u₀ : G₀.A n →ₐ[K] C) (hu : ∀ a, u₀ (s₁.app n a) = κ (u a)) (a : G₂.A n) : ∃ b, κ b = u₀ (s₂.app n a) := by
  letI : Algebra R₁ C := ((algebraMap K C).comp (algebraMap R₁ K)).toAlgebra
  letI : Algebra R₂ C := ((algebraMap K C).comp (algebraMap R₂ K)).toAlgebra
  haveI : IsScalarTower R₁ K C := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R₂ K C := .of_algebraMap_eq fun _ => rfl
  let κ₁ : L →ₐ[R₁] C := { κ with commutes' := hκ₁ }
  let κ₂ : L →ₐ[R₂] C := { κ with commutes' := hκ₂ }
  obtain ⟨z₁, hz₁⟩ := exists_pt_eq hθ n L (toConv u * toConv (tatePt (τ₁ (-x)) n L)).ofConv (by
    rw [toConv_ofConv, map_mul, _root_.mul_comm, ← tatePt_add τ₁ n (IsLocalRing.ResidueField L) x]
    refine congrArg₂ _ ?_ ?_
    · exact ofConv_injective (AlgHom.ext fun a => AlgHom.commutes (IsScalarTower.toAlgHom R₁ L (IsLocalRing.ResidueField L)) _)
    · exact ofConv_injective (AlgHom.ext fun a => ((Ideal.Quotient.eq.2 (hx a)).trans
        (AlgHom.commutes (IsScalarTower.toAlgHom R₁ L (IsLocalRing.ResidueField L)) _))))
  obtain ⟨z₂, hz₂⟩ := exists_tors h₁ h₂ L hL _ z₁
  obtain ⟨z₀, hz₀⟩ := exists_tors h₁ h₀ C (by rw [← hf, ← Category.assoc, ← Cris.spMap_comp]) _ (push κ₁ z₁)
  have e₁ := l₁.mul n L C κ₁ z₁ z₀ ((Category.assoc ..).symm.trans hz₀) x
  have e₂ := l₂.mul n L C κ₂ z₂ z₀ ((congrArg (spMap κ ≫ ·) hz₂.symm).trans ((Category.assoc ..).symm.trans hz₀)) x
  rw [hz₁, toConv_ofConv, _root_.mul_assoc, tatePt_add, _root_.mul_one] at e₁
  have e₃ : (toConv (θ₀.pt n C z₀) * toConv (tatePt (τ₀ x) n C)).ofConv = u₀ := AlgHom.ext fun y => by
    obtain ⟨y, rfl⟩ := hs y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => rw [SemiHom.lift_app, map_smul, map_smul, hu, ← e₁]; rfl
  rw [e₃] at e₂
  exact ⟨_, e₂ a⟩

include h₁ h₂ h₀ hf l₁ l₂ hθ hs in

theorem global_step (S : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsAlgClosed K] [Algebra S K]
    [IsFractionRing S K] [Algebra R₁ S] [Algebra R₂ S] [IsScalarTower R₁ S K] [IsScalarTower R₂ S K]
    (hS : spMap (algebraMap R₁ S) ≫ f₁ = spMap (algebraMap R₂ S) ≫ f₂)
    (honto : ∀ φ : G₁.A n →ₐ[R₁] K, ∃ x, tatePt (τ₁ x) n K = φ)
    (B C : Type) [CommRing B] [Algebra S B] [Algebra.IsIntegral S B] [Algebra R₁ B] [IsScalarTower R₁ S B]
    [CommRing C] [Algebra S C] [Algebra K C] [IsScalarTower S K C] (j : B →ₐ[S] C) (hj : Function.Injective j)
    (u : G₁.A n →ₐ[R₁] B) (u₀ : G₀.A n →ₐ[K] C) (hu : ∀ a, u₀ (s₁.app n a) = j (u a)) (a : G₂.A n) :
    ∃ b, j b = u₀ (s₂.app n a) := by
  let I : Ideal B :=
    { carrier := {b | ∃ c, j c = j b * u₀ (s₂.app n a)}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro b b' ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c + c', by rw [map_add, map_add, hc, hc', add_mul]⟩
      smul_mem' := by
        rintro r b ⟨c, hc⟩
        exact ⟨r * c, by rw [smul_eq_mul, map_mul, map_mul, hc, _root_.mul_assoc]⟩ }
  suffices hI : I = ⊤ by
    obtain ⟨c, hc⟩ : (1 : B) ∈ I := hI ▸ Submodule.mem_top
    exact ⟨c, by rw [hc, map_one, _root_.one_mul]⟩
  by_contra hI
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨σ, hσ⟩ := exists_section (K := K) j hj m
  obtain ⟨x, hx⟩ := honto ((IsScalarTower.toAlgHom R₁ S K).comp ((σ.restrictScalars R₁).comp u))
  let L := Localization.AtPrime m
  let M : Submonoid C := m.primeCompl.map j
  let C' := Localization M
  let κ : L →+* C' := IsLocalization.map C' (j : B →+* C) (T := M) (m.primeCompl.le_comap_map (f := j))
  have hκ : ∀ b, κ (algebraMap B L b) = algebraMap C C' (j b) := fun b => IsLocalization.map_eq _ _
  have hκS : ∀ r, κ (algebraMap S L r) = algebraMap K C' (algebraMap S K r) := fun r => by
    rw [IsScalarTower.algebraMap_apply S B L, hκ, j.commutes, IsScalarTower.algebraMap_apply S K C,
      ← IsScalarTower.algebraMap_apply K C C']
  letI : Algebra R₂ L := ((algebraMap S L).comp (algebraMap R₂ S)).toAlgebra
  have hR₁ : algebraMap R₁ L = (algebraMap S L).comp (algebraMap R₁ S) := IsScalarTower.algebraMap_eq R₁ S L
  obtain ⟨b, hb⟩ := local_step h₁ h₂ h₀ hf l₁ l₂ hθ n hs L C'
    (by
      rw [hR₁, Cris.spMap_comp, Category.assoc, hS, ← Category.assoc, ← Cris.spMap_comp]) κ
    (fun r => by rw [hR₁, RingHom.comp_apply, hκS, ← IsScalarTower.algebraMap_apply R₁ S K])
    (fun r => (hκS _).trans (by rw [← IsScalarTower.algebraMap_apply R₂ S K]))
    ((IsScalarTower.toAlgHom R₁ B L).comp u) x
    (fun a => by
      have h1 : algebraMap R₁ S ((τ₁ x).pt n a) = σ (u a) := IsFractionRing.injective S K (by
        rw [← IsScalarTower.algebraMap_apply]
        exact DFunLike.congr_fun hx a)
      have h2 : u a - algebraMap R₁ B ((τ₁ x).pt n a) ∈ m := hσ (by
        rw [RingHom.mem_ker, map_sub, IsScalarTower.algebraMap_apply R₁ S B, σ.commutes, h1]
        exact sub_self _)
      have h3 := (IsLocalization.AtPrime.to_map_mem_maximal_iff L m _).2 h2
      rw [map_sub, ← IsScalarTower.algebraMap_apply] at h3
      exact h3)
    ((IsScalarTower.toAlgHom K C C').comp u₀)
    (fun a => (congrArg (algebraMap C C') (hu a)).trans (hκ _).symm) a
  obtain ⟨⟨y, t⟩, hy⟩ := IsLocalization.surj m.primeCompl b
  have h4 := congrArg κ hy
  rw [map_mul, hκ, hκ, hb] at h4
  change algebraMap C C' _ * _ = _ at h4
  rw [← map_mul] at h4
  obtain ⟨⟨_, c, hc, rfl⟩, h5⟩ := (IsLocalization.eq_iff_exists M C').1 h4
  refine (m.primeCompl.mul_mem hc t.2) (hIm ⟨c * y, ?_⟩)
  rw [map_mul, map_mul]
  refine h5.symm.trans ?_
  change j c * (u₀ (s₂.app n a) * j t) = _
  ring

end Key

section Descent

variable {R S K A A' A₀ : Type} [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra S K] [Algebra R K]
  [IsScalarTower R S K] [CommRing A] [Bialgebra R A] [CommRing A'] [Bialgebra S A'] [CommRing A₀] [Bialgebra K A₀]

theorem semi_injective [Module.Flat S A'] (hK : Function.Injective (algebraMap S K)) (s : SemiBialgHom (algebraMap S K) A' A₀)
    (hs : Function.Injective s.liftBC) : Function.Injective s := fun a b h =>
  Algebra.TensorProduct.includeRight_injective (A := K) hK (hs (by
    change s.liftBC (1 ⊗ₜ a) = s.liftBC (1 ⊗ₜ b)
    rw [SemiBialgHom.liftBC_tmul, SemiBialgHom.liftBC_tmul, h]))

theorem two_injective [Module.Flat S A'] (hK : Function.Injective (algebraMap S K)) (s : SemiBialgHom (algebraMap S K) A' A₀)
    (hs : Function.Injective s.liftBC) : Function.Injective s.two := by
  let g : K ⊗[S] A' →ₗ[K] A₀ := s.liftBC
  have h1 : Function.Injective (TensorProduct.map g g) := TensorProduct.map_injective_of_flat_flat _ _ hs hs
  have h2 : Function.Injective (Algebra.TensorProduct.includeRight : A' ⊗[S] A' →ₐ[S] K ⊗[S] (A' ⊗[S] A')) :=
    Algebra.TensorProduct.includeRight_injective hK
  have h3 : ∀ c, s.two c = TensorProduct.map g g (TensorProduct.AlgebraTensorModule.distribBaseChange S K A' A' (1 ⊗ₜ c)) :=
    fun c => by
      induction c with
      | zero => simp
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
      | tmul a b => simp [g]
  intro x y h
  rw [h3, h3] at h
  exact h2 ((TensorProduct.AlgebraTensorModule.distribBaseChange S K A' A').injective (h1 h))

theorem exists_semi [Module.Flat S A'] (hK : Function.Injective (algebraMap S K)) (s : SemiBialgHom (algebraMap R K) A A₀)
    (s' : SemiBialgHom (algebraMap S K) A' A₀) (hs : Function.Injective s'.liftBC) (h : ∀ a, ∃ b, s' b = s a) :
    ∃ v : SemiBialgHom (algebraMap R S) A A', ∀ a, s' (v a) = s a := by
  choose f hf using h
  have hi := semi_injective hK s' hs
  let g : A →+* A' :=
    { toFun := f
      map_one' := hi (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hi (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hi (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => hi (by rw [hf, map_add, map_add, hf, hf]) }
  have hg : ∀ a, s' (g a) = s a := hf
  refine ⟨⟨g, fun r a => hi ?_, fun a => hK ?_, fun a => two_injective hK s' hs ?_⟩, hf⟩
  · rw [hg, s.smul_map, s'.smul_map, hg, ← IsScalarTower.algebraMap_apply R S K]
  · rw [← s'.counit_map, hg, s.counit_map, ← IsScalarTower.algebraMap_apply R S K]
  · rw [s'.two_comul, hg, ← s.two_comul]
    generalize Coalgebra.comul (R := R) a = c
    induction c with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [hg]

end Descent

def isoOfBijective {p : ℕ} {R : Type} [CommRing R] {G G' : PDivGroup p R} (f : G ⟶ G')
    (h : ∀ n, Function.Bijective (f.app n)) : G ≅ G' where
  hom := f
  inv := ⟨fun n => (BialgEquiv.ofBijective (f.app n) (h n)).symm, fun n => BialgHom.ext fun a => by
    obtain ⟨b, rfl⟩ := (h (n + 1)).2 a
    have k := fun m x => (BialgEquiv.ofBijective (f.app m) (h m)).symm_apply_apply x
    exact (congrArg (G'.res n) (k (n + 1) b)).trans
      ((k n _).symm.trans (congrArg (BialgEquiv.ofBijective (f.app n) (h n)).symm (res_app f n b).symm))⟩
  hom_inv_id := hom_ext fun n => BialgHom.ext fun a => (BialgEquiv.ofBijective (f.app n) (h n)).apply_symm_apply a
  inv_hom_id := hom_ext fun n => BialgHom.ext fun a => (BialgEquiv.ofBijective (f.app n) (h n)).symm_apply_apply a

theorem iso_bijective {p : ℕ} {R : Type} [CommRing R] {G G' : PDivGroup p R} (e : G ≅ G') (n : ℕ) :
    Function.Bijective (e.hom.app n) :=
  Function.bijective_iff_has_inverse.2 ⟨e.inv.app n, fun a => congrArg (fun f => Hom.app f n a) e.inv_hom_id,
    fun a => congrArg (fun f => Hom.app f n a) e.hom_inv_id⟩

section Main

variable {p : ℕ} [Fact p.Prime] {La : Type} [AddCommGroup La]
  {R S K : Type} [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
  [IsDomain S] [IsIntegrallyClosed S] [IsAlgClosed K] [IsFractionRing S K]
  {Z : Scheme.{0}} {T : Over Z} [GrpObj T] {T₁ : Over (Sp R)} [GrpObj T₁] {T₂ : Over (Sp S)} [GrpObj T₂]
  {T₀ : Over (Sp K)} [GrpObj T₀] {f₁ : Sp R ⟶ Z} {f₂ : Sp S ⟶ Z} {f₀ : Sp K ⟶ Z}
  {φ₁ : T₁.left ⟶ T.left} {φ₂ : T₂.left ⟶ T.left} {φ₀ : T₀.left ⟶ T.left}
  {G₁ : PDivGroup p R} {G₂ : PDivGroup p S} {G₀ : PDivGroup p K}
  {θ₁ : TorsionMap T₁ G₁} {θ₂ : TorsionMap T₂ G₂} {θ₀ : TorsionMap T₀ G₀}
  {τ₁ : La →+ G₁.Tate} {τ₂ : La →+ G₂.Tate} {τ₀ : La →+ G₀.Tate}
  (h₁ : IsGrpPullback T₁ T f₁ φ₁) (h₂ : IsGrpPullback T₂ T f₂ φ₂) (h₀ : IsGrpPullback T₀ T f₀ φ₀)
  (hf₁ : spMap (algebraMap R S) ≫ f₁ = f₂) (hf₂ : spMap (algebraMap S K) ≫ f₂ = f₀)
  {s₁ : SemiHom (algebraMap R K) G₀ G₁} {s₂ : SemiHom (algebraMap S K) G₀ G₂}
  (l₁ : Link φ₁ θ₁ τ₁ φ₀ θ₀ τ₀ s₁) (l₂ : Link φ₂ θ₂ τ₂ φ₀ θ₀ τ₀ s₂)
  (hs₁ : ∀ n, Function.Bijective (s₁.lift.app n)) (hs₂ : ∀ n, Function.Bijective (s₂.lift.app n))

include h₁ h₂ h₀ hf₁ hf₂ l₁ l₂ hs₁ hs₂ in

theorem exists_iso (hθ₁ : θ₁.IsOpenNearZero) (hθ₂ : θ₂.IsOpenNearZero)
    (o₁ : ∀ n (φ : G₁.A n →ₐ[R] K), ∃ x, tatePt (τ₁ x) n K = φ) (o₂ : ∀ n (φ : G₂.A n →ₐ[S] K), ∃ x, tatePt (τ₂ x) n K = φ) :
    ∃ e : G₂ ≅ G₁.baseChange S, ∀ n a, s₂.app n (e.hom.app n (1 ⊗ₜ a)) = s₁.app n a := by
  have hK := IsFractionRing.injective S K
  have hf₀ : spMap (algebraMap R K) ≫ f₁ = f₀ := by
    rw [IsScalarTower.algebraMap_eq R S K, Cris.spMap_comp, Category.assoc, hf₁, hf₂]
  have hSS : spMap (algebraMap S S) ≫ f₂ = spMap (algebraMap R S) ≫ f₁ := by
    rw [hf₁]
    exact (congrArg (· ≫ f₂) (Cris.spMap_id S)).trans (Category.id_comp _)
  have k1 : ∀ n a, ∃ b, s₂.app n b = s₁.app n a := fun n a => by
    letI : Algebra S (G₀.A n) := ((algebraMap K _).comp (algebraMap S K)).toAlgebra
    haveI : IsScalarTower S K (G₀.A n) := .of_algebraMap_eq fun _ => rfl
    exact global_step h₂ h₁ h₀ hf₂ l₂ l₁ hθ₂ n (hs₂ n).2 S hSS (o₂ n) (G₂.A n) (G₀.A n)
      { (s₂.app n).toRingHom with commutes' := (s₂.app n).map_algebraMap } (semi_injective hK _ (hs₂ n).1)
      (AlgHom.id _ _) (AlgHom.id _ _) (fun _ => rfl) a
  choose v hv using fun n => exists_semi hK (s₁.app n) (s₂.app n) (hs₂ n).1 (k1 n)
  let V : SemiHom (algebraMap R S) G₂ G₁ := ⟨v, fun n a => semi_injective hK _ (hs₂ n).1 (by
    rw [← s₂.res_app, hv, hv, s₁.res_app])⟩
  refine ⟨isoOfBijective V.lift fun n => ?_, fun n a => ?_⟩
  · letI : Algebra S (G₀.A n) := ((algebraMap K _).comp (algebraMap S K)).toAlgebra
    haveI : IsScalarTower S K (G₀.A n) := .of_algebraMap_eq fun _ => rfl
    let j : S ⊗[R] G₁.A n →ₐ[S] G₀.A n :=
      AlgHom.comp { (s₂.app n).toRingHom with commutes' := (s₂.app n).map_algebraMap } (V.lift.app n)
    have hj1 : ∀ y, j y = s₁.lift.app n (LinearMap.rTensor _ (IsScalarTower.toAlgHom R S K).toLinearMap y) := fun y => by
      induction y with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r a =>
        refine (congrArg (s₂.app n) (V.lift_app n r a)).trans ?_
        rw [(s₂.app n).smul_map, LinearMap.rTensor_tmul, SemiHom.lift_app]
        exact congrArg _ (hv n a)
    have hj : Function.Injective j := fun x y h => by
      rw [hj1, hj1] at h
      exact Module.Flat.rTensor_preserves_injective_linearMap _ hK ((hs₁ n).1 h)
    refine ⟨fun x y h => hj (congrArg (s₂.app n) h), fun b => ?_⟩
    obtain ⟨y, hy⟩ := global_step h₁ h₂ h₀ hf₀ l₁ l₂ hθ₁ n (hs₁ n).2 S hSS.symm (o₁ n) (S ⊗[R] G₁.A n) (G₀.A n) j hj
      Algebra.TensorProduct.includeRight (AlgHom.id _ _) (fun a => by
        refine (hv n a).symm.trans (congrArg (s₂.app n) ?_)
        exact ((V.lift_app n 1 a).trans (one_smul _ _)).symm) b
    exact ⟨y, semi_injective hK _ (hs₂ n).1 hy⟩
  · exact (congrArg (s₂.app n) ((V.lift_app n 1 a).trans (one_smul _ _))).trans (hv n a)

omit [IsIntegrallyClosed S] [IsAlgClosed K] in
include h₁ h₂ h₀ hf₁ hf₂ l₁ l₂ in

theorem pt_eq [IsCommMonObj T₂] (hT : IsSemiAbelian T₂) (n : ℕ) (a : G₁.A n) (a' : G₂.A n) (ha : s₂.app n a' = s₁.app n a)
    (B : Type) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (z : Tors T₁ (p ^ n) B) (z' : Tors T₂ (p ^ n) B)
    (hz : z.1.left ≫ φ₁ = z'.1.left ≫ φ₂) : θ₁.pt n B z a = θ₂.pt n B z' a' := by
  have hK := IsFractionRing.injective S K
  have flat : ∀ (D : Type) [CommRing D] [Algebra R D] [Algebra S D] [IsScalarTower R S D] [Module.Flat S D]
      (w : Tors T₁ (p ^ n) D) (w' : Tors T₂ (p ^ n) D), w.1.left ≫ φ₁ = w'.1.left ≫ φ₂ →
      θ₁.pt n D w a = θ₂.pt n D w' a' := fun D _ _ _ _ _ w w' hw => by
    let i : D →ₐ[S] K ⊗[S] D := Algebra.TensorProduct.includeRight
    obtain ⟨w₀, hw₀⟩ := exists_tors h₂ h₀ (K ⊗[S] D) (by
      rw [← hf₂, ← Category.assoc, ← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq]) _ (push i w')
    refine Algebra.TensorProduct.includeRight_injective (A := K) hK ?_
    have e₁ := l₁.2 n _ (push (i.restrictScalars R) w) w₀ (((Category.assoc ..).trans
      ((congrArg (spMap (i : D →+* K ⊗[S] D) ≫ ·) hw).trans (Category.assoc ..).symm)).trans hw₀) a
    have e₂ := l₂.2 n _ (push i w') w₀ hw₀ a'
    rw [θ₁.nat n D _ (i.restrictScalars R) w _ rfl] at e₁
    rw [θ₂.nat n D _ i w' _ rfl, ha] at e₂
    exact e₁.trans e₂.symm
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun m hm => ?_)
  rw [map_sub, sub_eq_zero]
  let L := Localization.AtPrime m
  let i : B →ₐ[S] L := IsScalarTower.toAlgHom S B L
  obtain ⟨D, _, _, _, w', c, hc⟩ := exists_flat hT (pow_ne_zero n (Fact.out : p.Prime).ne_zero) L (push i z')
  letI : Algebra R D := ((algebraMap S D).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S D := .of_algebraMap_eq fun _ => rfl
  obtain ⟨w, hw⟩ := exists_tors h₂ h₁ D (by rw [← hf₁, ← Category.assoc, ← Cris.spMap_comp]) _ w'
  have e₀ := congrArg c (flat D w w' hw.symm)
  have e₁ : (push (i.restrictScalars R) z).1 = spOver (c.restrictScalars R) ≫ w.1 :=
    Over.OverMorphism.ext (h₁.1.hom_ext (by
      have hc' : spMap (i : B →+* L) ≫ z'.1.left = spMap (c : D →+* L) ≫ w'.1.left := congrArg Over.Hom.left hc
      change (spMap (i : B →+* L) ≫ z.1.left) ≫ φ₁ = (spMap (c : D →+* L) ≫ w.1.left) ≫ φ₁
      rw [Category.assoc, Category.assoc, hz, ← hw, ← Category.assoc, hc', Category.assoc])
      ((Over.w _).trans (Over.w _).symm))
  have e₂ := (θ₁.nat n B L (i.restrictScalars R) z _ rfl).symm.trans (θ₁.nat n D L (c.restrictScalars R) w _ e₁)
  have e₃ := (θ₂.nat n B L i z' _ rfl).symm.trans (θ₂.nat n D L c w' _ hc)
  exact (DFunLike.congr_fun e₂ a).trans (e₀.trans (DFunLike.congr_fun e₃ a').symm)

end Main

theorem isRestr_of_isRestr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {p : ℕ} [Fact p.Prime]
    {R S K : Type} [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    [IsDomain S] [IsIntegrallyClosed S] [IsAlgClosed K] [IsFractionRing S K] (hp : (p : K) ≠ 0)
    {Z : Scheme.{0}} {tZ : SAB H Z} {f₁ : Sp R ⟶ Z} {f₂ : Sp S ⟶ Z} {f₀ : Sp K ⟶ Z}
    (hf₁ : spMap (algebraMap R S) ≫ f₁ = f₂) (hf₂ : spMap (algebraMap S K) ≫ f₂ = f₀)
    {t₀ : SAB H (Sp K)} (m₀ : SABMap t₀ tZ f₀) {GG₀ : PDivGroup p K} {act₀ : Action (𝓞 E) GG₀} {pol₀ : GG₀ ≅ GG₀.dual}
    {θ₀ : TorsionMap t₀.G GG₀} {ε₀ : (PDivGroup.mu p K).Tate} {τ₀ : Dw.La →+ GG₀.Tate}
    {t : SAB H (Sp R)} (m : SABMap t tZ f₁) {t' : SAB H (Sp S)} (m' : SABMap t' tZ f₂)
    {GG : PDivGroup p R} {act : Action (𝓞 E) GG} {pol : GG ≅ GG.dual} {θ : TorsionMap t.G GG}
    {ε : (PDivGroup.mu p R).Tate} {τ : Dw.La →+ GG.Tate}
    {GG' : PDivGroup p S} {act' : Action (𝓞 E) GG'} {pol' : GG' ≅ GG'.dual} {θ' : TorsionMap t'.G GG'}
    {ε' : (PDivGroup.mu p S).Tate} {τ' : Dw.La →+ GG'.Tate}
    (hG : IsPropG Dw t GG act pol θ ε τ) (r₁ : IsRestr m.φ act pol θ ε τ m₀.φ act₀ pol₀ θ₀ ε₀ τ₀)
    (hG' : IsPropG Dw t' GG' act' pol' θ' ε' τ') (r₂ : IsRestr m'.φ act' pol' θ' ε' τ' m₀.φ act₀ pol₀ θ₀ ε₀ τ₀) :
    IsRestr m.φ act pol θ ε τ m'.φ act' pol' θ' ε' τ' := by
  obtain ⟨hε₁, e₁, ha₁, hp₁, hτ₁, hθ₁⟩ := r₁
  obtain ⟨hε₂, e₂, ha₂, hp₂, hτ₂, hθ₂⟩ := r₂
  have hK := IsFractionRing.injective S K
  let s₁ := (semiHomEquiv GG GG₀).symm e₁.hom
  let s₂ := (semiHomEquiv GG' GG₀).symm e₂.hom
  have hs₁ : ∀ n, Function.Bijective (s₁.lift.app n) := fun n => by
    rw [show s₁.lift = e₁.hom from (semiHomEquiv GG GG₀).apply_symm_apply _]; exact iso_bijective e₁ n
  have hs₂ : ∀ n, Function.Bijective (s₂.lift.app n) := fun n => by
    rw [show s₂.lift = e₂.hom from (semiHomEquiv GG' GG₀).apply_symm_apply _]; exact iso_bijective e₂ n
  have l₁ : Link m.φ θ τ m₀.φ θ₀ τ₀ s₁ :=
    ⟨fun x n a => (congrArg (fun y => TateOver.pt y n (1 ⊗ₜ a)) (hτ₁ x)).trans (_root_.one_mul _), hθ₁⟩
  have l₂ : Link m'.φ θ' τ' m₀.φ θ₀ τ₀ s₂ :=
    ⟨fun x n a => (congrArg (fun y => TateOver.pt y n (1 ⊗ₜ a)) (hτ₂ x)).trans (_root_.one_mul _), hθ₂⟩
  obtain ⟨e, he⟩ := exists_iso m.cart m'.cart m₀.cart hf₁ hf₂ l₁ l₂ hs₁ hs₂ hG.nearZero hG'.nearZero
    (fun n => hG.onto n _ hp) (fun n => hG'.onto n _ hp)
  have he' : ∀ n a, e₂.hom.app n (1 ⊗ₜ e.hom.app n (1 ⊗ₜ a)) = e₁.hom.app n (1 ⊗ₜ a) := he
  have hi : ∀ n (a b : GG'.A n), e₂.hom.app n (1 ⊗ₜ a) = e₂.hom.app n (1 ⊗ₜ b) → a = b := fun n a b k =>
    semi_injective hK (s₂.app n) (hs₂ n).1 k
  refine ⟨fun n => hK ((hε₂ n).symm.trans ((hε₁ n).trans (IsScalarTower.algebraMap_apply R S K _))), e, fun c => baseChange_hom_ext fun n a => hi n _ _ ?_,
    baseChange_hom_ext fun n φ => hi n _ _ ?_, fun x => ?_, fun n B _ _ _ _ z z' hz a => ?_⟩
  · have k₁ := congrArg (fun f => Hom.app f n (1 ⊗ₜ a)) (ha₁ c)
    have k₂ := congrArg (fun f => Hom.app f n (1 ⊗ₜ e.hom.app n (1 ⊗ₜ a))) (ha₂ c)
    exact k₂.symm.trans ((congrArg (Hom.app (act₀ c : GG₀ ⟶ GG₀) n) (he' n a)).trans (k₁.trans (he' n _).symm))
  · let ψ : CartierDual S (GG'.A n) :=
      CartierDual.map (e.inv.app n) (CartierDual.baseChange R S (GG.A n) (1 ⊗ₜ φ))
    have k₁ := congrArg (fun f => Hom.app f n (1 ⊗ₜ φ)) hp₁
    have k₂ := congrArg (fun f => Hom.app f n (1 ⊗ₜ ψ)) hp₂
    refine k₂.symm.trans ((congrArg (pol₀.hom.app n) ?_).trans (k₁.trans (he' n _).symm))
    refine CartierDual.ext_apply fun y => ?_
    obtain ⟨y, rfl⟩ := (iso_bijective e₁ n).2 y
    change CartierDual.baseChange S K (GG'.A n) (1 ⊗ₜ ψ) (e₂.inv.app n (e₁.hom.app n y)) =
      CartierDual.baseChange R K (GG.A n) (1 ⊗ₜ φ) (e₁.inv.app n (e₁.hom.app n y))
    have i₁ : ∀ y, e₁.inv.app n (e₁.hom.app n y) = y := fun y => congrArg (fun f => Hom.app f n y) e₁.inv_hom_id
    have i₂ : ∀ y, e₂.inv.app n (e₂.hom.app n y) = y := fun y => congrArg (fun f => Hom.app f n y) e₂.inv_hom_id
    have i₀ : ∀ y, e.inv.app n (e.hom.app n y) = y := fun y => congrArg (fun f => Hom.app f n y) e.inv_hom_id
    rw [i₁]
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a =>
      have k : ψ (e.hom.app n (1 ⊗ₜ a)) = algebraMap R S (φ a) := by
        change CartierDual.baseChange R S (GG.A n) (1 ⊗ₜ φ) (e.inv.app n (e.hom.app n (1 ⊗ₜ a))) = _
        rw [i₀, CartierDual.baseChange_tmul_tmul, _root_.one_mul, Algebra.algebraMap_eq_smul_one]
      rw [← _root_.mul_one r, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, ← he', i₂,
        CartierDual.baseChange_tmul_tmul, CartierDual.baseChange_tmul_tmul, k, algebraMap_smul]
  · refine TateOver.ext (funext fun n => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => hK ?_))
    refine (l₂.1 x n _).symm.trans ((congrArg ((τ₀ x).pt n) (he n a)).trans ((l₁.1 x n a).trans ?_))
    exact (IsScalarTower.algebraMap_apply R S K _).trans (congrArg _ (_root_.one_mul _).symm)
  · exact pt_eq m.cart m'.cart m₀.cart hf₁ hf₂ l₁ l₂ t'.semi n a _ (he n a) B z z' hz

theorem isRestr_of_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    (X Z : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z) (tZ : SAB H Z), GlobalTheory.IsNormalScheme X →
    ∀ (t₀ : SAB H (Sp (Kbar X))) (m₀ : SABMap t₀ tZ (genPt X ≫ g)), IsOfType Dw t₀ →
    ∀ (GG₀ : PDivGroup p (Kbar X)) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀)
      (ε₀ : (PDivGroup.mu p (Kbar X)).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ →
    ∀ (U U' : AffOp X) (h : U'.1 ≤ U.1) (t : SAB H (Sp U.Bp)) (m : SABMap t tZ (U.toX ≫ g))
      (t' : SAB H (Sp U'.Bp)) (m' : SABMap t' tZ (U'.toX ≫ g))
      (GG : PDivGroup p U.Bp) (act : Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (θ : TorsionMap t.G GG)
      (ε : (PDivGroup.mu p U.Bp).Tate) (τ : Dw.La →+ GG.Tate)
      (GG' : PDivGroup p U'.Bp) (act' : Action (𝓞 E) GG') (pol' : GG' ≅ GG'.dual) (θ' : TorsionMap t'.G GG')
      (ε' : (PDivGroup.mu p U'.Bp).Tate) (τ' : Dw.La →+ GG'.Tate),
      IsPropG Dw t GG act pol θ ε τ → IsRestr m.φ act pol θ ε τ m₀.φ act₀ pol₀ θ₀ ε₀ τ₀ →
      IsPropG Dw t' GG' act' pol' θ' ε' τ' → IsRestr m'.φ act' pol' θ' ε' τ' m₀.φ act₀ pol₀ θ₀ ε₀ τ₀ →
      letI := (AffOp.res h).toAlgebra
      IsRestr m.φ act pol θ ε τ m'.φ act' pol' θ' ε' τ' := by
  intro E _ _ _ H Dw p _ X Z _ _ g tZ _ t₀ m₀ hty GG₀ act₀ pol₀ θ₀ ε₀ τ₀ _ U U' h t m t' m' GG act pol θ ε τ GG' act' pol' θ' ε' τ'
    hG r₁ hG' r₂
  letI := (AffOp.res h).toAlgebra
  haveI : IsScalarTower U.Bp U'.Bp (Kbar X) := .of_algebraMap_eq fun _ => rfl
  haveI := hty.charZero
  have hp : (p : Kbar X) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hf₁ : spMap (algebraMap U.Bp U'.Bp) ≫ U.toX ≫ g = U'.toX ≫ g := by
    rw [← Category.assoc]; exact congrArg (· ≫ g) (AffOp.res_toX h)
  have hf₂ : spMap (algebraMap U'.Bp (Kbar X)) ≫ U'.toX ≫ g = genPt X ≫ g := by
    rw [← Category.assoc, AffOp.val_toX]
  exact isRestr_of_isRestr hp hf₁ hf₂ m₀ m m' hG r₁ hG' r₂

end GlobalTheory.GroupBplus.Rigid

end
