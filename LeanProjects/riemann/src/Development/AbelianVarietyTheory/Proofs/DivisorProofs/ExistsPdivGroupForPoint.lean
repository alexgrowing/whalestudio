import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTangent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.KernelNoTorsion
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RaynaudPDiv

theorem card_torsion_pow_of_divisible : ∀ (p : ℕ) [Fact p.Prime] (M : Type) [CommGroup M], (∀ y : M, ∃ x : M, x ^ p = y) → Nat.card {x : M // x ^ p = 1} ≠ 0 → ∃ h : ℕ, ∀ n : ℕ, Nat.card {x : M // x ^ p ^ n = 1} = p ^ (n * h) := by
  intro p hp M _ hd h1
  have hp' : p.Prime := hp.out
  let K : ℕ → Subgroup M := fun k => (powMonoidHom k : M →* M).ker
  have hK : ∀ k, Nat.card (K k) = Nat.card {x : M // x ^ k = 1} := fun k => rfl
  haveI : Finite (K p) := Nat.finite_of_card_ne_zero h1
  obtain ⟨h, hh⟩ := (IsPGroup.iff_card (p := p) (G := K p)).1 fun g => ⟨1, Subtype.ext (by rw [pow_one]; exact g.2)⟩
  refine ⟨h, fun n => ?_⟩
  induction n with
  | zero =>
    simp only [pow_zero, pow_one, zero_mul]
    exact Nat.card_unique
  | succ n ih =>
    let f : K (p ^ (n + 1)) →* K (p ^ n) := ((powMonoidHom p : M →* M).comp (K _).subtype).codRestrict _
      fun x => show (x.1 ^ p) ^ p ^ n = 1 by rw [← pow_mul, ← pow_succ']; exact x.2
    have hf : Function.Surjective f := fun y => by
      obtain ⟨x, hx⟩ := hd y.1
      exact ⟨⟨x, show x ^ p ^ (n + 1) = 1 by rw [pow_succ', pow_mul, hx]; exact y.2⟩, Subtype.ext hx⟩
    have hk : Nat.card f.ker = Nat.card (K p) := Nat.card_congr
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, show x.1 ^ p ^ (n + 1) = 1 by
          rw [pow_succ', pow_mul, show x.1 ^ p = 1 from x.2, one_pow]⟩, Subtype.ext x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← hK, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, hk, hh,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hK, ih, ← pow_add, add_mul,
      _root_.one_mul]

theorem exists_isPullback_torsion : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] [Smooth A.hom] (N : ℕ), IsFinite (torsion A N).hom → Flat (torsion A N).hom → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (y : SpAlg O R ⟶ A), Module.Finite O R ∧ Module.Projective O R ∧ IsPullback y.left (spMap (algebraMap O R)) (mulN A N).left η[A].left := by
  intro O _ A _ _ N h1 h2
  have : LocallyOfFinitePresentation ((mulN A N).left ≫ A.hom) := by rw [Over.w]; infer_instance
  have h3 := TangentCrit.locallyOfFinitePresentation_of_comp (mulN A N).left A.hom
  let e : Sp O ⟶ A.left := η[A].left
  let X := (torsion A N).left
  have H0 : IsPullback (torsion.ι A N).left (torsion A N).hom (mulN A N).left e := by
    have h := (IsPullback.of_hasPullback (mulN A N) (η : 𝟙_ _ ⟶ A)).map (Over.forget _)
    have h' : (pullback.snd (mulN A N) (η : 𝟙_ _ ⟶ A)).left = (torsion A N).hom :=
      (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN A N) (η : 𝟙_ _ ⟶ A)))
    exact h' ▸ h
  have : IsAffine X := isAffine_of_isAffineHom (torsion A N).hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ (torsion A N).hom)
  have H : IsPullback (X.isoSpec.inv ≫ (torsion.ι A N).left) (Spec.map ψ) (mulN A N).left e := by
    rw [hψ]
    refine H0.of_iso X.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have f1 : ψ.hom.Finite := (IsFinite.SpecMap_iff _).1 (by rw [hψ]; infer_instance)
  have f2 : ψ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 (by rw [hψ]; infer_instance)
  have f3 : ψ.hom.FinitePresentation := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1
    (MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H h3)
  let _ : Algebra O Γ(X, ⊤) := ψ.hom.toAlgebra
  have : Module.Finite O Γ(X, ⊤) := f1
  have : Module.Flat O Γ(X, ⊤) := f2
  have : Algebra.FinitePresentation O Γ(X, ⊤) := f3
  have := Module.FinitePresentation.of_finite_of_finitePresentation O Γ(X, ⊤)
  exact ⟨Γ(X, ⊤), inferInstance, inferInstance,
    Over.homMk (X.isoSpec.inv ≫ (torsion.ι A N).left) (by rw [Category.assoc, Over.w]; exact hψ.symm),
    inferInstance, Module.Flat.projective_of_finitePresentation, H⟩

theorem finrank_torsion : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] [Smooth B.hom] (N : ℕ), (N : K) ≠ 0 → ∀ (S : Type) [CommRing S] [Algebra K S] [Module.Finite K S] (y : SpAlg K S ⟶ B), IsPullback y.left (spMap (algebraMap K S)) (mulN B N).left η[B].left → Module.finrank K S = Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ N = 1} ∧ Module.finrank K S ≠ 0 := by
  intro K _ _ B _ _ _ N hN S _ _ _ y h
  have he : Etale (mulN B N).left := GrpTangent.etale_mulN B (by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have : Algebra.Etale K S := RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1
    (MorphismProperty.of_isPullback (P := @Etale) h he))
  have hy := AbelianPDiv.isUnivTorsion_of_isPullback y h
  have : Nontrivial S := hy.counitMap.toRingHom.domain_nontrivial
  refine ⟨?_, Module.finrank_pos.ne'⟩
  rw [← natCard_algHom_eq_finrank_of_etale K S K]
  let i : SpAlg K K ≅ 𝟙_ (Over (Sp K)) := Over.isoMk (Iso.refl _) (by
    exact (Category.comp_id _).trans (Cris.spMap_id K).symm)
  refine Nat.card_eq_of_bijective (fun φ => ⟨i.inv ≫ spOver φ ≫ y, by
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hy.1, MonObj.comp_one, MonObj.comp_one]⟩) ⟨fun φ ψ e => ?_, fun x => ?_⟩
  · exact hy.inj ((cancel_epi i.inv).1 (congrArg Subtype.val e))
  · obtain ⟨φ, hφ, -⟩ := hy.2 K (i.hom ≫ x.1) (by rw [← MonObj.comp_pow, x.2, MonObj.comp_one])
    exact ⟨φ, Subtype.ext (by simp only [hφ, Iso.inv_hom_id_assoc])⟩

theorem exists_tateEquiv : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (G : PDivGroup p O) (t : G.TorsionTower A), ∃ e : G.Tate ≃ₗ[ℤ_[p]] GlobalTheory.HTLat.Tate p (specO O O ⟶ A), ∀ (s : G.Tate) (n : ℕ), (e s).lev n = spOver (s.pt n) ≫ t.y n := by
  intro p _ O _ A _ _ G t
  have hc : ∀ (n : ℕ) (φ : G.A (n + 1) →ₐ[O] O), spOver (φ.comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1))) ≫ t.y n =
      (spOver φ ≫ t.y (n + 1)) ^ p := fun n φ => by
    rw [← spOver_comp, Category.assoc, t.mulP_y, MonObj.comp_pow]
  let f : G.Tate →ₗ[ℤ_[p]] GlobalTheory.HTLat.Tate p (specO O O ⟶ A) :=
    { toFun := fun s => Tate.mk (fun n => spOver (s.pt n) ≫ t.y n) fun n =>
        ⟨(t.exists_iff n _).1 ⟨_, rfl⟩, (hc n _).symm.trans (by rw [s.compat])⟩
      map_add' := fun s s' => Tate.ext fun n => map_mul (t.pts n O) (s.conv n) (s'.conv n)
      map_smul' := fun a s => Tate.ext fun n => map_pow (t.pts n O) (s.conv n) _ }
  refine ⟨.ofBijective f ⟨fun s s' h => TateOver.ext (funext fun n => t.inj n O _ _ (congrArg (·.lev n) h)),
    fun z => ⟨⟨fun n => t.lift n (z.lev n) (z.lev_pow n), fun n => t.inj n O _ _ ?_⟩,
      Tate.ext fun n => t.lift_y n _ (z.lev_pow n)⟩⟩, fun _ _ => rfl⟩
  rw [hc, t.lift_y, t.lift_y]
  exact z.lev_succ n

theorem exists_dual_tate : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] (G : PDivGroup p O) (t : G.TorsionTower A) (χ : Tv A p), ∃ c : G.dual.Tate, ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ : G.A n →ₐ[O] B) (w : specO O B ⟶ torsion A (p ^ n)), w ≫ torsion.ι A (p ^ n) = spOver φ ≫ t.y n → φ (charElem c n) = (unitOf (w ≫ χ.χ n) : B) := by
  intro p _ O _ A _ G t χ
  let l : ∀ n, specO O (G.A n) ⟶ torsion A (p ^ n) := fun n => torsionLift (t.y n) (t.y_pow n)
  have hl : ∀ n, l n ≫ torsion.ι A (p ^ n) = t.y n := fun n => torsionLift_ι _ _
  let u : ∀ n, G.A n := fun n => unitOf (l n ≫ χ.χ n)
  have h0 : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ : G.A n →ₐ[O] B),
      φ (u n) = (unitOf ((spOver φ ≫ l n) ≫ χ.χ n) : B) := fun n B _ _ φ => by
    rw [Category.assoc]
    exact (GmPoints.unitOf_ptMap φ _).symm
  have hm : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ ψ : WithConv (G.A n →ₐ[O] B)),
      (φ * ψ).ofConv (u n) = φ.ofConv (u n) * ψ.ofConv (u n) := fun n B _ _ φ ψ => by
    rw [h0, h0, h0, ← Units.val_mul, ← GmPoints.unitOf_mul]
    refine congrArg (fun z : specO O B ⟶ Gm (Sp O) => (unitOf z : B)) (χ.isChar n _ _ _ _ ?_)
    rw [Category.assoc, Category.assoc, Category.assoc, hl]
    exact t.mul n B φ ψ
  have hg : ∀ n, IsGroupLikeElem O (u n) := fun n => by
    constructor
    · have h := hm n O 1 1
      rw [_root_.mul_one] at h
      exact ((Units.isUnit _).map (1 : WithConv (G.A n →ₐ[O] O)).ofConv).mul_left_cancel
        (h.symm.trans (_root_.mul_one _).symm)
    · have h := hm n (G.A n ⊗[O] G.A n) (WithConv.toConv Algebra.TensorProduct.includeLeft)
        (WithConv.toConv Algebra.TensorProduct.includeRight)
      rw [AlgHom.convMul_apply] at h
      simpa using h
  have hp : ∀ n, u n ^ p ^ n = 1 := fun n => by
    have h := convPow_apply_groupLike (WithConv.toConv (AlgHom.id O (G.A n))) (hg n) (p ^ n)
    rw [G.pts_pow_self] at h
    refine h.symm.trans ?_
    simp [(hg n).counit_eq_one]
  have hr : ∀ n, G.res n (u (n + 1)) = u n := fun n =>
    (h0 (n + 1) _ (G.res n : G.A (n + 1) →ₐ[O] G.A n)).trans (congrArg (fun z : specO O (G.A n) ⟶ Gm (Sp O) => (unitOf z : G.A n))
      (χ.compat n _ _ _ ((hl n).trans ((t.res n).symm.trans (by rw [Category.assoc, hl])))).symm)
  let f : G ⟶ PDivGroup.mu p O := ⟨fun n => muChar (u n) (hg n) (hp n), fun n => mu_bialgHom_ext <| by
    rw [BialgHom.comp_apply, BialgHom.comp_apply, muChar_muT, hr, muRes_muT, muChar_muT]⟩
  refine ⟨(charHom G).symm f, fun n B _ _ φ w hw => ?_⟩
  rw [← charHom_app_muT, LinearEquiv.apply_symm_apply,
    show w = spOver φ ≫ l n from torsion_hom_ext (by rw [Category.assoc, hl, hw]), ← h0]
  exact congrArg φ (muChar_muT _ (hg n) (hp n))

theorem lie_dlog : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (A : Over (Sp O)) [GrpObj A] (G : PDivGroup p O) (t : G.TorsionTower A) (χ : Tv A p) (c : G.dual.Tate), (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ : G.A n →ₐ[O] B) (w : specO O B ⟶ torsion A (p ^ n)), w ≫ torsion.ι A (p ^ n) = spOver φ ≫ t.y n → φ (charElem c n) = (unitOf (w ≫ χ.χ n) : B)) → ∀ (x : LieG A) (y : G.Lie), t.LieCorr y x.1 → y (PDivGroup.dlog G c) = (dlogTv χ).1 x := by
  intro p _ O _ _ A _ G t χ c hc x y h
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, ← Ideal.Quotient.eq]
  obtain ⟨ψ, h1, h2⟩ := h.2 n
  let w : specO O (DualNumber (ModPow p O n)) ⟶ torsion A (p ^ n) := torsionLift _ (epsRedPow_pow (p := p) h.1 n)
  have h3 : w ≫ torsion.ι A (p ^ n) = epsRedPow p n x.1 := torsionLift_ι _ _
  have h4 : epsTo O (ModPow p O n) = dualBC (Algebra.ofId O (ModPow p O n)) := AlgHom.ext fun z => by
    ext <;> simp [dualBC, TrivSqZeroExt.lift_def, TrivSqZeroExt.algebraMap_eq_inl']
  have h0 : (p : ModPow p O n) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have h5 := isAl_dlogTv χ n _ h0 x w (h3.trans (by rw [← h4]; rfl))
  refine (h2 _ (charElem c n) (dlog_val c n).symm).trans ?_
  rw [hc n _ ψ w (h3.trans h1.symm), h5]
  simp

theorem exists_tower (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] (h0 : (p : O) ≠ 0)
    (A : Over (Sp O)) [GrpObj A] (hA : IsSemiAbelian A)
    (hf : ∀ N, 1 ≤ N → IsFinite (torsion A N).hom ∧ Flat (torsion A N).hom) :
    ∃ G : PDivGroup p O, Nonempty (G.TorsionTower A) := by
  have := hA.comm
  have := hA.smooth
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  let B := (Over.pullback (spMap (algebraMap O K))).obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom _))
  choose R _ _ y h1 h2 H using fun n : ℕ =>
    exists_isPullback_torsion O A (p ^ n) (hf _ (one_le_ppow p n)).1 (hf _ (one_le_ppow p n)).2
  have h := fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  have hk : ∀ n, Module.finrank K (K ⊗[O] R n) = Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ p ^ n = 1} ∧
      Module.finrank K (K ⊗[O] R n) ≠ 0 := fun n => by
    obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange (y n) (H n) K
    exact finrank_torsion K B _ (by
      rw [← map_natCast (algebraMap O K), Nat.cast_pow]
      exact (map_ne_zero_iff _ hi).2 (pow_ne_zero _ h0)) _ y' h'
  obtain ⟨d, hd⟩ := card_torsion_pow_of_divisible p (𝟙_ (Over (Sp K)) ⟶ B)
    (SS.torusExtension_points_divisible K B (hA.fibres K _) p hp.out.pos)
    (by have h := (hk 1).2; rwa [(hk 1).1, pow_one] at h)
  have hr : ∀ n (q : PrimeSpectrum O), Module.rankAtStalk (R n) q = p ^ (n * d) := fun n q => by
    rw [← Module.rankAtStalk_eq_of_le_of_finite_of_flat (R n)
        (p := PrimeSpectrum.comap (algebraMap O K) ⊥) (q := q) ?_, ← Module.rankAtStalk_baseChange,
      Module.rankAtStalk_eq_finrank_of_free, (hk n).1, hd]
    · rfl
    · intro a ha
      have ha' : algebraMap O K a = 0 := ha
      rw [(map_eq_zero_iff _ hi).1 ha']
      exact zero_mem _
  choose r r1 r2 r3 using fun n : ℕ =>
    (h n).exists_res (h (n + 1)) (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := d
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := hr
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

theorem exists_lieEquiv (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (A : Over (Sp O)) [GrpObj A] [Smooth A.hom] (G : PDivGroup p O) (t : G.TorsionTower A) :
    ∃ l : LieG A ≃ G.Lie, ∀ x, t.LieCorr (l x) x.1 := by
  have ht : ∀ v : epsR O ⟶ A, ptMap (TrivSqZeroExt.fstHom O O O) ≫ v = toUnit (specO O O) ≫ η[A] ↔
      IsTangent v := fun v => by
    have e : (toUnit (specO O O) ≫ η[A]).left = η[A].left :=
      (AbelianPDiv.one_left O).trans ((congrArg (· ≫ η[A].left) (Cris.spMap_id O)).trans (Category.id_comp _))
    exact ⟨fun h => (congrArg Over.Hom.left h).trans e, fun h => Over.OverMorphism.ext (h.trans e.symm)⟩
  choose f hf using fun x : LieG A => (t.existsUnique_lieCorr ((ht _).1 x.2)).exists
  refine ⟨.ofBijective f ⟨fun x x' e => Subtype.ext ?_, fun y => ?_⟩, hf⟩
  · exact (TorsionTower.existsUnique_tangent p O G A t (f x)).unique (hf x) (e ▸ hf x')
  · obtain ⟨v, hv⟩ := (TorsionTower.existsUnique_tangent p O G A t y).exists
    exact ⟨⟨v, (ht v).2 hv.1⟩, (hf _).unique_left hv⟩

theorem exists_generator {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (ε : Eps p C) :
    ∃ ζ : (PDivGroup.mu p O).Tate, Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧
      ∀ n, algebraMap O C (muRoot ζ n) = ε.1.lev n := by
  have hi := hv.hom_inj
  have h1 : ∀ n, ((ε.1.lev n : Cˣ) : C) ^ p ^ n = 1 := fun n => by
    rw [← Units.val_pow_eq_pow_val, ε.1.lev_pow, Units.val_one]
  choose z hz using fun n => hv.exists_of_le_one (r := (ε.1.lev n : C))
    ((pow_le_one_iff_of_nonneg zero_le (Nat.one_le_iff_ne_zero.1 (one_le_ppow p n))).1
      (show v (ε.1.lev n : C) ^ p ^ n ≤ 1 by rw [← map_pow, h1, map_one]))
  let ζ := muTate O z (hi (by simpa [hz] using h1 0)) fun n => hi (by
    rw [map_pow, hz, hz, ← Units.val_pow_eq_pow_val, ε.1.lev_succ])
  have hζ : ∀ n, algebraMap O C (muRoot ζ n) = ε.1.lev n := fun n => by rw [muRoot_muTate, hz]
  have hs : ∀ (a : ℤ_[p]) n, algebraMap O C (muRoot (a • ζ) n) = (a • ε.1).lev n := fun a n => by
    rw [muRoot_smul, map_pow, hζ, Tate.lev_smul, Units.val_pow_eq_pow_val]
  refine ⟨ζ, ⟨fun a b e => ε.bijective.1 (Tate.ext fun n => Units.ext ?_), fun x => ?_⟩, hζ⟩
  · exact (hs a n).symm.trans ((congrArg (fun w => algebraMap O C (muRoot w n)) e).trans (hs b n))
  · have hx : ∀ n, algebraMap O C (muRoot x n) ^ p ^ n = 1 := fun n => by
      rw [← map_pow, muRoot_pow_self, map_one]
    obtain ⟨a, ha⟩ := ε.bijective.2 (Tate.mk (fun n => Units.ofPowEqOne _ _ (hx n)
      (Nat.one_le_iff_ne_zero.1 (one_le_ppow p n))) fun n => ⟨Units.ext (hx n), Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_ofPowEqOne, Units.val_ofPowEqOne, ← map_pow, muRoot_succ_pow])⟩)
    exact ⟨a, muRoot_ext fun n => hi ((hs a n).trans (congrArg (fun w => ((w.lev n : Cˣ) : C)) ha))⟩

theorem exists_pDivGroup_raynaud : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, PDivGroup.pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) ∧ ∀ x t, l x (PDivGroup.dlog (G := G) (c t)) = (P.al₀ t).1 x := by
  intro p hp C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hi := P.integers.hom_inj
  haveI : IsDomain O := hi.isDomain (algebraMap O C)
  have hA := isSemiAbelian_of_isGt _ _ P.Gt ⟨P.D⟩
  haveI := hA.smooth
  obtain ⟨G, ⟨t⟩⟩ := exists_tower p O (fun h => hp.out.ne_zero ((Nat.cast_eq_zero (R := C)).1 (by
    rw [← map_natCast (algebraMap O C), h, map_zero]))) P.Gt hA P.finite_flat
  obtain ⟨e, he⟩ := exists_tateEquiv p O P.Gt G t
  obtain ⟨l, hl⟩ := exists_lieEquiv p O P.Gt G t
  obtain ⟨ζ, hζ, hζ'⟩ := exists_generator P.integers P.eps
  choose c hc using fun s : P.T => exists_dual_tate p O P.Gt G t (P.weilChar s)
  have hu : ∀ s n, charElem (c s) n = (unitOf (torsionLift (t.y n) (t.y_pow n) ≫ (P.weilChar s).χ n) : G.A n) :=
    fun s n => hc s n _ (AlgHom.id O _) _ (by rw [torsionLift_ι, spOver_id, Category.id_comp])
  have hx : ∀ {a b : G.dual.Tate}, (∀ n, charElem a n = charElem b n) → a = b := fun h =>
    (charHom G).injective (hom_mu_ext fun n => by rw [charHom_app_muT, charHom_app_muT, h])
  have hadd : ∀ s s', c (s + s') = c s + c s' := fun s s' => hx fun n => by
    rw [charElem_add, hu, hu, hu, P.weilChar_add, MonObj.comp_mul, GmPoints.unitOf_mul, Units.val_mul]
  have hpow : ∀ (R : Type) [CommRing R] [Algebra O R] (w : specO O R ⟶ Gm (Sp O)) (k : ℕ),
      unitOf (w ^ k) = unitOf w ^ k := fun R _ _ w k => map_pow (MonoidHom.mk' unitOf GmPoints.unitOf_mul) w k
  have hsm : ∀ (a : ℤ_[p]) s, c (a • s) = a • c s := fun a s => hx fun n => by
    have h : (P.weilChar (a • s)).χ n = (P.weilChar s).χ n ^ digit n a := P.char_ext fun w => by
      rw [P.isWeilChar_weilChar, MonObj.comp_pow, hpow, Units.val_pow_eq_pow_val, map_pow,
        P.isWeilChar_weilChar, Tate.lev_smul, weil_pow_right (one_le_ppow p n) (s.lev_pow n) (P.toA_pow w),
        Units.val_pow_eq_pow_val]
    rw [charElem_smul, hu, hu, h, MonObj.comp_pow, hpow, Units.val_pow_eq_pow_val]
  refine ⟨G, e.trans (LinearEquiv.ofInjective _ (Tate.map_injective P.toA_injective)), l,
    ⟨⟨c, hadd⟩, hsm⟩, ζ, hζ, fun s s' => muRoot_ext fun n => hi ?_,
    fun x s => lie_dlog p O P.Gt G t _ _ (hc s) x _ (hl x)⟩
  have hw := torsionLift_ι _ ((t.exists_iff n _).1 ⟨s.pt n, rfl⟩)
  rw [muRoot_pairing, muRoot_smul, map_pow, hζ', ← Units.val_pow_eq_pow_val, pow_pairT]
  refine (congrArg (algebraMap O C) (hc s' n O _ _ hw)).trans ((P.isWeilChar_weilChar s' n _).trans ?_)
  rw [hw, ← he]
  rfl

end GlobalTheory.RaynaudPDiv
