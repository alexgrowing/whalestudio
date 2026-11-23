import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PicAffineSpace

theorem form_smul_comm {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (φ : M →ₗ[B] B) (s m : M) : φ s • m = φ m • s := by
  have h := congrArg (fun z => TensorProduct.lid B M (φ.rTensor M z))
    (Module.Invertible.tmul_comm (R := B) (m₁ := s) (m₂ := m))
  simpa using h

theorem exists_pairing_notMem {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Invertible A M] (P : Ideal A) (hP : P ≠ ⊤) : ∃ (φ : M →ₗ[A] A) (m : M), φ m ∉ P := by
  by_contra h
  push Not at h
  apply hP
  rw [Ideal.eq_top_iff_one]
  obtain ⟨z, hz⟩ := (Module.Invertible.bijective (R := A) (M := M)).2 1
  rw [← hz]
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ m => simpa using h φ m
  | add x y hx hy => rw [map_add]; exact P.add_mem hx hy

theorem exists_generator_away {A B M σ : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] (E : MvPolynomial σ A ≃+* B) [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (P : Ideal A) (hP : P ≠ ⊤) :
    ∃ (s : M) (a : A), a ∉ P ∧ ∀ m : M, ∃ r : B, E (MvPolynomial.C a) • m = r • s := by
  letI : Algebra A B := ((E : MvPolynomial σ A →+* B).comp (algebraMap A _)).toAlgebra
  obtain ⟨M₀, hM₀⟩ := (pic_mapAlgebra_mvPolynomial_bijective A σ).2
    (CommRing.Pic.mapRingHom (E.symm : B →+* MvPolynomial σ A) (CommRing.Pic.mk B M))
  have h : CommRing.Pic.mapAlgebra A B M₀ = CommRing.Pic.mk B M := by
    have := congrArg (CommRing.Pic.mapRingHom (E : MvPolynomial σ A →+* B)) hM₀
    rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom,
      CommRing.Pic.mapRingHom_mapRingHom, RingEquiv.comp_symm, CommRing.Pic.mapRingHom_id_apply] at this
    rw [← CommRing.Pic.mapRingHom_algebraMap]
    exact this
  obtain ⟨e⟩ : Nonempty (B ⊗[A] M₀ ≃ₗ[B] M) := CommRing.Pic.mk_eq_mk_iff.mp h
  obtain ⟨φ, m₀, hφ⟩ := exists_pairing_notMem (M := M₀) P hP
  let ψ : M →ₗ[B] B := (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ
    φ.baseChange B ∘ₗ e.symm.toLinearMap
  refine ⟨e (1 ⊗ₜ m₀), φ m₀, hφ, fun m => ⟨ψ m, ?_⟩⟩
  rw [← form_smul_comm]
  congr 1
  simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul]
  rw [Algebra.smul_def, _root_.mul_one]
  rfl

variable {X Y : Scheme.{0}}

theorem exists_lbIso_pull_of_local (p : Y ⟶ X) (e : X ⟶ Y) (he : e ≫ p = 𝟙 X) {N : LB Y} (hN : N.IsLB)
    (hu : ∀ V : X.Opens, IsAffineOpen V → ∀ u : Γ(Y, p ⁻¹ᵁ V)ˣ, ∃ v : Γ(X, V)ˣ, u = pullU p V v)
    (hl : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ s : ∀ i, Γ(Y, p ⁻¹ᵁ U ⊓ N.U i)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : N.ι), p (f z) ∈ U → f z ∈ N.U i → f z ∈ N.U j →
        gm f z _ (s i) = gm f z _ (N.g i j) * gm f z _ (s j)) :
    ∃ N₀ : LB X, N₀.IsLB ∧ LBIso N (N₀.pull p) := by
  choose U hU s hs using hl
  have hep : ∀ x : X, p (e x) = x := fun x => congrArg (fun q => q x) he
  have base : ∀ (W : X.Opens) (u : Γ(Y, p ⁻¹ᵁ W)ˣ) (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z), p (f z) ∈ W →
      gm ((f ≫ p) ≫ e) z _ u = gm f z _ u := by
    intro W u Z f z hz
    obtain ⟨V, hV, hx, hVW⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ p (f z) ∈ V ∧ V ≤ W := by
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hz W.isOpen
      exact ⟨V, hV, hx, hVW⟩
    obtain ⟨v, hv⟩ := hu V hV (res (p.preimage_mono hVW) u)
    have hx' : p (((f ≫ p) ≫ e) z) ∈ V := (congrArg (· ∈ V) (hep (p (f z)))).mpr hx
    rw [← gm_res f z (p.preimage_mono hVW) hx, ← gm_res _ z (p.preimage_mono hVW) hx', hv,
      gm_pull _ _ _ _ hx, gm_pull _ _ _ _ hx', Category.assoc, he, Category.comp_id]
  have quot : ∀ x y : X, ∃ h : Γ(Y, p ⁻¹ᵁ (U x ⊓ U y))ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i : N.ι),
      p (f z) ∈ U x → p (f z) ∈ U y → f z ∈ N.U i →
        gm f z _ h = gm f z _ (s y i) * (gm f z _ (s x i))⁻¹ := by
    intro x y
    let W : N.ι → Y.Opens := fun i => p ⁻¹ᵁ (U x ⊓ U y) ⊓ N.U i
    have l₁ : ∀ i, W i ≤ p ⁻¹ᵁ U x ⊓ N.U i := fun i _ hz => ⟨hz.1.1, hz.2⟩
    have l₂ : ∀ i, W i ≤ p ⁻¹ᵁ U y ⊓ N.U i := fun i _ hz => ⟨hz.1.2, hz.2⟩
    have v : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i : N.ι), f z ∈ W i →
        gm f z (W i) (res (l₂ i) (s y i) * (res (l₁ i) (s x i))⁻¹) =
          gm f z _ (s y i) * (gm f z _ (s x i))⁻¹ := fun Z f z i hz => by
      rw [map_mul, map_inv, gm_res f z _ hz, gm_res f z _ hz]
    obtain ⟨h, hh⟩ := glue_unit (p ⁻¹ᵁ (U x ⊓ U y)) W (fun _ => inf_le_left) (fun z hz => by
        obtain ⟨i, hi⟩ := exists_chart hN z
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hz, hi⟩)
      (fun i => res (l₂ i) (s y i) * (res (l₁ i) (s x i))⁻¹) (fun i j z hz => by
        rw [v _ _ z i hz.1, v _ _ z j hz.2, hs x _ (𝟙 Y) z i j hz.1.1.1 hz.1.2 hz.2.2,
          hs y _ (𝟙 Y) z i j hz.1.1.2 hz.1.2 hz.2.2, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel,
          _root_.one_mul])
    refine ⟨h, fun Z f z i hx hy hi => ?_⟩
    have hz : f z ∈ W i := ⟨⟨hx, hy⟩, hi⟩
    rw [← v Z f z i hz, ← hh i, gm_res f z _ hz]
  choose h hh using quot
  have l : ∀ x y, U x ⊓ U y ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (U x ⊓ U y)) := fun x y z hz =>
    (congrArg (· ∈ U x ⊓ U y) (hep z)).mpr hz
  let N₀ : LB X := ⟨X, U, fun x y => res (l x y) (pullU e _ (h x y))⟩
  have g₀ : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (x y : X), f z ∈ U x → f z ∈ U y →
      gm f z (U x ⊓ U y) (N₀.g x y) = gm (f ≫ e) z _ (h x y) := fun Z f z x y hx hy =>
    (gm_res f z (l x y) ⟨hx, hy⟩ _).trans (gm_pull f e z _ (l x y ⟨hx, hy⟩) _)
  have coc : ∀ (z : X) (a b c : X), z ∈ U a → z ∈ U b → z ∈ U c →
      gm (𝟙 X) z (U a ⊓ U b) (N₀.g a b) * gm (𝟙 X) z (U b ⊓ U c) (N₀.g b c) =
        gm (𝟙 X) z (U a ⊓ U c) (N₀.g a c) := by
    intro z a b c ha hb hc
    obtain ⟨i, hi⟩ := exists_chart hN (e z)
    have m : ∀ d, z ∈ U d → p ((𝟙 X ≫ e) z) ∈ U d := fun d hd => (congrArg (· ∈ U d) (hep z)).mpr hd
    rw [g₀ _ _ z a b ha hb, g₀ _ _ z b c hb hc, g₀ _ _ z a c ha hc,
      hh a b _ _ z i (m a ha) (m b hb) hi, hh b c _ _ z i (m b hb) (m c hc) hi,
      hh a c _ _ z i (m a ha) (m c hc) hi, mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  refine ⟨N₀, ⟨top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hU x⟩,
    fun a => unit_ext fun z hz => ?_, fun a b c => unit_ext fun z hz => ?_⟩, ?_⟩
  · rw [gm_res _ z _ hz, map_one]
    exact mul_eq_left.1 (coc z a a a hz hz hz)
  · exact (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res _ z _ hz _) (gm_res _ z _ hz _)).trans
      ((coc z a b c hz.1.1 hz.1.2 hz.2).trans (gm_res _ z _ hz _).symm))
  · have lw : ∀ (J : (N₀.pull p).ι) (k : N.ι), (N₀.pull p).U J ⊓ N.U k ≤ p ⁻¹ᵁ U (J PUnit.unit) ⊓ N.U k :=
      fun J k z hz => ⟨mem_pull.1 hz.1, hz.2⟩
    refine ⟨⟨fun q => (res (lw q.1 q.2) (s (q.1 PUnit.unit) q.2))⁻¹⟩, (isGen_iff _).2 ?_⟩
    intro Z f z x y k k' hx hy hk hk'
    have w : ∀ (a : X) (i : N.ι), p (f z) ∈ U a → f z ∈ N.U i →
        gw (L := N₀) (⟨fun q => (res (lw q.1 q.2) (s (q.1 PUnit.unit) q.2))⁻¹⟩ : LB.Iso N (N₀.pull p)) f z a i =
          (gm f z _ (s a i))⁻¹ := fun a i ha hi =>
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res f z (lw (fun _ => a) i) ⟨mem_pull.2 ha, hi⟩ _))
    have e₁ := (g₀ Z (f ≫ p) z x y hx hy).trans ((base (U x ⊓ U y) _ Z f z ⟨hx, hy⟩).trans (hh x y Z f z k hx hy hk))
    rw [w x k hx hk, w y k' hy hk']
    refine Eq.trans ?_ (congrArg (fun t => t * _ * _) e₁).symm
    rw [hs y Z f z k k' hy hk hk']
    have grp : ∀ {G : Type} [CommGroup G] (a b c : G), a⁻¹ = b * c * a⁻¹ * b⁻¹ * c⁻¹ := fun a b c => by
      rw [_root_.mul_assoc, ← mul_inv, mul_right_comm, mul_inv_cancel, _root_.one_mul]
    exact grp _ _ _

theorem exists_local_generator (p : Y ⟶ X) {N : LB Y} (hN : N.IsLB) {V : X.Opens}
    (hV : IsAffineOpen (p ⁻¹ᵁ V)) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] {σ : Type}
    (E : MvPolynomial σ Γ(X, V) ≃+* Γ(Y, p ⁻¹ᵁ V)) (hE : ∀ a, E (MvPolynomial.C a) = (p.app V).hom a)
    {x : X} (hx : x ∈ V) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ s : ∀ i, Γ(Y, p ⁻¹ᵁ U ⊓ N.U i)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : N.ι), p (f z) ∈ U → f z ∈ N.U i → f z ∈ N.U j →
        gm f z _ (s i) = gm f z _ (N.g i j) * gm f z _ (s j) := by
  haveI := SecOn.invertible hN hV
  obtain ⟨s, a, ha, hs⟩ := exists_generator_away (M := SecOn N (p ⁻¹ᵁ V)) E
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ V x hx).hom)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
  rw [hE] at hs
  have l : ∀ i, p ⁻¹ᵁ X.basicOpen a ⊓ N.U i ≤ p ⁻¹ᵁ V ⊓ N.U i := fun i =>
    inf_le_inf_right _ (p.preimage_mono (X.basicOpen_le a))
  have hu : ∀ i, IsUnit (rs Y (l i) (GlobalTheory.LB.coord s i)) := fun i =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨b, hb, hyb⟩ := hV.exists_basicOpen_le (V := p ⁻¹ᵁ X.basicOpen a ⊓ N.U i) ⟨y, hy⟩ (l i hy).1
      have hi : Y.basicOpen b ≤ N.U i := hb.trans inf_le_right
      obtain ⟨n, t, ht⟩ := SecOn.exists_pow_smul_eq_restrict hN hV.isCompact hV.isQuasiSeparated b
        (Y.basicOpen_le b) rfl ((SecOn.chart hN i hi).symm 1)
      obtain ⟨r, hr⟩ := hs t
      have h₁ := congrArg (fun m => SecOn.chart hN i hi (SecOn.restrict N (Y.basicOpen_le b) m)) hr
      simp only [LinearMap.map_smulₛₗ, ← ht, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul,
        _root_.mul_one] at h₁
      have u₁ : IsUnit (rs Y (Y.basicOpen_le b) b) := Y.toRingedSpace.isUnit_res_basicOpen b
      have u₂ : IsUnit (rs Y (Y.basicOpen_le b) ((p.app V).hom a)) := by
        have hle : Y.basicOpen b ≤ Y.basicOpen ((p.app V).hom a) := by
          rw [← Scheme.preimage_basicOpen]
          exact hb.trans inf_le_left
        have := (Y.toRingedSpace.isUnit_res_basicOpen ((p.app V).hom a)).map (rs Y hle)
        exact (congrArg IsUnit (rs_rs (Y.basicOpen_le _) hle _)).mp this
      have u₃ := isUnit_of_mul_isUnit_right (h₁ ▸ u₂.mul (u₁.pow n))
      have e₁ : SecOn.chart hN i hi (SecOn.restrict N (Y.basicOpen_le b) s) =
          rs Y hb (rs Y (l i) (GlobalTheory.LB.coord s i)) := by
        rw [SecOn.chart_apply, SecOn.coord_restrict, rs_rs, rs_rs]
      rw [e₁] at u₃
      exact (congrArg IsUnit (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hb) y hyb _)).mp
        (u₃.map (Y.presheaf.germ _ y hyb).hom)
  refine ⟨X.basicOpen a, (X.mem_basicOpen a x hx).2 (IsLocalRing.notMem_maximalIdeal.1 ha),
    fun i => (hu i).unit, fun Z f z i j h hi hj => ?_⟩
  let O := p ⁻¹ᵁ X.basicOpen a ⊓ N.U i ⊓ N.U j
  have hz : f z ∈ O := ⟨⟨h, hi⟩, hj⟩
  have l₁ : O ≤ p ⁻¹ᵁ X.basicOpen a ⊓ N.U i := inf_le_left
  have l₂ : O ≤ p ⁻¹ᵁ X.basicOpen a ⊓ N.U j := inf_le_inf_right _ inf_le_left
  have l₃ : O ≤ N.U i ⊓ N.U j := inf_le_inf_right _ inf_le_right
  have : res l₁ (hu i).unit = res l₃ (N.g i j) * res l₂ (hu j).unit := Units.ext <|
    (rs_rs (l i) l₁ _).trans ((SecOn.compat s i j _ (l₂.trans (l j)) l₃).trans
      (congrArg _ (rs_rs (l j) l₂ _).symm))
  rw [← gm_res f z l₁ hz, this, map_mul, gm_res f z _ hz, gm_res f z _ hz]

theorem exists_ringEquiv_mvPolynomial {K σ : Type} [CommRing K] {f : X ⟶ Spec (CommRingCat.of K)}
    {p : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (MvPolynomial σ K))}
    (H : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K)))))
    {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ E : MvPolynomial σ Γ(X, V) ≃+* Γ(Y, p ⁻¹ᵁ V), ∀ a, E (MvPolynomial.C a) = (p.app V).hom a := by
  letI := cstAlgebra f V
  letI : Algebra (MvPolynomial σ K) (MvPolynomial σ Γ(X, V)) := MvPolynomial.algebraMvPolynomial
  have h₁ := isPushout_cst H hV (V' := p ⁻¹ᵁ V) rfl
  have h₂ := CommRingCat.isPushout_iff_isPushout.mpr
    (inferInstance : Algebra.IsPushout K (MvPolynomial σ K) Γ(X, V) (MvPolynomial σ Γ(X, V)))
  refine ⟨(IsPushout.isoIsPushout _ _ h₂ h₁).commRingCatIsoToRingEquiv, fun a => ?_⟩
  have := congrArg (fun q => q.hom a) (IsPushout.inr_isoIsPushout_hom _ _ h₂ h₁)
  rw [Scheme.Hom.app_eq_appLE]
  exact this

end GlobalTheory.PicAffineSpace

namespace GlobalTheory

open PicAffineSpace

theorem exists_lbIso_pull_affineSpace : ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left] [IsLocallyNoetherian X.left], (∀ x : X.left, UniqueFactorizationMonoid (X.left.presheaf.stalk x)) → ∀ (g : ℕ) (N : LB (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) ⊗ X).left), N.IsLB → ∃ N₀ : LB X.left, N₀.IsLB ∧ LBIso N (N₀.pull (snd _ X).left) := by
  intro K _ X _ _ hX g N hN
  let A : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))
  have H : IsPullback (snd A X).left (fst A X).left X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) :=
    (IsPullback.of_hasPullback A.hom X.hom).flip
  let z : MvPolynomial (Fin g) K →ₐ[K] K := MvPolynomial.aeval fun _ => 0
  let e : X.left ⟶ (A ⊗ X).left := H.lift (𝟙 _) (X.hom ≫ Spec.map (CommRingCat.ofHom z.toRingHom)) (by
    rw [Category.id_comp, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : z.toRingHom.comp (algebraMap K (MvPolynomial (Fin g) K)) = RingHom.id K :=
      RingHom.ext fun a => z.commutes a
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
  refine exists_lbIso_pull_of_local (snd A X).left e (H.lift_fst _ _ _) hN (fun V hV u => ?_) fun x => ?_
  · obtain ⟨E, hE⟩ := exists_ringEquiv_mvPolynomial H hV
    obtain ⟨r, hr, h⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (u.isUnit.map E.symm)
    refine ⟨hr.unit, Units.ext ?_⟩
    exact ((E.apply_symm_apply _).symm.trans (congrArg E h)).trans (hE r)
  · obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    haveI : Nonempty V := ⟨⟨x, hx⟩⟩
    haveI := isIntegrallyClosed_sections_of_stalks (Y := X.left)
      (fun y => haveI := hX y; inferInstance) hV
    obtain ⟨E, hE⟩ := exists_ringEquiv_mvPolynomial H hV
    exact exists_local_generator _ hN (isAffineOpen_preimage_of_isPullback H hV) E hE hx

end GlobalTheory
