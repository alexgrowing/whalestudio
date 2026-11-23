import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.AbDatum GlobalTheory.ConjSeq
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrobAdjoint

section Dual

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {P : LB (A ⊗ A).left}

omit [GrpObj A] in

theorem evc_comm (hP : P.IsLB) (hs : LBIso (swap P) P) (a b : Y ⟶ A) : evc hP a b = evc hP b a := by
  have h' : (swap P).IsLB := pull_isLB hP _
  rw [← evc_swap hP h', evc, evc, (cls_eq_iff h' hP).2 hs]

theorem evc_mul_right (hd : IsDual A A P) (hs : LBIso (swap P) P) (a b b' : Y ⟶ A) :
    evc hd.isLB a (b * b') = evc hd.isLB a b + evc hd.isLB a b' := by
  rw [evc_comm _ hs, (isAdditive_iff hd.isLB).1 hd.additive, evc_comm _ hs b, evc_comm _ hs b']

theorem evc_pow_right (hd : IsDual A A P) (hs : LBIso (swap P) P) (a b : Y ⟶ A) (n : ℕ) :
    evc hd.isLB a (b ^ n) = n • evc hd.isLB a b := by
  induction n with
  | zero => rw [pow_zero, evc_one_right hd.isLB hd.zero, zero_smul]
  | succ n ih => rw [pow_succ, evc_mul_right hd hs, ih, succ_nsmul]

theorem dual_ext {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (hd : IsDual A B P) {x y : T ⟶ B}
    (h : evc hd.isLB (fst A T) (snd A T ≫ x) = evc hd.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hd.isLB _
  refine (hd.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique
    ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hd.isLB _)).1 h)
  simp only [evc_ev hd.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hd.isLB).1 hd.additive _ _ _ _

end Dual

section Down

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

theorem exists_corr (H : GlobalTheory.Published.AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (h : IsGrpPullback A' A (spMap σ) φ) (y : HdR A) :
    ∃ y' : HdR A', ∀ c, y' ((grpMor_of_isGrpPullback h).pull c) = σ (y c) :=
  letI := σ.toAlgebra
  (H.2.2.1 R A g hA hg R' A' φ h).1.exists y

end Down

section Frob

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {A A₁ : Over (Sp R)} [GrpObj A] [GrpObj A₁]
  {π : A₁.left ⟶ A.left}

theorem exists_frob_versch (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) {P : LB (A ⊗ A).left}
    (hd : IsDual A A P) (hs : LBIso (swap P) P) :
    ∃ (F : A ⟶ A₁) (V : A₁ ⟶ A) (h : (A ⊗ A₁).left ⟶ (A ⊗ A).left), IsMonHom F ∧ IsMonHom V ∧
      F.left ≫ π = VB.frob A.left p (cast_left p R hR A) ∧ F ≫ V = 𝟙 A ^ p ∧
      h ≫ (fst A A).left = (fst A A₁).left ≫ VB.frob A.left p (cast_left p R hR A) ∧
      h ≫ (snd A A).left = (snd A A₁).left ≫ π ∧ LBIso (P.pull h) (ev P (fst A A₁) (snd A A₁ ≫ V)) := by
  have mF := frobMor p R hR A (cast_left p R hR A)
  have mπ := grpMor_of_isGrpPullback hπ
  let F : A ⟶ A₁ := liftPt hπ A.hom _ mF.w
  have hF : F.left ≫ π = _ := liftPt_left hπ A.hom _ mF.w
  have dF : ∀ {Y : Over (Sp R)} (t : Y ⟶ A), down mπ (t ≫ F) = down mF t := fun t ↦
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (t.left ≫ ·) hF))
  obtain ⟨h, h₁, h₂⟩ : ∃ h : (A ⊗ A₁).left ⟶ (A ⊗ A).left,
      h ≫ (fst A A).left = (fst A A₁).left ≫ VB.frob A.left p (cast_left p R hR A) ∧
      h ≫ (snd A A).left = (snd A A₁).left ≫ π :=
    ⟨pullback.lift _ _ (by
      rw [Category.assoc, Category.assoc, mF.w, mπ.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hM : (P.pull h).IsLB := pull_isLB hd.isLB _
  have eM : ∀ {Y : Over (Sp R)} (a : Y ⟶ A) (b : Y ⟶ A₁), evc hM a b = evc hd.isLB (down mF a) (down mπ b) :=
    fun a b ↦ evc_eq h₁ h₂ hd.isLB hM ((cls_eq_iff hM hM).1 rfl) a b _ _ rfl rfl
  obtain ⟨V, hV, -⟩ := hd.univ A₁ _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ by
    rw [eM, eM, eM, down_mul]
    exact (isAdditive_iff hd.isLB).1 hd.additive _ _ _ _)
  have eV : ∀ {Y : Over (Sp R)} (a : Y ⟶ A) (b : Y ⟶ A₁),
      evc hd.isLB a (b ≫ V) = evc hd.isLB (down mF a) (down mπ b) := fun a b ↦ by
    have h' : (ev P (fst A A₁) (snd A A₁ ≫ V)).IsLB := pull_isLB hd.isLB _
    have e : evc hM a b = evc h' a b := by rw [evc, evc, (cls_eq_iff hM h').2 hV]
    rw [← eM, e, evc_ev hd.isLB, lift_fst, lift_snd_assoc]
  refine ⟨F, V, h, isMonHom_of_mul _ fun T x y ↦ pt_ext hπ ?_, isMonHom_of_mul _ fun T x y ↦ dual_ext hd ?_,
    hF, dual_ext hd ?_, h₁, h₂, hV⟩
  · have e : down mπ ((x * y) ≫ F) = down mπ ((x ≫ F) * (y ≫ F)) := by rw [down_mul, dF, dF, dF, down_mul]
    exact congrArg (fun z ↦ z.left) e
  · rw [MonObj.comp_mul, evc_mul_right hd hs, ← Category.assoc, ← Category.assoc, ← Category.assoc, eV, eV, eV,
      MonObj.comp_mul, down_mul, evc_mul_right hd hs]
  · have h0 := cast_left p R hR (A ⊗ A)
    have hP' : (P.pull (VB.frob _ p h0)).IsLB := pull_isLB hd.isLB _
    rw [← Category.assoc, eV, dF, MonObj.comp_pow, evc_pow_right hd hs, Category.comp_id,
      ← evc_eq (VB.frob_naturality p _ (fst A A).left h0) (VB.frob_naturality p _ (snd A A).left h0) hd.isLB hP'
        ((cls_eq_iff hP' hP').1 rfl) (fst A A) (snd A A) _ _ rfl rfl, evc, evc, VB.cls_pull_frob p h0 hd.isLB, map_nsmul]

variable {G : PDivGroup p R} (t : G.TorsionTower A)

theorem absFrob_y (n : ℕ) : spMap ((absFrob hR G).app n).toRingHom ≫ (t.y n).left =
    (t.y n).left ≫ VB.frob A.left p (cast_left p R hR A) := by
  have h := natCast_eq_zero_of_algebra hR (G.A n)
  exact (congrArg (· ≫ (t.y n).left) (frob_sp p _ h (SS.FrobField.cast_zero_sp _ h)).symm).trans
    (VB.frob_naturality p _ (t.y n).left _)

theorem exists_tower (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) :
    ∃ t₁ : (frobTwist hR G).TorsionTower A₁, ∀ n,
      spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π :=
  letI := (frobRing hR).toAlgebra
  ⟨t.baseChange (O' := R) hπ, t.toBase_y (O' := R) hπ⟩

theorem map_eq_verschiebung (t₁ : (frobTwist hR G).TorsionTower A₁)
    (ht : ∀ n, spMap ((frobProj hR G).app n).toRingHom ≫ (t.y n).left = (t₁.y n).left ≫ π)
    (F : A ⟶ A₁) (V : A₁ ⟶ A) [IsMonHom F] [IsMonHom V]
    (hF : F.left ≫ π = VB.frob A.left p (cast_left p R hR A)) (hV : F ≫ V = 𝟙 A ^ p) :
    t₁.map t V = verschiebung hR G := by
  have e : t.map t₁ F = relFrob hR G := frobTwist_hom_ext hR fun n a ↦
    (t₁.semiOf_semiOf t t (s' := SemiHom.ofHom (t.map t₁ F)) (s'' := absFrob hR G) (ψ := F.left) ht
      (fun n ↦ congrArg Over.Hom.left (t.map_y t₁ F n)) (fun n ↦ by rw [hF]; exact absFrob_y hR t n) n a).symm.trans
      ((absFrob_app hR G n a).trans (relFrob_app_frobProj hR n a).symm)
  have : IsMonHom (𝟙 A ^ p) := hV ▸ inferInstance
  refine eq_verschiebung_of_relFrob_comp hR ?_
  rw [← e, ← t.map_comp, t.map_congr t hV, t.map_pow_id]

end Frob

section Pairing

open GlobalTheory.CatCoh GlobalTheory.AbLaw

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A B : Over S} [GrpObj A] [GrpObj B]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' B' : Over S'} [GrpObj A'] [GrpObj B']

theorem isCorrForm_pull_tensorForm {P : LB (A ⊗ B).left} (hP : P.IsLB) {N : ℕ} {a : Fin N → prim κ t A}
    {c : Fin N → prim κ t B} (hc : IsChern κ ((A ⊗ B).hom ≫ t) P
      (∑ k, cup _ (pullOver κ t (fst A B) (a k).1) (pullOver κ t (snd A B) (c k).1)))
    {σ : R →+* R'} {b : S' ⟶ S} {f : A'.left ⟶ A.left}
    {g : B'.left ⟶ B.left} (m : GrpMor κ t A κ' t' A' σ b f) (n : GrpMor κ t B κ' t' B' σ b g)
    {h : (A' ⊗ B').left ⟶ (A ⊗ B).left} (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f)
    (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsCorrForm κ' t' A' B' (P.pull h) (tensorForm κ' t' A' B' (fun i ↦ m.pull (a i)) fun i ↦ n.pull (c i)) := by
  have k := grpMor_prod m n h₁ h₂
  refine ⟨N, _, _, ?_, tensorForm_apply _ _ _ _ _ _⟩
  have := isChern_pull k.isMor hc
  rw [map_sum] at this
  convert this using 2 with i
  rw [IsMor.pullCohomologyTwo_cup]
  congr 1
  · congr 1
    exact (IsMor.pullback1_comp _ _ (m.comp (homMor κ' t' (fst A' B'))).isMor (fun _ ↦ rfl) rfl _).trans
      (IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) h₁ _).symm
  · exact (IsMor.pullback1_comp _ _ (n.comp (homMor κ' t' (snd A' B'))).isMor (fun _ ↦ rfl) rfl _).trans
      (IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) h₂ _).symm

theorem exists_eq_sum {K : Type} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M] {N : ℕ}
    (a c : Fin N → M) (β : M → Module.Dual K M) (hβ : ∀ s (y : Module.Dual K M), ∑ k, β s (a k) * y (c k) = y s)
    (z : M) : ∃ y : Module.Dual K M, ∑ k, y (c k) • a k = z := by
  let T : Module.Dual K M →ₗ[K] M := ∑ k, (Module.Dual.eval K M (c k)).smulRight (a k)
  have hT : ∀ y, T y = ∑ k, y (c k) • a k := fun y ↦ by simp [T, LinearMap.sum_apply]
  have inj : Function.Injective T := (injective_iff_map_eq_zero _).2 fun y hy ↦ LinearMap.ext fun s ↦ by
    have e := congrArg (β s) ((hT y).symm.trans hy)
    rw [map_sum, map_zero] at e
    rw [← hβ, LinearMap.zero_apply, ← e]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq).1 inj z
  exact ⟨y, (hT y).symm.trans hy⟩

end Pairing

theorem frob_adjoint_verschiebung : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (hK : (p : K) = 0) (A : Over (Sp K)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A), SmoothOfRelativeDimension g A.hom → ∀ P : LB (A ⊗ A).left, IsDual A A P → LBIso (swap P) P → ∀ (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (β : primDR A →ₗ[K] HdR A), IsCorrForm (dp0 K) (𝟙 _) A A P ψ → (∀ s y, ψ (β s) y = y s) → ∀ (e : GlobalTheory.Published.DeRhamVectorExtension.Family p), e.Natural → ∀ (hn : IsNilpotent (p : K)) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A), (∀ z, e hn hA t (frobDR p K hK A z) = (absFrob hK 𝒜).rig (e hn hA t z)) ∧ ∀ (s z : primDR A) (n : ℕ) (r : Fin n → K) (w : Fin n → primDR A), rigExtMap (verschiebung hK 𝒜) (e hn hA t s) = ∑ i, r i • (frobProj hK 𝒜).rig (e hn hA t (w i)) → β s (frobDR p K hK A z) = ∑ i, r i * (β (w i) z) ^ p := by
  intro H _ p _ K _ hK A _ g hA hg P hd hs ψ β hψ hβ e he hn 𝒜 t
  refine ⟨fun z ↦ ?_, fun s z n r w hw ↦ ?_⟩
  · rw [(t.eq_semiOf_iff t (frobMor p K hK A (cast_left p K hK A)) (absFrob hK 𝒜)).2 (absFrob_y hK t)]
    exact he hn hn hA hA t t _ z
  let A₁ := (Over.pullback (spMap (frobR p K hK))).obj A
  have hπ : IsGrpPullback A₁ A _ _ := isGrpPullback_pullback A (spMap (frobR p K hK))
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj _ A hA
  have hg₁ : SmoothOfRelativeDimension g A₁.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hπ.1 hg
  obtain ⟨F, V, h, _, _, hF, hV, h₁, h₂, hh⟩ := exists_frob_versch hK hπ hd hs
  obtain ⟨t₁, ht⟩ := exists_tower hK t hπ
  have mF := frobMor p K hK A (cast_left p K hK A)
  have mπ := grpMor_of_isGrpPullback hπ
  have hw' : primPull (dp0 K) (𝟙 _) V s = ∑ i, r i • mπ.pull (w i) := (e hn hA₁ t₁).injective (by
    rw [he.primPull hn hA₁ hA t₁ t, map_eq_verschiebung hK t t₁ ht F V hF hV, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, he hn hn hA hA₁ t t₁ mπ, (t₁.eq_semiOf_iff t mπ (frobProj hK 𝒜)).2 ht])
  have C := cupSquare_of_free H.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A₁ hA hA₁) (smooth_prod hg hg₁)
  have hM : (P.pull h).IsLB := LB.isLB_pull hd.isLB _
  have hM' : (ev P (fst A A₁) (snd A A₁ ≫ V)).IsLB := LB.isLB_pull hd.isLB _
  obtain ⟨χ, hχ, k⟩ := hψ.pull hd.isLB (homMor (dp0 K) (𝟙 _) (𝟙 A)) (homMor (dp0 K) (𝟙 _) V)
    (h := (lift (fst A A₁) (snd A A₁ ≫ V)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id]) (by simp only [← Over.comp_left, lift_snd]) hM
    ((CechPic.cls_eq_iff hM' hM).1 ((CechPic.cls_eq_iff hM hM').2 hh).symm)
  obtain ⟨N, a, c, hc, hφ⟩ := hψ
  obtain rfl := (isCorrForm_pull_tensorForm hd.isLB hc mF mπ h₁ h₂).unique C hM hχ
  have := (GlobalTheory.Published.AbelianDeRham.Free.prim H.1 hA hg).1
  obtain ⟨y, rfl⟩ := exists_eq_sum a c β (fun s y ↦ (hφ _ _).symm.trans (hβ s y)) z
  obtain ⟨y₁, hy⟩ := exists_corr H hA hg hπ y
  have k₁ := k (push _ _ (𝟙 A) (β s)) (β s) (push _ _ V y₁) y₁ (fun _ ↦ rfl) fun _ ↦ rfl
  rw [push_id, LinearMap.id_apply, hβ, RingHom.id_apply, push_apply, hw', tensorForm_apply, map_sum] at k₁
  have hz : ∀ x : HdR A, x (∑ k, y (c k) • a k) = ψ x y := fun x ↦ by
    rw [hφ, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
  simp only [hz, hβ]
  rw [map_sum, map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun k _ ↦ ?_) (k₁.trans (Finset.sum_congr rfl fun i _ ↦ ?_))
  · rw [map_smulₛₗ, map_smul, smul_eq_mul, mul_comm, hy]
    rfl
  · rw [map_smul, smul_eq_mul, hy, frobR_apply]

end GlobalTheory.FrobAdjoint
