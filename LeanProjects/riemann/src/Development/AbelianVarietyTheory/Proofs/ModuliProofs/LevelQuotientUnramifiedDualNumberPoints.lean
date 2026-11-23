import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelQuotUnram

open GlobalTheory.TangentCrit (dualPt dualBase dualPt_dualBase dualPt_dualBase_assoc)

lemma subsingleton_sp_dual (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ a : PrimeSpectrum (DualNumber k), a.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom := by
    intro a
    ext d
    constructor
    · intro hd
      by_contra h
      exact a.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hd
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.mk0 _ h)))
    · intro hd
      have h : d.fst = 0 := hd
      refine a.isPrime.mem_of_pow_mem 2 ?_
      have : d ^ 2 = 0 := by ext1 <;> simp [pow_two, h]
      rw [this]; exact a.asIdeal.zero_mem
  exact PrimeSpectrum.ext ((key a).trans (key b).symm)

lemma dualMap_cancel {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}}
    {g g' : Sp (DualNumber k) ⟶ X} (h : spMap (Chart.dualMapR f) ≫ g = spMap (Chart.dualMapR f) ≫ g') : g = g' := by
  have := subsingleton_sp_dual k
  refine TangentCrit.hom_ext_of_ker_inf (CommRingCat.ofHom (Chart.dualMapR f)) (CommRingCat.ofHom (Chart.dualMapR f))
    (fun z => ⟨IsLocalRing.closedPoint (DualNumber K), Subsingleton.elim _ _⟩) (fun d hd _ => ?_) h h
  have h₁ : f d.fst = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.fst hd
  have h₂ : f d.snd = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.snd hd
  exact TrivSqZeroExt.ext (f.injective (by simpa using h₁)) (f.injective (by simpa using h₂))

lemma constPt_dualMap {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) :
    constPt (spMap (Chart.dualMapR f) ≫ x) = spMap (Chart.dualMapR f) ≫ constPt x := by
  simp only [constPt, ← Category.assoc]
  congr 1
  simp only [← Spec.map_comp]
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

lemma exists_dual_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [Smooth π] [IsAffineHom π] {k : Type} [Field k]
    (x : Sp (DualNumber k) ⟶ Y) (y : Sp k ⟶ X) (h : y ≫ π = dualPt k ≫ x) :
    ∃ x₂ : Sp (DualNumber k) ⟶ X, dualPt k ≫ x₂ = y ∧ x₂ ≫ π = x := by
  have := subsingleton_sp_dual k
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint (DualNumber k)))) isOpen_univ
  have hx : Set.range x ⊆ U := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint (DualNumber k))]
  refine exists_lift_of_smooth_of_isAffineOpen π hU (hU.preimage π) le_rfl _ x y h hx ?_ ?_
  · rintro _ ⟨z, rfl⟩
    change π (y z) ∈ U
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact hx ⟨_, rfl⟩
  · intro R A _ _ _ _ _ _ ρ hρ φ
    refine SmoothNilLift.exists_lift_of_nil ρ (fun c => ⟨TrivSqZeroExt.inl c, hρ _⟩) (fun d hd => ?_) φ
    have h : TrivSqZeroExt.fst d = 0 := (hρ d).symm.trans hd
    exact ⟨2, by ext1 <;> simp [pow_two, h]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

lemma sab_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

lemma torsion_rigid {X : Scheme.{0}} {k : Type} [Field k] (t : SAB H (Sp (DualNumber k))) (t₂ : SAB H X)
    (y : Sp k ⟶ X) (ν : SABMap t t₂ (dualBase k ≫ y)) {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤)))
    (σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ t.G) (τ : 𝟙_ (Over X) ⟶ t₂.G) (hσ : σ ^ n = 1) (hτ : τ ^ n = 1)
    (h : dualPt k ≫ σ.left ≫ ν.φ = y ≫ τ.left) : σ.left ≫ ν.φ = (dualBase k ≫ y) ≫ τ.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback ν.cart (𝟙 _) (dualBase k ≫ y) (Category.id_comp _).symm
  have h₁ : (e σ).left = σ.left ≫ ν.φ := he σ
  have h₂ : (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ).left = (dualBase k ≫ y) ≫ τ.left := by simp
  rw [← h₁, ← h₂]
  congr 1
  refine GrpTangent.eq_of_tangentMap_injective y (mulN t₂.G n)
    (GrpTangent.tangentMap_pullback_mulN_bijective t₂.G hn y).1 _ _ (Over.OverMorphism.ext ?_) ?_
  · change dualPt k ≫ Over.Hom.left (e σ) = dualPt k ≫ Over.Hom.left (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ)
    rw [h₁, h₂, h, Category.assoc, dualPt_dualBase_assoc]
  · rw [GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← comp_pow, hτ, comp_one, ← map_pow]
    exact (congrArg e hσ).trans (map_one e)

variable {D : Datum H}

section
variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)

lemma pow_eq_of_add {L Γ : Type} [AddCommGroup L] [Group Γ] (f : L → Γ) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (a := f 0) (by rw [← this, _root_.mul_one])).symm
  | succ n ih => rw [pow_succ, ih, add_smul, one_smul, hf]

lemma natCast_mem_Mb (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

lemma nsmul_mem_Mb (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (natCast_mem_Mb l) Submodule.mem_top

lemma eta_pow (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [pow_eq_of_add o.eta o.eta_add, o.eta_ker _ (nsmul_mem_Mb l a)]

lemma etaA_pow (a : D.La) : o.etaA a ^ l.A = 1 := by
  rw [pow_eq_of_add o.etaA o.etaA_add, o.etaA_ker]

include b s in
lemma isUnit_nat {n : ℕ} (hn : 0 < n) : IsUnit (n : Γ(S, ⊤)) := by
  simpa using (b.unit n hn).map ((Scheme.ΓSpecIso (.of B)).inv ≫ s.appTop).hom

end

theorem unram_of_isAlgClosed (hL : Out.Laws) {l l₂ : Level H} (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s))
    (m₁ : ObjMap ob Q.univ x) (m₂ : ObjMap ob Q.univ (constPt x)) : x = constPt x := by
  have := Q.fin
  have := Q.etale
  have := Q.onto
  obtain ⟨y, hy⟩ := GeomSurj.exists_lift_of_surjective Q.π (dualPt k ≫ x)
  obtain ⟨x₂, hx₂, hx⟩ := exists_dual_lift Q.π x y hy.symm
  have hc : constPt x₂ = dualBase k ≫ y := by rw [← hx₂]; rfl
  have hcπ : (dualBase k ≫ y) ≫ Q.π = constPt x := by rw [Category.assoc, ← hy]; rfl

  obtain ⟨o₀, ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    (dualPt k ≫ x ≫ Q.s) (dualPt k) rfl rfl (by simp [spMap]) ob
  have hr : r.toSABMap.φ ≫ m₁.toSABMap.φ = r.toSABMap.φ ≫ m₂.toSABMap.φ := by
    obtain ⟨n₁, hn₁⟩ := ObjMaps.exists_sab_comp m₁.toSABMap r.toSABMap
    obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp m₂.toSABMap r.toSABMap
    have e : dualPt k ≫ constPt x = dualPt k ≫ x := dualPt_dualBase_assoc k _
    obtain ⟨n₃, hn₃⟩ := sab_cast n₂ e
    rw [← hn₁, ← hn₂, ← hn₃]
    refine obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ Q.univ o₀ _ (Or.inl inferInstance) n₁ n₃
      fun a => ⟨_, rfl, ?_⟩
    rw [hn₃, hn₂, hn₁, reassoc_of% (r.eta a), reassoc_of% (r.eta a), m₁.eta, m₂.eta, reassoc_of% e]
  have hr' : ∀ {Z : Scheme.{0}} (z : Z ⟶ ob.t.G.left) (w : Z ⟶ Sp k), z ≫ ob.t.G.hom = w ≫ dualPt k →
      z ≫ m₁.toSABMap.φ = z ≫ m₂.toSABMap.φ := by
    intro Z z w hz
    rw [← r.cart.1.lift_fst z w hz, Category.assoc, Category.assoc]
    exact congrArg _ hr

  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l₂ _ _ (baseKA l₂) (baseKA l₂) (RingHom.id _) _ _ Xo₂.s
    (x₂ ≫ Xo₂.s) x₂ rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨a₁, ha₁⟩ := ObjMaps.exists_sab_comp Q.m n₁.toSABMap
  obtain ⟨a₂, ha₂⟩ := sab_cast a₁ (hx.trans (Category.id_comp x).symm)
  obtain ⟨u, hu⟩ := ObjMaps.exists_sab_cancel m₁.toSABMap a₂
  obtain ⟨a₃, ha₃⟩ := ObjMaps.exists_sab_comp m₂.toSABMap u
  obtain ⟨a₄, ha₄⟩ := sab_cast a₃ ((Category.id_comp _).trans hcπ.symm)
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_cancel Q.m a₄
  have e₁ : n₁.toSABMap.φ ≫ Q.m.φ = u.φ ≫ m₁.toSABMap.φ := by rw [← ha₁, ← ha₂, hu]
  have e₂ : n₂.φ ≫ Q.m.φ = u.φ ≫ m₂.toSABMap.φ := by rw [← hn₂, ha₄, ha₃]
  have key : ∀ σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o₁.t.G,
      dualPt k ≫ σ.left ≫ n₂.φ = dualPt k ≫ σ.left ≫ n₁.toSABMap.φ := by
    intro σ
    have hσ : σ.left ≫ o₁.t.G.hom = 𝟙 _ := Over.w σ
    refine Q.m.cart.1.hom_ext ?_ ?_
    · have := hr' (dualPt k ≫ σ.left ≫ u.φ) (𝟙 _) (by
        have w := u.cart.1.w
        simp only [Category.assoc, Category.id_comp, Category.comp_id] at w ⊢
        rw [w, hσ]
        exact Category.comp_id _)
      simp only [Category.assoc] at this ⊢
      rw [e₁, e₂, this]
    · have w₁ := n₁.cart.1.w
      have w₂ := n₂.cart.1.w
      simp only [Category.assoc]
      rw [w₁, w₂, reassoc_of% hσ, reassoc_of% hσ, dualPt_dualBase_assoc, hx₂]
  obtain ⟨n₃, hn₃⟩ := sab_cast n₂ hc.symm
  have h₂ : x₂ = constPt x₂ := by
    refine Xo₂.unram k x₂ o₁ ⟨n₁⟩ ⟨{ toSABMap := n₃, eta := fun a => ?_, etaA := fun a => ?_ }⟩
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) (by have := l₂.three_le; omega))
        _ _ (eta_pow o₁ a) (eta_pow Xo₂.univ a) ?_
      rw [key, n₁.eta, reassoc_of% hx₂]
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) l₂.A_pos)
        _ _ (etaA_pow o₁ a) (etaA_pow Xo₂.univ a) ?_
      rw [key, n₁.etaA, reassoc_of% hx₂]
  rw [← hcπ, ← hc, ← h₂, hx]

end GlobalTheory.LevelQuotUnram

namespace GlobalTheory

theorem levelQuot_unram : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s)), Nonempty (ObjMap ob Q.univ x) → Nonempty (ObjMap ob Q.univ (constPt x)) → x = constPt x := by
  rintro hL - E _ _ _ H D l l₂ Xo₂ Q - - k _ x ob ⟨m₁⟩ ⟨m₂⟩
  let f : k →+* AlgebraicClosure k := algebraMap _ _
  refine LevelQuotUnram.dualMap_cancel f ?_
  rw [← LevelQuotUnram.constPt_dualMap]
  obtain ⟨o', ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    ((spMap (Chart.dualMapR f) ≫ x) ≫ Q.s) (spMap (Chart.dualMapR f)) rfl rfl (by simp [spMap]) ob
  obtain ⟨n₁, -⟩ := ObjComp.objMap_comp m₁ r
  obtain ⟨n₂, -⟩ := ObjComp.objMap_comp m₂ r
  exact LevelQuotUnram.unram_of_isAlgClosed hL Xo₂ Q _ _ o' n₁ (LevelQuotUnram.constPt_dualMap f x ▸ n₂)

end GlobalTheory
