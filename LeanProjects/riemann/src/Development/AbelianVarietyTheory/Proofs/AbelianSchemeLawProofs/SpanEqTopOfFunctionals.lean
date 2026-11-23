import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VVRank

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj

section General

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_le_of_eq {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k)
    (j : K → L.ι) : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

def pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) : LB.Sec (LB.LinComb L φ' ε) where
  f j := (Y'.presheaf.map (homOfLE (wchart_le_of_eq h e j)).op).hom ((h.app _).hom (s.f j))
  compat := by
    obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
    exact (H1.SectionArithmetic.pullSec s h).compat

theorem sval_pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullTo s h e) r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact H1.SectionArithmetic.sval_pullSec s h r z hJ

theorem exists_gen_pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J),
      Good L z J → val t' r z J = val t (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨LB.pullGen L φ ε t h, LB.isGen_pullGen L φ ε t ht h, fun Z r z J hJ => val_pull hJ t h r⟩

end General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}

omit [GrpObj A] in
theorem whisker_snd_left {T T' : Over S} (h : T' ⟶ T) :
    (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by
  rw [← Over.comp_left, whiskerRight_snd]

def pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') :=
  pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (h ▷ A).left
    (fun _ => whisker_snd_left A h)

theorem isPullSec_pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    IsPullSec A L a (h ▷ A) (whiskerRight_snd h A) s (pullS A a h s) := fun _ => rfl

abbrev sv {a : ℤ} {T : Over S} (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : Z.presheaf.stalk z :=
  sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J

theorem sv_pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sv A (pullS A a h s) r z J = sv A s (r ≫ (h ▷ A).left) z J :=
  sval_pullTo _ _ _ r z hJ

theorem ofSec_ext (hL : L.IsLB) {a : ℤ} {T : Over S} {s s' : LB.Sec (LPow A L a T)}
    (h : ∀ y J, Good L y J → sv A s (𝟙 _) y J = sv A s' (𝟙 _) y J) :
    (SecM.ofSec A s : SecM A L a T) = SecM.ofSec A s' :=
  Subtype.ext (funext (sec_ext_val hL h))

def pullM (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⟶ T) :
    SecM A L a T →ₛₗ[h.left.appTop.hom] SecM A L a T' where
  toFun f := SecM.ofSec A (pullS A a h (SecM.toSec A f))
  map_add' f g := Subtype.ext (funext fun j => map_add ((h ▷ A).left.appLE _ _
    (chart_le_res A L (h ▷ A) (whiskerRight_snd h A) a j)).hom (f.1 j) (g.1 j))
  map_smul' c f := Subtype.ext (funext fun j => by
    refine (map_mul ((h ▷ A).left.appLE _ _
      (chart_le_res A L (h ▷ A) (whiskerRight_snd h A) a j)).hom (liftHom A _ c) (f.1 j)).trans ?_
    refine congrArg (· * _) (fn_ext fun y hy => ?_)
    have hy' := chart_le_res A L (h ▷ A) (whiskerRight_snd h A) a j hy
    have e : (h ▷ A).left ≫ (fst T A).left = (fst T' A).left ≫ h.left := by
      rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    refine (gs_res _ y _ hy _).trans ((gs_pull _ _ y _ hy' _).trans ((gs_res _ y le_top hy' _).trans
      ((gs_pull _ _ y ⊤ trivial _).trans (Eq.trans ?_ ((gs_res _ y le_top hy _).trans
        ((gs_pull _ _ y ⊤ trivial _).trans (gs_pull _ h.left y ⊤ trivial _))).symm))))
    rw [Category.assoc, e, Category.assoc])

theorem pullM_ofSec (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    pullM A L a h (SecM.ofSec A s) = SecM.ofSec A (pullS A a h s) := rfl

theorem pullM_comp (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T)
    (f : SecM A L a T) : pullM A L a h' (pullM A L a h f) = pullM A L a (h' ≫ h) f :=
  ofSec_ext A hL fun y J hJ => by
    refine (sv_pullS A a h' _ _ y hJ).trans ((sv_pullS A a h _ _ y hJ).trans
      (Eq.trans ?_ (sv_pullS A a (h' ≫ h) _ _ y hJ).symm))
    rw [comp_whiskerRight, Over.comp_left, Category.assoc]

theorem pullM_id (hL : L.IsLB) (a : ℤ) {T : Over S} (f : SecM A L a T) : pullM A L a (𝟙 T) f = f :=
  ofSec_ext A hL (s' := SecM.toSec A f) fun y J hJ => by
    refine (sv_pullS A a _ _ _ y hJ).trans ?_
    rw [id_whiskerRight, Over.id_left, Category.comp_id]

section Twist

variable {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem sv_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sv A s' r z J = (val α r z J).val * sv A s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

theorem isTwistPull_of_sv (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sv A s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sv A s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm

theorem exists_isTwistPull (hL : L.IsLB) (hα : α.IsGen) (s : LB.Sec (LPow A L b T)) :
    ∃ s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => a)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        e, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left α hα)
  exact ⟨s', isTwistPull_of_sv A hL hα fun y J hJ =>
    (hs' _ _ y J hJ).trans ((sval_pullMulSec _ _ α hα _ y hJ).trans (mul_comm _ _))⟩

theorem exists_twist_pull (hL : L.IsLB) (hα : α.IsGen) {T' : Over S} (h : T' ⟶ T)
    {ψ' : T' ⊗ A ⟶ T' ⊗ A} {m' : T' ⊗ A ⟶ A} (hm' : ψ' ≫ snd T' A = m')
    (e : ψ' ≫ h ▷ A = h ▷ A ≫ ψ) :
    ∃ α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b]), α'.IsGen ∧
      ∀ s s', IsTwistPull A L ψ m hm a b α s s' →
        IsTwistPull A L ψ' m' hm' a b α' (pullS A b h s) (pullS A a h s') := by
  obtain ⟨α', h₁, h₂⟩ := exists_gen_pullTo (φ' := ![(snd T' A).left, m'.left]) α hα (h ▷ A).left
    (fun k => by
      fin_cases k
      · exact whisker_snd_left A h
      · change (h ▷ A).left ≫ m.left = m'.left
        rw [← Over.comp_left, ← hm, ← hm', ← Category.assoc, ← e, Category.assoc, whiskerRight_snd])
  refine ⟨α', h₁, fun s s' H => isTwistPull_of_sv A hL h₁ fun y J hJ => ?_⟩
  rw [sv_pullS A a h s' _ y hJ, sv_pullS A b h s _ y hJ, h₂ _ _ y J hJ, sv_of_isTwistPull A H _ y hJ,
    Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, e]

end Twist

theorem exists_theta_pull (hL : L.IsLB) {k : ℤ} {T T' : Over S} (h : T' ⟶ T) (θ : ThetaGrp A L k T) :
    ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧
      ∀ s s', IsActOf A L k θ s s' → IsActOf A L k θ' (pullS A k h s) (pullS A k h s') := by
  obtain ⟨α', h₁, h₂⟩ := exists_twist_pull A (ψ := translT A θ.pt) (hm := lift_snd _ _) hL θ.isGen h
    (ψ' := translT A (h ≫ θ.pt)) (m' := translPt A (h ≫ θ.pt)) (lift_snd _ _) (by
      ext1
      · simp [translT]
      · simp [translT, translPt, comp_lift_assoc])
  exact ⟨⟨h ≫ θ.pt, α', h₁⟩, rfl, h₂⟩

theorem mulT_comm {T T' : Over S} (h : T' ⟶ T) (n : ℕ) :
    mulT A T' n ≫ h ▷ A = h ▷ A ≫ mulT A T n := by
  ext1
  · simp [mulT]
  · simp [mulT, MonObj.comp_pow]

theorem isVVGen_pull (P : PolAV S) (N n : ℕ) {T T' : Over S} (h : T' ⟶ T)
    {t : LB.Sec (LPow P.A P.L N T)} (ht : IsVVGen P N n t) : IsVVGen P N n (pullS P.A N h t) := by
  obtain ⟨th, s1, α, U, hα, h₁, h₂⟩ := ht
  obtain ⟨α', k₁, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    P.isLB hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨U', -, k₃⟩ := exists_theta_pull P.A P.isLB h U
  exact ⟨_, _, α', U', k₁, k₂ _ _ h₁, k₃ _ _ h₂⟩

theorem inVV_of_isVVGen (P : PolAV S) (N n : ℕ) {T : Over S}
    {t : LB.Sec (LPow P.A P.L N T)} (ht : IsVVGen P N n t) : InVV P N n t := fun _ =>
  ⟨⊤, trivial, _, isPullSec_pullS P.A N (overResι ⊤) t, 1, fun _ => 1, fun _ => pullS P.A N (overResι ⊤) t,
    fun _ => isVVGen_pull P N n _ ht, fun j => by simp [liftFun]⟩

theorem span_eq_top_of_functionals {R M I κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [Finite κ]
    (b : Module.Basis κ R M) (t : I → M)
    (H : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → ∀ l : M →ₗ[R] R, (∀ c, l (t c) ∈ 𝔪) → ∀ x, l x ∈ 𝔪) :
    Submodule.span R (Set.range t) = ⊤ := by
  have : Module.Finite R M := Module.Finite.of_basis b
  have : Module.Free R M := Module.Free.of_basis b
  rcases eq_top_or_exists_le_coatom (Submodule.span R (Set.range t)) with h | ⟨Q, hQ, hle⟩
  · exact h
  exfalso
  obtain ⟨𝔪, h𝔪, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := M ⧸ Q)).1
    ((isSimpleModule_iff_isCoatom).2 hQ)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property 𝔪.mkQ (e.toLinearMap ∘ₗ Q.mkQ)
    (Submodule.mkQ_surjective _)
  have key : ∀ x, l x ∈ 𝔪 ↔ x ∈ Q := fun x => by
    have := LinearMap.congr_fun hl x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at this
    rw [← Submodule.Quotient.mk_eq_zero, this, e.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  exact hQ.1 (eq_top_iff.2 fun x _ => (key x).1 (H 𝔪 h𝔪 l
    (fun c => (key _).2 (hle (Submodule.subset_span ⟨c, rfl⟩))) x))

theorem functional_mem_of_span {R R' M M' I κ : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] [Finite κ] (σ : R →+* R') (φ : M →ₛₗ[σ] M')
    (b : Module.Basis κ R M) (b' : Module.Basis κ R' M') (hb : ∀ i, b' i = φ (b i)) (t : I → M)
    (ht : Submodule.span R' (Set.range fun c => φ (t c)) = ⊤) (l : M →ₗ[R] R)
    (hl : ∀ c, σ (l (t c)) = 0) (x : M) : σ (l x) = 0 := by
  let l' : M' →ₗ[R'] R' := b'.constr R' fun i => σ (l (b i))
  have key : ∀ x, l' (φ x) = σ (l x) := fun x => by
    have := Fintype.ofFinite κ
    rw [← b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, ← hb, l', Module.Basis.constr_basis, smul_eq_mul,
      RingHom.id_apply, map_mul]
  have h0 : l' = 0 := LinearMap.ext_on_range ht fun c => (key _).trans (hl c)
  rw [← key, h0, LinearMap.zero_apply]

theorem exists_basis (P : PolAV S) (n : ℕ) {V : S.Opens} {κ : Type} [Fintype κ]
    (b : κ → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) V)))
    (hb : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
        (b' : κ → LB.Sec (LPow P.A P.L n (baseAt t))),
        (∀ i, IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) (b' i)) →
        LinearIndependent Γ((baseAt t).left, ⊤)
            (fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) ∧
          Submodule.span Γ((baseAt t).left, ⊤)
            (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) = ⊤)
    (T : Over S) [IsAffine T.left] (h : T ⟶ overRes (T := baseOver S) V) :
    ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T),
      ∀ i, c i = pullM P.A P.L n h (SecM.ofSec P.A (b i)) := by
  let t : Spec (CommRingCat.of Γ(T.left, ⊤)) ⟶ (overRes (T := baseOver S) V).left :=
    T.left.isoSpec.inv ≫ h.left
  let u : baseAt t ⟶ T := Over.homMk T.left.isoSpec.inv (by
    change T.left.isoSpec.inv ≫ T.hom = (T.left.isoSpec.inv ≫ h.left) ≫ _
    rw [Category.assoc, Over.w h])
  have hu : u ≫ h = homAt t := Over.OverMorphism.ext rfl
  have : IsIso u.left := inferInstanceAs (IsIso T.left.isoSpec.inv)
  have : IsIso ((Over.forget S).map u) := this
  have : IsIso u := isIso_of_reflects_iso u (Over.forget S)
  have hσ : Function.Bijective u.left.appTop.hom :=
    ConcreteCategory.bijective_of_isIso (u.left.app ⊤)
  have hφ : Function.Injective (pullM P.A P.L n u) := Function.LeftInverse.injective
    (g := pullM P.A P.L n (inv u)) fun f => by
      rw [pullM_comp P.A P.isLB, IsIso.inv_hom_id, pullM_id P.A P.isLB]
  obtain ⟨h₁, h₂⟩ := hb _ t (fun i => pullS P.A n (homAt t) (b i))
    (fun i => isPullSec_pullS P.A n (homAt t) (b i))
  have e : ∀ i, pullM P.A P.L n u (pullM P.A P.L n h (SecM.ofSec P.A (b i))) =
      SecM.ofSec P.A (pullS P.A n (homAt t) (b i)) := fun i => by
    rw [pullM_comp P.A P.isLB, hu, pullM_ofSec]
  refine ⟨Module.Basis.mk (v := fun i => pullM P.A P.L n h (SecM.ofSec P.A (b i))) ?_ ?_,
    fun i => Module.Basis.mk_apply _ _ _⟩
  · rw [Fintype.linearIndependent_iff] at h₁ ⊢
    intro g hg i
    have := congrArg (pullM P.A P.L n u) hg
    simp only [map_sum, LinearMap.map_smulₛₗ, map_zero, e] at this
    exact hσ.1 ((h₁ _ this i).trans (map_zero _).symm)
  · intro x _
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (h₂.ge (Submodule.mem_top (x := pullM P.A P.L n u x)))
    choose g' hg' using fun i => hσ.2 (g i)
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨g', hφ ?_⟩
    simp only [map_sum, LinearMap.map_smulₛₗ, e, hg', hg]

theorem surjective_mulA (P : PolAV S) (n : ℕ) (hn : n ≠ 0)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![((n ^ 2 : ℕ) : ℤ), -1]))
    (hα : α.IsGen) : Surjective (mulA P.A n).left := by
  have := P.isAb.proper
  have := P.isAb.comm
  have hf := MulFinite.isFinite_of_relAmple P.A P.L P.isLB P.ample _ (n ^ 2) (by positivity) α hα
  have hm := AbLaw.MulN.isMonHom_mulA P.A n
  exact AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t =>
    (flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (AbLaw.MulN.isPullback_baseChange t _) hf)).2

theorem surjective_mulT (n : ℕ) (h : Surjective (mulA A n).left) (T : Over S) :
    Surjective (mulT A T n).left := by
  have e₁ : (mulT A T n).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, mulT, lift_fst]
  have e₂ : (snd T A).left ≫ (mulA A n).left = (mulT A T n).left ≫ (snd T A).left := by
    rw [← Over.comp_left, ← Over.comp_left, mulT, lift_snd, MonObj.comp_pow, Category.comp_id]
  have hp : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
    (IsPullback.of_hasPullback T.hom A.hom).flip
  have : IsPullback (snd T A).left (mulT A T n).left (mulA A n).left (snd T A).left := by
    refine IsPullback.of_bot ?_ e₂ hp
    rw [e₁, Over.w]
    exact hp
  exact MorphismProperty.of_isPullback (P := @Surjective) this h

theorem ofSec_eq_zero_of_twist (hL : L.IsLB) {T : Over S} [IsReduced (T ⊗ A).left]
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (hψ : Surjective ψ.left) {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') (h0 : (SecM.ofSec A s' : SecM A L a T) = 0) :
    (SecM.ofSec A s : SecM A L b T) = 0 := by
  refine Subtype.ext (funext fun j => eq_zero_of_basicOpen_eq_bot (s.f j) (eq_bot_iff.2 fun y hy => ?_))
  exfalso
  obtain ⟨z, rfl⟩ := ψ.left.surjective y
  have hz : ψ.left z ∈ (LPow A L b T).U j := (T ⊗ A).left.basicOpen_le _ hy
  have hu := (MulFinite.isUnit_gs ψ.left z _ hz _).2 hy
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ z)
  have e := sv_of_isTwistPull A H (𝟙 _) z hJ
  have e0 : sv A s' (𝟙 _) z J = 0 := by
    have : ∀ j, s'.f j = 0 := fun j => congrFun (congrArg Subtype.val h0) j
    refine (congrArg (gs _ z _) (this _)).trans ((gs_eq _ z _ (Good.mem hJ _ _) _).trans ?_)
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  rw [e0, Category.id_comp, eq_comm, Units.mul_right_eq_zero] at e
  have e' := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left z hz
    (Good.mem hJ _ _)
  exact hu.ne_zero (e'.trans ((congrArg _ e).trans (mul_zero _)))

omit [GrpObj A] in
theorem comp_linComb {A : Over S} [GrpObj A] {T T' : Over S} (h : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : h ≫ linComb y a = linComb (fun i => h ≫ y i) a := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (h ≫ ·) fun x y => MonObj.comp_mul h x y
  refine (map_list_prod F _).trans (congrArg List.prod ?_)
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext fun i => map_pow F _ _)

omit [GrpObj A] in
theorem linComb_pow {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) (N : ℕ) (hy : ∀ i, y i ^ N = 1) : linComb y a ^ N = 1 := by
  rw [linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, _root_.mul_comm, pow_mul, hy, one_pow]

theorem span_translates_eq_top {k : ℤ} {T : Over S} {I : Type} [Nonempty I]
    (hirr : ∀ W : Submodule Γ(T.left, ⊤) (SecM A L k T),
      (∀ (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)), IsActOf A L k θ s s' →
        SecM.ofSec A s ∈ W → SecM.ofSec A s' ∈ W) → W = ⊥ ∨ W = ⊤)
    (ρ : ThetaGrp A L k T → (SecM A L k T ≃ₗ[Γ(T.left, ⊤)] SecM A L k T))
    (h₁ : ∀ θ s s', IsActOf A L k θ s s' ↔ ρ θ (SecM.ofSec A s) = SecM.ofSec A s')
    (h₃ : ∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v)
    (h₄ : ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v))
    (U : I → ThetaGrp A L k T) (hU : ∀ θ : ThetaGrp A L k T, ∃ c, (U c).pt = θ.pt)
    (v : SecM A L k T) (hv : v ≠ 0) :
    Submodule.span Γ(T.left, ⊤) (Set.range fun c => ρ (U c) v) = ⊤ := by
  have mem : ∀ θ, ρ θ v ∈ Submodule.span Γ(T.left, ⊤) (Set.range fun c => ρ (U c) v) := fun θ => by
    obtain ⟨c, hc⟩ := hU θ
    obtain ⟨u, hu⟩ := h₃ _ _ hc
    rw [hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  refine (hirr _ fun θ s s' hs hm => ?_).resolve_left fun h => ?_
  · rw [← (h₁ θ s s').1 hs]
    refine (Submodule.span_le (p := Submodule.comap (ρ θ).toLinearMap
      (Submodule.span Γ(T.left, ⊤) (Set.range fun c => ρ (U c) v)))).2 ?_ hm
    rintro _ ⟨c, rfl⟩
    obtain ⟨θ', -, h'⟩ := h₄ θ (U c)
    exact (h' v ▸ mem θ' :)
  · have := mem (U (Classical.arbitrary I))
    rw [h, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at this
    exact hv this

theorem exists_geomPoint (X : Scheme.{0}) [IsAffine X] (𝔪 : Ideal Γ(X, ⊤)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (u : Spec (CommRingCat.of K) ⟶ X),
      ∀ r, u.appTop.hom r = 0 ↔ r ∈ 𝔪 := by
  letI := Ideal.Quotient.field 𝔪
  let K := AlgebraicClosure (Γ(X, ⊤) ⧸ 𝔪)
  let f : Γ(X, ⊤) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom ((algebraMap (Γ(X, ⊤) ⧸ 𝔪) K).comp (Ideal.Quotient.mk 𝔪))
  refine ⟨K, inferInstance, inferInstance, Spec.map f ≫ X.isoSpec.inv, fun r => ?_⟩
  have e : (Spec.map f ≫ X.isoSpec.inv).appTop = f ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
    have e₀ : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
      rw [← Category.comp_id X.isoSpec.inv.appTop, ← (Scheme.ΓSpecIso Γ(X, ⊤)).hom_inv_id,
        ← Category.assoc, ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop,
        Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop, Category.id_comp]
    rw [Scheme.Hom.comp_appTop, e₀, Scheme.ΓSpecIso_inv_naturality]
  rw [e]
  refine (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1).trans ?_
  exact (map_eq_zero_iff _ (algebraMap (Γ(X, ⊤) ⧸ 𝔪) K).injective).trans Ideal.Quotient.eq_zero_iff_mem

theorem natCast_ne_zero {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S) {m : ℕ}
    (hm : IsUnit (m : Γ(S, ⊤))) : (m : K) ≠ 0 := by
  have := (hm.map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast, map_natCast] at this
  exact this.ne_zero

theorem vvRank_of_theta :
    SecBaseChangeAnySt → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (k : ℕ), (k = 1 ∨ 4 ≤ k) → (k : K) ≠ 0 → ∀ W : Submodule Γ((Over.mk t).left, ⊤) (SecM P.A P.L k (Over.mk t)), (∀ (θ : ThetaGrp P.A P.L k (Over.mk t)) (s s' : LB.Sec (LPow P.A P.L k (Over.mk t))), IsActOf P.A P.L k θ s s' → SecM.ofSec P.A s ∈ W → SecM.ofSec P.A s' ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔ x ^ N = 1) → ∀ S : Scheme.{0}, VVRankSt (S := S) := by
  intro hbc hirr hmul hlift hact hker S P m ze hodd hunit hlev T p
  obtain ⟨lev⟩ := hlev
  have hcomm := P.isAb.comm
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have hN : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hm0)
  have hk : m ^ 2 = 1 ∨ 4 ≤ m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [show m = 1 by omega]; rfl
    · right; nlinarith
  have : NeZero (m ^ 2) := ⟨by omega⟩
  obtain ⟨V₀, hp₀, b₀, hb₀⟩ := hbc S P (m ^ 2) hN (T.hom p)
  obtain ⟨V₁, hp₁, b₁, hb₁⟩ := hbc S P 1 le_rfl (T.hom p)
  let toB : ∀ T : Over S, T ⟶ baseOver S := fun T => Over.homMk T.hom (Category.comp_id _)
  let x : (Fin (2 * P.g) → Fin (m ^ 2)) → (T ⟶ P.A) := fun c =>
    linComb (fun i => toB T ≫ lev.pt i) fun i => (c i : ℕ)
  have hx : ∀ c, x c ^ (m ^ 2) = 1 := fun c => linComb_pow _ _ _ fun i => by
    rw [← MonObj.comp_pow, lev.torsion, MonObj.comp_one]
  choose W hW U₀ hU₀ using fun c => hlift S P (m ^ 2) T (x c) (hx c) p
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open
    (u := ((T.hom ⁻¹ᵁ V₀ : Set T.left) ∩ (T.hom ⁻¹ᵁ V₁ : Set T.left)) ∩ ⋂ c, (W c : Set T.left))
    ⟨⟨hp₀, hp₁⟩, Set.mem_iInter.2 hW⟩
    (((T.hom ⁻¹ᵁ V₀).isOpen.inter (T.hom ⁻¹ᵁ V₁).isOpen).inter
      (isOpen_iInter_of_finite fun c => (W c).isOpen))
  change T.left.Opens at V
  refine ⟨V, hpV, hV, ?_⟩
  have haff : IsAffine (overRes V).left := hV
  have hne : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨p, hpV⟩, trivial⟩⟩
  have hnt : Nontrivial Γ((overRes V).left, ⊤) :=
    Scheme.component_nontrivial V.toScheme ⊤
  have mk : ∀ V' : S.Opens, V ≤ T.hom ⁻¹ᵁ V' → (overRes V ⟶ overRes (T := baseOver S) V') :=
    fun V' h => Over.homMk (T.hom.resLE V' V h) (by
      change T.hom.resLE V' V h ≫ V'.ι ≫ 𝟙 S = V.ι ≫ T.hom
      rw [Category.comp_id, Scheme.Hom.resLE_comp_ι])
  have h₀ := mk V₀ fun y hy => (hle hy).1.1
  have h₁ := mk V₁ fun y hy => (hle hy).1.2
  have hWle : ∀ c, V ≤ W c := fun c y hy => Set.mem_iInter.1 (hle hy).2 c
  let hc : ∀ c, overRes V ⟶ overRes (W c) := fun c => Over.homMk (T.left.homOfLE (hWle c)) (by
    change T.left.homOfLE (hWle c) ≫ (W c).ι ≫ T.hom = V.ι ≫ T.hom
    rw [Scheme.homOfLE_ι_assoc])
  have hcι : ∀ c, hc c ≫ overResι (W c) = overResι V := fun c =>
    Over.OverMorphism.ext (T.left.homOfLE_ι (hWle c))
  choose U hU using fun c => exists_theta_pull P.A P.isLB (hc c) (U₀ c)
  have hUpt : ∀ c, (U c).pt = overResι V ≫ x c := fun c => by
    rw [(hU c).1, hU₀, ← Category.assoc, hcι]
  have H := hmul S P m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  have hsurj := surjective_mulA P m hm0 α₀ hα₀
  obtain ⟨α, hα, -⟩ := exists_gen_pullTo
    (φ' := ![(snd (overRes V) P.A).left, (snd (overRes V) P.A ^ m).left]) α₀ hα₀
    (snd (overRes V) P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd (overRes V) P.A).left ≫ (mulA P.A m).left = (snd (overRes V) P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  let th : LB.Sec (LPow P.A P.L 1 (overRes V)) := pullS P.A _ h₁ (b₁ i₀)
  obtain ⟨s₁, hs₁⟩ := exists_isTwistPull P.A (ψ := mulT P.A (overRes V) m) (hm := lift_snd _ _) (b := 1)
    P.isLB hα th
  obtain ⟨ρ, hρ, -⟩ := hact S P (m ^ 2 : ℕ) (overRes V)
  let t : (Fin (2 * P.g) → Fin (m ^ 2)) → SecM P.A P.L (m ^ 2 : ℕ) (overRes V) := fun c =>
    ρ (U c) (SecM.ofSec P.A s₁)
  have ht : ∀ c, IsActOf P.A P.L (m ^ 2 : ℕ) (U c) s₁ (SecM.toSec P.A (t c)) := fun c =>
    (hρ _ _ _).2 rfl
  obtain ⟨b, hb⟩ := exists_basis P (m ^ 2) b₀ hb₀ (overRes V) h₀
  have hspan : Submodule.span Γ((overRes V).left, ⊤) (Set.range t) = ⊤ := by
    refine span_eq_top_of_functionals b t fun 𝔪 h𝔪 l hl y => ?_
    obtain ⟨K, _, _, u, hu⟩ := exists_geomPoint (overRes V).left 𝔪 h𝔪
    let w : Spec (CommRingCat.of K) ⟶ S := u ≫ (overRes V).hom
    let h : Over.mk w ⟶ overRes V := Over.homMk u rfl
    have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
    have hntK : Nontrivial Γ((Over.mk w).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
    obtain ⟨b', hb'⟩ := exists_basis P (m ^ 2) b₀ hb₀ (Over.mk w) (h ≫ h₀)
    obtain ⟨b₁', hb₁'⟩ := exists_basis P 1 b₁ hb₁ (Over.mk w) (h ≫ h₁)
    refine (hu _).1 (functional_mem_of_span h.left.appTop.hom (pullM P.A P.L (m ^ 2 : ℕ) h) b b'
      (fun i => by rw [hb, hb', pullM_comp P.A P.isLB]) t ?_ l (fun c => (hu _).2 (hl c)) y)
    obtain ⟨ρ', k₁, -, k₃, k₄⟩ := hact S P (m ^ 2 : ℕ) (Over.mk w)
    choose U' hU' using fun c => exists_theta_pull P.A P.isLB h (U c)
    have e : ∀ c, pullM P.A P.L (m ^ 2 : ℕ) h (t c) =
        ρ' (U' c) (SecM.ofSec P.A (pullS P.A _ h s₁)) := fun c =>
      ((k₁ _ _ _).1 ((hU' c).2 _ _ (ht c))).symm
    simp only [e]
    refine span_translates_eq_top P.A (hirr S P K w (m ^ 2) hk
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ (natCast_ne_zero w hunit))) ρ' k₁ k₃ k₄ U'
      (fun θ => ?_) _ fun h0 => ?_
    · obtain ⟨c, hc'⟩ := lev.span K w θ.pt ((hker S P (m ^ 2) (Over.mk w) θ.pt).1 fun _ =>
        ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
      refine ⟨c, Eq.trans ?_ hc'⟩
      rw [(hU' c).1, hUpt, ← Category.assoc, comp_linComb]
      refine congrArg (fun y => linComb y _) (funext fun i => ?_)
      rw [← Category.assoc]
      refine congrArg (· ≫ lev.pt i) (Over.OverMorphism.ext ?_)
      exact Category.assoc u V.ι T.hom
    · obtain ⟨α', -, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A (overRes V) m) (hm := lift_snd _ _)
        (b := 1) P.isLB hα h (ψ' := mulT P.A (Over.mk w) m) (lift_snd _ _) (mulT_comm P.A h m)
      have hint : IsIntegral (Over.mk w ⊗ P.A).left :=
        (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
          P.isAb.geomConnected).geometrically_isIntegral w _ _
          (IsPullback.of_hasPullback w P.A.hom).flip
      have hz := ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A m hsurj _) (k₂ _ _ hs₁) h0
      exact b₁'.ne_zero i₀ ((hb₁' i₀).trans ((pullM_comp P.A P.isLB _ h h₁ _).symm.trans hz))
  have hVV : VVsub P (m ^ 2) m (overRes V) = SecM P.A P.L (m ^ 2 : ℕ) (overRes V) := by
    refine le_antisymm (Submodule.span_le.2 fun f hf => hf.1) fun f hf => ?_
    have h1 : Submodule.span Γ((overRes V).left, ⊤) (Set.range t) ≤
        (VVsub P (m ^ 2) m (overRes V)).comap (SecM P.A P.L (m ^ 2 : ℕ) (overRes V)).subtype := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨c, rfl⟩
      exact Submodule.subset_span ⟨(t c).2, inVV_of_isVVGen P _ m ⟨th, s₁, α, U c, hα, hs₁, ht c⟩⟩
    exact h1 (x := ⟨f, hf⟩) (hspan.ge trivial)
  rw [hVV]
  exact ⟨Module.Free.of_basis b, by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]⟩

theorem vvRank :
    SecBaseChangeAnySt → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (k : ℕ), (k = 1 ∨ 4 ≤ k) → (k : K) ≠ 0 → ∀ W : Submodule Γ((Over.mk t).left, ⊤) (SecM P.A P.L k (Over.mk t)), (∀ (θ : ThetaGrp P.A P.L k (Over.mk t)) (s s' : LB.Sec (LPow P.A P.L k (Over.mk t))), IsActOf P.A P.L k θ s s' → SecM.ofSec P.A s ∈ W → SecM.ofSec P.A s' ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔ x ^ N = 1) → PolBaseChangeSt → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ S : Scheme.{0}, VVRankSt (S := S) :=
  fun hbc hirr hmul hlift hact hker _ _ => vvRank_of_theta hbc hirr hmul hlift hact hker

end GlobalTheory.VVRank
