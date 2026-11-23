import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.TraceOrth

section Characters

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {Y : Scheme.{0}} {x x' : Y ⟶ S}

def cf {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) : Γ(Y, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (Scheme.Hom.appTop (X := Z) (Y := Y) (r ≫ (fst (Over.mk x) A).left)).hom

omit [GrpObj A] in
theorem gs_cf {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (a : Γ(Y, ⊤)) :
    gs (r ≫ (fst (Over.mk x) A).left) z ⊤ a = cf r z a := gs_eq _ z ⊤ trivial a

def cu {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) : Γ(Y, ⊤)ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (cf r z).toMonoidHom

omit [GrpObj A] in
theorem gm_cu {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (a : Γ(Y, ⊤)ˣ) :
    gm (r ≫ (fst (Over.mk x) A).left) z ⊤ a = cu r z a := Units.ext (gm_val _ z ⊤ trivial a)

theorem cf_transl {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (c : Over.mk x ⟶ A) :
    cf (r ≫ (translT A c).left) z = cf r z := by
  rw [cf, cf, Category.assoc, CommPairing.translT_fst]

theorem cu_transl {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (c : Over.mk x ⟶ A) :
    cu (r ≫ (translT A c).left) z = cu r z := by
  rw [cu, cu, cf_transl]

theorem sec_fst : (ptSecT A (1 : Over.mk x ⟶ A)).left ≫ (fst (Over.mk x) A).left = 𝟙 _ := by
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

variable (L x) in
theorem const_ext {u v : Γ(Y, ⊤)ˣ} (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J),
    Good L.L z J → cu r z u = cu r z v) : u = v :=
  unit_ext fun y _ => by
    choose I hI using fun χ : Y ⟶ A.left => exists_chart L.isLB (χ y)
    have := h Y (ptSecT A (1 : Over.mk x ⟶ A)).left y I hI
    rw [← gm_cu, ← gm_cu] at this
    exact (congrArg (fun q : Y ⟶ Y => gm q y ⊤ u) sec_fst).symm.trans
      (this.trans (congrArg (fun q : Y ⟶ Y => gm q y ⊤ v) sec_fst))

theorem transl_transl {T : Over S} (a b : T ⟶ A) :
    (translT A a).left ≫ (translT A b).left = (translT A (b * a)).left := by
  rw [← Over.comp_left, translT_mul]

variable {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  (β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))) (β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2)))

def gam {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.L.ι) :
    (Z.presheaf.stalk z)ˣ := val β₀ r z J * (val β r z J)⁻¹

variable {β β₀}

theorem exists_comm (hA : IsAbelianScheme A) (hβ : β.IsGen) (hβ₀ : β₀.IsGen) {e c : Over.mk x ⟶ A}
    (he : e ^ p = 1) (hc : c ∈ transKer A Ψ) :
    ∃ χ : Γ(Y, ⊤)ˣ, WeilIs A L.L ((p : ℤ) ^ 2) e c χ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J), Good L.L z J →
        gam β β₀ (r ≫ (translT A (e * c)).left) z J * gam β β₀ r z J =
          cu r z χ * (gam β β₀ (r ≫ (translT A e).left) z J * gam β β₀ (r ≫ (translT A c).left) z J) := by
  have := hA.comm
  obtain ⟨V, rfl, hV⟩ := exists_isDescLift hβ₀ ((mem_transKer_mulT p e).2 he)
  obtain ⟨U, rfl, hU⟩ := exists_isDescLift hβ hc
  obtain ⟨χ, hχ⟩ := CommutatorPairing.exists_commIsOf globalFns_holds hA L.isLB V U
  refine ⟨χ, GlobalLift.weilIs_of_commIsOf globalFns_holds hA L.isLB hχ, fun Z r z J hJ => ?_⟩
  have h := (CommPairing.commIsOf_iff L.isLB V U χ).1 hχ Z r z J hJ
  have h' := (congrArg₂ (· * ·) (hV.val r z hJ) (hU.val _ z hJ)).symm.trans (h.trans (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (hU.val r z hJ) (hV.val _ z hJ)) (gm_cu r z χ)))
  rw [Category.assoc, Category.assoc, transl_transl, transl_transl, mul_comm U.pt] at h'
  simp only [gam]
  apply Additive.ofMul.injective
  have a := congrArg Additive.ofMul h'
  simp only [ofMul_mul, ofMul_inv] at a ⊢
  linear_combination (norm := abel) a

theorem exists_root (hA : IsAbelianScheme A) (hβ : β.IsGen) (hβ₀ : β₀.IsGen) {c : Over.mk x ⟶ A}
    (he : c ^ p = 1) (hc : c ∈ transKer A Ψ) :
    ∃ ζ : Γ(Y, ⊤)ˣ, ζ ^ p = 1 ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J), Good L.L z J →
        gam β β₀ (r ≫ (translT A c).left) z J = cu r z ζ * gam β β₀ r z J := by
  have := hA.comm
  obtain ⟨⟨_, v, gv⟩, rfl, hV⟩ := exists_isDescLift hβ₀ ((mem_transKer_mulT p c).2 he)
  obtain ⟨⟨c', u, gu⟩, rfl, hU⟩ := exists_isDescLift hβ hc
  obtain ⟨ζ, hζ⟩ := CommutatorPairing.exists_ratio L.isLB (fun _ _ _ => rfl) (fst (Over.mk x) A).left
    (ptSecT A (1 : Over.mk x ⟶ A)).left sec_fst (CommPairing.surj_fst globalFns_holds hA _) gu gv
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J), Good L.L z J →
      gam β β₀ (r ≫ (translT A _).left) z J = cu r z ζ * gam β β₀ r z J := fun Z r z J hJ => by
    have h' := (hU.val r z hJ).symm.trans ((hζ Z r z J hJ).trans (congrArg₂ (· * ·) (hV.val r z hJ) (gm_cu r z ζ)))
    simp only [gam]
    apply Additive.ofMul.injective
    have a := congrArg Additive.ofMul h'
    simp only [ofMul_mul, ofMul_inv] at a ⊢
    linear_combination (norm := abel) a
  refine ⟨ζ, const_ext L x fun Z r z J hJ => ?_, key⟩
  have ind : ∀ j : ℕ, gam β β₀ (r ≫ (translT A (_ ^ j)).left) z J = cu r z ζ ^ j * gam β β₀ r z J := fun j => by
    induction j with
    | zero => rw [pow_zero, pow_zero, translT_one, Over.id_left, Category.comp_id, _root_.one_mul]
    | succ j ih =>
      rw [pow_succ', ← transl_transl, ← Category.assoc, key _ _ z J hJ, ih, cu_transl, pow_succ', _root_.mul_assoc]
  have h := ind p
  rw [show c' ^ p = 1 from he, translT_one, Over.id_left, Category.comp_id] at h
  rw [map_pow, map_one]
  exact right_eq_mul.1 h

theorem char_sum [IsDomain Γ(Y, ⊤)] [IsCommMonObj A] (hA : IsAbelianScheme A) (hβ : β.IsGen) (hβ₀ : β₀.IsGen) {D : Type} [Group D] [Fintype D]
    (e : D →* (Over.mk x ⟶ A)) (he : ∀ d, e d ^ p = 1) {c : Over.mk x ⟶ A} (hc : c ∈ transKer A Ψ)
    (hnt : ∃ d, ¬ WeilIs A L.L ((p : ℤ) ^ 2) (e d) c 1) {Z : Scheme.{0}} (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) {J}
    (hJ : Good L.L z J) :
    ∑ d, (gam β β₀ (r ≫ (translT A (e d * c)).left) z J * (gam β β₀ (r ≫ (translT A (e d)).left) z J)⁻¹).val = 0 := by
  choose χ hw hχ using fun d => exists_comm hA hβ hβ₀ (he d) hc
  have hm : ∀ d d', χ (d * d') = χ d * χ d' := fun d d' => const_ext L x fun Z r z J hJ => by
    have h₁ := hχ (d * d') Z r z J hJ
    have h₂ := hχ d Z (r ≫ (translT A (e d')).left) z J hJ
    have h₃ := hχ d' Z r z J hJ
    rw [cu_transl, Category.assoc, Category.assoc, Category.assoc, transl_transl, transl_transl, transl_transl,
      mul_right_comm, mul_comm c, ← map_mul] at h₂
    rw [map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul h₁
    have a₂ := congrArg Additive.ofMul h₂
    have a₃ := congrArg Additive.ofMul h₃
    simp only [ofMul_mul] at a₁ a₂ a₃ ⊢
    linear_combination (norm := abel) a₂ + a₃ - a₁
  let X : D →* Γ(Y, ⊤) := (Units.coeHom _).comp (MonoidHom.mk' χ hm)
  have hX : X ≠ 1 := fun h => by
    obtain ⟨d, hd⟩ := hnt
    have : χ d = 1 := Units.ext (DFunLike.congr_fun h d)
    exact hd (this ▸ hw d)
  have h0 := congrArg (cf r z) (sum_hom_units_eq_zero X hX)
  rw [map_sum, map_zero] at h0
  rw [← zero_mul (gam β β₀ (r ≫ (translT A c).left) z J * (gam β β₀ r z J)⁻¹).val, ← h0, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine Eq.trans (congrArg Units.val ?_) (Units.val_mul (cu r z (χ d)) _)
  apply Additive.ofMul.injective
  have a := congrArg Additive.ofMul (hχ d Z r z J hJ)
  simp only [ofMul_mul, ofMul_inv] at a ⊢
  linear_combination (norm := abel) a

end Characters

section Points

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {Y : Scheme.{0}} {x x' : Y ⟶ S}

def pt {Z : Scheme.{0}} {y : Z ⟶ S} (t : Z ⟶ Y) (h : t ≫ x = y) (a : Over.mk y ⟶ A) : Z ⟶ (Over.mk x ⊗ A).left :=
  (lift (Over.homMk t h : Over.mk y ⟶ Over.mk x) a).left

section
variable {Z : Scheme.{0}} {y : Z ⟶ S} (t : Z ⟶ Y) (h : t ≫ x = y)
omit [GrpObj A]

theorem pt_fst (a : Over.mk y ⟶ A) : pt t h a ≫ (fst (Over.mk x) A).left = t := lift_l_fst _ _

theorem pt_snd (a : Over.mk y ⟶ A) : pt t h a ≫ (snd (Over.mk x) A).left = a.left := lift_l_snd _ _

theorem pt_inj {a b : Over.mk y ⟶ A} (e : pt t h a = pt t h b) : a = b :=
  Over.OverMorphism.ext ((pt_snd t h a).symm.trans ((congrArg (· ≫ _) e).trans (pt_snd t h b)))

theorem comp_pt {Z' : Scheme.{0}} {y' : Z' ⟶ S} (u : Z' ⟶ Z) (hu : u ≫ y = y') {t' : Z' ⟶ Y} (ht : u ≫ t = t')
    (h' : t' ≫ x = y') (a : Over.mk y ⟶ A) :
    u ≫ pt t h a = pt t' h' ((Over.homMk u hu : Over.mk y' ⟶ Over.mk y) ≫ a) := by
  subst ht
  exact congrArg CommaMorphism.left (comp_lift (Over.homMk u hu : Over.mk y' ⟶ Over.mk y)
    (Over.homMk t h : Over.mk y ⟶ Over.mk x) a)

variable (x) in
theorem exists_pt : ∃ (t : (Over.mk x ⊗ A).left ⟶ Y) (a : Over.mk (t ≫ x) ⟶ A), pt t rfl a = 𝟙 _ :=
  ⟨(fst (Over.mk x) A).left, Over.homMk (snd (Over.mk x) A).left
    ((Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm),
    pullback.hom_ext ((pt_fst _ _ _).trans (Category.id_comp _).symm) ((pt_snd _ _ _).trans (Category.id_comp _).symm)⟩

theorem hom_ext_pt {W : Scheme.{0}} {u v : (Over.mk x ⊗ A).left ⟶ W}
    (H : ∀ (Z : Scheme.{0}) (t : Z ⟶ Y) (a : Over.mk (t ≫ x) ⟶ A), pt t rfl a ≫ u = pt t rfl a ≫ v) : u = v := by
  obtain ⟨t, a, e⟩ := exists_pt (A := A) x
  have := H _ t a
  rwa [e, Category.id_comp, Category.id_comp] at this

end

section
variable {Z : Scheme.{0}} {y : Z ⟶ S} (t : Z ⟶ Y) (h : t ≫ x = y)

theorem pt_transl (a : Over.mk y ⟶ A) (c : Over.mk x ⟶ A) :
    pt t h a ≫ (translT A c).left = pt t h (((Over.homMk t h : Over.mk y ⟶ Over.mk x) ≫ c) * a) := by
  rw [pt, ← Over.comp_left, CommutatorPairing.lift_translT]; rfl

theorem pt_mulT (a : Over.mk y ⟶ A) (n : ℕ) : pt t h a ≫ (mulT A (Over.mk x) n).left = pt t h (a ^ n) := by
  rw [pt, ← Over.comp_left, mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd]; rfl

theorem pt_negT (a : Over.mk y ⟶ A) : pt t h a ≫ (negT A (Over.mk x)).left = pt t h a⁻¹ := by
  rw [pt, ← Over.comp_left, negT, comp_lift, lift_fst, lift_snd_assoc]; rfl

end

theorem pt_id (a : Over.mk x ⟶ A) : pt (𝟙 Y) (Category.id_comp x) a = (ptSecT A a).left := rfl

def IsHomT (Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left) : Prop :=
  ∀ (Z : Scheme.{0}) (y y' : Z ⟶ S) (t : Z ⟶ Y) (h : t ≫ x = y) (h' : t ≫ x' = y'),
    ∃ φ : (Over.mk y ⟶ A) →* (Over.mk y' ⟶ A), ∀ a, pt t h a ≫ Ψ = pt t h' (φ a)

variable {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}

theorem IsHomT.pointed (H : IsHomT Ψ) : IsPointed A Ψ := by
  constructor
  · refine hom_ext_pt fun Z t a => ?_
    obtain ⟨φ, hφ⟩ := H Z _ _ t rfl rfl
    rw [← Category.assoc, hφ, pt_fst, pt_fst]
  · obtain ⟨φ, hφ⟩ := H Y x x' (𝟙 Y) (Category.id_comp _) (Category.id_comp _)
    have := hφ 1
    rwa [map_one, pt_id, pt_id] at this

theorem IsHomT.neg (H : IsHomT Ψ) : (negT A (Over.mk x)).left ≫ Ψ = Ψ ≫ (negT A (Over.mk x')).left := by
  refine hom_ext_pt fun Z t a => ?_
  obtain ⟨φ, hφ⟩ := H Z _ _ t rfl rfl
  rw [← Category.assoc, ← Category.assoc, pt_negT, hφ, hφ, pt_negT, map_inv]

theorem isHomT_mulT [IsCommMonObj A] (n : ℕ) : IsHomT (x := x) (x' := x) (mulT A (Over.mk x) n).left := by
  rintro Z _ _ t rfl rfl
  exact ⟨powMonoidHom n, fun a => pt_mulT _ _ a n⟩

theorem IsHomT.comp {x'' : Y ⟶ S} {Ψ' : (Over.mk x' ⊗ A).left ⟶ (Over.mk x'' ⊗ A).left} (H : IsHomT Ψ)
    (H' : IsHomT Ψ') : IsHomT (Ψ ≫ Ψ') := fun Z y y' t h h' => by
  obtain ⟨φ, hφ⟩ := H Z _ _ t h rfl
  obtain ⟨φ', hφ'⟩ := H' Z _ _ t rfl h'
  exact ⟨φ'.comp φ, fun a => by rw [← Category.assoc, hφ, hφ']; rfl⟩

omit [GrpObj A] in
theorem pt_nat {d : Over.mk x ⟶ A} {e : Over.mk x' ⟶ A}
    (H : pt (𝟙 Y) (Category.id_comp x) d ≫ Ψ = pt (𝟙 Y) (Category.id_comp x') e)
    {Z : Scheme.{0}} {y y' : Z ⟶ S} (t : Z ⟶ Y) (h : t ≫ x = y) (h' : t ≫ x' = y') :
    pt t h ((Over.homMk t h : Over.mk y ⟶ Over.mk x) ≫ d) ≫ Ψ =
      pt t h' ((Over.homMk t h' : Over.mk y' ⟶ Over.mk x') ≫ e) := by
  rw [← comp_pt (𝟙 Y) (Category.id_comp x) t h (Category.comp_id t),
    ← comp_pt (𝟙 Y) (Category.id_comp x') t h' (Category.comp_id t), Category.assoc, H]

theorem IsHomT.transl (H : IsHomT Ψ) {d : Over.mk x ⟶ A} {e : Over.mk x' ⟶ A}
    (hd : pt (𝟙 Y) (Category.id_comp x) d ≫ Ψ = pt (𝟙 Y) (Category.id_comp x') e) :
    (translT A d).left ≫ Ψ = Ψ ≫ (translT A e).left := by
  refine hom_ext_pt fun Z t a => ?_
  obtain ⟨φ, hφ⟩ := H Z _ _ t rfl rfl
  have := pt_inj _ _ ((hφ _).symm.trans (pt_nat hd t rfl rfl))
  rw [← Category.assoc, ← Category.assoc, pt_transl, hφ, hφ, pt_transl, map_mul, this]

theorem IsHomT.mem_ker (H : IsHomT Ψ) {d : Over.mk x ⟶ A} :
    d ∈ transKer A Ψ ↔ pt (𝟙 Y) (Category.id_comp x) d ≫ Ψ = pt (𝟙 Y) (Category.id_comp x') 1 := by
  constructor
  · intro hd
    have := congrArg (pt (𝟙 Y) (Category.id_comp x) (1 : Over.mk x ⟶ A) ≫ ·) (mem_transKer.1 hd)
    simp only [← Category.assoc, pt_transl, _root_.mul_one] at this
    exact ((congrArg (fun q => pt (𝟙 Y) (Category.id_comp x) q ≫ Ψ) (Category.id_comp d)).symm.trans this).trans
      H.pointed.2
  · intro hd
    rw [mem_transKer, H.transl hd, translT_one, Over.id_left, Category.comp_id]

end Points

section Fibres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [CommRing K]

theorem exists_tr (x : Sp K ⟶ Xo.X) {Z : Scheme.{0}} (t : Z ⟶ Sp K) :
    ∃ tr : (Over.mk (t ≫ x) ⟶ Xo.univ.t.G) ≃* (Over.mk t ⟶ Fib Xo x),
      ∀ a, pt t rfl a ≫ (swap x).hom = (tr a).left := by
  have h := isGrpPullback_pullback Xo.univ.t.G x
  have hl : ∀ u : Over.mk t ⟶ Fib Xo x, (pushHom h (Over.mk t) u).left = u.left ≫ pullback.fst _ _ := fun _ => rfl
  have hinj : ∀ u v : Over.mk t ⟶ Fib Xo x, u.left ≫ pullback.fst _ _ = v.left ≫ pullback.fst _ _ → u = v :=
    fun u v e => Over.OverMorphism.ext (h.1.hom_ext e ((Over.w u).trans (Over.w v).symm))
  have hb : Function.Bijective (pushHom h (Over.mk t)) := by
    refine ⟨fun u v e => hinj u v (by rw [← hl, ← hl, e]), fun q => ?_⟩
    refine ⟨Over.homMk (h.1.lift q.left t (Over.w q)) (h.1.lift_snd _ _ _), ?_⟩
    exact Over.OverMorphism.ext ((hl _).trans (h.1.lift_fst _ _ _))
  refine ⟨(MulEquiv.ofBijective _ hb).symm, fun a => pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, swap_hom_fst, pt_snd]
    exact ((hl _).symm.trans (congrArg (fun z => z.left) ((MulEquiv.ofBijective _ hb).apply_symm_apply a))).symm
  · rw [Category.assoc, swap_hom_snd, pt_fst]
    exact (Over.w ((MulEquiv.ofBijective _ hb).symm a)).symm

variable {x x' x'' : Sp K ⟶ Xo.X}

theorem isHomT_conj (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] : IsHomT (conj x x' f.left) := by
  rintro Z _ _ t rfl rfl
  obtain ⟨tr, h⟩ := exists_tr x t
  obtain ⟨tr', h'⟩ := exists_tr x' t
  refine ⟨tr'.symm.toMonoidHom.comp ((MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f).comp tr.toMonoidHom),
    fun a => ?_⟩
  rw [conj_apply, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq, h, h']
  exact (congrArg CommaMorphism.left (tr'.apply_symm_apply (tr a ≫ f))).symm

theorem conj_comp (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo x' ⟶ Fib Xo x'') :
    conj x x'' (f ≫ g).left = conj x x' f.left ≫ conj x' x'' g.left := by
  have key : ∀ (u : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')
      (v : pullback Xo.univ.t.G.hom x' ⟶ pullback Xo.univ.t.G.hom x''),
      conj x x'' (u ≫ v) = conj x x' u ≫ conj x' x'' v := fun u v => by
    simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc]
  exact key f.left g.left

theorem conj_pow (n : ℕ) : conj x x (𝟙 (Fib Xo x) ^ n : Fib Xo x ⟶ Fib Xo x).left =
    (mulT Xo.univ.t.G (Over.mk x) n).left := by
  refine hom_ext_pt fun Z t a => ?_
  obtain ⟨tr, h⟩ := exists_tr x t
  rw [pt_mulT, conj_apply, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq, h, h, map_pow]
  refine (Over.comp_left _ _ _ _ _).symm.trans ?_
  rw [MonObj.comp_pow, Category.comp_id]

end Fibres

section Sum

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {Y : Scheme.{0}} {x x' : Y ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {Ψ' : (Over.mk x' ⊗ A).left ⟶ (Over.mk x ⊗ A).left}

omit [GrpObj A] in
theorem cf_comp (h : Ψ ≫ (fst (Over.mk x') A).left = (fst (Over.mk x) A).left) {Z : Scheme.{0}}
    (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) : cf (r ≫ Ψ) z = cf r z := by
  rw [cf, cf, Category.assoc, h]

abbrev rv (L : RigLB A) {Z : Scheme.{0}} (q : Z ⟶ S) (z : Z) (J : (Z ⟶ A.left) → L.L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig q z J

theorem val_rig {k : ℤ} (z : Y) {J} (hJ : Good L.L z J) :
    val (LB.mulGen L.L (Y := Y) _ _ _ _ (rigT A L.L L.rig (Over.mk x) k) (rigT A L.L L.rig (Over.mk x') (-1)))
      (𝟙 Y) z J = rv L (𝟙 Y ≫ x) z J ^ k * rv L (𝟙 Y ≫ x') z J ^ (-1 : ℤ) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_rigT (Over.mk x) _ (𝟙 Y) z hJ) (val_rigT (Over.mk x') _ (𝟙 Y) z hJ))

theorem rig_val {k : ℤ} {β : LB.Gen (isoLB A L Ψ k)} (h : IsRigIso A L Ψ k β) (z : Y) {J} (hJ : Good L.L z J) :
    val β (𝟙 Y ≫ (ptSecT A (1 : Over.mk x ⟶ A)).left) z J =
      rv L (𝟙 Y ≫ x) z J ^ k * rv L (𝟙 Y ≫ x') z J ^ (-1 : ℤ) :=
  (val_pull hJ _ _ _).symm.trans ((val_corr hJ h.2.2 (𝟙 Y)).trans (val_rig z hJ))

variable {p : ℕ} {β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))}
  {β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2))}
  {Ψ₄ : (Over.mk x' ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {k : ℤ} {β₄ : LB.Gen (isoLB A L Ψ₄ k)}

theorem exists_rigIso_dual (h' : IsPointed A Ψ') (hc : Ψ' ≫ Ψ = Ψ₄) (hβ : IsRigIso A L Ψ _ β)
    (hβ₀ : IsRigIso A L _ _ β₀) (hβ₄ : IsRigIso A L Ψ₄ k β₄) :
    ∃ β₂ : LB.Gen (isoLB A L (Ψ' ≫ (mulT A (Over.mk x) p).left) k), IsRigIso A L _ k β₂ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x' ⊗ A).left) (z : Z) (J), Good L.L z J →
        val β₂ r z J = val β₄ r z J * gam β β₀ (r ≫ Ψ') z J := by
  subst hc
  obtain ⟨β₂, g₂, hv⟩ := exists_gen L.isLB (φ' := isoφ A (Ψ' ≫ (mulT A (Over.mk x) p).left)) (ε' := ![k, -1])
    (fun V _ g => by
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2 ⊕ Fin 2) (U := V) _ (prod_iso' g)
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_iso Ψ' g)
          (DVR.prod_neg _ _ (prod_iso Ψ' g)))).trans ?_
      rw [prod_iso']
      simp only [Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen L.L _ _ _ _ β₄ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ β₀ Ψ')
      (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β Ψ'))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ₄.2.1 (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ₀.2.1 _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ.2.1 _))))
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x' ⊗ A).left) (z : Z) (J), Good L.L z J →
      val β₂ r z J = val β₄ r z J * gam β β₀ (r ≫ Ψ') z J := fun Z r z J hJ => by
    rw [hv _ r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, gam]
  refine ⟨β₂, ⟨⟨?_, ?_⟩, g₂, corr_of_val L.isLB fun z J hJ => ?_⟩, hv'⟩
  · rw [Category.assoc, hβ₀.1.1, h'.1]
  · rw [← Category.assoc, h'.2, hβ₀.1.2]
  · refine (val_pull hJ _ _ _).trans ((hv' _ _ z J hJ).trans (Eq.trans ?_ (val_rig z hJ).symm))
    have e : (𝟙 Y ≫ (ptSecT A (1 : Over.mk x' ⟶ A)).left) ≫ Ψ' = 𝟙 Y ≫ (ptSecT A (1 : Over.mk x ⟶ A)).left :=
      (Category.assoc _ _ _).trans (congrArg (𝟙 Y ≫ ·) h'.2)
    have e₁ := (congrArg (fun q => gam β β₀ q z J) e).trans
      (congrArg₂ (fun u v : (Y.presheaf.stalk z)ˣ => u * v⁻¹) (rig_val hβ₀ z hJ) (rig_val hβ z hJ))
    refine (congrArg₂ (fun u v : (Y.presheaf.stalk z)ˣ => u * v) (rig_val hβ₄ z hJ) e₁).trans ?_
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel

theorem sum_val [IsDomain Γ(Y, ⊤)] [IsCommMonObj A] (hA : IsAbelianScheme A) (h0 : IsPointed A Ψ)
    (h' : IsPointed A Ψ') (hc : Ψ' ≫ Ψ = Ψ₄)
    (hβ : β.IsGen) (hβ₀ : β₀.IsGen) {β₂ : LB.Gen (isoLB A L (Ψ' ≫ (mulT A (Over.mk x) p).left) k)}
    (h₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x' ⊗ A).left) (z : Z) (J), Good L.L z J →
      val β₂ r z J = val β₄ r z J * gam β β₀ (r ≫ Ψ') z J)
    {D : Type} [Group D] [Fintype D] (e : D →* (Over.mk x ⟶ A)) (he : ∀ d, e d ^ p = 1)
    (U : D → ThetaGrp A L.L k (Over.mk x')) (hU : ∀ d, IsDescLift A L _ k β₂ (U d))
    (hUe : ∀ d, (translT A (U d).pt).left ≫ Ψ' = Ψ' ≫ (translT A (e d)).left)
    {n : ℕ} {c : Fin n → (Over.mk x ⟶ A)} (hr : IsRepsModTors (transKer A Ψ) p c)
    (hnt : ∀ i, c i ^ p ≠ 1 → ∃ d, ¬ WeilIs A L.L ((p : ℤ) ^ 2) (e d) (c i) 1)
    {s : LB.Sec (LPow A L.L 1 (Over.mk x))} {s₁ : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x))}
    {s₀ s' : LB.Sec (LPow A L.L 1 (Over.mk x'))} {s₄ : LB.Sec (LPow A L.L k (Over.mk x'))}
    (hs₁ : IsCarried A L _ _ β₀ s s₁) (hs₄ : IsCarried A L Ψ₄ k β₄ s₀ s₄) {a : Γ(Y, ⊤)}
    (ha : ∀ j, s'.f j = liftFun A (T := Over.mk x') _ a * s₀.f j)
    (htr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J), Good L.L z J →
      sv A L s' (r ≫ Ψ) z J = ∑ i, ((val β (r ≫ (translT A (c i)).left) z J)⁻¹).val *
        sv A L s₁ (r ≫ (translT A (c i)).left) z J)
    (F : D → LB.Sec (LPow A L.L k (Over.mk x'))) (hF : ∀ d, IsActOf A L.L k (U d) s₄ (F d)) :
    ∃ ζ : Γ(Y, ⊤)ˣ, ζ ^ p = 1 ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x' ⊗ A).left) (z : Z) (J), Good L.L z J →
        cf r z a * ∑ d, sv A L (F d) r z J = cf r z ((Fintype.card D : Γ(Y, ⊤)) * ζ.val) *
          (sv A L s (r ≫ Ψ' ≫ (mulT A (Over.mk x) p).left) z J * (val β₂ r z J).val) := by
  subst hc
  obtain ⟨i₀, hi₀, hu⟩ := hr.2 1 (Subgroup.one_mem _)
  have hi₀' : c i₀ ^ p = 1 := by simpa using hi₀
  obtain ⟨ζ, hζ, hζv⟩ := exists_root hA hβ hβ₀ hi₀' (hr.1 i₀)
  refine ⟨ζ, hζ, fun Z r z J hJ => ?_⟩
  have term : ∀ d, cf r z a * sv A L (F d) r z J = ∑ i,
      (gam β β₀ ((r ≫ Ψ') ≫ (translT A (e d * c i)).left) z J *
        (gam β β₀ ((r ≫ Ψ') ≫ (translT A (e d)).left) z J)⁻¹).val *
      (sv A L s ((r ≫ Ψ') ≫ (translT A (c i)).left ≫ (mulT A (Over.mk x) p).left) z J * (val β₂ r z J).val) := by
    intro d
    have q : (r ≫ (translT A (U d).pt).left) ≫ Ψ' = (r ≫ Ψ') ≫ (translT A (e d)).left := by
      rw [Category.assoc, hUe, Category.assoc]
    have a₁ := sv_smul (T := Over.mk x') ha ((r ≫ (translT A (U d).pt).left) ≫ Ψ' ≫ Ψ) z hJ
    have a₂ : gs (((r ≫ (translT A (U d).pt).left) ≫ Ψ' ≫ Ψ) ≫ (fst (Over.mk x') A).left) z ⊤ a = cf r z a := by
      rw [gs_cf, ← Category.assoc, cf_comp h0.1, cf_comp h'.1, cf_transl]
    have a₃ := htr Z ((r ≫ (translT A (U d).pt).left) ≫ Ψ') z J hJ
    rw [Category.assoc _ Ψ' Ψ, a₁, a₂, q] at a₃
    rw [act_val (hF d) r z hJ, (hU d).val r z hJ, hs₄.val _ z hJ, h₂ _ (r ≫ _) z J hJ, q]
    refine Eq.trans (b := (val β₂ r z J).val * ((gam β β₀ ((r ≫ Ψ') ≫ (translT A (e d)).left) z J)⁻¹).val *
      (cf r z a * sv A L s₀ ((r ≫ (translT A (U d).pt).left) ≫ Ψ' ≫ Ψ) z J)) ?_ ?_
    · rw [mul_inv, Units.val_mul, Units.val_mul]
      linear_combination (cf r z a * (val β₂ r z J).val *
        ((gam β β₀ ((r ≫ Ψ') ≫ (translT A (e d)).left) z J)⁻¹).val *
        sv A L s₀ ((r ≫ (translT A (U d).pt).left) ≫ Ψ' ≫ Ψ) z J) *
          (val β₄ (r ≫ (translT A (U d).pt).left) z J).inv_mul
    · rw [a₃, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have m : (translT A (e d * c i)).left ≫ (mulT A (Over.mk x) p).left =
          (translT A (c i)).left ≫ (mulT A (Over.mk x) p).left := by
        rw [← transl_transl, Category.assoc, mem_transKer.1 ((mem_transKer_mulT p _).2 (he d))]
      rw [hs₁.val _ z hJ, Category.assoc _ (translT A (e d)).left, transl_transl, mul_comm (c i),
        Category.assoc _ (translT A (e d * c i)).left, m, Units.val_mul,
        gam.eq_1 β β₀ ((r ≫ Ψ') ≫ (translT A (e d * c i)).left), Units.val_mul]
      ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun d _ => term d, Finset.sum_comm, Finset.sum_eq_single i₀]
  · rw [← Finset.sum_mul, mem_transKer.1 ((mem_transKer_mulT p _).2 hi₀'), Category.assoc]
    congr 1
    rw [map_mul, map_natCast, ← cf_comp h'.1 r z, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_comm (e d), ← transl_transl, ← Category.assoc, hζv _ _ z J hJ,
      mul_inv_cancel_right, cu_transl]
    rfl
  · intro i _ hi
    rw [← Finset.sum_mul, char_sum hA hβ hβ₀ e he (hr.1 i)
      (hnt i fun h => hi (hu i (by simpa using h))) _ z hJ, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Sum

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [Field K] {x x' : Sp K ⟶ Xo.X}

theorem finite_tors (x : Sp K ⟶ Xo.X) {M : ℕ} (hM : 0 < M) :
    Finite {w : Over.mk x ⟶ Xo.univ.t.G // w ^ M = 1} := by
  let ψ : K →+* AlgebraicClosure K := algebraMap _ _
  let g : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
  obtain ⟨J, _, hJ⟩ := TorsionRat.exists_enum Xo hM
  obtain ⟨u, -, hu⟩ := hJ _ (spMap ψ ≫ x)
  choose j hj using fun w : {w : Over.mk x ⟶ Xo.univ.t.G // w ^ M = 1} =>
    (hu (g ≫ w.1)).1 (by rw [← MonObj.comp_pow, w.2, MonObj.comp_one])
  exact Finite.of_injective j fun a b h =>
    Subtype.ext (TorsionRat.comp_injective ψ g rfl (by rw [← hj, ← hj, h]))

theorem exists_not_weilIs {Ψ : Gx x ⟶ Gx x'} {Ψ' : Gx x' ⟶ Gx x} (h : IsHomT Ψ) (h' : IsHomT Ψ') {p : ℕ}
    (hp : p.Prime) (hc : Ψ ≫ Ψ' = (mulT Xo.univ.t.G (Over.mk x) (p ^ 2)).left) (hR : AllRat Xo x' (p ^ 3))
    {c : Over.mk x ⟶ Xo.univ.t.G} (h₂ : c ^ p ^ 2 = 1) (h₁ : c ^ p ≠ 1) :
    ∃ (d : Over.mk x' ⟶ Xo.univ.t.G) (e : Over.mk x ⟶ Xo.univ.t.G),
      pt (𝟙 _) (Category.id_comp x') d ≫ Ψ' = pt (𝟙 _) (Category.id_comp x) e ∧ e ^ p = 1 ∧
        ¬ WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) e c 1 := by
  let Ω := AlgebraicClosure K
  let ψ : K →+* Ω := algebraMap _ _
  let g : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x := Over.homMk (spMap ψ) rfl
  let g' : Over.mk (spMap ψ ≫ x') ⟶ Over.mk x' := Over.homMk (spMap ψ) rfl
  have inj : ∀ {a b : Over.mk x ⟶ Xo.univ.t.G}, g ≫ a = g ≫ b → a = b := fun h =>
    TorsionRat.comp_injective ψ g rfl h
  obtain ⟨β, hβ⟩ := Spec.map_surjective ((spMap ψ ≫ x) ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom Ω (spMap ψ ≫ x) β.hom hβ.symm
  have p0 := hp.pos
  have p2 : 0 < p ^ 2 := by positivity
  have evp : ∀ n (k : ℕ) a, I.ev n (k • a) = I.ev n a ^ k := fun n k a => by
    induction k with
    | zero =>
      have := I.add n 0 0
      rw [add_zero] at this
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 this
    | succ k ih => rw [succ_nsmul, I.add, ih, pow_succ]
  obtain ⟨a, ha⟩ := (I.onto _ p2 (g ≫ c)).1 (by rw [← MonObj.comp_pow, h₂, MonObj.comp_one])
  obtain ⟨b, hb⟩ : ∃ b, ¬ (p : ℤ) ∣ Dw.EF b a := by
    by_contra hcon
    obtain ⟨f, rfl⟩ := H1.mem_nsmul_of_dvd Dw p a fun b => by_contra fun hb => hcon ⟨b, hb⟩
    refine h₁ (inj ?_)
    rw [MonObj.comp_pow, MonObj.comp_one, ← ha, ← evp, smul_smul, ← pow_two]
    exact (I.ker _ p2 _).2 ⟨f, rfl⟩
  have t₁ : I.ev (p ^ 2 * p) b ^ p ^ 2 = I.ev (p ^ 2) (p • b) := by
    rw [evp, ← I.tower _ p p2 p0, ← pow_mul, ← pow_two]
  have t₂ : I.ev (p ^ 2 * p) b ^ p ^ 3 = 1 := by
    rw [pow_succ p 2]
    exact (I.onto _ (by positivity) _).2 ⟨b, rfl⟩
  obtain ⟨φ, hφ⟩ := h _ _ _ (spMap ψ) rfl rfl
  obtain ⟨φ', hφ'⟩ := h' _ x' x (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  obtain ⟨d, hd⟩ := hR Ω ψ (φ (I.ev (p ^ 2 * p) b)) (by rw [← map_pow, t₂, map_one])
  have hd' : φ (I.ev (p ^ 2 * p) b) = g' ≫ d := Over.OverMorphism.ext hd
  have he : g ≫ φ' d = I.ev (p ^ 2) (p • b) := by
    refine pt_inj (spMap ψ) rfl ((pt_nat (hφ' d) (spMap ψ) rfl rfl).symm.trans ?_)
    refine (congrArg (fun q => pt (spMap ψ) rfl q ≫ Ψ') hd').symm.trans ?_
    rw [← hφ, Category.assoc, hc, pt_mulT, t₁]
  refine ⟨d, φ' d, hφ' d, inj ?_, fun hw => hb ?_⟩
  · rw [MonObj.comp_pow, MonObj.comp_one, he, ← t₁, ← pow_mul]
    exact pow_succ p 2 ▸ t₂
  · have hA : IsAbelianScheme Xo.univ.t.G := (UnivPol.pol Xo).isAb
    have w₁ := CommPairing.weilIs_pull globalFns_holds hA Xo.univ.t.PP.isLB g hw
    have w₂ := I.isom _ p2 (p • b) a
    rw [map_one, he, ← ha, ← Nat.cast_pow] at w₁
    have w₃ := CommutatorPairing.weilIs_unique globalFns_holds hA Xo.univ.t.PP.isLB w₂ w₁
    have w₄ : I.ζ (p ^ 2) ^ Dw.EF (p • b) a = 1 := by
      apply Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom)
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv).1
      exact w₃.trans (map_one _).symm
    have w₅ := ((I.ζ_prim _ p2).zpow_eq_one_iff_dvd _).1 w₄
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_pow, pow_two] at w₅
    exact (mul_dvd_mul_iff_left (Int.natCast_ne_zero.2 hp.ne_zero)).1 w₅

end Main

theorem thetaTrace_orthogonality : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K), p.Prime → IsPair (p ^ 2) f f' → AllRat Xo x' (p ^ 3) → a ≠ 0 → (∀ i, s'.f i = scal x' a i * s₀.f i) → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s' → ∃ (b ζ : K) (m : ℕ), ζ ^ p = 1 ∧ a * b = (p : K) ^ m * ζ ∧ ∃ f₂ : Fib Xo x' ⟶ Fib Xo x, IsMonHom f₂ ∧ f ≫ f₂ = 𝟙 _ ^ (p ^ 3) ∧ ∃ t, IsPullOf (p ^ 2) f₂ b s t ∧ IsTranslSum (p ^ 2) s₀ t := by
  intro E _ _ _ H Dw l Xo K _ x x' f f' p s s₀ s' a hp ⟨hf, hf', c₁, c₂, _, _⟩ hR ha hs htr
  have hA : IsAbelianScheme Xo.univ.t.G := (UnivPol.pol Xo).isAb
  have : Fact p.Prime := ⟨hp⟩
  have : IsCommMonObj (Fib Xo x) := Functor.isCommMonObj_obj
  let iso := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Sp K, ⊤) := iso.toMulEquiv.isDomain
  have hΨ := isHomT_conj f
  have hΨ' := isHomT_conj f'
  have k₁ : conj x x' f.left ≫ conj x' x f'.left = (mulT Xo.univ.t.G (Over.mk x) (p ^ 2)).left := by
    rw [← conj_comp, c₁, conj_pow]
  have k₂ : conj x' x f'.left ≫ conj x x' f.left = (mulT Xo.univ.t.G (Over.mk x') (p ^ 2)).left := by
    rw [← conj_comp, c₂, conj_pow]
  have k₃ : conj x' x (f' ≫ 𝟙 (Fib Xo x) ^ p).left =
      conj x' x f'.left ≫ (mulT Xo.univ.t.G (Over.mk x) p).left := by rw [conj_comp, conj_pow]
  generalize conj x x' f.left = Ψ at *
  generalize conj x' x f'.left = Ψ' at *
  have hΨ₂ := hΨ'.comp (isHomT_mulT p)
  obtain ⟨β, s₁, n, c, hβ, hs₁, hr, hv⟩ := isThetaTrace_iff.1 htr
  obtain ⟨β₀, hβ₀, hc₀⟩ := hs₁.exists_isRigIso
  obtain ⟨s₄, hs₄⟩ := exists_isMulPull (p ^ 2) s₀
  obtain ⟨β₄, hβ₄, hc₄⟩ := hs₄.exists_isRigIso
  obtain ⟨β₂, hβ₂, h₂⟩ := exists_rigIso_dual hΨ'.pointed k₂ hβ hβ₀ hβ₄
  obtain ⟨φ, hφ⟩ := hΨ _ x x' (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  obtain ⟨φ', hφ'⟩ := hΨ' _ x' x (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  have e₁ : ∀ u, φ' (φ u) = u ^ p ^ 2 := fun u => pt_inj (𝟙 _) (Category.id_comp x) (by
    rw [← hφ', ← hφ, Category.assoc, k₁, pt_mulT])
  have e₂ : ∀ u, φ (φ' u) = u ^ p ^ 2 := fun u => pt_inj (𝟙 _) (Category.id_comp x') (by
    rw [← hφ, ← hφ', Category.assoc, k₂, pt_mulT])
  let D : Subgroup (Over.mk x' ⟶ Xo.univ.t.G) := ((powMonoidHom p).comp φ').ker
  have hD : ∀ d : D, φ' d ^ p = 1 := fun d => d.2
  have hD3 : ∀ d : D, d.1 ^ p ^ 3 = 1 := fun d => by
    rw [pow_succ p 2, pow_mul, ← e₂, ← map_pow, hD, map_one]
  have hD4 : ∀ d : D, d.1 ^ (p ^ 2) ^ 2 = 1 := fun d => by
    rw [show (p ^ 2) ^ 2 = p ^ 3 * p by ring, pow_mul, hD3, one_pow]
  have := finite_tors x' (pow_pos hp.pos 3)
  have : Finite D := Finite.of_injective
    (fun d : D => (⟨d.1, hD3 d⟩ : {w : Over.mk x' ⟶ Xo.univ.t.G // w ^ p ^ 3 = 1}))
    fun a b h => Subtype.ext (congrArg (·.1) h)
  let _ := Fintype.ofFinite D
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p) (G := D)).1 fun d => ⟨3, Subtype.ext (hD3 d)⟩
  rw [Nat.card_eq_fintype_card] at hm
  have hK : ∀ d : D, d.1 ∈ transKer _ (Ψ' ≫ (mulT Xo.univ.t.G (Over.mk x) p).left) := fun d =>
    hΨ₂.mem_ker.2 (by rw [← Category.assoc, hφ', pt_mulT, hD])
  choose U hU hU' using fun d : D => exists_isDescLift hβ₂.2.1 (hK d)
  choose F hF using fun d : D => exists_isActOf (U d) s₄
  obtain ⟨ζ, hζ, hval⟩ := sum_val hA hΨ.pointed hΨ'.pointed k₂ hβ.2.1 hβ₀.2.1 h₂ (φ'.comp D.subtype) hD U hU'
    (fun d => by rw [hU]; exact hΨ'.transl (hφ' d)) hr (fun i hi => by
      have h0 : φ (c i) = 1 := pt_inj _ _ ((hφ _).symm.trans (hΨ.mem_ker.1 (hr.1 i)))
      obtain ⟨d, e, hde, he, hw⟩ := exists_not_weilIs hΨ hΨ' hp k₁ hR (by rw [← e₁, h0, map_one]) hi
      obtain rfl : φ' d = e := pt_inj _ _ ((hφ' d).symm.trans hde)
      exact ⟨⟨d, he⟩, hw⟩) hc₀ hc₄ (a := toΓ K a) hs hv F hF
  have hi : ∀ u, toΓ K (iso u) = u := fun u => iso.symm_apply_apply u
  refine ⟨a⁻¹ * (p ^ m * iso ζ.val), iso ζ.val, m, ?_, mul_inv_cancel_left₀ ha _, f' ≫ 𝟙 (Fib Xo x) ^ p, ?_, ?_, ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hζ, Units.val_one, map_one]
  · have hpow : ∀ j : ℕ, IsMonHom (𝟙 (Fib Xo x) ^ j) := fun j => by
      induction j with
      | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit _ ≫ η[Fib Xo x]))
      | succ j ih =>
        rw [pow_succ]
        exact inferInstanceAs (IsMonHom (lift (𝟙 (Fib Xo x) ^ j) (𝟙 _) ≫ μ[Fib Xo x]))
    have := hpow p
    infer_instance
  · rw [← Category.assoc, c₁, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← pow_succ]
  let ε := (Fintype.equivFin D).symm
  let t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (((p ^ 2 : ℕ) : ℤ) ^ 2) (Over.mk x')) :=
    SecM.toSec _ (∑ i, SecM.ofSec _ (F (ε i)))
  have ht : ∀ j, t.f j = ∑ i, (F (ε i)).f j := fun j => by
    show (∑ i, SecM.ofSec _ (F (ε i)) : SecM Xo.univ.t.G Xo.univ.t.PP.L _ (Over.mk x')).1 j = _
    rw [Submodule.coe_sum, Finset.sum_apply]; rfl
  refine ⟨t, ?_, _, fun i => F (ε i), fun i => ?_, ht⟩
  · let s'' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (Over.mk x)) :=
      SecM.toSec _ ((show Γ((Over.mk x).left, ⊤) from toΓ K (a⁻¹ * (p ^ m * iso ζ.val))) • SecM.ofSec _ s)
    have h'' : ∀ j, s''.f j = liftFun Xo.univ.t.G (T := Over.mk x) _ (toΓ K (a⁻¹ * (p ^ m * iso ζ.val))) * s.f j :=
      fun _ => rfl
    rw [IsPullOf, k₃]
    refine ⟨β₂, s'', hβ₂, h'', isCarried_of_val fun z J hJ => ?_⟩
    have h := hval _ (𝟙 _) z J hJ
    rw [sv_sum ht _ z hJ, ε.sum_comp (fun d => sv _ _ (F d) (𝟙 _) z J), sv_smul (T := Over.mk x) h'' _ z hJ,
      gs_cf, cf_comp hΨ₂.pointed.1, map_mul, map_mul, _root_.mul_assoc, _root_.mul_assoc, map_mul, hi, map_pow,
      map_natCast, ← Nat.cast_pow p m, ← hm, ← _root_.mul_assoc, ← _root_.mul_assoc, _root_.mul_assoc _ (sv _ _ s _ z J), _root_.mul_assoc, ← h, ← _root_.mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ ha,
      map_one, map_one, _root_.one_mul]
  · obtain ⟨α₀, α, a₁, a₂, a₃, a₄⟩ := hs₄
    have h4 : (U (ε i)).pt ^ (p ^ 2) ^ 2 = 1 := by rw [hU]; exact hD4 _
    exact ⟨_, (U (ε i)).pt, α₀, α, s₄, U (ε i), rfl, h4, a₁, a₂, a₃, a₄,
      (hU' _).symLift hβ₂.2.1 Xo.univ.t.sym hΨ₂.neg h4, hF _⟩

end GlobalTheory.TraceOrth
