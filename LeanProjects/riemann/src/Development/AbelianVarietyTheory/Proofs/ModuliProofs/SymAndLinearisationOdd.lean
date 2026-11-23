import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawRigidifiedLineBundleDenseFibresStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.OddLinearisation

open KerPow ThetaSplit

theorem sq_lift_mul {G U : Type} [CommGroup G] [CommGroup U] (f f' F n : G → U) (D D' : G) (a c c' : U)
    (hF : ∀ g, F g = f g * f' (D * g) * a)
    (hc : ∀ g, f g * (f (D * g)⁻¹ * n (D * g) * (n g)⁻¹) = c)
    (hc' : ∀ g, f' g * (f' (D' * g)⁻¹ * n (D' * g) * (n g)⁻¹) = c')
    (comm : ∀ g, f g * f' (D * g) = f' g * f (D' * g)) (g : G) :
    F g * (F (D * D' * (D * D' * g))⁻¹ * n (D * D' * (D * D' * g)) * (n (D * D' * g))⁻¹)⁻¹ =
      f g * (f (D * (D * g))⁻¹ * n (D * (D * g)) * (n (D * g))⁻¹)⁻¹ *
      (f' (D * D * g) * (f' (D' * (D' * (D * D * g)))⁻¹ * n (D' * (D' * (D * D * g))) *
        (n (D' * (D * D * g)))⁻¹)⁻¹) := by
  have e₁ := hF g
  have e₂ := hF (D * D' * (D * D' * g))⁻¹
  have e₃ := hc (D' * (D * D' * g))
  have e₄ := hc' (D * D' * g)
  have e₅ := hc (D * g)
  have e₆ := hc' (D' * (D * D * g))
  have e₇ := comm (D * D' * g)
  have e₈ := comm (D * g)
  rw [show D * (D * D' * (D * D' * g))⁻¹ = (D' * (D * D' * g))⁻¹ by
    rw [_root_.mul_assoc D D' (D * D' * g), mul_inv D, mul_inv_cancel_left]] at e₂
  rw [← _root_.mul_assoc D D'] at e₃
  rw [show D * (D * D' * g) = D' * (D * D * g) by ac_rfl] at e₇
  rw [show D' * (D * g) = D * D' * g by ac_rfl] at e₈
  rw [show f' (D * D * g) = f' (D * (D * g)) by rw [_root_.mul_assoc]]
  apply Additive.ofMul.injective
  replace e₁ := congrArg Additive.ofMul e₁
  replace e₂ := congrArg Additive.ofMul e₂
  replace e₃ := congrArg Additive.ofMul e₃
  replace e₄ := congrArg Additive.ofMul e₄
  replace e₅ := congrArg Additive.ofMul e₅
  replace e₆ := congrArg Additive.ofMul e₆
  replace e₇ := congrArg Additive.ofMul e₇
  replace e₈ := congrArg Additive.ofMul e₈
  simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ ⊢
  linear_combination (norm := abel) e₁ - e₂ - e₃ - e₄ + e₅ + e₆ - e₇ - e₈

theorem unit_eq_one_of_dense {S : Scheme.{0}} [IsReduced S] {Sg : Set S} (hd : Dense Sg) (κ : Γ(S, ⊤)ˣ)
    (h : ∀ p ∈ Sg, ∃ (Z : Scheme.{0}) (x : Z ⟶ S) (z : Z), x z = p ∧ gm x z ⊤ κ = 1) : κ = 1 := by
  apply Units.ext
  rw [Units.val_one, ← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  by_contra hne
  obtain ⟨p, hp, hS⟩ := hd.inter_open_nonempty _ (S.basicOpen (κ.val - 1)).isOpen (by
    by_contra h'
    exact hne fun q hq => h' ⟨q, hq⟩)
  obtain ⟨Z, x, z, rfl, e⟩ := h p hS
  have hz : z ∈ Z.basicOpen ((x.app ⊤).hom (κ.val - 1)) := by
    rw [← Scheme.preimage_basicOpen]; exact hp
  have hu := (Z.mem_basicOpen _ z (show z ∈ x ⁻¹ᵁ ⊤ from trivial)).1 hz
  have e' := congrArg Units.val e
  rw [gm_val x z ⊤ trivial] at e'
  simp only [map_sub, map_one] at hu
  exact not_isUnit_zero ((congrArg IsUnit (sub_eq_zero.2 e')).mp hu)

theorem exists_canonical_lifts {X Y : Scheme.{0}} {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {φ : X ⟶ Y}
    {n : ℕ} (hw : LBIso (lbPow L n) (M.pull φ)) {μ' : X ⟶ X} {k : ℤ} (hk : k = n)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![k, -1])) (hα : α.IsGen) :
    ∃ B : ∀ (Z : Scheme.{0}) (z : Z), ((Z ⟶ Y) → M.ι) → (Z ⟶ X) → (Z.presheaf.stalk z)ˣ,
      ∀ t : X ⟶ X, t ≫ μ' = μ' → ∃ g : LB.Gen (LB.LinComb M (K := Fin 2) (fun i => ![𝟙 X, t] i ≫ φ) ![1, -1]),
        g.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good M z J →
          val g r z J = B Z z J r * (B Z z J (r ≫ t))⁻¹ := by
  subst hk
  obtain ⟨w, hw⟩ := hw
  have hP : (lbPow L n).IsLB := DVR.linComb_isLB L hL _ _
  choose I hI using fun (Z : Scheme.{0}) (z : Z) (χ : Z ⟶ X) => exists_chart hP (χ z)
  refine ⟨fun Z z J r => gw w r z (J (r ≫ φ)) (I Z z r) * val α r z (fun χ => I Z z χ PUnit.unit), fun t ht => ?_⟩
  obtain ⟨a, ha, va⟩ := exists_gen hL (K' := Fin 2) (φ' := ![𝟙 X, t]) (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, Category.comp_id, ht]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ α (LB.invGen L _ _ (LB.pullGen L _ _ α t)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  obtain ⟨b, hb, vb⟩ := exists_gen_lbPow n (ε := ![1, -1]) (fun k => by fin_cases k <;> simp) a ha 1
  obtain ⟨g, hg, vg⟩ := exists_up ((isGen_iff w).1 hw) hM hP b hb
  refine ⟨g, hg, fun Z r z J hJ => ?_⟩
  have hI' : Good (lbPow L n) z (I Z z) := hI Z z
  have hI'' : Good L z (fun χ => I Z z χ PUnit.unit) := fun χ => Set.mem_iInter.1 (hI' χ) PUnit.unit
  refine (vg Z r z _ _ (hJ.mem _ r) (hI'.mem _ r)).trans ?_
  have e := vb Z r z _ hI'
  rw [va Z r z _ hI'', val_mul hI'', val_inv, val_pull hI'', map_one, _root_.mul_one] at e
  refine (congrArg (_ * ·) e).trans ?_
  rw [pw, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, Category.id_comp, Category.assoc,
    zpow_one, zpow_neg, mul_inv]
  ac_rfl

section Fibre

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {M : LB A.left} {x : S' ⟶ S}

theorem pushHom_injective {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left} (hp : IsGrpPullback A' A x φ)
    (T : Over S') : Function.Injective (pushHom hp T) := fun a b h =>
  Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))

theorem push_comm {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left} (hp : IsGrpPullback A' A x φ) {t : A' ⟶ A'}
    {s : A ⟶ A} (h : pushHom hp A' t = pushHom hp A' (𝟙 A') ≫ s) : t.left ≫ φ = φ ≫ s.left :=
  (congrArg (fun q => q.left) h).trans (congrArg (· ≫ s.left) (Category.id_comp φ))

theorem one_comm {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left} (hp : IsGrpPullback A' A x φ) :
    (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left :=
  push_comm hp ((map_one _).trans (MonObj.comp_one _).symm)

theorem inv_comm {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left} (hp : IsGrpPullback A' A x φ) :
    ((𝟙 A')⁻¹).left ≫ φ = φ ≫ ((𝟙 A)⁻¹).left :=
  push_comm hp ((map_inv _ _).trans (by rw [GrpObj.comp_inv, Category.comp_id]))

theorem exists_transl_lift [IsCommMonObj A] {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left}
    (hp : IsGrpPullback A' A x φ) {m : ℕ} {h : 𝟙_ (Over S) ⟶ A} (hh : h ^ m = 1) :
    ∃ t : A'.left ⟶ A'.left, t ≫ φ = φ ≫ transl h ∧ t ≫ A'.hom = A'.hom ∧
      t ≫ (Out.mulA A' m).left = (Out.mulA A' m).left := by
  have w : (φ ≫ transl h) ≫ A.hom = A'.hom ≫ x := by rw [Category.assoc, transl_hom, hp.1.w]
  let t : A' ⟶ A' := Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _)
  have e : t.left ≫ φ = φ ≫ transl h := hp.1.lift_fst _ _ _
  refine ⟨t.left, e, Over.w t, ?_⟩
  have e' : pushHom hp A' t = pushHom hp A' (𝟙 A') ≫ ((toUnit A ≫ h) * 𝟙 A) :=
    Over.OverMorphism.ext (e.trans (congrArg (· ≫ transl h) (Category.id_comp φ).symm))
  rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  refine congrArg (fun q => q.left) (pushHom_injective hp A' ?_)
  rw [map_pow, map_pow, e', ← MonObj.comp_pow, mul_pow, ← MonObj.comp_pow, hh, MonObj.comp_one, _root_.one_mul,
    MonObj.comp_pow, Category.comp_id]

theorem fibre_sym [Subsingleton S'] [Nonempty S'] (hM : M.IsLB) (P : Out.PolAV S') {φ : P.A.left ⟶ A.left}
    (hp : IsGrpPullback P.A A x φ) {n : ℕ} (hw : LBIso (lbPow P.L n) (M.pull φ)) :
    HasGen M (K := Fin 2) (fun k => φ ≫ (![𝟙 A, (𝟙 A)⁻¹] k).left) ![1, -1] := by
  obtain ⟨U, hU, t, ht⟩ := P.sym (Classical.arbitrary S')
  have h₀ : HasGen P.L (K := Fin 2) (fun k => (P.A.hom ⁻¹ᵁ U).ι ≫ ![((𝟙 P.A)⁻¹).left, 𝟙 _] k) ![1, -1] :=
    HasGen.pull ⟨t, ht⟩ (𝟙 _) fun k => by
      fin_cases k
      · exact (Category.id_comp _).trans (congrArg (fun q : P.A ⟶ P.A => (P.A.hom ⁻¹ᵁ U).ι ≫ q.left)
          (Category.id_comp (GrpObj.inv : P.A ⟶ P.A)).symm)
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
  have h₁ : HasGen P.L (K := Fin 2) ![((𝟙 P.A)⁻¹).left, 𝟙 _] ![1, -1] :=
    h₀.of_range (𝟙 _) (fun y => by
      show P.A.hom y ∈ U
      rw [Subsingleton.elim (P.A.hom y) (Classical.arbitrary S')]; exact hU) fun k => Category.id_comp _
  have h₂ : ∀ j : ℕ, HasGen P.L (K := Fin 2) ![𝟙 _, ((𝟙 P.A)⁻¹).left] ![(j : ℤ), -(j : ℤ)] := fun j => by
    induction j with
    | zero => exact hasGen_of_trivial P.isLB fun U _ h => by simp
    | succ j ih =>
      refine ih.comb P.isLB h₁ fun U _ h => ?_
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
      push_cast
      module
  obtain ⟨a, ha⟩ := h₂ n
  obtain ⟨w, hw⟩ := hw
  obtain ⟨b, hb, -⟩ := exists_gen_lbPow n (ε := ![1, -1]) (fun k => by fin_cases k <;> simp) a ha 1
  obtain ⟨g, hg, -⟩ := exists_up ((isGen_iff w).1 hw) hM (DVR.linComb_isLB P.L P.isLB _ _) b hb
  refine HasGen.pull ⟨g, hg⟩ (𝟙 _) fun k => (Category.id_comp _).trans ?_
  fin_cases k
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact inv_comm hp

theorem fibre_lifts [IsCommMonObj A] [IsLocallyNoetherian S'] (hG : Out.GlobalFnsSt) (hm : Out.MulPullSt)
    (hM : M.IsLB) (P : Out.PolAV S') {φ : P.A.left ⟶ A.left} (hp : IsGrpPullback P.A A x φ) {m : ℕ}
    (hw : LBIso (lbPow P.L (m ^ 2)) (M.pull φ)) :
    (∀ h : 𝟙_ (Over S) ⟶ A, h ^ m = 1 → HasGen M (K := Fin 2) (fun k => φ ≫ ![𝟙 _, transl h] k) ![1, -1]) ∧
    ∀ h h' : 𝟙_ (Over S) ⟶ A, h ^ m = 1 → h' ^ m = 1 →
      ∀ (f : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 _, transl h] ![1, -1]))
        (f' : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 _, transl h'] ![1, -1])), f.IsGen → f'.IsGen →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good M z J →
          val f (r ≫ φ) z J * val f' ((r ≫ φ) ≫ transl h) z J =
            val f' (r ≫ φ) z J * val f ((r ≫ φ) ≫ transl h') z J := by
  obtain ⟨α, hα⟩ := hm S' P m
  obtain ⟨B, hB⟩ := exists_canonical_lifts P.isLB hM hw (by push_cast; rfl) α hα
  have eq : ∀ {h : 𝟙_ (Over S) ⟶ A} {t : P.A.left ⟶ P.A.left}, t ≫ φ = φ ≫ transl h → ∀ k : Fin 2,
      ![𝟙 _, t] k ≫ φ = φ ≫ ![𝟙 _, transl h] k := fun e k => by
    fin_cases k
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact e
  constructor
  · intro h hh
    obtain ⟨t, e, -, ht⟩ := exists_transl_lift hp hh
    obtain ⟨g, hg, -⟩ := hB t ht
    exact HasGen.pull ⟨g, hg⟩ (𝟙 _) fun k => (Category.id_comp _).trans (eq e k)
  · have key : ∀ h : 𝟙_ (Over S) ⟶ A, h ^ m = 1 →
        ∀ f : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 _, transl h] ![1, -1]), f.IsGen →
        ∃ (t : P.A.left ⟶ P.A.left) (c : Γ(S', ⊤)ˣ), t ≫ φ = φ ≫ transl h ∧ t ≫ P.A.hom = P.A.hom ∧
          ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good M z J →
            val f (r ≫ φ) z J = B Z z J r * (B Z z J (r ≫ t))⁻¹ * gm (r ≫ P.A.hom) z ⊤ c := fun h hh f hf => by
      obtain ⟨t, e, e', ht⟩ := exists_transl_lift hp hh
      obtain ⟨g, hg, vg⟩ := hB t ht
      obtain ⟨c, hc⟩ := CommutatorPairing.exists_ratio hM
        (fun U _ q => Finset.prod_congr rfl fun k _ => congrArg (fun s => q s ^ _) (eq e k).symm)
        P.A.hom η[P.A].left (Over.w _) (hG _ _ P.isAb).2 (DVR.pullGen_isGen _ _ _ _ hf φ) hg
      exact ⟨t, c, e, e', fun Z r z J hJ => by rw [← vg Z r z J hJ, ← hc Z r z J hJ, val_pull hJ]⟩
    intro h h' hh hh' f f' hf hf' Z r z J hJ
    obtain ⟨t, c, e₁, e₂, v⟩ := key h hh f hf
    obtain ⟨t', c', e₁', e₂', v'⟩ := key h' hh' f' hf'
    have tt : t ≫ t' = t' ≫ t := hp.1.hom_ext (by
      rw [Category.assoc, Category.assoc, e₁, e₁', ← Category.assoc, ← Category.assoc, e₁, e₁', Category.assoc,
        Category.assoc, ← transl_mul, ← transl_mul, mul_comm]) (by
      rw [Category.assoc, Category.assoc, e₂, e₂', e₂])
    rw [Category.assoc r φ, Category.assoc r φ, ← e₁, ← e₁', ← Category.assoc, ← Category.assoc, v _ _ z J hJ,
      v _ _ z J hJ, v' _ _ z J hJ, v' _ _ z J hJ]
    simp only [Category.assoc, e₂, e₂', tt]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end Fibre

section Global

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left}

theorem comp_transl (g : A ⟶ A) (h : 𝟙_ (Over S) ⟶ A) : g.left ≫ transl h = ((toUnit A ≫ h) * g).left := by
  rw [transl, ← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem comp_neg (g : A ⟶ A) : g.left ≫ ((𝟙 A)⁻¹).left = (g⁻¹).left := by
  rw [← Over.comp_left, GrpObj.comp_inv, Category.comp_id]

theorem hasGen_sq (hM : M.IsLB) (D : A ⟶ A)
    (hν : ∀ g : A ⟶ A, HasGen M (K := Fin 2) (fun k => (![g, g⁻¹] k).left) ![1, -1])
    (hN : ∀ g : A ⟶ A, HasGen M (K := Fin 4) (fun k => (![g, D * g, 1, D] k).left) ![1, -1, -1, 1]) :
    HasGen M (K := Fin 2) (fun k => (![D * D, (1 : A ⟶ A)] k).left) ![1, -1] := by
  have h₁ : HasGen M (K := Fin 2) (fun k => (![D, (1 : A ⟶ A)] k).left) ![2, -2] :=
    (hN D⁻¹).comb hM (hν D⁻¹) fun U _ h => by
      simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, mul_inv_cancel, inv_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
      module
  refine h₁.comb hM (hN D) fun U _ h => ?_
  simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

theorem exists_cocycle_sq (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hM : M.IsLB) {C : Type} [CommGroup C]
    (i d : C →* (𝟙_ (Over S) ⟶ A)) (hd : ∀ c, d c * d c = i c)
    (ν : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 _, ((𝟙 A)⁻¹).left] ![1, -1])) (hν : ν.IsGen)
    (f : ∀ c, LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 _, transl (d c)] ![1, -1])) (hf : ∀ c, (f c).IsGen)
    (comm : ∀ c c' (r : A.left ⟶ A.left) (y : A.left) (J), Good M y J →
      val (f c) r y J * val (f c') (r ≫ transl (d c)) y J = val (f c') r y J * val (f c) (r ≫ transl (d c')) y J) :
    ∃ u : ∀ c, LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 A.left, transl (i c)] ![1, -1]),
      (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr M _ _ _ _ (u (c * c'))
        (LB.mulGen M _ _ _ _ (u c) (LB.pullGen M _ _ (u c') (transl (i c)))) := by
  have hp := (hG S A hA).2
  have he : η[A].left ≫ A.hom = 𝟙 _ := Over.w _
  have nn : ((𝟙 A)⁻¹).left ≫ ((𝟙 A)⁻¹).left = 𝟙 A.left := by rw [comp_neg, inv_inv]; rfl
  have hδ : ∀ c, ∃ δ : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 _, transl (d c)] ![-1, 1]), δ.IsGen ∧
      ∀ (g : A ⟶ A) (y : A.left) (J), Good M y J → val δ g.left y J =
        val (f c) (((toUnit A ≫ d c) * g)⁻¹).left y J * val ν ((toUnit A ≫ d c) * g).left y J *
          (val ν g.left y J)⁻¹ := fun c => by
    have e : (transl (d c) ≫ ((𝟙 A)⁻¹).left) ≫ transl (d c) = ((𝟙 A)⁻¹).left := by
      rw [comp_neg, comp_transl, mul_inv, mul_inv_cancel_left]
    obtain ⟨δ, h₁, h₂⟩ := exists_gen hM (K' := Fin 2) (φ' := ![𝟙 _, transl (d c)]) (ε' := ![-1, 1]) (fun U _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one, Category.comp_id, e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow]
        module)
      (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ (LB.pullGen M _ _ (f c) (transl (d c) ≫ ((𝟙 A)⁻¹).left))
        (LB.pullGen M _ _ ν (transl (d c)))) (LB.invGen M _ _ ν))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (hf c) _)
        (DVR.pullGen_isGen _ _ _ _ hν _)) (DVR.invGen_isGen _ _ _ _ hν))
    refine ⟨δ, h₁, fun g y J hJ => ?_⟩
    rw [h₂ _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, ← Category.assoc, comp_transl,
      comp_neg]
  choose δ hδ vδ using hδ
  have hu : ∀ c, ∃ u : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 _, transl (i c)] ![1, -1]), u.IsGen ∧
      ∀ (g : A ⟶ A) (y : A.left) (J), Good M y J → val u g.left y J =
        val (f c) g.left y J * (val (δ c) ((toUnit A ≫ d c) * g).left y J)⁻¹ := fun c => by
    obtain ⟨u, h₁, h₂⟩ := exists_gen hM (K' := Fin 2) (φ' := ![𝟙 _, transl (i c)]) (ε' := ![1, -1]) (fun U _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one, Category.comp_id, ← transl_mul, hd]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow]
        module)
      (LB.mulGen M _ _ _ _ (f c) (LB.invGen M _ _ (LB.pullGen M _ _ (δ c) (transl (d c)))))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hf c) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (hδ c) _)))
    refine ⟨u, h₁, fun g y J hJ => ?_⟩
    rw [h₂ _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, comp_transl]
  choose u hu vu using hu
  have hc : ∀ c, ∃ b : Γ(S, ⊤)ˣ, ∀ (g : A ⟶ A) (y : A.left) (J), Good M y J →
      val (f c) g.left y J * val (δ c) g.left y J = gm A.hom y ⊤ b := fun c => by
    obtain ⟨b, hb⟩ := SymLiftOdd.exists_const hM A.hom η[A].left he hp (fun U _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module) (DVR.mulGen_isGen _ _ _ _ _ _ _ (hf c) (hδ c))
    exact ⟨b, fun g y J hJ => by rw [← val_mul hJ, hb _ _ y J hJ, Over.w]⟩
  choose b hb using hc
  refine ⟨u, hu, fun c c' => ?_⟩
  obtain ⟨a, ha⟩ := CommutatorPairing.exists_ratio hM (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, Category.comp_id, ← transl_mul, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) A.hom η[A].left he hp (hf (c * c'))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hf c) (DVR.pullGen_isGen _ _ _ _ (hf c') (transl (d c))))
  refine corr_of_val hM fun y J hJ => ?_
  have key := sq_lift_mul (fun g : A ⟶ A => val (f c) g.left y J) (fun g => val (f c') g.left y J)
    (fun g => val (f (c * c')) g.left y J) (fun g => val ν g.left y J) (toUnit A ≫ d c) (toUnit A ≫ d c')
    (gm A.hom y ⊤ a) (gm A.hom y ⊤ (b c)) (gm A.hom y ⊤ (b c'))
    (fun g => by rw [ha _ _ y J hJ, val_mul hJ, val_pull hJ, comp_transl, Over.w])
    (fun g => by rw [← vδ c g y J hJ, hb c g y J hJ]) (fun g => by rw [← vδ c' g y J hJ, hb c' g y J hJ])
    (fun g => by rw [← comp_transl, ← comp_transl, comm c c' _ y J hJ]) (𝟙 A)
  have e₁ : toUnit A ≫ d (c * c') = (toUnit A ≫ d c) * (toUnit A ≫ d c') := by rw [map_mul, MonObj.comp_mul]
  have e₂ : toUnit A ≫ i c = (toUnit A ≫ d c) * (toUnit A ≫ d c) := by rw [← hd, MonObj.comp_mul]
  rw [val_mul hJ, val_pull hJ]
  show val (u (c * c')) (𝟙 A : A ⟶ A).left y J =
    val (u c) (𝟙 A : A ⟶ A).left y J * val (u c') ((𝟙 A : A ⟶ A).left ≫ transl (i c)) y J
  rw [comp_transl, vu _ _ y J hJ, vu _ _ y J hJ, vu _ _ y J hJ,
    vδ _ _ y J hJ, vδ _ _ y J hJ, vδ _ _ y J hJ, e₁, e₂]
  exact key

end Global

end GlobalTheory.OddLinearisation

namespace GlobalTheory

open KerPow ThetaSplit OddLinearisation in

theorem sym_and_linearisation_odd : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (m : ℕ) (M : LB A.left) (Sg : Set (Sp R)) (C : Type) [CommGroup C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → Odd m → IsUnit (m : R) → M.IsLB → Out.Rigidified A M → Out.RelAmple A M → Dense Sg → (∀ c, i c ^ m = 1) → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ Sp R) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), p ∈ Set.range x ∧ IsGrpPullback Pl.A A x φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → Out.Sym A M ∧ ∃ u : ∀ c, LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1]), (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr M _ _ _ _ (u (c * c')) (LB.mulGen M _ _ _ _ (u c) (LB.pullGen M _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left)) := by
  intro hlaw R _ _ _ A _ m M Sg C _ i hA hm _ hM _ hample hd htor hfib
  have := hA.comm
  have hG := hlaw.globalFns
  have eo : eSec A ≫ (1 : A ⟶ A).left = eSec A := by
    show η[A].left ≫ _ = η[A].left
    rw [← Over.comp_left, MonObj.comp_one, Hom.one_def]; simp
  have see : ∀ (ψ : Fin 2 → (A.left ⟶ A.left)),
      (∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (P : Out.PolAV (Sp K)) (φ : P.A.left ⟶ A.left),
        IsGrpPullback P.A A x φ → LBIso (lbPow P.L (m ^ 2)) (M.pull φ) →
        HasGen M (fun k => φ ≫ ψ k) ![1, -1]) →
      HasGen M (K := Fin 4) ![ψ 0, ψ 1, (1 : A ⟶ A).left ≫ ψ 0, (1 : A ⟶ A).left ≫ ψ 1] ![1, -1, -1, 1] := by
    intro ψ H
    refine GlobalTheory.T.seesaw_rigidified_lineBundle_dense_fibres R A M _ Sg hA hM hample (DVR.linComb_isLB M hM _ _) hd
      ((pull_iff _ _ _).2 (hasGen_of_trivial hM fun U _ h => ?_)) fun p hp => ?_
    · simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        ← Category.assoc, eo]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module
    · obtain ⟨K, _, _, x, P, φ, hx, hp, hw⟩ := hfib p hp
      refine ⟨K, inferInstance, x, _, φ, P.A.hom, hx, hp.1, (pull_iff _ _ _).2 ((H K x P φ hp hw).comb hM
        ((H K x P φ hp hw).pull (1 : P.A ⟶ P.A).left fun _ => rfl) fun U _ h => ?_)⟩
      simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        ← Category.assoc, one_comm hp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
      module
  have hν : ∀ g : A ⟶ A, HasGen M (K := Fin 2) (fun k => (![g, g⁻¹] k).left) ![1, -1] := fun g => by
    have H := see (fun k => (![𝟙 A, (𝟙 A)⁻¹] k).left) fun K _ x P φ hp hw => by
      have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      exact fibre_sym hM P hp hw
    refine (H.pull g.left fun _ => rfl).comb hM (hasGen_of_trivial (K := Fin 0) (φ := ![]) (ε := ![]) hM
      fun U _ h => by simp) fun U _ h => ?_
    simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      ← Over.comp_left, GrpObj.comp_inv, Category.comp_id, MonObj.comp_one, inv_one, Fin.prod_univ_zero]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  have hN : ∀ h : 𝟙_ (Over (Sp R)) ⟶ A, h ^ m = 1 → ∀ g : A ⟶ A, HasGen M (K := Fin 4)
      (fun k => (![g, (toUnit A ≫ h) * g, 1, toUnit A ≫ h] k).left) ![1, -1, -1, 1] := fun h hh g => by
    have H := see ![𝟙 _, transl h] fun K _ x P φ hp hw => (fibre_lifts hG hlaw.mulPull hM P hp hw).1 h hh
    refine H.pull g.left fun k => ?_
    fin_cases k
    · exact Category.comp_id _
    · exact comp_transl g h
    · show g.left ≫ (1 : A ⟶ A).left ≫ 𝟙 _ = (1 : A ⟶ A).left
      rw [Category.comp_id, ← Over.comp_left, MonObj.comp_one]
    · show g.left ≫ (1 : A ⟶ A).left ≫ transl h = (toUnit A ≫ h).left
      rw [← Category.assoc, ← Over.comp_left, MonObj.comp_one, comp_transl, _root_.mul_one]
  obtain ⟨l, hl⟩ := hm
  have half : ∀ c, i (c ^ (l + 1)) * i (c ^ (l + 1)) = i c := fun c => by
    rw [map_pow, ← pow_add, show l + 1 + (l + 1) = m + 1 by omega, pow_succ, htor, _root_.one_mul]
  have lifts : ∀ c, HasGen M (K := Fin 2) ![𝟙 _, transl (i c)] ![1, -1] := fun c => by
    have H := hasGen_sq hM _ hν (hN _ (htor (c ^ (l + 1))))
    rw [← MonObj.comp_mul, half] at H
    refine (hN _ (htor c) (𝟙 A)).comb hM H fun U _ h => ?_
    simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Over.id_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
    module
  refine ⟨fun s => ⟨⊤, trivial, (hν (GrpObj.inv : A ⟶ A)).pull (A.hom ⁻¹ᵁ ⊤).ι fun k => ?_⟩, ?_⟩
  · fin_cases k
    · rfl
    · show _ ≫ ((GrpObj.inv : A ⟶ A)⁻¹).left = _
      rw [← Category.id_comp (GrpObj.inv : A ⟶ A)]
      exact (congrArg (fun q : A ⟶ A => (A.hom ⁻¹ᵁ ⊤).ι ≫ q.left) (inv_inv (𝟙 A))).trans (Category.comp_id _)
  obtain ⟨ν, hν'⟩ : HasGen M (K := Fin 2) ![𝟙 _, ((𝟙 A)⁻¹).left] ![1, -1] :=
    (hν (𝟙 A)).pull (𝟙 _) fun k => (Category.id_comp _).trans (by fin_cases k <;> rfl)
  choose f hf using lifts
  refine exists_cocycle_sq hG hA hM i (i.comp (powMonoidHom (l + 1))) half ν hν' (fun c => f (c ^ (l + 1)))
    (fun c => hf _) fun c c' r y J hJ => ?_
  suffices H : ∀ c c', val (f c) r y J * val (f c') (r ≫ transl (i c)) y J =
      val (f c') r y J * val (f c) (r ≫ transl (i c')) y J from H _ _
  intro c c'
  obtain ⟨κ, hκ⟩ := CommutatorPairing.exists_ratio hM (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, Category.comp_id, ← transl_mul, mul_comm (i c')]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) A.hom η[A].left (Over.w _) (hG _ A hA).2
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hf c) (DVR.pullGen_isGen _ _ _ _ (hf c') (transl (i c))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hf c') (DVR.pullGen_isGen _ _ _ _ (hf c) (transl (i c'))))
  obtain rfl : κ = 1 := unit_eq_one_of_dense hd κ fun p hp => by
    obtain ⟨K, _, _, x, P, φ, ⟨z, hz⟩, hp, hw⟩ := hfib p hp
    refine ⟨_, x, z, hz, ?_⟩
    choose I hI using fun χ : Sp K ⟶ A.left => exists_chart hM (χ z)
    have hI : Good M z I := hI
    have e := hκ _ (η[P.A].left ≫ φ) z I hI
    have e' : (η[P.A].left ≫ φ) ≫ A.hom = x := by
      rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w]; exact Category.id_comp _
    rw [val_mul hI, val_mul hI, val_pull hI, val_pull hI, e', (fibre_lifts hG hlaw.mulPull hM P hp hw).2 _ _
      (htor c) (htor c') _ _ (hf c) (hf c') _ _ z I hI] at e
    exact mul_eq_left.1 e.symm
  have e := hκ _ r y J hJ
  rwa [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, map_one, _root_.mul_one] at e

end GlobalTheory
