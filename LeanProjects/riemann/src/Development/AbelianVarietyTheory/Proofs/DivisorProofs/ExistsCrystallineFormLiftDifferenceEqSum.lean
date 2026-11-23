import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS.FormLocal

open KaehlerDifferential
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

section Alg

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal C}

theorem mul_eq_zero_of_sq (hJ : J ^ 2 = 0) {a b : C} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

def diffDer (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J) :
    letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
    Derivation R B C :=
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  { toFun := fun b ↦ ρ₁ b - ρ₂ b
    map_add' := fun a b ↦ by simp only [map_add]; ring
    map_smul' := fun r b ↦ by
      simp only [map_smul, RingHom.id_apply, smul_sub]
    map_one_eq_zero' := by simp
    leibniz' := fun a b ↦ by
      change ρ₁ (a * b) - ρ₂ (a * b) = ρ₂ a * (ρ₁ b - ρ₂ b) + ρ₂ b * (ρ₁ a - ρ₂ a)
      have h0 := mul_eq_zero_of_sq hJ (hd a) (hd b)
      simp only [map_mul]
      linear_combination h0 }

def diffLam (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J) : Ω[B⁄R] →+ C :=
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  ((diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential).toAddMonoidHom

variable (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J)

theorem diffLam_smul (b : B) (m : Ω[B⁄R]) :
    diffLam hJ ρ₁ ρ₂ hd (b • m) = ρ₂ b * diffLam hJ ρ₁ ρ₂ hd m := by
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact ((diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential).map_smul b m

theorem diffLam_D (t : B) : diffLam hJ ρ₁ ρ₂ hd (D R B t) = ρ₁ t - ρ₂ t := by
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact (diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential_comp_D t

theorem diffLam_mem (m : Ω[B⁄R]) : diffLam hJ ρ₁ ρ₂ hd m ∈ J := by
  induction m using GlobalTheory.CechDR.ind1 with
  | h b c => rw [diffLam_smul, diffLam_D]; exact J.mul_mem_left _ (hd c)
  | h0 => rw [map_zero]; exact J.zero_mem
  | ha x y hx hy => rw [map_add]; exact J.add_mem hx hy

end Alg

section Alg2

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal C} (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J)

def diagLift : TrivSqZeroExt B Ω[B⁄R] →ₐ[R] C where
  toFun c := ρ₂ c.fst + diffLam hJ ρ₁ ρ₂ hd c.snd
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]; ring
  map_mul' a b := by
    have h0 := mul_eq_zero_of_sq hJ (diffLam_mem hJ ρ₁ ρ₂ hd a.snd) (diffLam_mem hJ ρ₁ ρ₂ hd b.snd)
    have e : (MulOpposite.op b.fst • a.snd : Ω[B⁄R]) = b.fst • a.snd := rfl
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, map_mul, map_add, e, diffLam_smul]
    linear_combination -h0
  commutes' r := by
    simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem diagLift_apply (c : TrivSqZeroExt B Ω[B⁄R]) :
    diagLift hJ ρ₁ ρ₂ hd c = ρ₂ c.fst + diffLam hJ ρ₁ ρ₂ hd c.snd := rfl

theorem diagLift_inl (b : B) : diagLift hJ ρ₁ ρ₂ hd (TrivSqZeroExt.inl b) = ρ₂ b := by
  simp [diagLift_apply]

theorem diagLift_diagSec (b : B) : diagLift hJ ρ₁ ρ₂ hd (diagSec R B b) = ρ₁ b := by
  rw [diagLift_apply, fst_derSec, snd_derSec, diffLam_D]; ring

theorem diagLift_sub_mem (c : TrivSqZeroExt B Ω[B⁄R]) : diagLift hJ ρ₁ ρ₂ hd c - ρ₂ c.fst ∈ J := by
  rw [diagLift_apply, add_sub_cancel_left]; exact diffLam_mem hJ ρ₁ ρ₂ hd _

end Alg2

section Repr

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem exists_sum_smul_D (m : Ω[B⁄R]) : ∃ (n : ℕ) (r t : Fin n → B), m = ∑ k, r k • D R B (t k) := by
  induction m using GlobalTheory.CechDR.ind1 with
  | h b c => exact ⟨1, fun _ ↦ b, fun _ ↦ c, by simp⟩
  | h0 => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | ha x y hx hy =>
    obtain ⟨n, r, t, rfl⟩ := hx
    obtain ⟨n', r', t', rfl⟩ := hy
    refine ⟨n + n', Fin.append r r', Fin.append t t', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end Repr

section Geo

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {U : X.Opens}

def valHom {C : Type} [CommRing C] [Algebra R C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (hs : y ≫ s = spMap (algebraMap R C)) : CechDR.Sec s U →ₐ[R] C :=
  { (GlobalTheory.Points.valMap y U hy).hom with
    commutes' := fun r ↦ by
      have e1 := GlobalTheory.Points.valR_appLE y s (U := ⊤) (V := U) le_top hy
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [hs, GlobalTheory.Points.valR_specMap, GlobalTheory.Points.valR_eq y U hy] at e1
      exact e1 }

theorem valR_eq_valHom {C : Type} [CommRing C] [Algebra R C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (hs : y ≫ s = spMap (algebraMap R C)) (f : Γ(X, U)) : valR y U f = valHom y hy hs f :=
  GlobalTheory.Points.valR_eq y U hy f

theorem valHom_pt {C : Type} [CommRing C] [Algebra R C] (hU : IsAffineOpen U) (y : Sp C ⟶ X)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (hs : y ≫ s = spMap (algebraMap R C)) :
    spMap (valHom y hy hs : CechDR.Sec s U →+* C) ≫ CechDR.affPt s ⟨U, hU⟩ = y :=
  GlobalTheory.Points.specMap_valMap_fromSpec hU y hy

theorem ringHom_ext_affPt {C : Type} [CommRing C] (hU : IsAffineOpen U) {a b : CechDR.Sec s U →+* C}
    (h : spMap a ≫ CechDR.affPt s ⟨U, hU⟩ = spMap b ≫ CechDR.affPt s ⟨U, hU⟩) : a = b := by
  have h1 : spMap a = spMap b := (cancel_mono hU.fromSpec).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

def diagPr (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    (diagExt R B).thick x hx ⟶ Thick.triv B x hx where
  φ := (diagExt R B).π
  φ₀ := RingHom.id B
  comm _ := rfl
  dp := (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ha,
    fun n hn a ha ↦ by
      have ha' : ((diagExt R B).π : TrivSqZeroExt B Ω[B⁄R] →+* B) a = 0 := ha
      have hm := (divided₂ (diagExt R B).sq).dpow_mem hn ha
      have hm' : ((diagExt R B).π : TrivSqZeroExt B Ω[B⁄R] →+* B) ((divided₂ (diagExt R B).sq).dpow n a) = 0 := hm
      rw [hm', ha', DividedPowers.dpow_eval_zero _ hn]⟩
  pt := by rw [spMap_id, Category.id_comp]

theorem fst_ev_secHom (ω : Form s) (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) (j : B →ₐ[R] TrivSqZeroExt B Ω[B⁄R])
    (hj : ∀ b, (j b).fst = b) :
    (ev ω.1 ((diagExt R B).secHom hx j hj)).fst = - ev ω.1 (diagPr B x hx) := by
  have h0 : ev ω.1 ((diagExt R B).secHom hx j hj ≫ diagPr B x hx) = 0 := ω.2 _ rfl rfl
  rw [ev_comp] at h0
  exact eq_neg_of_add_eq_zero_left h0

end Geo

theorem ev_idLift_sub_eq_sum : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ω : Form s) (U : X.Opens), IsAffineOpen U → ∃ (n : ℕ) (r t : Fin n → Γ(X, U)), ∀ (T : Thick (dp0 R) s) (hJ : T.J ^ 2 = 0), T.δ = divided₂ hJ → ∀ (y₁ y₂ : Sp T.B ⟶ X) (h₁ : y₁ ≫ s = spMap (algebraMap R T.B)) (h₂ : y₂ ≫ s = spMap (algebraMap R T.B)) (e₁ : spMap T.π ≫ y₁ = T.x) (e₂ : spMap T.π ≫ y₂ = T.x), ⊤ ≤ y₁ ⁻¹ᵁ U → ⊤ ≤ y₂ ⁻¹ᵁ U → ev ω.1 (idLift T y₂ h₂ e₂) - ev ω.1 (idLift T y₁ h₁ e₁) = ∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
  intro R _ X s ω U hU
  have hx := CechDR.affPt_w s ⟨U, hU⟩
  obtain ⟨n, r, t, hΩ⟩ := exists_sum_smul_D (connForm ω.1 (CechDR.affPt s ⟨U, hU⟩) hx)
  refine ⟨n, r, t, ?_⟩
  intro T hJ hδ y₁ y₂ h₁ h₂ e₁ e₂ hy₁ hy₂
  have p₁ := valHom_pt hU y₁ hy₁ h₁
  have p₂ := valHom_pt hU y₂ hy₂ h₂
  have hπ : T.π.comp (valHom y₁ hy₁ h₁ : CechDR.Sec s U →+* T.B) = T.π.comp (valHom y₂ hy₂ h₂ : CechDR.Sec s U →+* T.B) :=
    ringHom_ext_affPt hU (by rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, p₁, p₂, e₁, e₂])
  have hd : ∀ b, valHom y₁ hy₁ h₁ b - valHom y₂ hy₂ h₂ b ∈ T.J := fun b ↦
    (T.ker _).1 (by rw [map_sub, sub_eq_zero]; exact RingHom.congr_fun hπ b)
  let Φ : (diagExt R (CechDR.Sec s U)).thick (CechDR.affPt s ⟨U, hU⟩) hx ⟶ T :=
    { φ := diagLift hJ _ _ hd
      φ₀ := T.π.comp (valHom y₂ hy₂ h₂ : CechDR.Sec s U →+* T.B)
      comm := fun c ↦ by
        have h0 := (T.ker _).2 (diagLift_sub_mem hJ _ _ hd c)
        rw [map_sub, sub_eq_zero] at h0
        exact h0.symm
      dp := by
        have key : DividedPowers.IsDPMorphism (divided₂ (diagExt R (CechDR.Sec s U)).sq) (divided₂ hJ)
            (diagLift hJ _ _ hd : TrivSqZeroExt (CechDR.Sec s U) Ω[(CechDR.Sec s U)⁄R] →+* T.B) :=
          isDPMorphism_sqDP _ hJ _ fun (a : TrivSqZeroExt (CechDR.Sec s U) Ω[(CechDR.Sec s U)⁄R]) ha ↦ by
            have ha' : a.fst = 0 := ha
            have h0 := diagLift_sub_mem hJ _ _ hd a
            rwa [ha', map_zero, sub_zero] at h0
        rw [hδ]
        exact key
      pt := by rw [Cris.spMap_comp, Category.assoc, p₂, e₂] }
  let a₁ : Thick.triv (CechDR.Sec s U) (CechDR.affPt s ⟨U, hU⟩) hx ⟶ Thick.triv T.B y₁ h₁ :=
    Thick.trivHom (valHom y₁ hy₁ h₁) p₁
  let a₂ : Thick.triv (CechDR.Sec s U) (CechDR.affPt s ⟨U, hU⟩) hx ⟶ Thick.triv T.B y₂ h₂ :=
    Thick.trivHom (valHom y₂ hy₂ h₂) p₂
  have k₂ := Form.ev_sq ω a₂ (idLift T y₂ h₂ e₂)
    ((diagExt R (CechDR.Sec s U)).secHom hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl) Φ rfl rfl
    fun c ↦ (diagLift_inl hJ _ _ hd c).symm
  have k₁ := Form.ev_sq ω a₁ (idLift T y₁ h₁ e₁)
    ((diagExt R (CechDR.Sec s U)).secHom hx (diagSec R (CechDR.Sec s U)) (fst_derSec _)) Φ rfl rfl
    fun c ↦ (diagLift_diagSec hJ _ _ hd c).symm
  have f₁ := fst_ev_secHom ω (CechDR.Sec s U) _ hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl
  have f₂ := fst_ev_secHom ω (CechDR.Sec s U) _ hx (diagSec R (CechDR.Sec s U)) (fst_derSec _)
  rw [k₁, k₂, add_sub_add_right_eq_sub, ← map_sub]
  change diagLift hJ _ _ hd _ = _
  rw [diagLift_apply, TrivSqZeroExt.fst_sub, f₁, f₂, sub_self, map_zero, zero_add]
  have hc : (ev ω.1 ((diagExt R (CechDR.Sec s U)).secHom hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl) -
      ev ω.1 ((diagExt R (CechDR.Sec s U)).secHom hx (diagSec R (CechDR.Sec s U)) (fst_derSec _))).snd =
      connForm ω.1 (CechDR.affPt s ⟨U, hU⟩) hx := rfl
  rw [hc, hΩ, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [diffLam_smul, diffLam_D]
  exact (congrArg₂ (fun a b ↦ a * b) (valR_eq_valHom y₂ hy₂ h₂ (r k))
    (congrArg₂ (fun a b ↦ a - b) (valR_eq_valHom y₁ hy₁ h₁ (t k)) (valR_eq_valHom y₂ hy₂ h₂ (t k)))).symm

end GlobalTheory.CechKS.FormLocal
