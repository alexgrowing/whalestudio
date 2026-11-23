import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TwistedSectionsLocaliseToChartsStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw.Dehom

open SecOn

variable {Y : Scheme.{0}} {M H : LB Y} {V : Y.Opens}

def secUnit (σ : LB.Sec H) (k : H.ι) {O : Y.Opens} (hk : O ≤ H.U k) (h : O ≤ nonzeroLocus σ) :
    Γ(Y, O)ˣ := (isUnit_rs_of_le_nonzeroLocus σ k hk h).unit

theorem val_secUnit (σ : LB.Sec H) (k : H.ι) {O : Y.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus σ) : (secUnit σ k hk h).val = rs Y hk (σ.f k) := rfl

theorem rs_secUnit_zpow (σ : LB.Sec H) (k : H.ι) {O O' : Y.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus σ) (e : O' ≤ O) (t : ℤ) :
    rs Y e (secUnit σ k hk h ^ t).val = (secUnit σ k (e.trans hk) (e.trans h) ^ t).val := by
  have : secUnit σ k (e.trans hk) (e.trans h) =
      Units.map (rs Y e).toMonoidHom (secUnit σ k hk h) :=
    Units.ext (rs_rs _ _ _).symm
  rw [this, ← map_zpow]
  rfl

theorem secUnit_compat (σ : LB.Sec H) (k l : H.ι) {O : Y.Opens} (hH : O ≤ H.U k ⊓ H.U l)
    (h : O ≤ nonzeroLocus σ) :
    secUnit σ k (hH.trans inf_le_left) h =
      res hH (H.g k l) * secUnit σ l (hH.trans inf_le_right) h :=
  Units.ext (GlobalTheory.LB.sec_rel σ k l _ (hH.trans inf_le_right) hH)

variable (M) in

def divPow (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (t : ℤ) :
    SecOn (tw M H t) V →ₗ[Γ(Y, V)] SecOn (tw M H 0) V where
  toFun x := twMk 0
    (fun p k => (secUnit σ k (inf_le_right.trans inf_le_right) (inf_le_left.trans h) ^ (-t)).val *
      twCoord x p k)
    fun p q k l O hp hq hM hH => by
      rw [map_mul, map_mul, rs_secUnit_zpow, rs_secUnit_zpow, twCoord_compat x p q k l hp hq hM hH,
        secUnit_compat σ k l hH, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
        ← Units.val_mul]
      congr 2
      rw [mul_zpow, zpow_zero, _root_.mul_one, zpow_neg (res hH (H.g k l)), mul_mul_mul_comm,
        mul_comm _ (res hM (M.g p q)), mul_mul_mul_comm, inv_mul_cancel, _root_.mul_one]
  map_add' x y := tw_ext fun p k => by simp only [twCoord_twMk, twCoord_add, mul_add]
  map_smul' a x := tw_ext fun p k => mul_left_comm _ _ _

theorem twCoord_divPow (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (t : ℤ) (x : SecOn (tw M H t) V)
    (p : M.ι) (k : H.ι) : twCoord (divPow M σ h t x) p k =
      (secUnit σ k (inf_le_right.trans inf_le_right) (inf_le_left.trans h) ^ (-t)).val *
        twCoord x p k := rfl

theorem divPow_zero (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (x : SecOn (tw M H 0) V) :
    divPow M σ h 0 x = x :=
  tw_ext fun p k => by rw [twCoord_divPow, neg_zero, zpow_zero, Units.val_one, _root_.one_mul]

theorem divPow_injective (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (t : ℤ) :
    Function.Injective (divPow M σ h t) := fun _ _ e =>
  tw_ext fun p k => (Units.isUnit _).mul_left_cancel (congrArg (twCoord · p k) e)

theorem divPow_mulSec (σ : LB.Sec H) (h : V ≤ nonzeroLocus σ) (t : ℤ) (x : SecOn (tw M H t) V) :
    divPow M σ h (t + 1) (mulSec M t σ V x) = divPow M σ h t x :=
  tw_ext fun p k => by
    rw [twCoord_divPow, twCoord_divPow, twCoord_mulSec, ← _root_.mul_assoc,
      ← val_secUnit σ k _ (inf_le_left.trans h), ← Units.val_mul, ← zpow_add_one]
    congr 3
    ring

variable {R : Type} [CommRing R] (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} (s : ι → LB.Sec H)
  (hx : OperatorsCommute (ι := ι) (A := fun t => SecOnR f (tw M H t) V)
    fun i t => SecOnR.mulSec f M t (s i) V)
  (i : ι) (h : V ≤ nonzeroLocus (s i)) (r : ι → Γ(Y, V))
  (hr : ∀ j k, rs Y (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s j).f k) =
    rs Y (inf_le_left : V ⊓ H.U k ≤ V) (r j) * rs Y (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s i).f k))

def dehom : GrSum hx →ₛₗ[MvPolynomial.eval₂Hom (cst f V) r] SecOnR f (tw M H 0) V where
  toFun := GrSum.desc hx fun t => SecOnR.lin f (divPow M (s i) h t)
  map_add' := map_add _
  map_smul' p m := by
    have hX (j : ι) (m : GrSum hx) :
        GrSum.desc hx (fun t => SecOnR.lin f (divPow M (s i) h t))
          ((MvPolynomial.X j : MvPolynomial ι R) • m) =
        r j • GrSum.desc hx (fun t => SecOnR.lin f (divPow M (s i) h t)) m := by
      induction m using DirectSum.Decomposition.inductionOn (GrSum.grading hx) with
      | zero => simp
      | add a b ha hb => rw [smul_add, map_add, map_add, smul_add, ha, hb]
      | @homogeneous n a =>
        obtain ⟨_, a, rfl⟩ := a
        rw [GrSum.X_smul_of, GrSum.desc_of, GrSum.desc_of]
        have e (b : SecOn (tw M H n) V) :
            divPow M (s i) h (n + 1) (mulSec M n (s j) V b) = r j • divPow M (s i) h n b := by
          rw [mulSec_eq_smul (s i) (s j) (r j) (hr j), map_smul, divPow_mulSec]
        exact e a
    induction p using MvPolynomial.induction_on generalizing m with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, algebraMap_smul, map_smul]
      rfl
    | add p q hp hq => rw [add_smul, map_add, map_add, add_smul, hp, hq]
    | mul_X p j hp => rw [mul_smul, hp, hX, map_mul, MvPolynomial.eval₂Hom_X', mul_smul]

theorem dehom_of (t : ℤ) (a : SecOnR f (tw M H t) V) :
    dehom f s hx i h r hr (GrSum.of hx t a) = SecOnR.lin f (divPow M (s i) h t) a :=
  GrSum.desc_of hx _ t a

include h hr in

theorem ratio_self : r i = 1 := by
  refine Y.sheaf.eq_of_locally_eq' (fun k : H.ι => V ⊓ H.U k) V
    (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun k => ?_
  · obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (h hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hx, Y.basicOpen_le _ hl⟩
  · change rs Y inf_le_left (r i) = rs Y inf_le_left 1
    rw [map_one]
    exact (isUnit_rs_of_le_nonzeroLocus (s i) k inf_le_right
      (inf_le_left.trans h)).mul_right_cancel ((hr i k).symm.trans (_root_.one_mul _).symm)

theorem exists_dehom_top
    (hx : ∀ V : Y.Opens, OperatorsCommute (ι := ι) (A := fun t => SecOnR f (tw M H t) V)
      fun i t => SecOnR.mulSec f M t (s i) V)
    (i : ι) (h : V ≤ nonzeroLocus (s i)) (r : ι → Γ(Y, V))
    (hr : ∀ j k, rs Y (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s j).f k) =
      rs Y (inf_le_left : V ⊓ H.U k ≤ V) (r j) *
        rs Y (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s i).f k))
    (h₁ : ∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : V ≤ ⊤) a = 0 →
      ∃ k : ℕ, xProd R {i} ^ k • GrSum.of (hx ⊤) t a = 0)
    (h₂ : ∀ (t : ℤ) (y : SecOnR f (tw M H t) V), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤),
      GrSum.of (hx V) t' (SecOnR.restrict f _ le_top a) = xProd R {i} ^ k • GrSum.of (hx V) t y) :
    ∃ ε : GrSum (hx ⊤) →ₛₗ[MvPolynomial.eval₂Hom (cst f V) r] SecOn (tw M H 0) V,
      Function.Surjective ε ∧
      (∀ n, ∀ y ∈ GrSum.grading (hx ⊤) n, ε y = 0 →
        ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) ∧
      ∀ a : SecOn (tw M H 0) ⊤,
        ε (GrSum.of (hx ⊤) 0 (SecOnR.of f _ ⊤ a)) = SecOn.restrict _ le_top a := by
  have hp : xProd R {i} = MvPolynomial.X i := Finset.prod_singleton _ _
  rw [hp] at h₁ h₂
  have hi := ratio_self s i h r hr
  obtain ⟨ρ, hρ⟩ : ∃ ρ : GrSum (hx ⊤) →ₗ[MvPolynomial ι R] GrSum (hx V), ∀ t a,
      ρ (GrSum.of (hx ⊤) t a) = GrSum.of (hx V) t (SecOnR.restrict f _ le_top a) :=
    ⟨_, GrSum.map_of (hx ⊤) (hx V) (fun t => SecOnR.restrict f (tw M H t) le_top) fun j t a =>
      (SecOn.mulSec_restrict (s j) le_top a).symm⟩
  let ε : GrSum (hx ⊤) →ₛₗ[MvPolynomial.eval₂Hom (cst f V) r] SecOnR f (tw M H 0) V :=
    (dehom f s (hx V) i h r hr).comp ρ
  have hε (t : ℤ) (a : SecOnR f (tw M H t) ⊤) : ε (GrSum.of (hx ⊤) t a) =
      dehom f s (hx V) i h r hr (GrSum.of (hx V) t (SecOnR.restrict f _ le_top a)) := by
    rw [← hρ]
    exact LinearMap.comp_apply _ _ _
  have s₁ : Function.Surjective ε := fun y => by
    obtain ⟨k, t, a, e⟩ := h₂ 0 y
    refine ⟨GrSum.of (hx ⊤) t a, (hε t a).trans ?_⟩
    rw [e, map_smulₛₗ, map_pow, MvPolynomial.eval₂Hom_X', hi, one_pow, one_smul, dehom_of]
    exact divPow_zero (s i) h y
  have s₂ : ∀ n, ∀ y ∈ GrSum.grading (hx ⊤) n, ε y = 0 →
      ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0 := by
    rintro n _ ⟨a, rfl⟩ ha
    rw [hε, dehom_of] at ha
    exact h₁ n a ((map_eq_zero_iff _ (divPow_injective (s i) h n)).1 ha)
  have s₃ (a : SecOnR f (tw M H 0) ⊤) :
      ε (GrSum.of (hx ⊤) 0 a) = SecOnR.restrict f _ le_top a := by
    rw [hε, dehom_of]
    exact divPow_zero (s i) h _
  exact ⟨ε, s₁, s₂, s₃⟩

end GlobalTheory.AbLaw.Dehom

namespace GlobalTheory.AbLaw

open Dehom

theorem exists_dehom_chart : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(Y, nonzeroLocus (s i))), (∀ j k, rs Y (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) = rs Y (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r j) * rs Y (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)) → r i = 1 ∧ ∃ ε : GrSum (hx ⊤) →ₛₗ[MvPolynomial.eval₂Hom (cst f (nonzeroLocus (s i))) r] SecOn (tw M H 0) (nonzeroLocus (s i)), Function.Surjective ε ∧ (∀ n, ∀ y ∈ GrSum.grading (hx ⊤) n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • y = 0) ∧ ∀ a : SecOn (tw M H 0) ⊤, ε (GrSum.of (hx ⊤) 0 (SecOnR.of f _ ⊤ a)) = SecOn.restrict _ le_top a := by
  intro R _ Y f H m s M hH hM hs hx i r hr
  have key : ∀ V : Y.Opens, (⨅ j ∈ ({i} : Finset (Fin (m + 1))), nonzeroLocus (s j)) = V →
      (∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : V ≤ ⊤) a = 0 →
        ∃ k : ℕ, xProd R {i} ^ k • GrSum.of (hx ⊤) t a = 0) ∧
      ∀ (t : ℤ) (y : SecOnR f (tw M H t) V), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤),
        GrSum.of (hx V) t' (SecOnR.restrict f _ le_top a) = xProd R {i} ^ k • GrSum.of (hx V) t y := by
    rintro _ rfl
    exact GlobalTheory.T.twistedSections_localise_to_charts R Y f H m s M hH hM hs hx {i}
  obtain ⟨h₁, h₂⟩ := key (nonzeroLocus (s i)) (by simp)
  exact ⟨ratio_self s i le_rfl r hr, exists_dehom_top f s hx i le_rfl r hr h₁ h₂⟩

end GlobalTheory.AbLaw
