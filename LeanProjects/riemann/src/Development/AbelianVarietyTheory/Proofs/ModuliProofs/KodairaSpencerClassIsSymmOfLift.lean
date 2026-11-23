import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCocyclePeriodicNonvanishingSectionsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem isHolFamily_ex_comp (m : A₀.left ⟶ X) : PowUnif.IsHolFamily fun z => (u.ex z).left ≫ m := PowUnif.IsHolFamily.comp (c := fun z => (u.ex z).left) u.hol m

private theorem top_le_preimage_inf_iff {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (A B : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (A ⊓ B) ↔ ⊤ ≤ x ⁻¹ᵁ A ∧ ⊤ ≤ x ⁻¹ᵁ B := by
  show ⊤ ≤ x ⁻¹ᵁ A ⊓ x ⁻¹ᵁ B ↔ _
  exact le_inf_iff

private theorem valAt'_units_val_ne_zero {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : (Γ(X, W))ˣ) : valAt' y W f.val ≠ 0 := by
  have h1 : valAt' y W (f.val * f.inv) = valAt' y W f.val * valAt' y W f.inv := by
    unfold valAt'
    simp only [dif_pos hW]
    unfold valAt
    simp only [map_mul]
  have h2 : valAt' y W (1 : Γ(X, W)) = 1 := by
    unfold valAt'
    simp only [dif_pos hW]
    unfold valAt
    simp only [map_one]
  intro h0
  rw [f.val_inv, h2, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem exists_frame_on_family (hL₀ : L₀.IsLB) (m : A₀.left ⟶ X) (L : LB X) (hL : L.IsLB)
    (hw : LBIso L₀ (L.pull m)) :
    ∃ a : L.ι → (Fin g → ℂ) → ℂ,
      (∀ i, DifferentiableOn ℂ (a i) (dom u m (L.U i)) ∧ ∀ z ∈ dom u m (L.U i), a i z ≠ 0) ∧
      (∀ i j, ∀ z ∈ dom u m (L.U i) ∩ dom u m (L.U j), a i z = fn u m _ (L.g i j).val z * a j z) ∧
      ∀ i (l : u.Λ) z (c : ℂ), z ∈ dom u m (L.U i) →
        (∀ b, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b → u.fr b z = c * u.fr b (z + l)) → a i z = c * a i (z + l) := by
  obtain ⟨w, hw⟩ := hw

  have hJ : ∀ (i : L.ι) (z : Fin g → ℂ), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull m).U (fun _ => i) := fun i z hi =>
    (PowUnif.le_wchart_iff (u.ex z).left L (fun _ : PUnit => m) (fun _ => i)).2 (fun _ => hi)

  have hM : ∀ (i j : L.ι) (z : Fin g → ℂ), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U j →
      valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => j))
        ((L.pull m).g (fun _ => i) (fun _ => j)).val = fn u m (L.U i ⊓ L.U j) (L.g i j).val z := by
    intro i j z hi hj
    have h := PowUnif.val_linComb_g (u.ex z).left L (fun _ : PUnit => m) (fun _ => i) (fun _ => j)
      ((top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hJ j z hj⟩)
    rw [Fintype.prod_unique] at h
    exact h

  have indep : ∀ (i : L.ι) (z : Fin g → ℂ) (b b' : L₀.ι), ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b' →
      valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b)) (w.s ((fun _ => i), b)).val * u.fr b z =
        valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b')) (w.s ((fun _ => i), b')).val *
          u.fr b' z := by
    intro i z b b' hi hb hb'
    have hbb : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => i), b')) :=
      (top_le_preimage_inf_iff _ _ _).2 ⟨(top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hb⟩, (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hi, hb'⟩⟩
    have h1 := PowUnif.val_gen hw (u.ex z).left ((fun _ => i), b) ((fun _ => i), b') hbb
    have h2 : valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => i), b'))
        (((L.pull m).div L₀).g ((fun _ => i), b) ((fun _ => i), b')).val =
        valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => i))
          ((L.pull m).g (fun _ => i) (fun _ => i)).val *
        (valAt' (u.ex z).left (L₀.U b ⊓ L₀.U b') (L₀.g b b').val)⁻¹ :=
      PowUnif.val_div_g (L.pull m) L₀ (u.ex z).left (fun _ => i) (fun _ => i) b b' hbb
    have h3 : valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => i))
        ((L.pull m).g (fun _ => i) (fun _ => i)).val = 1 := by
      rw [hM i i z hi hi]
      exact PowUnif.val_g_self hL ((u.ex z).left ≫ m) i hi
    have hbb' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L₀.U b ⊓ L₀.U b') := (top_le_preimage_inf_iff _ _ _).2 ⟨hb, hb'⟩
    have h4 := u.fr_compat b b' z hbb'
    have n4 := valAt'_units_val_ne_zero (u.ex z).left hbb' (L₀.g b b')
    rw [h1, h2, h3, h4]
    field_simp

  have ch : ∀ z : Fin g → ℂ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) :=
    fun z => Classical.choose_spec (PowUnif.exists_chart hL₀ (u.ex z).left)
  have hdom : ∀ (i : L.ι) (z : Fin g → ℂ), z ∈ dom u m (L.U i) ↔ ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i :=
    fun _ _ => Iff.rfl
  refine ⟨fun i z => valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i),
      Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)))
      (w.s ((fun _ => i), Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left))).val *
      u.fr (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) z, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · intro z₀ hz₀
      obtain ⟨b₀, hb₀⟩ := PowUnif.exists_chart hL₀ (u.ex z₀).left
      have hO := (u.hol (((L.pull m).div L₀).U ((fun _ => i), b₀)) (w.s ((fun _ => i), b₀)).val)
      have hz : z₀ ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b₀))} :=
        (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z₀ hz₀, hb₀⟩
      have hsub : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b₀))} ⊆
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L₀.U b₀} := fun z hz => ((top_le_preimage_inf_iff _ _ _).1 hz).2
      have hd : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b₀))
          (w.s ((fun _ => i), b₀)).val * u.fr b₀ z) z₀ :=
        (hO.2.mul ((u.fr_hol b₀).mono hsub)).differentiableAt (hO.1.mem_nhds hz)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hO.1.mem_nhds hz] with z hz'
      have hz1 := (top_le_preimage_inf_iff _ _ _).1 hz'
      have hi : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i :=
        (PowUnif.le_wchart_iff (u.ex z).left L (fun _ : PUnit => m) (fun _ => i)).1 hz1.1 PUnit.unit
      exact indep i z _ _ hi (ch z) hz1.2
    · intro z hz
      have hzz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i),
          Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left))) :=
        (top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hz, ch z⟩
      exact mul_ne_zero (valAt'_units_val_ne_zero _ hzz _) (u.fr_ne _ z (ch z))
  · intro i j z hz
    dsimp only
    obtain ⟨hzi, hzj⟩ := hz
    have hzi' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i := hzi
    have hzj' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U j := hzj
    set b := Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left) with hbdef
    have hbb : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => j), b)) :=
      (top_le_preimage_inf_iff _ _ _).2 ⟨(top_le_preimage_inf_iff _ _ _).2 ⟨hJ i z hzi', ch z⟩, (top_le_preimage_inf_iff _ _ _).2 ⟨hJ j z hzj', ch z⟩⟩
    have h1 := PowUnif.val_gen hw (u.ex z).left ((fun _ => i), b) ((fun _ => j), b) hbb
    have h2 : valAt' (u.ex z).left (((L.pull m).div L₀).U ((fun _ => i), b) ⊓
        ((L.pull m).div L₀).U ((fun _ => j), b))
        (((L.pull m).div L₀).g ((fun _ => i), b) ((fun _ => j), b)).val =
        valAt' (u.ex z).left ((L.pull m).U (fun _ => i) ⊓ (L.pull m).U (fun _ => j))
          ((L.pull m).g (fun _ => i) (fun _ => j)).val *
        (valAt' (u.ex z).left (L₀.U b ⊓ L₀.U b) (L₀.g b b).val)⁻¹ :=
      PowUnif.val_div_g (L.pull m) L₀ (u.ex z).left (fun _ => i) (fun _ => j) b b hbb
    rw [h1, h2, hM i j z hzi' hzj', PowUnif.val_g_self hL₀ (u.ex z).left b (ch z), inv_one, _root_.mul_one]
    ring
  · intro i l z c hz hper
    have hx : (u.ex (z + l)).left = (u.ex z).left := by rw [ex_add_lattice]
    have hz' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ L.U i := hz
    have hzl : ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ L.U i := by rw [hx]; exact hz'
    have e1 := indep i (z + l) (Classical.choose (PowUnif.exists_chart hL₀ (u.ex (z + l)).left))
      (Classical.choose (PowUnif.exists_chart hL₀ (u.ex z).left)) hzl (ch (z + l)) (by rw [hx]; exact ch z)
    dsimp only
    rw [e1, hper _ (ch z), hx]
    ring

private theorem valAt'_mul_of_whole_le_preimage {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f f' : Γ(X, W)) : valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt'
  simp only [dif_pos hW]
  unfold valAt
  simp only [map_mul]

private theorem valAt'_one_of_whole_le_preimage {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) :
    valAt' y W 1 = 1 := by
  unfold valAt'
  simp only [dif_pos hW]
  unfold valAt
  simp only [map_one]

private theorem valAt'_unit_ne_zero' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : (Γ(X, W))ˣ) : valAt' y W f.val ≠ 0 := by
  intro h0
  have h1 := valAt'_mul_of_whole_le_preimage y hW f.val f.inv
  rw [f.val_inv, valAt'_one_of_whole_le_preimage y hW, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem PtDer.log_cocycle {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) {L : LB X} (hL : L.IsLB)
    (i j k : L.ι) (hi : ⊤ ≤ y ⁻¹ᵁ L.U i) (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) (hk : ⊤ ≤ y ⁻¹ᵁ L.U k) :
    δ _ (L.g i j).val / valAt' y _ (L.g i j).val + δ _ (L.g j k).val / valAt' y _ (L.g j k).val =
      δ _ (L.g i k).val / valAt' y _ (L.g i k).val := by
  have hT : ⊤ ≤ y ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_inf (le_inf hi hj) hk
  have hc := congrArg Units.val (hL.cocycle i j k)
  rw [Units.val_mul] at hc
  have hv := congrArg (valAt' y _) hc
  have hd := congrArg (δ _) hc
  rw [valAt'_mul_of_whole_le_preimage y hT, PowUnif.val_res y _ _ hT, PowUnif.val_res y _ _ hT,
    PowUnif.val_res y _ _ hT] at hv
  rw [h.mul _ hT, PowUnif.val_res y _ _ hT, PowUnif.val_res y _ _ hT] at hd
  have hd1 : ∀ (a b : L.ι) (hab : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U a ⊓ L.U b),
      δ _ (Semi.res hab (L.g a b)).val = δ (L.U a ⊓ L.U b) (L.g a b).val := fun a b hab =>
    h.res _ _ hab hT _
  rw [hd1, hd1, hd1] at hd
  have na : valAt' y (L.U i ⊓ L.U j) (L.g i j).val ≠ 0 := valAt'_unit_ne_zero' y (W := L.U i ⊓ L.U j) (le_inf hi hj) _
  have nb : valAt' y (L.U j ⊓ L.U k) (L.g j k).val ≠ 0 := valAt'_unit_ne_zero' y (W := L.U j ⊓ L.U k) (le_inf hj hk) _
  rw [← hv, ← hd]
  field_simp
  ring

private theorem top_le_preimage_inf_iff_and {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (A B : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (A ⊓ B) ↔ ⊤ ≤ x ⁻¹ᵁ A ∧ ⊤ ≤ x ⁻¹ᵁ B := by
  show ⊤ ≤ x ⁻¹ᵁ A ⊓ x ⁻¹ᵁ B ↔ _
  exact le_inf_iff

private theorem valAt'_val_unit_ne_zero {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W : X.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : (Γ(X, W))ˣ) : valAt' y W f.val ≠ 0 := by
  have h1 : valAt' y W (f.val * f.inv) = valAt' y W f.val * valAt' y W f.inv := by
    unfold valAt'
    simp only [dif_pos hW]
    unfold valAt
    simp only [map_mul]
  have h2 : valAt' y W (1 : Γ(X, W)) = 1 := by
    unfold valAt'
    simp only [dif_pos hW]
    unfold valAt
    simp only [map_one]
  intro h0
  rw [f.val_inv, h2, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem isSymm_of_lift : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ L : LB X, L.IsLB → LBIso P₀.L (L.pull m) → IsSymm Hm Θ := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ s hks L hL hw
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_frame_on_family u P₀.isLB m L hL hw
  have hhol := isHolFamily_ex_comp u m
  have hopen : ∀ W : X.Opens, IsOpen (dom u m W) := fun W => (hhol W 0).1
  have hfn : ∀ (W : X.Opens) (f : Γ(X, W)), DifferentiableOn ℂ (fn u m W f) (dom u m W) :=
    fun W f => (hhol W f).2
  have hdom : ∀ A B : X.Opens, dom u m (A ⊓ B) = dom u m A ∩ dom u m B := by
    intro A B
    ext z
    exact top_le_preimage_inf_iff_and _ _ _
  have hfnper : ∀ (W : X.Opens) (f : Γ(X, W)) (z : Fin P₀.g → ℂ) (l : u.Λ),
      fn u m W f (z + l) = fn u m W f z := by
    intro W f z l
    unfold fn
    rw [ex_add_lattice]
  have key := _root_.GlobalTheory.T.theta_cocycle_periodic_nonvanishing_sections P₀.g u.Λ u.discrete u.full Hm Θ L.ι (fun i => dom u m (L.U i)) a
    (fun i j z => s z (L.U i ⊓ L.U j) (L.g i j).val / fn u m (L.U i ⊓ L.U j) (L.g i j).val z)
    (fun l => χ l * Complex.exp (↑Real.pi / 2 * ((l : Fin P₀.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P₀.g → ℂ)))))
    (fun i => hopen _)
    (by
      intro i l z hz
      show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ L.U i
      rw [ex_add_lattice]
      exact hz)
    (fun z => PowUnif.exists_chart hL ((u.ex z).left ≫ m))
    ha1
    (by
      intro i l z hz
      refine ha3 i l z _ hz fun b hb => ?_
      rw [hG.ah.2.2.2 l b z hb, Complex.exp_add]
      ring)
    (by
      intro i j
      rw [← hdom]
      have h1 : DifferentiableOn ℂ (fun z => s z (L.U i ⊓ L.U j) (L.g i j).val) (dom u m (L.U i ⊓ L.U j)) :=
        hks.hol _ _
      have h2 : DifferentiableOn ℂ (fn u m (L.U i ⊓ L.U j) (L.g i j).val) (dom u m (L.U i ⊓ L.U j)) := hfn _ _
      have h3 : ∀ z ∈ dom u m (L.U i ⊓ L.U j), fn u m (L.U i ⊓ L.U j) (L.g i j).val z ≠ 0 :=
        fun z hz => valAt'_val_unit_ne_zero _ hz _
      refine (h1.mul (h2.inv h3)).congr fun z _ => ?_
      exact div_eq_mul_inv _ _)
    (by
      intro i j k z hz
      obtain ⟨⟨hi, hj⟩, hk⟩ := hz
      exact PtDer.log_cocycle (hks.der z) hL i j k hi hj hk)
    (by
      intro i j l z hz
      have hzW : z ∈ dom u m (L.U i ⊓ L.U j) := by
        rw [hdom]
        exact hz
      have hs := hks.per l (L.U i ⊓ L.U j) (L.g i j).val z hzW
      show s (z + l) (L.U i ⊓ L.U j) (L.g i j).val / fn u m (L.U i ⊓ L.U j) (L.g i j).val (z + l) = _
      rw [hs, hfnper]
      have hdf : DifferentiableAt ℂ (fn u m (L.U i ⊓ L.U j) (L.g i j).val) z :=
        (hfn _ _).differentiableAt ((hopen _).mem_nhds hzW)
      have hda : DifferentiableAt ℂ (a j) z := (ha1 j).1.differentiableAt ((hopen _).mem_nhds hz.2)
      have hEq : fderiv ℂ (a i) z = fderiv ℂ (fun y => fn u m (L.U i ⊓ L.U j) (L.g i j).val y * a j y) z := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [(hopen _).mem_nhds hzW] with y hy
        rw [hdom] at hy
        exact ha2 i j y hy
      have nf : fn u m (L.U i ⊓ L.U j) (L.g i j).val z ≠ 0 := valAt'_val_unit_ne_zero _ hzW _
      have na : a j z ≠ 0 := (ha1 j).2 z hz.2
      rw [hEq, fderiv_fun_mul hdf hda, ha2 i j z hz]
      simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring)
  intro z w
  unfold hermForm
  exact key z w

end GlobalTheory.KS
