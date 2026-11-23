import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM.LamAdd

open GlobalTheory.ProdUnifSq

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ}

def B (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) : ℂ := x ⬝ᵥ Hm.mulVec (star y)

theorem B_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (x x' y : Fin g → ℂ) : B Hm (x + x') y = B Hm x y + B Hm x' y := by
  simp [B, add_dotProduct]

theorem B_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y y' : Fin g → ℂ) : B Hm x (y + y') = B Hm x y + B Hm x y' := by
  simp [B, star_add, Matrix.mulVec_add, dotProduct_add]

theorem B_zero_left (Hm : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) : B Hm 0 y = 0 := by simp [B]

theorem B_add_mat (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) : B (Hm + Hm') x y = B Hm x y + B Hm' x y := by
  simp [B, Matrix.add_mulVec, dotProduct_add]

def cmap (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  (if (0 : Fin 2) ∈ I.down then (halfL g).toLinearMap else 0) + (if (1 : Fin 2) ∈ I.down then (halfR g).toLinearMap else 0)

theorem pt_psum [IsCommMonObj A] (y : 𝟙_ (Over (Sp ℂ)) ⟶ A ⊗ A) (I : Finset (Fin 2)) :
    y ≫ psum A (x2 A) I = (if (0 : Fin 2) ∈ I then y ≫ fst A A else 1) * (if (1 : Fin 2) ∈ I then y ≫ snd A A else 1) := by
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, DiagFrame.padd_eq, DiagFrame.pzero_eq, x2, List.finRange_succ, comp_mul, comp_one]

theorem ex_zero {L : LB A.left} (u : HolUnif A L g) : u.ex 0 = 1 := (u.ker 0).2 (Submodule.zero_mem _)

theorem ex_cmap [IsCommMonObj A] {L L₁ : LB A.left} (u₁ : HolUnif A L₁ g) (u : HolUnif A L g) (hex : u.ex = u₁.ex)
    (I : ULift.{0} (Finset (Fin 2))) (z : Fin (g + g) → ℂ) :
    u.ex (cmap g I z) = (sqUnif A u₁).ex z ≫ psum A (x2 A) I.down := by
  rw [pt_psum]
  change _ = (if (0 : Fin 2) ∈ I.down then lift (u₁.ex (halfL g z)) (u₁.ex (halfR g z)) ≫ fst A A else 1) *
    (if (1 : Fin 2) ∈ I.down then lift (u₁.ex (halfL g z)) (u₁.ex (halfR g z)) ≫ snd A A else 1)
  rw [lift_fst, lift_snd, hex]
  by_cases h0 : (0 : Fin 2) ∈ I.down <;> by_cases h1 : (1 : Fin 2) ∈ I.down <;>
    simp [cmap, h0, h1, u₁.ex_add, ex_zero]

end GlobalTheory.TorusRM.LamAdd

namespace GlobalTheory.TorusRM.LamAdd

open GlobalTheory.ProdUnifSq

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ}

def ε (I : ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - I.down.card)

def lamUnif0 [IsCommMonObj A] {L L₁ : LB A.left} (u₁ : HolUnif A L₁ g) (u : HolUnif A L g) (hex : u.ex = u₁.ex) :
    HolUnif (A ⊗ A) (L.LinComb (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) ε) (g + g) :=
  GlobalTheory.linCombUnif (sqUnif A u₁) u (fun I : ULift.{0} (Finset (Fin 2)) => psum A (x2 A) I.down) (cmap g) ε (ex_cmap u₁ u hex)

def lamUnif [IsCommMonObj A] {L L₁ : LB A.left} (u₁ : HolUnif A L₁ g) (u : HolUnif A L g) (hex : u.ex = u₁.ex) :
    HolUnif (A ⊗ A) (abelian₂ A L) (g + g) := lamUnif0 u₁ u hex

theorem lamUnif_fr [IsCommMonObj A] {L L₁ : LB A.left} (u₁ : HolUnif A L₁ g) (u : HolUnif A L g) (hex : u.ex = u₁.ex)
    (j : (abelian₂ A L).ι) (z : Fin (g + g) → ℂ) :
    (lamUnif u₁ u hex).fr j z = ∏ I, u.fr (j I) (cmap g I z) ^ ε I := rfl

theorem lamUnif_ex [IsCommMonObj A] {L L₁ : LB A.left} (u₁ : HolUnif A L₁ g) (u : HolUnif A L g) (hex : u.ex = u₁.ex) :
    (lamUnif u₁ u hex).ex = (sqUnif A u₁).ex := rfl

theorem lamUnif_Λ [IsCommMonObj A] {L L₁ : LB A.left} (u₁ : HolUnif A L₁ g) (u : HolUnif A L g) (hex : u.ex = u₁.ex) :
    (lamUnif u₁ u hex).Λ = sqLat u₁.Λ := rfl

open Classical in

def ext (Λ : Submodule ℤ (Fin g → ℂ)) (χ : Λ → ℂ) (w : Fin g → ℂ) : ℂ := if h : w ∈ Λ then χ ⟨w, h⟩ else 0

theorem ext_of_mem (Λ : Submodule ℤ (Fin g → ℂ)) (χ : Λ → ℂ) {w : Fin g → ℂ} (h : w ∈ Λ) : ext Λ χ w = χ ⟨w, h⟩ := by
  simp [ext, h]

theorem semichar {L : LB A.left} {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hM : L.IsLB)
    (hF : IsFactorAH u Hm χ) (a b : Fin g → ℂ) (ha : a ∈ u.Λ) (hb : b ∈ u.Λ) :
    ext u.Λ χ (a + b) * Complex.exp (Real.pi / 2 * (B Hm a b + B Hm b a)) =
      ext u.Λ χ a * ext u.Λ χ b * Complex.exp (Real.pi * B Hm a b) := by
  rw [ext_of_mem _ _ (add_mem ha hb), ext_of_mem _ _ ha, ext_of_mem _ _ hb]
  obtain ⟨i, hi⟩ := GlobalTheory.PowUnif.exists_chart hM (u.ex 0).left
  have hexΛ : ∀ w ∈ u.Λ, u.ex w = u.ex 0 := fun w hw => by rw [(u.ker w).2 hw, ex_zero]
  have ca : ⊤ ≤ (u.ex a).left ⁻¹ᵁ L.U i := by rw [hexΛ a ha]; exact hi
  have cab : ⊤ ≤ (u.ex (a + b)).left ⁻¹ᵁ L.U i := by rw [hexΛ _ (add_mem ha hb)]; exact hi
  have e1 := hF.2.2 ⟨a + b, add_mem ha hb⟩ i 0 hi
  have e2 := hF.2.2 ⟨a, ha⟩ i 0 hi
  have e3 := hF.2.2 ⟨b, hb⟩ i a ca
  have hB : ∀ x y : Fin g → ℂ, x ⬝ᵥ Hm.mulVec (star y) = B Hm x y := fun _ _ => rfl
  simp only [hB, B_zero_left, zero_add, mul_zero] at e1 e2 e3
  have hF0 := u.fr_ne i (a + b) cab
  have hexp : B Hm (a + b) (a + b) = B Hm a a + B Hm a b + B Hm b a + B Hm b b := by
    rw [B_add_left, B_add_right, B_add_right]; ring
  rw [hexp] at e1
  rw [e3] at e2
  have E1 : Complex.exp (Real.pi / 2 * (B Hm a a + B Hm a b + B Hm b a + B Hm b b)) =
      Complex.exp (Real.pi / 2 * (B Hm a b + B Hm b a)) * Complex.exp (Real.pi / 2 * (B Hm a a + B Hm b b)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have E2 : Complex.exp (Real.pi / 2 * (B Hm a a + B Hm b b)) =
      Complex.exp (Real.pi / 2 * B Hm a a) * Complex.exp (Real.pi / 2 * B Hm b b) := by
    rw [← Complex.exp_add]; congr 1; ring
  have E3 : Complex.exp (Real.pi * B Hm a b + Real.pi / 2 * B Hm b b) =
      Complex.exp (Real.pi * B Hm a b) * Complex.exp (Real.pi / 2 * B Hm b b) := Complex.exp_add _ _
  rw [E1, E2] at e1
  rw [E3] at e2
  have hK : Complex.exp (Real.pi / 2 * B Hm a a) * Complex.exp (Real.pi / 2 * B Hm b b) * u.fr i (a + b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)) hF0
  refine mul_right_cancel₀ hK ?_
  linear_combination e1.symm.trans e2

theorem ext_zero {L : LB A.left} {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hM : L.IsLB)
    (hF : IsFactorAH u Hm χ) : ext u.Λ χ 0 = 1 := by
  have h := semichar hM hF 0 0 (Submodule.zero_mem _) (Submodule.zero_mem _)
  simp only [B_zero_left, add_zero, mul_zero, Complex.exp_zero, _root_.mul_one] at h
  have hn : ext u.Λ χ 0 ≠ 0 := by
    rw [ext_of_mem _ _ (Submodule.zero_mem _)]
    intro h0
    have := hF.2.1 ⟨0, Submodule.zero_mem _⟩
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hn (h.symm.trans (_root_.mul_one _).symm)

end GlobalTheory.TorusRM.LamAdd

namespace GlobalTheory.TorusRM.LamAdd

open GlobalTheory.ProdUnifSq

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ}

theorem prod_ulift (f : ULift.{0} (Finset (Fin 2)) → ℂ) :
    ∏ I, f I = f ⟨∅⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨{0, 1}⟩ := by
  rw [← Fintype.prod_equiv Equiv.ulift.symm (fun I : Finset (Fin 2) => f ⟨I⟩) f (fun _ => rfl)]
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  ring

theorem charProd {L : LB A.left} {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hM : L.IsLB)
    (hF : IsFactorAH u Hm χ) (l : Fin (g + g) → ℂ) (h1 : halfL g l ∈ u.Λ) (h2 : halfR g l ∈ u.Λ) :
    ∏ I, ext u.Λ χ (cmap g I l) ^ ε I =
      Complex.exp (Real.pi / 2 * (B Hm (halfL g l) (halfR g l) - B Hm (halfR g l) (halfL g l))) := by
  rw [prod_ulift]
  have c0 : cmap g ⟨∅⟩ l = 0 := by simp [cmap]
  have c1 : cmap g ⟨{0}⟩ l = halfL g l := by simp [cmap]
  have c2 : cmap g ⟨{1}⟩ l = halfR g l := by simp [cmap]
  have c3 : cmap g ⟨{0, 1}⟩ l = halfL g l + halfR g l := by simp [cmap]
  have e0 : ε ⟨∅⟩ = 1 := by decide
  have e1 : ε ⟨{0}⟩ = -1 := by decide
  have e2 : ε ⟨{1}⟩ = -1 := by decide
  have e3 : ε ⟨{0, 1}⟩ = 1 := by decide
  rw [c0, c1, c2, c3, e0, e1, e2, e3, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one, ext_zero hM hF, _root_.one_mul]
  set a := halfL g l
  set b := halfR g l
  have S := semichar hM hF a b h1 h2
  have na : ext u.Λ χ a ≠ 0 := by
    rw [ext_of_mem _ _ h1]; intro h0
    have := hF.2.1 ⟨a, h1⟩; rw [h0, norm_zero] at this; exact zero_ne_one this
  have nb : ext u.Λ χ b ≠ 0 := by
    rw [ext_of_mem _ _ h2]; intro h0
    have := hF.2.1 ⟨b, h2⟩; rw [h0, norm_zero] at this; exact zero_ne_one this
  have hx : Complex.exp (Real.pi / 2 * (B Hm a b - B Hm b a)) * Complex.exp (Real.pi / 2 * (B Hm a b + B Hm b a)) =
      Complex.exp (Real.pi * B Hm a b) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hP := Complex.exp_ne_zero (Real.pi / 2 * (B Hm a b + B Hm b a))
  have key : ext u.Λ χ (a + b) = Complex.exp (Real.pi / 2 * (B Hm a b - B Hm b a)) * ext u.Λ χ a * ext u.Λ χ b :=
    mul_right_cancel₀ hP (by linear_combination S - ext u.Λ χ a * ext u.Λ χ b * hx)
  rw [key]
  field_simp

def Q (Hm : Matrix (Fin g) (Fin g) ℂ) (z l : Fin (g + g) → ℂ) : ℂ :=
  Real.pi / 2 * (B Hm (halfL g l) (halfR g l) - B Hm (halfR g l) (halfL g l)) +
    ∑ I, (ε I : ℂ) * (Real.pi * B Hm (cmap g I z) (cmap g I l) + Real.pi / 2 * B Hm (cmap g I l) (cmap g I l))

theorem Q_add (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (z l : Fin (g + g) → ℂ) : Q (Hm + Hm') z l = Q Hm z l + Q Hm' z l := by
  have hs : ∀ I, (ε I : ℂ) * (Real.pi * B (Hm + Hm') (cmap g I z) (cmap g I l) +
      Real.pi / 2 * B (Hm + Hm') (cmap g I l) (cmap g I l)) =
      (ε I : ℂ) * (Real.pi * B Hm (cmap g I z) (cmap g I l) + Real.pi / 2 * B Hm (cmap g I l) (cmap g I l)) +
      (ε I : ℂ) * (Real.pi * B Hm' (cmap g I z) (cmap g I l) + Real.pi / 2 * B Hm' (cmap g I l) (cmap g I l)) :=
    fun I => by simp only [B_add_mat]; ring
  unfold Q
  rw [Finset.sum_congr rfl (fun I _ => hs I), Finset.sum_add_distrib]
  simp only [B_add_mat]
  ring

theorem lam_shift [IsCommMonObj A] {L L₁ : LB A.left} (u₁ : HolUnif A L₁ g) (u : HolUnif A L g) (hex : u.ex = u₁.ex)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hM : L.IsLB) (hF : IsFactorAH u Hm χ) (j : (abelian₂ A L).ι)
    (z l : Fin (g + g) → ℂ) (hl : l ∈ sqLat u₁.Λ)
    (hz : ⊤ ≤ ((lamUnif u₁ u hex).ex z).left ⁻¹ᵁ (abelian₂ A L).U j) :
    (lamUnif u₁ u hex).fr j z = Complex.exp (Q Hm z l) * (lamUnif u₁ u hex).fr j (z + l) := by
  have hΛ : ∀ w, w ∈ u.Λ ↔ w ∈ u₁.Λ := fun w => by rw [← u.ker, ← u₁.ker, hex]
  obtain ⟨hl1, hl2⟩ := (mem_sqLat _ _).1 hl
  have hmem : ∀ I, cmap g I l ∈ u.Λ := fun I => by
    rw [hΛ]
    by_cases h0 : (0 : Fin 2) ∈ I.down <;> by_cases h1 : (1 : Fin 2) ∈ I.down <;>
      simp [cmap, h0, h1, hl1, hl2, add_mem]
  have hz' : ⊤ ≤ ((sqUnif A u₁).ex z).left ⁻¹ᵁ
      LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) j := hz
  have hc : ∀ I, ⊤ ≤ (u.ex (cmap g I z)).left ⁻¹ᵁ L.U (j I) := fun I => by
    have := (GlobalTheory.PowUnif.le_wchart_iff _ L _ j).1 hz' I
    rw [ex_cmap u₁ u hex, Over.comp_left]
    exact this
  have step : ∀ I, u.fr (j I) (cmap g I z) ^ ε I = ext u.Λ χ (cmap g I l) ^ ε I *
      Complex.exp ((ε I : ℂ) * (Real.pi * B Hm (cmap g I z) (cmap g I l) +
        Real.pi / 2 * B Hm (cmap g I l) (cmap g I l))) * u.fr (j I) (cmap g I (z + l)) ^ ε I := fun I => by
    rw [hF.2.2 ⟨_, hmem I⟩ (j I) _ (hc I), map_add, ext_of_mem _ _ (hmem I), mul_zpow, mul_zpow, Complex.exp_int_mul]
    rfl
  rw [lamUnif_fr, lamUnif_fr, Finset.prod_congr rfl (fun I _ => step I), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, ← Complex.exp_sum, charProd hM hF l ((hΛ _).2 hl1) ((hΛ _).2 hl2)]
  unfold Q
  rw [Complex.exp_add]

end GlobalTheory.TorusRM.LamAdd

open GlobalTheory.TorusRM.LamAdd GlobalTheory.ProdUnifSq in

theorem GlobalTheory.TorusRM.lbIso_lam_of_add : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M₁ M₂ M₃ : LB A.left) (u₁ : HolUnif A M₁ g) (u₂ : HolUnif A M₂ g) (u₃ : HolUnif A M₃ g)
      (H₁ H₂ H₃ : Matrix (Fin g) (Fin g) ℂ) (χ₁ : u₁.Λ → ℂ) (χ₂ : u₂.Λ → ℂ) (χ₃ : u₃.Λ → ℂ),
    M₁.IsLB → M₂.IsLB → M₃.IsLB → u₂.ex = u₁.ex → u₃.ex = u₁.ex →
    IsFactorAH u₁ H₁ χ₁ → IsFactorAH u₂ H₂ χ₂ → IsFactorAH u₃ H₃ χ₃ → H₃ = H₁ + H₂ →
    LBIso (abelian₂ A M₂) (LB.div (abelian₂ A M₃) (abelian₂ A M₁)) := by
  intro g A _ hA hP M₁ M₂ M₃ u₁ u₂ u₃ H₁ H₂ H₃ χ₁ χ₂ χ₃ h1 h2 h3 he2 he3 f1 f2 f3 hH
  haveI : IsCommMonObj A := hA.comm
  have hl1 : (abelian₂ A M₁).IsLB := LB.isLB_linComb h1 _ _
  have hl2 : (abelian₂ A M₂).IsLB := LB.isLB_linComb h2 _ _
  have hl3 : (abelian₂ A M₃).IsLB := LB.isLB_linComb h3 _ _
  have hPP : IsProjOver (A ⊗ A).hom := GlobalTheory.ProjSpace.isProjOver_pullback hP hP
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hPP _
    (LB.isLB_div (LB.isLB_div hl3 hl1) hl2) (g + g)
    (GlobalTheory.SameFactor.divUnif (lamUnif u₁ u₂ he2) (GlobalTheory.SameFactor.divUnif (lamUnif u₁ u₁ rfl) (lamUnif u₁ u₃ he3) rfl) rfl)
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro l hl p z hz
  obtain ⟨hz12, hz2⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz
  obtain ⟨hz3, hz1⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz12
  have hexl : (sqUnif A u₁).ex (z + l) = (sqUnif A u₁).ex z := by
    rw [(sqUnif A u₁).ex_add, ((sqUnif A u₁).ker l).2 hl, _root_.mul_one]
  have e1 := lam_shift u₁ u₁ rfl h1 f1 p.1.2 z l hl hz1
  have e2 := lam_shift u₁ u₂ he2 h2 f2 p.2 z l hl hz2
  have e3 := lam_shift u₁ u₃ he3 h3 f3 p.1.1 z l hl hz3
  have n1 := (lamUnif u₁ u₁ rfl).fr_ne p.1.2 (z + l) (by rw [lamUnif_ex, hexl]; exact hz1)
  have n2 := (lamUnif u₁ u₂ he2).fr_ne p.2 (z + l) (by rw [lamUnif_ex, hexl]; exact hz2)
  have n3 := (lamUnif u₁ u₃ he3).fr_ne p.1.1 (z + l) (by rw [lamUnif_ex, hexl]; exact hz3)
  show 1 * ((lamUnif u₁ u₃ he3).fr p.1.1 (z + l) * ((lamUnif u₁ u₁ rfl).fr p.1.2 (z + l))⁻¹ *
      ((lamUnif u₁ u₂ he2).fr p.2 (z + l))⁻¹) =
    1 * ((lamUnif u₁ u₃ he3).fr p.1.1 z * ((lamUnif u₁ u₁ rfl).fr p.1.2 z)⁻¹ * ((lamUnif u₁ u₂ he2).fr p.2 z)⁻¹)
  rw [e1, e2, e3, hH, Q_add, Complex.exp_add]
  have q1 := Complex.exp_ne_zero (Q H₁ z l)
  have q2 := Complex.exp_ne_zero (Q H₂ z l)
  field_simp
