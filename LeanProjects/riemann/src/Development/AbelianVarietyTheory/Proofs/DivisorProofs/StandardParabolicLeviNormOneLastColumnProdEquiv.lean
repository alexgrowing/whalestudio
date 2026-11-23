import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionCommuteOfFixesIsotropicColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFrameCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneModularCharacter
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.LeviLast

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem cT_mul_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    cT s (A * B) = cT s B * cT s A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} : cT s (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

def cTUnit {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (β : GL (Fin k) R) : GL (Fin k) R where
  val := cT s (β⁻¹).1
  inv := cT s β.1
  val_inv := by rw [← cT_mul_sq, Units.mul_inv, cT_one_sq]
  inv_val := by rw [← cT_mul_sq, Units.inv_mul, cT_one_sq]

theorem adMat_mul' {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {a : ℕ} : adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

def blk {k : ℕ} (P : Matrix (Fin k) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (g : GAd σ J) :
    Matrix (Fin k) (Fin k) (AF F ⊗[F] E) :=
  adMat F P * (matHom _ σ J g).1 * adMat F X

theorem blk_of {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) {g : GAd σ J}
    {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J g).1 * adMat F X = adMat F X * B) : blk P X g = B := by
  rw [blk, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← adMat_mul', hPX, adMat_one', Matrix.one_mul]

theorem blk_mul {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) (a : GAd σ J)
    {b : GAd σ J} {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J b).1 * adMat F X = adMat F X * B) :
    blk P X (a * b) = blk P X a * blk P X b := by
  rw [blk_of hPX h, blk, blk, map_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [h]

variable {r : ℕ}

theorem mem_leviOne_last {X Y : Matrix (Fin n) (Fin (r + 1)) E} {g : GAd σ J} :
    g ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ↔
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) ∧
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Y = adMat F Y * B.1) ∧
      (∃ B ∈ ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker,
        (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) := by
  rw [GlobalTheory.LeviSplit.mem_leviOne]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨⟨B, -, h⟩, ⟨B', -, h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
  · rintro ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, Subgroup.mem_top _, h⟩, ⟨B', Subgroup.mem_top _, h'⟩, ⟨B'', h2, h''⟩⟩

set_option maxHeartbeats 1000000 in
open GlobalTheory.UAut GlobalTheory.EisLine in

theorem leviOne_last_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∃ φ : (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) × ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ≃ₜ* GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∀ p, ((φ p : GAd σ J) ∈ ratPts σ J ↔ (p.1 : GAd σ J) ∈ ratPts σ J ∧ (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range) := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ hF
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  obtain ⟨lv, hlv, -, -⟩ := GlobalTheory.SphEis.Inhabitant.existsUnique_isLv hF
  set K := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hK
  set A := GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} with hA
  set T := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hT
  set P : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) Y * J with hP
  set Q : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) X * J with hQ
  have hPX : P * X = 1 := hF.dc
  have hQY : Q * Y = 1 := hF.cd
  have h1X : ∀ g : GAd σ J, (matHom _ σ J g).1 * adMat F X = adMat F X →
      (matHom _ σ J g).1 * adMat F X = adMat F X * (1 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := fun g h => by
    rw [Units.val_one, Matrix.mul_one]; exact h
  have hinv : ∀ a : A, blk P X (a : GAd σ J) * blk P X ((a⁻¹ : A) : GAd σ J) = 1 ∧
      blk P X ((a⁻¹ : A) : GAd σ J) * blk P X (a : GAd σ J) = 1 := by
    intro a
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 a.2
    obtain ⟨⟨B', hB'⟩, -, -⟩ := mem_leviOne_last.1 (a⁻¹).2
    have e1 : blk P X (1 : GAd σ J) = 1 := by
      have := blk_of hPX (h1X 1 (by rw [map_one, Units.val_one, Matrix.one_mul]))
      rw [this, Units.val_one]
    refine ⟨?_, ?_⟩
    · rw [← blk_mul hPX _ hB', ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, e1]
    · rw [← blk_mul hPX _ hB, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, e1]
  let πu : A → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun a =>
    ⟨blk P X (a : GAd σ J), blk P X ((a⁻¹ : A) : GAd σ J), (hinv a).1, (hinv a).2⟩
  have hπK : ∀ a : A, πu a ∈ K := by
    intro a
    obtain ⟨-, -, ⟨B, hBK, hB⟩⟩ := mem_leviOne_last.1 a.2
    have : πu a = B := Units.ext (blk_of hPX hB)
    rw [this]; exact hBK
  let π : A → K := fun a => ⟨πu a, hπK a⟩
  have hlvA : ∀ β : K, lv β ∈ A := fun β =>
    mem_leviOne_last.2 ⟨⟨β, hlv.onC β⟩, ⟨cTUnit (sigR (AF F) σ) (β : GL (Fin (r + 1)) (AF F ⊗[F] E)), hlv.onD β⟩,
      ⟨β, β.2, hlv.onC β⟩⟩
  let mm : K → A := fun β => ⟨lv β, hlvA β⟩
  have hTA : T ≤ A := by
    intro x hx
    obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.1 hx
    have hX' : (matHom _ σ J x).1 * adMat F X = adMat F X := hxX
    have hY' : (matHom _ σ J x).1 * adMat F Y = adMat F Y := hxY
    exact mem_leviOne_last.2 ⟨⟨1, by rw [hX', Units.val_one, Matrix.mul_one]⟩, ⟨1, by rw [hY', Units.val_one, Matrix.mul_one]⟩,
      ⟨1, one_mem _, by rw [hX', Units.val_one, Matrix.mul_one]⟩⟩
  have hTiff : ∀ a : A, (a : GAd σ J) ∈ T ↔ π a = 1 := by
    intro a
    constructor
    · intro hx
      exact Subtype.ext (Units.ext (blk_of hPX (h1X _ (Subgroup.mem_inf.1 hx).1)))
    · intro h1
      have hb : blk P X (a : GAd σ J) = 1 := by
        have := congrArg (fun x : K => (x : GL (Fin (r + 1)) (AF F ⊗[F] E)).1) h1
        exact this
      obtain ⟨⟨B, hB⟩, ⟨B', hB'⟩, -⟩ := mem_leviOne_last.1 a.2
      have hB1 : B.1 = 1 := (blk_of hPX hB).symm.trans hb
      have hfX : (matHom _ σ J (a : GAd σ J)).1 * adMat F X = adMat F X := by rw [hB, hB1, Matrix.mul_one]
      have hfXi : (a : GAd σ J)⁻¹ ∈ GlobalTheory.SphEis.fixG σ J X :=
        inv_mem (show (a : GAd σ J) ∈ GlobalTheory.SphEis.fixG σ J X from hfX)
      have hform := form_mul_of_mul_cols (B := 1)
        (show (matHom _ σ J (a : GAd σ J)⁻¹).1 * adMat F X = adMat F X * 1 by rw [Matrix.mul_one]; exact hfXi)
      rw [inv_inv, cT_one_sq, Matrix.one_mul] at hform
      have e1 : blk Q Y (a : GAd σ J) = B'.1 := blk_of hQY hB'
      rw [blk, hform, ← adMat_mul', hQY, adMat_one'] at e1
      have hfY : (matHom _ σ J (a : GAd σ J)).1 * adMat F Y = adMat F Y := by rw [hB', ← e1, Matrix.mul_one]
      exact Subgroup.mem_inf.2 ⟨hfX, hfY⟩
  have hπc : Continuous π := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun a : A => adMat F P * (matHom _ σ J (a : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp continuous_subtype_val)).matrix_mul continuous_const
    · show Continuous fun a : A => adMat F P * (matHom _ σ J ((a⁻¹ : A) : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp (continuous_subtype_val.comp continuous_inv))).matrix_mul
        continuous_const
  have hmc : Continuous mm := (hlv.cont.comp continuous_subtype_val).subtype_mk _
  have hmm : ∀ a b, mm (a * b) = mm a * mm b := fun a b => Subtype.ext (map_mul lv _ _)
  have hππ : ∀ a b, π (a * b) = π a * π b := by
    intro a b
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 b.2
    exact Subtype.ext (Units.ext (blk_mul hPX (a : GAd σ J) hB))
  have hπm : ∀ β, π (mm β) = β := fun β => Subtype.ext (Units.ext (blk_of hPX (hlv.onC β)))
  have hc : ∀ τ ∈ T, ∀ β, τ * (mm β : GAd σ J) = mm β * τ := fun τ hτ β =>
    (GlobalTheory.SphEis.lv_comm_of_fix_cols F E σ n J (r + 1) m X Y Z J₀ hF lv hlv β τ hτ).symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LeviSplit.exists_prod_equiv A T mm π hmc hπc hmm hππ hπm hTA hTiff hc
  refine ⟨φ, fun p => ?_⟩
  rw [hφ p]
  change (p.1 : GAd σ J) * lv p.2 ∈ ratPts σ J ↔ _
  constructor
  · intro h
    have hp1 : (matHom _ σ J (p.1 : GAd σ J)).1 * adMat F X = adMat F X := (Subgroup.mem_inf.1 p.1.2).1
    have hg : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 * adMat F X =
        adMat F X * (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hp1]
    have hb := blk_of hPX hg
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
    have hM : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    rw [blk, hM, ← adMat_mul', ← adMat_mul'] at hb
    have hrng : (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) :
        GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range := by
      rcases subsingleton_or_nontrivial (AF F ⊗[F] E) with _ | _
      · exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
      · have hd : (P * γ.1 * X).det ≠ 0 := fun h0 => by
          have hu : IsUnit (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1.det :=
            (Matrix.isUnit_iff_isUnit_det _).1 (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).isUnit
          rw [← hb, show (adMat F (P * γ.1 * X)).det = inclR (F := F) (AF F) (P * γ.1 * X).det from
            (RingHom.map_det _ _).symm, h0, map_zero] at hu
          exact not_isUnit_zero hu
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext hb⟩
    obtain ⟨δ, hδ⟩ := hrng
    refine ⟨?_, ⟨δ, hδ⟩⟩
    have h2 : lv p.2 ∈ ratPts σ J := by rw [← hδ]; exact hlv.rat δ
    have := mul_mem h (inv_mem h2)
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨h1, ⟨δ, hδ⟩⟩
    refine mul_mem h1 ?_
    rw [← hδ]; exact hlv.rat δ

end GlobalTheory.SphEis.LeviLast
