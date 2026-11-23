import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcB

open GlobalTheory.CompanionTheory.FourierN (mat_injective continuous_halfTr blk4_map_alt exists_compact_cover)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem blockMatrix_multiply {R : Type} [CommRing R] (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn a b c d) (bl hn a' b' c' d') =
      bl hn (a ⬝ a' + b ⬝ c') (a ⬝ b' + b ⬝ d') (c ⬝ a' + d ⬝ c') (c ⬝ b' + d ⬝ d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_add' {R : Type} [CommRing R] (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem blockMatrix_one {R : Type} [CommRing R] (hn : ρ + p = n) :
    bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 1 = 1 := by
  simp only [bl]
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_map₂ {R S : Type} (f : R → S) (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (b : Matrix (Fin ρ) (Fin p) R)
    (c : Matrix (Fin p) (Fin ρ) R) (d : Matrix (Fin p) (Fin p) R) :
    (bl hn a b c d).map f = bl hn (a.map f) (b.map f) (c.map f) (d.map f) := by
  simp only [bl]
  rw [← Matrix.fromBlocks_map]
  rfl

theorem mat_mul' (a b : G D n) : mat (a * b) = HMul.hMul (mat a) (mat b) := rfl

section Gen
variable {R : Type} [CommRing R] {k : ℕ}

theorem block_unipotent_mul (B B' : Matrix (Fin k) (Fin k) R) :
    HMul.hMul (blk4 1 B 0 1) (blk4 1 B' 0 1) = blk4 1 (B + B') 0 1 := by
  rw [submatrix_fromBlocks_mul]
  congr 1
  · simp
  · simp [add_comm]
  · simp
  · simp

theorem block_diagonal_mul (A A' B B' : Matrix (Fin k) (Fin k) R) :
    HMul.hMul (blk4 A 0 0 A') (blk4 B 0 0 B') = blk4 (A ⬝ B) 0 0 (A' ⬝ B') := by
  rw [submatrix_fromBlocks_mul]
  congr 1 <;> simp

theorem block_unipotent_mul_diagonal (B A A' : Matrix (Fin k) (Fin k) R) :
    HMul.hMul (blk4 1 B 0 1) (blk4 A 0 0 A') = blk4 A (B ⬝ A') 0 A' := by
  rw [submatrix_fromBlocks_mul]
  congr 1 <;> simp

theorem block_diagonal_mul_unipotent (B A A' : Matrix (Fin k) (Fin k) R) :
    HMul.hMul (blk4 A 0 0 A') (blk4 1 B 0 1) = blk4 A (A ⬝ B) 0 A' := by
  rw [submatrix_fromBlocks_mul]
  congr 1 <;> simp

theorem blockMatrix_upper (hn : ρ + p = n) (y y' : Matrix (Fin ρ) (Fin p) R) :
    HMul.hMul (bl hn 1 y 0 1) (bl hn 1 y' 0 1) = bl hn 1 (y + y') 0 1 := by
  rw [blockMatrix_multiply]
  congr 1
  · simp
  · simp [add_comm]
  · simp
  · simp

theorem lowerUnipotent_mul (hn : ρ + p = n) (c c' : Matrix (Fin p) (Fin ρ) R) :
    HMul.hMul (bl hn 1 0 c 1) (bl hn 1 0 c' 1) = bl hn 1 0 (c + c') 1 := by
  rw [blockMatrix_multiply]
  congr 1
  · simp
  · simp
  · simp [add_comm]
  · simp

theorem blockMatrix_twist (hn : ρ + p = n) (z z' : Matrix (Fin ρ) (Fin ρ) R) (x η : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (h : z' = z + x ⬝ c' - η ⬝ c) :
    HMul.hMul (bl hn z x c 0) (bl hn 1 0 c' 1) = HMul.hMul (bl hn 1 η 0 1) (bl hn z' x c 0) := by
  rw [blockMatrix_multiply, blockMatrix_multiply]
  congr 1
  · subst h; simp
  · simp
  · simp
  · simp

end Gen

theorem nzx_mul (M : Maps D hn) (z z' : hermA D ρ) (x x' : Mx D ρ p) :
    M.nzx z x * M.nzx z' x' = M.nzx (z + z') (x + x') := by
  apply mat_injective
  rw [mat_mul', M.nzx_mat, M.nzx_mat, M.nzx_mat, block_unipotent_mul, blockMatrix_add', adj_add, add_zero]
  rfl

theorem nzx_zero (M : Maps D hn) : M.nzx 0 0 = 1 := by
  have h := nzx_mul M 0 0 0 0
  simp only [add_zero] at h
  exact mul_eq_left.1 h

theorem sh_mul (M : Maps D hn) (y y' : Mx D ρ p) : M.sh y * M.sh y' = M.sh (y + y') := by
  apply mat_injective
  rw [mat_mul', M.sh_mat, M.sh_mat, M.sh_mat, block_diagonal_mul, blockMatrix_upper, lowerUnipotent_mul, adj_add, neg_add]

theorem sh_zero (M : Maps D hn) : M.sh 0 = 1 := by
  have h := sh_mul M 0 0
  simp only [add_zero] at h
  exact mul_eq_left.1 h

def tw (z : hermA D ρ) (x η : Mx D ρ p) : hermA D ρ :=
  ⟨z.1 - x ⬝ adj η - η ⬝ adj x, by
    have hz : adj z.1 = z.1 := z.2
    have hs : ∀ a b : Mx D ρ ρ, adj (a - b) = adj a - adj b := fun a b => by
      have := adj_add (a - b) b
      rw [sub_add_cancel] at this
      rw [this, add_sub_cancel_right]
    show adj (z.1 - x ⬝ adj η - η ⬝ adj x) = z.1 - x ⬝ adj η - η ⬝ adj x
    rw [hs, hs, hz, adj_mul, adj_mul, adj_adj, adj_adj]
    abel⟩

theorem nzx_sh (M : Maps D hn) (z : hermA D ρ) (x η : Mx D ρ p) :
    M.nzx z x * M.sh η = M.sh η * M.nzx (tw z x η) x := by
  apply mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.nzx_mat, M.sh_mat, block_unipotent_mul_diagonal, block_diagonal_mul_unipotent]
  congr 1
  refine blockMatrix_twist hn _ _ _ _ _ _ ?_
  show z.1 - x ⬝ adj η - η ⬝ adj x = z.1 + x ⬝ (-adj η) - η ⬝ adj x
  rw [Matrix.mul_neg, sub_eq_add_neg z.1]

end GlobalTheory.CompanionTheory.PcB

namespace GlobalTheory.CompanionTheory.PcB

open GlobalTheory.CompanionTheory.FourierN (mat_injective continuous_halfTr blk4_map_alt exists_compact_cover)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem mem_GF (g : G D n) (X Y : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (hX : mat g = rat X)
    (hY : mat g⁻¹ = rat Y) : g ∈ GF D n := by
  have e1 : mat g * mat g⁻¹ = 1 := (mat_mul' g g⁻¹).symm.trans (by rw [mul_inv_cancel]; rfl)
  have e2 : mat g⁻¹ * mat g = 1 := (mat_mul' g⁻¹ g).symm.trans (by rw [inv_mul_cancel]; rfl)
  have r1 : rat (1 : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) = (1 : Mx D (n + n) (n + n)) :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let x : GL (Fin (n + n)) D.host.E := ⟨X, Y,
    rat_injective (D := D) (by rw [rat_mul, r1, ← hX, ← hY]; exact e1),
    rat_injective (D := D) (by rw [rat_mul, r1, ← hX, ← hY]; exact e2)⟩
  have hm : x.1.map (incA D) = mat g := hX.symm
  refine ⟨x, ?_, Units.ext hm⟩
  apply rat_injective (D := D)
  have h2 : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [← hm] at h2
  erw [rat_mul, rat_mul]
  exact h2

theorem rational_map_block_matrix {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) D.host.E) :
    rat (D := D) (blk4 a b c d) = blk4 (rat a) (rat b) (rat c) (rat d) := blk4_map_alt _ _ _ _ _

theorem rat_bl' (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) D.host.E) (b : Matrix (Fin ρ) (Fin p) D.host.E)
    (c : Matrix (Fin p) (Fin ρ) D.host.E) (d : Matrix (Fin p) (Fin p) D.host.E) :
    rat (D := D) (bl hn a b c d) = bl hn (rat a) (rat b) (rat c) (rat d) := blockMatrix_map₂ _ _ _ _ _ _

theorem rat_one' {k : ℕ} : rat (D := D) (1 : Matrix (Fin k) (Fin k) D.host.E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem rat_zero' {k l : ℕ} : rat (D := D) (0 : Matrix (Fin k) (Fin l) D.host.E) = 0 :=
  Matrix.map_zero _ (map_zero _)

theorem rat_neg' {k l : ℕ} (a : Matrix (Fin k) (Fin l) D.host.E) : rat (D := D) (-a) = -rat a := by
  ext i j
  exact map_neg (incA D) _

theorem nzx_mat_rat (M : Maps D hn) (z : hermA D ρ) (Z : Matrix (Fin ρ) (Fin ρ) D.host.E)
    (X : Matrix (Fin ρ) (Fin p) D.host.E) (hZ : rat Z = z.1) :
    mat (M.nzx z (rat X)) = rat (blk4 1 (bl hn Z X Xᴴ 0) 0 1) := by
  rw [M.nzx_mat, rational_map_block_matrix, rat_bl', rat_one', rat_zero', rat_zero', rat_conjTranspose, hZ]

theorem sh_mat_rat (M : Maps D hn) (Y : Matrix (Fin ρ) (Fin p) D.host.E) :
    mat (M.sh (rat Y)) = rat (blk4 (bl hn 1 Y 0 1) 0 0 (bl hn 1 0 (-Yᴴ) 1)) := by
  simp only [M.sh_mat, rational_map_block_matrix, rat_bl', rat_one', rat_zero', rat_neg', rat_conjTranspose]

theorem nzx_rat (M : Maps D hn) (z : hermA D ρ) (hz : z ∈ ratHerm D ρ) (X : Matrix (Fin ρ) (Fin p) D.host.E) :
    M.nzx z (rat X) ∈ GF D n := by
  obtain ⟨Z, hZ⟩ := hz
  have hZ' : rat Z = z.1 := hZ
  have hinv : (M.nzx z (rat X))⁻¹ = M.nzx (-z) (rat (-X)) := by
    rw [inv_eq_iff_mul_eq_one, nzx_mul, rat_neg', add_neg_cancel, add_neg_cancel, nzx_zero]
  refine mem_GF _ _ (blk4 1 (bl hn (-Z) (-X) (-X)ᴴ 0) 0 1) (nzx_mat_rat M z Z X hZ') ?_
  rw [hinv]
  exact nzx_mat_rat M (-z) (-Z) (-X) (by rw [rat_neg', hZ']; rfl)

theorem sh_rat (M : Maps D hn) (X : Matrix (Fin ρ) (Fin p) D.host.E) : M.sh (rat X) ∈ GF D n := by
  have hinv : (M.sh (rat X))⁻¹ = M.sh (rat (-X)) := by
    rw [inv_eq_iff_mul_eq_one, sh_mul, rat_neg', add_neg_cancel, sh_zero]
  refine mem_GF _ _ (blk4 (bl hn 1 (-X) 0 1) 0 0 (bl hn 1 0 (-(-X)ᴴ) 1)) (sh_mat_rat M X) ?_
  rw [hinv]
  exact sh_mat_rat M (-X)

theorem reduce (M : Maps D hn) {Kz : Set (hermA D ρ)} {Kx : Set (Mx D ρ p)}
    (hKz : ∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ Kz) (hKx : ∀ x : Mx D ρ p, ∃ η, rat η + x ∈ Kx)
    (z : hermA D ρ) (x y : Mx D ρ p) : ∃ γ ∈ GF D n, ∃ a ∈ Kz, ∃ b ∈ Kx, ∃ c ∈ Kx,
      γ * (M.nzx z 0 * (M.nzx 0 x * M.sh y)) = M.nzx a 0 * (M.nzx 0 b * M.sh c) := by
  obtain ⟨η, hy⟩ := hKx y
  obtain ⟨ξ, hx⟩ := hKx x
  obtain ⟨ζ, hζ, hz⟩ := hKz (tw z x (rat (-η)))
  refine ⟨M.nzx ζ (rat ξ) * M.sh (rat η), mul_mem (nzx_rat M ζ hζ ξ) (sh_rat M η), _, hz, _, hx, _, hy, ?_⟩
  have h1 : M.nzx z 0 * M.nzx 0 x = M.nzx z x := by rw [nzx_mul, add_zero, zero_add]
  have h2 : M.sh y = M.sh (rat (-η)) * M.sh (rat η + y) := by
    rw [sh_mul, rat_neg', neg_add_cancel_left]
  have h3 : M.sh (rat η) * M.sh (rat (-η)) = 1 := by
    rw [sh_mul, rat_neg', add_neg_cancel, sh_zero]
  have h4 : M.nzx (ζ + tw z x (rat (-η))) 0 * M.nzx 0 (rat ξ + x) =
      M.nzx ζ (rat ξ) * M.nzx (tw z x (rat (-η))) x := by
    rw [nzx_mul, nzx_mul, add_zero, zero_add]
  calc M.nzx ζ (rat ξ) * M.sh (rat η) * (M.nzx z 0 * (M.nzx 0 x * M.sh y))
      = M.nzx ζ (rat ξ) * M.sh (rat η) * ((M.nzx z 0 * M.nzx 0 x) * M.sh y) := by
        simp only [mul_assoc]
    _ = M.nzx ζ (rat ξ) * M.sh (rat η) * ((M.nzx z x * M.sh (rat (-η))) * M.sh (rat η + y)) := by
        rw [h1, mul_assoc (M.nzx z x), ← h2]
    _ = M.nzx ζ (rat ξ) * (M.sh (rat η) * M.sh (rat (-η))) *
          (M.nzx (tw z x (rat (-η))) x * M.sh (rat η + y)) := by
        rw [nzx_sh M z x]; simp only [mul_assoc]
    _ = M.nzx (ζ + tw z x (rat (-η))) 0 * (M.nzx 0 (rat ξ + x) * M.sh (rat η + y)) := by
        rw [h3, mul_one, ← mul_assoc (M.nzx _ 0), h4]; simp only [mul_assoc]

theorem chz_norm {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (z : hermA D ρ) :
    ‖chz ψ b₀ z‖ = 1 := hψ.2.1 _

theorem continuous_chz {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (chz ψ b₀ : hermA D ρ → ℂ) :=
  hψ.1.comp (continuous_halfTr.comp (Continuous.matrix_trace (continuous_const.matrix_mul continuous_subtype_val)))

theorem cont_dom {X Y : Type} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    [MeasurableSpace Y] (ν : Measure Y) (hν : ν Set.univ < ⊤) (f : X → Y → ℂ)
    (h1 : ∀ x, AEStronglyMeasurable (f x) ν) (h2 : ∀ y, Continuous fun x => f x y)
    (hb : ∀ Q : Set X, IsCompact Q → ∃ B : ℝ, ∀ y, ∀ x ∈ Q, ‖f x y‖ ≤ B) :
    Continuous fun x => ∫ y, f x y ∂ν := by
  haveI : IsFiniteMeasure ν := ⟨hν⟩
  refine continuous_iff_continuousAt.2 fun g => ?_
  obtain ⟨Q, hQ, hgQ⟩ := exists_compact_mem_nhds g
  obtain ⟨B, hB⟩ := hb Q hQ
  refine continuousAt_of_dominated (bound := fun _ => B) (Eventually.of_forall h1) ?_ (integrable_const B)
    (ae_of_all _ fun y => (h2 y).continuousAt)
  filter_upwards [hgQ] with h hh
  exact ae_of_all _ fun y => hB y h hh

section An

variable (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)

include hψ in
theorem zc_bound (F : G D n → ℂ) (h : G D n) (B : ℝ) (hB : ∀ z, ‖F (M.nzx z 0 * h)‖ ≤ B) :
    ‖zc M m ψ b₀ F h‖ ≤ B := by
  have h0 := norm_setIntegral_le_of_norm_le_const (μ := m.lz) (s := m.𝓖) (C := B)
    (f := fun z => F (M.nzx z 0 * h) * conj (chz ψ b₀ z)) (by rw [m.hz.2.2]; simp)
    (fun z _ => by rw [norm_mul, RCLike.norm_conj, chz_norm hψ, mul_one]; exact hB z)
  have h1 : m.lz.real m.𝓖 = 1 := by simp [Measure.real, m.hz.2.2]
  rw [h1, mul_one] at h0
  exact h0

theorem pc_bound (F : G D n → ℂ) (h : G D n) (B : ℝ) (hB : ∀ x, ‖zc M m ψ b₀ F (M.nzx 0 x * h)‖ ≤ B) :
    ‖pc M m ψ b₀ F h‖ ≤ B := by
  have h0 := norm_setIntegral_le_of_norm_le_const (μ := m.μ) (s := m.𝓕) (C := B)
    (f := fun x => zc M m ψ b₀ F (M.nzx 0 x * h)) (by rw [m.hμ.2.2]; simp) (fun x _ => hB x)
  have h1 : m.μ.real m.𝓕 = 1 := by simp [Measure.real, m.hμ.2.2]
  rw [h1, mul_one] at h0
  exact h0

theorem continuous_nz : Continuous fun z : hermA D ρ => M.nzx z 0 :=
  M.nzx_cont.comp (continuous_id.prodMk continuous_const)

theorem continuous_nx : Continuous fun x : Mx D ρ p => M.nzx 0 x :=
  M.nzx_cont.comp (continuous_const.prodMk continuous_id)

include hψ in
theorem zc_cont (F : G D n → ℂ) (hF : Continuous F)
    (hb : ∀ Q : Set (G D n), IsCompact Q → ∃ B : ℝ, ∀ z, ∀ h ∈ Q, ‖F (M.nzx z 0 * h)‖ ≤ B) :
    Continuous (zc M m ψ b₀ F) := by
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  have hcz : ∀ h : G D n, Continuous fun z : hermA D ρ => F (M.nzx z 0 * h) * conj (chz ψ b₀ z) := fun h =>
    (hF.comp ((continuous_nz M).mul continuous_const)).mul
      (Complex.continuous_conj.comp (continuous_chz hψ b₀))
  refine cont_dom (m.lz.restrict m.𝓖) (by rw [Measure.restrict_apply_univ, m.hz.2.2]; exact ENNReal.one_lt_top) _ (fun h => (hcz h).aestronglyMeasurable)
    (fun z => (hF.comp (continuous_const.mul continuous_id)).mul continuous_const) fun Q hQ => ?_
  obtain ⟨B, hB⟩ := hb Q hQ
  refine ⟨B, fun z h hh => ?_⟩
  rw [norm_mul, RCLike.norm_conj, chz_norm hψ, mul_one]
  exact hB z h hh

theorem pc_cont (F : G D n → ℂ) (hF : Continuous (zc M m ψ b₀ F))
    (hb : ∀ Q : Set (G D n), IsCompact Q → ∃ B : ℝ, ∀ x, ∀ h ∈ Q, ‖zc M m ψ b₀ F (M.nzx 0 x * h)‖ ≤ B) :
    Continuous (pc M m ψ b₀ F) := by
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  exact cont_dom (m.μ.restrict m.𝓕) (by rw [Measure.restrict_apply_univ, m.hμ.2.2]; exact ENNReal.one_lt_top) _
    (fun h => (hF.comp ((continuous_nx M).mul continuous_const)).aestronglyMeasurable)
    (fun x => hF.comp (continuous_const.mul continuous_id)) (fun Q hQ => hb Q hQ)

end An

end GlobalTheory.CompanionTheory.PcB

theorem GlobalTheory.CompanionTheory.PcB.pcBound : PcBound := by
  intro D n ρ p hn M m ψ hψ b₀
  obtain ⟨Kz, hKz, hcz⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := ρ)
  obtain ⟨-, -, -, -, -, Kx, hKx, hcx₀⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ p
  have hcx : ∀ x : Mx D ρ p, ∃ η, rat η + x ∈ Kx := fun x => by
    obtain ⟨γ, ⟨η, hη⟩, hk⟩ := hcx₀ x
    have hη' : γ = rat η := hη.symm
    exact ⟨η, hη' ▸ hk⟩
  let e : hermA D ρ × Mx D ρ p × Mx D ρ p → G D n := fun u => M.nzx u.1 0 * (M.nzx 0 u.2.1 * M.sh u.2.2)
  have he : Continuous e := ((GlobalTheory.CompanionTheory.PcB.continuous_nz M).comp continuous_fst).mul
    (((GlobalTheory.CompanionTheory.PcB.continuous_nx M).comp (continuous_fst.comp continuous_snd)).mul
      (M.sh_cont.comp (continuous_snd.comp continuous_snd)))
  let C₀ : Set (G D n) := e '' (Kz ×ˢ (Kx ×ˢ Kx))
  have hC₀ : IsCompact C₀ := (hKz.prod (hKx.prod hKx)).image he
  have red : ∀ z x y, ∃ γ ∈ GF D n, γ * (M.nzx z 0 * (M.nzx 0 x * M.sh y)) ∈ C₀ := fun z x y => by
    obtain ⟨γ, hγ, a, ha, b, hb, c, hc, h⟩ := GlobalTheory.CompanionTheory.PcB.reduce M hcz hcx z x y
    exact ⟨γ, hγ, h ▸ ⟨(a, b, c), ⟨ha, hb, hc⟩, rfl⟩⟩
  refine ⟨fun F hF hinv => ?_, fun g => ⟨(· * g) '' C₀, hC₀.image (continuous_id.mul continuous_const), fun z x y => ?_, ?_⟩⟩
  · have hbd : ∀ Q : Set (G D n), IsCompact Q → ∃ B : ℝ, ∀ z x, ∀ h ∈ Q, ‖F (M.nzx z 0 * (M.nzx 0 x * h))‖ ≤ B := by
      intro Q hQ
      obtain ⟨B, hB⟩ := (hC₀.mul hQ).exists_bound_of_continuousOn hF.continuousOn
      refine ⟨B, fun z x h hh => ?_⟩
      obtain ⟨γ, hγ, hc⟩ := red z x 0
      rw [← hinv γ hγ]
      have := hB _ (Set.mul_mem_mul hc hh)
      rw [GlobalTheory.CompanionTheory.PcB.sh_zero, mul_one] at this
      simpa only [mul_assoc] using this
    have hz : Continuous (zc M m ψ b₀ F) := by
      refine GlobalTheory.CompanionTheory.PcB.zc_cont M m hψ b₀ F hF fun Q hQ => ?_
      obtain ⟨B, hB⟩ := hbd Q hQ
      refine ⟨B, fun z h hh => ?_⟩
      have := hB z 0 h hh
      rwa [show M.nzx 0 0 = 1 from GlobalTheory.CompanionTheory.PcB.nzx_zero M, one_mul] at this
    refine GlobalTheory.CompanionTheory.PcB.pc_cont M m b₀ F hz fun Q hQ => ?_
    obtain ⟨B, hB⟩ := hbd Q hQ
    exact ⟨B, fun x h hh => GlobalTheory.CompanionTheory.PcB.zc_bound M m hψ b₀ F _ B fun z => hB z x h hh⟩
  · obtain ⟨γ, hγ, hc⟩ := red z x y
    exact ⟨γ, hγ, _, hc, by simp only [mul_assoc]⟩
  · intro F hF hinv B hB y
    refine GlobalTheory.CompanionTheory.PcB.pc_bound M m b₀ F _ B fun x => GlobalTheory.CompanionTheory.PcB.zc_bound M m hψ b₀ F _ B fun z => ?_
    obtain ⟨γ, hγ, hc⟩ := red z x y
    rw [← hinv γ hγ]
    have := hB _ ⟨_, hc, rfl⟩
    simpa only [mul_assoc] using this
