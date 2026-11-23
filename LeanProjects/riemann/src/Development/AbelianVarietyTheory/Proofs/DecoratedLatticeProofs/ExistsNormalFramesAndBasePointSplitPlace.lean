import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul_gaMat (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_gaMat (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem Place.pi_idem (p : Place D k) : p.π p.e = 1 := by
  have h1 := p.ι_π 1
  rw [mul_one, map_one] at h1
  rw [← h1, p.π_ι]

theorem Place.pi_eq_of_toEAf (p : Place D k) {a b : AE D} (h : toEAf D a = toEAf D b) : p.π a = p.π b := by
  have hf : finPart D a = finPart D b :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective h
  have key : p.e * a = p.e * b := GlobalTheory.SplitScalar.adele_ext
    (by rw [map_mul, map_mul, GlobalTheory.SplitScalar.infPart_splitIdem p.split, zero_mul, zero_mul])
    (by rw [map_mul, map_mul, hf])
  calc p.π a = p.π (p.e * a) := by rw [map_mul, p.pi_idem, one_mul]
    _ = p.π (p.e * b) := by rw [key]
    _ = p.π b := by rw [map_mul, p.pi_idem, one_mul]

theorem Place.map_pi_eq_of_toEAf (p : Place D k) {m n : ℕ} {a b : Matrix (Fin m) (Fin n) (AE D)}
    (h : a.map (toEAf D) = b.map (toEAf D)) : a.map p.π = b.map p.π := by
  ext i j
  exact p.pi_eq_of_toEAf (congrFun (congrFun h i) j)

theorem exists_toEAf_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

def liftM {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : Matrix (Fin m) (Fin n) (AE D) :=
  x.map fun z => (exists_toEAf_lift z).choose

theorem liftM_map {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : (liftM x).map (toEAf D) = x := by
  ext i j
  exact (exists_toEAf_lift (x i j)).choose_spec

def stdFrame (k : Type) [Field k] (N : ℕ) : Frame k N (Fin N) := ⟨1, 1, by simp, by simp⟩

theorem exists_GL_mul_of_mul_eq_one {n : ℕ} (M : GL (Fin n) k) (N Ni : Matrix (Fin n) (Fin n) k) (h : N * Ni = 1) :
    ∃ gk : GL (Fin n) k, gk.val = M.val * Ni := by
  have h' : Ni * N = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 h
  exact ⟨M * ⟨Ni, N, h', h⟩, rfl⟩

theorem Place.exists_movedTo (p : Place D k) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (M : GL (Fin V.rank) k) (g₀ : GA D V) : ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), b₀.map (toEAf D) = β.val :=
    ⟨liftM β.val, liftM_map _⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), c₀.map (toEAf D) = (β⁻¹).val :=
    ⟨liftM (β⁻¹).val, liftM_map _⟩
  have hbc : b₀.map p.π * c₀.map p.π = 1 := by
    rw [← Matrix.map_mul]
    have h1 : (b₀ * c₀).map (toEAf D) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (toEAf D) := by
      rw [Matrix.map_mul, hb₀, hc₀, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
    rw [p.map_pi_eq_of_toEAf h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : ((mt V g₀).map p.π * b₀.map p.π) * (c₀.map p.π * (mt V g₀⁻¹).map p.π) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (b₀.map p.π), hbc, Matrix.one_mul, ← Matrix.map_mul, ← mt_mul_gaMat,
      mul_inv_cancel, mt_one_gaMat, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN' : (c₀.map p.π * (mt V g₀⁻¹).map p.π) * ((mt V g₀).map p.π * b₀.map p.π) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 hN
  obtain ⟨gk, hgk⟩ := exists_GL_mul_of_mul_eq_one M _ _ hN
  obtain ⟨g, hg, -⟩ := ((GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 V (Fin V.rank) (stdFrame k V.rank)).1 gk
  refine ⟨g, hg.1, fun b hb => ?_⟩
  have h2 : (mt V g).map p.π = gk.val := by
    rw [hg.2]
    change (1 : Matrix (Fin V.rank) (Fin V.rank) k) * gk.val * 1 = gk.val
    rw [Matrix.one_mul, Matrix.mul_one]
  have hbb : b.map p.π = b₀.map p.π := p.map_pi_eq_of_toEAf (by rw [hb, hb₀])
  rw [mt_mul_gaMat, Matrix.map_mul, Matrix.map_mul, h2, hbb, hgk, Matrix.mul_assoc (M.val * _), Matrix.mul_assoc M.val,
    hN', Matrix.mul_one]

theorem normalFrames_and_basePoint_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), p.xi ≠ 0 → (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n), s ≠ 0 → (∃ F : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F) ∧ ∃ F : Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n), s ≠ 0 → hh ≠ 0 → ∃ F : Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (M : GL (Fin V.rank) k) (g₀ : GA D V), ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val :=
  fun _ _ _ _ _ _ p _ =>
    ⟨fun _ _ _ _ B _ FA hs => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA⟩,
      fun _ _ _ _ J _ _ F₀ hs hh0 => p.exists_isJacFrame hs J hh0 F₀,
      fun V β M g₀ => p.exists_movedTo V β M g₀⟩

end GlobalTheory.LocMod
