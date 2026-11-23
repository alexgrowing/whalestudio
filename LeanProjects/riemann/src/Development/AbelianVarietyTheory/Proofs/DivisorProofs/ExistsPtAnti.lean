import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviChartBlockDiagonalAdjointStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}
  {J : Matrix (Fin n) (Fin n) D.host.E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
  {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n} {ι : UD D (-V.gram) ≃ₜ* GA D V} {d : ℕ}
  {ε : Module.Basis (Fin d) D.host.F D.host.E} {co : Dbx V J₂ d}
  {om : UD D (-V.gram) × UD D J₂ →* Module.End ℂ ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ)}

theorem exists_pt_anti (hT : IsWittBasis D.sp.cm.sig J 1 T) {m : ℕ} {u : Mx D m (n + n)}
    (hu : ∀ i, u i ∈ antiSub (AE D) finSumFinEquiv) : ∃ x, u = pt T 0 x := by
  obtain ⟨q, x, rfl⟩ := exists_pt T u
  rw [(pt_anti_iff hT q x).1 hu]
  exact ⟨x, rfl⟩

theorem IsTrans.right (hom : IsTrans ε ι κ ω om) (g : UD D J₂) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (Φ : schwartzA θ V.rank n) (h : φ ∘ coord ε = Φ.1)
    (x : Mx D V.rank n) : om (1, g) φ (coord ε x) = (ω (κ g) Φ).1 x := by
  rw [hom.2 1 g φ hφ Φ h, map_one, inv_one, mt_one, Matrix.one_mul]

theorem invOf_two_mul (z : AE D) : ⅟(2 : AF D.host.F) * StdUnn.trA z = StdUnn.halfTr z := by
  rw [StdUnn.halfTr]
  congr 1
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem mat_inv_weyl {w : StdUnn.G D n} (hw : StdUnn.mat w = StdUnn.blk4 0 1 (-1) 0) :
    StdUnn.mat w⁻¹ = StdUnn.blk4 0 (-1) 1 0 := by
  have h1 : StdUnn.mat w⁻¹ * StdUnn.mat w = 1 := by
    rw [← StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, StdUnn.LeftInvSect.mat_one]
  have h2 : (StdUnn.blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * StdUnn.blk4 0 (-1) 1 0 = 1 := by
    rw [StdUnn.Model.submatrix_fromBlocks_mul, ← StdUnn.Model.block_matrix_one]
    simp only [mul_zero, zero_mul, mul_one, add_zero, zero_add, mul_neg, neg_zero, neg_neg]
  rw [← Matrix.mul_one (StdUnn.mat w⁻¹), ← h2, ← hw, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem zmul {a b c : ℕ} (y : Mx D b c) : ((0 : Mx D a b) ⬝ y : Mx D a c) = 0 := Matrix.zero_mul y

theorem mulz {a b c : ℕ} (y : Mx D a b) : (y ⬝ (0 : Mx D b c) : Mx D a c) = 0 := Matrix.mul_zero y

theorem mulo {a b : ℕ} (y : Mx D a b) : (y ⬝ (1 : Mx D b b) : Mx D a b) = y := Matrix.mul_one y

theorem formula_lin (hθ : IsInfFam θ) (hι : IsConjV V ι) (hco : IsCoord V T ε co) (hom : IsTrans ε ι κ ω om)
    (h : UD D (-V.gram)) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (h, 1) φ (co.e (pt T 0 x)).1 = φ (co.e (umat h⁻¹ ⬝ pt T 0 x)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  rw [mul_pt, (hco _ _).1, (hco _ _).1, hom.2 h 1 φ hφ ⟨_, hS⟩ rfl, map_one, map_one, ← map_inv, hι]
  rfl

theorem formula_levi (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    (hom : IsTrans ε ι κ ω om) {p : UD D J₂} {a : GL (Fin n) (AE D)}
    (h1 : StdUnn.mat (κ p) = StdUnn.blk4 a.1 0 0 (adj (a⁻¹).1))
    (h2 : StdUnn.mat (κ p⁻¹) = StdUnn.blk4 (a⁻¹).1 0 0 (adj a.1)) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, p) φ (co.e (pt T 0 x)).1 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) * φ (co.e (pt T 0 x ⬝ (umat p⁻¹)ᵀ)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  rw [hκ.pt_mul h2, (hco _ _).1, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.levi _ _ h1, zmul, zero_add, adj_adj]
  rfl

theorem formula_unip (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω)
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = StdUnn.Jst D n) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    (hom : IsTrans ε ι κ ω om) {b : UD D J₂} {β : Mx D n n} (hβ : StdUnn.mat (κ b) = StdUnn.blk4 1 β 0 1)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, b) φ (co.e (pt T 0 x)).1 =
      ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂)
        (pt T 0 x ⬝ (umat b)ᵀ) (pt T 0 x)) * φ (co.e (pt T 0 x)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  have e1 : StdUnn.inner V (x ⬝ adj β : Mx D V.rank n) x = β ⬝ StdUnn.inner V x x := by
    rw [StdUnn.inner, StdUnn.inner, adj_mul, adj_adj, Matrix.mul_assoc]
  have e2 : ∀ y, StdUnn.inner V y (0 : Mx D V.rank n) = 0 := fun y => by rw [StdUnn.inner, mulz, mulz]
  rw [hκ.pt_mul hβ, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.unip _ _ hβ, symp_pt V hG, e2, zmul, zero_add, e1,
    Matrix.trace_zero]
  have e3 : StdUnn.trA (0 : AE D) = 0 := map_zero _
  rw [e3, sub_zero, invOf_two_mul]
  rfl

theorem formula_weyl (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    [MeasurableSpace (Fin V.rank × Fin n × Fin d → AF D.host.F)] {μ' : Measure (Fin V.rank × Fin n × Fin d → AF D.host.F)}
    (hμ : ∀ f : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ)
    (hom : IsTrans ε ι κ ω om) {w : UD D J₂} (hw : StdUnn.mat (κ w) = StdUnn.blk4 0 1 (-1) 0)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, w) φ (co.e (pt T 0 x)).1 = 1 * ∫ y, φ y * ψ (y ⬝ᵥ (co.e (pt T 0 x ⬝ (umat w⁻¹)ᵀ)).2) ∂μ' := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  have h2 : StdUnn.mat (κ w⁻¹) = StdUnn.blk4 0 (-1) 1 0 := by rw [map_inv]; exact mat_inv_weyl hw
  have e0 : ((0 : Mx D V.rank n) ⬝ adj (0 : Mx D n n) + x ⬝ adj (-1 : Mx D n n) : Mx D V.rank n) = -x := by
    rw [zmul, zero_add, adj_neg, adj_one, Matrix.mul_neg, mulo]
  rw [hκ.pt_mul h2, e0, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.weyl _ hw, one_mul, hμ]
  refine integral_congr_ae (.of_forall fun y => ?_)
  have e1 : StdUnn.inner V y (-x) = -StdUnn.inner V y x := by
    rw [StdUnn.inner, StdUnn.inner, Matrix.mul_neg, Matrix.mul_neg]
  have e3 : ∀ z : AE D, StdUnn.trA (-z) = -StdUnn.trA z := fun z => map_neg _ z
  beta_reduce
  rw [(hco _ _).2, e1, Matrix.trace_neg, e3, neg_neg, trA_inner_comm]
  rfl

theorem levi_pair (hT : IsWittBasis D.sp.cm.sig J 1 T) (hκ : IsChartW T κ) {p : UD D J₂}
    (hs : p ∈ siegelOf finSumFinEquiv (uinc D J₂)) (hp : p ∈ leviSubOf finSumFinEquiv (uinc D J₂)) :
    ∃ a : GL (Fin n) (AE D), aOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩ = Matrix.GeneralLinearGroup.det a ∧
      StdUnn.mat (κ p) = StdUnn.blk4 a.1 0 0 (adj (a⁻¹).1) ∧ StdUnn.mat (κ p⁻¹) = StdUnn.blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 := (GlobalTheory.T.levi_chart_block_diagonal_adjoint D n J₂ T κ hκ J hT).1 ⟨p, hs⟩ hp
  refine ⟨leviOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩, rfl, h1, ?_⟩
  generalize leviOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩ = a at h1 ⊢
  have h2 : StdUnn.mat (κ p⁻¹) * StdUnn.mat (κ p) = 1 := by
    rw [← StdUnn.LeftInvSect.mat_mul, ← map_mul, inv_mul_cancel, map_one, StdUnn.LeftInvSect.mat_one]
  rw [← Matrix.mul_one (StdUnn.mat (κ p⁻¹)), ← StdUnn.LeftInvSect.levi_mul_inv a, ← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]

set_option maxHeartbeats 4000000 in

theorem formulas (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hT : IsWittBasis D.sp.cm.sig J 1 T)
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = StdUnn.Jst D n) (hκ : IsChartW T κ) (hι : IsConjV V ι) (hco : IsCoord V T ε co)
    [MeasurableSpace (Fin V.rank × Fin n × Fin d → AF D.host.F)] {μ' : Measure (Fin V.rank × Fin n × Fin d → AF D.host.F)}
    (hμ : ∀ f : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ)
    (hom : IsTrans ε ι κ ω om) : IsWeilFormulas D.sp.cm.sig ψ χ T co μ' om := by
  refine ⟨hom.1, ?_, ?_, ?_, ?_⟩
  · intro h φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    exact formula_lin hθ hι hco hom h hφ x
  · rintro ⟨p, hs⟩ hp φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    obtain ⟨a, ha, h1, h2⟩ := levi_pair hT hκ hs hp
    rw [ha]
    exact formula_levi hθ hω hκ hco hom h1 h2 hφ x
  · intro b hb φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.levi_chart_block_diagonal_adjoint D n J₂ T κ hκ J hT).2 b hb
    exact formula_unip hθ hω hG hκ hco hom hβ hφ x
  · intro w hw
    refine ⟨1, 1, one_pos, one_pow _, fun φ hφ u hu => ?_⟩
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    exact formula_weyl hθ hω hκ hco hμ hom ((hκ w).trans hw) hφ x

end GlobalTheory.SWLink

end
