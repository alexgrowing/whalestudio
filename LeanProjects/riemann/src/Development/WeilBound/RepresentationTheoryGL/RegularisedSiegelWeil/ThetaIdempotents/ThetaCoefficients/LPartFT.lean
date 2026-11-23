import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTE

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t : ℕ}

def h0 (D : D7) (p : ℕ) : HermE D p := ⟨0, by simp⟩

theorem j_zero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {p : ℕ} (y : Mx D V.rank p) :
    ψ (halfTr (Matrix.trace (HMul.hMul ((h0 D p).1.map (incA D)) (GlobalTheory.StdUnn.inner V y y) : Mx D p p))) = 1 := by
  simp [h0, halfTr]

theorem clause1 {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (hn : r + t = n) (M : Maps D hn)
    (μr : Measure (Mx D V.rank r)) (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) (Φ : schwartzA θ V.rank n) :
    (ω M.w Φ).1 0 = ∫ x, Φ.1 (jn hn x 0) ∂μr := by
  have hmat : mat M.w = (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D r).1 1).map (incA D) := by
    rw [h0, repMat_zero, mA_one, Matrix.mul_one, mat_w]
  have hγ : M.w ∈ GF D n := mem_gf_of _ (wr_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (wr_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2 (mat_w hn M)
  rw [partial_fourier_second_term hS Φ r (by omega) μr hμr (c₁ D hn) 1 (compl_c₁ hn) (h0 D r) M.w hγ hmat]
  unfold J pull
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [j_zero, mul_one]
  exact congrArg Φ.1 (mul_c₁ hn y)

theorem clause2 {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hn : r + t = n) (Φ : schwartzA θ V.rank n) :
    (fun x => Φ.1 (jn hn x 0)) ∈ schwartzA θ V.rank r := by
  have := GlobalTheory.T.pullback_schwartz_linear_independent D θ hθ V.rank r n (c₁ D hn) (linInd_c₁ hn) Φ.1 Φ.2
  convert this using 1
  funext x
  exact congrArg Φ.1 (mul_c₁ hn x).symm

theorem clause3 {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (hn : r + t = n) (M : Maps D hn)
    (μt : Measure (Mx D V.rank t)) (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n)
    (w : G D t) (hw : IsW w) (x : Mx D V.rank r) (v₀ : Mx D V.rank t) :
    (ω (M.emb w) Φ).1 (jn hn x v₀) = ∫ v, Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V v₀ v))) ∂μt := by
  have hγ : M.emb w ∈ GF D n := mem_gf_of _ (second_block_weyl_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (second_block_weyl_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2 (mat_emb hn M w hw)
  obtain ⟨γQ, hQ, hmQ⟩ := (GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n).2.1 _ (gQ_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (gQ_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2
  have hγ' : γQ⁻¹ * M.emb w ∈ GF D n := (GF D n).mul_mem ((GF D n).inv_mem hQ) hγ
  have hmat' : mat (γQ⁻¹ * M.emb w) =
      (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D t).1 (Pm D.host.E hn)).map (incA D) := by
    have h1 : mat γQ * (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D t).1 (Pm D.host.E hn)).map (incA D) =
        mat (M.emb w) := by
      rw [hmQ, ← Matrix.map_mul, h0, key3, mat_emb hn M w hw]
    rw [mat_mul', ← h1, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
  have hψ := hS.1
  have hθ := hS.2.2.1
  have hΨm := GlobalTheory.T.eisenstein_heisenberg_schwartz D ψ hψ θ hθ V n (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ.1 Φ.2
  let Ψ : schwartzA θ V.rank n := ⟨Heisenberg₂ ψ V (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ.1, hΨm⟩
  have hc := covar_w hS (M.emb w) hγ (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ Ψ rfl
  have hv : HMul.hMul (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) (mat (M.emb w)⁻¹) = xz (jn hn x v₀) := by
    rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]
  rw [hv] at hc
  have step1 : (ω (M.emb w) Φ).1 (jn hn x v₀) = (ω (M.emb w) Ψ).1 0 := by rw [hc, heis_xz]
  have step2 : (ω (M.emb w) Ψ).1 0 = (ω (γQ⁻¹ * M.emb w) Ψ).1 0 := by
    conv_lhs => rw [show M.emb w = γQ * (γQ⁻¹ * M.emb w) by group]
    rw [map_mul, Module.End.mul_apply]
    exact levi_zero hS γQ (uP D hn) (mat_gQ hn hmQ) _
  rw [step1, step2, partial_fourier_second_term hS Ψ t (by omega) μt hμt (c₃ D hn) (Pm D.host.E hn) (compl_c₃ hn) (h0 D t) _ hγ' hmat']
  have hx : xPart (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) = jn hn x 0 := by
    rw [mat_emb' hn M w hw, x_part_mul_block, xPart_xz, yPart_xz, jn_mul_bl]; simp
  have hy : yPart (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) = jn hn 0 v₀ := by
    rw [mat_emb' hn M w hw, y_part_mul_block, xPart_xz, yPart_xz, jn_mul_bl]; simp
  have hip1 : ∀ {a b : ℕ} (z : Mx D V.rank b), ip V (0 : Mx D V.rank a) z = 0 := fun z => by simp [ip, mm, adj]
  have hip2 : ∀ {a b : ℕ} (z : Mx D V.rank a), ip V z (0 : Mx D V.rank b) = 0 := fun z => by simp [ip, mm]
  unfold J pull
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [j_zero, mul_one]
  show PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V _ Φ.1 _ = _
  rw [show (HMul.hMul y ((c₃ D hn).map (incA D)) : Mx D V.rank n) = jn hn 0 y from mul_c₃ hn y]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [hx, hy, jn_add, trace_inner_jn, trace_inner_jn, hip1, hip1, hip2]
  simp only [Matrix.trace_zero, zero_add, add_zero, halfTr, map_zero, mul_zero]
  rw [psi_ip_symm, mul_comm]

end PositivityTheory.Rg.Rsw.L.LPartFT

namespace PositivityTheory.Rg.Rsw.L

theorem partFT : PartFT := by
  intro D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt Φ
  have hS : LPartFT.SetW D n V ψ χ θ μ ω := ⟨hψ, hχ, hθ, hμ, hω⟩
  exact ⟨LPartFT.clause1 hS hn M μr hμr Φ, LPartFT.clause2 hθ hn Φ,
    fun w hw x v₀ => LPartFT.clause3 hS hn M μt hμt Φ w hw x v₀⟩

end PositivityTheory.Rg.Rsw.L
