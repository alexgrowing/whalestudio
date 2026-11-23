import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAB

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

theorem gens_inv (g : G D n)
    (hg : (∃ b, mat g⁻¹ = blk4 1 b 0 1) ∨ (∃ a d, mat g⁻¹ = blk4 a 0 0 d) ∨ (∃ c, mat g⁻¹ = blk4 1 0 c 1)) :
    (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1) := by
  have hgg : g = (g⁻¹)⁻¹ := (inv_inv g).symm
  rcases hg with ⟨b, hb⟩ | ⟨a, d, h⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨-adj b, ?_⟩
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hb]; simp [adj_one, adj_zero]
  · refine Or.inr (Or.inl ⟨adj d, adj a, ?_⟩)
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ h]; simp [adj_zero]
  · refine Or.inr (Or.inr ⟨-adj c, ?_⟩)
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hc]; simp [adj_one, adj_zero]

theorem closure_triv (hG : GenA) (hDA : DecompAway) {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι) (x : G D n) (hx : IsTrivAt θ τ x) :
    x ∈ Submonoid.closure {x : G D n | IsTrivAt θ τ x ∧
      ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))} := by
  classical
  choose π yf hπ using fun g => hDA D n θ τ ι hθ hι g
  have πmul : ∀ g h : G D n, π (g * h) = π g * π h := by
    intro g h
    have e1 := (hπ (g * h)).2.1
    have hg := (hπ g).2.1
    have hh := (hπ h).2.1
    have hc := (hπ h).2.2 (yf g)
    have e2 : g * h = (π g * π h) * ι (yf g * yf h) := by
      calc g * h = π g * ι (yf g) * (π h * ι (yf h)) := by rw [← hg, ← hh]
        _ = π g * (ι (yf g) * π h) * ι (yf h) := by group
        _ = π g * (π h * ι (yf g)) * ι (yf h) := by rw [hc]
        _ = (π g * π h) * ι (yf g * yf h) := by rw [map_mul]; group
    have e3 : π (g * h) * ι (yf (g * h)) = (π g * π h) * ι (yf g * yf h) := e1.symm.trans e2
    have hy := uniq_dec hι (hπ (g * h)).1 (triv_mul (hπ g).1 (hπ h).1) e3
    rw [hy] at e3
    exact mul_right_cancel e3
  have πtriv : ∀ a, IsTrivAt θ τ a → π a = a := by
    intro a ha
    have e1 := (hπ a).2.1
    have hy := uniq_dec hι (hπ a).1 ha (show π a * ι (yf a) = a * ι 1 by rw [← e1, map_one, mul_one])
    rw [hy, map_one, mul_one] at e1
    exact e1.symm
  have fz : ((0 : Mx D n n)).map (finPart D) = 0 := Matrix.map_zero _ (map_zero _)
  have fo : ((1 : Mx D n n)).map (finPart D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have gen : ∀ s : G D n, ((∃ b, mat s = blk4 1 b 0 1) ∨ (∃ a d, mat s = blk4 a 0 0 d) ∨ (∃ c, mat s = blk4 1 0 c 1)) →
      IsTrivAt θ τ (π s) ∧ ((∃ b, mat (π s) = blk4 1 b 0 1) ∨ (∃ a d, mat (π s) = blk4 a 0 0 d) ∨
        (∃ c, mat (π s) = blk4 1 0 c 1)) := by
    intro s hs
    refine ⟨(hπ s).1, ?_⟩
    have e := (hπ s).2.1
    have hps : π s = s * (ι (yf s))⁻¹ := eq_mul_inv_of_mul_eq e.symm
    have hMaway : ∀ τ', τ' ≠ τ → compAt θ τ' (mat (ι (yf s))) = 1 := fun τ' h => (hι.2 (yf s)).2.1 τ' h
    have hMf : (mat (ι (yf s))).map (finPart D) = 1 := (hι.2 (yf s)).2.2
    have hMτ : compAt θ τ (mat (ι (yf s))) = compAt θ τ (mat s) := by
      have : compAt θ τ (mat s) = compAt θ τ (mat (π s)) * compAt θ τ (mat (ι (yf s))) := by
        conv_lhs => rw [e]
        rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul']
      rw [this, (hπ s).1, Matrix.one_mul]
    have hmat : mat (π s) = mat s * mat (ι (yf s))⁻¹ := by rw [hps, GlobalTheory.StdUnn.LeftInvSect.mat_mul]
    rcases hs with ⟨b, hb⟩ | ⟨a, d, had⟩ | ⟨c, hc⟩
    · rw [hb, component_block_matrix, compAt_one', compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, hA, -, hC, hE, haw, hAf, -, hCf, hEf⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hA1 : A = 1 := eq_of_comps hθ (by rw [hA, compAt_one']) (fun τ' h => by rw [(haw τ' h).1, compAt_one'])
        (by rw [hAf, fo])
      have hC0 : C = 0 := eq_of_comps hθ (by rw [hC, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.2.1, compAt_zero'])
        (by rw [hCf, fz])
      have hE1 : E' = 1 := eq_of_comps hθ (by rw [hE, compAt_one']) (fun τ' h => by rw [(haw τ' h).2.2.2, compAt_one'])
        (by rw [hEf, fo])
      rw [hA1, hC0, hE1] at hM
      refine Or.inl ⟨-adj B + b, ?_⟩
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, hb, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_one, adj_zero]
    · rw [had, component_block_matrix, compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, -, hB, hC, -, haw, -, hBf, hCf, -⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hB0 : B = 0 := eq_of_comps hθ (by rw [hB, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.1, compAt_zero'])
        (by rw [hBf, fz])
      have hC0 : C = 0 := eq_of_comps hθ (by rw [hC, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.2.1, compAt_zero'])
        (by rw [hCf, fz])
      rw [hB0, hC0] at hM
      refine Or.inr (Or.inl ⟨a * adj E', d * adj A, ?_⟩)
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, had, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_zero]
    · rw [hc, component_block_matrix, compAt_one', compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, hA, hB, -, hE, haw, hAf, hBf, -, hEf⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hA1 : A = 1 := eq_of_comps hθ (by rw [hA, compAt_one']) (fun τ' h => by rw [(haw τ' h).1, compAt_one'])
        (by rw [hAf, fo])
      have hB0 : B = 0 := eq_of_comps hθ (by rw [hB, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.1, compAt_zero'])
        (by rw [hBf, fz])
      have hE1 : E' = 1 := eq_of_comps hθ (by rw [hE, compAt_one']) (fun τ' h => by rw [(haw τ' h).2.2.2, compAt_one'])
        (by rw [hEf, fo])
      rw [hA1, hB0, hE1] at hM
      refine Or.inr (Or.inr ⟨c + -adj C, ?_⟩)
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, hc, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_one, adj_zero]
  set S : Set (G D n) := {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}
    with hSdef
  have hxS : x ∈ Submonoid.closure (S ∪ S⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, hG D n]
    show x ∈ (⊤ : Subgroup (G D n))
    exact Subgroup.mem_top x
  have key : ∀ g ∈ Submonoid.closure (S ∪ S⁻¹), π g ∈ Submonoid.closure {x : G D n | IsTrivAt θ τ x ∧
      ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))} := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      apply Submonoid.subset_closure
      rcases hg with hg | hg
      · exact gen g hg
      · exact gen g (gens_inv g hg)
    | one => rw [πtriv 1 triv_one]; exact one_mem _
    | mul g h _ _ ihg ihh => rw [πmul]; exact mul_mem ihg ihh
  have := key x hxS
  rwa [πtriv x hx] at this

end PositivityTheory.Rg.Sw.Glob.AW
