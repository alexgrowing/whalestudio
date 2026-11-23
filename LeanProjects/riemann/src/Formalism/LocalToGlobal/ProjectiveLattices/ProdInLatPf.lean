import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

theorem prodInLat_of (hj : InR D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (wL ka : WeightFamilies.Wt D j) (n : ℕ)
    (hw : ∀ k, ∃ F : (recB hL).Cusp j wL, F ∈ (recB hL).Mlat j wL ∧ (F : Tc.R j) = wR k)
    (hn : 1 ≤ n) (hka : ∀ x, wtA ka x = n * wtA wL x) (hkn : ka.n = n * wL.n) : ProdInLat hL j ka wR n := by
  have hV : ∀ la, ∀ v ∈ Tc.Vs j la, IsVal la v := fun la => isVal_valSet la
  have hw1 : ∀ k, wR k ∈ Tc.C j wL ∧ ∀ la, ∀ v ∈ Tc.Vs j la, 0 ≤ v (wR k) := by
    intro k
    obtain ⟨F, hF, hFk⟩ := hw k
    rw [← hFk]
    exact ⟨cutR_le Tc.C j wL F.2, hF⟩
  have key : ∀ m (s : Fin (m + 1) → Fin (N + 1)), ∃ W : WeightFamilies.Wt D j, (∀ x, wtA W x = (m + 1) * wtA wL x) ∧
      W.n = (m + 1) * wL.n ∧ ∏ k, wR (s k) ∈ Tc.C j W ∧ ∀ la, ∀ v ∈ Tc.Vs j la, 0 ≤ v (∏ k, wR (s k)) := by
    intro m
    induction m with
    | zero =>
      intro s
      refine ⟨wL, fun x => by ring, by ring, ?_, ?_⟩
      · rw [Fin.prod_univ_one]; exact (hw1 _).1
      · rw [Fin.prod_univ_one]; exact (hw1 _).2
    | succ m ih =>
      intro s
      obtain ⟨W, hW1, hW2, hWm, hWv⟩ := ih (fun k => s k.succ)
      refine ⟨WeightAlgebra.wadd wL W, fun x => ?_, ?_, ?_, ?_⟩
      · rw [wtA_wadd, Pi.add_apply, hW1 x]; ring
      · rw [n_wadd, hW2]; ring
      · rw [Fin.prod_univ_succ]; exact hL.mul j hj wL W _ (hw1 _).1 _ hWm
      · intro la v hv
        rw [Fin.prod_univ_succ, (hV la v hv).mul]
        exact add_nonneg ((hw1 _).2 la v hv) (hWv la v hv)
  intro s
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨W, hW1, hW2, hWm, hWv⟩ := key m s
  have hmem : ∏ k, wR (s k) ∈ Tc.C j ka := by
    have hC : Tc.C j ka = Tc.C j W := by
      show Tc.cuspA j (wtA ka) ka.n = Tc.cuspA j (wtA W) W.n
      rw [hkn, hW2, show wtA ka = wtA W from funext fun x => by rw [hka x, hW1 x]]
    rw [hC]; exact hWm
  refine ⟨⟨∏ k, wR (s k), ?_⟩, ?_, rfl⟩
  · show _ ∈ cutR Tc.C j ka
    rw [cutR_eq Tc.C hj]; exact hmem
  · exact hWv

theorem prodInLat_of_wtZ (hj : InR D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (wL ka : WeightFamilies.Wt D j) (n : ℕ)
    (hw : ∀ k, ∃ F : (recB hL).Cusp j wL, F ∈ (recB hL).Mlat j wL ∧ (F : Tc.R j) = wR k)
    (hn : 1 ≤ n) (hkaZ : wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n) : ProdInLat hL j ka wR n := by
  refine prodInLat_of hL j hj wR wL ka n hw hn (fun x => ?_) ?_
  · have h1 := congrFun (congrArg Prod.fst hkaZ) x
    simp only [wtZ, Prod.smul_fst, Pi.smul_apply] at h1
    rw [nsmul_eq_mul] at h1
    exact_mod_cast h1
  · have h2 := congrArg Prod.snd hkaZ
    simp only [wtZ, Prod.smul_snd] at h2
    rw [nsmul_eq_mul] at h2
    exact_mod_cast h2

end Formalism.L2.Pj
