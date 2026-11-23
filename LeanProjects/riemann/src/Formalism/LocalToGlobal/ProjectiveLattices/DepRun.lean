import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem satDir_of (hS : ChartSaturated Xo c) {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntChart T io y) :
    SatDir T (letI := io.toAlgebra; C.ch.uvec) := by
  intro τ
  obtain ⟨⟨w, emb, hw, hbasis⟩, -⟩ := hS T io y C τ
  have huv := C.gen.1.2.2.2.2.2.2
  choose A hA using fun m : Fin (chD C.ch) => (hbasis (Pi.single m 1)).exists
  have hAw : (Matrix.of A) * (Matrix.of w) = 1 := by
    ext m j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [hA m j, Pi.single_apply]
    by_cases hjm : j = m
    · subst hjm; simp
    · simp [hjm, Ne.symm hjm]
  have hwA : (Matrix.of w) * (Matrix.of A) = 1 := by
    first
      | exact mul_eq_one_comm.mp hAw
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hAw
  refine ⟨fun i j => A j (emb i), fun i i' => ?_⟩
  letI := io.toAlgebra
  have e1 : ∀ j, C.ch.uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (A j (emb i)) =
      algebraMap T.V T.Fr (w (emb i') j * A j (emb i)) := by
    intro j
    rw [huv, map_mul, hw]
  refine (Finset.sum_congr rfl (fun j _ => e1 j)).trans ?_
  rw [← map_sum]
  have h3 := congrFun (congrFun hwA (emb i')) (emb i)
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h3
  rw [h3]
  by_cases hii : i' = i
  · subst hii; simp
  · rw [if_neg (fun h' => hii (emb.injective h')), if_neg hii, map_zero]

theorem nuW_le_crude (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n) :
    nuW Xo c la k a n ≤ max 0 (crudeBd la (DF Dw a) : EReal) := by
  unfold nuW
  refine max_le_max le_rfl ?_
  unfold nuSup
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho =>
    iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  unfold nuLoc
  refine (iInf_le _ C).trans ?_
  letI := io.toAlgebra
  exact (crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).1

omit [StarRing (𝓞 E)] in
theorem card_Lt1_le_finrank_mul : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc ∑ τ : E →+* ℂ, Dw.mult τ ≤ ∑ _τ : E →+* ℂ, (Dw.p + Dw.q) := by
        apply Finset.sum_le_sum
        intro τ _
        unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
        split_ifs <;> omega
    _ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
        rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, smul_eq_mul]

end

variable {D : D7}

theorem nuFinAt_of (T : Core D) (hp : T.Q.Pins) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)]
    (hw : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j)
    (hE : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c) (hS : ∀ j, InR D j → ChartSaturated (T.Q.Xo j) T.Q.c) :
    NuFinAt T Dd := by
  intro j hj la
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have hn : Fintype.card (Lt1 (T.Q.Dw j)) ≤ Dd.nW j := by
    refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]; exact (hw j hj).2
  refine ne_top_of_le_ne_top ?_ (nuW_le_crude (hE j hj) (hS j hj) la _ _ _ (fun τ i i' h => (hw j hj).1 τ h) hn)
  rcases le_total (0 : EReal) (crudeBd la (DF (T.Q.Dw j) (Dd.aL j)) : EReal) with h | h
  · rw [max_eq_right h]; exact EReal.coe_ne_top _
  · rw [max_eq_left h]; exact EReal.zero_ne_top

def depRun (T : Core D) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j) : DepData D.host.E :=
  depDataOf T EX Tn vd (fun j => wtA (wL j)) (fun j => wtA (wF j)) (fun j => (wL j).n)
    (fun j => ∑ τ, ∑ i, (ka j).aP τ i) fun j => ∑ τ, ∑ i, (ka j).aM τ i

theorem lawsPi_depRun [StarRing (𝓞 D.host.E)] {T : Core D} (h : LawsM T) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j)
    (hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (wL j).n) : LawsPi T (depRun T EX Tn vd wL wF ka) where
  page := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  tPos := tPos_depDataOf ..
  sm := rfl
  wts j hj := ⟨(dom_wtA (wL j)).1, hn j hj⟩
  piSplit := piSplit_depDataOf ..
  piHalf := piHalf_depDataOf _ _ _ _ _ _ _ _ _ h

end Formalism.L2.Pj
