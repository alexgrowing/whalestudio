import Formalism.LocalToGlobal.CharacterGerms.SubstSubst

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Pull

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_expAll (x : Fin dd) : MvPowerSeries.constantCoeff (expAll Y p x) = 0 := by
  have hu : ∀ f : PS C 1 dd, MvPowerSeries.constantCoeff (un1 f) = MvPowerSeries.constantCoeff f := fun f => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) f = _
    rw [Finsupp.mapDomain_zero]
  unfold expAll
  exact VP.cc_subst (fun _ => by simp [MvPowerSeries.smul_eq_C_mul]) (by rw [hu]; exact Y.ex_const x)

theorem cc_X {σ : Type} (s : σ) : MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries σ C) = 0 := MvPowerSeries.constantCoeff_X s

theorem cc_rowOf {n : ℕ} (b : Fin n) {F : MvPowerSeries (WVO I) C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (rowOf b F) = 0 := by
  unfold rowOf
  exact VP.cc_subst (fun _ => MvPowerSeries.constantCoeff_X _) hF

theorem cc_pullPt {n : ℕ} (q : Fin n × Fin dd) :
    MvPowerSeries.constantCoeff (rowOf q.1 (expAll Y p q.2)) = 0 := cc_rowOf q.1 (cc_expAll Y p q.2)

theorem pullN_mul {n : ℕ} (F G : PS C n dd) : pullN Y p (F * G) = pullN Y p F * pullN Y p G := by
  unfold pullN
  exact VP.subst_mul (cc_pullPt Y p) F G

theorem pullN_prod {n : ℕ} {ι : Type} (s : Finset ι) (F : ι → PS C n dd) :
    pullN Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pullN Y p (F i) := by
  unfold pullN
  exact VP.subst_prod (cc_pullPt Y p) s F

theorem cc_pull1Pt (q : Fin 1 × Fin dd) : MvPowerSeries.constantCoeff (expAll Y p q.2) = 0 := cc_expAll Y p q.2

theorem pullback_one_var_mul (F G : PS C 1 dd) : pull1 Y p (F * G) = pull1 Y p F * pull1 Y p G := by
  unfold pull1
  exact VP.subst_mul (cc_pull1Pt Y p) F G

theorem pullback_one_var_prod {ι : Type} (s : Finset ι) (F : ι → PS C 1 dd) :
    pull1 Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pull1 Y p (F i) := by
  unfold pull1
  exact VP.subst_prod (cc_pull1Pt Y p) s F

theorem pullback_one_var_one : pull1 Y p (1 : PS C 1 dd) = 1 := by
  unfold pull1
  exact VP.subst_one (cc_pull1Pt Y p)

theorem constantCoeff_single_point_zero {n : ℕ} (b : Fin n) (q : Fin 1 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2) = 0 := by
  simp [pt]

theorem pullN_ev {n : ℕ} (b : Fin n) (F : PS C 1 dd) :
    pullN Y p (ev (n := n) ![pt C dd b] F) = rowOf b (pull1 Y p F) := by
  unfold pullN ev pull1
  rw [VP.subst_subst (constantCoeff_single_point_zero b) (cc_pullPt Y p)]
  rw [show rowOf b (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) F) =
      MvPowerSeries.subst (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C))
        (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) F) from rfl]
  rw [VP.subst_subst (fun q : Fin 1 × Fin dd => cc_expAll Y p q.2) (fun _ => MvPowerSeries.constantCoeff_X _)]
  congr 1
  funext q
  rw [Matrix.cons_val_fin_one, show pt C dd b q.2 = (MvPowerSeries.X (b, q.2) : PS C n dd) from rfl,
    VP.subst_X (cc_pullPt Y p)]
  rfl

end Pull

section Emb

variable {n : ℕ}

def eRow (b : Fin n) : WVO I ↪ Fin n × WVO I := ⟨fun w => (b, w), Prod.mk_right_injective b⟩

def eAll (n : ℕ) (o : Orb) : Fin n × WV (I o) ↪ Fin n × WVO I :=
  ⟨fun x => (x.1, (⟨o, x.2⟩ : WVO I)), fun x y h => by
    have h1 : x.1 = y.1 := (Prod.ext_iff.1 h).1
    have h2 : (⟨o, x.2⟩ : WVO I) = ⟨o, y.2⟩ := (Prod.ext_iff.1 h).2
    exact Prod.ext h1 (eq_of_heq (Sigma.mk.inj h2).2)⟩

theorem rowOf_eq (b : Fin n) (F : MvPowerSeries (WVO I) C) : rowOf b F = MvPowerSeries.rename (eRow b) F := by
  unfold rowOf
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem rowOf_toAllS (b : Fin n) (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    rowOf b (toAllS o F) = MvPowerSeries.rename (eAll n o) (rowCopy b F) := by
  have e1 : toAllS o F =
      MvPowerSeries.rename (Function.Embedding.sigmaMk (β := fun o => WV (I o)) o) F := by
    unfold toAllS
    rw [MvPowerSeries.rename_eq_subst]
    rfl
  rw [rowOf_eq, e1, rtj_rowCopy_eq, MvPowerSeries.rename_rename, MvPowerSeries.rename_rename]
  exact rtj_rename_congr (by funext w; rfl) F

theorem rowOf_mul (b : Fin n) (F G : MvPowerSeries (WVO I) C) : rowOf b (F * G) = rowOf b F * rowOf b G := by
  unfold rowOf
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G

theorem rowOf_prod (b : Fin n) {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries (WVO I) C) :
    rowOf b (∏ i ∈ s, F i) = ∏ i ∈ s, rowOf b (F i) := by
  unfold rowOf
  exact VP.subst_prod (fun _ => MvPowerSeries.constantCoeff_X _) s F

theorem toAllS_mul (o : Orb) (F G : MvPowerSeries (WV (I o)) C) : toAllS o (F * G) = toAllS o F * toAllS o G := by
  unfold toAllS
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G

theorem jet_orb (Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C) (Φ : ∀ o, MvPowerSeries (Fin n × WV (I o)) C) :
    jetAt0 (∏ o, toAll o (Po o)) (∏ o, MvPowerSeries.rename (eAll n o) (Φ o)) = ∏ o, jetAt0 (Po o) (Φ o) := by
  have hA : ∀ o ∈ (Finset.univ : Finset Orb), ∀ o' ∈ (Finset.univ : Finset Orb), o ≠ o' →
      Disjoint (Set.range (eAll (I := I) n o)) (Set.range (eAll (I := I) n o')) := by
    intro o _ o' _ h
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact h (congrArg (fun z : Fin n × WVO I => z.2.1) hy).symm
  have hT : ∀ o, toAll o (Po o) = MvPolynomial.rename (eAll n o) (Po o) := fun o => rfl
  exact (rtj_jet_prod (fun o => Set.range (eAll (I := I) n o)) Finset.univ hA
    (fun o => toAll o (Po o)) (fun o => MvPowerSeries.rename (eAll n o) (Φ o))
    (fun o _ => by rw [hT]; exact rtj_rename_supported _ _)
    (fun o _ => rtj_serIn_rename _ _)).trans
    (Finset.prod_congr rfl fun o _ => by rw [hT]; exact rtj_jet_rename _ _ _)

end Emb

end VP

end Formalism.L2.FormalSeriesBounds
