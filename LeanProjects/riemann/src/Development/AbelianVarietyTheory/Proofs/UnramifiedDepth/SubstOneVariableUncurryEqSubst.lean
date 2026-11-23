import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDerivationPolynomialEqJetAt0Statement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdSubstDisjointVariablesStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdmissibleRowsValueEqRowGaugeStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPartStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEndStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegralStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairDataStatement

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal

open MvPowerSeries

theorem pairing_sum {R G : Type} [Ring R] [AddCommGroup G] (N : AddSubgroup G) (IE : R → Prop) (H : R → R → G)
    (Adj : R → R → Prop) (h0 : IE 0) (h1 : IE 1) (hadd : ∀ A B, IE A → IE B → IE (A + B))
    (hmul : ∀ A B, IE A → IE B → IE (A * B)) (hz : ∀ A, H A 0 = 0 ∧ H 0 A = 0)
    (hb : ∀ A A' B, IE A → IE A' → IE B → H A B + H A' B - H (A + A') B ∈ N ∧ H B A + H B A' - H B (A + A') ∈ N)
    (hs : ∀ A B, IE A → IE B → H B A - H A B ∈ N)
    (hadj : ∀ M M' A B, Adj M M' → IE A → IE B → H (M * A) B - H A (M' * B) ∈ N)
    {Orb : Type} [Fintype Orb] (M : Orb → Fin 2 → R) (W W' : R) (hM : ∀ o g, IE (M o g)) (hW : IE W) (hW' : IE W')
    (aW : Adj W W') (aM : ∀ o g, Adj (M o g) (M o (1 - g)))
    (orth : ∀ o g o' g', (o, g) ≠ (o', g') → M o g * (W * M o' g') = 0)
    (tr : ∀ o, W * M o 1 + W' * M o 1 = M o 1) :
    ∑ o, H (M o 0) (M o 1) - H (∑ x : Orb × Fin 2, M x.1 x.2) (W * ∑ x : Orb × Fin 2, M x.1 x.2) ∈ N := by
  classical
  set q := QuotientAddGroup.mk' N with hq
  have qe : ∀ a b : G, a - b ∈ N → q a = q b := fun a b h => by
    rw [← sub_eq_zero, ← map_sub]
    exact (QuotientAddGroup.eq_zero_iff _).2 h
  have b1 : ∀ A A' B, IE A → IE A' → IE B → q (H (A + A') B) = q (H A B) + q (H A' B) := fun A A' B a a' b => by
    rw [← map_add, qe _ _ (hb A A' B a a' b).1]
  have b2 : ∀ A A' B, IE A → IE A' → IE B → q (H B (A + A')) = q (H B A) + q (H B A') := fun A A' B a a' b => by
    rw [← map_add, qe _ _ (hb A A' B a a' b).2]
  have ies : ∀ (s : Finset (Orb × Fin 2)) (A : Orb × Fin 2 → R), (∀ i, IE (A i)) → IE (∑ i ∈ s, A i) := by
    intro s A hA
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact hadd _ _ (hA a) ih
  have s1 : ∀ (s : Finset (Orb × Fin 2)) (A : Orb × Fin 2 → R) (B : R), (∀ i, IE (A i)) → IE B →
      q (H (∑ i ∈ s, A i) B) = ∑ i ∈ s, q (H (A i) B) := by
    intro s A B hA hB
    induction s using Finset.induction_on with
    | empty => simp [(hz B).2]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, b1 _ _ _ (hA a) (ies s A hA) hB, ih]
  have s2 : ∀ (s : Finset (Orb × Fin 2)) (A : Orb × Fin 2 → R) (B : R), (∀ i, IE (A i)) → IE B →
      q (H B (∑ i ∈ s, A i)) = ∑ i ∈ s, q (H B (A i)) := by
    intro s A B hA hB
    induction s using Finset.induction_on with
    | empty => simp [(hz B).1]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, b2 _ _ _ (hA a) (ies s A hA) hB, ih]
  have hWM : ∀ x : Orb × Fin 2, IE (W * M x.1 x.2) := fun x => hmul _ _ hW (hM _ _)
  rw [← QuotientAddGroup.eq_zero_iff]
  change q _ = 0
  rw [map_sub, map_sum, Finset.mul_sum, s1 _ _ _ (fun x => hM x.1 x.2) (ies _ _ hWM), sub_eq_zero,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  have one : ∀ g : Fin 2, q (H (M o g) (∑ x : Orb × Fin 2, W * M x.1 x.2)) = q (H (M o g) (W * M o (1 - g))) := by
    intro g
    rw [s2 _ _ _ hWM (hM o g), Finset.sum_eq_single (o, 1 - g)]
    · intro x _ hx
      have e := qe _ _ (hadj _ _ 1 (W * M x.1 x.2) (aM o g) h1 (hWM x))
      rw [mul_one, orth o (1 - g) x.1 x.2 (Ne.symm hx), (hz 1).1, map_zero] at e
      exact e
    · simp
  rw [Fin.sum_univ_two, one, one]
  have e10 : (1 - 0 : Fin 2) = 1 := by decide
  have e11 : (1 - 1 : Fin 2) = 0 := by decide
  rw [e10, e11, qe _ _ (hs (W * M o 0) (M o 1) (hmul _ _ hW (hM _ _)) (hM _ _)),
    qe _ _ (hadj W W' (M o 0) (M o 1) aW (hM _ _) (hM _ _)),
    ← b2 _ _ _ (hmul _ _ hW (hM _ _)) (hmul _ _ hW' (hM _ _)) (hM _ _), tr]

variable {C : Type} [Field C]

theorem subst_oneVariableUncurry_eq_subst {dd : ℕ} {τ : Type} (a : Fin dd → MvPowerSeries τ C)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : PS C 1 dd) :
    subst a (un1 f) = subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  let ι : Fin dd ≃ Fin 1 × Fin dd :=
    { toFun := fun x => (0, x)
      invFun := fun p => p.2
      left_inv := fun _ => rfl
      right_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl }
  ext μ
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin dd => ha p.2),
    ← finsum_comp_equiv (Finsupp.equivCongrLeft ι)]
  refine finsum_congr fun e => ?_
  rw [Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain, Finsupp.equivMapDomain_eq_mapDomain]
  rfl

theorem subst_sum_smul {σ τ α : Type} [Finite σ] [Fintype α] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (c : α → C) (F : α → MvPowerSeries σ C) :
    subst a (∑ i, c i • F i) = ∑ i, c i • subst a (F i) := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [← coe_substAlgHom hs, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [coe_substAlgHom hs, subst_smul hs]

theorem subst_prod' {σ τ α : Type} [Finite σ] [Fintype α] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (F : α → MvPowerSeries σ C) :
    subst a (∏ i, F i) = ∏ i, subst a (F i) := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [← coe_substAlgHom hs, map_prod]

theorem subst_sum'' {σ τ α : Type} [Finite σ] [Fintype α] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (F : α → MvPowerSeries σ C) :
    subst a (∑ i, F i) = ∑ i, subst a (F i) := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [← coe_substAlgHom hs, map_sum]

theorem subst_subst {σ τ υ : Type} [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries υ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (F : MvPowerSeries σ C) :
    subst b (subst a F) = subst (fun s => subst b (a s)) F :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (hasSubst_of_constantCoeff_zero hb) F

section Law

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem cc_lg (hX : RLaw X V) (i : κ) : constantCoeff (X.lg i) = 0 := by
  have := hX.lin i 0 (by simp)
  simpa using this

theorem cc_lin (A : Matrix κ κ C) {τ : Type} {Z : κ → MvPowerSeries τ C} (hZ : ∀ i, constantCoeff (Z i) = 0) (x : κ) :
    constantCoeff (∑ y, A x y • Z y) = 0 := by
  simp [map_sum, hZ]

theorem endP_X (A : Matrix κ κ C) (i : κ) :
    endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i = subst (fun x => ∑ y, A x y • X.lg y) (X.ex i) := by
  unfold endP
  simp only [subst_self, id]

theorem cc_endP (hX : RLaw X V) (A : Matrix κ κ C) (i : κ) :
    constantCoeff (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i) = 0 := by
  rw [endP_X, cc_subst (cc_lin A (cc_lg hX)), hX.exc]

theorem intEnd_one [DecidableEq κ] (hX : RLaw X V) : IntEnd X V 1 := by
  intro i
  have e : (fun x => ∑ y, (1 : Matrix κ κ C) x y • X.lg y) = X.lg := by
    funext x
    simp [Matrix.one_apply]
  rw [endP_X, e, hX.exlg]
  exact intS_X i

theorem subst_endP (hX : RLaw X V) (A : Matrix κ κ C) {τ : Type} {Z : κ → MvPowerSeries τ C}
    (hZ : ∀ i, constantCoeff (Z i) = 0) (i : κ) :
    subst (fun j => subst Z (X.ex j)) (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i) =
      subst (fun x => ∑ y, A x y • Z y) (X.ex i) := by
  have hE : ∀ j, constantCoeff (subst Z (X.ex j)) = 0 := fun j => by rw [cc_subst hZ, hX.exc]
  rw [endP_X, subst_subst (cc_lin A (cc_lg hX)) hE]
  congr 1
  funext x
  rw [subst_sum_smul hE]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← subst_subst hX.exc hZ, hX.lgex, subst_X (hasSubst_of_constantCoeff_zero hZ)]

theorem subst_two (hX : RLaw X V) (A : Fin 2 → Matrix κ κ C) {τ : Type} {Z : κ → MvPowerSeries τ C}
    (hZ : ∀ i, constantCoeff (Z i) = 0) (f : MvPowerSeries (Fin 2 × κ) C) :
    subst (fun j => subst Z (X.ex j))
        (subst (fun s : Fin 2 × κ => endP X (A s.1) (MvPowerSeries.X : κ → MvPowerSeries κ C) s.2) f) =
      subst (fun s : Fin 2 × κ => subst (fun x => ∑ y, A s.1 x y • Z y) (X.ex s.2)) f := by
  have hE : ∀ j, constantCoeff (subst Z (X.ex j)) = 0 := fun j => by rw [cc_subst hZ, hX.exc]
  rw [subst_subst (fun s => cc_endP hX _ _) hE]
  congr 1
  funext s
  exact subst_endP hX _ hZ _

theorem hEnd_eq (A B : Matrix κ κ C) : hEnd X A B =
    subst (fun s : Fin 2 × κ => endP X (![A, B] s.1) (MvPowerSeries.X : κ → MvPowerSeries κ C) s.2) X.h := by
  unfold hEnd hAt
  congr 1
  funext ⟨g, x⟩
  fin_cases g <;> simp

end Law

section Row

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o))

def genVec {τ : Type} (v : WVO I → τ) (j : Fin dd) : MvPowerSeries τ C :=
  ∑ w : WVO I, (p w.1).u w.2.1 w.2.2 j • (X (v w) : MvPowerSeries τ C)

omit [NeZero d] in
theorem cc_genVec {τ : Type} (v : WVO I → τ) (j : Fin dd) : constantCoeff (genVec Y p v j) = 0 := by
  simp [genVec, map_sum]

omit [NeZero d] in
theorem lin_genVec {τ : Type} (v : WVO I → τ) (A : Matrix (Fin dd) (Fin dd) C) (x : Fin dd) :
    ∑ y, A x y • genVec Y p v y =
      ∑ w : WVO I, A.mulVec ((p w.1).u w.2.1 w.2.2) x • (X (v w) : MvPowerSeries τ C) := by
  simp only [genVec, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

theorem cc_hL (a : O) : constantCoeff (Y.B.hL C Y.h a) = 0 := by
  unfold FB.hL ev
  rw [cc_subst, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h Y.gauge]
  rintro ⟨g, x⟩
  fin_cases g
  · simp [pt]
  · show constantCoeff (comp1 (Y.B.actK C a) (pt C dd 0) x) = 0
    unfold comp1 ev
    rw [cc_subst]
    · show constantCoeff (MvPowerSeries.map (algebraMap C C) (Y.B.A.act a x)) = 0
      rw [GlobalTheory.GaugeCocycle.map_self, Y.B.A.const]
    · rintro ⟨g, x⟩
      fin_cases g
      simp [pt]

theorem cc_ex (i : Fin dd) : constantCoeff (un1 (Y.ex i)) = 0 := by
  rw [constantCoeff_uncurry, Y.ex_const]

omit [NeZero d] in
theorem cc_hRow (o : Orb) : constantCoeff (Y.raw (p o)).hRow = 0 := by
  unfold RawChart.hRow
  rw [constantCoeff_smul, cc_subst (fun s : Fin 2 × Fin dd => ((Y.raw (p o)).van_expPt (cc_ex Y) s.1 s.2).const)]
  show _ • constantCoeff Y.h = 0
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h Y.gauge, smul_zero]

set_option maxHeartbeats 400000 in

theorem one_row (hs : PairsSep Y p) (gr : ∀ o, MvPowerSeries (WV (I o)) C)
    (hg : ∀ o, gr o ∈ ExpInt (Y.raw (p o)) V) :
    ∃ f : MvPowerSeries (Fin dd) C, IntS V f ∧ ∀ (τ : Type) (v : WVO I → τ),
      subst (fun i => subst (genVec Y p v) (un1 (Y.ex i))) (f * mvExp ((Y.k : C) • un1 (Y.B.hL C Y.h Y.w0))) =
        ∏ o, subst (fun x : WV (I o) => (X (v ⟨o, x⟩) : MvPowerSeries τ C)) (gr o * mvExp (Y.raw (p o)).hRow) := by
  classical
  have cL : constantCoeff ((Y.k : C) • un1 (Y.B.hL C Y.h Y.w0)) = 0 := by
    rw [constantCoeff_smul, constantCoeff_uncurry, cc_hL, smul_zero]
  have cE : ∀ (τ : Type) (v : WVO I → τ) i, constantCoeff (subst (genVec Y p v) (un1 (Y.ex i))) = 0 :=
    fun τ v i => by rw [cc_subst (cc_genVec Y p v), cc_ex]
  rcases isEmpty_or_nonempty Orb with hO | ⟨⟨o0⟩⟩
  · refine ⟨1, intS_one, fun τ v => ?_⟩
    have hz : ∀ {F : MvPowerSeries (Fin dd) C}, constantCoeff F = 0 →
        subst (fun _ : Fin dd => (0 : MvPowerSeries τ C)) F = 0 := by
      intro F hF
      have hV : Van (∅ : Set τ) (subst (fun _ : Fin dd => (0 : MvPowerSeries τ C)) F) := by
        refine Van.subst Set.univ (fun _ => map_zero _) (fun _ _ _ _ => map_zero _) fun e he => ?_
        have he0 : e = 0 := by
          rw [← Finsupp.support_eq_empty]
          exact Finset.eq_empty_of_forall_notMem fun s hs => he s hs (Set.mem_univ s)
        rw [he0, coeff_zero_eq_constantCoeff_apply, hF]
      ext μ
      exact hV μ fun _ _ h => h
    have e0 : genVec Y p v = fun _ => 0 := by
      funext j
      simp [genVec]
    have e1 : (fun i => subst (genVec Y p v) (un1 (Y.ex i))) = fun _ => 0 := by
      funext i
      rw [e0, hz (cc_ex Y i)]
    rw [one_mul, subst_mvExp (cE τ v) cL, e1, hz cL, mvExp_zero']
    simp
  obtain ⟨M, hadj, hfix, hkill, himg⟩ := GlobalTheory.T.exists_orthogonal_adjoint_projectors_placePairs C V O dd Y d Orb I p hs
  have hX := GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d (I o0) (p o0)
  obtain ⟨W, W', hW, hW', aW, hL⟩ := GlobalTheory.T.exists_integralEnd_of_action_linearPart C V O dd Y d (I o0) (p o0) Y.w0
  obtain ⟨c0, cadd, cmul, cz, cb, cs, cadj⟩ := GlobalTheory.T.gauge_biadditive_symm_adjoint_integralEnd C V d (I o0) (Fin dd) (Y.raw (p o0)) hX
  have aM : ∀ o g, IsEnd (Y.raw (p o0)) V (M o g) (M o (1 - g)) := by
    intro o g
    fin_cases g
    · exact (hadj o).1
    · exact (hadj o).2
  have iM : ∀ o g, IntEnd (Y.raw (p o0)) V (M o g) := fun o g => (aM o g).1
  have mext : ∀ {A B : Matrix (Fin dd) (Fin dd) C}, (∀ v, A.mulVec v = B.mulVec v) → A = B := fun h =>
    Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using h v)
  have uW : ∀ o g c, W.mulVec ((p o).u g c) = (p o).em g ((p o).ty g c) Y.w0 • (p o).u g c :=
    fun o g c => by rw [hW, (p o).u_eig]
  have uW' : ∀ o g c, W'.mulVec ((p o).u g c) = (p o).em g ((p o).ty g c) (star Y.w0) • (p o).u g c :=
    fun o g c => by rw [hW', (p o).u_eig]
  have orth : ∀ o g o' g', (o, g) ≠ (o', g') → M o g * (W * M o' g') = 0 := by
    intro o g o' g' hne
    refine mext fun v => ?_
    obtain ⟨b, hb⟩ := himg o' g' v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, uW, hkill o g o' g' _ hne]
    simp
  have tr : ∀ o, W * M o 1 + W' * M o 1 = M o 1 := by
    intro o
    refine mext fun v => ?_
    obtain ⟨b, hb⟩ := himg o 1 v
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, uW, uW', ← Finset.sum_add_distrib, ← smul_add,
      ← add_smul, ← map_add, Y.halfIntegralGenerator_add_conj_eq_one, map_one, one_smul]
  have key := pairing_sum (logInt V (Fin dd)) (IntEnd (Y.raw (p o0)) V) (hEnd (Y.raw (p o0)))
    (IsEnd (Y.raw (p o0)) V) c0 (intEnd_one hX) cadd cmul cz cb cs cadj M W W' iM aW.1 aW.2.1 aW aM orth tr
  set e := ∑ x : Orb × Fin 2, M x.1 x.2 with he
  set D := ∑ o, hEnd (Y.raw (p o0)) (M o 0) (M o 1) - hEnd (Y.raw (p o0)) e (W * e) with hD
  have kD : (Y.k : C) • D ∈ logInt V (Fin dd) := by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem key _
  choose F hF hFe using hg
  have iF : ∀ o, IntS V (subst (fun s : Fin 2 × Fin dd => endP (Y.raw (p o0)) (M o s.1)
      (X : Fin dd → MvPowerSeries (Fin dd) C) s.2) (F o)) := fun o =>
    intS_subst (a := fun s : Fin 2 × Fin dd => endP (Y.raw (p o0)) (M o s.1)
      (X : Fin dd → MvPowerSeries (Fin dd) C) s.2) (fun s => cc_endP hX (M o s.1) s.2) (fun s => iM o s.1 s.2) (hF o)
  refine ⟨(∏ o, subst (fun s : Fin 2 × Fin dd => endP (Y.raw (p o0)) (M o s.1)
    (X : Fin dd → MvPowerSeries (Fin dd) C) s.2) (F o)) * mvExp ((Y.k : C) • D),
    intS_mul (intS_prod _ iF) kD.2, fun τ v => ?_⟩
  have hZ := cc_genVec Y p v
  have hE := cE τ v
  have hEs := hasSubst_of_constantCoeff_zero hE
  have cU : ∀ o (x : WV (I o)), constantCoeff (X (v ⟨o, x⟩) : MvPowerSeries τ C) = 0 := fun o x => constantCoeff_X _
  have two : ∀ (A : Fin 2 → Matrix (Fin dd) (Fin dd) C) (f : MvPowerSeries (Fin 2 × Fin dd) C),
      subst (fun i => subst (genVec Y p v) (un1 (Y.ex i)))
        (subst (fun s : Fin 2 × Fin dd => endP (Y.raw (p o0)) (A s.1) (X : Fin dd → MvPowerSeries (Fin dd) C) s.2) f) =
      subst (fun s : Fin 2 × Fin dd => subst (fun x => ∑ w : WVO I,
        (A s.1).mulVec ((p w.1).u w.2.1 w.2.2) x • (X (v w) : MvPowerSeries τ C)) (un1 (Y.ex s.2))) f := by
    intro A f
    have := subst_two hX A hZ f
    simp only [lin_genVec] at this
    exact this
  have proj : ∀ o (f : MvPowerSeries (Fin 2 × Fin dd) C),
      subst (fun i => subst (genVec Y p v) (un1 (Y.ex i)))
        (subst (fun s : Fin 2 × Fin dd => endP (Y.raw (p o0)) (M o s.1) (X : Fin dd → MvPowerSeries (Fin dd) C) s.2) f) =
      subst (fun x : WV (I o) => (X (v ⟨o, x⟩) : MvPowerSeries τ C))
        (subst (fun s : Fin 2 × Fin dd => (Y.raw (p o)).expPt s.1 s.2) f) := by
    intro o f
    rw [two (M o), subst_subst (fun s : Fin 2 × Fin dd => ((Y.raw (p o)).van_expPt (cc_ex Y) s.1 s.2).const) (cU o)]
    congr 1
    funext ⟨g, i⟩
    unfold RawChart.expPt
    rw [subst_subst (fun i => (RawChart.van_lin g _).const) (cU o)]
    congr 1
    funext x
    rw [subst_sum_smul (cU o), Fintype.sum_sigma, Finset.sum_eq_single o, Fintype.sum_sigma, Finset.sum_eq_single g]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [subst_X (hasSubst_of_constantCoeff_zero (cU o))]
      dsimp only
      rw [hfix]
      rfl
    · intro g' _ hg'
      refine Finset.sum_eq_zero fun c _ => ?_
      dsimp only
      rw [hkill o g o g' c (by simp [Ne.symm hg'])]
      simp
    · simp
    · intro o' _ ho'
      refine Finset.sum_eq_zero fun w _ => ?_
      dsimp only
      rw [hkill o g o' w.1 w.2 (by simp [Ne.symm ho'])]
      simp
    · simp
  have eu : ∀ w : WVO I, e.mulVec ((p w.1).u w.2.1 w.2.2) = (p w.1).u w.2.1 w.2.2 := by
    intro w
    rw [he, Matrix.sum_mulVec, Finset.sum_eq_single (w.1, w.2.1), hfix]
    · intro x _ hx
      exact hkill x.1 x.2 _ _ _ hx
    · simp
  have same : subst (fun i => subst (genVec Y p v) (un1 (Y.ex i))) (hEnd (Y.raw (p o0)) e (W * e)) =
      subst (fun i => subst (genVec Y p v) (un1 (Y.ex i))) (hEnd (Y.raw (p o0)) 1 W) := by
    rw [hEnd_eq e (W * e), hEnd_eq 1 W, two ![e, W * e], two ![1, W]]
    congr 1
    funext ⟨g, i⟩
    fin_cases g
    · simp [eu]
    · simp [eu, ← Matrix.mulVec_mulVec]
  have hrow : ∀ o, (Y.k : C) • subst (fun i => subst (genVec Y p v) (un1 (Y.ex i)))
      (hEnd (Y.raw (p o0)) (M o 0) (M o 1)) =
      subst (fun x : WV (I o) => (X (v ⟨o, x⟩) : MvPowerSeries τ C)) (Y.raw (p o)).hRow := by
    intro o
    have e2 : ![M o 0, M o 1] = M o := by
      funext g
      fin_cases g <;> rfl
    rw [hEnd_eq (M o 0) (M o 1), e2, proj o, RawChart.hRow, subst_smul (hasSubst_of_constantCoeff_zero (cU o))]
    rfl
  rw [mul_assoc, ← mvExp_add kD.1 cL, subst_mul hEs, subst_mvExp hE (by rw [map_add, kD.1, cL, add_zero]),
    subst_prod' hE, subst_add hEs, subst_smul hEs, subst_smul hEs, hL, hD, subst_sub hEs, same, ← smul_add,
    sub_add_cancel, subst_sum'' hE, Finset.smul_sum]
  simp only [hrow]
  rw [mvExp_sum _ fun o => by rw [cc_subst (cU o), cc_hRow], ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [subst_mul (hasSubst_of_constantCoeff_zero (cU o)), subst_mvExp (cU o) (cc_hRow Y p o), proj o, ← hFe o]

end Row

section Rows

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o))

omit [NeZero d] in
theorem deriv_genVec {n : ℕ} (b : Fin n) (u : Fin dd → C) (co : WVO I → C)
    (hu : u = ∑ w : WVO I, co w • (p w.1).u w.2.1 w.2.2) (b' : Fin n) (j : Fin dd) :
    ∑ x : Fin n × WVO I, (if x.1 = b then co x.2 else 0) •
        pderiv C x (genVec Y p (fun w : WVO I => (b', w)) j) =
      if b' = b then MvPowerSeries.C (u j) else 0 := by
  classical
  have h1 : ∀ x : Fin n × WVO I, pderiv C x (genVec Y p (fun w : WVO I => (b', w)) j) =
      if x.1 = b' then MvPowerSeries.C ((p x.2.1).u x.2.2.1 x.2.2.2 j) else 0 := by
    rintro ⟨ρ, w⟩
    unfold genVec
    rw [map_sum, Finset.sum_eq_single w]
    · rw [Derivation.map_smul]
      by_cases h : ρ = b'
      · subst h
        simp [smul_eq_C_mul]
      · rw [pderiv_X_of_ne (by simp [Ne.symm h]), if_neg h, smul_zero]
    · intro w' _ hw'
      rw [Derivation.map_smul, pderiv_X_of_ne (by simp [hw']), smul_zero]
    · simp
  simp only [h1]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · by_cases h : b' = b
    · subst h
      simp [hu, map_sum, smul_eq_C_mul]
    · simp [h, Ne.symm h]
  · intro ρ _ hρ
    simp [hρ]
  · simp

theorem all_rows (n : ℕ) (gr : ∀ o, Fin n → MvPowerSeries (WV (I o)) C) (f : Fin n → MvPowerSeries (Fin dd) C)
    (hf : ∀ ρ (v : WVO I → Fin n × WVO I),
      subst (fun i => subst (genVec Y p v) (un1 (Y.ex i))) (f ρ * mvExp ((Y.k : C) • un1 (Y.B.hL C Y.h Y.w0))) =
        ∏ o, subst (fun x : WV (I o) => (X (v ⟨o, x⟩) : MvPowerSeries (Fin n × WVO I) C))
          (gr o ρ * mvExp (Y.raw (p o)).hRow)) :
    subst (fun s : Fin n × Fin dd => subst (genVec Y p fun w : WVO I => (s.1, w)) (un1 (Y.ex s.2)))
      ((∏ ρ, subst (fun i : Fin dd => (X (ρ, i) : PS C n dd)) (f ρ)) *
        FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))) =
      ∏ o, subst (fun x : Fin n × WV (I o) => (X (x.1, (⟨o, x.2⟩ : WVO I)) : MvPowerSeries (Fin n × WVO I) C))
        (∏ ρ, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.raw (p o)).hRow))) := by
  have cL : constantCoeff ((Y.k : C) • un1 (Y.B.hL C Y.h Y.w0)) = 0 := by
    rw [constantCoeff_smul, constantCoeff_uncurry, cc_hL, smul_zero]
  have cX : ∀ (ρ : Fin n) (i : Fin dd), constantCoeff (X (ρ, i) : PS C n dd) = 0 := fun _ _ => constantCoeff_X _
  have hE : ∀ s : Fin n × Fin dd,
      constantCoeff (subst (genVec Y p fun w : WVO I => (s.1, w)) (un1 (Y.ex s.2))) = 0 :=
    fun s => by rw [cc_subst (cc_genVec Y p _), cc_ex]
  have e1 : (Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0) =
      ∑ b : Fin n, subst (fun i : Fin dd => (X (b, i) : PS C n dd)) ((Y.k : C) • un1 (Y.B.hL C Y.h Y.w0)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [subst_smul (hasSubst_of_constantCoeff_zero (cX b)), subst_oneVariableUncurry_eq_subst _ (cX b)]
    unfold ev
    congr 2
    funext ⟨g, x⟩
    fin_cases g
    rfl
  have c2 : ∀ b : Fin n, constantCoeff (subst (fun i : Fin dd => (X (b, i) : PS C n dd))
      ((Y.k : C) • un1 (Y.B.hL C Y.h Y.w0))) = 0 := fun b => by rw [cc_subst (cX b), cL]
  rw [e1, FB.expS, ← mvExp_eq_subst (by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => c2 b), mvExp_sum _ c2,
    ← Finset.prod_mul_distrib, subst_prod' hE]
  have cU : ∀ o (x : Fin n × WV (I o)),
      constantCoeff (X (x.1, (⟨o, x.2⟩ : WVO I)) : MvPowerSeries (Fin n × WVO I) C) = 0 :=
    fun _ _ => constantCoeff_X _
  have e2 : ∀ o, subst (fun x : Fin n × WV (I o) => (X (x.1, (⟨o, x.2⟩ : WVO I)) : MvPowerSeries (Fin n × WVO I) C))
        (∏ ρ, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.raw (p o)).hRow))) =
      ∏ ρ, subst (fun x : WV (I o) => (X (ρ, (⟨o, x⟩ : WVO I)) : MvPowerSeries (Fin n × WVO I) C))
          (gr o ρ * mvExp (Y.raw (p o)).hRow) := by
    intro o
    rw [subst_prod' (cU o)]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    have cR : ∀ w : WV (I o), constantCoeff (X (ρ, w) : MvPowerSeries (Fin n × WV (I o)) C) = 0 :=
      fun _ => constantCoeff_X _
    unfold rowCopy
    rw [← subst_mvExp cR (cc_hRow Y p o), ← subst_mul (hasSubst_of_constantCoeff_zero cR), subst_subst cR (cU o)]
    congr 1
    funext w
    rw [subst_X (hasSubst_of_constantCoeff_zero (cU o))]
  simp only [e2]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [← subst_mvExp (cX ρ) cL, ← subst_mul (hasSubst_of_constantCoeff_zero (cX ρ)), subst_subst (cX ρ) hE,
    ← hf ρ fun w => (ρ, w)]
  congr 1
  funext i
  rw [subst_X (hasSubst_of_constantCoeff_zero hE)]

end Rows

theorem value_eq_prod : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ), ValEqPSt Y p H Ls n := by
  intro C _ _ V O _ _ dd Y d _ Orb _ I _ p H Ls n hs P _ Po hQ kind hk S t ht gr hg
  classical
  have hg' : ∀ ρ o, gr o ρ ∈ ExpInt (Y.raw (p o)) V := fun ρ o => by
    rw [← GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral C V d (I o) (Fin dd) (Y.raw (p o)) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d (I o) (p o)) (H o).cartH (S o) (t o)
      (ht o)]
    exact hg o ρ
  choose f hfi hf using fun ρ => one_row Y p hs (fun o => gr o ρ) (hg' ρ)
  refine ⟨∏ ρ, subst (fun i : Fin dd => (X (ρ, i) : PS C n dd)) (f ρ),
    intS_prod _ fun ρ => intS_subst (fun _ => constantCoeff_X _) (fun _ => intS_X _) (hfi ρ), ?_⟩
  obtain ⟨co, hco, hQ⟩ := hQ
  have hE : ∀ s : Fin n × Fin dd,
      constantCoeff (subst (genVec Y p fun w : WVO I => (s.1, w)) (un1 (Y.ex s.2))) = 0 :=
    fun s => by rw [cc_subst (cc_genVec Y p _), cc_ex]
  have hj := GlobalTheory.T.constantCoeff_derivationPolynomial_eq_jetAt0 C dd n (Y.B.FK C) (Ls.ι n) (Ls.cp n) (Ls.uv n) (Fin n × WVO I) _ hE
    (fun ℓ x => if x.1 = Ls.cp n ℓ then co ℓ x.2 else 0) P (fun ℓ hℓ G =>
      GlobalTheory.T.invariantDerivations_constant_in_logCoordinates C V O dd Y n (Fin n × WVO I) (fun s => genVec Y p (fun w : WVO I => (s.1, w)) s.2)
        (fun s => cc_genVec Y p _ _) (Ls.cp n ℓ) (Ls.uv n ℓ) _
        (deriv_genVec Y p (Ls.cp n ℓ) (Ls.uv n ℓ) (co ℓ) (hco ℓ hℓ)) G)
  have e1 : (fun ℓ => ∑ x : Fin n × WVO I, MvPolynomial.C (if x.1 = Ls.cp n ℓ then co ℓ x.2 else 0) *
      (MvPolynomial.X x : MvPolynomial (Fin n × WVO I) C)) =
      fun ℓ => ∑ w : WVO I, MvPolynomial.C (co ℓ w) * MvPolynomial.X (Ls.cp n ℓ, w) := by
    funext ℓ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Ls.cp n ℓ)]
    · simp
    · intro ρ _ hρ
      simp [hρ]
    · simp
  unfold FBChart.nab nabValN
  rw [hj, e1, ← hQ, all_rows Y p n gr f fun ρ v => hf ρ _ v]
  have hp := GlobalTheory.T.jetAt0_prod_subst_disjoint_variables C Orb (fun o => Fin n × WV (I o)) (Fin n × WVO I)
    (fun o x => (x.1, (⟨o, x.2⟩ : WVO I))) (by
      rintro ⟨o, ρ, w⟩ ⟨o', ρ', w'⟩ h
      simp only [Prod.mk.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, rfl, h⟩ := h
      rw [eq_of_heq h]) Po
    (fun o => ∏ ρ, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.raw (p o)).hRow)))
  refine hp.trans (Finset.prod_congr rfl fun o _ => ?_)
  exact (GlobalTheory.T.admissibleRows_value_eq_rowGauge C V d (I o) (Fin dd) (Y.raw (p o)) (H o) n (Po o) (kind o) (hk o) (gr o)).symm

end GlobalTheory.RowVal
