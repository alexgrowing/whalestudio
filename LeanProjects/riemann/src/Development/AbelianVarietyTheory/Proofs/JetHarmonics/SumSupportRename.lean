import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.InvariantDerivationsCommuteFormalConnection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm

namespace GlobalTheory.NabCol

section Fold

variable {ι β : Type}

def fo (D : ι → β → β) (L : List ι) (m : ι →₀ ℕ) (x : β) : β := L.foldr (fun l g => (D l)^[m l] g) x

theorem fo_comm (D : ι → β → β) (L : List ι) (m : ι →₀ ℕ) (T : β → β) (hT : ∀ a, Function.Commute T (D a)) (x : β) :
    T (fo D L m x) = fo D L m (T x) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show T ((D a)^[m a] (fo D L m x)) = (D a)^[m a] (fo D L m (T x))
    rw [← ih]
    exact ((hT a).iterate_right (m a)) _

theorem fo_add (D : ι → β → β) (hD : ∀ a b, Function.Commute (D a) (D b)) (L : List ι) (m m' : ι →₀ ℕ) (x : β) :
    fo D L (m + m') x = fo D L m (fo D L m' x) := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih =>
    show (D a)^[(m + m') a] (fo D L (m + m') x) = (D a)^[m a] (fo D L m ((D a)^[m' a] (fo D L m' x)))
    rw [ih, ← fo_comm D L m ((D a)^[m' a]) (fun b => (hD a b).iterate_left _), Finsupp.add_apply,
      Function.iterate_add_apply]

theorem fo_of_zero (D : ι → β → β) (L : List ι) (m : ι →₀ ℕ) (hm : ∀ a ∈ L, m a = 0) (x : β) : fo D L m x = x := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show (D a)^[m a] (fo D L m x) = x
    rw [hm a (by simp), ih (fun b hb => hm b (by simp [hb]))]
    rfl

theorem fo_single (D : ι → β → β) (L : List ι) (hL : L.Nodup) (a : ι) (ha : a ∈ L) (r : ℕ) (x : β) :
    fo D L (Finsupp.single a r) x = (D a)^[r] x := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    show (D b)^[Finsupp.single a r b] (fo D L (Finsupp.single a r) x) = _
    by_cases hab : a = b
    · subst hab
      rw [Finsupp.single_eq_same, fo_of_zero]
      intro c hc
      exact Finsupp.single_eq_of_ne (fun h => hL.1 (h ▸ hc))
    · rw [Finsupp.single_eq_of_ne (Ne.symm hab), ih hL.2 (by simpa [hab] using ha)]
      rfl

end Fold

variable {k : Type} [CommRing k] {d n : ℕ}

def inCol (b : Fin n) (f : PS k 1 d) : PS k n d := ev (n := n) ![pt k d b] f

theorem gp (b : Fin n) : ∀ j, GP ((![pt k d b] : Fin 1 → Pt k n d) j) := single_point_zero_constant (gp_pt b)

theorem rename_eq (b : Fin n) (f : PS k 1 d) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) f = inCol b f := by
  rw [rename_eq_subst]
  unfold inCol ev
  congr 1
  funext ⟨j, i⟩
  fin_cases j
  rfl

def inColHom (b : Fin n) : PS k 1 d →+* PS k n d := (substAlgHom (gt_hasSubst _ (gp (k := k) (d := d) b))).toRingHom

theorem inColHom_apply (b : Fin n) (f : PS k 1 d) : inColHom b f = inCol b f := by
  simp [inColHom, inCol, ev]

theorem inCol_C (b : Fin n) (r : k) : inCol b (C r : PS k 1 d) = C r := by
  unfold inCol ev
  rw [subst_C]

theorem pderiv_inCol (b c : Fin n) (j : Fin d) (f : PS k 1 d) :
    pderiv k (c, j) (inCol b f) = if b = c then inCol b (pderiv k ((0 : Fin 1), j) f) else 0 := by
  unfold inCol ev
  rw [FormalLog.pderiv_subst (a := fun p : Fin 1 × Fin d => (![pt k d b] : Fin 1 → Pt k n d) p.1 p.2)
    (fun p => gp b p.1 p.2)]
  have e : ∀ p : Fin 1 × Fin d, (![pt k d b] : Fin 1 → Pt k n d) p.1 p.2 = X (b, p.2) := by
    rintro ⟨a, i⟩
    fin_cases a
    rfl
  split_ifs with hbc
  · subst hbc
    rw [Finset.sum_eq_single ((0 : Fin 1), j)]
    · rw [e, pderiv_X_self, mul_one]
    · rintro ⟨a, i⟩ _ hne
      have hb : i ≠ j := fun h => hne (by subst h; rw [Subsingleton.elim a 0])
      rw [e, pderiv_X_of_ne (fun h => hb (congrArg Prod.snd h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun p _ => ?_
    rw [e, pderiv_X_of_ne (fun h => hbc (congrArg Prod.fst h)), mul_zero]

theorem ev_axis (b : Fin n) (g : PS k 2 d) :
    ev (n := n) ![pt k d b, 0] g = inCol b (ev (n := 1) ![pt k d 0, 0] g) := by
  unfold inCol
  rw [gt_ev_ev _ _ (gp b) (pair_points_zero_constant (gp_pt 0) gp_zero₂)]
  congr 1
  funext q i
  fin_cases q
  · exact (gt_ev_X _ (gp b) 0 i).symm
  · exact (gt_ev_zero _ (gp b)).symm

theorem dofN_inCol (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f : PS k 1 d) :
    DofN F b u (inCol b f) = inCol b (Dof F u f) := by
  unfold DofN Dof
  rw [← inColHom_apply b (∑ _, _), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_sum, pderiv_inCol, if_pos rfl, inColHom_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, inColHom_apply, inColHom_apply, inCol_C, ev_axis]

theorem pderiv_prod_out (b : Fin n) (j : Fin d) (g : Fin n → PS k 1 d) (s : Finset (Fin n)) (hs : b ∉ s) :
    pderiv k (b, j) (∏ c ∈ s, inCol c (g c)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert hc, Derivation.leibniz, ih hs.2, pderiv_inCol, if_neg (Ne.symm hs.1)]
    simp

theorem dofN_mul_out (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f G : PS k n d)
    (hG : ∀ j, pderiv k (b, j) G = 0) : DofN F b u (f * G) = DofN F b u f * G := by
  unfold DofN
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, hG, smul_zero, zero_add, smul_eq_mul]
  ring

def colD (F : Fin d → PS k 2 d) (c : Fin n) (u : Fin d → k) (b : Fin n) : PS k 1 d → PS k 1 d :=
  if c = b then Dof F u else id

theorem dofN_prod (F : Fin d → PS k 2 d) (c : Fin n) (u : Fin d → k) (g : Fin n → PS k 1 d) :
    DofN F c u (∏ b, inCol b (g b)) = ∏ b, inCol b (colD F c u b (g b)) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
    dofN_mul_out F c u _ _ (fun j => pderiv_prod_out c j g _ (Finset.notMem_erase c _)), dofN_inCol]
  congr 1
  · simp [colD]
  · refine Finset.prod_congr rfl fun b hb => ?_
    rw [colD, if_neg (Finset.ne_of_mem_erase hb).symm]
    rfl

theorem iter_prod (F : Fin d → PS k 2 d) (c : Fin n) (u : Fin d → k) (r : ℕ) (g : Fin n → PS k 1 d) :
    (DofN F c u)^[r] (∏ b, inCol b (g b)) = ∏ b, inCol b ((colD F c u b)^[r] (g b)) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [Function.iterate_succ_apply', ih, dofN_prod]

theorem dmonN_prod (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ)
    (g : Fin n → PS k 1 d) :
    DmonN F cp u m (∏ b, inCol b (g b)) =
      ∏ b, inCol b (fo (fun l => colD F (cp l) (u l) b) Finset.univ.toList m (g b)) := by
  unfold DmonN fo
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => simp only [List.foldr_cons, ih, iter_prod]

theorem fo_col (F : Fin d → PS k 2 d) (hF : ∀ u v, Function.Commute (Dof F u) (Dof F v)) {Λ Ix : Type} [Fintype Λ]
    [Fintype Ix] (e : Λ × Fin n → Ix) (cp : Ix → Fin n) (u : Λ → Fin d → k) (u' : Ix → Fin d → k)
    (hcp : ∀ p, cp (e p) = p.2) (hu : ∀ p, u' (e p) = u p.1) (b : Fin n) (mo : Λ × Fin n →₀ ℕ) (x : PS k 1 d) :
    fo (fun l => colD F (cp l) (u' l) b) Finset.univ.toList (Finsupp.mapDomain e mo) x =
      DmonOf F u (colM mo b) x := by
  show _ = fo (fun l => Dof F (u l)) Finset.univ.toList (colM mo b) x
  induction mo using Finsupp.induction_linear generalizing x with
  | zero => rw [fo_of_zero _ _ _ (by simp), fo_of_zero _ _ _ (by simp [colM])]
  | add m m' ih ih' =>
    have hc : colM (m + m') b = colM m b + colM m' b := by
      ext l; simp [colM]
    rw [Finsupp.mapDomain_add, hc, fo_add, fo_add _ (fun a a' => hF _ _), ih', ih]
    intro a a'
    unfold colD
    split_ifs
    · exact hF _ _
    · exact Function.Commute.id_right
    · exact Function.Commute.id_left
    · exact Function.Commute.id_left
  | single p r =>
    obtain ⟨l, c⟩ := p
    rw [Finsupp.mapDomain_single, fo_single _ _ (Finset.nodup_toList _) _ (by simp), hcp, hu]
    by_cases hcb : c = b
    · subst hcb
      have hc : colM (Finsupp.single (l, c) r) c = Finsupp.single l r := by
        classical
        ext l'; simp [colM, Finsupp.single_apply]
      rw [hc, fo_single _ _ (Finset.nodup_toList _) _ (by simp)]
      simp [colD]
    · rw [fo_of_zero _ _ _ (fun a _ => by simp [colM, Finsupp.single_apply, hcb])]
      simp [colD, hcb]

theorem cc_inCol (b : Fin n) (f : PS k 1 d) : constantCoeff (inCol b f) = constantCoeff f :=
  gt_const_ev_eq _ (gp b) f

theorem sum_support_eq {ι : Type} (φ : (ι →₀ ℕ) → k) (P : MvPolynomial ι k) :
    ∑ m ∈ P.support, P.coeff m * φ m = (MvPolynomial.basisMonomials ι k).constr k φ P := by
  conv_rhs => rw [P.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : MvPolynomial.monomial m (P.coeff m) = P.coeff m • MvPolynomial.basisMonomials ι k m := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]

theorem sum_support_rename {ι κ : Type} (e : ι → κ) (φ : (κ →₀ ℕ) → k) (P : MvPolynomial ι k) :
    ∑ m ∈ (MvPolynomial.rename e P).support, (MvPolynomial.rename e P).coeff m * φ m =
      ∑ m ∈ P.support, P.coeff m * φ (Finsupp.mapDomain e m) := by
  rw [sum_support_eq]
  conv_lhs => rw [P.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : MvPolynomial.monomial (Finsupp.mapDomain e m) (P.coeff m) =
      P.coeff m • MvPolynomial.basisMonomials κ k (Finsupp.mapDomain e m) := by
    simp [MvPolynomial.smul_monomial]
  rw [MvPolynomial.rename_monomial, this, map_smul, Module.Basis.constr_basis, smul_eq_mul]

theorem expS_sum [Algebra ℚ k] {J : Type} (s : Finset J) (g : J → PS k n d) (hg : ∀ j, constantCoeff (g j) = 0) :
    FB.expS k (∑ j ∈ s, g j) = ∏ j ∈ s, FB.expS k (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    unfold FB.expS
    have hs : PowerSeries.HasSubst (0 : PS k n d) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    ext m
    rw [PowerSeries.coeff_subst hs, finsum_eq_single _ 0]
    · simp
    · intro r hr
      simp [hr]
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.prod_insert hc, gt_expS_add _ _ (hg c) (by simp [hg]), ih]

end GlobalTheory.NabCol

namespace GlobalTheory

open NabCol in

theorem nabValN_boxSer : NabColSt := by
  intro R _ d O _ _ B k _ _ _ h w0 hh q n f Λ Ix _ _ e cp u u' hcp hu P
  have hL0 : constantCoeff (B.hL k h w0) = 0 := by
    refine gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (fun i => ?_) (gp_pt 0))) _ hh
    simp only [FB.actK]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, B.A.const, map_zero]
  have hq0 : constantCoeff ((q : k) • B.hL k h w0) = 0 := by rw [smul_eq_C_mul, map_mul, hL0, mul_zero]
  have hsm : ∀ b : Fin n, (q : k) • ev (n := n) ![pt k d b] (B.hL k h w0) = inCol b ((q : k) • B.hL k h w0) := by
    intro b
    rw [smul_eq_C_mul, smul_eq_C_mul, ← inColHom_apply, map_mul, inColHom_apply, inColHom_apply, inCol_C]
    rfl
  have hprod : boxSer f * FB.expS k ((q : k) • ∑ b : Fin n, ev (n := n) ![pt k d b] (B.hL k h w0)) =
      ∏ b, inCol b (f b * FB.expS k ((q : k) • B.hL k h w0)) := by
    rw [Finset.smul_sum, Finset.sum_congr rfl fun b _ => hsm b,
      expS_sum _ _ (fun b => by rw [cc_inCol, hq0]), boxSer, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [rename_eq, ← inColHom_apply b (_ * _), map_mul, inColHom_apply, inColHom_apply]
    congr 1
    exact (gt_ev_expS _ (gp b) _ hq0).symm
  unfold nabValN DpolyN
  rw [hprod]
  simp only [map_sum, map_mul, constantCoeff_C]
  rw [sum_support_rename e (fun m => constantCoeff (DmonN (B.FK k) cp u' m
    (∏ b, inCol b (f b * FB.expS k ((q : k) • B.hL k h w0)))))]
  refine Finset.sum_congr rfl fun mo _ => ?_
  congr 1
  rw [dmonN_prod, map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [cc_inCol, fo_col (B.FK k) (fun v w g => FormalConnection.invariantDerivations_commute_formal_connection R d O k B v w g) e cp u u' hcp hu]
  unfold FB.nabVal DpolyOf
  simp only [map_sum, map_mul, constantCoeff_C]
  rw [sum_support_eq (fun m => constantCoeff (DmonOf (B.FK k) u m (f b * FB.expS k ((q : k) • B.hL k h w0))))]
  have hb : (MvPolynomial.monomial (colM mo b) 1 : MvPolynomial Λ k) = MvPolynomial.basisMonomials Λ k (colM mo b) := by
    simp
  rw [hb, Module.Basis.constr_basis]

end GlobalTheory
