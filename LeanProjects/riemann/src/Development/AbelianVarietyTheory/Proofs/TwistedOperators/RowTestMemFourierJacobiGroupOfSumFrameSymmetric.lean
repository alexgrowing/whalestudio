import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowRepLoc
open GlobalTheory.LocGrp GlobalTheory.LocMod

private lemma lev_le_of_sum_elim_le {σ p' : ℕ} (hp : p' = σ ∨ p' = σ + 1) {n : Type} (r s : n ⊕ Fin (2 * σ))
    (h : (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2) : n ⊕ Fin (2 * σ) → ℕ) s ≤
      (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2) : n ⊕ Fin (2 * σ) → ℕ) r) :
    GlobalTheory.RootEx.lev p' s ≤ GlobalTheory.RootEx.lev p' r := by

  rcases hp with rfl | rfl <;> rcases r with r | r <;> rcases s with s | s <;>
    simp only [Sum.elim_inl, Sum.elim_inr, GlobalTheory.RootEx.lev] at h ⊢ <;> (try split_ifs at h) <;> omega

private lemma mul_apply_eq_of_mul_eq_of_col_eq {K : Type} [Field K] {m n n' : Type} [Fintype m] (M : Matrix m m K) (X : Matrix m n K)
    (Y : Matrix m n' K) (hX : M * X = X) (i : n) (j : n') (hc : ∀ t, X t i = Y t j) (r : m) : (M * Y) r j = Y r j := by

  have h := congrFun (congrFun hX r) i
  simp only [Matrix.mul_apply, hc] at h ⊢
  exact h

theorem mem_jac {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    {A B : HSp D} {σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B (2 * σ) ε)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) k} (hb : b * b' = 1) (hb' : b' * b = 1) {u : Fin (2 * σ) → k}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ)) (Fin B.rank) k} (h1 : Γ * sumCols d p.π b u = 1) (h2 : sumCols d p.π b u * Γ = 1)
    {g : GA D B} (hg : SuppAt p.e B g) {x : GL (Fin A.rank ⊕ Fin (2 * σ)) k}
    (e : x.val = Γ * ((mt B g).map p.π * sumCols d p.π b u)) (hx : x ∈ symR k (Fin A.rank) (2 * σ)) :
    g ∈ jacGrp (jacDec d rfl) := by
  classical
  have hS : ∀ r (j : Fin (2 * σ)), sumCols d p.π b u r (Sum.inr j) = p.π (incA D (d.a r j)) * u j := by
    intro r j
    simp only [sumCols, Matrix.fromCols_apply_inr, Matrix.mul_diagonal, Matrix.map_apply, RingHom.comp_apply]
  let F : Frame k B.rank (Fin A.rank ⊕ Fin (2 * σ)) := ⟨sumCols d p.π b u, Γ, h2, h1⟩
  let FA : Frame k A.rank (Fin A.rank) := ⟨b, b', hb, hb'⟩
  obtain ⟨φ, hφ⟩ := exists_hom p F
  have hgx : p.IsLoc F g x := by
    refine ⟨hg, ?_⟩
    show (mt B g).map p.π = sumCols d p.π b u * x.val * Γ
    rw [e]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [isLoc_unique p hgx (hφ x)]

  have hfix : ∀ g₀ : GA D A, (mt B ((jacDec d rfl).emb0 g₀)).map p.π * d.a.map (p.π.comp (incA D)) =
      d.a.map (p.π.comp (incA D)) := by
    intro g₀
    have hX := map_fix p (HypDec.wittDecomp_anisotropicEmbedding_inclX (d := jacDec d rfl) (g := g₀))
    have hY := map_fix p (HypDec.wittDecomp_anisotropicEmbedding_inclY (d := jacDec d rfl) (g := g₀))
    ext r j
    by_cases hj : j.val < σ
    · exact mul_apply_eq_of_mul_eq_of_col_eq _ _ _ hX ⟨j.val, hj⟩ j (fun t => rfl) r
    · refine mul_apply_eq_of_mul_eq_of_col_eq _ _ _ hY ⟨2 * σ - 1 - j.val, by omega⟩ j (fun t => ?_) r
      show p.π (incA D ((jacDec d rfl).e' t ⟨2 * σ - 1 - j.val, by omega⟩)) = p.π (incA D (d.a t j))
      dsimp only [jacDec, Matrix.submatrix_apply, id]
      congr 3
      apply Fin.ext
      simp
      omega
  have hN : ∀ p', (p' = σ ∨ p' = σ + 1) → GlobalTheory.RootEx.N k (Fin A.rank) (2 * σ) p' ≤ (jacGrp (jacDec d rfl)).comap φ := by
    intro p' hp'
    unfold GlobalTheory.RootEx.N
    rw [Subgroup.closure_le]
    intro q hq
    show φ q ∈ flagN (jacDec d rfl) ⊔ (jacDec d rfl).emb0.range
    refine Subgroup.mem_sup_left (flag_of_strict p (jacDec d rfl) FA F
      (Sum.elim (fun a => Sum.inl a) (Sum.elim (fun i : Fin σ => Sum.inr ⟨i.val, by omega⟩)
        (fun i : Fin σ => Sum.inr ⟨2 * σ - 1 - i.val, by omega⟩))) ?_
      (Sum.elim (fun _ => (1 : k)) (Sum.elim (fun i : Fin σ => u ⟨i.val, by omega⟩)
        (fun i : Fin σ => u ⟨2 * σ - 1 - i.val, by omega⟩))) ?_
      (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2)) ?_ (hφ q) ?_)
    · rintro (a | j)
      · exact ⟨Sum.inl a, rfl⟩
      · by_cases hj : j.val < σ
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, hj⟩), rfl⟩
        · refine ⟨Sum.inr (Sum.inr ⟨2 * σ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext ?_)⟩
          show 2 * σ - 1 - (2 * σ - 1 - j.val) = j.val
          omega
    · rintro r (a | i | i)
      · show sumCols d p.π b u r (Sum.inl a) = 1 * ((jacDec d rfl).j0.map p.π * b) r a
        rw [one_mul]
        rfl
      · show sumCols d p.π b u r (Sum.inr ⟨i.val, _⟩) = u ⟨i.val, _⟩ * ((jacDec d rfl).jX.map p.π) r i
        rw [hS, mul_comm]
        rfl
      · show sumCols d p.π b u r (Sum.inr ⟨2 * σ - 1 - i.val, _⟩) = u ⟨2 * σ - 1 - i.val, _⟩ * ((jacDec d rfl).jY.map p.π) r i
        rw [hS, mul_comm]
        show u ⟨2 * σ - 1 - i.val, _⟩ * p.π (incA D (d.a r ⟨2 * σ - 1 - i.val, _⟩)) =
          u ⟨2 * σ - 1 - i.val, _⟩ * p.π (incA D ((jacDec d rfl).e' r i))
        dsimp only [jacDec, Matrix.submatrix_apply, id]
        congr 4
        apply Fin.ext
        simp
        omega
    · rintro (a | i | i)
      · rfl
      · show (if i.val < σ then i.val + 1 else i.val + 2) = i.val + 1
        rw [if_pos i.isLt]
      · show (if 2 * σ - 1 - i.val < σ then 2 * σ - 1 - i.val + 1 else 2 * σ - 1 - i.val + 2) = 2 * σ - i.val + 1
        have := i.isLt
        rw [if_neg (by omega)]
        omega
    · intro r s hrs
      have hq' : GlobalTheory.RootEx.InN p' q := hq
      rw [Matrix.sub_apply, hq' r s (lev_le_of_sum_elim_le hp' r s hrs), sub_self]
  have hR : symR k (Fin A.rank) (2 * σ) ≤ (jacGrp (jacDec d rfl)).comap φ := by
    unfold symR symN
    rw [show (2 * σ + 1) / 2 = σ by omega, show 2 * σ / 2 + 1 = σ + 1 by omega]
    refine sup_le ?_ (sup_le (hN σ (Or.inl rfl)) (hN (σ + 1) (Or.inr rfl)))
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨ψ, hψ⟩ := exists_hom p FA
    have hloc : p.IsLoc F ((jacDec d rfl).emb0 (ψ g₀)) (embX (2 * σ) g₀) := by
      refine ⟨suppAt_wittLeviEmbedding _ (hψ g₀).1, ?_⟩
      refine eq_embX F _ g₀ ((frameMat B A d.ι).map (p.π.comp (incA D)) * b) (fun r a => rfl) ?_ ?_
      · exact intertwine p (HypDec.wittDecomp_anisotropicEmbedding_inclAnisotropic (d := jacDec d rfl) (g := ψ g₀)) (hψ g₀)
      · intro j
        refine fix_col (hfix (ψ g₀)) (u j) j (fun r => ?_)
        show sumCols d p.π b u r (Sum.inr j) = u j * (d.a.map (p.π.comp (incA D))) r j
        rw [hS, mul_comm]
        rfl
    show φ (embX (2 * σ) g₀) ∈ flagN (jacDec d rfl) ⊔ (jacDec d rfl).emb0.range
    rw [isLoc_unique p (hφ _) hloc]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  exact hR hx

end GlobalTheory.RowRepLoc

theorem GlobalTheory.RowRepLoc.mem_jacGrp_of_symR : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ), 1 ≤ σ → ∀ (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b) (q : GlobalTheory.FinPl.SplitPt D (Kw w)), (∀ x, q.pr x = GlobalTheory.RowRep.piAt w x) → ∀ g : GA D B, SuppAt q.e B g → frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c → g ∈ jacGrp (jacDec d h) := by
  intro D A B c σ ε d h _ w β β' u hF _ a b ha hb hab q hq g hg hx
  subst h ha hb
  obtain ⟨Γ, hΓ1, hΓ2, hΓ⟩ := frame_val d w hF
  have hπ : (GlobalTheory.LocMod.Place.ofSplitPt q).π = piAt w := RingHom.ext hq
  refine GlobalTheory.RowRepLoc.mem_jac (GlobalTheory.LocMod.Place.ofSplitPt q) d (b' := (GlobalTheory.StdFrames.loc w β)⁻¹.val)
    (Units.mul_inv _) (Units.inv_mul _) (u := u) (Γ := Γ) ?_ ?_ hg (x := frameGL hab (inBasis rfl β' w (Lev.finE B g))) ?_ hx
  · rw [hπ]; exact hΓ1
  · rw [hπ]; exact hΓ2
  · rw [hπ]; exact hΓ g

end
