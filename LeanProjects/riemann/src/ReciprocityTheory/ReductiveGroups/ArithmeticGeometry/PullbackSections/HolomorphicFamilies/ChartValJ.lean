import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Closed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmSecond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

section Letters

variable {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ)

def colL (m : Formalism.L2.Pj.Letter T rr n →₀ ℕ) (b : Fin n) : (Σ τ : T, Fin (rr τ)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

theorem colM_lEq_colL (m : Formalism.L2.Pj.Letter T rr n →₀ ℕ) (b : Fin n) :
    colM (m.mapDomain (CVA.lEq (T := T) (r := rr) (n := n))) b = colL rr n m b := by
  ext ℓ
  show Finsupp.mapDomain CVA.lEq m (CVA.lEq ⟨ℓ.1, ℓ.2, b⟩) = m ⟨ℓ.1, ℓ.2, b⟩
  rw [Finsupp.mapDomain_apply CVA.lEq.injective]

end Letters

section Main

variable {R k : Type} [CommRing R] [Field k] [Algebra ℚ k] [Algebra R k]

set_option maxHeartbeats 1000000 in
theorem chartValJ (hRQ : IsRQ (R := R) k) (J : Submodule R k) (hJ1 : (1 : k) ∈ J)
    {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h)
    (w0 : O) (hw0 : w0 + star w0 = 1) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ))
    {π : Type} [Fintype π] [DecidableEq π] (c : T → π) (s : T → Bool)
    (hcs : ∀ τ, c (cc τ) = c τ ∧ s (cc τ) ≠ s τ)
    (u φ : (Σ τ : T, Fin (rr τ)) → Fin d → R) (ψ : (Σ τ : T, Fin (rr τ)) → Fin d → k) (hψ : ∀ ℓ i, ψ ℓ i ∈ J)
    (heig : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 →
      ∑ i, (algebraMap R k (φ ℓ' i) + ψ ℓ' i - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0)
    (h21a : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)))
    (h21b : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ))
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)))
    (h21c : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
      (fun ℓ => (0, ψ ℓ)))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Formalism.L2.Pj.Letter T rr n) k)
    (hP : P ∈ Formalism.L2.Pj.HaO rr n k (algebraMap R k).range cc isX a)
    (e : ℕ) (he : ∀ mo ∈ P.support, ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (colL rr n mo b) ≤ e)
    (f : Fin n → PS k 1 d) (hf : ∀ b, IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ J ^ e := by
  classical
  set uK : (Σ τ : T, Fin (rr τ)) → Fin d → k := fun ℓ j => algebraMap R k (u ℓ j) with huK
  set φK : (Σ τ : T, Fin (rr τ)) → Fin d → k :=
    fun ℓ i => algebraMap R k (φ ℓ i) + ψ ℓ i - (sg1 k h).mulVec (uK ℓ) i with hφK
  set g : Fin n → PS k 1 d := fun b => FB.expS k ((m : k) • B.hL k h w0) * f b with hgdef
  set P2 := MvPolynomial.rename (CVA.lEq (T := T) (r := rr) (n := n)) P with hP2

  have hvan : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 → ∑ i, φK ℓ' i * uK ℓ i = 0 := fun ℓ ℓ' hne => heig ℓ ℓ' hne
  have hpair : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 = cc ℓ.1 → (c ℓ.1 = c ℓ'.1 ∧ s ℓ.1 ≠ s ℓ'.1) := by
    intro ℓ ℓ' he'
    rw [he']
    exact ⟨(hcs ℓ.1).1.symm, (hcs ℓ.1).2.symm⟩
  have hL1 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (uK ℓ, 0))
      (fun ℓ => (uK ℓ, 0)) := by
    intro l l' _
    simp [betaH]
  have hL2 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (uK ℓ, 0))
      (fun ℓ => (0, φK ℓ)) := by
    intro l l' hnot
    by_cases hl : l'.1 = cc l.1
    · exact absurd (hpair l l' hl) hnot
    · simp only [betaH, Pi.zero_apply, zero_mul, sub_zero]
      exact hvan l l' hl
  have hL3 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, φK ℓ))
      (fun ℓ => (uK ℓ, 0)) := by
    intro l l' hnot
    by_cases hl : l.1 = cc l'.1
    · exfalso
      apply hnot
      have := hpair l' l hl
      exact ⟨this.1.symm, this.2.symm⟩
    · simp only [betaH, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero]
      exact hvan l' l hl

  have hharm := CVA.harm_rename (r := rr) (n := n) cc isX P hP.1.1

  set cfun : (Σ τ : T, Fin (rr τ)) → (Σ τ : T, Fin (rr τ)) → k := fun l l' =>
    if c l.1 = c l'.1 ∧ s l.1 = true ∧ s l'.1 = false then (m : k) * betaH k (0, φK l) (uK l', 0) else 0
    with hcfun
  have hcvan : ∀ l l' : (Σ τ : T, Fin (rr τ)), l'.1 ≠ cc l.1 → cfun l l' = 0 := by
    intro l l' hne
    have hne' : l.1 ≠ cc l'.1 := fun h' => hne (by rw [h', hcc])
    have hz : betaH k (0, φK l) (uK l', 0) = 0 := by
      simp only [betaH, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero]
      exact hvan l' l hne'
    simp only [hcfun, hz, mul_zero, ite_self]
  have hso := harmSecond_holds k T rr cc isX hcc hX n cfun hcvan P2 hharm
  have hfun : (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n =>
      if p.2 = q.2 ∧ c p.1.1 = c q.1.1 ∧ s p.1.1 = true ∧ s q.1.1 = false then
        (m : k) * betaH k (0, φK p.1) (uK q.1, 0) else 0) =
      (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n => if p.2 = q.2 then cfun p.1 q.1 else 0) := by
    funext p q
    by_cases h1 : p.2 = q.2 <;> simp [h1, hcfun]
  have hso' : secondOrder k (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n =>
      if p.2 = q.2 ∧ c p.1.1 = c q.1.1 ∧ s p.1.1 = true ∧ s q.1.1 = false then
        (m : k) * betaH k (0, φK p.1) (uK q.1, 0) else 0) P2 = 0 := by
    rw [hfun]
    exact hso

  have hLH := TB.WickVanishing.Closed.lemma_H_columns R d O k B h hg.ax0 m (Σ τ : T, Fin (rr τ)) π (fun ℓ => c ℓ.1) (fun ℓ => s ℓ.1)
    uK φK hL1 hL2 hL3 n P2 hso' g

  set ξh : (Σ τ : T, Fin (rr τ)) → (Fin d → k) × (Fin d → k) := fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
      fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i) with hξh
  have hxi : (fun ℓ => ξh ℓ + ((0 : Fin d → k), ψ ℓ)) = fun ℓ => (uK ℓ, φK ℓ) := by
    funext ℓ
    refine Prod.ext ?_ ?_
    · funext j
      simp [hξh, huK]
    · funext i
      simp only [hξh, Prod.snd_add, Pi.add_apply, hφK, huK]
      ring
  have he2 : ∀ mo ∈ P2.support, ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (colM mo b) ≤ e := by
    intro mo hmo
    rw [hP2, MvPolynomial.support_rename_of_injective CVA.lEq.injective] at hmo
    obtain ⟨mo0, hmo0, rfl⟩ := Finset.mem_image.1 hmo
    simp only [colM_lEq_colL]
    exact he mo0 hmo0
  have hSC := TB.WickVanishing.Closed.scaled_connection_columns R d O k hRQ J hJ1 B h hg w0 hw0 m (Σ τ : T, Fin (rr τ)) π (fun ℓ => c ℓ.1)
    (fun ℓ => s ℓ.1) ξh ψ (fun ℓ => ⟨u ℓ, φ ℓ, rfl⟩) hψ h21a h21b h21c n P2
    (CVA.coeff_rename_mem _ P hP.2) e he2 f hf
  rw [hxi] at hSC
  have hchain : ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) uK
      (MvPolynomial.monomial (colL rr n mo b) 1) =
      ∑ mo ∈ P2.support, P2.coeff mo * ∏ b, constantCoeff (ordNabla k B h m (fun ℓ => s ℓ.1)
        (fun ℓ => (uK ℓ, φK ℓ)) (MvPolynomial.monomial (colM mo b) 1) (liftX k (g b))) := by
    rw [hLH, hP2, CVA.sum_rename]
    refine Finset.sum_congr rfl fun mo _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [colM_lEq_colL]
    simp only [FB.nabVal, hgdef]
    rw [mul_comm]
  rw [hchain]
  have hg' : g = fun b => FB.expS k ((m : k) • B.hL k h w0) * f b := hgdef
  rw [hg']
  exact hSC

end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
