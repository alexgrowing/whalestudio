import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp

noncomputable section

namespace GlobalTheory.FlatLine.Definite

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem frMap_of_comp {R S T : Type} [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] {φ : R →ₐ[c.F] S} {ψ : S →ₐ[c.F] T} {χ : R →ₐ[c.F] T} (h : ψ.comp φ = χ) {y : FrPt Xo c R}
    {z : FrPt Xo c S} {w : FrPt Xo c T} (hz : FrMap φ y z) (hw : FrMap χ y w) : FrMap ψ z w := by
  obtain ⟨w', hw'⟩ := exists_bc ψ z
  rwa [(frMap_unique_refl_iff E H Dw l Xo c R T χ y).1 w w' hw (h ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hz hw')]

abbrev idemAt (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : S :=
  CompSplitPfB.cspB_idem _ (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over

theorem idemAt_eq_one_iff (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    idemAt Z y = 1 ↔ LiesOn Z y := by
  refine ⟨fun h q => (CompSplitPfB.cspB_idem_spec _
    (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over q).1 ?_, fun h => ?_⟩
  · show idemAt Z y ∉ _
    rw [h]
    exact (Ideal.ne_top_iff_one _).1 q.isPrime.ne_top
  · refine CompSplitPfB.cspB_idem_eq_of (CompSplitPfB.cspB_idem_idem _ _ _ _) IsIdempotentElem.one fun q => ?_
    rw [CompSplitPfB.cspB_idem_spec]
    exact iff_of_true (h q) ((Ideal.ne_top_iff_one _).1 q.isPrime.ne_top)

def IsCoef (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (τ : E →+* ℂ) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (s : S) : Prop :=
  idemAt Z y * s = s ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (w z : FrPt Xo c T)
    (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) T)) (a : T),
    FrMap φ y w → FrMap (Algebra.ofId c.F T) y₀ z → FrChg g a w z → φ s = (g τ).det

theorem eq_of_mk_eq {S : Type} [CommRing S] {e s t : S} (he : IsIdempotentElem e) (hs : e * s = s) (ht : e * t = t)
    (h : Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) t) : s = t := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have := he.eq
  linear_combination ht - hs - e * hb - b * this

theorem exists_isCoef {Z : Comp Xo c} {y₀ : FrPt Xo c c.F} (h₀ : LiesOn Z y₀)
    (hy₀ : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y →
      y.x = spMap (algebraMap c.F S) ≫ y₀.x) (τ : E →+* ℂ) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) : ∃ s s' : S, IsCoef Z y₀ τ y s ∧ (∀ t, IsCoef Z y₀ τ y t → t = s) ∧
      idemAt Z y * s' = s' ∧ s * s' = idemAt Z y := by
  have he : IsIdempotentElem (idemAt Z y) := CompSplitPfB.cspB_idem_idem _ _ _ _
  let π := Ideal.Quotient.mkₐ c.F (Ideal.span {1 - idemAt Z y})
  have hπ : π (idemAt Z y) = 1 := by
    rw [← map_one π]
    exact (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)).symm
  obtain ⟨w, hw⟩ := exists_bc π y
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (S ⧸ Ideal.span {1 - idemAt Z y})) y₀
  have hwZ : LiesOn Z w := (idemAt_eq_one_iff Z w).1
    ((CompSplitPfB.cspB_idem_map _ _ π y.x_over w.x_over hw.1).symm.trans hπ)
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c _ w z).1 (hz.1.trans (hy₀ _ w hwZ).symm)
  obtain ⟨d', hd'⟩ := (hg τ).exists_right_inv
  obtain ⟨s, hs⟩ := Ideal.Quotient.mkₐ_surjective c.F _ (g τ).det
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mkₐ_surjective c.F _ d'
  have k : ∀ t, idemAt Z y * (idemAt Z y * t) = idemAt Z y * t := fun t => by rw [← mul_assoc, he.eq]
  have hs₁ : π (idemAt Z y * s) = (g τ).det := by rw [map_mul, hπ, one_mul]; exact hs
  have hs₂ : π (idemAt Z y * s') = d' := by rw [map_mul, hπ, one_mul]; exact hs'
  refine ⟨idemAt Z y * s, idemAt Z y * s', ⟨k s, fun T _ _ φ w' z' g' a' hw' hz' hc' => ?_⟩,
    fun t ht => eq_of_mk_eq he ht.1 (k s) ((ht.2 _ π w z g a hw hz hc).trans hs₁.symm), k s',
    eq_of_mk_eq he (by rw [← mul_assoc, k]) he.eq ?_⟩
  · have h1 : φ (idemAt Z y) = 1 := (CompSplitPfB.cspB_idem_map _ _ φ y.x_over w'.x_over hw'.1).trans
      ((CompSplitPfB.cspB_idem_congr _ _ z'.x_over w'.x_over hc'.1.symm).trans
        ((idemAt_eq_one_iff Z z').2 (liesOn_frMap hz' h₀)))
    let ψ := Ideal.Quotient.liftₐ (Ideal.span {1 - idemAt Z y}) φ fun b hb => by
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
      rw [map_mul, map_sub, h1, map_one, sub_self, mul_zero]
    have hψ : ψ.comp π = φ := Ideal.Quotient.liftₐ_comp _ _ _
    have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ w z w' z' g a hc (frMap_of_comp hψ hw hw')).1
      (frMap_of_comp (Subsingleton.elim _ _) hz hz')
    rw [((frChg_exists_unique E H Dw l Xo c T w' z').2 _ _ _ _ hc' c₁).1, ← hψ, AlgHom.comp_apply, hs₁]
    exact ψ.toRingHom.map_det (g τ)
  · show π _ = π _
    rw [map_mul, hs₁, hs₂, hd', hπ]

theorem prod_exOf_flatWt (hq : Dw.q = 0) (τ : Psi H) {G : Type} [CommGroup G] (t : Ix Dw → G) :
    ∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i = (∏ i, t (some ⟨τ.1, i⟩))⁻¹ := by
  have h : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      exOf Dw (flatWt Dw τ) 0 (some ⟨ρ, i⟩) = open Classical in if ρ = τ.1 then -1 else 0 := fun ρ i => by
    have hi := i.2
    have hρ : ρ (H.rt : E) = H.rt0 := by
      by_contra hn
      simp [Datum.mult, hn, hq] at hi
    refine (wtOf_big (flatWt Dw τ) 0 ⟨ρ, hρ⟩ i (by simpa [Datum.mult, hρ] using hi)).trans ?_
    simp only [flatWt, parWt, sub_zero]
    by_cases h1 : ρ = τ.1
    · rw [if_pos h1, if_pos (Subtype.ext h1)]
    · rw [if_neg h1, if_neg fun h2 => h1 (congrArg Subtype.val h2)]
  have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
  rw [Fintype.prod_option, h0, zpow_zero, one_mul, Fintype.prod_sigma, Finset.prod_eq_single τ.1
    (fun ρ _ hρ => by simp [h, hρ]) (by simp)]
  simp [h]

theorem inv_mem_secZ_on {Z : Comp Xo c} {e : Ix Dw → ℤ} {f f' : Rul Xo c} (hf : f ∈ secZ Xo c e)
    (h1 : idem Z * f' = f') (h2 : f * f' = idem Z) : f' ∈ secZ Xo c (-e) := by
  have k1 : ∀ p y, idem Z p y * f' p y = f' p y := fun p y => congrFun (congrFun h1 p) y
  have k2 : ∀ p y, f p y * f' p y = idem Z p y := fun p y => congrFun (congrFun h2 p) y
  have hi := idem_mem_secZ Z
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · have a1 := congrArg φ (k1 p y)
    have a2 := congrArg φ (k2 p y)
    rw [map_mul, ← hi.1 p q φ y z h] at a1
    rw [map_mul, ← hi.1 p q φ y z h, ← hf.1 p q φ y z h] at a2
    linear_combination a1 - k1 q z - f' q z * a2 + φ (f' p y) * k2 q z
  · have a1 := k2 p y'
    have a0 : idem Z p y' = idem Z p y := by simpa using hi.2 p t y y' h
    have a4 := k1 p y'
    rw [hf.2 p t y y' h, a0] at a1
    rw [a0] at a4
    have a3 : ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) * ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]; simp
    generalize ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) = A at *
    generalize ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = B at *
    linear_combination A * f' p y * a1 - a4 - f' p y' * k2 p y + A * k1 p y - f p y * f' p y * f' p y' * a3

theorem exists_flatRule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → ∀ (Z : Comp Xo c) (τ : Psi H) (y₀ : FrPt Xo c c.F), LiesOn Z y₀ → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x) → ∃ f f' : Rul Xo c, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) ∧ f' ∈ secZ Xo c (-exOf Dw (flatWt Dw τ) 0) ∧ idem Z * f = f ∧ idem Z * f' = f' ∧ f * f' = idem Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) S)) (a : S), Tested y → FrMap (Algebra.ofId c.F S) y₀ z → FrChg g a y z → evR Xo c f y = (g τ.1).det := by
  intro E _ _ _ H Dw l Xo c hq Z τ y₀ h₀ hy₀
  choose f f' hf hu h1 h2 using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_isCoef h₀ hy₀ τ.1 y
  have i1 : idem Z * f' = f' := funext fun p => funext fun y => h1 p y
  have i2 : (f : Rul Xo c) * f' = idem Z := funext fun p => funext fun y => h2 p y
  have hm : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) := by
    refine ⟨fun p q φ y z h => (hu q z _ ⟨?_, fun T _ _ ψ w z' g a hw hz hc => ?_⟩).symm,
      fun p t y y' h => (hu p y' _ ⟨?_, fun T _ _ ψ w' z' g a hw hz hc => ?_⟩).symm⟩
    · rw [idemAt, ← CompSplitPfB.cspB_idem_map _ _ φ y.x_over z.x_over h.1, ← map_mul]
      exact congrArg φ (hf p y).1
    · exact (hf p y).2 T (ψ.comp φ) w z' g a (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ h hw) hz hc
    · rw [mul_left_comm, idemAt, CompSplitPfB.cspB_idem_congr _ _ y.x_over y'.x_over h.1]
      exact congrArg _ (hf p y).1
    · obtain ⟨k, k0, k1, hk⟩ := ((frBor_calculus E H Dw l Xo c _ y y' y').1 t).1 h
      obtain ⟨w, hw₀⟩ := exists_bc ψ y
      have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ y y' w w' k _ hk hw₀).1 hw
      have c₂ := (frChg_refl_and_comp E H Dw l Xo c T w w' z').2 _ _ _ _ c₁ hc
      have hd : (k τ.1).det = ((∏ i, t (some ⟨τ.1, i⟩) : (p.R)ˣ) : p.R) := by
        rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => k0 τ.1 i j hij), Units.coe_prod]
        exact Finset.prod_congr rfl fun i _ => k1 τ.1 i
      have hd' : ((k τ.1).map ψ).det = ψ (k τ.1).det := (ψ.toRingHom.map_det (k τ.1)).symm
      rw [map_mul, (hf p y).2 T ψ w z' _ _ hw₀ hz c₂, Matrix.det_mul, hd', hd, prod_exOf_flatWt hq, mul_left_comm,
        ← map_mul, Units.inv_mul, map_one, mul_one]
  refine ⟨f, f', hm, inv_mem_secZ_on hm i1 i2, funext fun p => funext fun y => (hf p y).1, i1, i2,
    fun S _ _ y z g a ht hz hc => ?_⟩
  unfold evR evalAt
  rw [dif_pos ht]
  exact (hf _ _).2 S _ y z g a ht.choose_spec.choose_spec.choose_spec hz hc

end GlobalTheory.FlatLine.Definite
