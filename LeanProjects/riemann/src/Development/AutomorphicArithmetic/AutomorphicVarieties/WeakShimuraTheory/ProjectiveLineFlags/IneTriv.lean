import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem res_one_lemma {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (y : A) (hy : IsLocalRing.residue B (f y) = 1) : IsLocalRing.residue A y = 1 := by
  change Ideal.Quotient.mk _ (f y) = Ideal.Quotient.mk _ 1 at hy
  change Ideal.Quotient.mk _ y = Ideal.Quotient.mk _ 1
  rw [Ideal.Quotient.eq] at hy ⊢
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
  intro hu
  apply hy
  simpa using hu.map f

theorem UpperTheory.V.Ws.P1.ineTriv :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q → ∀ u, ∀ g ∈ K.r.Ip u, ρ g = 1 := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q ρ hQ hρ u g hg
  simp only [W.Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hg
  obtain ⟨hgu, hgc⟩ := hg
  unfold UpperTheory.V.W.HidaSetting.Lev.frame at hgu u
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hgu
  have hu : (u : W.Plc (W.Lp ↥T.L)) ∈ K.s.St := u.2
  have hsurj : ∀ b : Bool, ∀ j : Fin 4, ∃ i, lab b i = j := by decide
  have key : ∀ i, IsLocalRing.residue c'.O
      ((K.κ g' : c'.O) * inc h (D.ps (lab T.pr i) (resQ T.L g') : c.O)) = 1 := by
    intro i
    have e := K.chib i g'
    rw [hgc i, Units.val_one] at e
    exact e.symm
  have hκr : IsLocalRing.residue c'.O (K.κ g' : c'.O) = 1 := by
    obtain ⟨i, hi⟩ := hsurj T.pr 3
    have e := key i
    rw [hi] at e
    simpa [Raw.ps] using e
  have hres : ∀ j, IsLocalRing.residue c.O (D.ps j (resQ T.L g') : c.O) = 1 := by
    intro j
    obtain ⟨i, hi⟩ := hsurj T.pr j
    have e := key i
    rw [hi, map_mul, hκr, one_mul] at e
    exact res_one_lemma (inc h) _ e
  have hrb : D.rbar (resQ T.L g') = 1 := by
    have hf : (fun i => IsLocalRing.residue c.O (D.ps i (resQ T.L g') : c.O)) = fun _ => 1 := funext hres
    show (RingHom.mapMatrix (IsLocalRing.residue c.O))
      (Matrix.diagonal fun i => (D.ps i (resQ T.L g') : c.O)) = 1
    rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _), hf, Matrix.diagonal_one]
  have hnl : ¬ (K.s.A ↑u).valuation (l : Ω) < 1 := by
    intro hlt
    have hin := (K.s.hA ↑u (l : 𝓞 (W.Lp ↥T.L))).mp (by simpa using hlt)
    exact K.s.St_l ↑u hu (by simpa using hin)
  obtain ⟨m, hm, hκt⟩ := K.tame
  have hκm := hκt (K.s.A ↑u) hnl g' hg'
  have hκ1 : (K.κ g' : c'.O) = 1 :=
    (coefRes c').2.2.2 m _ hm (by rw [← Units.val_pow_eq_pow_val, hκm, Units.val_one]) hκr
  have hQr : Q.r (resLe T.F_le g') = 1 := by
    apply hQ.kill
    unfold UpperTheory.V.Ws.Tower.fr
    simp only [Set.mem_setOf_eq]
    refine ⟨K.s.A ↑u, ?_, ?_, ?_⟩
    · intro p hp
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hp
      subst hp
      exact hnl
    · exact ((towerGal D T).2.2.2.2.2 _ g').2.mpr hg'
    · rw [((towerGal D T).2.2.2.2.1 g').1]
      exact hrb
  have e := hρ g'
  rw [hQr, hκ1, map_one, one_smul] at e
  exact Units.ext e
