import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CoprimeOfResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpRedProdScaleRoots

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem residue_eq_one_of_map {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (x : R)
    (hx : residue S (f x) = 1) : residue R x = 1 := by
  rw [← map_one (residue R), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  rw [← map_one (residue S), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_one f, ← map_sub] at hx
  exact fun hu => hx (hu.map f)

private theorem lab_surj (pr : Bool) : Function.Surjective (lab pr) := by
  cases pr
  · exact Function.surjective_id
  · decide

private theorem ine_resLe {Ω : Type} [Field Ω] [CharZero Ω] {F L : IntermediateField ℚ Ω} [NumberField F] [NumberField L]
    (h : F ≤ L) (A : ValuationSubring Ω) (g : G L Ω) (hg : g ∈ Ine (F := L) A) : resLe h g ∈ Ine (F := F) A :=
  ⟨hg.1, hg.2⟩

theorem UpperTheory.V.Ws.phiIne :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ u, ∀ g ∈ K.r.Ip u, ∃ g', K.V.pr g' = g ∧ K.rho X n g' = 1 := by
  intro Ω _ _ _ l hl c D T c' h K X n u g hg
  obtain ⟨⟨g', hg', rfl⟩, hk⟩ := hg
  refine ⟨g', rfl, ?_⟩
  have hk' : ∀ i, K.r.chib i (K.V.pr g') = 1 := fun i => Subgroup.mem_iInf.1 hk i
  have hA : ¬ (K.s.A u.1).valuation (l : Ω) < 1 := fun hv => K.s.St_l u.1 u.2 ((K.s.hA u.1 l).1 (by simpa using hv))
  obtain ⟨m, hm, hκ⟩ := K.tame
  have hβ : K.β g' = 1 := K.β_t (K.t_unr _ hA hg')
  have hκm : K.κ (g' ^ m) = 1 := by rw [map_pow]; exact hκ _ hA g' hg'
  have hbar : D.rbar (resQ T.F (resLe T.F_le (g' ^ m))) = 1 := by
    have h1 : ∀ j, residue c.O (D.ps j (resQ T.L (g' ^ m)) : c.O) = 1 := fun j => by
      obtain ⟨i, rfl⟩ := lab_surj T.pr j
      have h2 := K.chib i (g' ^ m)
      have h3 : K.r.chib i (K.V.pr (g' ^ m)) = 1 :=
        (map_pow ((K.r.chib i).comp K.V.pr) g' m).trans ((congrArg (· ^ m) (hk' i)).trans (one_pow m))
      rw [hκm, h3, Units.val_one, Units.val_one, one_mul] at h2
      exact residue_eq_one_of_map (inc h) _ h2.symm
    show (Matrix.diagonal fun j => (D.ps j (resQ T.L (g' ^ m)) : c.O)).map (residue c.O) = 1
    rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one]
    exact congrArg _ (funext h1)
  have hr : X.P.r (resLe T.F_le (g' ^ m)) = 1 := by
    refine X.pair.kill _ ⟨K.s.A u.1, fun p hp => ?_, ine_resLe _ _ _ (pow_mem hg' m), hbar⟩
    obtain rfl : p = l := by simpa using hp
    exact hA
  have hpow : K.rho X n g' ^ m = 1 := by
    rw [← map_pow, Link.rho_apply, hr, Link.sc, hκm, map_pow K.β, hβ]
    simp
  obtain ⟨-, -, hmon, hmap⟩ := phiCpMap K X n g'
  refine phiRigid (res c'.O X.B : X.B →+* ResidueField c'.O) (fun x hx => (res_eq_zero_iff c'.O X.B x).1 hx) _ (K.cpT X n g') 4 m
    hmon ?_ ?_ hpow ?_
  · rw [← aeval_map_algebraMap X.A, hmap, Matrix.aeval_self_charpoly]
  · rw [phiCpRed K X n g']
    simp [hk']
  · obtain ⟨-, -, -, -, -, -, -, -, hu⟩ := dvrFacts l c'.O
    simpa using (hu m ((Nat.Prime.coprime_iff_not_dvd hl.out).1 hm)).map (algebraMap c'.O X.B)
