import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.LevEps
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Ws.P1.condC :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (η : K.V.frame.G₀ →* (ResidueField c'.O)ˣ), η ^ 2 = 1 → (K.V.frame.eps c'.O (ResidueField c'.O)).ker ≤ η.ker →
          (∀ i, ∃ j, η * K.r.chib i = K.r.chib j) → η = 1 := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K η hη2 hker hperm
  obtain ⟨hrange, hinj, -, -, hres, -⟩ := P1.towerGal D T
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hgood : D.Good := by
    rcases hfit.2 with ⟨h2, -⟩ | ⟨h3, -⟩
    exacts [h2.1, h3.1]
  have hlev := P1.levEps K.V
  have hsurj := (phiKer K.V).1
  have hφ : Function.Injective (ResidueField.map (inc h)) := (ResidueField.map (inc h)).injective
  have hη2' : η * η = 1 := by rw [← pow_two]; exact hη2
  have hE2 : ∀ x, ((η (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O) * η (K.V.pr x) = 1 := fun x =>
    congrArg (fun θ => ((θ (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hη2'
  have hpm : ∀ x, ∃ y : ResidueField c.O, ResidueField.map (inc h) y = η (K.V.pr x) := by
    intro x
    rcases mul_self_eq_one_iff.mp (hE2 x) with e | e
    · exact ⟨1, by rw [map_one, e]⟩
    · exact ⟨-1, by rw [map_neg, map_one, e]⟩
  choose f hf using hpm
  have hff : ∀ x, f x * f x = 1 := fun x => hφ (by rw [map_mul, hf, map_one, hE2])
  have hfmul : ∀ a b, f (a * b) = f a * f b := fun a b =>
    hφ (by rw [map_mul, hf, hf, hf]; exact congrArg Units.val ((η.comp K.V.pr).map_mul a b))
  have hf1 : f 1 = 1 := hφ (by rw [hf, map_one]; exact congrArg Units.val (η.comp K.V.pr).map_one)
  let F' : G T.L Ω →* (ResidueField c.O)ˣ :=
    { toFun := fun x => ⟨f x, f x, hff x, hff x⟩
      map_one' := Units.ext hf1
      map_mul' := fun a b => Units.ext (hfmul a b) }
  let e := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let η' : T.GalL →* (ResidueField c.O)ˣ := F'.comp e.symm.toMonoidHom
  have hxg : ∀ g : T.GalL, resLe (Tower.F_le T) (e.symm g) = (g : G T.F Ω) := fun g =>
    congrArg Subtype.val (e.apply_symm_apply g)
  have hmain : η' = 1 := by
    refine hfit.1.g3' η' ?_ ?_ ?_
    · rw [pow_two]
      refine MonoidHom.ext fun g => ?_
      exact Units.ext (hff _)
    · intro g hom
      have hq : resQ T.F (g : G T.F Ω) = resQ T.L (e.symm g) := by rw [← hxg]; exact (hres _).1
      rw [hq] at hom
      have hb := hgood.om_bar (resQ T.L (e.symm g))
      simp only [Raw.bar, hom, Units.val_one, map_one] at hb
      have heps : K.V.frame.eps c'.O (ResidueField c'.O) (K.V.pr (e.symm g)) = 1 := by
        apply Units.ext
        rw [hlev.2.2.2 c'.O (ResidueField c'.O) (e.symm g), Units.val_one]
        have hc : (cycZ (↥T.L) Ω l) (e.symm g) = cycZ ℚ Ω l (resQ T.L (e.symm g)) := ((hres _).2.2).symm
        have key : algebraMap ℤ_[l] c'.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g))) =
            inc h (algebraMap ℤ_[l] c.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g)))) :=
          ((Subalgebra.inclusion h).commutes _).symm
        show residue c'.O (algebraMap ℤ_[l] c'.O ↑(cycZ (↥T.L) Ω l (e.symm g))) = 1
        rw [hc, key, ← ResidueField.map_residue]
        have hb' : residue c.O (algebraMap ℤ_[l] c.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g)))) = 1 := by
          first | exact hb | exact hb.symm
        rw [hb', map_one]
      have hη1 : η (K.V.pr (e.symm g)) = 1 := hker heps
      apply Units.ext
      show f (e.symm g) = 1
      exact hφ (by rw [hf, hη1]; simp)
    · intro i
      obtain ⟨j, hj⟩ := hperm i
      refine ⟨j, fun g => ?_⟩
      have hq : resQ T.F (g : G T.F Ω) = resQ T.L (e.symm g) := by rw [← hxg]; exact (hres _).1
      show f (e.symm g) * residue c.O ↑(chi D T.pr i (resQ T.F ↑g)) = residue c.O ↑(chi D T.pr j (resQ T.F ↑g))
      rw [hq]
      generalize e.symm g = x
      have hc' : ((η (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O) *
          (K.r.chib i (K.V.pr x) : ResidueField c'.O) = K.r.chib j (K.V.pr x) :=
        congrArg (fun θ => ((θ (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hj
      rw [K.chib i x, K.chib j x, map_mul (residue c'.O), map_mul (residue c'.O)] at hc'
      have hκ : residue c'.O (K.κ x : c'.O) ≠ 0 := ((K.κ x).isUnit.map (residue _)).ne_zero
      apply hφ
      rw [map_mul, ResidueField.map_residue (inc h), ResidueField.map_residue (inc h), hf x]
      apply mul_left_cancel₀ hκ
      linear_combination hc'
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  have h1 : f x = 1 := by
    have hm := congrArg (fun θ => ((θ (e x) : (ResidueField c.O)ˣ) : ResidueField c.O)) hmain
    rw [show f x = f (e.symm (e x)) by rw [e.symm_apply_apply]]
    exact hm
  apply Units.ext
  rw [← hf x, h1, map_one]
  rfl
