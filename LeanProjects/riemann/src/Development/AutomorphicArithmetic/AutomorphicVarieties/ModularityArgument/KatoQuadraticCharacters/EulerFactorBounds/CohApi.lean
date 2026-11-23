import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.GalAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.HeckeInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.HeckeGal
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sCohApi :
    UpperTheory.V.Z.Kato.Nb.SCohApi := by
  intro Ω _ _ _ ε X l hl N w n hN A _ κ
  obtain ⟨he, hadd, hsm, hsum, -, hact, hgal, hsucc, h0, -, -⟩ := sApi Ω ε X l n
  obtain ⟨i0, iadd, ism, -, isum, isucc, iz, -⟩ := sInvApi Ω ε X l N w n
  have cast : ∀ {a b b' : X.Fn l}, CgF X l n a b → b = b' → CgF X l n a b' := fun h e => e ▸ h
  have lin : ∀ T : X.Fn l →ₗ[ℤ_[l]] X.Fn l, (∀ a b, CgF X l n a b → CgF X l n (T a) (T b)) →
      (∀ a, InvM X l N w n a → InvM X l N w n (T a)) →
      (∀ s a, InvM X l N w n a → CgF X l n (X.galB l s (T a)) (T (X.galB l s a))) →
      ∀ z z', CohB X l N w n κ z z' → CohB X l N w n κ (fun s y => T (z s y)) (fun s y => T (z' s y)) := by
    rintro T h1 h2 h3 z z' ⟨b, hb, hz⟩
    refine ⟨fun y => T (b y), fun y => h2 _ (hb y), fun s y => ?_⟩
    refine he.trans (cast (h1 _ _ (hz s y)) (by rw [map_add, map_sub])) ?_
    exact (hadd _ _ _ _ (he.refl _) (hadd _ _ _ _ (he.symm (h3 s _ (hb _))) (he.refl _)).2).1
  have ofCg : ∀ z z' : (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l, (∀ s y, CgF X l n (z s y) (z' s y)) → CohB X l N w n κ z z' :=
    fun z z' h => ⟨fun _ => 0, fun _ => i0, fun s y => cast (h s y) (by simp)⟩
  refine ⟨⟨fun z => ofCg z z fun s y => he.refl _, ?_, ?_⟩, ofCg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z z' ⟨b, hb, hz⟩
    refine ⟨fun y => 0 - b y, fun y => (iadd _ _ i0 (hb y)).2, fun s y => ?_⟩
    have h := (hadd _ _ _ _ (he.symm (hz s y)) (he.refl (X.galB l s (b (y * κ s)) - b y))).2
    rw [add_sub_cancel_right] at h
    exact cast h (by simp only [map_sub, map_zero]; abel)
  · rintro z z' z'' ⟨b, hb, hz⟩ ⟨c, hc, hz'⟩
    refine ⟨fun y => b y + c y, fun y => (iadd _ _ (hb y) (hc y)).1, fun s y => ?_⟩
    refine he.trans (hz s y) (cast (hadd _ _ _ _ (hz' s y) (he.refl _)).1 ?_)
    simp only [map_add]; abel
  · rintro z z' v v' ⟨b, hb, hz⟩ ⟨c, hc, hv⟩
    refine ⟨⟨fun y => b y + c y, fun y => (iadd _ _ (hb y) (hc y)).1, fun s y => ?_⟩,
      ⟨fun y => b y - c y, fun y => (iadd _ _ (hb y) (hc y)).2, fun s y => ?_⟩⟩
    · refine cast (hadd _ _ _ _ (hz s y) (hv s y)).1 ?_
      simp only [map_add, Pi.add_apply]; abel
    · refine cast (hadd _ _ _ _ (hz s y) (hv s y)).2 ?_
      simp only [map_sub, Pi.sub_apply]; abel
  · rintro k t z z' ⟨b, hb, hz⟩
    refine ⟨fun y => k • b (y * t), fun y => ism k _ (hb _), fun s y => ?_⟩
    refine cast (hsm k _ _ (hz s (y * t))) ?_
    simp only [map_smul, smul_add, smul_sub, mul_right_comm y t]
  · rintro z z' ⟨b, hb, hz⟩
    exact ⟨b, fun y => isucc _ (hb y), fun s y => hsucc _ _ (hz s y)⟩
  · intro z z'
    exact ⟨fun _ => 0, fun _ => iz _, fun s y => h0 _ _⟩
  · rintro A' _ _ _ π z z' ⟨b, hb, hz⟩
    refine ⟨fun t => ∑ y ∈ Finset.univ.filter (fun y => π y = t), b y, fun t => isum _ _ _ fun y _ => hb y, fun s t => ?_⟩
    refine cast (hsum _ _ _ _ fun y _ => hz s y) ?_
    have e : ∑ y ∈ Finset.univ.filter (fun y => π y = t * π (κ s)), b y =
        ∑ y ∈ Finset.univ.filter (fun y => π y = t), b (y * κ s) := by
      symm
      refine Finset.sum_equiv (Equiv.mulRight (κ s)) (fun y => ?_) (fun y _ => rfl)
      simp
    simp only [GlobalTheory.KA.push, e, Finset.sum_add_distrib, Finset.sum_sub_distrib, map_sum]
  · intro p hp hc z z' h
    have hd := (GlobalTheory.KZ.Betti.isDiam_sgD (l := l) hN.ne' hl.out.ne_zero (Nat.Coprime.coprime_mul_left_right hc)).1
    refine ⟨lin _ (fun a b hab => ?_) (sHeckeInv Ω ε X l N w n p hN hp hc) (sHeckeGal Ω ε X l N w n p hN hp hc) z z' h,
      lin _ (hact _) (fun a ha => ((sGalAct Ω ε X l N w n hN 1 a ha).2 _ hd).1)
        (fun s a ha => ((sGalAct Ω ε X l N w n hN s a ha).2 _ hd).2) z z' h⟩
    simp only [Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]
    exact (hadd _ _ _ _ (hsum _ _ _ _ fun j _ => hact _ _ _ hab) (hact _ _ _ hab)).1
