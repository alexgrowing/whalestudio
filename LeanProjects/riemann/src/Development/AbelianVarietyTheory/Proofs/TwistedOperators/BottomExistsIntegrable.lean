import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)
open scoped ComplexOrder

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

open GlobalTheory.Grid (neg neg_gram sigOK_sgn isCartanInv_sgn)

theorem exists_stdRig (n : ℕ) : ∃ (V : HSp D) (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), V.rank = n ∧ V.SigOK ∧ r.IsStd ∧ r.Is := by
  let V : HSp D := Formalism.BasicNotions.Examples₂.posSpace Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hg : V.gram = 1 := Matrix.ext fun i j => by
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0 i j).trans ?_
    exact (Matrix.one_apply (i := i) (j := j)).symm
  let Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)
  have hmem : ∀ y, y ∈ Λ ↔ ∀ i, IsIntegral ℤ (y i) := fun y => by
    simp only [Λ, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨y i, h⟩, rfl⟩⟩
  have hsingle : ∀ i, (Pi.single i 1 : Fin V.rank → D.host.E) ∈ Λ := fun i => (hmem _).2 fun k => by
    by_cases h : k = i
    · subst h; simpa using isIntegral_one
    · simpa [h] using isIntegral_zero
  have hsd : IsSelfDualC V Λ := by
    refine ⟨⟨Submodule.fg_pi fun _ => ?_, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => (hmem y).2 fun i => ?_⟩⟩
    · rw [Submodule.one_eq_span]
      exact Submodule.fg_span (Set.finite_singleton _)
    · rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      rw [Pi.basisFun_apply]
      exact hsingle i
    · have hs : IsIntegral ℤ (∑ a, ∑ b, star (x a) * V.gram a b * y b) := by
        rw [hg]
        refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
        by_cases hab : a = b
        · subst hab
          simpa using (Formalism.BasicNotions.Examples₂.star_isIntegral _ ((hmem x).1 hx a)).mul ((hmem y).1 hy a)
        · simpa [Matrix.one_apply, hab] using isIntegral_zero
      exact ⟨⟨_, hs⟩, rfl⟩
    · obtain ⟨b, hb⟩ := h _ (hsingle i)
      have e : ∑ a, ∑ c, star ((Pi.single i 1 : Fin V.rank → D.host.E) a) * V.gram a c * y c = y i := by
        rw [hg, Finset.sum_eq_single i]
        · simp [Matrix.one_apply]
        · intro a _ ha
          simp [ha]
        · simp
      rw [e] at hb
      exact hb ▸ b.isIntegral_coe
  obtain ⟨r, hr, hri⟩ := GlobalTheory.T.self_dual_lattice_has_rigidification D V Λ (Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n) hsd
  have hgt : ∀ τ, gramAt D V τ = 1 := fun τ => by rw [gramAt, hg]; simp
  refine ⟨V, ⟨Λ, r.β, fun _ => 1, fun _ => 1⟩, rfl, Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n,
    ⟨hg, fun y => (hmem y).trans (forall_congr' fun i => ⟨fun h => ⟨⟨y i, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩),
      fun _ => ⟨rfl, rfl⟩⟩, hsd, hr ▸ hri.2.1, fun τ => ⟨?_, V.rank, ?_⟩⟩
  · rw [hgt]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  · rw [hgt]
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩ <;> simp

theorem bottom_chars {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i j : Fin D.R.m) (t : T) :
    IsHeckeChar D (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) ∧
      IsHeckeChar D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) ∧
      ResEta D (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) (SqNum.botSmall D i j) ∧
      ResEta D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (SqNum.botBig D i j) := by
  have hmul : ∀ {χ η : (AE D)ˣ →* Circle}, IsHeckeChar D χ → IsHeckeChar D η → IsHeckeChar D (χ * η) := fun h1 h2 =>
    ⟨h1.1.mul h2.1, fun x => by rw [MonoidHom.mul_apply, h1.2, h2.2, mul_one]⟩
  have heta : IsHeckeChar D L.eta := hL.eta.1
  have hpow : ∀ n, IsHeckeChar D (L.eta ^ n) := fun n =>
    ⟨heta.1.pow n, fun x => by rw [MonoidHom.pow_apply, heta.2, one_pow]⟩
  have hi := i.2
  have hchiE := G.ch.chi_eq (D.R.m - i) (by omega) (by omega)
  have rpow : ∀ n, ResEta D (L.eta ^ n) n := fun n => by
    induction n with
    | zero => exact ⟨(GlobalTheory.HeckeCharacterRestriction.resEta_eta hL).1, fun η _ a => by simp⟩
    | succ n ih => rw [pow_succ]; exact resEta_mul ih (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
  have rchi : ResEta D (G.ch.chi (D.R.m - i)) 0 := ⟨(GlobalTheory.HeckeCharacterRestriction.resEta_eta hL).1, fun η _ a => by
    rw [pow_zero]; exact GlobalTheory.GridWeil.triv_base hchiE (G.ch.triv _ (by omega) (by omega)) a⟩
  obtain ⟨h1, h2, h3⟩ := SqNum.ranks_exact D i j
  refine ⟨hmul (GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j) (hpow _), hmul hchiE.1 (hpow _),
    resEta_parity (resEta_mul (GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j) (rpow _)) ?_,
    resEta_parity (resEta_mul rchi (rpow _)) ?_⟩ <;> omega

theorem isSelfDualC_neg' {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (h : IsSelfDualC A Λ) :
    IsSelfDualC (neg A) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [neg_gram, hc]
  · simp [neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

theorem exists_bottomTri {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (W : G.Weil) (i j : Fin D.R.m) :
    ∃ (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X := by
  obtain ⟨A, rA, hA1, hA2, hA3, hA4⟩ := exists_stdRig (D := D) (SqNum.botBig D i j)
  obtain ⟨A', rA', hB1, hB2, hB3, hB4⟩ := exists_stdRig (D := D) (SqNum.botSmall D i j)
  obtain ⟨WW, rW, hW1, hW2, hW3, hW4⟩ := exists_stdRig (D := D) (SqNum.botBig D i j + SqNum.botSmall D i j)
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hc := fun t => bottom_chars hL G i j t
  have hd : ∀ {χ η : (AE D)ˣ →* Circle}, IsHeckeChar D χ → IsHeckeChar D η → IsHeckeChar D (χ / η) := fun h1 h2 =>
    ⟨h1.1.div' h2.1, fun x => by rw [MonoidHom.div_apply, h1.2, h2.2, div_one]⟩
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true A WW (hc t).2.1 (hd (hc t).2.1 (hc t).1)
    (hA1 ▸ (hc t).2.2.2) (by rw [hW1, div_eq_mul_inv]; exact resEta_mul (hc t).2.2.2 (resEta_inv (hc t).2.2.1))
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false A' WW (hc t).1 (hd (hc t).1 (hc t).2.1)
    (hB1 ▸ (hc t).2.2.1) (by rw [hW1, div_eq_mul_inv, Nat.add_comm (SqNum.botBig D i j)]; exact resEta_mul (hc t).2.2.1 (resEta_inv (hc t).2.2.2))
  have s1 : (neg A).SigOK := sigOK_sgn true hA2
  obtain ⟨vac, hv⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (neg A) WW (fun τ => -rA.s τ) rW.s
    s1 hW2 (fun τ => isCartanInv_sgn true _ τ (hA4.2.2 τ).1) (fun τ => (hW4.2.2 τ).1) rA.Λ rW.Λ (isSelfDualC_neg' hA4.1) hW4.1
  obtain ⟨vac', hv'⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ A' WW rA'.s rW.s
    hB2 hW2 (fun τ => (hB4.2.2 τ).1) (fun τ => (hW4.2.2 τ).1) rA'.Λ rW.Λ hB4.1 hW4.1
  choose e he using GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G
  choose c hc' using fun t w => GlobalTheory.ConstRatio.exists_expAt (SqNum.nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ A WW rA rW _ _ _ _ _ hA4 hW4 (hd (hc t).1 (hc t).2.1) (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ A' WW rA' rW _ _ _ _ A.rank _ hB4 hW4 (hd (hc t).1 (hc t).2.1) (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas A
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas A'
  exact ⟨A, A', WW, ⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩, hA1, hB1, hA3, hB3, hW3,
    ⟨by rw [hA1, hB1, hW1], hA4, hB4, hW4, hω, hω', hv, hv', he, fun t w _ => hc' t w, hf, hf', hm, hm'⟩⟩

theorem IsBottomTri.integrable {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) :
    (∀ P g, IntegrableOn (X.ker W.ψ W.θ t P g) X.fd X.m) ∧ ∀ P g, IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := by
  have h := hX.is
  have hA := GlobalTheory.ConstRatio.posDef_of_std hX.std
  have hA' := GlobalTheory.ConstRatio.posDef_of_std hX.std'
  refine ⟨fun P g => ?_, fun P g => ?_⟩
  · exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ true A WW _ _ (X.ω t) X.m X.fd _ (h.weil t) hA h.meas.1 h.meas.2
      (GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f h t).1 P)).1 g
  · exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (h.weil' t) hA' h.meas'.1 h.meas'.2
      (GlobalTheory.Chain.InnerSteps.theta_pureTensorO h.isVac'.1 h.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f h t).2 P)).1 g

end GlobalTheory.RowTest

end
