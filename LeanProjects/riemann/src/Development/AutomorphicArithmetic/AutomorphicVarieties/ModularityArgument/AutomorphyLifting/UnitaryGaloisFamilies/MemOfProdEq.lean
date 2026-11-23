import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.GalAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpehParameterStrings
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.KernelSemisimpleCharpolyProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitarStatement

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem tw_one {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (g : Γ) :
    UpperTheory.V.W.mat (UpperTheory.V.Af.tw r 1) g = (r g : Matrix (Fin n) (Fin n) k) := by
  change (UpperTheory.V.Af.tw r 1 g : Matrix (Fin n) (Fin n) k) = _
  rw [UpperTheory.V.Af.tw_val]
  simp

open Polynomial in
private theorem mem_of_prod_eq {I : Type} [Fintype I] {b : Multiset ℂ} {B : I → Multiset ℂ}
    (h : (b.map fun x => X - C x).prod = ∏ i, ((B i).map fun x => X - C x).prod) {z : ℂ} (hz : z ∈ b) : ∃ i, z ∈ B i := by
  rw [← Multiset.prod_sum, ← UpperTheory.V.Af.Es.map_sum_ms] at h
  have e := congrArg Polynomial.roots h
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e
  simpa [e, Multiset.mem_sum] using hz

open GlobalTheory.WeilDeligne UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Af.Es UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu in
theorem UpperTheory.V.Z.Win.Gu.endShape_of (hB : GlobalTheory.BcSpeh.BcSpeh) (hLink : SatLink) (hHalf : HalfG) (hRec : RecTotT) (hFrob : FrobTotT)
    (hTw : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ t : ℝ, (ParAtT ι r w fun _ _ rc => (rc (cl σ)).lpTw t) → FrobEig ι r w (B.map fun α : ℂˣ => (α : ℂ) * ((normV w : ℕ) : ℂ) ^ (-(t : ℂ)))) :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → IsSSRep ρ → (∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → LocGlobT ι ρ w τ) → ∃ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, G E Ω →* GL (Fin (d i)) (Qbar l)), (∀ i, 1 ≤ d i ∧ 1 ≤ m i ∧ Continuous (ρ' i)) ∧ (∀ g, (UpperTheory.V.W.mat ρ g).charpoly = ∏ i, ∏ j ∈ Finset.range (m i), (UpperTheory.V.W.mat (UpperTheory.V.Af.tw (ρ' i) (cycBar E Ω l ^ (-(j : ℤ)))) g).charpoly) ∧ ((∀ i, m i = 1) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ b : Multiset ℂ, UpperTheory.V.Af.FrobEig ι ρ w b → ∀ z ∈ b, ∀ z' ∈ b, ‖z‖ < (normV w : ℝ) * ‖z'‖) := by
  intro E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ R hRc hRs hR
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ := hB E hE n hn π hπ
  have hint : ∀ i τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) 0 : ℂ) / 2 = j := fun i τ => by
    obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ
    exact (UpperTheory.speh_parameter_strings n c d (m · τ) lam (hP.weight τ lam hl)).1 i ⟨0, (hP.pos i).2⟩
  choose r HT hr _ using fun i =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i)
      (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) 0) (hint i)
  have hch : ∀ g, (UpperTheory.V.W.mat R g).charpoly = ∏ i, ∏ j ∈ Finset.range (d i),
      (UpperTheory.V.W.mat (tw (r i) (cycBar E Ω l ^ (-(j : ℤ)))) g).charpoly := fun g => by
    have := charpoly_eq_prod ι (I := Σ i, Fin (d i)) (a := fun x => a x.1) R
      (fun x => tw (r x.1) (cycBar E Ω l ^ (-((x.2 : ℕ) : ℤ)))) hRc
      (fun x => UpperTheory.galoisRep_irreducibility_criterion.2 _ _ _ _ _ (hr x.1).cont (cyc_cont.zpow _)) ?_ g
    · rw [Fintype.prod_sigma] at this
      exact this.trans (Finset.prod_congr rfl fun i _ => (Finset.prod_range fun j =>
        (UpperTheory.V.W.mat (tw (r i) (cycBar E Ω l ^ (-(j : ℤ)))) g).charpoly).symm)
    filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w hw h2 hd
    obtain ⟨S, hS'⟩ := Classical.skolem.1 h2
    have hSat : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i) := fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS' i)
    have hsp := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
    let τ : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
      ⟨_, locProd hsum w (σ · w), GlobalTheory.SmGL.isSmooth_parInd _ _, (hsplit w hsp).1⟩
    have hpar : ParAtT ι R w (totPar n d (ρ · w)) := fun A h rc hrc =>
      (hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) τ ⟨.refl _⟩ A h rc hrc).symm ▸
        hR w hsp τ (hsplit w hsp) A h rc hrc
    refine ⟨_, algSat_satTot w n d S ▸ hFrob E Ω l ι n c a d R hRc w hw (ρ · w) S hSat hpar, fun x => ?_⟩
    exact UpperTheory.frobenius_eigenvalues_twist E Ω l ι _ _ _ w _ _ (hTw E Ω l ι _ (r x.1) w hw _ _ (hSat x.1) _ ((hr x.1).par w))
      (charEig_cyc ι hw _)
  refine ⟨c, a, d, r, fun i => ⟨(hP.pos i).1, (hP.pos i).2, (hr i).cont⟩, hch, fun h1 => ?_⟩
  have hch' : ∀ g, (R g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      ∏ i, (r i g : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly := fun g =>
    (hch g).trans (Finset.prod_congr rfl fun i _ => by
      rw [h1 i, Finset.prod_range_one, Nat.cast_zero, neg_zero, zpow_zero, tw_one])
  filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w hw h2 b hb
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨s, hs⟩ := Formalism.MainNotions.LatticeVariant.exists_isFrob A w hA
  obtain ⟨S, hS'⟩ := Classical.skolem.1 h2
  have hSat : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i) := fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS' i)
  have hF := fun i => (hTw E Ω l ι _ (r i) w hw _ _ (hSat i) _ ((hr i).par w) A hA).2 s hs
  have e := (hb A hA).2 s hs
  rw [hch', Polynomial.map_prod, Finset.prod_congr rfl fun i _ => hF i] at e
  have hq : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq0 : (0 : ℝ) < (normV w : ℕ) := by
    rw [hq]; exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w)
  have key : ∀ z ∈ b, (normV w : ℝ) ^ (-(1 / 2) : ℝ) * (normV w : ℝ) ^ (((n : ℝ) - 1) / 2) < ‖z‖ ∧
      ‖z‖ < (normV w : ℝ) ^ (1 / 2 : ℝ) * (normV w : ℝ) ^ (((n : ℝ) - 1) / 2) := fun z hz => by
    obtain ⟨i, hi⟩ := mem_of_prod_eq e.symm hz
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hi
    have hu := UpperTheory.GalN.satake_window E (a i) (P i) (hP.csd i) w _ (hP.loc i w) _ (hSat i) α hα
    rw [← hq] at hu
    rw [norm_mul, ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.norm_real, Real.norm_of_nonneg (by positivity), h1 i]
    have ee : ∀ t : ℝ, t = ((n : ℝ) - 1) / 2 → (normV w : ℝ) ^ (-(1 / 2) : ℝ) * (normV w : ℝ) ^ (((n : ℝ) - 1) / 2) < ‖(α : ℂ)‖ * (normV w : ℝ) ^ t ∧
        ‖(α : ℂ)‖ * (normV w : ℝ) ^ t < (normV w : ℝ) ^ (1 / 2 : ℝ) * (normV w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
      rintro _ rfl
      exact ⟨mul_lt_mul_of_pos_right hu.1 (by positivity), mul_lt_mul_of_pos_right hu.2 (by positivity)⟩
    refine ee _ ?_
    simp only [ex]
    push_cast
    ring
  intro z hz z' hz'
  refine (key z hz).2.trans_le (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left (key z' hz').1.le hq0.le))
  rw [← mul_assoc]
  congr 1
  nth_rewrite 2 [← Real.rpow_one (normV w : ℝ)]
  rw [← Real.rpow_add hq0]
  norm_num

end
