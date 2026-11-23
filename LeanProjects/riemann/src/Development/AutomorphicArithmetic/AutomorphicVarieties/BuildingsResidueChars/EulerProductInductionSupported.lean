import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductInductionUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersTwistedAutomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.CrossGOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SecDiff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem ram3 {ν c : kˣ →* ℂˣ} (hν : IsUnram ν) (hc : ¬ IsUnram c) : Ram3 ν c :=
  ⟨fun h => hc (unr_cancel hν h), hc, fun h => hc (unr_cancel (unr_inv hν) h)⟩

private theorem lin_zero (a : kˣ →* ℂˣ) : (lin a).eval 0 = 1 := by
  unfold lin
  split_ifs <;> simp

private theorem local_linear_factor_eval_zero (a b : kˣ →* ℂˣ) : (lin3 a b).eval 0 = 1 := by
  simp only [lin3, eval_mul, lin_zero, mul_one]

end Loc

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

private theorem unr_iff (u : Ad3.Pl) (a : (u.adicCompletion ℚ)ˣ →* ℂˣ) : IsUnramifiedChar a ↔ IsUnram a := by
  haveI : (Valued.v : Valuation (u.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [isUnramifiedChar_iff]
  refine forall_congr' fun x => imp_congr_left ?_
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq u x.ne_zero, neg_eq_zero,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion ℚ)) Valued.v).eq_one_iff_eq_one]
  have h0 : Valued.v (x : u.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  constructor
  · intro h
    rw [← WithZero.exp_log h0, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

private theorem localChar_mul' (c η : HeckeCharacter ℚ) (u : Ad3.Pl) :
    localChar (c * η) u = localChar c u * localChar η u := by
  ext x
  rfl

private theorem under_eq {K : Type} [Field K] [NumberField K] {p : Ad3.Pl} (w : PlacesOver K p) : w.1.under (𝓞 ℚ) = p :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem exists_above (K : Type) [Field K] [NumberField K] (S : Finset Ad3.Pl) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ w.under (𝓞 ℚ) ∈ S := by
  refine ⟨S.biUnion fun p => (Finset.univ : Finset (PlacesOver K p)).map (Function.Embedding.subtype _), fun w => ?_⟩
  simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, w', rfl⟩
    change w'.1.under (𝓞 ℚ) ∈ S
    rwa [under_eq]
  · exact fun h => ⟨_, h, ⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem unr_of_norm {K : Type} [Field K] [NumberField K] {η : HeckeCharacter ℚ} (hη : EtaOK K η) (c : HChar ℚ)
    {u : Ad3.Pl} (hu : (toH η).UnrAt u) (w : PlacesOver K u) (h : IsUnram ((c.loc u).comp (nm w))) : IsUnram (c.loc u) := by
  have hc := (((hη.loc u w).2.2 _ (GlobalTheory.HeckeComp.smooth_loc c u)).2.2 h)
  have hpos : 0 < ∑ w' : PlacesOver K u, fdeg w' :=
    lt_of_lt_of_le (normVal ℚ K u w 1).2.2.1 (Finset.single_le_sum (f := fun w' : PlacesOver K u => fdeg w')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))
  rw [← hc] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
  have hj' := (Finset.mem_filter.1 hj).2
  have hp : ∀ j : ℕ, IsUnram ((toH η ^ j).loc u) := fun j => by
    induction j with
    | zero => intro x hx; rfl
    | succ j ih =>
      intro x hx
      rw [pow_succ]
      change (toH η ^ j).loc u x * (toH η).loc u x = 1
      rw [ih x hx, (unrAt_iff _ _).1 hu x hx, one_mul]
  exact unr_cancel (hp j) (mul_comm (c.loc u) _ ▸ hj')

private theorem tri_pow (a x : ℂˣ) (f : ℕ) :
    ((({a ^ f, 1, (a ^ f)⁻¹} : Multiset ℂˣ).map (· * x ^ f)).map fun b : ℂˣ => (b : ℂ)) = (tri a x).map (· ^ f) := by
  simp [tri, mul_pow]

theorem UpperTheory.euler_product_induction_supported :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ D : Ad3.Dat, Ad3.An D →
        ∀ (P : CuspSub K 3) (η c : HeckeCharacter ℚ), EtaOK K η → IsOfFinOrder c → ∀ (S₀ : Finset Ad3.Pl) (v : Ad3.Pl)
        (s : ∀ w : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (w.adicCompletion K))), (∀ w, SuppAt P w (s w)) →
        D.bad ⊆ S₀ → v ∈ S₀ →
        (∀ u ∉ S₀, (toH η).UnrAt u ∧ ∀ w : PlacesOver K u, IsPrimitiveRoot ((toH η).val u) (fdeg w) ∧
          Fintype.card (PlacesOver K u) * fdeg w = 2 ∧ w.1 ∉ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∧
          (CG.mk P).HasSat w.1 {D.ν u (unif (u.adicCompletion ℚ)) ^ fdeg w, 1, (D.ν u (unif (u.adicCompletion ℚ)) ^ fdeg w)⁻¹}) →
        (∀ u ∈ S₀, u ≠ v → Ram3 (D.ν u) (localChar c u) ∧ Ram3 (D.ν u) (localChar (c * η) u) ∧
          ∀ w : PlacesOver K u, ∀ ζ ∈ chars (s w.1), ¬ IsUnram (ζ * (localChar c u).comp (nm w))) →
        lin3 (D.ν v) (localChar c v) * lin3 (D.ν v) (localChar (c * η) v) =
          ∏ w : PlacesOver K v, (pol (s w.1) ((localChar c v).comp (nm w))).comp (X ^ fdeg w) := by
  intro K _ _ _ hK D hD P η c hη hc S₀ v s hs hbad hv hout hin
  obtain ⟨ξ, hξ⟩ := normLoc ℚ K (toH c)
  obtain ⟨S, hS⟩ : ∃ S : Finset Ad3.Pl, ∀ u, u ∈ S ↔ u ∈ S₀ ∨ ¬ (toH c).UnrAt u :=
    ⟨S₀ ∪ (GlobalTheory.Mem.UnrAe.finite_ramified (toH c)).toFinset, fun u => by simp⟩
  obtain ⟨MainNotions, hSK⟩ := exists_above K S
  have out0 : ∀ u ∉ S, u ∉ S₀ := fun u hu h => hu ((hS u).2 (Or.inl h))
  have outc : ∀ u ∉ S, (toH c).UnrAt u := fun u hu => not_not.1 fun h => hu ((hS u).2 (Or.inr h))
  have hex : ∀ w : HeightOneSpectrum (𝓞 K), ∃ B : Multiset ℂˣ, (w ∉ MainNotions → (CG.mk (P.twist ξ)).HasSat w B) ∧
      ∀ p ∉ S, ∀ w' : PlacesOver K p, w'.1 = w → (B.map fun b : ℂˣ => (b : ℂ)) = (par D (toH c) p).map (· ^ fdeg w') := by
    intro w
    by_cases hw : w.under (𝓞 ℚ) ∈ S
    · refine ⟨0, fun h => absurd ((hSK w).2 hw) h, fun p hp w' e => ?_⟩
      subst e
      rw [under_eq] at hw
      exact absurd hw hp
    · obtain ⟨u1, v1⟩ := (hξ _ ⟨w, ⟨rfl⟩⟩).2.1 (outc _ hw)
      have h := (((hout _ (out0 _ hw)).2 ⟨w, ⟨rfl⟩⟩).2.2.2).twist u1
      rw [CG.twist_mk, v1] at h
      refine ⟨_, fun _ => h, fun p hp w' e => ?_⟩
      obtain ⟨w', hw'⟩ := w'
      obtain rfl : w' = w := e
      obtain rfl : p = w'.under (𝓞 ℚ) := HeightOneSpectrum.ext hw'.over
      exact tri_pow _ _ _
  choose B hB1 hB2 using hex
  obtain ⟨β, hβ, pL⟩ := UpperTheory.euler_product_induction_unramified K hK D hD η c hη hc S v (fun u hu => (hS u).2 (Or.inl (hbad hu)))
    ((hS v).2 (Or.inl hv)) (fun u hu => (unr_iff u _).2 ((unrAt_iff _ u).1 (outc u hu)))
    (fun u hu => ⟨(hout u (out0 u hu)).1, fun w => ⟨((hout u (out0 u hu)).2 w).1, ((hout u (out0 u hu)).2 w).2.1⟩⟩)
    (fun u hu hne => by
      by_cases h0 : u ∈ S₀
      · exact ⟨(hin u h0 hne).1, (hin u h0 hne).2.1⟩
      · have hν : IsUnram (D.ν u) := (unr_iff u _).1 (D.unr u fun h => h0 (hbad h))
        have hr : ¬ IsUnram (localChar c u) := fun h => ((hS u).1 hu).resolve_left h0 ((unrAt_iff _ u).2 h)
        refine ⟨ram3 hν hr, ram3 hν fun h => hr ?_⟩
        rw [localChar_mul', mul_comm] at h
        exact unr_cancel ((unrAt_iff _ u).1 (hout u h0).1) h)
    (MainNotions : Set _) (cx B) (fun w => by simpa using hSK w) (fun p hp w => hB2 w.1 p hp w rfl)
  obtain ⟨β', hβ', pR⟩ := UpperTheory.satake_parameters_twisted_automorphic K P ξ MainNotions B v s
    (fun w hw => (hSK w).2 (not_not.1 fun h => ((hout _ (out0 _ h)).2 ⟨w, ⟨rfl⟩⟩).2.2.1 hw)) hB1 hs
    (fun w => (hSK w.1).2 (by rw [under_eq]; exact (hS v).2 (Or.inl hv)))
    (fun w hw hne ζ hζ => by
      rw [(hξ (w.under (𝓞 ℚ)) ⟨w, ⟨rfl⟩⟩).1]
      by_cases h0 : w.under (𝓞 ℚ) ∈ S₀
      · exact (hin _ h0 hne).2.2 ⟨w, ⟨rfl⟩⟩ ζ hζ
      · intro h
        obtain ⟨hζ', hm⟩ := hζ
        obtain ⟨μ, hμ, e⟩ := (suppFacts K 3 (by omega) P w).2.2.2.1 _ _ (hs w) ((hout _ h0).2 ⟨w, ⟨rfl⟩⟩).2.2.2 _ hm
        rw [(polFacts _).2.2.1 _ _ _ _ e] at h
        exact ((hS _).1 ((hSK w).1 hw)).resolve_left h0
          ((unrAt_iff _ _).2 (unr_of_norm hη (toH c) (hout _ h0).1 ⟨w, ⟨rfl⟩⟩ (unr_cancel hμ h))))
  have e : ∀ w : PlacesOver K v, ξ.loc w.1 = (localChar c v).comp (nm w) := fun w => (hξ v w).1
  simp only [e] at pR
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine crossGOf expAlg expIndep secDiff _ _ _ _ _ _ _ (by exact_mod_cast hq) hβ hβ' ?_ ?_ pL pR
  · rw [eval_mul, local_linear_factor_eval_zero, local_linear_factor_eval_zero, mul_one]
  · rw [eval_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [eval_comp, eval_pow, eval_X, zero_pow (normVal ℚ K v w 1).2.2.1.ne']
    exact ((polFacts _).2.2.2 _ _).1
