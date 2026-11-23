import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpansLeContinuousCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthHeckeValueIdealLeDeterminantBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCutCoboundaryModuleLeUnitDeltaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesAboveEllInCutUnitDeltaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocycleBlockLengthLeOfQuadraticRelationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaRestrictionPolynomialConditionSecondFormStatement

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut Module

noncomputable section

namespace GlobalTheory.CutCoreUnit

variable {D : D7} (i : D.nd.Loc)

theorem ccOff_univ (π : D.nd.X i) : ccOff i Set.univ π = ccAt (D.nd.T i) (D.nd.Z i) π := by
  rw [ccOff, ccAt, Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨f, hf, h0, rfl⟩
    refine ⟨⟨f, hf⟩, ?_, rfl⟩
    change (⟨f, hf⟩ : D.nd.T i) ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    funext y
    exact h0 y.1 trivial y.2
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f.1, f.2, fun x _ hx => ?_, rfl⟩
    change f ∈ RingHom.ker _ at hf
    rw [RingHom.mem_ker] at hf
    exact congrFun hf ⟨x, hx⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  intro hA D i r ρ π S hr hS hZ hN hU hSv hQ hl hsel hsha
  classical
  have hπ : π ∈ (Set.univ : Set (D.nd.X i)) := trivial
  obtain ⟨L, hL⟩ := CutCore.exists_length_quot (GlobalTheory.LenUnitPow.natCast_ne_zero (D.nd.l i) (O := D.nd.O i))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact GlobalTheory.LenUnitPow.natCast_not_isUnit (D.nd.l i) (O := D.nd.O i) (CutCore.length_quot_eq_zero_iff.mp hL)
  have hd : lenQ i (del51 D.nd S S.π') = 0 :=
    CutCore.length_quot_eq_zero_iff.mpr hS.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hsel)

  have hρ : Module.length (D.nd.O i) ↥(cocRho i r S Set.univ) ≤ (s : ℕ∞) := by
    obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Set.univ _ (WpO D.nd i ρ π) (cocRho i r S Set.univ) 0
      (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).1⟩)
    rw [mul_zero, Nat.cast_zero, zero_mul, zero_add] at hlen
    refine hlen.trans ((GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer D i ρ π C (hC.trans (GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles D i r ρ π Set.univ S hr hS hπ).1) hfin ?_).trans ?_)
    · intro v h1 h2 h3
      exact CutCore.resIne_eq_bot_of_le i hC
        (GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ S.ψρ (CutCore.inR'_one i r S) hU v h1 h2 h3)
    · have hc := (CutCore.lenCob_mono i _ hC).trans (GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta D i r ρ π Set.univ S hr hS hπ).1
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc
      rw [hc, zero_add, ← hs]

  have hχ : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * (if (c : ℕ) = 0 then ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞)
          else Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c : ℕ) : ℤ)) +
        ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) := by
    intro c
    obtain ⟨C', hC', hq, hlen'⟩ := GlobalTheory.Cut.Peel.main D i 1 (cocChi i r S Set.univ c) (D.nd.Q i)
    have hZ1 := hC'.trans ((GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles D i r ρ π Set.univ S hr hS hπ).2 c)
    have hunr : ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C' v = ⊥ := by
      intro v h1
      by_cases h3 : v ∈ D.nd.Q i
      · exact hq v h3
      refine CutCore.resIne_eq_bot_of_le i hC' ?_
      by_cases h2 : v ∈ D.nd.S i
      · rcases hSv v h2 with ⟨hqd, hu⟩ | hp
        · have h := GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation D i r ρ π Set.univ S hr hS hπ v (Or.inl h2) hqd c
          rw [lenQ, CutCore.length_quot_eq_zero_iff.mpr hu, nonpos_iff_eq_zero, Module.length_eq_zero_iff] at h
          exact Submodule.subsingleton_iff_eq_bot.mp h
        · exact GlobalTheory.T.inertia_restriction_polynomial_condition_second_form D i r ρ π Set.univ S hr hS hπ v h2 hp c
      · exact GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ _ (CutCore.inR'_one i r S) hU v h1 h2 h3
    refine hlen'.trans (add_le_add ?_ (Finset.sum_le_sum fun q hq' =>
      GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation D i r ρ π Set.univ S hr hS hπ q (Or.inr hq') (hQ q hq').1 c))
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc]
      have e : (c : ℕ) + 1 = 1 := by omega
      rw [e] at hZ1
      have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), ∀ f ∈ C',
          InCut i r Set.univ (chiRatO D.nd i 1) w hw f := by
        intro w hw f hf
        have h := (GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf)
        rwa [e] at h
      refine GlobalTheory.UnramHom.length_le_classNumber hA D i C' hZ1 fun v => ?_
      by_cases hv : v ∈ placesOver D.host.E (D.nd.l i)
      · exact GlobalTheory.CutTrivIne.main D i C' v hv fun f hf =>
          (Submodule.span_le.mpr fun z hz => (hl v hv).2.2 z hz) (hloc v hv f hf)
      · exact hunr v hv
    · rw [if_neg hc]
      have h2 : 2 ≤ (c : ℕ) + 1 := by omega
      have ht : (c : ℕ) + 1 ≤ D.R.t := c.2
      have h := GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha D i ((c : ℕ) + 1) C' hZ1 h2 ht
        (fun f hf w hw => (Submodule.span_le.mpr fun z hz =>
          (hl w hw).2.1 _ (Finset.mem_Icc.mpr ⟨h2, ht⟩) z hz)
            ((GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf))) hunr
      rw [Nat.add_sub_cancel] at h
      have hc0 := (CutCore.lenCob_mono i _ hC').trans ((GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta D i r ρ π Set.univ S hr hS hπ).2 c)
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc0
      rw [hc0, zero_add] at h
      exact h

  have hz : ∀ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) = ((lenQ i (D.nd.zeta i q - 1)).toNat : ℕ∞) := by
    intro q hq
    obtain ⟨n, hn⟩ := CutCore.exists_length_quot (sub_ne_zero.mpr (hQ q hq).2)
    rw [lenQ, hn, ENat.toNat_coe]
  set z : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun q => (lenQ i (D.nd.zeta i q - 1)).toNat with hzdef
  set g : ℕ → ℕ := fun e => (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)).toNat with hg
  have hg' : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) = (g e : ℕ∞) :=
    fun e he => (ENat.coe_toNat (hsha e he).ne).symm
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set h := padicValNat (D.nd.l i) (hE D.host) with hh
  have hχ' : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      ((L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q : ℕ) : ℕ∞) := by
    intro c
    refine (hχ c).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl hz, lenQ, hL]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc, if_pos hc]
      push_cast
      rfl
    · rw [if_neg hc, if_neg hc, hg' c (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hc, c.2⟩)]
      push_cast
      rfl
  have htot := (GlobalTheory.T.length_heckeValueIdeal_le_determinant_bound D i r ρ π Set.univ S hr hS hπ hZ hN).trans
    (add_le_add hρ (Finset.sum_le_sum fun c _ => hχ' c))
  rw [← Nat.cast_sum, ← Nat.cast_add] at htot
  have hnat := ENat.toNat_le_of_le_coe htot
  have hsum : ∑ c : Fin D.R.t, (L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q) =
      L * (h + ∑ e ∈ Finset.Ioo 0 D.R.t, g e) + D.R.t * ∑ q ∈ D.nd.Q i, z q := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, CutCore.sum_fin_ite ht, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hsum] at hnat
  have hsp : Br.sPi D.loc D.nbr i ρ π = (s : ℚ) / L := by
    rw [Br.sPi, lenUnit, hL, ← hs, ENat.toNat_coe, ENat.toNat_coe]
  have hsh : ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, g e : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e he =>
      D.nd.sha_eq _ e (Finset.mem_Ioo.mp he).1 (Finset.mem_Ioo.mp he).2 _ (hg' e he)
  have hzq : ∑ q ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) =
        ((∑ q ∈ D.nd.Q i, z q : ℕ) : ℚ) / L := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lenUnit, hL, ENat.toNat_coe]
    rfl
  show lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤ _
  rw [← ccOff_univ, hsp, hsh, hzq, lenUnit, hL, ENat.toNat_coe]
  have hLq : (0 : ℚ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  generalize (Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Set.univ π)).toNat = a at hnat
  generalize ∑ e ∈ Finset.Ioo 0 D.R.t, g e = G at hnat ⊢
  generalize ∑ q ∈ D.nd.Q i, z q = Z at hnat ⊢
  have hq : (a : ℚ) ≤ ((s + (L * (h + G) + D.R.t * Z) : ℕ) : ℚ) := Nat.cast_le.mpr hnat
  push_cast at hq
  rw [div_le_iff₀ hLq]
  have e : ((s : ℚ) / L + G + (h : ℚ) + (D.R.t : ℚ) * ((Z : ℚ) / L)) * L =
      s + G * L + h * L + D.R.t * Z := by
    field_simp
  rw [e]
  nlinarith [hq]

end GlobalTheory.CutCoreUnit
