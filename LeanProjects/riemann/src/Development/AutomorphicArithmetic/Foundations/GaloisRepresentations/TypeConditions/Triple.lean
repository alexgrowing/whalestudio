import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.FrobDualOfTripleAttN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTrivialEverywhere
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjOfFrobeniusMatch
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeneralAdmissibleOfIrreducibilityStmt

noncomputable section

namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TripleLocal

theorem galW {D : D7} {a : ℕ} {π : D.naut.CG a} {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin a) (Qbar l)} (h : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.IsGaloisRepOf D π l ι r) :
    IsGaloisRepOfN D π l ι r := ⟨h.1, h.2.1, fun w hw => ⟨fun _ => (h.2.2 w hw).1,
      fun u => (h.2.2 w hw).2.1.1 ((D.naut.monomial_twist_iff _ _).2 (D.naut.unr_mono0 _ u)), (h.2.2 w hw).2.2⟩⟩
theorem galW' {D : D7} {a : ℕ} {π : D.naut.CG a} {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin a) (Qbar l)} (h : IsGaloisRepOfN D π l ι r) : IsGaloisRepOfN D π l ι r := h

end UpperTheory.GalS

namespace GlobalTheory.TripleResidual
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise
variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)

theorem charpoly_cConj_eq_charpoly_cyc_zpow_smul_inv (hD : FrobDense D) {n : ℕ} {π : D.naut.CG n} (hπ : D.naut.csd π) {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {r : GalE D →* GL (Fin n) (Qbar l)} (hr : UpperTheory.GalS.IsGaloisRepOfN D π l ι r) (g : GalE D) :
    ((r (cConj Y g) : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      ((((cyc D.host.E D.nd.Om l g : (Qbar l)ˣ) : Qbar l) ^ (1 - (n : ℤ))) •
        ((r g⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l))).charpoly := by
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  obtain ⟨bar, hinj, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  obtain ⟨hcont, -, hfr⟩ := hr
  have hl := (GlobalTheory.ConjPoly.finite_placesOver D.host.E l (Fact.out : l.Prime).ne_zero).compl_mem_cofinite
  have hall := (D.naut.locG_unr_ae π).and hl
  have hcc : Continuous (cConj Y) := GlobalTheory.AntiLAdic.continuous_conjHom Y.cc (cc_symm_mem Y)
  refine GlobalTheory.TypeLeaf.charpoly_eq_of_dense (GalE D) (Qbar l) n
    (fun g => ((r (cConj Y g) : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)))
    (fun g => (((cyc D.host.E D.nd.Om l g : (Qbar l)ˣ) : Qbar l) ^ (1 - (n : ℤ))) •
        ((r g⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l))) _ (hD _ (Filter.eventually_cofinite.1 hall))
    (hcont.comp hcc)
    (((GlobalTheory.ConjPoly.continuous_cyc_val D.host.E D.nd.Om l).zpow₀ (1 - (n : ℤ))
      fun g => Or.inl (Units.ne_zero _)).fun_smul (hcont.comp continuous_inv)) ?_ g
  rintro σ ⟨w, hw, -, B, hB, hσ⟩
  obtain ⟨hu, hwl⟩ := not_not.1 hw
  obtain ⟨hcj, hn, -⟩ := hbar w
  obtain ⟨hu', he⟩ := D.naut.csd_unr π w (bar w) hπ hcj hu
  have e1 := (hfr w hwl).2.2 hu B σ hB hσ
  have e2 := (hfr (bar w) fun h => hwl (mem_placesOver_conj (isConjPl_symm hcj) h)).2.2 hu' _ _
    (isPlaceOver_moveVal_cc Y hcj hB) (by rw [hn]; exact isFrob_cConj Y hσ)
  rw [galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  rw [galPol, D.naut.frobEig_tw _ _ hu', he, hn, ← Matrix.charpoly_map] at e2
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.ConjPoly.normV_ne_zero w)
  have e3 := GlobalTheory.ConjPoly.charpoly_smul_inv _
    (((r σ⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)).map ι.toRingHom)
    (by rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]) _ (((normV w : ℕ) : ℂ) ^ (1 - (n : ℤ))) e1
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, GlobalTheory.ConjPoly.cyc_val_frob hwl hB hσ]
  refine e2.trans (Eq.trans ?_ (e3.symm.trans ?_))
  · rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    rw [GlobalTheory.ConjPoly.cpow_sq hq ((1 - (n : ℝ)) / 2) _ (by push_cast; ring)]
    have : ((normV w : ℕ) : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) ≠ 0 := by
      simp [hq]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right₀ this, mul_comm a⁻¹]
  · congr 1
    ext a b
    simp

end GlobalTheory.TripleResidual

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
namespace GlobalTheory.TripleLocal

theorem conj_of_frobMatch_alt : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → ∀ (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : D.naut.CG a) (s : ℝ) (r r' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)),
    IsAttachedAwayS D T ι π s r → Continuous (fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep r' →
    FrobMatch D π ι.toRingHom r' (s + (1 - (a : ℝ)) / 2) → ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := by
  intro D T hD l _ ι a π s r r' h hc' hss' hm
  have hall := (hm.and (D.naut.locG_unr_ae π)).and (frobConj_natCast_notMem D.host.E l)
  have htr : ∀ g, ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
    intro g
    refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 hall))
      (h.cont.matrix_trace) (hc'.matrix_trace) ?_) g
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨⟨h1, hu⟩, hl⟩ := not_not.1 hw
    have e1 := (h.frob hl hu).2 B σ hB hσ
    have e2 := h1 B σ hB hσ
    have e : ((r σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
        ((r' σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
      Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)
    show Matrix.trace _ = Matrix.trace _
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.trace]
    · haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]
  exact GlobalTheory.TraceConj.conj_of_trace_eq _ _ a r r' h.ss hss' htr

end GlobalTheory.TripleLocal

namespace GlobalTheory.GoodRowMono
variable {D : D7}

theorem sep_over_g {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (hG : UpperTheory.GalS.GalHodgeN D T)
    {σ : D.what₂.FT} {π : D.naut.CG D.R.r} (hg : D.nd.goodRow σ) (hc : D.naut.csd π)
    (hlab : ∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v)))
    (k : Fin 2) {w : PlE D.host} (hk : w ∈ placesOver D.host.E (D.host.g k)) :
    UpperTheory.GalS.Sep D.nd D.naut (D.naut.locG π w) := by
  have h0 : ∀ v, UpperTheory.GalS.Sep D.nd D.naut (D.naut.locG π (D.naut.plGw k v)) := fun v =>
    ⟨fun u hu hw => hG.2.1 k v _ (by rw [← hlab, (D.nd.lab_monic k σ v).2, D.naut.locG_dim]) u hu hw,
      _, D.ntypes.tg_mem k v, separable_fixed hg hlab k v⟩
  obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hk
  · exact h0 v
  · exact hG.2.2.1 π hc _ _ hv (h0 v)

end GlobalTheory.GoodRowMono
end

namespace GlobalTheory.TripleLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleGal
open GlobalTheory.TypeLeaf (FrobDense)
variable {D : D7} {T : WDTie D.nd D.naut} {i : D.ntw.Tw} {j : FractionRing (D.ntw.O0 i) →+* ℂ}
  {ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i)} {π : D.naut.CG D.R.r} {s : ℝ}

theorem exists_isAttachedHodgeS_conj_mapRep (hF : FrobDense D) (hG : UpperTheory.GalS.GalHodgeN D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ} (hφ : Continuous φ)
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ)) :
    ∃ r A, IsAttachedHodgeS D T ι π s r ∧ ∀ g, mapRep φ ρ g = A * r g * A⁻¹ := by
  obtain ⟨r, h⟩ := hG.1 _ ι π s hc hr
  have e : ι.toRingHom.comp φ = rd i j := RingHom.ext hι
  obtain ⟨A, hA⟩ := conj_of_frobMatch_alt D T hF _ ι _ π s r (mapRep φ ρ) h.toIsAttachedAwayS (hρ.matrix_map hφ) hs
    (hM.mono fun w hw B σ hB hσ => by
      rw [← hw B σ hB hσ, ← e, ← Polynomial.map_map, ← Matrix.charpoly_map _ φ]
      rfl)
  exact ⟨r, A, h, hA⟩

theorem exists_conj_br_alt (hF : FrobDense D) (hG : UpperTheory.GalS.GalHodgeN D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ}
    (hφ : ∀ z : ℤ_[D.ntw.l i], φ (algebraMap _ _ z) = algebraMap ℚ_[D.ntw.l i] _ (z : ℚ_[D.ntw.l i]))
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ))
    (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    ∃ (ι' : Qbar (D.ntw.l i) ≃+* ℂ) (r : _) (A : GL (Fin D.R.r) (Qbar (D.ntw.l i))),
      (∀ x, ι' (brEmb i v hv x) = rd i j x) ∧ IsAttachedHodgeS D T ι' π s r ∧
      ∀ g, resDec D.nd.plOm.1 (mapRep (brEmb i v hv) ρ) v g = A * resDec D.nd.plOm.1 r v g * A⁻¹ := by
  have hj : Function.Injective (rd i j) := j.injective.comp (IsFractionRing.injective _ _)
  have h1 : Function.Injective φ := fun x y h => hj (by rw [← hι, ← hι, h])
  have h2 : Function.Injective (brEmb i v hv) :=
    (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).injective.comp (GlobalTheory.EmbInj.toLL_inj _)
  obtain ⟨γ, hγ⟩ := exists_aut φ (brEmb i v hv) h1 h2 hφ fun z =>
    congrArg (fun y : ↥(OL (D.ntwbr i v hv).LL) => ((y : ↥(D.ntwbr i v hv).LL.1) : Om (D.ntw.l i)))
      ((D.ntwbr i v hv).eO_alg z)
  have h3 : ∀ x, (γ.symm.trans ι) (brEmb i v hv x) = rd i j x := fun x => by
    rw [← hγ, RingEquiv.trans_apply, γ.symm_apply_apply, hι]
  have h4 : mapRep (brEmb i v hv) ρ = mapRep γ.toRingHom (mapRep φ ρ) := by
    ext g a b
    exact (hγ _).symm
  obtain ⟨r, A, h, hA⟩ := exists_isAttachedHodgeS_conj_mapRep hF hG hc hr hρ hM (φ := brEmb i v hv)
    (continuous_subtype_val.comp (continuous_subtype_val.comp (D.ntwbr i v hv).eO_cont)) h3
    (h4 ▸ GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ _ _ _ hs)
  exact ⟨_, r, A, h3, h, fun g => hA g⟩

theorem attN_of_isSSRep_mapRep_of_nc_locG (hF : FrobDense D) (hG : UpperTheory.GalS.GalHodgeN D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ} (hφc : Continuous φ)
    (hφ : ∀ z : ℤ_[D.ntw.l i], φ (algebraMap _ _ z) = algebraMap ℚ_[D.ntw.l i] _ (z : ℚ_[D.ntw.l i]))
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ))
    (hN : ∀ v ∈ placesOver D.host.E (D.ntw.l i), UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π v)) :
    AttN D.naut (bk0 D) i j ρ π (s + (1 - (D.R.r : ℝ)) / 2) := by
  have hj : Function.Injective (rd i j) := j.injective.comp (IsFractionRing.injective _ _)
  have h1 : Function.Injective φ := fun x y h => hj (by rw [← hι, ← hι, h])
  obtain ⟨r, A, h, hA⟩ := exists_isAttachedHodgeS_conj_mapRep hF hG hc hr hρ hM hφc hι hs
  refine ⟨fun w hw hu σ hσ => ?_, fun w hw hu B σ hB hσ => ?_, fun w hw => h.temp w hw, fun v hv => ?_,
    fun v hv τ τc hτ a => ?_⟩
  · have h2 := hA σ
    rw [(h.toIsAttachedAwayS.frob hw hu).1 σ hσ, mul_one, mul_inv_cancel] at h2
    refine Units.ext (Matrix.map_injective h1 ?_)
    exact (congrArg Units.val h2).trans (Matrix.map_one φ (map_zero φ) (map_one φ)).symm
  · rw [← (h.toIsAttachedAwayS.frob hw hu).2 B σ hB hσ, ← (RingHom.ext hι : ι.toRingHom.comp φ = rd i j),
      ← Polynomial.map_map, ← Matrix.charpoly_map _ φ]
    have h2 : ((mapRep φ ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).charpoly =
        ((r σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).charpoly := by
      rw [hA, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact congrArg (Polynomial.map ι.toRingHom) h2
  · obtain ⟨ι', r', A', -, h', hA'⟩ := exists_conj_br_alt hF hG hc hr hρ hM hφ hι hs v hv
    obtain ⟨a1, a2, a3⟩ := h'.above v hv _ (D.ntwbr i v hv) (D.ntwbr_ind i v hv)
    obtain ⟨b1, b2, b3, -⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant _ (D.loc _) _ _ _ _ (D.ntwbr i v hv) _ _ _ A' hA'
    exact ⟨((isModel_brEmb v hv).isdRAt_iff _).1 (b1 (a1 (hN v hv)).deRham),
      fun hu => ((isModel_brEmb v hv).isCrysAt_iff _).1 (b2 (a2 hu)),
      fun _ => ((isModel_brEmb v hv).isPotCrysAt_iff _).1 (b3 (a3 (hN v hv)))⟩
  · obtain ⟨ι', r', A', hι', h', hA'⟩ := exists_conj_br_alt hF hG hc hr hρ hM hφ hι hs v hv
    obtain ⟨a1, -, -⟩ := h'.above v hv _ (D.ntwbr i v hv) (D.ntwbr_ind i v hv)
    obtain ⟨-, -, -, b4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant _ (D.loc _) _ _ _ _ (D.ntwbr i v hv) _ _ _ A' hA'
    let c : D.host.E →+* ↥(D.ntwbr i v hv).Kw.1 :=
      ((D.ntwbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)).codRestrict (D.ntwbr i v hv).Kw.1 (D.ntwbr i v hv).j_E
    let τ₀ : D.host.E →+* Qbar (D.ntw.l i) :=
      (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).comp ((AlgHom.toRingHom τ).comp c)
    have hi : IsInduced (D.ntwbr i v hv) τ₀ τ := fun _ => rfl
    have e : ι'.toRingHom.comp τ₀ = τc := by
      ext x
      obtain ⟨n, d, hd, hnd⟩ := GlobalTheory.EmbInj.exists_frac (D.ntwbr i v hv) (τ (c x))
      have h3 := (map_mul (ι'.toRingHom.comp (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i)))) _ _).symm.trans
        (congrArg _ hnd)
      have h4 : rd i j d * ι' (τ₀ x) = rd i j n := by rw [← hι', ← hι']; exact h3
      exact mul_left_cancel₀ ((map_ne_zero_iff _ hj).2 hd) (h4.trans (hτ x n d ⟨hd, hnd⟩).symm)
    obtain ⟨J, hJ, hJ'⟩ := (a1 (hN v hv)).jumps τ₀ _ τ hi
    refine ((b4 τ₀ J hJ').count_eq _ (isModel_brEmb v hv) hi a).symm.trans ?_
    rw [e] at hJ
    rw [← Multiset.count_map_eq_count' (fun n : ℤ => (n : ℂ)) J Int.cast_injective, hJ]
    congr 2
    refine Multiset.map_congr rfl fun z _ => ?_
    push_cast
    ring
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}

end

end GlobalTheory.TripleLocal
