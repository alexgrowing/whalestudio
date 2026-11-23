import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionOrderAboveLFiniteModulesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityPerfectPairFiniteModulesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLSaturatedOfSelmerSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.SelOrder

theorem cupB_sub_cob {Γ A M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
    {n : ℕ} (χ : Γ → ZMod n) (π : Representation A Γ M) (π' : Representation A Γ M') (P : M →+ M' →+ ZMod n)
    (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x : Γ → M) (y y' : Γ → M') (m : M')
    (hx : Continuous x) (hx' : ∀ g h, x (g * h) = x g + π g (x h)) (hm : Continuous fun g => π' g m)
    (hy : ∀ g, y' g = y g - (π' g m - m))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x y' := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P (x g) (π' g m), hF.add (((IsLocallyConstant.iff_continuous _).2 (hx.prodMk hm)).comp
    fun p : M × M' => P p.1 p.2), fun g k => ?_⟩
  have h1 := h g k
  have h2 := hP g (x k) (π' k m)
  simp only [hy, map_add, map_sub, AddMonoidHom.add_apply, Pi.add_apply, hx', map_mul, Module.End.mul_apply] at h1 ⊢
  linear_combination h1 + h2

theorem tors_all (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (B : Type) [AddCommGroup B] [Module A B] :
    Tors A B := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine fun b => ⟨n, fun x hx => ?_⟩
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

section General

open Formalism.GaloisCohomology

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] (n : ℕ) {Λ W W' : Type} [CommRing Λ]
  [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W]
  [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W']

theorem order_formula (hPT : PoitouTateTotallyComplex) (hLF : LocalFiniteness) (hLD : LocalTateDuality)
    (hLE : LocalEulerChar) (hGF : GlobalFiniteness) (hGE : GlobalEulerChar)
    (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)) (hn : 0 < n)
    (hc : ContAction ρ) (hc' : ContAction ρ') (hl : ∀ x, (∀ y, P x y = 0) → x = 0) (hr : ∀ y, (∀ x, P x y = 0) → y = 0)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y)
    (A : Places F Ω) (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (hTl : ∀ v ∈ T, v ∉ placesOver F l) (hQl : ∀ v ∈ Q, v ∉ placesOver F l)
    (hur : ∀ v, v ∉ placesOver F l → v ∉ T → v ∉ Q → ∀ B : ValuationSubring Ω, IsPlaceOver B v →
      ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1)
    (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (C : Set (H1 ρ'))
    (hC : ∀ c, c ∈ C ↔ ∃ y : Z1 ρ',
      ((∀ v, v ∉ placesOver F l → v ∉ T → v ∉ Q → ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧
        (∀ v, v ∈ T ∨ v ∈ Q → ∃ m, ∀ g ∈ Dec (F := F) (A.1 v), y.1 g = ρ' g m - m) ∧
        ∀ v ∈ placesOver F l, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v →
          CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
            (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) ∧ c = Submodule.Quotient.mk y)
    (h0 : H0 ρ = ⊥) (h0' : H0 ρ' = ⊥) (hT0 : ∀ v ∈ T, H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype) = ⊥)
    (hcount : ∏ᶠ v ∈ placesOver F l, Nat.card (L v) =
      (∏ᶠ v ∈ placesOver F l, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
        Nat.card W ^ InfinitePlace.nrComplexPlaces F) :
    Finite C ∧ Nat.card (SelAll ρ A (bkCond ρ A l (T ∪ ↑Q) L)) =
      Nat.card C * ∏ v ∈ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) := by
  classical
  have hfin := GlobalTheory.SelObstruction.finite_above (F := F) l
  have hsub : ∀ {M : Type} [AddCommGroup M] [Module Λ M] [TopologicalSpace M] [DiscreteTopology M]
      (π : Representation Λ (G F Ω) M), ContAction π → ∀ U : Subgroup (G F Ω), ContAction (π.comp U.subtype) :=
    fun π h U => h.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hloc := fun v => GlobalTheory.T.localDuality_perfect_pair_finite_modules hLF hLD hLE F Ω l n (A.1 v) v (A.2 v) Λ W W'
    (ρ.comp (Dec (F := F) (A.1 v)).subtype) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P hn (hsub ρ hc _) (hsub ρ' hc' _)
    hl hr (fun g x y => hP g.1 x y)
  have hS : ∀ v, v ∈ hfin.toFinset ∪ (hT.toFinset ∪ Q) ↔ v ∈ placesOver F l ∨ v ∈ T ∨ v ∈ Q := by simp
  have hS' : ∀ v, v ∉ hfin.toFinset ∪ (hT.toFinset ∪ Q) ↔ v ∉ placesOver F l ∧ v ∉ T ∧ v ∉ Q := fun v => by
    rw [hS, not_or, not_or]
  have hnl : ∀ v, v ∈ T ∨ v ∈ Q → v ∉ placesOver F l := fun v h => h.elim (hTl v) (hQl v)
  have b1 : ∀ v ∈ placesOver F l, bkCond ρ A l (T ∪ ↑Q) L v = L v := fun v hv => if_pos hv
  have b2 : ∀ v, v ∈ T ∨ v ∈ Q → bkCond ρ A l (T ∪ ↑Q) L v = ⊤ := fun v hv => (if_neg (hnl v hv)).trans (if_pos hv)
  obtain ⟨fC, e⟩ := GlobalTheory.T.greenbergWiles_pair_alt hPT hLF hGF hGE F Ω l n Λ W W' ρ ρ' P hn hc hc' hl hr hP
    (hfin.toFinset ∪ (hT.toFinset ∪ Q)) A (fun v hv => (hS v).2 (.inl hv))
    (fun v hv => hur v ((hS' v).1 hv).1 ((hS' v).1 hv).2.1 ((hS' v).1 hv).2.2) (bkCond ρ A l (T ∪ ↑Q) L)
    (fun v hv => (if_neg ((hS' v).1 hv).1).trans (if_neg (not_or.2 ((hS' v).1 hv).2))) C (fun y => by
      rw [hC]
      constructor
      · rintro ⟨y', ⟨k1, k2, k3⟩, e⟩
        have e' : (y' - y).1 ∈ B1 ρ' := (Submodule.Quotient.eq ((B1 ρ').comap (Z1 ρ').subtype)).1 e.symm
        obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 e'
        have hm' : ∀ g, y.1 g = y'.1 g - (ρ' g m - m) := fun g => by
          rw [← hm g]
          exact (sub_sub_cancel _ _).symm
        refine ⟨fun v hv τ hτ => ?_, fun v hv x hx => ?_⟩
        · obtain ⟨a, b, c⟩ := (hS' v).1 hv
          rw [hm', k1 v a b c τ hτ, (hur v a b c _ (A.2 v) τ hτ).2]
          simp
        · rcases (hS v).1 hv with hv | hv
          · rw [b1 v hv] at hx
            exact cupB_sub_cob _ (ρ.comp (Dec (F := F) (A.1 v)).subtype) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P
              (fun g x y => hP g.1 x y) x.1 _ _ m x.2.1 x.2.2
              ((hsub ρ' hc' _).comp (continuous_id.prodMk continuous_const)) (fun g => hm' g.1) (k3 v hv x hx)
          · obtain ⟨m', hm''⟩ := k2 v hv
            refine ((hloc v).1 (restrictCocycles1 ρ' _ continuous_subtype_val y)).2 ⟨m' - m, fun g => ?_⟩ x
            change y.1 g.1 = ρ' g.1 (m' - m) - (m' - m)
            rw [hm', hm'' g.1 g.2, map_sub]
            abel
      · rintro ⟨k1, k2⟩
        refine ⟨y, ⟨fun v a b c => k1 v ((hS' v).2 ⟨a, b, c⟩), fun v hv => ?_, fun v hv x hx => ?_⟩, rfl⟩
        · obtain ⟨m, hm⟩ := ((hloc v).1 (restrictCocycles1 ρ' _ continuous_subtype_val y)).1 fun x =>
            k2 v ((hS v).2 (.inr hv)) x (by rw [b2 v hv]; trivial)
          exact ⟨m, fun g hg => hm ⟨g, hg⟩⟩
        · exact k2 v ((hS v).2 (.inl hv)) x (by rw [b1 v hv]; exact hx))
  refine ⟨fC, ?_⟩
  have hd : Disjoint hfin.toFinset (hT.toFinset ∪ Q) := Finset.disjoint_right.2 fun v hv h =>
    hnl v (by simpa using hv) (by simpa using h)
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin] at hcount
  have e1 : ∏ v ∈ hfin.toFinset, Nat.card (bkCond ρ A l (T ∪ ↑Q) L v) = ∏ v ∈ hfin.toFinset, Nat.card (L v) :=
    Finset.prod_congr rfl fun v hv => by rw [b1 v (by simpa using hv)]
  have e2 : ∏ v ∈ hT.toFinset ∪ Q, Nat.card (bkCond ρ A l (T ∪ ↑Q) L v) =
      (∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
        ∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ∈ T ∨ v ∈ Q := by simpa using hv
    rw [b2 v hv', Nat.card_congr Submodule.topEquiv.toEquiv]
    exact (hloc v).2 (hnl v hv')
  have e3 : ∏ v ∈ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) =
      ∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) :=
    Finset.prod_subset Finset.subset_union_right fun v hv hv' => by
      have : v ∈ T ∨ v ∈ Q := by simpa using hv
      rw [hT0 v (this.resolve_right hv')]
      exact Nat.card_unique
  have hpos : 0 < (∏ v ∈ hfin.toFinset ∪ (hT.toFinset ∪ Q), Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
      Nat.card W ^ InfinitePlace.nrComplexPlaces F :=
    mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (pow_pos Nat.card_pos _)
  rw [h0, h0', Nat.card_unique (α := (⊥ : Submodule Λ W)), Nat.card_unique (α := (⊥ : Submodule Λ W')), mul_one, mul_one,
    Finset.prod_union hd (f := fun v => Nat.card (bkCond ρ A l (T ∪ ↑Q) L v)), e1, e2, hcount, ← e3, mul_assoc] at e
  refine Nat.eq_of_mul_eq_mul_right hpos (e.trans ?_)
  rw [Finset.prod_union hd]
  ring

end General

theorem orderFormula : PoitouTateTotallyComplex → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q := by
  intro hPT hLF hLD hLE hGF hGE h4 D N X bkP i s A _ _ _ _ κ Q ρ hS hK hD hNI Y Y' _ _ _ _ _ _ _ _ _ _ β hβ
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := hS.2.1
  have hcx : InfinitePlace.nrComplexPlaces D.host.E = D.R.f := by
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
      rw [D.host.finrank_cmField]
      unfold Ranks.f Ranks.n
      ring
    omega
  obtain ⟨hc, hc', hP, hU⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y Y' β hβ.1
  have hcount := GlobalTheory.T.localConditionOrder_aboveL_finiteModules D N X bkP i s A κ Q hS hK
    (GlobalTheory.LocalSaturation.main hLF hLD hLE h4 D N X bkP i s A κ Q hS)
    (GlobalTheory.LocalConditionCount.locCount hLF hLD hLE h4 D N X bkP i s A κ Q hS) Y
  have hko : IsOpen ((κ⁻¹).ker : Set (GE N)) := by
    convert hS.2.2.2.1 using 2
    ext g
    simp
  refine order_formula (X.l i) (nu X i + 1) hPT hLF hLD hLE hGF hGE (repOn (Tgl i s) κ Y) (repOn ρ κ⁻¹ Y') (vecPair D.R.r β)
    (show 0 < nu X i + 1 by omega) hc hc' (fun x hx => funext fun c => hβ.2.1 _ fun y' => ?_) (fun y hy => funext fun c => hβ.2.2 _ fun x => ?_) hP
    N.plOm (Spl i) (GlobalTheory.SelObstruction.finite_Spl i) Q (fun v hv => hv.2) hS.2.2.2.2.2.2.1 hU
    (bkOn bkP i (Tgl i s) κ Y) (DualCl bkP i s κ ρ β Q) (fun c => Iff.rfl)
    (GlobalTheory.NoGlobalInv.noInv D N X bkP i s A κ Q hS Y (tors_all A Y)) (eq_bot_iff.2 fun m hm => hNI Y' m hm)
    (fun v hv => (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hS.1 v hv A κ⁻¹ hko (fun g => ?_) Y'
      (tors_all A Y') ρ (.inr hD)).1) ?_
  · have := hx (Pi.single c y')
    rw [vecPair_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  · have := hy (Pi.single c x)
    rw [vecPair_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  · obtain ⟨n, hn⟩ := hS.2.2.2.2.1 g
    exact ⟨n, by rw [MonoidHom.inv_apply, inv_pow, hn, inv_one]⟩
  · rw [hcount, hcx, Nat.card_pi, Finset.prod_const, Finset.card_fin, ← pow_mul, mul_comm D.R.r]

end GlobalTheory.SelOrder
