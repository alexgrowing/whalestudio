import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeParametersInertPlaceIndependentOfModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordinateModelOfAlgWeightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicRepCmQuotientModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicMultiplicityEqOfIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentConjSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSphericalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SphericalVectorFixedLocalStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem autIso_symm {π π' : NG.AutRep L n} (h : π.Iso π') : π'.Iso π := NG.AutRep.iso_equivalence.symm h

theorem autIso_trans {π π' π'' : NG.AutRep L n} (h : π.Iso π') (h' : π'.Iso π'') : π.Iso π'' :=
  NG.AutRep.iso_equivalence.trans h h'

theorem clsA_eq_iff (π π' : NG.AutRep L n) : clsA π = clsA π' ↔ π.Iso π' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := GlobalTheory.T.automorphic_rep_cm_quotient_model L n π'
    have h2 : m ∈ (clsA π).1 := by rw [h]; exact hm
    exact autIso_trans h2 (autIso_symm hm)
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => autIso_trans (autIso_symm h) h', fun h' => autIso_trans h h'⟩

theorem clsW_eq_iff (a b : NG.AlgWt L n) : clsW a = clsW b ↔ a.Iso b := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_coordinate_model_of_algWeight L n b
    have h2 : m ∈ (clsW a).1 := by rw [h]; exact hm
    exact h2.trans hm.symm
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem rep_iso (π : NG.AutRep L n) : (clsA π).rep.Iso π :=
  (clsA_eq_iff _ _).1 (AUq.cls_rep (clsA π))

theorem repW_iso (a : NG.AlgWt L n) : (clsW a).rep.Iso a :=
  (clsW_eq_iff _ _).1 (WtQ.cls_rep (clsW a))

theorem sphAt_iso {π π' : NG.AutRep L n} (h : π.Iso π') {v} (hs : π.SphAt v) : π'.SphAt v := by
  obtain ⟨-, T, hT⟩ := h
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  refine ⟨(T ⟨f, hf⟩ : _), (T ⟨f, hf⟩).2, ?_, fun κ hκ ht => ?_⟩
  · intro h0
    apply hf0
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val (T.injective (this.trans T.map_zero.symm))
    exact this
  · have := hT κ ⟨f, hf⟩ ⟨f, hf⟩ (hfix κ hκ ht).symm
    exact this.symm

theorem overPl_unique {w : HeightOneSpectrum (𝓞 L)} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (h : NG.OverPl w v) (h' : NG.OverPl w v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem locAt_of_split (π : NG.AutRep L n) (s : SplitPlace L) : ∃ x, LocAt π s.w x := by
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  exact ⟨_, s, σ, rfl, hσ, HEq.rfl⟩

theorem locAt_unique {π π' : NG.AutRep L n} (hi : π.Iso π') {w : HeightOneSpectrum (𝓞 L)} {x x'}
    (hx : LocAt π w x) (hx' : LocAt π' w x') : x = x' := by
  obtain ⟨s, σ, hs, hσ, e⟩ := hx
  obtain ⟨s', σ', hs', hσ', e'⟩ := hx'
  obtain ⟨σ₀, -, hu⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  have h1 := hu π s rfl σ (NG.AutRep.iso_equivalence.refl π) hσ
  have h2 := hu π' s' (hs'.trans hs.symm) σ' hi hσ'
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 L)) (_ : u = u') (a : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u.adicCompletion L)))
      (b : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u'.adicCompletion L))), HEq a b →
      HEq (⟨n, a⟩ : GlobalTheory.LocGL.IrrGL (u.adicCompletion L)) (⟨n, b⟩ : GlobalTheory.LocGL.IrrGL (u'.adicCompletion L)) := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    rfl
  have h3 : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls σ') :=
    key _ _ (hs.trans hs'.symm) _ _ (h1.trans h2.symm)
  exact eq_of_heq (e.symm.trans (h3.trans e'))

end

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

theorem locOf_eq {π : NG.AutRep D.host.E D.R.nV} {w : PlE D.host} {x} (hx : LocAt π w x) :
    locOf hL D T (clsA π).rep w = (T.e w).symm (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) x) := by
  have hex : ∃ x, LocAt (clsA π).rep w x := by
    obtain ⟨s, σ, hs, -, -⟩ := hx
    subst hs
    exact locAt_of_split _ s
  unfold locOf
  rw [dif_pos hex, locAt_unique (rep_iso π) hex.choose_spec hx]

end

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

theorem f_sph (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : NG.OverPl w v) : (∃ v', NG.OverPl w v' ∧ (clsA π).rep.SphAt v') ↔ π.SphAt v := by
  constructor
  · rintro ⟨v', hv', hs⟩
    rw [overPl_unique hv hv']
    exact sphAt_iso (rep_iso π) hs
  · intro hs
    exact ⟨v, hv, sphAt_iso (autIso_symm (rep_iso π)) hs⟩

theorem f_sat (π : NG.AutRep D.host.E D.R.nV) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (w : PlE D.host)
    (hv : NG.OverPl w v) (Dv : InertDatum D.host.E D.R.nV v w) (hα : ∃ α, NG.SatAt π Dv α) :
    ∃ α, NG.SatAt π Dv α ∧ satOf (clsA π).rep w = Finset.univ.val.map α := by
  obtain ⟨α, hα⟩ := hα
  have hex : ∃ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' ∧ NG.SatAt (clsA π).rep Dv' α' :=
    ⟨v, Dv, α, hv, GlobalTheory.T.satakeParameters_inertPlace_independent_of_model _ _ π _ (autIso_symm (rep_iso π)) v w hv Dv Dv α hα⟩
  unfold satOf
  rw [dif_pos hex]
  have key : ∀ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' → NG.SatAt (clsA π).rep Dv' α' → NG.SatAt π Dv α' := by
    intro v' Dv' α' hv' hs'
    have e := overPl_unique hv hv'
    subst e
    exact GlobalTheory.T.satakeParameters_inertPlace_independent_of_model _ _ _ π (rep_iso π) v w hv _ Dv _ hs'
  obtain ⟨hv', hs'⟩ := hex.choose_spec.choose_spec.choose_spec
  exact ⟨_, key _ _ _ hv' hs', rfl⟩

theorem f_wt (π : NG.AutRep D.host.E D.R.nV) (a : NG.AlgWt D.host.E D.R.nV) (hd : π.toAlgWt.IsDual a) :
    wtOf D (clsA π).rep = clsW a := by
  have hπ : (clsA π).rep.toAlgWt.Iso π.toAlgWt := (rep_iso π).1
  obtain ⟨b, hb, hbu, hba⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ π.toAlgWt
  have hrb : (clsA π).rep.toAlgWt.IsDual b := (hba _ hπ.symm).1
  have hex : ∃ b, (clsA π).rep.toAlgWt.IsDual b := ⟨b, hrb⟩
  unfold wtOf
  rw [dif_pos hex]
  obtain ⟨b', -, hbu', -⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ (clsA π).rep.toAlgWt
  have h1 : b'.Iso hex.choose := (hbu' _).1 hex.choose_spec
  have h2 : b'.Iso b := (hbu' _).1 hrb
  have h3 : b.Iso a := (hbu a).1 hd
  exact (clsW_eq_iff _ _).2 ((h1.symm.trans h2).trans h3)

theorem f_infW (a : NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ) (hl : a.HWAt τ lam) :
    NG.infOf (hwOf (clsW a).rep τ) = NG.infOf lam := by
  have hi : a.Iso (clsW a).rep := (repW_iso a).symm
  obtain ⟨b0, hb0, hb0', hhw⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ a
  have hr : (clsW a).rep.HWAt τ lam := ((hhw _ hi).2 τ lam hl)
  obtain ⟨huniq, hanti⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ (clsW a).rep τ
  have hex : ∃ lam, (clsW a).rep.HWAt τ lam ∧ Antitone lam := ⟨lam, hr, hanti lam hr⟩
  unfold hwOf
  rw [dif_pos hex, huniq.unique hex.choose_spec.1 hr]

theorem f_locUnr (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (hs : π.SphAt s.v) :
    D.naut.unr (locOf hL D T (clsA π).rep s.w) := by
  obtain ⟨x, hx⟩ := locAt_of_split π s
  rw [locOf_eq hL D T hx, T.unr, Equiv.apply_symm_apply]
  exact GlobalTheory.T.local_reciprocity_unramified_spherical hL D π s x hx hs

theorem f_locPol (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ)
    (J : Subgroup (GAf D.host.E D.R.nV)) (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV))
    (f : GAf D.host.E D.R.nV → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) (c : ℕ → ℂ)
    (hc' : ∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) :
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (locOf hL D T (clsA π).rep w) ((1 - (D.R.nV : ℝ)) / 2)) := by
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_localComponent_conj_splitPlace D π s w hc
  obtain ⟨hun, hpol⟩ := GlobalTheory.T.spherical_vector_fixed_local hL D π s w ϖ hc hu J hJ f hf hf0 hfix c hc' x hx
  rw [locOf_eq hL D T hx]
  have hu2 : D.naut.unr (D.naut.lpTw ((T.e w).symm (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) x))
      ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [T.unr, T.tw, Equiv.apply_symm_apply]; exact hun
  unfold galPol
  rw [T.frobEig _ _ hu2, T.tw, Equiv.apply_symm_apply]
  exact hpol

theorem f_true (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E))) (hσ : IsLocS π.S s σ) :
    T.e s.w (locOf hL D T (clsA π).rep s.w) =
      GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls σ) := by
  rw [locOf_eq hL D T ⟨s, σ, rfl, hσ, HEq.rfl⟩, Equiv.apply_symm_apply]

set_option maxHeartbeats 1000000 in

theorem exists_auSide (hE : IsEmpty D.nd.Loc) :
    ∃ (C : NBC D.naut) (A : AUSide (setBC D C)), AUTrue hL (setBC D C) T A :=
  ⟨nbcOf hL D T hE,
    { cls := fun _ _ _ π => clsA π
      surj := fun _ _ _ X => ⟨X.rep, AUq.cls_rep X⟩
      iso := fun _ _ _ π π' => clsA_eq_iff π π'
      mult := fun _ _ _ π => GlobalTheory.T.automorphic_multiplicity_eq_of_iso _ _ _ _ (rep_iso π)
      sph := fun _ _ _ π w v _ hv => f_sph D π w v hv
      sat := fun _ _ _ π v w hv Dv hα => f_sat D π v w hv Dv hα
      clsWt := fun _ _ _ a => clsW a
      surjWt := fun _ _ _ Y => ⟨Y.rep, WtQ.cls_rep Y⟩
      isoWt := fun _ _ _ a b => clsW_eq_iff a b
      wt := fun _ _ _ π a hd => f_wt D π a hd
      infW := fun _ _ _ a τ lam hl => f_infW D a τ lam hl
      locUnr := fun _ _ _ π s hs => f_locUnr hL D T π s hs
      locPol := fun _ _ _ π s w ϖ hc hu J hJ f hf hf0 hfix c hc' => f_locPol hL D T π s w ϖ hc hu J hJ f hf hf0 hfix c hc' },
    fun _ _ _ π s σ hσ => f_true hL D T π s σ hσ⟩

end

end GlobalTheory.AutQuot

open Formalism.BasicNotions GlobalTheory.HeightCounting in

theorem GlobalTheory.AutQuot.exists_nbc_auSide : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), IsEmpty D.nd.Loc →
    ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : AUSide (setBC D C)), AUTrue hL (setBC D C) T A :=
  fun hL D hE T => GlobalTheory.AutQuot.exists_auSide hL D T hE
