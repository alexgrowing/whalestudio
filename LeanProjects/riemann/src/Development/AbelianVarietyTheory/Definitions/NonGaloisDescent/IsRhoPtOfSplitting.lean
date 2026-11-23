import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.LocalRingCardinality.DataNChTie
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockComplementLattice
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistedTriples
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceCoefficientRing

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.PtCore

section Enl

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (L' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ L'.1)

def inc : Br.LL D.nbr i w hw →+* ↥L'.1 := (IntermediateField.inclusion h).toRingHom

def locE {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥L'.1 :=
  mapM (inc D i w hw L' h) (Br.loc D.nbr i w hw M)

def chiE (χ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O i)ˣ) : Br.G D.nbr i w hw →* (↥L'.1)ˣ :=
  (Units.map (inc D i w hw L' h).toMonoidHom).comp (Br.locChi D.nbr i w hw χ)

theorem locE_apply {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : locE D i w hw L' h M g a b = inc D i w hw L' h (Br.loc D.nbr i w hw M g a b) := rfl

theorem chiE_apply (χ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    ((chiE D i w hw L' h χ g : (↥L'.1)ˣ) : ↥L'.1) =
      inc D i w hw L' h ((Br.locChi D.nbr i w hw χ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := rfl

include h in

theorem nonempty_embE : Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥L'.1) :=
  ⟨((D.nbr i w hw).Kw.1.val).codRestrict L'.1.toSubalgebra
    fun x => h ((D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x)⟩

example {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    locE D i w hw (D.nbr i w hw).LL le_rfl M = Br.loc D.nbr i w hw M := rfl

end Enl

variable (D : D7)

def BlockE (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (L' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ L'.1)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥L'.1),
    (∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' h (rTwO D.nd i r π))) τ a =
      multV (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' h (WpO D.nd i ρ π))) τ a +
        (if 0 ≤ a ∧ a < D.R.t then 1 else 0)) ∧
    ∀ c ∈ Finset.Icc 1 D.R.t, ∀ a : ℤ,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' h (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0

def ChiOneE (i : D.nd.Loc) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (L' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ L'.1),
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (chiE D i w hw L' h (D.nd.chi i 1))⁻¹)

def RhoFrob (i : D.nd.Loc) (π : D.nd.X i) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
  IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) ∧
  ∀ w, SplitOut D.nd i w → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.MainNotions.N.GE D.nd),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (Polynomial.X - Polynomial.C ((D.nd.chi i c σ : (D.nd.O i)ˣ) : D.nd.O i)) =
      heckePol D.nd i π w

def EpsAll (i : D.nd.Loc) : Prop :=
  ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ z : ℤ_[D.nd.l i], ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * z

theorem EpsAll.exists_generator {D : D7} {i : D.nd.Loc} (h : EpsAll D i) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i := by
  simpa using h w hw 1

def psiG (C : NChoice D) (w : D.what₂.places.Pl) : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok (C.twI w) (C.k' w))ˣ :=
  (C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))

def TameCyc (C : NChoice D) : Prop :=
  ∀ i : D.nd.Loc, ∀ v ∈ D.nd.Q i, ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ m : ℤ, psiG D C (D.nd.w i) σ = (psiG D C (D.nd.w i) (D.nd.gam0 i v)) ^ m

def AttachedIn (a : D.nd.Loc) (π : D.nd.X a) (j : D.ntw.Tw) (s : D.ntw.Sig j) : Prop :=
  ∃ h : D.ntw.twOf a = j, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.Attached D a π (cast (congrArg D.ntw.Sig h.symm) s)

theorem attachedIn_self (a : D.nd.Loc) (π : D.nd.X a) (s : D.ntw.Sig (D.ntw.twOf a)) :
    AttachedIn D a π _ s ↔ GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.Attached D a π s :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩

theorem AttachedIn.jS_side {D : D7} {a : D.nd.Loc} {π : D.nd.X a} {j : D.ntw.Tw} {s : D.ntw.Sig j}
    (h : AttachedIn D a π j s) : D.ntw.jS j s = D.nd.j a ∧ D.ntw.side j s = D.ntw.twSide a := by
  obtain ⟨rfl, _, _, -, -, -, ht⟩ := h
  exact ⟨ht.1, ht.2.1⟩

def SelCore (C : NChoice D) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) : Prop :=
  ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, ∃ s : D.ntw.Sig (C.twI (D.nd.w i)),
    BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s ∧ D.ntw.side _ s = C.sd (D.nd.w i) ∧
    (BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i)) (psiG D C (D.nd.w i)) ≠ ⊤ →
      Br.sFin D.loc D.nbr i (ρ i) π) ∧
    ENNReal.ofReal (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤
      BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i)) (psiG D C (D.nd.w i)) ∧
    AttachedIn D i π (C.twI (D.nd.w i)) s

theorem SelCore.bound {D : D7} {C : NChoice D}
    {ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} (h : SelCore D C ρ)
    (i : D.nd.Loc) (b : ℝ) (hb : 0 ≤ b)
    (hs : ∀ s : D.ntw.Sig (C.twI (D.nd.w i)), BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s →
      D.ntw.jS _ s = D.nd.j i → D.ntw.side _ s = C.sd (D.nd.w i) →
      BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i)) (psiG D C (D.nd.w i)) ≤
        ENNReal.ofReal b) :
    ∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i (ρ i) π ∧ (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤ b := by
  intro π hπ
  obtain ⟨s, h1, h2, h3, h4, h6⟩ := h i π hπ
  have h5 := hs s h1 h6.jS_side.1 h2
  exact ⟨h3 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h5), (ENNReal.ofReal_le_ofReal_iff hb).1 (h4.trans h5)⟩

def TriplesGood : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.GoodRowOf D (D.nd.j a) σ →
    HasParamW D.nd D.naut a σ Sg →
      ∃ s, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg ∧ BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) (D.ntw.twOf a) s

def GoodPtRow : Prop :=
  ∀ (a : D.nd.Loc), ∀ π ∈ D.nd.Zgood a, ∃ (σ : D.what₂.FT) (Sg : List (Part D.naut.CG)),
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.GoodRowOf D (D.nd.j a) σ ∧ HasParamW D.nd D.naut a σ Sg ∧ HasParamX D.nd D.naut a π Sg

theorem GoodPtRow.exists_attached {D : D7} (hG : GoodPtRow D) (hT : TriplesGood D) (a : D.nd.Loc)
    (π : D.nd.X a) (hπ : π ∈ D.nd.Zgood a) :
    ∃ s, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.Attached D a π s ∧ BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) (D.ntw.twOf a) s := by
  obtain ⟨σ, Sg, h1, h2, h3⟩ := hG a π hπ
  obtain ⟨s, h4, h5⟩ := hT a σ Sg h1 h2
  exact ⟨s, ⟨σ, Sg, h1, h2, h3, h4⟩, h5⟩

def ResAbsIrr : Prop :=
  ∀ (a : D.nd.Loc), ∀ π ∈ D.nd.Zgood a, ∀ ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a),
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → AbsIrrSub (redRep D.nd a ρ) ⊤

def SameTwistAt (a : D.nd.Loc) (j : D.ntw.Tw) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok j k)ˣ) : Prop :=
  ∃ h : D.ntw.twOf a = j, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar (D.ntw.twist₂ a) (BlochKatoReduction.Gen.phiK D.ntw (D.ntw.twOf a) k)
    (D.ntw.psiL a) (cast (congrArg (fun j => Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok j k)ˣ) h.symm) ψ)

theorem sameTwistAt_iff (a : D.nd.Loc) (j : D.ntw.Tw) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok j k)ˣ) :
    SameTwistAt D a j k ψ ↔ D.ntw.twOf a = j ∧ ∃ f : D.ntw.O0 j →+* D.nd.O a, HEq f (D.ntw.twist₂ a) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f (BlochKatoReduction.Gen.phiK D.ntw j k) (D.ntw.psiL a) ψ := by
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, _, HEq.rfl, h⟩
  · rintro ⟨rfl, f, hf, h⟩
    obtain rfl := eq_of_heq hf
    exact ⟨rfl, h⟩

def SameTwist (C : NChoice D) : Prop :=
  ∀ a : D.nd.Loc, SameTwistAt D a (C.twI (D.nd.w a)) (C.k' (D.nd.w a)) (psiG D C (D.nd.w a))

theorem SameTwist.twOf_eq {D : D7} {C : NChoice D} (h : SameTwist D C) (a : D.nd.Loc) :
    D.ntw.twOf a = C.twI (D.nd.w a) := (h a).1

theorem SameTwist.exists_heq {D : D7} {C : NChoice D} (h : SameTwist D C) (a : D.nd.Loc) :
    ∃ f : D.ntw.O0 (C.twI (D.nd.w a)) →+* D.nd.O a, HEq f (D.ntw.twist₂ a) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f (BlochKatoReduction.Gen.phiK D.ntw (C.twI (D.nd.w a)) (C.k' (D.nd.w a))) (D.ntw.psiL a)
        (psiG D C (D.nd.w a)) :=
  ((sameTwistAt_iff D a _ _ _).1 (h a)).2

section Splitting

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.BlockJumps

theorem isRhoPt_of_splitting (i : D.nd.Loc) (π : D.nd.X i)
    (r : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (hr : IsHeckeGalois D.nd i π r) (h : BlockRepresentationsSemisimple.IsComplement D.nd i r ρ) : LatticeConditions.IsRhoPt D i π ρ := by
  obtain ⟨e, he⟩ := h.rho
  exact ⟨h.cont, r, hr, e, fun g u => he g u⟩

theorem RhoFrob.of_splitting (i : D.nd.Loc) (π : D.nd.X i)
    (r : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (hr : IsHeckeGalois D.nd i π r) (h : BlockRepresentationsSemisimple.IsComplement D.nd i r ρ) : RhoFrob D i π ρ := by
  refine ⟨h.cont, ?_, (RepresentationOverSumChar.isRhoAt_iff D.nd i π ρ).1
    (GlobalTheory.ComplementCompare.second_of_first D.nd i π r ρ hr h).1⟩
  intro W hW
  let P : Subrepresentation (BlockRepresentationsSemisimple.blockRep ρ (D.nd.chi i) D.R.t) :=
    ⟨W.prod ⊥, fun g v hv => by
      rw [BlockRepresentationsSemisimple.blockRep_apply]
      refine ⟨hW g _ hv.1, ?_⟩
      have h2 : v.2 = 0 := hv.2
      change _ = 0
      funext c
      simp [h2]⟩
  obtain ⟨Q, hQ⟩ := h.ss.exists_isCompl P
  have hQ' := (GlobalTheory.ComplementCompare.isCompl_sub_iff P Q).1 hQ
  refine ⟨Q.toSubmodule.comap (LinearMap.inl _ _ _), fun g v hv => ?_, ?_, ?_⟩
  · have := Q.apply_mem_toSubmodule g hv
    rw [BlockRepresentationsSemisimple.blockRep_apply] at this
    change (_, (0 : Fin D.R.t → _)) ∈ Q.toSubmodule
    convert this using 2
    · rfl
    · funext c
      simp
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have := (Submodule.disjoint_def.1 hQ'.disjoint) (x, 0) ⟨hx, rfl⟩ hx'
    exact congrArg Prod.fst this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : ((x, 0) : _ × (Fin D.R.t → FractionRing (D.nd.O i))) ∈ P.toSubmodule ⊔ Q.toSubmodule := by
      rw [hQ'.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hx
    have hp2 : p.2 = 0 := hp.2
    have hq2 : q.2 = 0 := by
      have := congrArg Prod.snd hpq
      simpa [hp2] using this
    refine Submodule.mem_sup.2 ⟨p.1, hp.1, q.1, ?_, congrArg Prod.fst hpq⟩
    change (q.1, (0 : Fin D.R.t → _)) ∈ Q.toSubmodule
    rw [← hq2]
    exact hq

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem multV_cycPow_line [Algebra.IsSeparable Qp K] [FiniteDimensional Qp LL] (hF : IsField BdR)
    (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1) (σ : Representation LL G (Fin 1 → LL)) (e : ℕ)
    (h : ∀ g u, σ g u 0 = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e * u 0) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD σ τ a = if a = e then 1 else 0 := by
  let χ : G →* LLˣ := ((Units.map (algebraMap Qp LL).toMonoidHom).comp PD.χ)⁻¹ ^ e
  have hχ : ∀ g, ((χ g : LLˣ) : LL) = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e := fun g => by
    simp [χ]
  have : σ = diagRep fun _ : Fin 1 => χ := by
    ext1 g
    refine LinearMap.ext fun u => funext fun c => ?_
    rw [Subsingleton.elim c 0, h, diagRep_apply, hχ]
  rw [this, multV_diagRep PD hF, Fin.sum_univ_one]
  exact multV_twist PD hs (Formalism.WeaklyAdmissibleFiltrations.charRep χ) e (fun g x => by rw [← hχ]; rfl) τ a

end Periods

set_option maxHeartbeats 1600000 in

theorem BlockE.of_splitting (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hc : BlockRepresentationsSemisimple.IsComplement D.nd i (r π) (ρ π)) : BlockE D i r ρ π := by
  obtain ⟨e, he⟩ : BlockJumpCount.IsBlockSum D.nd i r ρ π := by
    obtain ⟨e, he⟩ := hc.rho
    exact ⟨e, fun g u => he g u⟩
  intro w hw L' h τ
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI := L'.2
  let s : Br.G D.nbr i w hw → Formalism.MainNotions.N.GE D.nd := fun g => decS D.nd w (Br.iota D.nbr i w hw g)
  let f := (inc D i w hw L' h).comp (Br.toLLK (D.nbr i w hw))
  have hf : ∀ c, f (toK D.nd i c) = inc D i w hw L' h ((D.nbr i w hw).toLL c) := fun c =>
    congrArg (inc D i w hw L' h) (Br.toLLK_alg (D.nbr i w hw) c)
  have hχ : ∀ (c : ℕ), c < D.R.t → ∀ g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i (c + 1) g =
      (epsU D.nd i g)⁻¹ ^ c := fun c hc g => by
    have h := D.nd.chi_def i (c + 1) (by omega) hc
    change (D.nd.chi i 1)⁻¹ g * D.nd.chi i (c + 1) g = _
    rw [h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl
  obtain ⟨e', he'⟩ := split_map f (fun g => mapM (toK D.nd i) (rTwO D.nd i r π) (s g))
    (fun g => mapM (toK D.nd i) (WpO D.nd i ρ π) (s g))
    (fun g c => toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ (c : ℕ) : (D.nd.O i)ˣ) : D.nd.O i)) e (fun g u => by
      have h1 : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) v,
          (mapM (toK D.nd i) (twistM M (chiU D.nd i 1)⁻¹) (s g)).mulVec v =
            toK D.nd i (((chiU D.nd i 1)⁻¹ (s g) : (D.nd.O i)ˣ) : D.nd.O i) •
              (mapM (toK D.nd i) M (s g)).mulVec v := fun M v => by
        rw [← Matrix.smul_mulVec]
        congr 1
        ext a b
        exact map_mul (toK D.nd i) _ _
      rw [rTwO, WpO, h1, h1, map_smul, he]
      refine Prod.ext rfl (funext fun c => ?_)
      simp only [← hχ _ c.2, Units.val_mul, map_mul, mul_assoc]
      rfl)
  have hε : ∀ g, inc D i w hw L' h ((D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i)) =
      algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
    intro g
    have h0 : (D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i) =
        algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
      rw [Br.PD, (D.loc _).PD_χ, ← cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
      exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)
    rw [h0]
    exact (IntermediateField.inclusion h).commutes _
  have hM : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) g v,
      matRep (locE D i w hw L' h M) g v = ((mapM (toK D.nd i) M (s g)).map f).mulVec v := fun M g v => by
    rw [show (mapM (toK D.nd i) M (s g)).map f = locE D i w hw L' h M g from
      Matrix.ext fun a b => hf _]
    rfl
  have hs : ∃ x ∈ (Br.PD D.loc D.nbr i w hw).Fil (-1),
      (Br.PD D.loc D.nbr i w hw).ι (Br.PD D.loc D.nbr i w hw).t * x = 1 := by
    obtain ⟨x, hx, hx1⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one (D.locT (D.nd.l i))
    refine ⟨x, ?_, by rw [Br.PD, (D.loc _).PD_ι, (D.loc _).period_datum_t_eq, hx1]⟩
    exact ((D.locT _).fil _ _ _).2 (((D.locT _).fil _ _ _).1 hx)
  have hF := GlobalTheory.SmallJumpExample.isField_bdR D (D.nd.l i)
  refine ⟨fun a => ?_, fun c hc a => ?_⟩
  · obtain ⟨J, h1, h2⟩ := jumps_of_split (Br.PD D.loc D.nbr i w hw) hF hs
      (matRep (locE D i w hw L' h (rTwO D.nd i r π))) (matRep (locE D i w hw L' h (WpO D.nd i ρ π))) e'
      (fun g u => by
        rw [hM, hM, he']
        refine Prod.ext rfl (funext fun c => ?_)
        refine congrArg (· * (e' u).2 c) ?_
        rw [hf, Units.val_pow_eq_pow_val, map_pow, map_pow, map_units_inv, map_inv₀, hε]) τ
    rw [h1.2, h2.2, Multiset.count_add, BlockJumpCount.count_blockJumps]
    push_cast
    rfl
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by have := (Finset.mem_Icc.1 hc).1; omega⟩
    have hc' : c < D.R.t := (Finset.mem_Icc.1 hc).2
    rw [multV_cycPow_line (Br.PD D.loc D.nbr i w hw) hF hs _ c (fun g u => by
      rw [hM]
      have h1 : ((mapM (toK D.nd i) (chiRatO D.nd i (c + 1)) (s g)).map f) 0 0 =
          f (toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ c : (D.nd.O i)ˣ) : D.nd.O i)) := by
        rw [← hχ c hc', mul_comm]
        change f (toK D.nd i (_ * (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) 0 0)) = _
        rw [Matrix.one_apply_eq, mul_one]
        rfl
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, h1, hf, Units.val_pow_eq_pow_val, map_pow, map_pow,
        map_units_inv, map_inv₀, hε]) τ a]
    push_cast
    rw [add_sub_cancel_right]

end Splitting

structure PtFam (r : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) : Prop where

  good : ∀ i, GoodR D.nd i (r i)

  cont : ∀ i π, Continuous
    (fun g => ((ρ i π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))

  compl : ∀ i, ∀ π ∈ D.nd.Z i, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r i π) (ρ i π)

namespace PtFam

variable {D} {r : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}

theorem frob (h : PtFam D r ρ) : ∀ i, ∀ π ∈ D.nd.Z i, RhoFrob D i π (ρ i π) :=
  fun i π hπ => RhoFrob.of_splitting D i π _ _ (h.good i π) (h.compl i π hπ)

theorem pt (h : PtFam D r ρ) : ∀ i, ∀ π ∈ D.nd.Z i, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (ρ i π) :=
  fun i π hπ => isRhoPt_of_splitting D i π _ _ (h.good i π) (h.compl i π hπ)

theorem block (h : PtFam D r ρ) : ∀ i, ∀ π ∈ D.nd.Z i, BlockE D i (r i) (ρ i) π :=
  fun i π hπ => BlockE.of_splitting D i _ _ π (h.compl i π hπ)

theorem exists_extend (hC : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (hr : ∀ i, GoodR D.nd i (r i)) :
    ∃ ρ, PtFam D r ρ := by
  classical
  refine ⟨fun i π => if hπ : π ∈ D.nd.Z i then (hC i π hπ (r i π) (hr i π)).choose else 1,
    hr, fun i π => ?_, fun i π hπ => ?_⟩
  · by_cases hπ : π ∈ D.nd.Z i
    · simp only [dif_pos hπ]
      exact (hC i π hπ (r i π) (hr i π)).choose_spec.cont
    · simp only [dif_neg hπ]
      exact continuous_const
  · simp only [dif_pos hπ]
    exact (hC i π hπ (r i π) (hr i π)).choose_spec

theorem exists_pair (hC : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (hr : ∀ i, ∃ r, GoodR D.nd i r) :
    ∃ r ρ, PtFam D r ρ := by
  choose r hr using hr
  exact ⟨r, exists_extend hC hr⟩

example (h : PtFam D r ρ) (ht : 0 < D.R.t) (i : D.nd.Loc) (π : D.nd.X i) (hπ : π ∈ D.nd.Z i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (L' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ L'.1) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥L'.1) :
    multV (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL (rTwO D.nd i (r i) π))) τ 0 =
      multV (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL (WpO D.nd i (ρ i) π))) τ 0 + 1 ∧
    multV (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL (rTwO D.nd i (r i) π))) τ (-1) =
      multV (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL (WpO D.nd i (ρ i) π))) τ (-1) := by
  have h0 := (h.block i π hπ w hw L' hL τ).1
  refine ⟨?_, ?_⟩
  · rw [h0 0, if_pos ⟨le_rfl, by exact_mod_cast ht⟩]
  · rw [h0 (-1), if_neg (by omega), add_zero]

end PtFam

end GlobalTheory.PtCore

end
