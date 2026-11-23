import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Triple
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenExport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly

noncomputable section

section
section
namespace GlobalTheory.Triple
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
variable {D : D7}
section API

theorem isGaloisRepOfN_of_conj {a : ℕ} {π : D.naut.CG a} {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {r r' : GalE D →* GL (Fin a) (Qbar l)} (h : UpperTheory.GalS.IsGaloisRepOfN D π l ι r) (A : GL (Fin a) (Qbar l))
    (hA : ∀ g, r' g = A * r g * A⁻¹) : UpperTheory.GalS.IsGaloisRepOfN D π l ι r' := by
  have hc : ∀ g, ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := fun g => by
    rw [hA, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  refine ⟨?_, GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_conj A hA h.2.1, fun w hw => ⟨fun k s hs => ?_, ?_, fun hu B s hB hs => ?_⟩⟩
  · simp only [hA, Units.val_mul]
    exact (continuous_const.mul h.1).mul continuous_const
  · rw [hc]; exact (h.2.2 w hw).1 k s hs
  · intro hm
    rw [show (r' : GalE D → _) = (MulAut.conj A) ∘ r from funext hA, Set.image_comp]
    exact ((h.2.2 w hw).2.1 hm).image _
  · rw [hc]; exact (h.2.2 w hw).2.2 hu B s hB hs

end API
end GlobalTheory.Triple
end
end

section
section
namespace GlobalTheory.Triple
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
variable {D : D7}
section API
variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool} {ρ : Reading X i b} {s : X.Sig i} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ} {w : D.what₂.places.Pl}
  {red : Zbar (X.l i) →+* FbAt D w}

theorem IsTripleWith.charpoly_frob_of_isTriple (ha : IsGlobalArtin art) (h : IsTripleWith C art ρ s σ π r ν w red) {P : PlE D.host}
    (hl : P ∉ placesOver D.host.E (X.l i)) (hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k))
    {B : ValuationSubring D.nd.Om} (hB : IsPlaceOver B P) {g : GalE D} (hF : IsFrob (F := D.host.E) B (normV P) g) :
    ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).charpoly.map ρ.toC =
      ((D.naut.frobEig (D.naut.locG π P)).map fun a => Polynomial.X - Polynomial.C
        (a * ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) * (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹)).prod := by
  have hu := h.param.unr P hg
  obtain ⟨n, hn⟩ := h.shift
  have e1 := ((UpperTheory.GalS.galW h.gal).2.2 P hl).2.2 hu B g hB hF
  have e2 := hn.frob ha (Or.inl hl) (shiftChar_unr C P) hB hF
  rw [galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  have e3 : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map ρ.toC =
      (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹ •
        ((r g : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))).map ρ.ι.toRingHom := by
    ext x y
    have := congrArg ρ.ι (congrFun (congrFun (h.rho g) x) y)
    simpa [e2, Reading.toC_apply] using this
  rw [← Matrix.charpoly_map, e3, charpoly_smul_of_prod _ _ _ e1, Multiset.map_map]
  rfl

end API
end GlobalTheory.Triple
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section
namespace GlobalTheory.TripInhab
open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)
variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

theorem isRepOf_twGL_of_isGal (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (hCS : CharSide D C) {i : D.ntw.Tw} {b : Bool}
    (ρ : Reading D.ntw i b) {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))}
    (hr : UpperTheory.GalS.IsGaloisRepOfN D π (D.ntw.l i) ρ.ι r) {ν : GalE D →* (D.ntw.O0 i)ˣ} {n : _}
    (hν : IsGal art ρ.κ ρ.ι (shiftChar C) n ν) :
    IsRepOf D (D.ntw.l i) ρ.ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) (twGL (inQ ρ.κ ν) r) := by
  refine ⟨(Units.continuous_val.comp (hν.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg)).smul hr.1,
    isSSRep_twGL _ _ hr.2.1, ?_⟩
  have hfin := Formalism.L2.NR.placesOver_finite D.host.E (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hu hwl
  intro B σ hB hσ
  have hl : w ∉ placesOver D.host.E (D.ntw.l i) := hwl
  have e1 := (hr.2.2 w hl).2.2 hu B σ hB hσ
  rw [galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  have e2 := hν.frob ha (Or.inl hl) (shiftChar_unr C w) hB hσ

  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hfe : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {((C.eta.val w : ℂˣ) : ℂ)} := by
    rw [hCS.frob _ w ((hCS.unr_iff _ w).1 hue), hCS.etaTinv, HChar.val_inv, inv_inv]
  have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  have hM : ((((twGL (inQ ρ.κ ν) r σ : GL (Fin D.R.r) (Qbar (D.ntw.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i)))).map ρ.ι.toRingHom) =
      ρ.ι (toQ ρ.κ ((ν σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) •
        ((r σ : GL (Fin D.R.r) (Qbar (D.ntw.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).map
          ρ.ι.toRingHom := by
    ext x y
    simp [GlobalTheory.TwistAbove.twGL_val, GlobalTheory.GalChar.inQ_val]
  rw [← Matrix.charpoly_map, hM, charpoly_smul_of_prod _ _ _ e1, galPol, D.naut.locG_tw,
    D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hd hu hue), D.naut.frobEig_char _ _ _ hu hue hd hfe]
  simp only [Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  congr 2
  rw [e2, shiftChar_val]
  have hq := normV_ne_zero (D := D) w
  have h0 := (C.eta.val w).ne_zero
  have e3 : ((D.R.nV : ℕ) : ℝ) = (D.R.r : ℝ) + (D.R.t : ℝ) := by
    rw [show D.R.nV = D.R.r + D.R.t from rfl]; push_cast; ring
  have e4 : ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) *
        (((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) / 2 : ℝ)) : ℂ))⁻¹ := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hq, e3]
    congr 1
    push_cast
    ring
  rw [e4, mul_inv, inv_inv]
  ring

end GlobalTheory.TripInhab
end
end

section
section
namespace GlobalTheory.TripleAdm
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar Formalism.L2.Host
variable {D : D7}
section Row
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}

theorem gw_fixed (hW : WildOne D) (hg : D.nd.goodRow σ) (hπ : IsParam σ π) (k : Fin 2) (v : D.nd.PlG k) :
    UpperTheory.GalS.Gw D.nd D.naut (D.naut.locG π (D.naut.plGw k v)) :=
  Or.inr ⟨by rw [D.naut.locG_dim]; exact UpperTheory.GalS.thr_split (D.host.g_prime k) (D.naut.plGw_over k v) (D.nd.g_split k) (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by unfold Formalism.BasicNotions.Ranks.nV; omega)),
    fun u hu hw => hW k v _ (by rw [← hπ.lab, (D.nd.lab_monic k σ v).2, D.naut.locG_dim]) u hu hw,
    _, D.ntypes.tg_mem k v, GlobalTheory.GoodRowMono.separable_fixed hg hπ.lab k v⟩

theorem charpoly_rbar_tg_eq_prod_roots (hW : WildOne D) (hg : D.nd.goodRow σ) (hπ : IsParam σ π) {l : ℕ} [Fact l.Prime] {k : Fin 2}
    (hl : l ≠ D.host.g k) (v : D.nd.PlG k) {ι : Qbar l ≃+* ℂ} {r : GalE D →* GL (Fin D.R.r) (Qbar l)}
    {red : Zbar l →+* FbAt D w} (hr : UpperTheory.GalS.IsGaloisRepOfN D π l ι r) (hρ : IsResidual ι r σ w red) :
    ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly =
      ((@rootsBar _ ⟨D.host.g_prime k⟩ (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.iota k v w x)).prod := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have h1 := (hr.2.2 _ (not_mem_of_ne (v := v) (Fact.out : l.Prime) hl)).1 (gw_fixed hW hg hπ k v) _ (D.ntypes.tg_mem k v)
  rw [D.naut.inePol_tw _ _ _ (D.ntypes.tg_mem k v), D.ntypes.inertiaCharpoly_type k v _
    (by rw [← hπ.lab, (D.nd.lab_monic k σ v).2, D.naut.locG_dim]), ← hπ.lab] at h1
  have hz : ∀ x, ∃ z : Zbar l, x ≠ 0 → (z : Qbar l) = ι.symm (D.ntypes.teichC k x) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, fun h => absurd hx h⟩
    · have hfin : IsOfFinOrder (ι.symm (D.ntypes.teichC k x)) :=
        (ι.symm.toRingHom.toMonoidHom.comp (D.ntypes.teichC k)).isOfFinOrder (isOfFinOrder_of_ne_zero hx)
      exact ⟨⟨_, hfin.norm_eq_one.le⟩, fun _ => rfl⟩
  choose z hz using hz
  obtain ⟨p, hp1, hp2⟩ := hρ.charpoly (D.ntypes.tg k v)
  have hp : p = ((rootsBar (D.nd.lab k σ v)).map fun x => X - C (z x)).prod := by
    apply Polynomial.map_injective (ι.toRingHom.comp (Zbar l).subtype) (ι.injective.comp Subtype.val_injective)
    rw [← Polynomial.map_map, hp1, h1, Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    simp [hz x (root_ne_zero hg k v hx)]
  rw [← hp2, hp, Polynomial.map_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
  rw [← hρ.teich k hl v x (root_ne_zero hg k v hx) _ (hz x (root_ne_zero hg k v hx))]
  simp

end Row
end GlobalTheory.TripleAdm
end
end

section
section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

theorem charpoly_lattice_alt {D : D7} (hC : GlobalTheory.RowTie.ChebSplit D.nd) {Rw : RowSide D} (i : D.nd.Loc)
    (ι : Qbar (D.what₂.places.resChar (D.nd.w i)) ≃+* ℂ) (hι : D.naut.iotaQC i = qCast (D.nd.w_l i) ι)
    {σ : D.what₂.FT} (hW : ∀ w, D.naut.locW i σ w = Rw.locR σ w) {Sig : List (Formalism.BasicNotions.Part D.naut.CG)}
    {ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)} (hP : HasParamW D.nd D.naut i σ Sig)
    (hR : IsRepOfSig D.nd D.naut i Sig ρ) {π : D.naut.CG D.R.r} (hπ : IsRowPar Rw σ π)
    {r : GalE D →* GL (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))} (hr : UpperTheory.GalS.IsGaloisRepOfN D π _ ι r) (g : GalE D) :
    ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        (ι.symm.toRingHom.comp (iotaO D.nd D.naut i)) =
      ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))).charpoly := by
  have hc : Continuous (ι.symm.toRingHom.comp (iotaO D.nd D.naut i)) := by
    have := continuous_qCast (D.nd.w_l i) ι (GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i).1
    rw [← hι] at this
    exact this
  have hfin : (placesOver D.host.E (D.what₂.places.resChar (D.nd.w i)) ∪ ⋃ k, placesOver D.host.E (D.host.g k)).Finite :=
    (Formalism.L2.TwC.placesOver_finite' _ _ (D.what₂.places.resChar_prime _).ne_zero).union
      (Set.finite_iUnion fun k => Formalism.L2.TwC.placesOver_finite' _ _ (D.host.g_prime k).ne_zero)
  have hall := Filter.eventually_cofinite.1 (hR.2.2.and hfin.eventually_cofinite_notMem)
  rw [← Matrix.charpoly_map]
  refine GlobalTheory.TypeLeaf.charpoly_eq_of_dense _ (Qbar (D.what₂.places.resChar (D.nd.w i))) D.R.r
    (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
      (ι.symm.toRingHom.comp (iotaO D.nd D.naut i)))
    (fun g => ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar (D.nd.w i)))))
    _ (hC hall.toFinset) (hR.1.matrix_map hc) hr.1 ?_ g
  rintro y ⟨w, hw, hs, B, hB, hy⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hw
  obtain ⟨h1, h2⟩ := hw
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at h2
  apply Polynomial.map_injective ι.toRingHom ι.injective
  have e : ι.toRingHom.comp (ι.symm.toRingHom.comp (iotaO D.nd D.naut i)) = iotaO D.nd D.naut i := by
    ext z
    simp
  rw [Matrix.charpoly_map, Polynomial.map_map, e, h1 B y hB hy, (hr.2.2 w h2.1).2.2 (hπ.1.unr w h2.2) B y hB hy,
    hP.2.2 w hs, hW w, hπ.2 w hs]

end GlobalTheory.ResLoc
end
end

section
section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

end GlobalTheory.ResLoc
end
end

section
section
namespace GlobalTheory.TripleResidual
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise
section Row
variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)

theorem reduction_eq_one_of_wildAt (hW : WildOne D) {k : Fin 2} {v : D.nd.PlG k} {π : D.naut.CG D.R.r}
    (hgw : UpperTheory.GalS.Gw D.nd D.naut (D.naut.locG π (D.naut.plGw k v)))
    (hf : (D.naut.items₂ k _ (D.naut.locG π (D.naut.plGw k v))).natDegree = D.R.r)
    {l : ℕ} [Fact l.Prime] (hl : l ≠ D.host.g k) {ι : Qbar l ≃+* ℂ} {red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l}
    {r : GalE D →* GL (Fin D.R.r) (Qbar l)} {ρ : GalE D →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)}
    (hr : UpperTheory.GalS.IsGaloisRepOfN D π l ι r) (hρ : IsReduction D red r ρ) {u : GalE D}
    (hu : WildAt (D.nd.plOm.1 (D.naut.plGw k v)) u) : ρ u = 1 := by
  have hw := not_mem_of_ne (v := v) (Fact.out : l.Prime) hl
  have huI := mem_ine_of_wildAt hu
  have h1 := (hr.2.2 _ hw).1 hgw u huI
  rw [D.naut.inePol_tw _ _ _ huI, hW k v _ (by rw [hf, D.naut.locG_dim]) u huI hu, D.naut.locG_dim] at h1
  obtain ⟨p, hp1, hp2⟩ := hρ.2.2 u
  have hp : p = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective (ι.toRingHom.comp (Zbar l).subtype) (ι.injective.comp Subtype.val_injective)
    rw [← Polynomial.map_map, hp1, h1]
    simp
  refine eq_one_of_wildAt (D.nd.plOm.2 _) hw ρ hρ.1 hu ?_
  rw [← hp2, hp]
  simp

end Row
end GlobalTheory.TripleResidual
end
end

section
section
namespace GlobalTheory.Triple
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)
variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}

theorem unramified_of_isGaloisRepOfN_of_unr {a : ℕ} {π : D.naut.CG a} {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {r : GalE D →* GL (Fin a) (Qbar l)} (h : UpperTheory.GalS.IsGaloisRepOfN D π l ι r) {w : PlE D.host} (hl : w ∉ placesOver D.host.E l)
    (hu : D.naut.unr (D.naut.locG π w)) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver (F := D.host.E) A w)
    {σ : GalE D} (hσ : σ ∈ Ine (F := D.host.E) A) : r σ = 1 := by
  refine GlobalTheory.PointIrredCompare.Ine_le_of_normal (D.nd.plOm.2 w) hA r.ker (fun τ hτ => ?_) hσ
  obtain ⟨h1, h2, -⟩ := h.2.2 w hl
  obtain ⟨-, h4⟩ := (D.naut.unr_iff_ine _).1 ((D.naut.unr_tw _ ((1 - (a : ℝ)) / 2)).2 hu)
  refine eq_one_of_isOfFinOrder_of_charpoly (finite_zpowers.1 ((h2 hu).subset ?_)) ?_
  · rintro _ ⟨n, rfl⟩
    exact ⟨τ ^ n, zpow_mem hτ n, map_zpow r τ n⟩
  · apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [h1 (Or.inl hu) τ hτ, h4 τ hτ, D.naut.lpDim_tw, D.naut.locG_dim]
    simp

end GlobalTheory.Triple
end
end

section
namespace GlobalTheory.TripleAdm
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar Formalism.L2.Host
variable {D : D7}
section Row
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}

end Row
end GlobalTheory.TripleAdm
end
