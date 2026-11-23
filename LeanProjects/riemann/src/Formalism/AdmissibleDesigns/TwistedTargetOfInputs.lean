import Formalism.AdmissibleDesigns.YtTargetOf
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.FirstSummandActionMem

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section GenE

variable {G : Type} [Group G] {LL : Type} [Field LL]
    {O : Type} [CommRing O] [IsDomain O] {e : FractionRing O ≃+* LL}
    {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
    (r : GG →* A) (χ : GG →* T'ˣ) (E : A) (Dw : Subgroup GG) (eG : ↥Dw ≃* G)

variable (O) in

def lRep : Representation O GG A where
  toFun g := LinearMap.mulLeft O (uElt r χ g)
  map_one' := LinearMap.ext fun a => by simp [uElt_one]
  map_mul' g h := LinearMap.ext fun a => by simp [uElt_mul, mul_assoc]

abbrev aVG : Representation LL G (TrV e (MK (O := O) A)) :=
  repL e (locRep (resRep (lRep O r χ) Dw)) eG.symm.toMonoidHom

def j1 : (↥(Ymod r χ E) × O) →ₗ[O] A := LinearMap.fst O A O ∘ₗ ytEmb O r χ E

theorem projection_equivariant (g : GG) (m : ↥(Ymod r χ E) × O) : j1 r χ E (ytRep O r χ E g m) = lRep O r χ g (j1 r χ E m) := by
  rcases m with ⟨y, c⟩
  have hu : ((↑(χ g)⁻¹ : T') • r g : A) = uElt r χ g := by simp [uElt]
  simp only [j1, ytEmb, ytRep, lRep, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.coe_mk, AddHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.mulLeft_apply, Submodule.coe_add, Submodule.coe_smul_of_tower]
  simp [yY, ycoc, hu, sub_mul, smul_sub, mul_add, mul_smul_comm, smul_eq_mul]
  all_goals first | abel1 | exact trivial

def jK : MK (O := O) (↥(Ymod r χ E) × O) →ₗ[O] MK (O := O) A := liftK (mkK ∘ₗ j1 r χ E)

theorem jK_mk (m : ↥(Ymod r χ E) × O) : jK r χ E (mkK m) = mkK (j1 r χ E m) := by
  exact liftK_mkK _ m

theorem jK_equiv (g : GG) (v : MK (O := O) (↥(Ymod r χ E) × O)) :
    jK r χ E (locRep (ytRep O r χ E) g v) = locRep (lRep O r χ) g (jK r χ E v) := by
  have key : (jK r χ E).comp (locRep (ytRep O r χ E) g) = (locRep (lRep O r χ) g).comp (jK r χ E) := by
    refine IsLocalizedModule.ext (S := nonZeroDivisors O) (f := mkK (O := O) (M := ↥(Ymod r χ E) × O)) ?_ ?_
    · exact fun s => isUnit_end s
    · apply LinearMap.ext
      intro m
      simp only [LinearMap.comp_apply, locRep_mkK, jK_mk, projection_equivariant]
  exact LinearMap.congr_fun key v

variable [TopologicalSpace LL]

def embY {k mA : ℕ} (v₀ : Fin k → LL) (φA : TrV e (MK (O := O) A) →ₗ[LL] (Fin mA → Fin k → LL)) :
    TrV e (MK (O := O) (↥(Ymod r χ E) × O)) →ₗ[LL] (Fin (mA + 1) → Fin k → LL) :=
  consV (W := Fin k → LL) mA ∘ₗ (LinearMap.smulRight (pY e ↥(Ymod r χ E)) v₀) +
    consZ (W := Fin k → LL) mA ∘ₗ (φA ∘ₗ trL e (jK r χ E))

theorem embY_apply {k mA : ℕ} (v₀ : Fin k → LL) (φA : TrV e (MK (O := O) A) →ₗ[LL] (Fin mA → Fin k → LL))
    (v : TrV e (MK (O := O) (↥(Ymod r χ E) × O))) :
    embY r χ E v₀ φA v = Fin.cons (pY e ↥(Ymod r χ E) v • v₀) (φA (trL e (jK r χ E) v)) := by
  funext a
  refine Fin.cases ?_ (fun j => ?_) a
  · simp [embY, consV, consZ]
  · simp [embY, consV, consZ]

theorem embY_of [NoZeroSMulDivisors O A] {ιx : Type} {k mA : ℕ} (Ms : ιx → G →* Matrix (Fin k) (Fin k) LL)
    (xsA : Fin mA → ιx) (φA : TrV e (MK (O := O) A) →ₗ[LL] (Fin mA → Fin k → LL)) (hφA : Function.Injective φA)
    (heqA : ∀ g v, φA (aVG (e := e) r χ Dw eG g v) = fun a => (Ms (xsA a) g).mulVec (φA v a))
    (x₀ : ιx) (v₀ : Fin k → LL) (hv₀ : v₀ ≠ 0) (hfix : ∀ g, (Ms x₀ g).mulVec v₀ = v₀) :
    Function.Injective (embY r χ E v₀ φA) ∧
      ∀ g v, embY r χ E v₀ φA (ytVG (e := e) r χ E Dw eG g v) =
        fun a => (Ms ((Fin.cons x₀ xsA : Fin (mA + 1) → ιx) a) g).mulVec (embY r χ E v₀ φA v a) := by

  have hsnd : ∀ h : GG,
      (liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O ↥(Ymod r χ E) O)).comp
          (locRep (ytRep O r χ E) h) =
        liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O ↥(Ymod r χ E) O) := by
    intro h
    refine IsLocalizedModule.ext (S := nonZeroDivisors O) (f := mkK (O := O) (M := ↥(Ymod r χ E) × O)) ?_ ?_
    · exact fun s => isUnit_end s
    · apply LinearMap.ext
      intro m
      simp only [LinearMap.comp_apply, locRep_mkK, liftK_mkK]
      all_goals rfl
  have hpY : ∀ g v, pY e ↥(Ymod r χ E) (ytVG (e := e) r χ E Dw eG g v) = pY e ↥(Ymod r χ E) v := by
    intro g v
    exact congrArg (eLin e) (LinearMap.congr_fun (hsnd ((eG.symm g : Dw) : GG)) v)
  have hjK : ∀ g v, trL e (jK r χ E) (ytVG (e := e) r χ E Dw eG g v) =
      aVG (e := e) r χ Dw eG g (trL e (jK r χ E) v) := by
    intro g v
    exact jK_equiv r χ E ((eG.symm g : Dw) : GG) v

  have hker : ∀ v : MK (O := O) (↥(Ymod r χ E) × O), jK r χ E v = 0 →
      liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O ↥(Ymod r χ E) O) v = 0 →
      v = 0 := by
    intro v h1 h2
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (S := nonZeroDivisors O)
      (f := mkK (O := O) (M := ↥(Ymod r χ E) × O)) v
    simp only at hs
    rw [Submonoid.smul_def] at hs
    have hm2 : m.2 = 0 := by
      have h3 := congrArg (liftK (V := FractionRing O)
        (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O ↥(Ymod r χ E) O)) hs
      rw [map_smul, h2, smul_zero, liftK_mkK] at h3
      have h' : algebraMap O (FractionRing O) m.2 = 0 := by simpa using h3.symm
      exact (IsFractionRing.injective O (FractionRing O)) (h'.trans (map_zero _).symm)
    have hm1 : j1 r χ E m = 0 := by
      have h3 := congrArg (jK r χ E) hs
      rw [map_smul, h1, smul_zero, jK_mk] at h3
      obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (S := nonZeroDivisors O)
        (f := mkK (O := O) (M := A))).1 h3.symm
      rw [Submonoid.smul_def] at ht
      exact (smul_eq_zero.1 ht).resolve_left (nonZeroDivisors.coe_ne_zero t)
    have hm : m = 0 := by
      rcases m with ⟨y, c⟩
      simp only at hm2
      subst hm2
      have hy : (y : A) = 0 := by simpa [j1, ytEmb] using hm1
      exact Prod.ext (Submodule.coe_eq_zero.1 hy) rfl
    rw [hm, map_zero] at hs
    have hu := (Module.End.isUnit_iff _).1 (isUnit_end (V := MK (O := O) (↥(Ymod r χ E) × O)) s)
    apply hu.1
    rw [Module.algebraMap_end_apply, map_zero]
    exact hs
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    rw [embY_apply] at hv
    have hp : pY e ↥(Ymod r χ E) v = 0 := by
      have h0 := congrFun hv 0
      simp only [Fin.cons_zero, Pi.zero_apply] at h0
      exact (smul_eq_zero.1 h0).resolve_right hv₀
    have hj : trL e (jK r χ E) v = 0 := by
      apply hφA
      rw [map_zero]
      funext a
      have h0 := congrFun hv a.succ
      simpa only [Fin.cons_succ, Pi.zero_apply] using h0
    have hp' : e (liftK (V := FractionRing O)
        (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O ↥(Ymod r χ E) O) v) = 0 := hp
    exact hker v hj ((map_eq_zero_iff e e.injective).1 hp')
  · intro g v
    funext a
    rw [embY_apply, embY_apply]
    refine Fin.cases ?_ (fun j => ?_) a
    · simp only [Fin.cons_zero]
      rw [hpY, Matrix.mulVec_smul, hfix]
    · simp only [Fin.cons_succ]
      rw [hjK, heqA]

end GenE

section RecE

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

def EmbRW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∃ (m : ℕ) (xs : Fin m → D.nd.X i)
    (φ : TrV (eS i hw) (MK (O := D.nd.O i) ↥Dd.R') →ₗ[↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1]
      (Fin m → Fin D.R.nV → ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)),
    Function.Injective φ ∧ ∀ g v, φ (aVG (e := eS i hw) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) g v) =
      fun a => (MsW i r hw (xs a) g).mulVec (φ v a)

def LineW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∃ (x₀ : D.nd.X i) (v₀ : Fin D.R.nV → ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1), v₀ ≠ 0 ∧
    ∀ g, (MsW i r hw x₀ g).mulVec v₀ = v₀

theorem ytEmbW_of {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hE : EmbRW i dc r Dd hw) (hL : LineW i r hw) : YtEmbW i dc r Dd hw := by
  obtain ⟨mA, xs, φ, hφ, heq⟩ := hE
  obtain ⟨x₀, v₀, hv₀, hfix⟩ := hL
  haveI hK : NoZeroSMulDivisors (D.nd.O i) (FractionRing (D.nd.O i)) := by
    first
    | exact inferInstance
    | exact ⟨fun {c x} h => by
        rw [Algebra.smul_def, mul_eq_zero] at h
        exact h.imp_left (fun h' => (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h')⟩
  haveI hM : NoZeroSMulDivisors (D.nd.O i)
      (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) :=
    inferInstanceAs (NoZeroSMulDivisors (D.nd.O i) (Dd.X' → Fin D.R.nV → Fin D.R.nV → FractionRing (D.nd.O i)))
  haveI : NoZeroSMulDivisors (D.nd.O i) ↥Dd.R' :=
    Function.Injective.noZeroSMulDivisors Subtype.val Subtype.val_injective rfl (fun _ _ => rfl)
  have h := embY_of (r := Dd.r) (χ := Dd.χ) (E := Dd.E) (Dw := Dw i dc (idx i dc w)) (eG := eW i dc hw)
    (Ms := MsW i r hw) (xsA := xs) (φA := φ) (hφA := hφ) (heqA := heq) (x₀ := x₀) (v₀ := v₀) (hv₀ := hv₀)
    (hfix := hfix)
  exact ⟨mA + 1, Fin.cons x₀ xs, _, h.1, h.2⟩

end RecE

section RecL

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem msW_entry {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i)
    (g : Br.G D.nbr i w hw) :
    MsW i r hw x g = (mapM (toK D.nd i) (rTwO D.nd i r x) ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map (eS i hw) := by
  ext a b
  simp only [Matrix.map_apply]
  first
  | rfl
  | (simp [MsW, TruncatedSeriesCountingIdentities.locC, Br.loc, mapM, Br.locM, decS, eS, Br.locO, eK, Br.iota, Br.toLLK, toK]; done)
  | (simp [MsW, TruncatedSeriesCountingIdentities.locC, Br.loc, mapM, Br.locM, decS, eS, Br.locO, eK, Br.iota, Br.toLLK]
     erw [RingEquiv.ofBijective_apply, IsFractionRing.lift_algebraMap]
     rfl)

theorem fixK (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    ∃ u₀ : Fin D.R.nV → KK D.nd i, u₀ ≠ 0 ∧ ∀ h : GE D.nd, (mapM (toK D.nd i) (rTwO D.nd i r π) h).mulVec u₀ = u₀ := by
  obtain ⟨e, he⟩ := hD
  have ht : 0 < D.R.t := D.R.t_odd.pos
  refine ⟨e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1), ?_, fun h => ?_⟩
  · intro h0
    have h1 := congrArg e h0
    rw [LinearEquiv.apply_symm_apply, map_zero] at h1
    have h2 := congrArg (fun p => p.2 ⟨0, ht⟩) h1
    simp at h2
  · apply e.injective
    have hM : mapM (toK D.nd i) (rTwO D.nd i r π) h =
        toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rO D.nd i r π) h := by
      ext a b
      simp [mapM, rTwO, twistM]
    have hsm : ∀ (s : KK D.nd i) (M : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) (u : Fin D.R.nV → KK D.nd i),
        (s • M).mulVec u = s • M.mulVec u := by
      intro s M u
      first
      | exact Matrix.smul_mulVec s M u
      | exact Matrix.smul_mulVec_assoc s M u
      | (funext j; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])
    rw [hM, hsm, map_smul, he, LinearEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · simp
    · funext c
      by_cases hc : c = ⟨0, ht⟩
      · subst hc
        simp [← map_mul]
      · simp [Pi.single_apply, hc]

theorem lineW_of (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : LineW i r hw := by
  obtain ⟨u₀, hu₀, hfix⟩ := fixK i r ρ π hD
  refine ⟨π, fun j => eS i hw (u₀ j), ?_, fun g => ?_⟩
  · intro h0
    apply hu₀
    funext j
    have h1 := congrFun h0 j
    simpa using h1
  · rw [msW_entry i r hw π g]
    funext j
    have h2 := RingHom.map_mulVec (eS i hw).toRingHom
      (mapM (toK D.nd i) (rTwO D.nd i r π) ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)) u₀ j
    rw [hfix] at h2
    exact h2.symm

end RecL

section RecT

variable {D : D7} {i : D.nd.Loc} {dc : TruncatedSeriesCountingIdentities.Decl D i}
  {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} (π : D.nd.X i)
  {Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R)}
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

theorem twisted_target_of_inputs (hfin : Module.Finite (D.nd.O i) Dd.R') (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hE : EmbRW i dc r Dd hw) (hc : MsContW i r hw)
    [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (c : Fin (D.R.t + 1)) :
    YtTarget i dc r π Dd hw c := by
  exact ytTarget_of (hfin := hfin) (hF := hF) (hG2 := hG2)
    (hemb := ytEmbW_of i dc r Dd hw hE (lineW_of i r ρ π hD hw)) (hc := hc) (c := c)

end RecT

end Formalism.MainNotions.N.K.TBa

end
