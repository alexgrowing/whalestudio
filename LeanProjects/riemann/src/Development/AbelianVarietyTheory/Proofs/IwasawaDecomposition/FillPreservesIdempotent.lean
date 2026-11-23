import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature

noncomputable section

namespace GlobalTheory.RowPar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Filter

theorem exists_ss {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) :
    ∃ r : Γ →* GL (Fin n) k, IsSSRep r ∧ ρ.ker ≤ r.ker ∧
      ∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin n) (Fin n) k).charpoly := by
  obtain ⟨s, hs⟩ := GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf (glRep (QuotientGroup.kerLift ρ))
  let t : (Γ ⧸ ρ.ker) →* GL (Fin n) k :=
    ((LinearMap.toMatrixAlgEquiv' (R := k) (n := Fin n)).toAlgHom.toMonoidHom.comp s).toHomUnits
  have ht : ∀ x, (t x : Matrix (Fin n) (Fin n) k) = LinearMap.toMatrix' (s x) := fun _ => rfl
  have hv : ∀ x v, (t x : Matrix (Fin n) (Fin n) k).mulVec v = s x v := fun x v => by
    rw [ht, LinearMap.toMatrix'_mulVec]
  refine ⟨t.comp (QuotientGroup.mk' _), fun W hW => ?_, fun g hg => ?_, fun g => ?_⟩
  · obtain ⟨W', h1, h2⟩ := hs.1 W fun x v hx => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
      rw [← hv]
      exact hW g v hx
    exact ⟨W', fun g v hx => (hv _ v).symm ▸ h1 (QuotientGroup.mk' _ g) v hx, h2⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg, map_one]
  · have h := GlobalTheory.SemisimplificationCharpoly.charpoly_eq _ _ hs (QuotientGroup.mk' _ g)
    rw [MonoidHom.comp_apply, ht, ← Matrix.charpoly_toLin', Matrix.toLin'_toMatrix', h]
    exact Matrix.charpoly_toLin' _

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}

theorem eq_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    {f f' : G H.E N.Om → Y} (hf : Continuous f) (hf' : Continuous f')
    (h : ∀ᶠ w in cofinite, IsSplitPl H w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → f σ = f' σ) : f = f' := by
  obtain ⟨S, hS, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split H
  refine hC.eq_of_frob (hS.union (eventually_cofinite.1 h)) hf hf' fun v hv hd B hB σ hσ => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  exact hv.2 (hsp v hv.1 hd) B σ hB hσ

variable (A : NAut N)

def redAt (i : N.Loc) {w : what₂.places.Pl} (h : N.w i = w) :
    N.O i →+* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w) :=
  (fbCast (h ▸ N.w_l i) (what₂.places.resChar_prime w) (N.lPrime i).out).symm.toRingHom.comp
    ((A.kFbar i).comp (IsLocalRing.residue (N.O i)))

def LocWIndep : Prop := ∀ i i' σ w, IsSplitPl H w → A.locW i σ w = A.locW i' σ w

def LocWIndepAt : Prop := ∀ i i', N.w i = N.w i' → ∀ σ w, IsSplitPl H w → A.locW i σ w = A.locW i' σ w

theorem LocWIndep.at {A : NAut N} (h : LocWIndep A) : LocWIndepAt A := fun i i' _ => h i i'

def RedIndep : Prop := ∀ (w : what₂.places.Pl) (i i' : N.Loc) (h : N.w i = w) (h' : N.w i' = w) (x : N.O i) (x' : N.O i'),
  iotaO N A i x = iotaO N A i' x' → redAt A i h x = redAt A i' h' x'

theorem redIndep_of_map (κ : ∀ w, ℂ → Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))
    (hκ : ∀ i x, fbCast (N.w_l i) (what₂.places.resChar_prime (N.w i)) (N.lPrime i).out (κ (N.w i) (iotaO N A i x)) =
      A.kFbar i (IsLocalRing.residue (N.O i) x)) : RedIndep A := by
  have key : ∀ w i (h : N.w i = w) x, redAt A i h x = κ w (iotaO N A i x) := by
    rintro _ i rfl x
    exact (RingEquiv.symm_apply_eq _).2 (hκ i x).symm
  intro w i i' h h' x x' e
  rw [key, key, e]

theorem iotaO_injective (i : N.Loc) : Function.Injective (iotaO N A i) :=
  ((A.iotaQC i).toRingHom.comp (A.iotaQ i)).injective.comp (IsFractionRing.injective _ _)

theorem redIndep_of_injective (h : Function.Injective N.w) : RedIndep A := by
  rintro _ i i' rfl h' x x' e
  obtain rfl := h h'
  rw [iotaO_injective A _ e]

theorem continuous_red (i : N.Loc) {k : Type} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    (κ : IsLocalRing.ResidueField (N.O i) →+* k) {n : ℕ} {ρ : G H.E N.Om → Matrix (Fin n) (Fin n) (N.O i)}
    (hρ : Continuous ρ) : Continuous fun g => (ρ g).map (κ.comp (IsLocalRing.residue (N.O i))) := by
  refine hρ.matrix_map (continuous_of_continuousAt_zero _ ?_)
  have ho := (isAdic_iff.1 (N.O_adic i)).1 1
  rw [pow_one] at ho
  refine (continuousAt_const (y := (0 : k))).congr ?_
  filter_upwards [ho.mem_nhds (Ideal.zero_mem _)] with x hx
  rw [RingHom.comp_apply, (IsLocalRing.residue_eq_zero_iff x).2 hx, map_zero]

theorem continuous_redAt (i : N.Loc) {w : what₂.places.Pl} (h : N.w i = w)
    [TopologicalSpace (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))]
    [DiscreteTopology (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))]
    {n : ℕ} {ρ : G H.E N.Om → Matrix (Fin n) (Fin n) (N.O i)} (hρ : Continuous ρ) :
    Continuous fun g => (ρ g).map (redAt A i h) :=
  continuous_red i ((fbCast (h ▸ N.w_l i) (what₂.places.resChar_prime w) (N.lPrime i).out).symm.toRingHom.comp
    (A.kFbar i)) hρ

variable {A}

theorem charpoly_red_eq (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hW : LocWIndepAt A) (hR : RedIndep A)
    {w : what₂.places.Pl} {σ : what₂.FT} {i i' : N.Loc} (h : N.w i = w) (h' : N.w i' = w)
    {Sig Sig' : List (Formalism.BasicNotions.Part A.CG)} {ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)}
    {ρ' : G H.E N.Om →* GL (Fin R.r) (N.O i')} (h1 : HasParamW N A i σ Sig) (h2 : IsRepOfSig N A i Sig ρ)
    (h1' : HasParamW N A i' σ Sig') (h2' : IsRepOfSig N A i' Sig' ρ') (g : G H.E N.Om) :
    (ρ g : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly.map (redAt A i h) =
      (ρ' g : Matrix (Fin R.r) (Fin R.r) (N.O i')).charpoly.map (redAt A i' h') := by
  letI : TopologicalSpace (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w)) := ⊥
  haveI : DiscreteTopology (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w)) := ⟨rfl⟩
  letI : TopologicalSpace (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))[X] := ⊥
  haveI : DiscreteTopology (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))[X] := ⟨rfl⟩
  have hc : Continuous (Matrix.charpoly : Matrix (Fin R.r) (Fin R.r)
      (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w)) → _) := continuous_of_discreteTopology
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
  refine congrFun (eq_of_split hC (hc.comp (continuous_redAt A i h h2.1))
    (hc.comp (continuous_redAt A i' h' h2'.1)) ?_) g
  filter_upwards [h2.2.2, h2'.2.2] with v e e' hv B s hB hs
  have e3 := e B s hB hs
  rw [h1.2.2 v hv, hW i i' (h.trans h'.symm) σ v hv, ← h1'.2.2 v hv, ← e' B s hB hs] at e3
  simp only [Function.comp_apply, Matrix.charpoly_map]
  ext n
  rw [coeff_map, coeff_map]
  exact hR w i i' h h' _ _ (by simpa only [coeff_map] using congrArg (coeff · n) e3)

section Residual

variable (A) (B₀ : what₂.places.Pl → ValuationSubring ℂ)
  (κ : ∀ w, B₀ w →+* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))

def LiesOverAt (w : what₂.places.Pl) : Prop := ∀ x, 0 ≤ what₂.places.val w x ↔ what₂.embLL x ∈ B₀ w

def RedTie : Prop := ∀ i (x : N.O i), ∃ h : iotaO N A i x ∈ B₀ (N.w i), κ (N.w i) ⟨_, h⟩ = redAt A i rfl x

def IsRbar (σ : what₂.FT) (w : what₂.places.Pl)
    (r : G H.E N.Om →* GL (Fin R.r) (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))) : Prop :=
  IsSSRep r ∧ IsOpen (r.ker : Set (G H.E N.Om)) ∧ ∃ i Sig, HasParamW N A i σ Sig ∧
    ∀ᶠ v in cofinite, IsSplitPl H v → ∀ (B : ValuationSubring N.Om) (s : G H.E N.Om),
      IsPlaceOver (F := H.E) B v → IsFrob (F := H.E) B (normV v) s →
      ∃ p : (B₀ w)[X], p.map (B₀ w).subtype = galPol A (A.lpTw (isoLoc N A Sig v) ((1 - (R.r : ℝ)) / 2)) ∧
        (r s : Matrix (Fin R.r) (Fin R.r) _).charpoly = p.map (κ w)

open Classical in

def rbarOf (σ : what₂.FT) (w : what₂.places.Pl) :
    G H.E N.Om →* GL (Fin R.r) (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w)) :=
  if h : ∃ r, IsRbar A B₀ κ σ w r then h.choose else 1

theorem rbarOf_open (σ : what₂.FT) (w : what₂.places.Pl) : IsOpen ((rbarOf A B₀ κ σ w).ker : Set (G H.E N.Om)) := by
  unfold rbarOf
  split_ifs with h
  · exact h.choose_spec.2.1
  · simp

theorem rbarOf_ss (σ : what₂.FT) (w : what₂.places.Pl) : IsSSRep (rbarOf A B₀ κ σ w) := by
  unfold rbarOf
  split_ifs with h
  · exact h.choose_spec.1
  · intro W _
    obtain ⟨W', h'⟩ := W.exists_isCompl
    exact ⟨W', fun g v hv => by simpa using hv, h'⟩

variable {A B₀ κ}

theorem IsRbar.chosen {σ : what₂.FT} {w : what₂.places.Pl} {r} (h : IsRbar A B₀ κ σ w r) :
    IsRbar A B₀ κ σ w (rbarOf A B₀ κ σ w) := by
  have h' : ∃ r, IsRbar A B₀ κ σ w r := ⟨r, h⟩
  rw [rbarOf, dif_pos h']
  exact h'.choose_spec

theorem redTie_iff : RedTie A B₀ κ ↔ ∀ i (x : N.O i), ∃ h : iotaO N A i x ∈ B₀ (N.w i),
    fbCast (N.w_l i) (what₂.places.resChar_prime (N.w i)) (N.lPrime i).out (κ (N.w i) ⟨_, h⟩) =
      A.kFbar i (IsLocalRing.residue (N.O i) x) :=
  forall₂_congr fun _ _ => exists_congr fun _ => eq_comm.trans ((RingEquiv.symm_apply_eq _).trans eq_comm)

theorem RedTie.redIndep (h : RedTie A B₀ κ) : RedIndep A := by
  rintro _ i i' rfl h' x x' e
  have key : ∀ w i (hi : N.w i = w) (x : N.O i), ∃ h : iotaO N A i x ∈ B₀ w, κ w ⟨_, h⟩ = redAt A i hi x := by
    rintro _ i rfl x
    exact h i x
  obtain ⟨a, b⟩ := key _ i rfl x
  obtain ⟨a', b'⟩ := key _ i' h' x'
  rw [← b, ← b']
  exact congrArg _ (Subtype.ext e)

theorem RedTie.liesOverAt (h : RedTie A B₀ κ) (i : N.Loc) : LiesOverAt B₀ (N.w i) := by
  have e : ∀ x y, algebraMap (N.O i) (FractionRing (N.O i)) y = N.embK i x → iotaO N A i y = what₂.embLL x :=
    fun x y hy => by rw [← A.iota_LL i x, ← hy]; rfl
  intro x
  rw [N.embK_w]
  refine ⟨fun ⟨y, hy⟩ => e x y hy ▸ (h i y).1, fun hx => ?_⟩
  rcases ValuationRing.isInteger_or_isInteger (N.O i) (N.embK i x) with hy | ⟨y, hy⟩
  · exact hy
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨a, b⟩ := h i y
  have e1 : (⟨_, hx⟩ : B₀ (N.w i)) * ⟨_, a⟩ = 1 := Subtype.ext <| by
    change what₂.embLL x * iotaO N A i y = 1
    rw [e x⁻¹ y (by rw [hy, map_inv₀]), ← map_mul, mul_inv_cancel₀ h0, map_one]
  have hu : IsUnit y := by
    by_contra hn
    have h1 := congrArg (κ (N.w i)) e1
    rw [map_mul, b, map_one, redAt, RingHom.comp_apply, RingHom.comp_apply,
      (IsLocalRing.residue_eq_zero_iff y).2 hn, map_zero, map_zero, mul_zero] at h1
    exact zero_ne_one h1
  obtain ⟨u, rfl⟩ := hu
  exact ⟨(u⁻¹ : (N.O i)ˣ), by rw [map_units_inv, hy, inv_inv]⟩

theorem exists_isRbar_of_lattice {σ : what₂.FT} {w : what₂.places.Pl} {i : N.Loc} {Sig : List (Formalism.BasicNotions.Part A.CG)}
    (h1 : HasParamW N A i σ Sig) {O : Type} [CommRing O] (φ : O →+* B₀ w) (ρ : G H.E N.Om →* GL (Fin R.r) O)
    (ho : IsOpen ((mapRep ((κ w).comp φ) ρ).ker : Set (G H.E N.Om)))
    (h2 : ∀ᶠ v in cofinite, IsSplitPl H v → ∀ (B : ValuationSubring N.Om) (s : G H.E N.Om),
      IsPlaceOver (F := H.E) B v → IsFrob (F := H.E) B (normV v) s →
      (ρ s : Matrix (Fin R.r) (Fin R.r) O).charpoly.map ((B₀ w).subtype.comp φ) =
        galPol A (A.lpTw (isoLoc N A Sig v) ((1 - (R.r : ℝ)) / 2))) :
    ∃ r, IsRbar A B₀ κ σ w r ∧ ∀ g, (r g : Matrix (Fin R.r) (Fin R.r) _).charpoly =
      (ρ g : Matrix (Fin R.r) (Fin R.r) O).charpoly.map ((κ w).comp φ) := by
  obtain ⟨r, hs, hk, hc⟩ := exists_ss (mapRep ((κ w).comp φ) ρ)
  refine ⟨r, ⟨hs, Subgroup.isOpen_mono hk ho, i, Sig, h1, ?_⟩, fun s => (hc s).trans (Matrix.charpoly_map _ _)⟩
  filter_upwards [h2] with v e hv B s hB hs
  refine ⟨(ρ s : Matrix (Fin R.r) (Fin R.r) O).charpoly.map φ, ?_, ?_⟩
  · rw [Polynomial.map_map]
    exact e hv B s hB hs
  · rw [Polynomial.map_map]
    exact (hc s).trans (Matrix.charpoly_map _ _)

theorem exists_isRbar (h : RedTie A B₀ κ) {i : N.Loc} {σ : what₂.FT} {Sig : List (Formalism.BasicNotions.Part A.CG)}
    {ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)} (h1 : HasParamW N A i σ Sig) (h2 : IsRepOfSig N A i Sig ρ) :
    ∃ r, IsRbar A B₀ κ σ (N.w i) r ∧ ∀ g, (r g : Matrix (Fin R.r) (Fin R.r) _).charpoly =
      (ρ g : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly.map (redAt A i rfl) := by
  obtain ⟨φ, e1, e2⟩ : ∃ φ : N.O i →+* B₀ (N.w i),
      (B₀ (N.w i)).subtype.comp φ = iotaO N A i ∧ (κ (N.w i)).comp φ = redAt A i rfl :=
    ⟨(iotaO N A i).codRestrict (B₀ (N.w i)) fun x => (h i x).1, RingHom.ext fun _ => rfl,
      RingHom.ext fun x => (h i x).2⟩
  rw [← e2]
  refine exists_isRbar_of_lattice h1 φ ρ ?_ (h2.2.2.mono fun v e _ => e1.symm ▸ e)
  letI : TopologicalSpace (Fb (what₂.places.resChar (N.w i)) (what₂.places.resChar_prime (N.w i))) := ⊥
  haveI : DiscreteTopology (Fb (what₂.places.resChar (N.w i)) (what₂.places.resChar_prime (N.w i))) := ⟨rfl⟩
  rw [e2]
  convert (isOpen_discrete {1}).preimage (continuous_redAt A i rfl h2.1) using 1
  ext g
  exact ⟨fun e => congrArg Units.val e, fun e => Units.ext e⟩

theorem IsRbar.charpoly_eq (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hW : LocWIndep A) {σ : what₂.FT}
    {w : what₂.places.Pl} {r r'} (h : IsRbar A B₀ κ σ w r) (h' : IsRbar A B₀ κ σ w r') (g : G H.E N.Om) :
    Matrix.charpoly (Units.val (r g)) = Matrix.charpoly (Units.val (r' g)) := by
  obtain ⟨-, o, i, S, a, b⟩ := h
  obtain ⟨-, o', i', S', a', b'⟩ := h'
  letI : TopologicalSpace (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))[X] := ⊥
  haveI : DiscreteTopology (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))[X] := ⟨rfl⟩
  have hc : ∀ r : G H.E N.Om →* GL (Fin R.r) (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w)),
      IsOpen (r.ker : Set (G H.E N.Om)) → Continuous fun g => Matrix.charpoly (Units.val (r g)) := by
    intro r o
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g =>
      ⟨(fun x => g⁻¹ * x) ⁻¹' r.ker, o.preimage (by fun_prop), by simp, fun x hx => ?_⟩)
    have : r (g⁻¹ * x) = 1 := hx
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    rw [this]
  refine congrFun (eq_of_split hC (hc r o) (hc r' o') ?_) g
  filter_upwards [b, b'] with v e e' hv B s hB hs
  obtain ⟨p, p1, p2⟩ := e hv B s hB hs
  obtain ⟨p', p1', p2'⟩ := e' hv B s hB hs
  rw [a.2.2 v hv, hW i i' σ v hv, ← a'.2.2 v hv, ← p1'] at p1
  rw [p2, p2', Polynomial.map_injective _ Subtype.val_injective p1]

theorem rbarOf_charpoly (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hW : LocWIndep A) {σ : what₂.FT} {w : what₂.places.Pl}
    {i : N.Loc} {Sig : List (Formalism.BasicNotions.Part A.CG)} (h1 : HasParamW N A i σ Sig) {O : Type} [CommRing O]
    (φ : O →+* B₀ w) (ρ : G H.E N.Om →* GL (Fin R.r) O)
    (ho : IsOpen ((mapRep ((κ w).comp φ) ρ).ker : Set (G H.E N.Om)))
    (h2 : ∀ᶠ v in cofinite, IsSplitPl H v → ∀ (B : ValuationSubring N.Om) (s : G H.E N.Om),
      IsPlaceOver (F := H.E) B v → IsFrob (F := H.E) B (normV v) s →
      (ρ s : Matrix (Fin R.r) (Fin R.r) O).charpoly.map ((B₀ w).subtype.comp φ) =
        galPol A (A.lpTw (isoLoc N A Sig v) ((1 - (R.r : ℝ)) / 2))) (g : G H.E N.Om) :
    (rbarOf A B₀ κ σ w g : Matrix (Fin R.r) (Fin R.r) _).charpoly =
      (ρ g : Matrix (Fin R.r) (Fin R.r) O).charpoly.map ((κ w).comp φ) := by
  obtain ⟨r, hr, hc⟩ := exists_isRbar_of_lattice h1 φ ρ ho h2
  rw [hr.chosen.charpoly_eq hC hW hr, hc]

theorem rbarTie (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hW : LocWIndep A) (hR : RedTie A B₀ κ) {X : NTypes A}
    (hX : X.rbar = rbarOf A B₀ κ) : RbarTie N A X := by
  intro i σ Sig ρ h1 h2
  obtain ⟨r, hr, hc⟩ := exists_isRbar hR h1 h2
  rw [hX]
  refine ⟨hr.chosen.1, fun g => ?_⟩
  rw [hr.chosen.charpoly_eq hC hW hr, hc, Polynomial.map_map]
  congr 1
  ext x
  exact RingEquiv.apply_symm_apply _ _

end Residual

variable (A)

def FrobFam (i : N.Loc) (f : PlE H → ℂ[X]) : Prop :=
  ∃ F : Qbar (N.l i) → G H.E N.Om → Qbar (N.l i), (∀ z, Continuous (F z)) ∧
    ∀ᶠ w in cofinite, ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ → ∀ z, A.iotaQC i (F z σ) = (f w).eval (A.iotaQC i z)

variable {A}

theorem FrobFam.congr {i : N.Loc} {f f' : PlE H → ℂ[X]} (h : FrobFam A i f) (e : ∀ᶠ w in cofinite, f w = f' w) :
    FrobFam A i f' := by
  obtain ⟨F, h1, h2⟩ := h
  exact ⟨F, h1, (h2.and e).mono fun w hw => hw.2 ▸ hw.1⟩

theorem FrobFam.one (i : N.Loc) : FrobFam A i fun _ => 1 :=
  ⟨fun _ _ => 1, fun _ => continuous_const, Eventually.of_forall fun _ _ _ _ _ _ => by simp⟩

theorem FrobFam.mul {i : N.Loc} {f f' : PlE H → ℂ[X]} (h : FrobFam A i f) (h' : FrobFam A i f') :
    FrobFam A i fun w => f w * f' w := by
  obtain ⟨F, h1, h2⟩ := h
  obtain ⟨F', h1', h2'⟩ := h'
  refine ⟨fun z σ => F z σ * F' z σ, fun z => (h1 z).mul (h1' z), (h2.and h2').mono fun w hw B σ hB hσ z => ?_⟩
  rw [map_mul, hw.1 B σ hB hσ, hw.2 B σ hB hσ, eval_mul]

theorem FrobFam.eq_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) {i : N.Loc} {f f' : PlE H → ℂ[X]}
    (h : FrobFam A i f) (h' : FrobFam A i f') (e : ∀ᶠ w in cofinite, IsSplitPl H w → f w = f' w) :
    ∀ᶠ w in cofinite, f w = f' w := by
  obtain ⟨F, h1, h2⟩ := h
  obtain ⟨F', h1', h2'⟩ := h'
  have hF : ∀ z, F z = F' z := fun z => GlobalTheory.RowPar.eq_of_split hC (h1 z) (h1' z) <| by
    filter_upwards [h2, h2', e] with w a a' b hw B σ hB hσ
    apply (A.iotaQC i).injective
    rw [a B σ hB hσ, a' B σ hB hσ, b hw]
  filter_upwards [h2, h2'] with w a a'
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 w)
  refine Polynomial.funext fun z => ?_
  obtain ⟨z, rfl⟩ := (A.iotaQC i).surjective z
  rw [← a _ σ (N.plOm.2 w) hσ, ← a' _ σ (N.plOm.2 w) hσ, hF]

theorem frobFam_cusp (hG : GlobalTheory.GalOfCusp.Reading A) (i : N.Loc) {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hπ : A.csd π)
    (s : ℝ) (hs : GlobalTheory.GalOfCusp.RegAlgShift A π s) :
    FrobFam A i fun w => galPol A (A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)) := by
  obtain ⟨r, hr⟩ := hG i a ha π hπ s hs
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (Fact.out : (N.l i).Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  refine ⟨fun z σ => (r σ : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.eval z, fun z => ?_, ?_⟩
  · simp only [Matrix.eval_charpoly]
    exact (continuous_const.sub hr.cont).matrix_det
  · filter_upwards [hfin.eventually_cofinite_notMem, A.locG_unr_ae π] with w h1 h2 B σ hB hσ z
    rw [← (hr.frob h1 h2).2 B σ hB hσ]
    exact (eval_map_apply (A.iotaQC i).toRingHom _).symm

open GlobalTheory.RowTie

variable (A) in
theorem twSum_unr (L : List ((Σ a : ℕ, A.CG a) × ℝ)) : ∀ᶠ w in cofinite, ∀ p ∈ L, A.unr (A.locG p.1.2 w) :=
  (eventually_all_finite L.finite_toSet).2 fun p _ => A.locG_unr_ae p.1.2

theorem frobEig_twSum {L : List ((Σ a : ℕ, A.CG a) × ℝ)} {w : PlE H} (h : ∀ p ∈ L, A.unr (A.locG p.1.2 w)) :
    A.unr (twSum N A L w) ∧
      A.frobEig (twSum N A L w) = (L.map fun p => A.frobEig (A.lpTw (A.locG p.1.2 w) p.2)).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons p L ih =>
    have h1 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have h2 := (A.unr_tw _ p.2).2 (h p List.mem_cons_self)
    exact ⟨(A.unr_sum _ _).2 ⟨h2, h1.1⟩, by
      rw [List.map_cons, List.sum_cons, ← h1.2]; exact A.frobEig_sum _ _ h2 h1.1⟩

theorem frobFam_twSum (hG : GlobalTheory.GalOfCusp.Reading A) (i : N.Loc) (u : ℝ) (L : List ((Σ a : ℕ, A.CG a) × ℝ))
    (hL : ∀ p ∈ L, 1 ≤ p.1.1 ∧ A.csd p.1.2 ∧ GlobalTheory.GalOfCusp.RegAlgShift A p.1.2 (p.2 + u - (1 - (p.1.1 : ℝ)) / 2)) :
    FrobFam A i fun w => galPol A (A.lpTw (twSum N A L w) u) := by
  induction L with
  | nil =>
    refine (FrobFam.one i).congr (Eventually.of_forall fun w => ?_)
    simp [galPol, twSum, A.frobEig_tw _ u (A.lpZero_unr w), A.frobEig_zero]
  | cons p L ih =>
    obtain ⟨h1, h2, h3⟩ := hL p List.mem_cons_self
    refine ((frobFam_cusp hG i h1 _ h2 _ h3).mul (ih fun q hq => hL q (List.mem_cons_of_mem _ hq))).congr ?_
    filter_upwards [A.locG_unr_ae p.1.2, twSum_unr A L] with w a b
    change _ = galPol A (A.lpTw (A.lpSum (A.lpTw (A.locG p.1.2 w) p.2) (twSum N A L w)) u)
    rw [A.lpTw_sum, A.lpTw_add, sub_add_cancel, galPol, galPol, galPol,
      A.frobEig_sum _ _ ((A.unr_tw _ _).2 a) ((A.unr_tw _ _).2 (frobEig_twSum b).1), Multiset.map_add,
      Multiset.prod_add]

theorem eq_of_galPol {w : PlE H} {a b : A.LP w} (ha : A.unr a) (hb : A.unr b) {u : ℝ}
    (h : galPol A (A.lpTw a u) = galPol A (A.lpTw b u)) : a = b := by
  have h1 := congrArg Polynomial.roots h
  rw [galPol, galPol, roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h1
  have h2 : A.lpTw a u = A.lpTw b u := by
    rw [A.unr_eq_lpUnr _ ((A.unr_tw a u).2 ha), h1, ← A.unr_eq_lpUnr _ ((A.unr_tw b u).2 hb)]
  simpa only [A.lpTw_add, add_neg_cancel, A.lpTw_zero] using congrArg (A.lpTw · (-u)) h2

variable (A) in

def IsCohSum (n : ℕ) (Sig : List (Formalism.BasicNotions.Part A.CG)) : Prop :=
  (∀ p ∈ Sig, A.csd p.π) ∧ ∀ p ∈ Sig, ∀ τ, (A.infG p.π τ).Nodup ∧
    ∀ z ∈ A.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - (p.d : ℂ)) / 2

open GlobalTheory.SpehRigid in
theorem frobFam_isoLoc (hG : GlobalTheory.GalOfCusp.Reading A) (i : N.Loc) {n : ℕ} {Sig : List (Formalism.BasicNotions.Part A.CG)}
    (h0 : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) (h : IsCohSum A n Sig) :
    FrobFam A i fun w => galPol A (A.lpTw (isoLoc N A Sig w) ((1 - (n : ℝ)) / 2)) := by
  simp only [isoLoc_eq]
  refine frobFam_twSum hG i _ _ fun q hq => ?_
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
  refine ⟨(h0 p hp).1, h.1 p hp, fun τ => ⟨(h.2 p hp τ).1, fun z hz => ?_⟩⟩
  obtain ⟨m, rfl⟩ := (h.2 p hp τ).2 z hz
  exact ⟨m - k, by push_cast; ring⟩

theorem perm_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hJ : IsobaricRigid N A) (hG : GlobalTheory.GalOfCusp.Reading A)
    (i : N.Loc) {n : ℕ} {Sig Sig' : List (Formalism.BasicNotions.Part A.CG)} (h0 : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d)
    (h0' : ∀ p ∈ Sig', 1 ≤ p.a ∧ 1 ≤ p.d) (h : IsCohSum A n Sig) (h' : IsCohSum A n Sig')
    (e : ∀ᶠ w in cofinite, IsSplitPl H w → isoLoc N A Sig w = isoLoc N A Sig' w) : Sig.Perm Sig' := by
  refine GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne R H what₂ N A hJ _ _
    (fun p hp => ⟨(h0 p hp).1, (h0 p hp).2, h.1 p hp⟩) (fun p hp => ⟨(h0' p hp).1, (h0' p hp).2, h'.1 p hp⟩) ?_
  filter_upwards [(frobFam_isoLoc hG i h0 h).eq_of_split hC (frobFam_isoLoc hG i h0' h')
    (e.mono fun w hw hs => by rw [hw hs]), twSum_unr A (Sig.flatMap (GlobalTheory.SpehRigid.flat N A)),
    twSum_unr A (Sig'.flatMap (GlobalTheory.SpehRigid.flat N A))] with w a b b'
  refine eq_of_galPol ?_ ?_ a
  · rw [GlobalTheory.SpehRigid.isoLoc_eq]; exact (frobEig_twSum b).1
  · rw [GlobalTheory.SpehRigid.isoLoc_eq]; exact (frobEig_twSum b').1

section Cusp

open GlobalTheory.CuspRep

variable [IsTotallyComplex H.E]

variable (A) in

def ReadsCusp (e : ∀ a, A.CG a → CG H.E a) : Prop :=
  (∀ a, 1 ≤ a → Function.Injective (e a)) ∧ (∀ a π, 1 ≤ a → (e a π).IsUnitary) ∧
    ∀ a π w, 1 ≤ a → A.unr (A.locG π w) → ∃ B : Multiset ℂˣ, (e a π).HasSat w B ∧
      A.frobEig (A.locG π w) = B.map fun b => ((b⁻¹ : ℂˣ) : ℂ)

theorem hasSat_twist {a : ℕ} {π : CG H.E a} {w : PlE H} {B : Multiset ℂˣ} (h : π.HasSat w B)
    {χ : Formalism.L2.Host.HChar H.E} (hχ : χ.UnrAt w) : (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem isobaricRigid_of_jacquetShalika (hJ : GlobalTheory.Published.JacquetShalikaRigidity) {e : ∀ a, A.CG a → CG H.E a}
    (he : ReadsCusp A e) : IsobaricRigid N A := by
  intro L L' hL hL' h
  let ν := GlobalTheory.HeckeGal.Model.absPow H.E
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow H.E
  let Φ : ℂˣ → ℂ := fun b => ((b⁻¹ : ℂˣ) : ℂ)
  have hΦ : Function.Injective Φ := Units.val_injective.comp inv_injective
  have key : ∀ (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H), (∀ p ∈ L, 1 ≤ p.1.1) →
      (∀ p ∈ L, A.unr (A.locG p.1.2 w)) → ∃ B : Fin L.length → Multiset ℂˣ,
        (∀ j, ((e _ (L.get j).1.2).twist (ν (L.get j).2)).HasSat w (B j)) ∧
          (∑ j, B j).map Φ = A.frobEig (twSum N A L w) := by
    intro L w h1 h2
    choose B hB hB' using fun j : Fin L.length =>
      he.2.2 _ (L.get j).1.2 w (h1 _ (List.get_mem _ _)) (h2 _ (List.get_mem _ _))
    refine ⟨_, fun j => hasSat_twist (hB j) ((hν _).1 w), ?_⟩
    rw [(frobEig_twSum h2).2, ← Multiset.coe_mapAddMonoidHom, map_sum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Eq.trans ?_ (A.frobEig_tw _ (L.get j).2 (h2 _ (List.get_mem _ _))).symm
    rw [hB', Multiset.coe_mapAddMonoidHom, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Φ, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, ν, (hν _).2.1 w,
      Complex.cpow_neg, inv_inv]
    rfl
  obtain ⟨s, hs⟩ := hJ.unitary (fun j : Fin L.length => e _ (L.get j).1.2) (fun j : Fin L'.length => e _ (L'.get j).1.2)
    (fun j => hL _ (List.get_mem _ _)) (fun j => hL' _ (List.get_mem _ _))
    (fun j => he.2.1 _ _ (hL _ (List.get_mem _ _))) (fun j => he.2.1 _ _ (hL' _ (List.get_mem _ _))) ν hν
    (fun j => (L.get j).2) (fun j => (L'.get j).2) (by
      filter_upwards [h, twSum_unr A L, twSum_unr A L'] with w a b b'
      obtain ⟨B, h1, h2⟩ := key L w hL b
      obtain ⟨B', h1', h2'⟩ := key L' w hL' b'
      exact ⟨B, B', h1, h1', Multiset.map_injective hΦ (by rw [h2, h2', a])⟩)
  have inj : ∀ p q : Σ a : ℕ, A.CG a, 1 ≤ p.1 → (⟨p.1, e _ p.2⟩ : Σ a, CG H.E a) = ⟨q.1, e _ q.2⟩ → p = q := by
    rintro ⟨a, π⟩ ⟨b, π'⟩ ha h
    obtain rfl : a = b := (Sigma.mk.inj h).1
    exact congrArg _ (he.1 a ha (eq_of_heq (Sigma.mk.inj h).2))
  have e' : ∀ L : List ((Σ a : ℕ, A.CG a) × ℝ), (L : Multiset _) = Finset.univ.val.map L.get := fun L => by
    rw [Fin.univ_val_map, List.ofFn_get]
  rw [← Multiset.coe_eq_coe, e', e', ← Finset.map_univ_equiv s, Finset.map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun j _ => Prod.ext (inj _ _ (hL _ (List.get_mem _ _)) (hs j).1) (hs j).2

end Cusp

variable (A)

def shape (Sig : List (Formalism.BasicNotions.Part A.CG)) : Multiset (ℕ × ℕ) := Multiset.ofList (Sig.map fun p => (p.a, p.d))

def IsRowPar (σ : what₂.FT) (Sig : List (Formalism.BasicNotions.Part A.CG)) : Prop :=
  (∃ i, HasParamW N A i σ Sig) ∧ IsCohSum A R.r Sig

open Classical in

def bcOf (σ : what₂.FT) : Multiset (ℕ × ℕ) :=
  if h : ∃ Sig, IsRowPar A σ Sig then shape A h.choose else {(R.r, 1)}

theorem bcOf_pos (σ : what₂.FT) : ∀ p ∈ bcOf A σ, 0 < p.1 ∧ 0 < p.2 := by
  unfold bcOf
  split_ifs with h
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hp)
    obtain ⟨⟨i, hi⟩, -⟩ := h.choose_spec
    exact hi.1 q hq
  · intro p hp
    rw [Multiset.mem_singleton.1 hp]
    have := R.two_le_m
    have := R.m_add_three_le_k
    exact ⟨by unfold Ranks.r; omega, one_pos⟩

theorem bcOf_sum (σ : what₂.FT) : ((bcOf A σ).map fun p => p.1 * p.2).sum = R.r := by
  unfold bcOf
  split_ifs with h
  · obtain ⟨⟨i, hi⟩, -⟩ := h.choose_spec
    rw [shape, Multiset.map_coe, Multiset.sum_coe, List.map_map]
    exact hi.2.1
  · simp

variable {A}

theorem IsRowPar.perm (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hJ : IsobaricRigid N A) (hG : GlobalTheory.GalOfCusp.Reading A)
    (hW : LocWIndep A) {σ : what₂.FT} {Sig Sig' : List (Formalism.BasicNotions.Part A.CG)} (h : IsRowPar A σ Sig)
    (h' : IsRowPar A σ Sig') : Sig.Perm Sig' := by
  obtain ⟨⟨i, hi⟩, h⟩ := h
  obtain ⟨⟨i', hi'⟩, h'⟩ := h'
  exact perm_of_split hC hJ hG i hi.1 hi'.1 h h' (Eventually.of_forall fun w hw => by
    rw [hi.2.2 w hw, hi'.2.2 w hw, hW i i' σ w hw])

theorem bcTie (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hJ : IsobaricRigid N A) (hG : GlobalTheory.GalOfCusp.Reading A)
    (hW : LocWIndep A) {X : NTypes A} (hX : X.bc = bcOf A) : BcTie N A X := by
  intro i σ Sig h1 h2 h3
  have h : IsRowPar A σ Sig := ⟨⟨i, h1⟩, h2, h3⟩
  rw [hX, bcOf, dif_pos ⟨Sig, h⟩]
  exact Multiset.coe_eq_coe.2 ((IsRowPar.perm hC hJ hG hW (Exists.choose_spec ⟨Sig, h⟩) h).map _)

variable (A)

def IsPar (Sig : List (Formalism.BasicNotions.Part A.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧ rankIso N A Sig = R.r ∧
  ∀ k v, (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).Monic ∧
    (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).natDegree = R.r

def Par : Type := {Sig // IsPar A Sig}

def locPar (σ : Par A) (w : PlE H) : A.LP w := isoLoc N A σ.1 w

def labPar (k : Fin 2) (σ : Par A) (v : N.PlG k) : (ZMod (H.g k))[X] :=
  A.items₂ k (A.plGw k v) (locPar A σ (A.plGw k v))

theorem lpDim_twSum (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) :
    A.lpDim (twSum N A L w) = (L.map fun p => p.1.1).sum := by
  induction L with
  | nil => exact A.lpDim_zero w
  | cons p L ih =>
    refine (A.lpDim_sum _ _).trans (congrArg₂ (· + ·) ?_ ih)
    rw [A.lpDim_tw, A.locG_dim]

theorem lpDim_isoLoc (Sig : List (Formalism.BasicNotions.Part A.CG)) (w : PlE H) : A.lpDim (isoLoc N A Sig w) = rankIso N A Sig := by
  induction Sig with
  | nil => exact A.lpDim_zero w
  | cons p L ih =>
    refine (A.lpDim_sum _ _).trans (congrArg₂ (· + ·) ?_ ih)
    rw [GlobalTheory.SpehRigid.spehLoc_eq, lpDim_twSum, GlobalTheory.SpehRigid.flat, List.map_map]
    simp [Function.comp_def, mul_comm]

variable {A} in

theorem isPar_of_hasParamW {i : N.Loc} {σ : what₂.FT} {Sig : List (Formalism.BasicNotions.Part A.CG)} (h : HasParamW N A i σ Sig)
    (hc : ∀ p ∈ Sig, A.csd p.π) (hn : (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup) :
    ∃ h' : IsPar A Sig, ∀ k v, labPar A k ⟨Sig, h'⟩ v = N.lab k σ v := by
  have e : ∀ k v, A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v)) = N.lab k σ v := fun k v => by
    rw [h.2.2 _ (GlobalTheory.Proof.SplitPlaceGoodSignature.isSplitPl_of_not_isConjPl _ (A.plGw_nconj k v v)), A.lab_loc i]
  exact ⟨⟨fun p hp => ⟨(h.1 p hp).1, (h.1 p hp).2, hc p hp⟩, hn, h.2.1, fun k v => (e k v).symm ▸ N.lab_monic k σ v⟩, e⟩

structure Spec (M : Type) [AddCommGroup M] [Module ℂ M] where

  I : Type

  tp : I → Submodule ℂ M

  loc : I → ∀ w, A.LP w

  sat : I → PlE H → Multiset ℂ

  inf : (H.E →+* ℂ) → Multiset ℂ

namespace Spec

def ofLoc (i : N.Loc) : Spec A (what₂.Mt (N.mu i) (N.j i)) := ⟨A.AV i, A.typeV i, A.locV i, A.satV i, A.infWt i⟩

theorem iSup_ofLoc (i : N.Loc) : ⨆ P, (ofLoc A i).tp P = ⊤ := A.typeV_top i

variable {A} {M : Type} [AddCommGroup M] [Module ℂ M] (S S' : Spec A M)

def IsBC (n : ℕ) (P : S.I) (Pa : List (Formalism.BasicNotions.Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = n ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = S.loc P w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧ A.frobEig (isoLoc N A Pa w) = ubc n (S.sat P w)) ∧
  ∀ τ, isoInf N A Pa τ = S.inf τ

theorem isBC_ofLoc (i : N.Loc) (P : A.AV i) (Pa : List (Formalism.BasicNotions.Part A.CG)) :
    (ofLoc A i).IsBC R.nV P Pa ↔ IsBCV N A i P Pa := Iff.rfl

def part (n : ℕ) (T : List (Formalism.BasicNotions.Part A.CG) → List (Formalism.BasicNotions.Part A.CG)) (L : ∀ w, A.LP w) : Submodule ℂ M :=
  ⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc N A Sig w = L w) ∧ S.IsBC n P (T Sig)}, S.tp P

def Sub : Prop := S.inf = S'.inf ∧ ∀ P, ∃ Q, S.tp P = S'.tp Q ∧ S.loc P = S'.loc Q ∧ S.sat P = S'.sat Q

theorem Sub.refl : S.Sub S := ⟨rfl, fun P => ⟨P, rfl, rfl, rfl⟩⟩

variable {S S'} in
theorem Sub.part_le (h : S.Sub S') (n : ℕ) (T : List (Formalism.BasicNotions.Part A.CG) → List (Formalism.BasicNotions.Part A.CG))
    (L : ∀ w, A.LP w) : S.part n T L ≤ S'.part n T L := by
  refine iSup₂_le fun P ⟨Sig, h1, h2⟩ => ?_
  obtain ⟨Q, e1, e2, e3⟩ := h.2 P
  refine e1 ▸ le_iSup₂_of_le (f := fun P (_ : P ∈ {P | ∃ Sig, (∀ w, isoLoc N A Sig w = L w) ∧ S'.IsBC n P (T Sig)}) =>
    S'.tp P) Q ⟨Sig, h1, ?_⟩ le_rfl
  unfold IsBC at h2 ⊢
  rwa [← e2, ← e3, ← h.1]

end Spec

variable {A} (S : ∀ μ j, Spec A (what₂.Mt μ j)) (T : ∀ μ, Spec A (what₂.Amb μ)) (c : what₂.Tup → ℕ → A.CG 1)

def mtPar (μ : what₂.Tup) (j : ℕ) (σ : Par A) : Submodule ℂ (what₂.Mt μ j) :=
  (S μ j).part R.nV (fun Sig => twistIso N A (Sig ++ [⟨1, c μ j, R.t⟩]) A.etaTinv) (locPar A σ)

def ambPar (μ : what₂.Tup) (σ : Par A) : Submodule ℂ (what₂.Amb μ) :=
  (T μ).part (R.r + R.m * R.t) (fun Sig => Sig ++ (List.range' 1 R.m).map fun j => ⟨1, c μ j, R.t⟩) (locPar A σ)

def SpecTie : Prop := ∀ i, (S (N.mu i) (N.j i)).Sub (Spec.ofLoc A i) ∧ (Spec.ofLoc A i).Sub (S (N.mu i) (N.j i)) ∧
  c (N.mu i) (N.j i) = A.muC i

variable (A) in

theorem exists_specTie (h : ∀ i i', N.mu i = N.mu i' → N.j i = N.j i' →
    HEq (Spec.ofLoc A i) (Spec.ofLoc A i') ∧ A.muC i = A.muC i') :
    ∃ (S : ∀ μ j, Spec A (what₂.Mt μ j)) (c : what₂.Tup → ℕ → A.CG 1), SpecTie S c := by
  have key : ∀ μ j, ∃ (S : Spec A (what₂.Mt μ j)) (c : A.CG 1), ∀ i, N.mu i = μ → N.j i = j →
      HEq S (Spec.ofLoc A i) ∧ c = A.muC i := by
    intro μ j
    by_cases hi : ∃ i, N.mu i = μ ∧ N.j i = j
    · obtain ⟨i, rfl, rfl⟩ := hi
      exact ⟨_, _, fun i' h1 h2 => h i i' h1.symm h2.symm⟩
    · exact ⟨⟨Empty, Empty.elim, Empty.elim, Empty.elim, fun _ => 0⟩, A.etaT, fun i h1 h2 => (hi ⟨i, h1, h2⟩).elim⟩
  choose S c hS using key
  refine ⟨S, c, fun i => ?_⟩
  rw [eq_of_heq (hS _ _ i rfl rfl).1]
  exact ⟨Spec.Sub.refl _, Spec.Sub.refl _, (hS _ _ i rfl rfl).2⟩

variable (B₀ : what₂.places.Pl → ValuationSubring ℂ)
  (κ : ∀ w, B₀ w →+* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))

def fill (X : NTypes A) : NTypes A :=
  { X with
    bc := bcOf A
    bc_pos := bcOf_pos A
    bc_sum := bcOf_sum A
    rbar := rbarOf A B₀ κ
    rbar_open := rbarOf_open A B₀ κ
    Par := Par A
    labPar := labPar A
    labPar_monic := fun k σ v => σ.2.2.2.2 k v
    locPar := locPar A
    locPar_dim := fun σ w => (lpDim_isoLoc A σ.1 w).trans σ.2.2.2.1
    labPar_def := fun _ _ _ => rfl
    MtPar := mtPar S c
    AmbPar := ambPar T c }

variable {S c}

theorem mtParTie (h : SpecTie S c) (X : NTypes A) : MtParTie N A (fill S T c B₀ κ X) := by
  intro i σ
  refine (le_antisymm ((h i).1.part_le _ _ _) ((h i).2.1.part_le _ _ _)).trans ?_
  rw [(h i).2.2]
  rfl

theorem fill_preserves_idempotent (X : NTypes A) : (fill S T c B₀ κ X).e0 = X.e0 ∧ ((fill S T c B₀ κ X).IdempotentMatchesAction ↔ X.IdempotentMatchesAction) := ⟨rfl, Iff.rfl⟩

theorem ties_of_record (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hJ : IsobaricRigid N A) (hG : GlobalTheory.GalOfCusp.Reading A)
    (hW : LocWIndep A) (hR : RedTie A B₀ κ) (hS : SpecTie S c) (X : NTypes A) :
    BcTie N A (fill S T c B₀ κ X) ∧ RbarTie N A (fill S T c B₀ κ X) ∧ MtParTie N A (fill S T c B₀ κ X) :=
  ⟨bcTie hC hJ hG hW rfl, rbarTie hC hW hR rfl, mtParTie T B₀ κ hS X⟩

theorem ties [IsTotallyComplex H.E] (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hJ : GlobalTheory.Published.JacquetShalika)
    {e : ∀ a, A.CG a → GlobalTheory.CuspRep.CG H.E a} (he : ReadsCusp A e) (hG : GlobalTheory.GalOfCusp.Reading A)
    (hW : LocWIndep A) (hR : RedTie A B₀ κ) (hS : SpecTie S c) (X : NTypes A) :
    BcTie N A (fill S T c B₀ κ X) ∧ RbarTie N A (fill S T c B₀ κ X) ∧ MtParTie N A (fill S T c B₀ κ X) :=
  ties_of_record T B₀ κ hC (isobaricRigid_of_jacquetShalika hJ.1 he) hG hW hR hS X

end GlobalTheory.RowPar

end
