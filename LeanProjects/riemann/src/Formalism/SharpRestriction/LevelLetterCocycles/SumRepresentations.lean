import Formalism.ConjugateSelfDual.StatementRest
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem

noncomputable section

namespace Formalism.MainNotions.SumRepresentations

namespace At

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

section RepOps

variable {Γ : Type} [Group Γ] {k : Type} [CommRing k]

def blkHom (a b : ℕ) :
    (Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) →* Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) k where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]

def sumRep {a b : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) : Γ →* GL (Fin (a + b)) k :=
  (Units.map (((Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toRingHom.toMonoidHom).comp
    (blkHom a b))).comp ((MulEquiv.prodUnits.symm : _ ≃* (Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k)ˣ).toMonoidHom.comp
      (ρ.prod ρ'))

def twGL {a : ℕ} (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) : Γ →* GL (Fin a) k where
  toFun g := Units.map (algebraMap k (Matrix (Fin a) (Fin a) k)).toMonoidHom (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    ext1
    simp only [map_mul, Units.val_mul, Units.coe_map]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Algebra.commutes _ _

end RepOps

def ContQ (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) : Prop :=
  Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))))

def WDok (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (w : PlE H) : Prop :=
  w ∉ placesOver H.E (N.l i) ∨ A.IsdRW i ρ w

def TieLP : Prop :=
  ∀ (w : PlE H) (a b χ χ' : A.LP w) (s : ℝ), A.lpDim χ = 1 → A.lpDim χ' = 1 →
    A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
    A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧
    A.lpChar a (A.lpTw χ s) = A.lpTw (A.lpChar a χ) s ∧
    A.lpChar (A.lpChar a χ) χ' = A.lpChar a (A.lpChar χ χ') ∧
    A.lpChar a (A.lpUnr w {1}) = a ∧
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      ((A.inePol a σ).Monic ∧ (A.inePol a σ).natDegree = A.lpDim a) ∧
      ∀ c : ℂ, A.inePol χ σ = X - C c → A.inePol (A.lpChar a χ) σ = (A.inePol a σ).scaleRoots c

def TieAut : Prop :=
  (A.csd A.etaT ∧ A.csd A.etaTinv) ∧
  (∀ τ : H.E →+* ℂ, (A.infG A.etaT τ = {1 / 2} ∨ A.infG A.etaT τ = {-(1 / 2)}) ∧
      A.infG A.etaTinv τ = (A.infG A.etaT τ).map (fun z => -z)) ∧
  (∀ w, A.tempered (A.locG A.etaT w)) ∧
  (∀ i w, A.tempered (A.locG (A.muC i) w))

def TieGal : Prop :=
  CrysIffWD N A ∧ PotCrysIffWD N A ∧ JumpsCard N A ∧
  ∀ i,
  (∀ a (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))), ContQ N i ρ → ∀ w, w ∉ placesOver H.E (N.l i) →
      ∀ p q : A.LP w, A.wdOf i ρ w = A.lpSum p q →
      ∃ U U' : Submodule (Qbar (N.l i)) (Fin a → Qbar (N.l i)), IsCompl U U' ∧
        Module.finrank (Qbar (N.l i)) U = A.lpDim p ∧ Module.finrank (Qbar (N.l i)) U' = A.lpDim q ∧
        (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
          (∀ v ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).mulVec v ∈ U) ∧
          (∀ v ∈ U', ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).mulVec v ∈ U')) ∧
        (A.mono0 q → ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), ∀ c : Qbar (N.l i),
          A.inePol q σ = (X - C (A.iotaQC i c)) ^ A.lpDim q →
          ∀ v ∈ U', ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).mulVec v = c • v)) ∧
  (∀ a (ρ ρ' : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))), ContQ N i ρ →
      ∀ Pm : GL (Fin a) (Qbar (N.l i)), (∀ g, ρ' g = Pm⁻¹ * ρ g * Pm) →
      (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ' w ↔ A.IsdRW i ρ w) ∧
      (∀ w, WDok N A i ρ w → A.wdOf i ρ' w = A.wdOf i ρ w) ∧
      (∀ τ, (∀ w, InducesW N i τ w → A.IsdRW i ρ w) → A.jumpsW i ρ' τ = A.jumpsW i ρ τ)) ∧
  (∀ a b (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (ρ' : G H.E N.Om →* GL (Fin b) (Qbar (N.l i))),
      ContQ N i ρ → ContQ N i ρ' →
      (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i (sumRep ρ ρ') w ↔ A.IsdRW i ρ w ∧ A.IsdRW i ρ' w) ∧
      (∀ w, WDok N A i ρ w → WDok N A i ρ' w →
        A.wdOf i (sumRep ρ ρ') w = A.lpSum (A.wdOf i ρ w) (A.wdOf i ρ' w)) ∧
      (∀ τ, (∀ w, InducesW N i τ w → A.IsdRW i ρ w ∧ A.IsdRW i ρ' w) →
        A.jumpsW i (sumRep ρ ρ') τ = A.jumpsW i ρ τ + A.jumpsW i ρ' τ)) ∧
  (∀ a (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (χ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i))),
      ContQ N i ρ → ContQ N i χ →
      (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i χ w →
        (A.IsdRW i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ A.IsdRW i ρ w)) ∧
      (∀ w, WDok N A i ρ w → WDok N A i χ w →
        A.wdOf i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = A.lpChar (A.wdOf i ρ w) (A.wdOf i χ w)) ∧
      (∀ τ (c : ℤ), (∀ w, InducesW N i τ w → A.IsdRW i ρ w ∧ A.IsdRW i χ w) → A.jumpsW i χ τ = {c} →
        A.jumpsW i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (A.jumpsW i ρ τ).map (· + c)))

def IsHeckeGaloisQ (i : N.Loc) (x : N.X i) (ρ : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i))) : Prop :=
  ContQ N i ρ ∧ IsSSRep ρ ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))).charpoly =
      (heckePol N i x w).map (iotaOQ N A i)

def OLarge : Prop :=
  ∀ i (x : N.X i) (ρ : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i))), IsHeckeGaloisQ N A i x ρ →
    ∃ (r : G H.E N.Om →* GL (Fin R.nV) (N.O i)) (Pm : GL (Fin R.nV) (Qbar (N.l i))),
      ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm

def G1 (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ (g : G H.E N.Om) (k : ℕ), ∃ f : N.T i, ∀ x,
    (f : N.X i → N.O i) x =
      ((r x g : GL (Fin R.nV) (N.O i)) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpolyRev.coeff k

def G2 (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ w ∈ placesOver H.E (N.l i),
    (N.l i ≠ H.g 0 → N.l i ≠ H.g 1 → ∀ x, A.IsCrysW i (mapRep (iotaOQ N A i) (r x)) w ∧
      ∀ τ, InducesW N i τ w → A.jumpsW i (mapRep (iotaOQ N A i) (r x)) τ = A.locAutHodgeTateWeightsLevelZero i τ) ∧
    ((N.l i = H.g 0 ∨ N.l i = H.g 1) → ∀ x,
      (∀ P Pa, A.ptV i P = some x → IsBCV N A i P Pa → A.mono0 (isoLoc N A Pa w)) →
      A.IsPotCrysW i (mapRep (iotaOQ N A i) (r x)) w)

def G3 (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  (∃ (K' : Type) (_ : Field K') (_ : Algebra (Kf N i) K') (_ : FiniteDimensional (Kf N i) K'),
    ∀ x, (∀ W, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W →
        AbsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W) ∧
      ∀ W₁ W₂, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ →
        IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₂ →
        W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ W₂) ∧
  ∀ (x y : N.X i) (g : G H.E N.Om),
    ((redRep N i (r x) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      ((redRep N i (r y) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly

def G4 (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x w, w ∉ placesOver H.E (N.l i) → w ∉ N.S i → w ∉ N.Q i → UnramAt (F := H.E) (r x) w

def Conclusion41 (i : N.Loc) : Prop :=
  ((∃ rq : N.X i → (G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i))), ∀ x, IsHeckeGaloisQ N A i x (rq x)) ∧
    ∃ r, GoodR N i r) ∧
  (∀ P P' : A.AV i, A.ptV i P ≠ none → A.ptV i P = A.ptV i P' →
    (∀ Pa Pa', IsBCV N A i P Pa → IsBCV N A i P' Pa' → Pa.Perm Pa') ∧
    ∀ w, w ∉ N.S i → w ∉ N.Q i →
      (IsSplitPl H w → A.locV i P w = A.locV i P' w) ∧
      (¬ IsSplitPl H w → ubc R.nV (A.satV i P w) = ubc R.nV (A.satV i P' w))) ∧
  ∀ r, GoodR N i r → G1 N i r ∧ G2 N A i r ∧ G3 N i r ∧ G4 N i r

def CuspidalGaloisUnramified (i : N.Loc) : Prop :=
  ∀ r, GoodR N i r → ∀ x, (x ∈ ZgoodN N A i ∨ (x ∈ ZN N A i ∧ ∃ Sig, HasParamX N A i x Sig ∧ IsCuspIso N A Sig)) →
    ∀ ρ : G H.E N.Om →* GL (Fin R.r) (N.O i),
    IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) →
    (∀ g, ((r x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly =
      ((ρ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c g : (N.O i)ˣ) : N.O i))) →
    ∀ w : PlE H,
      H0 ((Formalism.MainNotions.N.Glob.WpK N i ρ).comp (Dec (F := H.E) (N.plOm.1 w)).subtype) = ⊥ ∧
      H0 ((Formalism.MainNotions.N.coefRep (Formalism.MainNotions.N.Glob.T2 N i ρ) (Kf N i)).comp
        (Dec (F := H.E) (N.plOm.1 w)).subtype) = ⊥

def Conclusion42 (i : N.Loc) : Prop :=
  ∀ σ, what₂.isot (N.j i) σ ≠ ⊥ →
    ((∃ lam : ℝ, 0 < lam ∧ ∀ f ∈ what₂.isot (N.j i) σ,
        what₂.thetaP (N.mu i) (N.j i) (what₂.thetaT (N.mu i) (N.j i) f) = (lam : ℂ) • f) ∧
      ∃ P, thetaOf N A i σ P) ∧
    (∃ Sig, HasParamW N A i σ Sig ∧
      ∀ P, thetaOf N A i σ P → IsBCV N A i P (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv)) ∧
    (N.goodRow σ → ∀ Sig, HasParamW N A i σ Sig → IsCuspIso N A Sig)

def chiEpsBar (i : N.Loc) (e : ℤ) : G H.E N.Om →* (IsLocalRing.ResidueField (N.O i))ˣ :=
  ((Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (N.chi i 1))⁻¹ *
    ((Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO N i)) ^ e

def HStarZero (i : N.Loc) (w : PlE H)
    (ρ : Representation (IsLocalRing.ResidueField (N.O i)) (G H.E N.Om)
      (Fin R.r → IsLocalRing.ResidueField (N.O i))) : Prop :=
  letI : TopologicalSpace (IsLocalRing.ResidueField (N.O i)) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField (N.O i)) := ⟨rfl⟩
  H0 (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) = ⊥ ∧
  Subsingleton (H1 (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype)) ∧
  Subsingleton (H2 (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype))

def Del (i : N.Loc) : Prop :=
  ∀ w ∈ N.S i, w ∈ placesOver H.E (if N.l i = H.pde then H.pde' else H.pde) →
    Nat.card ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) = 15

def IdempotentChoiceProperties {i : N.Loc} (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (G H.E N.Om →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=

  (InR N i r S.eB ∧ InR N i r S.e1 ∧ S.eB * S.eB = S.eB ∧ S.e1 * S.e1 = S.e1 ∧
    S.eB * S.e1 = 0 ∧ S.e1 * S.eB = 0 ∧
    (∀ x, ((S.eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((S.e1 x).map (toK N i)).rank = 1)) ∧

  (∀ g u, S.e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
      ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧
  (∀ a, InR' N r S a → ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) =
      (((S.ψρ a).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i (S.ψχ c a) * (S.e u).2 c)) ∧
  (∀ A : Matrix (Fin R.r) (Fin R.r) (N.O i), ∃ a, InR' N r S a ∧ S.ψρ a = A) ∧

  (∃ w ∈ placesOver H.E (N.l i), S.g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧

  (InR N i r S.X0 ∧ S.eB * S.X0 = S.X0 ∧ S.X0 * S.eB = S.X0 ∧
    ∀ u, S.e (((S.X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) S.g0 : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧

  ((∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') ∧ (∀ c ∈ Finset.Icc 1 R.t, S.rr c ∈ S.T') ∧
    S.T' = Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f (S.p x')) '' (N.T i : Set _) ∪
      (fun c => S.rr c) '' (Finset.Icc 1 R.t : Set ℕ)) ∧
    (∃ b : Fin R.t.factorial → S.X' → N.O i, (∀ k, b k ∈ S.T') ∧
      ∀ f ∈ S.T', ∃! cf : Fin R.t.factorial → N.T i,
        f = ∑ k, ((fun x' => (cf k : N.X i → N.O i) (S.p x')) : S.X' → N.O i) * b k) ∧
    (∀ x, Nat.card {x' // S.p x' = x} = R.t.factorial)) ∧

  (∀ x', ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) =
    Matrix.det ((Polynomial.X : Polynomial (N.O i)) • (S.eB (S.p x')).map (Polynomial.C (R := N.O i)) -
      (S.X0 (S.p x')).map (Polynomial.C (R := N.O i)) + 1 -
      (S.eB (S.p x')).map (Polynomial.C (R := N.O i)))) ∧

  (S.p S.π' = π ∧ ∀ c ∈ Finset.Icc 1 R.t,
    S.rr c S.π' = ((chiU N i c S.g0 : (N.O i)ˣ) : N.O i)) ∧

  ((∀ x', ((Eel N S x').map (toK N i)).rank = 1) ∧
    (∀ x', Eel N S x' * Eel N S x' = del51 N S x' • Eel N S x') ∧
    (∀ u, S.e (((Eel N S S.π').map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => if (c : ℕ) = 0 then toK N i (del51 N S S.π') * (S.e u).2 c else 0))) ∧

  CharpolyCoeffsInSubalgebra N i S.T' (fun x' => rO N i r (S.p x'))

theorem inertia_props_of_idempotent_choice {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))}
    {ρ : N.X i → (G H.E N.Om →* GL (Fin R.r) (N.O i))} {π : N.X i} {S : IdempotentChoiceData N i} (h : GoodCongruenceObjects N r ρ π S) :
    IdempotentChoiceProperties N r ρ π S := by
  obtain ⟨c1, c2, c3, c4, c5, -, c7, c8, c9, c10, ⟨e1, e2, e3, -⟩, c12⟩ := h
  exact ⟨c1, c2, c3, c4, c5, c7, c8, c9, c10, ⟨e1, e2, e3⟩, c12⟩

def ConclusionG5 (i : N.Loc) : Prop :=
  HG N A i → ∀ r, GoodR N i r → ∀ w : PlE H, (w ∈ N.S i ∨ w ∈ N.Q i) →
    w ∉ placesOver H.E (N.l i) →
    ((w ∈ N.Q i ∨ w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde')) → ∀ x,
      (∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - 1) *
          (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0) ∧
      ∃ Pm : GL (Fin R.nV) (Kf N i), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        ((Pm⁻¹ * mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ * Pm : GL _ _) :
          Matrix (Fin R.nV) (Fin R.nV) (Kf N i)) =
        Matrix.diagonal (fun k : Fin R.nV => if (k : ℕ) < R.r then 1 else algebraMap (N.O i) (Kf N i) (chi1 N i γ))) ∧
    ((∃ k, w ∈ placesOver H.E (H.g k)) → w ∈ N.S i →
      ∃ Pp : Polynomial (N.T i),
        IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
        ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
          Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
              (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
            (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0) ∧
    (w ∈ N.S i →
      (∀ (ρ : N.X i → (G H.E N.Om →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i),
        IdempotentChoiceProperties N r ρ π S → ∀ (c : Fin R.t) (φ : (S.X' → MatN N i) →ₗ[N.O i] KmodO (N.O i)),
        (∀ a, InR' N r S a → ∀ y, InY N r S y → φ (a * y) = S.ψχ c a • φ y) →
        ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w), φ (yg N r S γ) = 0) ∧
      ∀ rb, IsRhoBar N i rb → ∀ e : ℤ, HStarZero N i w (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (chiEpsBar N i e)))

def ConclusionG6 (i : N.Loc) : Prop :=
  HG N A i → ∀ r, GoodR N i r → ∀ x,
    (∃ v : Fin R.nV → Kf N i, v ≠ 0 ∧ ∀ g,
      ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) g : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Kf N i)).mulVec v = algebraMap (N.O i) (Kf N i) (chi1 N i g) • v) →
    x ∈ ZN N A i ∧ ∀ Sig, HasParamX N A i x Sig → IsCuspIso N A Sig

open Classical in

def ConclusionZ (i : N.Loc) : Prop :=
  HG N A i →
    (∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
      LinearMap.ker ((what₂.thetaT (N.mu i) (N.j i)).domRestrict (MjSig N A i Sig)) = ⊥ ∧
      (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) = eigC N A i x) ∧
    (goodPartM N A i).map (what₂.thetaT (N.mu i) (N.j i)) = ⨆ x ∈ ZgoodN N A i, eigC N A i x ∧
    ∑ x : N.X i, (if x ∈ ZgoodN N A i then N.mult i x else 0) = dM N A i

def admBC : Prop := ∀ i (P : A.AV i), ∃ Pa, IsBCV N A i P Pa

def exists_galois_rep_local_global_compatible : Prop :=
  ∀ i, (∀ a, 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
      ∃ ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) ∧
        IsSSRep ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) →
          A.wdOf i ρ w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2) ∧ A.tempered (A.locG π w)) ∧
        (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧
          (∀ τ, InducesW N i τ w → A.jumpsW i ρ τ = A.jumpsInf i π τ) ∧
          A.wdOf i ρ w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2))) ∧
    (∀ a (π : A.CG a), A.ralg π → ∃ w₀ : ℂ, ∀ τ : H.E →+* ℂ,
      A.infG π (τ.comp (H.conj : H.E ≃ₐ[ℚ] H.E).toRingEquiv.toRingHom) = (A.infG π τ).map (w₀ - ·)) ∧
    (∀ (χ : A.CG 1) (s : ℝ), (∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
      ∃ ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)), ContQ N i ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i ρ w = A.lpTw (A.locG χ w) s) ∧
        ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧ A.wdOf i ρ w = A.lpTw (A.locG χ w) s ∧
          ∀ τ, InducesW N i τ w → (A.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
            (A.infG χ ((A.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))))

def ThetaLocalSplit : Prop :=
  ∀ i σ P, thetaOf N A i σ P →
    ∀ w, IsSplitPl H w → A.locV i P w =
      A.lpChar (A.lpSum (A.locW i σ w) (spehLoc N A (muPart N A i) w)) (A.locG A.etaTinv w)

def MonodromyInertiaType : Prop :=
  (∀ (i : N.Loc) (P : A.AV i) (w : PlE H), (w ∈ N.S i ∨ w ∈ N.Q i) →
    (w ∈ N.Q i ∨ (Del N i ∧ (w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde')))) →
    A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t) ∧
  (∀ (i : N.Loc) (P : A.AV i) (w : PlE H), w ∈ N.S i → (∃ k, w ∈ placesOver H.E (H.g k)) →
    TameGen N (N.plOm.1 w) (N.gam0 i w) →
    (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t →
    ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧
      ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t) ∧
  ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b

def JacquetShalikaStrongMultOne : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa') ∧
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa') ∧
  (∀ Sg : Set (PlE H), Sg.Finite →
    closure {σ : G H.E N.Om | ∃ w ∉ Sg, IsSplitPl H w ∧ ∃ B : ValuationSubring N.Om,
      IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ} = Set.univ) ∧
  (∀ (k : Type) [Field k] (a : ℕ) (ρ ρ' : G H.E N.Om →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' →
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) k).charpoly) →
    ∃ Pm : GL (Fin a) k, ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)

def TemperedCuspidal : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.csd π → A.ralg π → ∀ w, A.tempered (A.locG π w)

def IrreducibilityParameter : Prop :=
  ∀ i σ, what₂.isot (N.j i) σ ≠ ⊥ → N.goodRow σ → ∀ Sig, HasParamW N A i σ Sig →
    ∀ ρ, IsRepOfSig N A i Sig ρ →
      Formalism.CyclotomicNorms.IrredOn (mapRep ((A.kFbar i).comp (IsLocalRing.residue (N.O i))) ρ) ⊤ ∧
      ∀ k, N.l i ≠ H.g k → ∀ v : N.PlG k, TameGen N (N.plOm.1 (A.plGw k v)) (N.gam0 i (A.plGw k v)) →
        ¬ (((mapRep ((A.kFbar i).comp (IsLocalRing.residue (N.O i))) ρ (N.gam0 i (A.plGw k v)) :
            GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
          ((A.kFbar i) (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i (A.plGw k v)))))

def ResidualIrreducibility : Prop :=
  ∀ i, HG N A i → ∀ rb : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i)), IsRhoBar N i rb →
    Formalism.CyclotomicNorms.IrredOn (mapRep (A.kFbar i) rb) ⊤ ∧
    ∀ k, N.l i ≠ H.g k → ∀ v ∈ placesOver H.E (H.g k),
      ¬ (((rb (N.gam0 i v) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i v)))

end At

open Formalism.BasicNotions

def tie0 (D : D7) : Prop := At.TieLP D.nd D.naut ∧ At.TieAut D.nd D.naut ∧ At.TieGal D.nd D.naut

def hypO (D : D7) : Prop := At.OLarge D.nd D.naut

def adm1 (D : D7) : Prop := At.admBC D.nd D.naut

def adm2 (D : D7) : Prop := At.exists_galois_rep_local_global_compatible D.nd D.naut

def adm3 (D : D7) : Prop := At.ThetaLocalSplit D.nd D.naut

def ArchimedeanSignatureMatching (D : D7) : Prop := At.MonodromyInertiaType D.nd D.naut

def adm5 (D : D7) : Prop := At.JacquetShalikaStrongMultOne D.nd D.naut

def adm6 (D : D7) : Prop := At.ResidualIrreducibility D.nd D.naut

def adm7 (D : D7) : Prop := At.TemperedCuspidal D.nd D.naut

def adm8 (D : D7) : Prop := Rows.IsotInternal D.what₂

def Conclusion41 (D : D7) : Prop := ∀ i, At.Conclusion41 D.nd D.naut i

def CuspidalGaloisUnramified (D : D7) : Prop := ∀ i, At.CuspidalGaloisUnramified D.nd D.naut i

def Conclusion42 (D : D7) : Prop := ∀ i, At.Conclusion42 D.nd D.naut i

def ConclusionG5 (D : D7) : Prop := ∀ i, At.ConclusionG5 D.nd D.naut i

def ConclusionG6 (D : D7) : Prop := ∀ i, At.ConclusionG6 D.nd D.naut i

def ConclusionZ (D : D7) : Prop := ∀ i, At.ConclusionZ D.nd D.naut i

def Conclusion1 (D : D7) : Prop := Conclusion41 D ∧ CuspidalGaloisUnramified D ∧ Conclusion42 D

def Conclusion2 (D : D7) : Prop := ConclusionG5 D ∧ ConclusionG6 D ∧ ConclusionZ D

def AdmA (D : D7) : Prop := tie0 D ∧ hypO D ∧ adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D

def AdmAt (D : D7) : Prop := AdmA D ∧ adm7 D

def admitted (D : D7) : Prop := AdmAt D ∧ adm6 D ∧ adm8 D

def IntegralityFromMetric (D : D7) : Prop := AdmAt D → Conclusion1 D
def HodgeTateFromSandwich (D : D7) : Prop := admitted D → Conclusion2 D

def Stmt (D : D7) : Prop := IntegralityFromMetric D ∧ HodgeTateFromSandwich D

end Formalism.MainNotions.SumRepresentations

end
