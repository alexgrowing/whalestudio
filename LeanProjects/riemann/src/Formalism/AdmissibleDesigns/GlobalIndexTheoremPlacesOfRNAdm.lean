import Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents
import Formalism.AdmissibleDesigns.InvariantsEqBotIff

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace Formalism.MainNotions.N.K.Norm

section Split

variable {O : Type} [CommRing O] {r t : ℕ}

def splitMat (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) : Matrix (Fin (r + t)) (Fin (r + t)) O :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (Matrix.diagonal d))

theorem splitMat_mul (A A' : Matrix (Fin r) (Fin r) O) (d d' : Fin t → O) :
    splitMat A d * splitMat A' d' = splitMat (A * A') (d * d') := by
  simp only [splitMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rfl

theorem splitMat_one : splitMat (1 : Matrix (Fin r) (Fin r) O) (1 : Fin t → O) = 1 := by
  simp only [splitMat, Matrix.reindex_apply]
  rw [show (Matrix.diagonal (1 : Fin t → O)) = 1 from rfl, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem splitMat_map {O' : Type} [CommRing O'] (f : O →+* O') (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) :
    (splitMat A d).map f = splitMat (A.map f) (fun c => f (d c)) := by
  rw [splitMat, splitMat, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ f.map_zero, Matrix.map_zero _ f.map_zero, Matrix.diagonal_map f.map_zero]

theorem splitMat_castAdd (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) (a b : Fin r) :
    splitMat A d (Fin.castAdd t a) (Fin.castAdd t b) = A a b := by
  simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem splitMat_natAdd (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) (c : Fin t) :
    splitMat A d (Fin.natAdd r c) (Fin.natAdd r c) = d c := by
  simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem splitMat_off (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) (a b : Fin (r + t))
    (h : RepresentationBoundsCohomology.blkG r t a ≠ RepresentationBoundsCohomology.blkG r t b) : splitMat A d a b = 0 := by
  obtain ⟨a', rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b', rfl⟩ := finSumFinEquiv.surjective b
  rcases a' with a' | a' <;> rcases b' with b' | b'
  · exact absurd (by simp [RepresentationBoundsCohomology.blkG_castAdd]) h
  · simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply]
  · simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply]
  · simp only [finSumFinEquiv_apply_right, RepresentationBoundsCohomology.blkG_natAdd, ne_eq] at h
    have hab : a' ≠ b' := fun e => h (by rw [e])
    simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hab]

variable {Γ : Type} [Group Γ]

def chiVec (t : ℕ) (χ : ℕ → Γ →* Oˣ) (g : Γ) : Fin t → O := fun c => ((χ ((c : ℕ) + 1) g : Oˣ) : O)

theorem chiVec_mul (χ : ℕ → Γ →* Oˣ) (g h : Γ) : chiVec t χ (g * h) = chiVec t χ g * chiVec t χ h := by
  funext c
  simp [chiVec]

theorem chiVec_one (χ : ℕ → Γ →* Oˣ) : chiVec t χ 1 = 1 := by
  funext c
  simp [chiVec]

def splitRep (ρ : Γ →* GL (Fin r) O) (χ : ℕ → Γ →* Oˣ) : Γ →* GL (Fin (r + t)) O where
  toFun g := ⟨splitMat ((ρ g : GL _ _) : Matrix _ _ O) (chiVec t χ g),
    splitMat ((ρ g⁻¹ : GL _ _) : Matrix _ _ O) (chiVec t χ g⁻¹),
    by rw [splitMat_mul, ← chiVec_mul, mul_inv_cancel, chiVec_one, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, splitMat_one],
    by rw [splitMat_mul, ← chiVec_mul, inv_mul_cancel, chiVec_one, ← Units.val_mul, ← map_mul, inv_mul_cancel,
      map_one, Units.val_one, splitMat_one]⟩
  map_one' := by
    apply Units.ext
    show splitMat _ _ = 1
    rw [map_one, Units.val_one, chiVec_one, splitMat_one]
  map_mul' g h := by
    apply Units.ext
    show splitMat _ _ = splitMat _ _ * splitMat _ _
    rw [splitMat_mul, ← chiVec_mul, map_mul, Units.val_mul]

theorem splitRep_coe (ρ : Γ →* GL (Fin r) O) (χ : ℕ → Γ →* Oˣ) (g : Γ) :
    ((splitRep (t := t) ρ χ g : GL _ _) : Matrix (Fin (r + t)) (Fin (r + t)) O) =
      splitMat ((ρ g : GL _ _) : Matrix _ _ O) (chiVec t χ g) := rfl

end Split

section Rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical in

def rN : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) :=
  Function.update r π (splitRep (t := D.R.t) (ρ π) (D.nd.chi i))

def AdmR : Prop :=
  TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.admG2 i r ρ π ∧ TruncatedSeriesCountingIdentities.admG3 i r ρ π ∧ TruncatedSeriesCountingIdentities.admG4 i r ∧ TruncatedSeriesCountingIdentities.admG5 i r ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions i ∧
    TruncatedSeriesCountingIdentities.admG6 i r ∧ TruncatedSeriesCountingIdentities.admBK i ∧ LargeLevelLemmas.BlochKatoAnnihilators i ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π ∧
    LargeLevelLemmas.CyclotomicInertiaHypothesis i ∧ TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i ∧ TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible i ∧ TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i ∧ TruncatedSeriesCountingIdentities.admH2 i ∧ LargeLevelLemmas.tateH1FinitenessAtPlacesOver i ∧ TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i

theorem admitted_items_of_adm (h : LargeLevelLemmas.admitted i r ρ π) : AdmR i r ρ π := by
  obtain ⟨-, -, -, -, g1, g2, g3, g4, -, g5, g5x, g6, bk, bka, ct, ss, dcm, ep, tie, sh, fo, h2, fin, cft⟩ := h
  exact ⟨g1, g2, g3, g4, g5, g5x, g6, bk, bka, ct, ss, dcm, ep, tie, sh, fo, h2, fin, cft⟩

def RhoCont : Prop := Continuous (fun g => rhoO D.nd i ρ π g)

end Rec

section RecN

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem rN_self : rN i r ρ π π = splitRep (t := D.R.t) (ρ π) (D.nd.chi i) := by
  unfold rN
  exact Function.update_self ..

theorem rN_ne {x : D.nd.X i} (hx : x ≠ π) : rN i r ρ π x = r x := by
  unfold rN
  exact Function.update_of_ne hx ..

theorem rO_rN_self (g : GE D.nd) : rO D.nd i (rN i r ρ π) π g =
    splitMat (t := D.R.t) (rhoO D.nd i ρ π g) (chiVec D.R.t (D.nd.chi i) g) := by
  show ((rN i r ρ π π g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) = _
  rw [rN_self]
  rfl

theorem rO_rN_ne {x : D.nd.X i} (hx : x ≠ π) : rO D.nd i (rN i r ρ π) x = rO D.nd i r x := by
  simp only [rO, rN_ne i r ρ π hx]

theorem normAt_rN : RepresentationBoundsCohomology.NormAt D.nd (rN i r ρ π) ρ π := by
  refine ⟨fun g a b h => ?_, fun g c => ?_, fun g a b => ?_⟩
  · rw [rO_rN_self]
    exact splitMat_off _ _ a b h
  · rw [rO_rN_self]
    exact splitMat_natAdd _ _ c
  · rw [rO_rN_self]
    exact splitMat_castAdd _ _ a b

end RecN

section DecConj

variable {Γ : Type} {K : Type} [CommRing K] {r t : ℕ}

theorem conj_of_decomp (M : Γ → Matrix (Fin (r + t)) (Fin (r + t)) K) (A : Γ → Matrix (Fin r) (Fin r) K)
    (d : Γ → Fin t → K) (e : (Fin (r + t) → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)))
    (he : ∀ g u, e ((M g).mulVec u) = ((A g).mulVec (e u).1, fun c => d g c * (e u).2 c)) :
    IsConjM M (fun g => splitMat (A g) (d g)) := by
  let f : (Fin (r + t) → K) ≃ₗ[K] (Fin (r + t) → K) := e.trans (RepresentationBoundsCohomology.eG r t K).symm
  refine ⟨LinearMap.toMatrix' (f : (Fin (r + t) → K) →ₗ[K] (Fin (r + t) → K)),
    LinearMap.toMatrix' (f.symm : (Fin (r + t) → K) →ₗ[K] (Fin (r + t) → K)), ?_, ?_, fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.toMatrix'_id]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, LinearMap.comp_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply]
    apply (RepresentationBoundsCohomology.eG r t K).injective
    have hoff : ∀ a b, RepresentationBoundsCohomology.blkG r t a ≠ RepresentationBoundsCohomology.blkG r t b → splitMat (A g) (d g) a b = 0 :=
      fun a b h => splitMat_off _ _ a b h
    have hsub : (splitMat (A g) (d g)).submatrix (Fin.castAdd t) (Fin.castAdd t) = A g := by
      ext a b
      exact splitMat_castAdd _ _ a b
    have hdiag : ∀ c, splitMat (A g) (d g) (Fin.natAdd r c) (Fin.natAdd r c) = d g c :=
      fun c => splitMat_natAdd _ _ c
    rw [RepresentationBoundsCohomology.eG_mulVec _ hoff]
    simp only [f, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he, hsub, hdiag]

end DecConj

section ConjFacts

variable {Γ : Type} {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem IsConjM.charpoly_eq {M M' : Γ → Matrix n n K} (h : IsConjM M M') (g : Γ) :
    (M' g).charpoly = (M g).charpoly := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  let u : (Matrix n n K)ˣ := ⟨P, Q, h1, h2⟩
  have hQ : Q = (u.val)⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  have : M' g = u.val * M g * (u.val)⁻¹ := by
    rw [← hQ]
    show M' g = P * M g * Q
    rw [h3, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [this, Matrix.charpoly_units_conj]

theorem IsConjM.congr_right {M M₁ M₂ : Γ → Matrix n n K} (h : IsConjM M M₁) (hM : ∀ g, M₁ g = M₂ g) :
    IsConjM M M₂ := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => by rw [h3, hM]⟩

theorem IsConjM.apply_eq {M M' : Γ → Matrix n n K} (h : IsConjM M M') (g : Γ) :
    ∃ P Q : Matrix n n K, P * Q = 1 ∧ Q * P = 1 ∧ M' g = P * M g * Q := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, by rw [h3, Matrix.mul_assoc, h1, Matrix.mul_one]⟩

theorem IsConjM.eigen {M M' : Γ → Matrix n n K} (h : IsConjM M M') (c : Γ → K)
    (hu : ∃ u : n → K, u ≠ 0 ∧ ∀ g, (M' g).mulVec u = c g • u) :
    ∃ u : n → K, u ≠ 0 ∧ ∀ g, (M g).mulVec u = c g • u := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h.symm
  obtain ⟨u, hu0, hu⟩ := hu
  refine ⟨P.mulVec u, fun h0 => hu0 ?_, fun g => ?_⟩
  · have := congrArg (Matrix.mulVec Q) h0
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  · rw [Matrix.mulVec_mulVec, ← h3, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul]

end ConjFacts

section MapFacts

variable {Γ : Type} [Group Γ] {O K : Type} [CommRing O] [CommRing K] {k : ℕ} (f : O →+* K)

theorem map_twistM (M : Γ →* Matrix (Fin k) (Fin k) O) (χ : Γ →* Oˣ) (g : Γ) :
    (twistM M χ g).map f = f ((χ g : Oˣ) : O) • (M g).map f := by
  ext a b
  simp [twistM]

theorem map_dualM (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) :
    (dualM M g).map f = ((M g⁻¹).map f).transpose := by
  ext a b
  simp [dualM]

theorem conj_twistM {M M' : Γ →* Matrix (Fin k) (Fin k) O} (h : IsConjM (fun g => (M g).map f) (fun g => (M' g).map f))
    (χ : Γ →* Oˣ) : IsConjM (fun g => (twistM M χ g).map f) (fun g => (twistM M' χ g).map f) := by
  simp only [map_twistM]
  exact h.smul _

theorem conj_dualM {M M' : Γ →* Matrix (Fin k) (Fin k) O} (h : IsConjM (fun g => (M g).map f) (fun g => (M' g).map f)) :
    IsConjM (fun g => (dualM M g).map f) (fun g => (dualM M' g).map f) := by
  simp only [map_dualM]
  exact h.dual

end MapFacts

section RecC

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem conjK_self (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    IsConjM (fun g => (rO D.nd i r π g).map (toK D.nd i))
      (fun g => (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i)) := by
  obtain ⟨e, he⟩ := hd
  have h := conj_of_decomp (r := D.R.r) (t := D.R.t) (fun g => (rO D.nd i r π g).map (toK D.nd i))
    (fun g => (rhoO D.nd i ρ π g).map (toK D.nd i))
    (fun g c => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) e he
  refine h.congr_right (fun g => ?_)
  have e1 := rO_rN_self i r ρ π g
  have e2 := splitMat_map (toK D.nd i) (rhoO D.nd i ρ π g) (chiVec D.R.t (D.nd.chi i) g)
  exact ((congrArg (fun A => Matrix.map A (toK D.nd i)) e1).trans e2).symm

theorem conjK (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (x : D.nd.X i) :
    IsConjM (fun g => (rO D.nd i r x g).map (toK D.nd i))
      (fun g => (rO D.nd i (rN i r ρ π) x g).map (toK D.nd i)) := by
  by_cases hx : x = π
  · subst hx
    exact conjK_self i r ρ x hd
  · rw [rO_rN_ne i r ρ π hx]
    exact IsConjM.refl _

theorem toK_inj : Function.Injective (toK D.nd i) := IsFractionRing.injective (D.nd.O i) (KK D.nd i)

theorem charpoly_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (x : D.nd.X i) (g : GE D.nd) :
    (rO D.nd i (rN i r ρ π) x g).charpoly = (rO D.nd i r x g).charpoly := by
  apply Polynomial.map_injective _ (toK_inj i)
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
  exact (conjK i r ρ π hd x).charpoly_eq g

end RecC

section RecT

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem IsConjM.congr' {Γ K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
    {M₁ M₂ N₁ N₂ : Γ → Matrix n n K} (h : IsConjM M₁ M₂) (e1 : ∀ g, M₁ g = N₁ g) (e2 : ∀ g, M₂ g = N₂ g) :
    IsConjM N₁ N₂ := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => by rw [← e1, ← e2, h3]⟩

theorem admG1_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG1 i r) : TruncatedSeriesCountingIdentities.admG1 i (rN i r ρ π) := by
  intro g k
  have e : (fun x : D.nd.X i => ((rO D.nd i (rN i r ρ π) x g).charpolyRev).coeff k) =
      (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff k) := by
    funext x
    rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, charpoly_rN i r ρ π hd x g]
  rw [e]
  exact h g k

theorem admG3_rN_of_absIrrDistinct (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG3 i r ρ π)
    (habs : ∀ x, AbsIrrDistinct (repK D.nd i (rN i r ρ π) x)) : TruncatedSeriesCountingIdentities.admG3 i (rN i r ρ π) ρ π := by
  obtain ⟨_, h2, h3⟩ := h
  refine ⟨habs, fun x g => ?_, h3⟩
  rw [← h2 x g]
  exact (Matrix.charpoly_map (rO D.nd i (rN i r ρ π) x g) (IsLocalRing.residue (D.nd.O i))).trans
    ((congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i))) (charpoly_rN i r ρ π hd x g)).trans
      (Matrix.charpoly_map (rO D.nd i r x g) (IsLocalRing.residue (D.nd.O i))).symm)

theorem admG4_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG4 i r) : TruncatedSeriesCountingIdentities.admG4 i (rN i r ρ π) := by
  intro x v h1 h2 h3 g hg
  have hr := h x v h1 h2 h3 g hg
  by_cases hx : x = π
  · subst hx
    obtain ⟨P, Q, hPQ, _, he⟩ := (conjK i r ρ x hd x).apply_eq g
    have h1' : rO D.nd i r x g = 1 := by
      show ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) = 1
      rw [hr]
      rfl
    simp only [h1', Matrix.map_one _ (map_zero (toK D.nd i)) (map_one (toK D.nd i)), Matrix.mul_one, hPQ] at he
    apply Units.ext
    rw [Units.val_one]
    change rO D.nd i (rN i r ρ x) x g = 1
    apply Matrix.map_injective (toK_inj i)
    show (rO D.nd i (rN i r ρ x) x g).map (toK D.nd i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (toK D.nd i)
    rw [he, Matrix.map_one _ (map_zero (toK D.nd i)) (map_one (toK D.nd i))]
  · rw [rN_ne i r ρ π hx]
    exact hr

theorem admG6_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG6 i r) : TruncatedSeriesCountingIdentities.admG6 i (rN i r ρ π) := by
  intro x hx
  exact h x ((conjK i r ρ π hd x).eigen (fun g => toK D.nd i ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i)) hx)

theorem semisimple_normalized (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admSS i r) : TruncatedSeriesCountingIdentities.admSS i (rN i r ρ π) := by
  intro x
  obtain ⟨e, he⟩ := exists_equiv_of_conj (M := mapM (toK D.nd i) (rO D.nd i r x))
    (M' := mapM (toK D.nd i) (rO D.nd i (rN i r ρ π) x)) (conjK i r ρ π hd x)
  exact isSS_congr e he (h x)

theorem eG_splitMat {K : Type} [CommRing K] {r t : ℕ} (A : Matrix (Fin r) (Fin r) K) (d : Fin t → K)
    (u : Fin (r + t) → K) :
    RepresentationBoundsCohomology.eG r t K ((splitMat A d).mulVec u) = (A.mulVec (RepresentationBoundsCohomology.eG r t K u).1, fun c => d c * (RepresentationBoundsCohomology.eG r t K u).2 c) := by
  have hsub : (splitMat A d).submatrix (Fin.castAdd t) (Fin.castAdd t) = A := by
    ext a b
    exact splitMat_castAdd _ _ a b
  have hdiag : ∀ c, splitMat A d (Fin.natAdd r c) (Fin.natAdd r c) = d c := fun c => splitMat_natAdd _ _ c
  rw [RepresentationBoundsCohomology.eG_mulVec _ (fun a b h => splitMat_off _ _ a b h)]
  simp only [hsub, hdiag]

theorem decomposes_normalized : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (rN i r ρ π) ρ π := by
  refine ⟨RepresentationBoundsCohomology.eG D.R.r D.R.t (KK D.nd i), fun g u => ?_⟩
  have e1 := rO_rN_self i r ρ π g
  have e2 := splitMat_map (toK D.nd i) (rhoO D.nd i ρ π g) (chiVec D.R.t (D.nd.chi i) g)
  have hM : (mapM (toK D.nd i) (rO D.nd i (rN i r ρ π) π)) g =
      splitMat (t := D.R.t) ((rhoO D.nd i ρ π g).map (toK D.nd i))
        (fun c => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) :=
    (congrArg (fun A => Matrix.map A (toK D.nd i)) e1).trans e2
  rw [hM]
  exact eG_splitMat _ _ u

theorem continuity_normalized (hc : RhoCont i ρ π) (h : TruncatedSeriesCountingIdentities.FamilyContinuous i r) : TruncatedSeriesCountingIdentities.FamilyContinuous i (rN i r ρ π) := by
  intro x
  by_cases hx : x = π
  · subst hx
    have hc2 : Continuous (fun g => splitMat (t := D.R.t) (rhoO D.nd i ρ x g) (chiVec D.R.t (D.nd.chi i) g)) := by
      unfold splitMat
      refine Continuous.matrix_reindex ?_ _ _
      refine Continuous.matrix_fromBlocks hc continuous_const continuous_const ?_
      refine Continuous.matrix_diagonal ?_
      exact continuous_pi fun c => D.nd.chi_cont i ((c : ℕ) + 1)
    exact hc2.congr (fun g => (rO_rN_self i r ρ x g).symm)
  · have e : (fun g => rO D.nd i (rN i r ρ π) x g) = fun g => rO D.nd i r x g := by
      rw [rO_rN_ne i r ρ π hx]
    rw [e]
    exact h x

section LocalC

variable {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locC_eq (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC C M g = ((M (decS D.nd w (Br.ι (D.nbr i w hw) g))).map (toK D.nd i)).map
      (C.inc.comp (Br.toLLK (D.nbr i w hw))) := by
  ext a b
  simp only [Matrix.map_apply, RingHom.comp_apply, Br.toLLK_alg]
  rfl

theorem conj_locC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} {M M' : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)}
    (h : IsConjM (fun g => (M g).map (toK D.nd i)) (fun g => (M' g).map (toK D.nd i))) :
    IsConjM ⇑(TruncatedSeriesCountingIdentities.locC C M) ⇑(TruncatedSeriesCountingIdentities.locC C M') :=
  ((h.map (C.inc.comp (Br.toLLK (D.nbr i w hw)))).comp
    (fun g => decS D.nd w (Br.ι (D.nbr i w hw) g))).congr' (fun g => (locC_eq i C M g).symm)
    (fun g => (locC_eq i C M' g).symm)

end LocalC

section JD

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {k : ℕ}

theorem jd {N N' : G →* Matrix (Fin k) (Fin k) LL} (h : IsConjM ⇑N ⇑N') :
    (IsCrys PD (matRep N) → IsCrys PD (matRep N')) ∧
    (∀ τ a, multV PD (matRep N) τ a = multV PD (matRep N') τ a) ∧
    (∀ τ a, IsJumpV PD (matRep N) τ a ↔ IsJumpV PD (matRep N') τ a) := by
  obtain ⟨e, he⟩ := exists_equiv_of_conj h
  exact ⟨isCrys_congr PD e he, multV_congr PD e he, isJumpV_congr PD e he⟩

theorem conj_twLL {N N' : G →* Matrix (Fin k) (Fin k) LL} (h : IsConjM ⇑N ⇑N') (χ : G →* LLˣ) :
    IsConjM ⇑(twistM N χ) ⇑(twistM N' χ) :=
  h.smul (fun g => ((χ g : LLˣ) : LL))

end JD

theorem admG2_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG2 i r ρ π) : TruncatedSeriesCountingIdentities.admG2 i (rN i r ρ π) ρ π := by
  intro w hw C
  obtain ⟨⟨g1, g2, g3, g4, g5, g6, g7⟩, g8⟩ := h w hw C
  have hc : ∀ x, IsConjM ⇑(TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) ⇑(TruncatedSeriesCountingIdentities.locC C (rO D.nd i (rN i r ρ π) x)) :=
    fun x => conj_locC i C (conjK i r ρ π hd x)
  have ht := fun x => conj_twLL (hc x) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹
  refine ⟨⟨fun x => (jd _ (hc x)).1 (g1 x), fun τ x y a => ?_, fun τ x a => ?_, g4, fun τ x => ?_, g6, g7⟩,
    fun x => (jd _ (ht x)).1 (g8 x)⟩
  · rw [← (jd _ (ht x)).2.1, ← (jd _ (ht y)).2.1]
    exact g2 τ x y a
  · rw [← (jd _ (ht x)).2.1]
    exact g3 τ x a
  · rw [← (jd _ (ht x)).2.2]
    exact g5 τ x

theorem trivial_bound_normalized (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (cB : ℕ) (h : TruncatedSeriesCountingIdentities.admTB i r π cB) :
    TruncatedSeriesCountingIdentities.admTB i (rN i r ρ π) π cB := by
  intro w hw C hC
  have ht : IsConjM ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)) ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (rN i r ρ π) π)) :=
    conj_locC i C (conj_twistM _ (conjK i r ρ π hd π) _)
  have hset : (fun τ => {a | IsJumpV (Br.PD D.loc D.nbr i w hw)
      (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (rN i r ρ π) π))) τ a}) =
      (fun τ => {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a}) :=
    funext fun τ => Set.ext fun a => ((jd _ ht).2.2 τ a).symm
  have := h w hw C hC
  rw [← hset] at this
  exact this

theorem row_normalized (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (h : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow) :
    TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (rN i r ρ π) ρ π dc lenRow := by
  intro w hw hrow C hC V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hm2 V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hs1 F hF
  exact h w hw hrow C hC V2 ρ2 T2 hc2 hm2 V1 ρ1 T1 hc1
    (isSubOfSums_of_conj ρ1 _ _ (fun x => conj_locC i C (conj_twistM _ (conj_dualM _ (conjK i r ρ π hd x)) _)) hs1)
    F hF

theorem lift_normalized (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (h : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e') :
    TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i (rN i r ρ π) dc e' := by
  intro w hw hcol C hC V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF
  have hcx := fun x => conj_locC i C (conj_twistM _ (conjK i r ρ π hd x) ((chiU D.nd i 1)⁻¹))
  exact h w hw hcol C hC V1 ρ1 L1 hc1 (isSubquotOfSums_of_conj ρ1 _ _ hcx hs1)
    V2 ρ2 L2 hc2 (isSubquotOfSums_of_conj ρ2 _ _ hcx hs2) F hF

end RecT

section G5gen

variable {O K : Type} [CommRing O] [CommRing K] [Algebra O K] {n : Type} [Fintype n] [DecidableEq n]

theorem map_smul_one' (c : O) : (c • (1 : Matrix n n O)).map (algebraMap O K) = algebraMap O K c • (1 : Matrix n n K) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem map_quad (A : Matrix n n O) (c : O) :
    ((A - 1) * (A - c • 1)).map (algebraMap O K) =
      (A.map (algebraMap O K) - 1) * (A.map (algebraMap O K) - algebraMap O K c • 1) := by
  rw [Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), map_smul_one']

def conjAlg (P Q : Matrix n n K) (h1 : P * Q = 1) (h2 : Q * P = 1) : Matrix n n K →ₐ[O] Matrix n n K where
  toFun X := P * X * Q
  map_one' := by rw [Matrix.mul_one, h1]
  map_mul' X Y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, h2, Matrix.one_mul]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    show P * algebraMap O (Matrix n n K) c * Q = algebraMap O (Matrix n n K) c
    rw [← Algebra.commutes c P, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conjAlg_apply (P Q : Matrix n n K) (h1 : P * Q = 1) (h2 : Q * P = 1) (X : Matrix n n K) :
    conjAlg (O := O) P Q h1 h2 X = P * X * Q := rfl

theorem aeval_map (A : Matrix n n O) (p : Polynomial O) :
    (Polynomial.aeval A p).map (algebraMap O K) = Polynomial.aeval (A.map (algebraMap O K)) p := by
  have := Polynomial.aeval_algHom_apply ((Algebra.ofId O K).mapMatrix (m := n)) A p
  exact (this.trans (AlgHom.mapMatrix_apply _ _)).symm

theorem conj_smul_one (P Q : Matrix n n K) (h1 : P * Q = 1) (c : K) : P * (c • (1 : Matrix n n K)) * Q = c • 1 := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]

theorem conj_sub_smul (P Q : Matrix n n K) (h1 : P * Q = 1) (X : Matrix n n K) (c : K) :
    P * X * Q - c • 1 = P * (X - c • 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, conj_smul_one P Q h1]

theorem conj_sub_one (P Q : Matrix n n K) (h1 : P * Q = 1) (X : Matrix n n K) :
    P * X * Q - 1 = P * (X - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]

end G5gen

section G5rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem admG5_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG5 i r) : TruncatedSeriesCountingIdentities.admG5 i (rN i r ρ π) := by
  intro w hw
  obtain ⟨hA, hB⟩ := h w hw
  have hK := conjK_self i r ρ π hd
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := hK
  have hA' : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q :=
    fun g => by rw [hconj, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  refine ⟨fun hc x => ?_, fun hk hS hT => ?_⟩
  · obtain ⟨h1, Pm, hPm⟩ := hA hc x
    by_cases hx : x = π
    · subst hx
      let uP : GL (Fin D.R.nV) (KK D.nd i) := ⟨P, Q, hPQ, hQP⟩
      refine ⟨fun γ hγ => ?_, uP * Pm, fun γ hγ => ?_⟩
      · apply Matrix.map_injective (toK_inj i)
        show (((rO D.nd i (rN i r ρ x) x γ) - 1) * ((rO D.nd i (rN i r ρ x) x γ) - chi1 D.nd i γ • 1)).map
          (algebraMap (D.nd.O i) (KK D.nd i)) = (0 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (toK D.nd i)
        rw [map_quad, Matrix.map_zero _ (map_zero _)]
        have e1 : (rO D.nd i (rN i r ρ x) x γ).map (algebraMap (D.nd.O i) (KK D.nd i)) =
            P * (rO D.nd i r x γ).map (toK D.nd i) * Q := hA' γ
        rw [e1, conj_sub_one P Q hPQ, conj_sub_smul P Q hPQ]
        have e2 := congrArg (fun M => M.map (algebraMap (D.nd.O i) (KK D.nd i))) (h1 γ hγ)
        beta_reduce at e2
        rw [map_quad, Matrix.map_zero _ (map_zero _)] at e2
        have e3 : P * ((rO D.nd i r x γ).map (toK D.nd i) - 1) * Q *
            (P * ((rO D.nd i r x γ).map (toK D.nd i) - algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ) • 1) * Q) =
            P * (((rO D.nd i r x γ).map (toK D.nd i) - 1) *
              ((rO D.nd i r x γ).map (toK D.nd i) - algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ) • 1)) * Q := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
        rw [e3]
        erw [e2]
        rw [Matrix.mul_zero, Matrix.zero_mul]
      · have key : (((uP * Pm)⁻¹ * mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (rN i r ρ x x) γ * (uP * Pm) :
            GL (Fin D.R.nV) (KK D.nd i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
            ((Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r x) γ * Pm : GL (Fin D.R.nV) (KK D.nd i)) :
              Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
          simp only [Units.val_mul, mul_inv_rev]
          have e1 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (rN i r ρ x x) γ : GL (Fin D.R.nV) (KK D.nd i)) :
              Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
              P * ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r x) γ : GL (Fin D.R.nV) (KK D.nd i)) :
                Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * Q := hA' γ
          have e2 : ((uP⁻¹ : GL (Fin D.R.nV) (KK D.nd i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = Q := rfl
          have e3 : ((uP : GL (Fin D.R.nV) (KK D.nd i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = P := rfl
          rw [e1, e2, e3]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul, ← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
        rw [key]
        exact hPm γ hγ
    · rw [rN_ne i r ρ π hx]
      exact ⟨h1, Pm, hPm⟩
  · obtain ⟨Pp, hu, hP⟩ := hB hk hS hT
    refine ⟨Pp, hu, fun x γ hγ => ?_⟩
    have h0 := hP x γ hγ
    by_cases hx : x = π
    · subst hx
      set p := Pp.map ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) x).comp (D.nd.T i).val.toRingHom) with hp
      apply Matrix.map_injective (toK_inj i)
      show (Polynomial.aeval (rO D.nd i (rN i r ρ x) x (D.nd.gam0 i w)) p *
          (rO D.nd i (rN i r ρ x) x γ - chi1 D.nd i γ • 1)).map (algebraMap (D.nd.O i) (KK D.nd i)) =
        (0 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (toK D.nd i)
      rw [Matrix.map_mul, Matrix.map_sub _ (map_sub _), map_smul_one', aeval_map, Matrix.map_zero _ (map_zero _)]
      have e1 : ∀ g, (rO D.nd i (rN i r ρ x) x g).map (algebraMap (D.nd.O i) (KK D.nd i)) =
          conjAlg (O := D.nd.O i) P Q hPQ hQP ((rO D.nd i r x g).map (toK D.nd i)) := hA'
      rw [e1, e1, Polynomial.aeval_algHom_apply, conjAlg_apply, conjAlg_apply, conj_sub_smul P Q hPQ]
      have e2 := congrArg (fun M => M.map (algebraMap (D.nd.O i) (KK D.nd i))) h0
      beta_reduce at e2
      rw [Matrix.map_mul, Matrix.map_sub _ (map_sub _), map_smul_one', aeval_map, Matrix.map_zero _ (map_zero _)] at e2
      have e3 : ∀ X Y : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i), P * X * Q * (P * Y * Q) = P * (X * Y) * Q := by
        intro X Y
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
      rw [e3]
      erw [e2]
      rw [Matrix.mul_zero, Matrix.zero_mul]
    · rw [rN_ne i r ρ π hx]
      exact h0

end G5rec

section Final

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem abs_irreducible_normalized (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : ∀ x, AbsIrrDistinct (repK D.nd i r x)) (x : D.nd.X i) :
    AbsIrrDistinct (repK D.nd i (rN i r ρ π) x) := by
  obtain ⟨e, he⟩ := exists_equiv_of_conj (M := mapM (toK D.nd i) (rO D.nd i r x))
    (M' := mapM (toK D.nd i) (rO D.nd i (rN i r ρ π) x)) (conjK i r ρ π hd x)
  exact absIrrDistinct_congr e he (h x)

theorem admitted_items_normalized (hRho : RhoCont i ρ π) (hA : AdmR i r ρ π) : AdmR i (rN i r ρ π) ρ π := by
  obtain ⟨g1, g2, g3, g4, g5, g5x, g6, bk, bka, ct, ss, dcm, ep, tie, sh, fo, h2, fin, cft⟩ := hA
  exact ⟨admG1_rN i r ρ π dcm g1, admG2_rN i r ρ π dcm g2, admG3_rN_of_absIrrDistinct i r ρ π dcm g3 (abs_irreducible_normalized i r ρ π dcm g3.1),
    admG4_rN i r ρ π dcm g4, admG5_rN i r ρ π dcm g5, g5x, admG6_rN i r ρ π dcm g6, bk, bka,
    continuity_normalized i r ρ π hRho ct, semisimple_normalized i r ρ π dcm ss, decomposes_normalized i r ρ π, ep, tie, sh, fo, h2, fin, cft⟩

theorem globalIndexTheoremPlaces_of_rN (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) (hRho : RhoCont i ρ π)
    (H : AdmR i (rN i r ρ π) ρ π → LargeLevelLemmas.GlobalIndexTheoremPlaces i (rN i r ρ π) ρ π dc lenRow e' cB)
    (hA : AdmR i r ρ π) : LargeLevelLemmas.GlobalIndexTheoremPlaces i r ρ π dc lenRow e' cB := by
  have dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π := hA.2.2.2.2.2.2.2.2.2.2.2.1
  intro hR hL hT
  exact H (admitted_items_normalized i r ρ π hRho hA)
    (row_normalized i r ρ π dcm dc lenRow hR) (lift_normalized i r ρ π dcm dc e' hL) (trivial_bound_normalized i r ρ π dcm cB hT)

theorem globalIndexTheoremPlaces_of_rN_adm (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) (hRho : RhoCont i ρ π)
    (H : AdmR i (rN i r ρ π) ρ π → LargeLevelLemmas.GlobalIndexTheoremPlaces i (rN i r ρ π) ρ π dc lenRow e' cB)
    (hA : LargeLevelLemmas.admitted i r ρ π) : LargeLevelLemmas.GlobalIndexTheoremPlaces i r ρ π dc lenRow e' cB :=
  globalIndexTheoremPlaces_of_rN i r ρ π dc lenRow e' cB hRho H (admitted_items_of_adm i r ρ π hA)

end Final

end Formalism.MainNotions.N.K.Norm
