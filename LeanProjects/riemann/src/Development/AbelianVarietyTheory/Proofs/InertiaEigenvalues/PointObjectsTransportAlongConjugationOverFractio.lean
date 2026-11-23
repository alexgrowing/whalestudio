import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDeterminant
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

noncomputable section

namespace GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field

section General

variable {A K : Type} [CommRing A] [CommRing K] {n : ℕ}

def Cj (f : A →+* K) (P : GL (Fin n) K) (a a' : Matrix (Fin n) (Fin n) A) : Prop :=
  (P : Matrix (Fin n) (Fin n) K) * a.map f = a'.map f * (P : Matrix (Fin n) (Fin n) K)

variable {f : A →+* K} {P : GL (Fin n) K} {a a' b b' : Matrix (Fin n) (Fin n) A}

theorem Cj.eq_conj (h : Cj f P a a') :
    a'.map f = (P : Matrix (Fin n) (Fin n) K) * a.map f * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [show (P : Matrix (Fin n) (Fin n) K) * a.map f = _ from h, mul_assoc, Units.mul_inv, mul_one]

theorem Cj.inv_mul (h : Cj f P a a') :
    ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * a'.map f =
      a.map f * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [h.eq_conj, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]

theorem Cj.unique (hf : Function.Injective f) (h : Cj f P a a') (h' : Cj f P a b') : a' = b' := by
  apply Matrix.map_injective hf
  show a'.map f = b'.map f
  rw [h.eq_conj, h'.eq_conj]

theorem Cj.mul (h : Cj f P a a') (h' : Cj f P b b') : Cj f P (a * b) (a' * b') := by
  unfold Cj at *
  rw [Matrix.map_mul, Matrix.map_mul, ← mul_assoc, h, mul_assoc, h', mul_assoc]

theorem Cj.one : Cj f P 1 1 := by
  unfold Cj
  rw [Matrix.map_one _ f.map_zero f.map_one, mul_one, one_mul]

theorem Cj.zero : Cj f P 0 0 := by
  unfold Cj
  rw [Matrix.map_zero _ f.map_zero, mul_zero, zero_mul]

theorem Cj.sub (h : Cj f P a a') (h' : Cj f P b b') : Cj f P (a - b) (a' - b') := by
  unfold Cj at *
  rw [Matrix.map_sub _ f.map_sub, Matrix.map_sub _ f.map_sub, mul_sub, sub_mul, h, h']

theorem map_smul_eq (c : A) (a : Matrix (Fin n) (Fin n) A) : (c • a).map f = f c • a.map f := by
  ext i j; simp

theorem Cj.smul (c : A) (h : Cj f P a a') : Cj f P (c • a) (c • a') := by
  unfold Cj at *
  rw [map_smul_eq, map_smul_eq, Matrix.mul_smul, Matrix.smul_mul, h]

theorem Cj.list_prod {ι : Type} (l : List ι) (u u' : ι → Matrix (Fin n) (Fin n) A)
    (h : ∀ c, Cj f P (u c) (u' c)) : Cj f P (l.map u).prod (l.map u').prod := by
  induction l with
  | nil => exact Cj.one
  | cons c l ih => simpa using (h c).mul ih

theorem Cj.rank (h : Cj f P a a') : (a'.map f).rank = (a.map f).rank := by
  rw [h.eq_conj, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units _),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units _)]

theorem Cj.det (hf : Function.Injective f) (h : Cj f P a a') : a'.det = a.det := by
  apply hf
  rw [RingHom.map_det, RingHom.map_det]
  have h1 := congrArg Matrix.det h
  unfold Cj at h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at h1
  exact ((Matrix.isUnits_det_units P).mul_left_injective h1).symm

theorem Cj.add (h : Cj f P a a') (h' : Cj f P b b') : Cj f P (a + b) (a' + b') := by
  unfold Cj at *
  rw [Matrix.map_add _ f.map_add, Matrix.map_add _ f.map_add, mul_add, add_mul, h, h']

theorem Cj.toPoly (h : Cj f P a a') :
    Cj (Polynomial.mapRingHom f) (Matrix.GeneralLinearGroup.map (Polynomial.C (R := K)) P)
      (a.map (Polynomial.C (R := A))) (a'.map (Polynomial.C (R := A))) := by
  unfold Cj at *
  have e : ∀ m : Matrix (Fin n) (Fin n) A, (m.map (Polynomial.C (R := A))).map (Polynomial.mapRingHom f) =
      (m.map f).map (Polynomial.C (R := K)) := by
    intro m; ext i j; simp
  have e2 : ((Matrix.GeneralLinearGroup.map (Polynomial.C (R := K)) P : GL (Fin n) (Polynomial K)) :
      Matrix (Fin n) (Fin n) (Polynomial K)) = (P : Matrix (Fin n) (Fin n) K).map (Polynomial.C (R := K)) := rfl
  rw [e, e, e2, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem Cj.blockDet (hf : Function.Injective f) (h : Cj f P a a') (h' : Cj f P b b') :
    Matrix.det ((Polynomial.X : Polynomial A) • a'.map (Polynomial.C (R := A)) -
      b'.map (Polynomial.C (R := A)) + 1 - a'.map (Polynomial.C (R := A))) =
    Matrix.det ((Polynomial.X : Polynomial A) • a.map (Polynomial.C (R := A)) -
      b.map (Polynomial.C (R := A)) + 1 - a.map (Polynomial.C (R := A))) :=
  Cj.det (f := Polynomial.mapRingHom f) (Polynomial.map_injective f hf)
    ((((h.toPoly.smul _).sub h'.toPoly).add Cj.one).sub h.toPoly)

theorem Cj.sum {ι : Type} (s : Finset ι) (u u' : ι → Matrix (Fin n) (Fin n) A)
    (h : ∀ c, Cj f P (u c) (u' c)) : Cj f P (∑ c ∈ s, u c) (∑ c ∈ s, u' c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cj.zero
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc]; exact (h c).add ih

theorem exists_cj_of_forall (h : ∀ b, ∃ b', Cj f P b b') (a' : Matrix (Fin n) (Fin n) A) :
    ∃ a, Cj f P a a' := by
  have key : ∀ i x y j, ∃ c : A, f c = (P : Matrix (Fin n) (Fin n) K) i x *
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) y j := by
    intro i x y j
    obtain ⟨b', hb⟩ := h (Matrix.single x y 1)
    refine ⟨b' i j, ?_⟩
    have := congrFun (congrFun hb.eq_conj i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.map_single _ _ _ f, map_one, Matrix.mul_apply, Finset.sum_eq_single y]
    · rw [Matrix.mul_single_apply_same, mul_one]
    · intro z _ hz
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hz, zero_mul]
    · simp
  choose c hc using key
  refine ⟨Matrix.of fun y x => ∑ j, ∑ i, c i x y j * a' j i, ?_⟩
  have : (Matrix.map (Matrix.of fun y x => ∑ j, ∑ i, c i x y j * a' j i) f : Matrix (Fin n) (Fin n) K) =
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (a'.map f * (P : Matrix (Fin n) (Fin n) K)) := by
    ext y x
    simp only [Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, hc, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  unfold Cj
  rw [this, ← mul_assoc, Units.mul_inv, one_mul]

def glEquiv (P : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinearMap (Matrix.mulVecLin (P : Matrix (Fin n) (Fin n) K))
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])

variable {r t : ℕ}

def Act (f : A →+* K) (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (M : Matrix (Fin n) (Fin n) A)
    (B : Matrix (Fin r) (Fin r) A) (d : Fin t → A) : Prop :=
  ∀ u, e ((M.map f).mulVec u) = ((B.map f).mulVec (e u).1, fun c => f (d c) * (e u).2 c)

def newE (P : GL (Fin n) K) (Q : GL (Fin r) K) (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) :
    (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)) :=
  ((glEquiv P⁻¹).trans e).trans ((glEquiv Q).prodCongr (LinearEquiv.refl K _))

theorem newE_apply (P : GL (Fin n) K) (Q : GL (Fin r) K) (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)))
    (u : Fin n → K) : newE P Q e u =
      ((Q : Matrix (Fin r) (Fin r) K).mulVec (e (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec u)).1,
        (e (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec u)).2) := rfl

variable {e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))}

theorem Act.conj {Q : GL (Fin r) K} {B B' : Matrix (Fin r) (Fin r) A} {d : Fin t → A}
    (h : Act f e a B d) (ha : Cj f P a a') (hB : Cj f Q B B') : Act f (newE P Q e) a' B' d := by
  intro u
  rw [newE_apply, newE_apply, Matrix.mulVec_mulVec, ha.inv_mul, ← Matrix.mulVec_mulVec, h]
  simp only [Matrix.mulVec_mulVec]
  rw [show (Q : Matrix (Fin r) (Fin r) K) * B.map f = _ from hB]

theorem Act.unique (hf : Function.Injective f) {B B' : Matrix (Fin r) (Fin r) A} {d d' : Fin t → A}
    (h : Act f e a B d) (h' : Act f e a B' d') : B = B' := by
  apply Matrix.map_injective hf
  show B.map f = B'.map f
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have := congrArg Prod.fst ((h (e.symm (Pi.single j 1, 0))).symm.trans (h' _))
  simpa using this

theorem Act.sum {ι : Type} (s : Finset ι) (c : ι → A) (M : ι → Matrix (Fin n) (Fin n) A)
    (B : ι → Matrix (Fin r) (Fin r) A) (d : ι → Fin t → A) (h : ∀ k, Act f e (M k) (B k) (d k)) :
    Act f e (∑ k ∈ s, c k • M k) (∑ k ∈ s, c k • B k) (fun j => ∑ k ∈ s, c k * d k j) := by
  classical
  intro u
  induction s using Finset.induction_on with
  | empty => ext <;> simp
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    rw [Matrix.map_add _ f.map_add, Matrix.map_add _ f.map_add, Matrix.add_mulVec, Matrix.add_mulVec, map_add, ih,
      map_smul_eq, map_smul_eq, Matrix.smul_mulVec, Matrix.smul_mulVec, map_smul, h k u]
    refine Prod.ext rfl ?_
    funext j
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring

theorem act_zero_iff {d : Fin t → A} : Act f e a 0 d ↔
    ∀ u, e ((a.map f).mulVec u) = (0, fun c => f (d c) * (e u).2 c) := by
  unfold Act
  rw [Matrix.map_zero _ f.map_zero]
  simp only [Matrix.zero_mulVec]

end General

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem exists_act {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i)) (rep : X' → (GE N →* MatN N i)) (y : X')
    (e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)))
    (B : GE N → Matrix (Fin R.r) (Fin R.r) (N.O i)) (d : GE N → Fin R.t → N.O i)
    (h : ∀ g, Act (toK N i) e (rep y g) (B g) (d g)) (a : X' → MatN N i) (ha : InSpan N i T' rep a) :
    ∃ (m : ℕ) (c : Fin m → N.O i) (g : Fin m → GE N) (δ : Fin R.t → N.O i),
      Act (toK N i) e (a y) (∑ k, c k • B (g k)) δ := by
  obtain ⟨m, f, g, -, rfl⟩ := ha
  refine ⟨m, fun k => f k y, g, fun j => ∑ k, f k y * d (g k) j, ?_⟩
  rw [Finset.sum_apply]
  exact Act.sum Finset.univ (fun k => f k y) _ _ _ fun k => h (g k)

end Record

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), (∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)))) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) → ∀ S : IdempotentChoiceData N i, GoodCongruenceObjects N r ρ π S → ∃ S' : IdempotentChoiceData N i, S'.g0 = S.g0 ∧ GoodCongruenceObjects N r' ρ' π S' := by
  intro R H what₂ N i r r' ρ ρ' π hP hQ S hS
  classical
  choose P hP using hP
  obtain ⟨Q, hQ⟩ := hQ
  have hf : Function.Injective (toK N i) := IsFractionRing.injective _ _
  obtain ⟨⟨hB, h1, hBB, h11, hB1, h1B, rkB, rk1⟩, hdec, hact, honto, hg1, hg2, ⟨hX, hBX, hXB, hXe⟩, hT, hroot,
    ⟨hπ, hrr⟩, ⟨rkE, hEE, hEe, hv⟩, hL⟩ := hS
  have sp := (GlobalTheory.Proof.BlockDeterminant.main N i r r' P hP (N.X i) id (N.T i)).1
  obtain ⟨eB, hB', cB⟩ := sp S.eB hB
  obtain ⟨e1, h1', c1⟩ := sp S.e1 h1
  obtain ⟨X0, hX', cX⟩ := sp S.X0 hX
  replace cB : ∀ x, Cj (toK N i) (P x) (S.eB x) (eB x) := cB
  replace c1 : ∀ x, Cj (toK N i) (P x) (S.e1 x) (e1 x) := c1
  replace cX : ∀ x, Cj (toK N i) (P x) (S.X0 x) (X0 x) := cX
  obtain ⟨sp', hL'⟩ := GlobalTheory.Proof.BlockDeterminant.main N i r r' P hP S.X' S.p S.T'
  have hdec0 : ∀ g, Act (toK N i) S.e (rO N i r π g) (rhoO N i ρ π g)
      (fun c : Fin R.t => ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i)) := hdec
  have hdec' : ∀ g, Act (toK N i) (newE (P π) Q S.e) (rO N i r' π g) (rhoO N i ρ' π g)
      (fun c : Fin R.t => ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i)) :=
    fun g => (hdec0 g).conj (hP π g) (hQ g)
  have hact0 : ∀ a, InR' N r S a → Act (toK N i) S.e (a S.π') (S.ψρ a) (fun c => S.ψχ c a) := hact
  have ex : ∀ a : S.X' → MatN N i, ∃ (B : Matrix (Fin R.r) (Fin R.r) (N.O i)) (δ : Fin R.t → N.O i),
      InSpan N i S.T' (fun y => rO N i r' (S.p y)) a → Act (toK N i) (newE (P π) Q S.e) (a S.π') B δ := by
    intro a
    by_cases ha : InSpan N i S.T' (fun y => rO N i r' (S.p y)) a
    · obtain ⟨m, c, g, δ, h⟩ := exists_act N i S.T' _ S.π' (newE (P π) Q S.e) _ _
        (fun g => by rw [hπ]; exact hdec' g) a ha
      exact ⟨_, δ, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h ha⟩
  choose ψρ ψχ hψ using ex
  have hint : ∀ b, ∃ b', Cj (toK N i) Q b b' := by
    intro b
    obtain ⟨a, ha, rfl⟩ := honto b
    obtain ⟨m, c, g, δ, h⟩ := exists_act N i S.T' _ S.π' S.e _ _
      (fun g => by rw [hπ]; exact hdec0 g) a ha
    rw [(hact0 a ha).unique hf h]
    exact ⟨_, Cj.sum _ _ _ fun k => Cj.smul (c k) (hQ (g k))⟩
  let S' : IdempotentChoiceData N i :=
    { eB := eB, e1 := e1, g0 := S.g0, X0 := X0, X' := S.X', p := S.p, T' := S.T', rr := S.rr, π' := S.π',
      e := newE (P π) Q S.e, ψρ := ψρ, ψχ := fun c a => ψχ a c }
  have cE : ∀ y, Cj (toK N i) (P (S.p y)) (Eel N S y) (Eel N S' y) := fun y =>
    Cj.list_prod _ _ _ fun c => (cX _).sub ((cB _).smul _)
  have rel : ∀ {a a' b b' c c' : N.X i → MatN N i}, (∀ x, Cj (toK N i) (P x) (a x) (a' x)) →
      (∀ x, Cj (toK N i) (P x) (b x) (b' x)) → (∀ x, Cj (toK N i) (P x) (c x) (c' x)) → a * b = c →
      a' * b' = c' := by
    intro a a' b b' c c' ha hb hc h
    funext x
    have h2 := (ha x).mul (hb x)
    rw [show a x * b x = c x from congrFun h x] at h2
    exact h2.unique hf (hc x)
  have c0 : ∀ x, Cj (toK N i) (P x) ((0 : N.X i → MatN N i) x) ((0 : N.X i → MatN N i) x) := fun _ => Cj.zero
  refine ⟨S', rfl, ⟨hB', h1', rel cB cB cB hBB, rel c1 c1 c1 h11, rel cB c1 c0 hB1, rel c1 cB c0 h1B,
    fun x => (cB x).rank.trans (rkB x), fun x => (c1 x).rank.trans (rk1 x)⟩, hdec', hψ, ?_, hg1, hg2,
    ⟨hX', rel cB cX cX hBX, rel cX cB cX hXB, ?_⟩, hT, fun y => ?_, ⟨hπ, hrr⟩,
    ⟨fun y => (cE y).rank.trans (rkE y), fun y => ?_, ?_, hv⟩, hL' hL⟩
  · intro A
    obtain ⟨b, hb⟩ := exists_cj_of_forall hint A
    obtain ⟨a, ha, rfl⟩ := honto b
    obtain ⟨a', ha', ca⟩ := sp' a ha
    refine ⟨a', ha', ?_⟩
    have ca' : Cj (toK N i) (P π) (a S.π') (a' S.π') := by
      have := ca S.π'
      rwa [hπ] at this
    exact (hψ a' ha').unique hf ((hact0 a ha).conj ca' hb)
  · exact act_zero_iff.1 ((act_zero_iff.2 hXe).conj (cX π) Cj.zero)
  · exact (hroot y).trans (Cj.blockDet hf (cB _) (cX _)).symm
  · have h2 := (cE y).mul (cE y)
    rw [hEE y] at h2
    exact h2.unique hf ((cE y).smul _)
  · have cE' : Cj (toK N i) (P π) (Eel N S S.π') (Eel N S' S.π') := by
      have := cE S.π'
      rwa [hπ] at this
    have h0 : Act (toK N i) S.e (Eel N S S.π') (0 : Matrix (Fin R.r) (Fin R.r) (N.O i))
        (fun c : Fin R.t => if (c : ℕ) = 0 then del51 N S S.π' else 0) := by
      refine act_zero_iff.2 fun u => (hEe u).trans ?_
      congr 1
      funext c
      split_ifs <;> simp
    intro u
    refine (act_zero_iff.1 (h0.conj (Q := Q) cE' Cj.zero) u).trans ?_
    congr 1
    funext c
    split_ifs
    · rfl
    · simp

end GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field

end
