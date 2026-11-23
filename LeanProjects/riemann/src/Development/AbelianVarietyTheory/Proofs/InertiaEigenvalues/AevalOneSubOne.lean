import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSpanMatrixEqValDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubgroupIsUnit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwistDet

def polyMat {O S : Type} [CommRing O] [CommRing S] {n : ℕ} (r : ℕ) (t : ℕ → Matrix (Fin n) (Fin n) O) (f : O →+* S)
    (y : S) : Matrix (Fin n) (Fin n) S :=
  1 + ∑ m ∈ Finset.Icc 1 r, y ^ m • (t m).map f

theorem map_det_polyMat {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] {n : ℕ} (r : ℕ)
    (t : ℕ → Matrix (Fin n) (Fin n) O) (f : O →+* S) (y : S) (φ : S →+* S') :
    φ (polyMat r t f y).det = (polyMat r t (φ.comp f) (φ y)).det := by
  rw [RingHom.map_det]
  congr 1
  ext a c
  simp [polyMat, Matrix.one_apply, Matrix.sum_apply, apply_ite]

theorem pow_val_neg {A : Type} [CommGroup A] {n : ℕ} [NeZero n] {u : A} (hu : u ^ n = 1) (x : ZMod n) :
    u ^ (-x).val = (u ^ x.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_add, pow_eq_pow_mod _ hu, ← ZMod.val_add, neg_add_cancel, ZMod.val_zero, pow_zero]

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : ℕ} {b : Bool} {n : ℕ}

def hcoef (i : X.Tw) (P : PlE D.host) (m : ℕ) : X.O i := (-1) ^ m * ((normV P : ℕ) : X.O i) ^ (m * (m - 1) / 2)

def Coord (A : Module.End (X.O i) (Y.Fm i j b)) (bs : Fin n → Y.Fm i j b) (e : Fin n → Y.Dat i j b) (x : X.O i)
    (Q : Finset (PlE D.host)) (M k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (m : Matrix (Fin n) (Fin n) (X.Ok i k)) : Prop :=
  ∀ a, algebraMap (X.O i) (X.Ok i k) x • A.baseChange (X.Ok i k) (specU Y i j b Q M k χ (Y.thU i j b Q M (e a))) =
    ∑ c, m c a • (1 : X.Ok i k) ⊗ₜ[X.O i] bs c

variable {A : Module.End (X.O i) (Y.Fm i j b)} {bs : Fin n → Y.Fm i j b} {e : Fin n → Y.Dat i j b} {x : X.O i}

theorem Coord.unique (hbs : LinearIndependent (X.O i) bs) {Q : Finset (PlE D.host)} {M k : ℕ}
    {χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ} {m m' : Matrix (Fin n) (Fin n) (X.Ok i k)}
    (h : Coord A bs e x Q M k χ m) (h' : Coord A bs e x Q M k χ m') : m = m' := by
  ext c a
  exact Fintype.linearIndependent_iffₛ.1 (linearIndependent_one_tmul (X.Ok_inj i k) hbs) (fun c => m c a)
    (fun c => m' c a) ((h a).symm.trans (h' a)) c

theorem specU_rTensor (A : Module.End (X.O i) (Y.Fm i j b)) (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (w : Y.Fm i j b ⊗[X.O i] AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)) :
    specU Y i j b Q M k χ (A.rTensor _ w) = A.baseChange (X.Ok i k) (specU Y i j b Q M k χ w) := by
  induction w with
  | zero => simp
  | tmul v g => simp [specU]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem exists_coord {Ball : Submodule (X.O i) (Y.Fm i j b)}
    (hA : Ball.map A ≤ Submodule.span (X.O i) (Set.range bs)) {ι : Type} [Fintype ι] (P : ι → PlE D.host)
    (Q : Finset (PlE D.host)) (M : ℕ)
    (hx : ∀ a, x • Y.thU i j b Q M (e a) ∈ LinearMap.range (Ball.subtype.rTensor _)) :
    ∃ m : Matrix (Fin n) (Fin n) (MvPolynomial ι (X.O i)), ∀ (k : ℕ) (u : ι → (X.Ok i k)ˣ)
      (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ), IsChi P Q u χ →
      Coord A bs e x Q M k χ (m.map (MvPolynomial.aeval fun q => (u q : X.Ok i k) - 1)) := by
  have h1 : ∀ a, A.rTensor _ (x • Y.thU i j b Q M (e a)) ∈
      LinearMap.range ((Submodule.span (X.O i) (Set.range bs)).subtype.rTensor
        (AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M))) := by
    intro a
    obtain ⟨w, hw⟩ := hx a
    refine ⟨(A.restrict fun v hv => hA (Submodule.mem_map_of_mem hv)).rTensor _ w, ?_⟩
    rw [← hw, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
    rfl
  choose m hm using fun a => exists_coords bs P Q _ (h1 a)
  refine ⟨Matrix.of fun c a => m a c, fun k u χ hχ a => ?_⟩
  have := hm a (X.Ok i k) u χ hχ
  rw [algebraMap_smul, ← (A.baseChange (X.Ok i k)).map_smul_of_tower, ← map_smul, ← specU_rTensor]
  exact this

theorem pqF_basis {P : PlE D.host} {t : ℕ → Matrix (Fin n) (Fin n) (X.O i)}
    (ht : ∀ m ∈ Finset.Icc 1 D.R.r, ∀ a, hkO Y i j b m P (bs a) = ∑ c, t m c a • bs c) (k : ℕ) (y : X.Ok i k)
    (a : Fin n) : PqF Y i j b k P y ((1 : X.Ok i k) ⊗ₜ[X.O i] bs a) =
      ∑ c, polyMat D.R.r (fun m => hcoef i P m • t m) (algebraMap _ _) y c a • (1 : X.Ok i k) ⊗ₜ[X.O i] bs c := by
  simp only [PqF, polyMat, LinearMap.add_apply, Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.baseChange_tmul, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.sum_apply,
    Finset.sum_smul]
  congr 1
  · simp [Matrix.one_apply]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [ht m hm, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (X.Ok i k) (t m c a), smul_smul]
    congr 1
    simp only [hcoef, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_neg, map_one,
      map_natCast]
    ring

theorem Coord.step {P : PlE D.host} {t : ℕ → Matrix (Fin n) (Fin n) (X.O i)}
    (ht : ∀ m ∈ Finset.Icc 1 D.R.r, ∀ a, hkO Y i j b m P (bs a) = ∑ c, t m c a • bs c)
    (hA : ∀ m ∈ Finset.Icc 1 D.R.r, A ∘ₗ hkO Y i j b m P = hkO Y i j b m P ∘ₗ A)
    {Q Q' : Finset (PlE D.host)} {M k : ℕ} {χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ}
    {χ' : Multiplicative (DelQM D.host (X.l i) Q' M) →* (X.Ok i k)ˣ} {y : X.Ok i k}
    (hrel : ∀ a, specU Y i j b Q M k χ (Y.thU i j b Q M (e a)) =
      PqF Y i j b k P y (specU Y i j b Q' M k χ' (Y.thU i j b Q' M (e a))))
    {m' : Matrix (Fin n) (Fin n) (X.Ok i k)} (h : Coord A bs e x Q' M k χ' m') :
    Coord A bs e x Q M k χ (polyMat D.R.r (fun m => hcoef i P m • t m) (algebraMap _ _) y * m') := by
  intro a
  have hc : ∀ w, A.baseChange (X.Ok i k) (PqF Y i j b k P y w) = PqF Y i j b k P y (A.baseChange (X.Ok i k) w) := by
    intro w
    simp only [PqF, LinearMap.add_apply, Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add,
      map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hA m hm, LinearMap.baseChange_comp, LinearMap.comp_apply]
  rw [hrel, hc, ← map_smul, h a, map_sum]
  simp only [map_smul, pqF_basis ht, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

open Classical in

def Rel (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool) (ch : Set (PlE D.host)) (sg : Bool) : Prop :=
  ∀ (M : ℕ) d (Q : Finset (PlE D.host)) (a : Y.Dat i j b), IsCoord Y i M d → QOk X i Q →
    ClsQ (D := D) Q → Disjoint Q (Y.lev i j b a) →
    (∀ P ∈ Q, GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
    ∀ (P Pb : PlE D.host), P ∈ Q → Pb ∈ Q → P ≠ Pb → IsConjPl D.host P Pb → P ∈ ch →
    ∀ (k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
      (χ' : Multiplicative (DelQM D.host (X.l i) ((Q.erase P).erase Pb) M) →* (X.Ok i k)ˣ),
      (∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) = χ' (Multiplicative.ofAdd fun v =>
        x ⟨v.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase v.2)⟩)) →
      ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ →
        specU Y i j b Q M k χ (Y.thU i j b Q M a) =
          PqF Y i j b k P ((psiAt sg χ' (Y.delU i ((Q.erase P).erase Pb) M σ) : (X.Ok i k)ˣ) : X.Ok i k)
            (specU Y i j b ((Q.erase P).erase Pb) M k χ' (Y.thU i j b ((Q.erase P).erase Pb) M a))

def sgnProd {ι B : Type} [Fintype ι] [CommGroup B] {n : ℕ} (sg : Bool) (u : ι → B) (x : ι → ZMod n) : B :=
  if sg then ∏ q, u q ^ (x q).val else (∏ q, u q ^ (x q).val)⁻¹

open Classical in

theorem det_factor {ch : Set (PlE D.host)} {sg : Bool} (hrel : Rel Y i j b ch sg)
    {Ball : Submodule (X.O i) (Y.Fm i j b)} (hbs : LinearIndependent (X.O i) bs)
    (hAB : Ball.map A ≤ Submodule.span (X.O i) (Set.range bs)) {t : ℕ → PlE D.host → Matrix (Fin n) (Fin n) (X.O i)}
    (ht : ∀ m P, HkIdx i m P → ∀ a, hkO Y i j b m P (bs a) = ∑ c, t m P c a • bs c)
    (hAc : ∀ m P, HkIdx i m P → A ∘ₗ hkO Y i j b m P = hkO Y i j b m P ∘ₗ A) {M : ℕ}
    (hx : ∀ Q, (∀ P ∈ Q, IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (X.S0 i) → ∀ a,
      Disjoint Q (Y.lev i j b (e a)) → x • Y.thU i j b Q M (e a) ∈ LinearMap.range (Ball.subtype.rTensor _))
    {ι : Type} [Fintype ι] {A₀ : Finset (PlE D.host)} {P : ι → PlE D.host}
    {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (hd : IsCoord Y i M d)
    (hA : SlopeTestRemainingChoices X i M A₀ P fun q => d (P q)) (hq : placesOver D.host.E D.host.q ⊆ A₀)
    (hd' : placesOver D.host.E D.host.d ⊆ A₀) (hlev : ∀ a, Y.lev i j b (e a) ⊆ A₀)
    {P' : ι → PlE D.host} (hP' : ∀ q, Over (P q) (P' q)) (hch : ∀ q, P' q ∈ ch) {σ : ι → GE N}
    (hσ : ∀ q, IsFrob (N.plOm.1 (P' q)) (normV (P' q)) (σ q)) {k : ℕ} {u : ι → (X.Ok i k)ˣ}
    (hu : ∀ q, u q ^ (X.l i ^ M) = 1) {J₀ : Finset ι} (hJ₀ : ∀ q, q ∉ J₀ → u q = 1) {Q₀ : Finset (PlE D.host)}
    (hQ₀ : IsSub P J₀ Q₀) {χ₀ : Multiplicative (DelQM D.host (X.l i) Q₀ M) →* (X.Ok i k)ˣ} (hχ₀ : IsChi P Q₀ u χ₀)
    {m₀ : Matrix (Fin n) (Fin n) (X.Ok i k)} (hm₀ : Coord A bs e x Q₀ M k χ₀ m₀) (J : Finset ι) :
    Disjoint J J₀ → ∀ (Q : Finset (PlE D.host)) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
      (m : Matrix (Fin n) (Fin n) (X.Ok i k)), IsSub P (J ∪ J₀) Q → IsChi P Q u χ → Coord A bs e x Q M k χ m →
      m.det = (∏ q ∈ J, (polyMat D.R.r (fun m => hcoef i (P' q) m • t m (P' q)) (algebraMap _ (X.Ok i k))
        ((sgnProd sg u fun q' => Multiplicative.toAdd (d (P q') (σ q)) : (X.Ok i k)ˣ) : X.Ok i k)).det) * m₀.det := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  induction J using Finset.induction_on with
  | empty =>
    intro _ Q χ m hQ hχ hm
    rw [Finset.empty_union] at hQ
    obtain rfl := hQ.unique hQ₀
    obtain rfl := hχ.unique hχ₀
    rw [hm.unique hbs hm₀, Finset.prod_empty, one_mul]
  | insert q J hqJ ih =>
    intro hdis Q χ m hQ hχ hm
    rw [Finset.disjoint_insert_left] at hdis
    rw [Finset.insert_union] at hQ
    have hq' : q ∉ J ∪ J₀ := by simp [hqJ, hdis.1]
    obtain ⟨Pb, hPb⟩ := exists_isConjPl (P' q)
    have hQ' := hQ.erase hq' hA.2.1 (hP' q) hPb
    obtain ⟨a1, a2, a3, a4⟩ := hQ.admissible Y hd hA hq hd'
    obtain ⟨b1, b2, b3, -⟩ := hQ'.admissible Y hd hA hq hd'
    have hm1 : P' q ∈ Q := (hQ _).2 ⟨q, Finset.mem_insert_self _ _, hP' q⟩
    obtain ⟨χ', hχ'⟩ := exists_isChi P ((Q.erase (P' q)).erase Pb) u hu
    obtain ⟨mp, hmp⟩ := exists_coord (A := A) (e := e) (x := x) hAB P ((Q.erase (P' q)).erase Pb) M
      fun a => hx _ b1.1 b2 b1.2.1 a (b3.mono_right (hlev a))
    have hm' := hmp k u χ' hχ'
    have hidx : ∀ m ∈ Finset.Icc 1 D.R.r, HkIdx i m (P' q) := fun m hm =>
      ⟨(Finset.mem_Icc.1 hm).1, (Finset.mem_Icc.1 hm).2, a1.1 _ hm1, Finset.disjoint_left.1 a1.2.1 hm1⟩
    have hcomp : ∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) = χ' (Multiplicative.ofAdd fun v =>
        x ⟨v.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase v.2)⟩) := by
      intro x
      rw [hχ, hχ']
      refine Finset.prod_congr rfl fun q' _ => ?_
      by_cases h1 : P q' ∈ (Q.erase (P' q)).erase Pb
      · rw [dif_pos h1, dif_pos (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h1))]
      · rw [dif_neg h1, hJ₀ q' fun h => h1 ((hQ'.mem_iff hA.2.1 q').2 (Finset.mem_union_right _ h))]
        simp
    have hy : psiAt sg χ' (Y.delU i ((Q.erase (P' q)).erase Pb) M (σ q)) =
        sgnProd sg u fun q' => Multiplicative.toAdd (d (P q') (σ q)) := by
      have : χ' (Y.delU i ((Q.erase (P' q)).erase Pb) M (σ q)) =
          ∏ q', u q' ^ (Multiplicative.toAdd (d (P q') (σ q))).val := by
        refine (hχ' (Multiplicative.toAdd _)).trans (Finset.prod_congr rfl fun q' _ => ?_)
        by_cases h1 : P q' ∈ (Q.erase (P' q)).erase Pb
        · rw [dif_pos h1, ← hd _ hQ'.conjCl _ h1]
          rfl
        · rw [dif_neg h1, hJ₀ q' fun h => h1 ((hQ'.mem_iff hA.2.1 q').2 (Finset.mem_union_right _ h)), one_pow]
      cases sg <;> simp [psiAt, sgnProd, this]
    have hstep := Coord.step (fun m hm => ht m _ (hidx m hm)) (fun m hm => hAc m _ (hidx m hm))
      (fun a => hrel M d Q (e a) hd a1 a2 (a3.mono_right (hlev a)) a4 (P' q) Pb hm1 (hQ.conjCl _ hm1 _ hPb)
        (ne_of_isSplitPl (a1.1 _ hm1) hPb) hPb (hch q) k χ χ' hcomp (σ q) (hσ q)) hm'
    rw [hm.unique hbs hstep, Matrix.det_mul, ih hdis.2 _ χ' _ hQ' hχ' hm', Finset.prod_insert hqJ, hy, mul_assoc]

theorem exists_exponent {M R : ℕ} (hM : 1 ≤ M) {P : Fin R ⊕ Fin R → PlE D.host}
    {d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (hanti : ∀ q, AntiHom X.cc (d q))
    {H : Subgroup (GE N)} {z : GE N} (hS : Steps X i M H z P d) (sg : Bool) (a : Fin R) {v : PlE D.host}
    (hv : Over (P (.inr a)) v) {σ : GE N} (hσ : IsFrob (N.plOm.1 v) (normV v) σ) :
    ∃ ε : ℕ, (ε : IsLocalRing.ResidueField (X.O i)) ≠ 0 ∧ ∀ (B : Type) [CommGroup B] (u : Fin R ⊕ Fin R → B),
      (∀ q, u q ^ (X.l i ^ M) = 1) → (∀ a, u (.inr a) = 1) →
      (sgnProd sg u fun q => Multiplicative.toAdd (d q σ)) = u (.inl a) ^ ε := by
  have hl := (X.lPrime i).out
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hlt : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hl.one_lt
  have : Fact (1 < X.l i ^ M) := ⟨hlt⟩
  have h0 : ∀ σ₀ : GE N, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ₀ → ∀ (B : Type) [CommGroup B]
      (u : Fin R ⊕ Fin R → B), (∀ a, u (.inr a) = 1) →
      ∏ q, u q ^ (Multiplicative.toAdd (d q σ₀)).val = u (.inl a) := by
    intro σ₀ h B _ u hu
    rw [Fintype.prod_sum_type, Finset.prod_eq_single a, hS.2 a a σ₀ h]
    · simp [hu, ZMod.val_one]
    · intro c _ hc
      rw [hS.2 a c σ₀ h, if_neg hc.symm]; simp
    · simp
  have h1 : (∀ (B : Type) [CommGroup B] (u : Fin R ⊕ Fin R → B), (∀ q, u q ^ (X.l i ^ M) = 1) →
      (∀ a, u (.inr a) = 1) → (sgnProd sg u fun q => Multiplicative.toAdd (d q σ)) = u (.inl a)) ∨
      (∀ (B : Type) [CommGroup B] (u : Fin R ⊕ Fin R → B), (∀ q, u q ^ (X.l i ^ M) = 1) →
      (∀ a, u (.inr a) = 1) → (sgnProd sg u fun q => Multiplicative.toAdd (d q σ)) = (u (.inl a))⁻¹) := by
    rcases hv with rfl | hv
    · cases sg
      · exact Or.inr fun B _ u _ hu => by simp [sgnProd, h0 σ hσ B u hu]
      · exact Or.inl fun B _ u _ hu => by simp [sgnProd, h0 σ hσ B u hu]
    · obtain ⟨σ₀, g, hσ₀, rfl⟩ := exists_frob_of_conj X hv hσ
      have h2 : ∀ (B : Type) [CommGroup B] (u : Fin R ⊕ Fin R → B), (∀ q, u q ^ (X.l i ^ M) = 1) →
          (∀ a, u (.inr a) = 1) →
          ∏ q, u q ^ (Multiplicative.toAdd (d q (g * cConj X σ₀ * g⁻¹))).val = (u (.inl a))⁻¹ := by
        intro B _ u hu hu'
        rw [← h0 σ₀ hσ₀ B u hu', ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [(d q).map_mul, (d q).map_mul, (d q).map_inv, mul_inv_cancel_comm, antiHom_cConj X (hanti q), toAdd_inv, pow_val_neg (hu q)]
      cases sg
      · exact Or.inl fun B _ u hu hu' => by simp only [sgnProd, h2 B u hu hu']; simp
      · exact Or.inr fun B _ u hu hu' => by simp only [sgnProd, h2 B u hu hu']; simp
  rcases h1 with h | h
  · exact ⟨1, by simp, fun B _ u hu hu' => by rw [h B u hu hu', pow_one]⟩
  · refine ⟨X.l i ^ M - 1, ?_, fun B _ u hu hu' => ?_⟩
    · have : ((X.l i : ℕ) : IsLocalRing.ResidueField (X.O i)) = 0 := by
        rw [← map_natCast (IsLocalRing.residue (X.O i)), IsLocalRing.residue_eq_zero_iff]
        exact X.O_l i
      rw [Nat.cast_sub hlt.le, Nat.cast_pow, this, zero_pow (by omega)]
      simp
    · rw [h B u hu hu', inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hlt.le, hu]

theorem one_tmul_injective (k : ℕ) {v w : Y.Fm i j b}
    (h : (1 : X.Ok i k) ⊗ₜ[X.O i] v = (1 : X.Ok i k) ⊗ₜ[X.O i] w) : v = w := by
  have : Module.IsTorsionFree (X.O i) (Y.Fm i j b) :=
    Module.IsTorsionFree.trans_faithfulSMul (X.O i) (FractionRing (X.O i)) _
  by_contra hne
  have h1 : LinearIndependent (X.O i) fun _ : Unit => v - w := linearIndependent_unique_iff.2 (sub_ne_zero.2 hne)
  exact (linearIndependent_one_tmul (X.Ok_inj i k) h1).ne_zero () (by rw [TensorProduct.tmul_sub, h, sub_self])

theorem l_ne_zero (i : X.Tw) : ((X.l i : ℕ) : X.O i) ≠ 0 := by
  intro h
  have : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have h1 := (X.zk_prim i 1).neZero'.out
  rw [pow_one, ← map_natCast (algebraMap (X.O i) (X.Ok i 1)), h, map_zero] at h1
  exact h1 rfl

theorem aeval_one_sub_one {O S ι : Type} [CommRing O] [CommRing S] [Algebra O S] (p : MvPolynomial ι O) :
    MvPolynomial.aeval (fun q => (((1 : ι → Sˣ) q : Sˣ) : S) - 1) p = algebraMap O S (p.coeff 0) := by
  simp [MvPolynomial.constantCoeff_eq]

theorem residue_prod_det {O k ι κ : Type} [CommRing O] [Field k] [Fintype κ] {n : ℕ} (r : ℕ)
    (t : κ → ℕ → Matrix (Fin n) (Fin n) O) (ρ : O →+* k) (ε : κ → ℕ) (hε : ∀ a, (ε a : k) ≠ 0) (f : κ → ι) :
    ∃ (w : MvPolynomial ι k) (ν : κ → ℕ), w.coeff 0 ≠ 0 ∧ (∀ a, ν a ≤ r * n) ∧
      MvPolynomial.map ρ (∏ a, (polyMat r (t a) MvPolynomial.C ((1 + MvPolynomial.X (f a)) ^ ε a)).det) =
        w * ∏ a, MvPolynomial.X (f a) ^ ν a := by
  choose w ν hw hν hdet using fun a => det_eq_mul_X_pow n r (ε a) (fun m => (t a m).map ρ) (f a) (hε a)
  refine ⟨∏ a, w a, ν, ?_, hν, ?_⟩
  · rw [← MvPolynomial.constantCoeff_eq, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hw a
  · rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    have e : (MvPolynomial.map (σ := ι) ρ).comp MvPolynomial.C = MvPolynomial.C.comp ρ := by ext1 r; simp
    rw [← hdet, map_det_polyMat, e]
    simp only [polyMat, Matrix.map_map, map_pow, map_add, map_one, MvPolynomial.map_X, RingHom.coe_comp]

theorem propABCD_of_rel : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (Y : NExp D.R D.host D.what₂ D.LL0 N X), ThURel Y → HeckeLaws Y → AllGood Y → Formalism.MainNotions.BlochKatoReduction.Gen.adm8 X Y → PropABCD Y := by
  intro D N X Y hTh hH hG h8 i F j b z hW hj hAB hz
  classical
  obtain ⟨-, -, -, hlat, hABle, hBst, hli, hsp, -, hAc, ⟨c, hc⟩, hT3⟩ := hAB
  obtain ⟨ch, sg, hch, h0, hrel⟩ := hTh i hW j hj b
  have hrel' : Rel Y i j b ch sg := hrel
  obtain ⟨H, hHo, hHn, hHu⟩ := exists_subgroup_isUnit Y i z (hG i hW) (h8 i hW) (hH i hW).2 hz
  obtain ⟨n, ⟨eqv⟩⟩ : ∃ n, Nonempty (Fin n ≃ ↥(F.S j b)) := ⟨_, ⟨(F.S j b).equivFin.symm⟩⟩
  let e : Fin n → Y.Dat i j b := fun a => (eqv a).1
  have he : ∀ a, e a ∈ F.S j b := fun a => (eqv a).2
  let th : Fin n → Y.Fm i j b := fun a => F.A j b (Y.th i j b (e a))
  have hthi : LinearIndependent (X.O i) th := hli.comp eqv eqv.injective
  have hthr : Set.range th = (fun a => F.A j b (Y.th i j b a)) '' ↑(F.S j b) := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e a, he a, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨eqv.symm ⟨a, ha⟩, by simp [th, e]⟩
  obtain ⟨bs, hbs, hB⟩ := exists_basis_fin hlat.1 hthi (by rw [hthr, hsp])
  have ht' : ∀ m P, ∃ t : Matrix (Fin n) (Fin n) (X.O i), HkIdx i m P →
      ∀ a, hkO Y i j b m P (bs a) = ∑ c, t c a • bs c := by
    intro m P
    by_cases h : HkIdx i m P
    · have : ∀ a, ∃ v : Fin n → X.O i, ∑ c, v c • bs c = hkO Y i j b m P (bs a) := fun a =>
        (Submodule.mem_span_range_iff_exists_fun _).1 (by
          rw [hB]
          exact hBst m P h (Submodule.mem_map_of_mem (hB ▸ Submodule.subset_span ⟨a, rfl⟩)))
      choose v hv using this
      exact ⟨Matrix.of fun c a => v a c, fun _ a => (hv a).symm⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose t ht using ht'
  rw [← hB] at hABle
  set x : X.O i := (X.l i : X.O i) ^ c with hxdef
  have hx0 : x ≠ 0 := pow_ne_zero _ (l_ne_zero i)
  have hx : ∀ M Q, (∀ P ∈ Q, IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (X.S0 i) → ∀ a,
      Disjoint Q (Y.lev i j b (e a)) →
      x • Y.thU i j b Q M (e a) ∈ LinearMap.range ((F.Ball j b).subtype.rTensor _) :=
    fun M Q h1 h2 h3 a h4 => hc Q M h1 h2 h3 _ (he a) h4
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : Matrix (Fin n) (Fin n) (X.O i), ∀ a, x • th a = ∑ c, m₀ c a • bs c := by
    obtain ⟨mp, hmp⟩ := exists_coord (A := F.A j b) (e := e) (x := x) hABle (fun q : Empty => q.elim) ∅ 0
      fun a => hx 0 ∅ (by simp) (by simp [ClsQ]) (by simp) a (by simp)
    refine ⟨mp.map (MvPolynomial.coeff 0), fun a => one_tmul_injective 0 ?_⟩
    have := hmp 0 1 1 (fun x => by rw [Fintype.prod_empty]; rfl) a
    rw [h0, LinearMap.baseChange_tmul, algebraMap_smul, ← TensorProduct.tmul_smul] at this
    rw [this, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.map_apply, aeval_one_sub_one, algebraMap_smul, TensorProduct.tmul_smul, Matrix.map_apply]
  have hd₀ : m₀.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 : ∑ a, (v a * x) • th a = ∑ c, (m₀.mulVec v) c • bs c := by
      simp only [mul_smul, hm₀, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _
    rw [hv] at h1
    have h2 := Fintype.linearIndependent_iff.1 hthi _ (h1.trans (by simp))
    exact hv0 (funext fun a => (mul_eq_zero.1 (h2 a)).resolve_right hx0)
  have hco₀ : ∀ M k χ, Coord (F.A j b) bs e x ∅ M k χ (m₀.map (algebraMap (X.O i) (X.Ok i k))) := by
    intro M k χ a
    rw [h0, LinearMap.baseChange_tmul, algebraMap_smul, ← TensorProduct.tmul_smul, hm₀, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.map_apply, algebraMap_smul, TensorProduct.tmul_smul]
  let A₀ : Finset (PlE D.host) := (finite_placesOver (D := D) D.host.hyp.1.ne_zero).toFinset ∪
    (finite_placesOver (D := D) D.host.hyp.2.1.ne_zero).toFinset ∪ (F.S j b).biUnion (Y.lev i j b)
  have hAq : placesOver D.host.E D.host.q ⊆ A₀ := fun v hv => by simp [A₀, hv]
  have hAd : placesOver D.host.E D.host.d ⊆ A₀ := fun v hv => by simp [A₀, hv]
  have hlev : ∀ a, Y.lev i j b (e a) ⊆ A₀ := fun a v hv =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, he a, hv⟩)
  refine ⟨H, A₀, (IsDiscreteValuationRing.addVal (X.O i) m₀.det).toNat, D.R.r * n, hHo, hHn, ?_⟩
  intro M R P d Q hM hd hA hS hQ
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have hP'e : ∀ q, ∃ v, Over (P q) v ∧ v ∈ ch := by
    intro q
    obtain ⟨v, hv⟩ := exists_isConjPl (P q)
    by_cases h : P q ∈ ch
    · exact ⟨_, over_refl _, h⟩
    · exact ⟨v, Or.inr hv, not_not.1 (mt (hch _ _ hv (ne_of_isSplitPl (hA.1 q _ (over_refl _)).1 hv)).2 h)⟩
  choose P' hP' hP'c using hP'e
  choose σ hσ using fun q => exists_isFrob (F := D.host.E) (N.plOm.2 (P' q))
  let J₁ : Finset (Fin R ⊕ Fin R) := Finset.univ.map Function.Embedding.inl
  let J₂ : Finset (Fin R ⊕ Fin R) := Finset.univ.map Function.Embedding.inr
  have hQs : IsSub P (J₂ ∪ J₁) Q := fun v => by
    rw [hQ]
    exact exists_congr fun q => by rcases q with q | q <;> simp [J₁, J₂]
  obtain ⟨Q₁, hQ₁⟩ := exists_isSub P J₁
  obtain ⟨a1, a2, a3, -⟩ := hQs.admissible Y hd hA hAq hAd
  obtain ⟨b1, b2, b3, -⟩ := hQ₁.admissible Y hd hA hAq hAd
  obtain ⟨mQ, hmQ⟩ := exists_coord (A := F.A j b) (e := e) (x := x) hABle P Q M
    fun a => hx M _ a1.1 a2 a1.2.1 a (a3.mono_right (hlev a))
  obtain ⟨m₁, hm₁⟩ := exists_coord (A := F.A j b) (e := e) (x := x) hABle P Q₁ M
    fun a => hx M _ b1.1 b2 b1.2.1 a (b3.mono_right (hlev a))
  choose ε hε hεu using fun a => exists_exponent hM (fun q => (hA.2.2 q).2.1) hS sg a (hP' (.inr a)) (hσ (.inr a))
  refine ⟨mQ.det, ⟨∏ a, (polyMat D.R.r (fun m => hcoef i (P' (.inr a)) m • t m (P' (.inr a))) MvPolynomial.C
    ((1 + MvPolynomial.X (.inl a)) ^ ε a)).det, m₁.det, ?_, ?_, ?_⟩, ?_⟩
  · refine mem_span_of_aeval_eq_zero (X.Ok_inj i M) (NeZero.pos _) (X.zk_prim i M) _ fun u hu hu' => ?_
    obtain ⟨χ, hχ⟩ := exists_isChi P Q u hu
    obtain ⟨χ₁, hχ₁⟩ := exists_isChi P Q₁ u hu
    have := det_factor hrel' hbs hABle ht hAc (hx M) hd hA hAq hAd hlev hP' hP'c hσ hu (J₀ := J₁)
      (by rintro (q | q) h; exacts [absurd (by simp [J₁]) h, hu' q]) hQ₁ hχ₁ (hm₁ M u χ₁ hχ₁) J₂
      (by simp [J₁, J₂, Finset.disjoint_left]) Q χ _ (by convert hQs) hχ (hmQ M u χ hχ)
    rw [map_sub, map_mul, sub_eq_zero, AlgHom.map_det, AlgHom.map_det, map_prod]
    refine this.trans ?_
    congr 1
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun a _ => ?_
    refine Eq.trans ?_ (map_det_polyMat _ _ _ _
      (MvPolynomial.aeval (R := X.O i) fun q => (u q : X.Ok i M) - 1).toRingHom).symm
    congr 2
    · ext r; simp
    · rw [Function.Embedding.inr_apply, hεu a _ u hu hu']; simp
  · obtain ⟨χ₁, hχ₁⟩ := exists_isChi (n := X.l i ^ M) P Q₁ (1 : Fin R ⊕ Fin R → (X.Ok i 0)ˣ) (by simp)
    have := det_factor hrel' hbs hABle ht hAc (hx M) hd hA hAq hAd hlev hP' hP'c hσ (k := 0) (u := 1) (by simp)
      (J₀ := ∅) (fun _ _ => rfl) (Q₀ := ∅) (fun v => by simp) (χ₀ := 1) (fun x => by simp) (hco₀ M 0 1) J₁ (by simp)
      Q₁ χ₁ _ (fun v => by rw [hQ₁]; simp) hχ₁ (hm₁ 0 1 χ₁ hχ₁)
    have e1 : m₁.det.coeff 0 = (∏ q ∈ J₁, (polyMat D.R.r (fun m => hcoef i (P' q) m • t m (P' q))
        (RingHom.id _) 1).det) * m₀.det := by
      apply X.Ok_inj i 0
      rw [← aeval_one_sub_one, AlgHom.map_det, map_mul, map_prod, RingHom.map_det]
      refine this.trans ?_
      congr 1
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [map_det_polyMat]
      congr 2
      cases sg <;> simp [sgnProd]
    have hu : IsUnit (∏ q ∈ J₁, (polyMat D.R.r (fun m => hcoef i (P' q) m • t m (P' q)) (RingHom.id _) 1).det) := by
      refine IsUnit.prod_iff.2 fun q hq => ?_
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hq
      have hv := hA.1 (.inl a) _ (hP' (.inl a))
      have hidx : ∀ m ∈ Finset.Icc 1 D.R.r, HkIdx i m (P' (.inl a)) := fun m hm =>
        ⟨(Finset.mem_Icc.1 hm).1, (Finset.mem_Icc.1 hm).2, hv.1, hv.2.2.2.1⟩
      have := X.resO_ac i
      have h1 := isUnit_det_of_eigen hbs (HkIdx i) (hkO Y i j b) t
        (fun k p k' p' hg hg' => LinearMap.ext fun w => LinearMap.congr_fun ((hH i hW).1 j b k p k' p' hg hg') w)
        ht (Finset.Icc 1 D.R.r) (P' (.inl a)) (hcoef i (P' (.inl a))) hidx (by
          rw [hB]
          intro w hw hw' ev hev
          obtain ⟨s, -, -, hs⟩ := hT3 w hw hw' ev hev
          have h2 := hHu _ _ (hP' (.inl a)) hv.1 hv.2.2.2.1 (hS.1 a) s
          rw [← IsLocalRing.residue_ne_zero_iff_isUnit] at h2 ⊢
          convert h2 using 1
          simp only [map_add, map_sum, map_mul]
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          have h3 := (IsLocalRing.residue_eq_zero_iff _).2 (hs m _ (hidx m hm))
          rw [map_sub, sub_eq_zero] at h3
          rw [h3, hcoef, map_mul])
      simpa [polyMat] using h1
    rw [e1, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu, zero_add,
      ENat.natCast_toNat (mt IsDiscreteValuationRing.addVal_eq_top_iff.1 hd₀)]
  · obtain ⟨w, ν, hw, hν, hdet⟩ := residue_prod_det D.R.r
      (fun a m => hcoef i (P' (.inr a)) m • t m (P' (.inr a))) (IsLocalRing.residue (X.O i)) ε hε Sum.inl
    exact ⟨w, ν, hw, hν, by rw [hdet, sub_self]; exact Ideal.zero_mem _⟩
  · intro k u χ hu hχ hne T hT hw
    have hχ' : IsChi P Q u χ := fun y => by
      rw [hχ]
      exact Finset.prod_congr rfl fun q _ => by rw [dif_pos]
    have : Module.Finite (X.O i) (X.Ok i k) := X.Ok_fin i k
    have : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
    have : IsLocalHom (algebraMap (X.O i) (X.Ok i k)) := Algebra.IsIntegral.isLocalHom _ _
    have hV : IsLatIn (Submodule.span (X.O i) (Set.range bs))
        ((Submodule.span (FractionRing (X.O i)) (F.B j b : Set (Y.Fm i j b))).restrictScalars (X.O i)) := by
      rw [hB]
      refine ⟨hlat.1, fun v hv => Submodule.subset_span hv, fun v hv => hlat.2.2 v ?_⟩
      exact (Submodule.span_le (R := FractionRing (X.O i))).2 (fun y hy => hlat.2.1 hy) hv
    rw [AlgHom.map_det] at hne ⊢
    have h1 := sIdx_le_of_coords (X.Ok_inj i k) (X.l i) hx0 hbs hV (th := th)
      (fun a => by
        rw [Submodule.restrictScalars_mem, ← hsp]
        exact Submodule.subset_span ⟨e a, he a, rfl⟩) hm₀ hd₀ (hmQ k u χ hχ') hne hT fun a => hw _ (he a)
    rw [hB, hthr] at h1
    exact h1

end GlobalTheory.TwistDet

end
