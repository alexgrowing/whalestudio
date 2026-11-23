import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantToZModPow
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

variable {l : ℕ} [Fact l.Prime]

instance neZeroPow (m : ℕ) : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

def ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) : (A.cont ℤ_[l]).A :=
  ⟨fun z => if PadicInt.toZModPow m z = c then 1 else 0, fun k =>
    ((GlobalTheory.CompanionTheory.PadicShift.isLocallyConstant_toZModPow l m).comp fun a =>
      if a = c then (1 : A.A) else 0).comp (Ideal.Quotient.mk (Ideal.span {A.pi ^ k}))⟩

theorem ev_ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) (z : ℤ_[l]) :
    Hom.f (A.evCont z) (ind A m c) = if PadicInt.toZModPow m z = c then 1 else 0 := rfl

theorem cont_ext {A : PAlg l} {f g : (A.cont ℤ_[l]).A}
    (h : ∀ z, Hom.f (A.evCont z) f = Hom.f (A.evCont z) g) : f = g :=
  Subtype.ext (funext h)

theorem ev_toCont (A : PAlg l) (z : ℤ_[l]) (a : A.A) :
    Hom.f (A.evCont z) (Hom.f (A.toCont ℤ_[l]) a) = a := rfl

theorem mem_span_pi_pow (A : PAlg l) (k : ℕ) (f : (A.cont ℤ_[l]).A) :
    f ∈ Ideal.span {(A.cont ℤ_[l]).pi ^ k} ↔ ∀ z, Hom.f (A.evCont z) f ∈ Ideal.span {A.pi ^ k} :=
  (RL.cont_ex A ℤ_[l]).2.2.2 k f

theorem sharp_zero (A : PAlg l) : A.sharp 0 = 0 := by
  have h : WittVector.teichmuller l (0 : A.A) = 0 := by
    ext n
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos]
  change A.th (WittVector.teichmuller l (0 : A.A)) = 0
  rw [h, map_zero]

theorem sharp_add (A : PAlg l) {e f : A.A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : e * f = 0) : A.sharp (e + f) = A.sharp e + A.sharp f := by
  have hs : IsIdempotentElem (e + f) := by
    have h' : f * e = 0 := by rw [mul_comm, h]
    simp only [IsIdempotentElem, add_mul, mul_add, h, h', he.eq, hf.eq, add_zero, zero_add]
  have h1 := (RL.sharp_cong A).2.2 _ hs
  have h2 := (RL.sharp_cong A).2.2 _ he
  have h3 := (RL.sharp_cong A).2.2 _ hf
  have h4 : (1 - (e + f)) = (1 - e) * (1 - f) := by
    have : (1 - e) * (1 - f) = 1 - e - f + e * f := by ring
    rw [this, h]; ring
  have h5 : A.sharp e * A.sharp f = 0 := by rw [← map_mul, h, sharp_zero]
  rw [h4, map_mul, h2, h3] at h1
  have : (1 - A.sharp e) * (1 - A.sharp f) = 1 - A.sharp e - A.sharp f + A.sharp e * A.sharp f := by ring
  rw [this, h5] at h1
  have h6 : A.sharp (e + f) = 1 - (1 - A.sharp e - A.sharp f + 0) := by rw [h1]; ring
  rw [h6]; ring

theorem sharp_sum (A : PAlg l) {I : Type} (s : Finset I) (e : I → A.A)
    (hi : ∀ i ∈ s, IsIdempotentElem (e i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    A.sharp (∑ i ∈ s, e i) = ∑ i ∈ s, A.sharp (e i) ∧ IsIdempotentElem (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using sharp_zero A, by simp [IsIdempotentElem]⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i h => hi i (Finset.mem_insert_of_mem h))
      (fun i h j h' => ho i (Finset.mem_insert_of_mem h) j (Finset.mem_insert_of_mem h'))
    have h3 : e a * ∑ i ∈ s, e i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i h => ho a (Finset.mem_insert_self _ _) i
        (Finset.mem_insert_of_mem h) (fun e' => ha (e' ▸ h))
    have h4 := hi a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [sharp_add A h4 h2 h3, h1], ?_⟩
    have h5 : (∑ i ∈ s, e i) * e a = 0 := by rw [mul_comm, h3]
    simp only [IsIdempotentElem, add_mul, mul_add, h3, h5, h4.eq, h2.eq, add_zero, zero_add]

theorem sum_sharp_eq_one (A : PAlg l) {I : Type} [Fintype I] {e : I → A.A}
    (h : CompleteOrthogonalIdempotents e) : ∑ i, A.sharp (e i) = 1 := by
  have := (sharp_sum A Finset.univ e (fun i _ => h.idem i) (fun i _ j _ hij => h.ortho hij)).1
  rw [← this, h.complete]
  exact (map_one A.sharp)

theorem ind_mul_ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) :
    ind A m c * ind A m c = ind A m c := by
  refine cont_ext fun z => ?_
  rw [map_mul, ev_ind]
  split_ifs <;> simp

theorem ind_orth (A : PAlg l) (m : ℕ) {c c' : ZMod (l ^ m)} (h : c ≠ c') :
    ind A m c * ind A m c' = 0 := by
  refine cont_ext fun z => ?_
  rw [map_mul, ev_ind, ev_ind, map_zero]
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) h
  all_goals simp

theorem sum_ind (A : PAlg l) (m : ℕ) : ∑ c, ind A m c = 1 := by
  refine cont_ext fun z => ?_
  rw [map_sum, map_one]
  simp only [ev_ind]
  rw [Finset.sum_ite_eq]
  simp

theorem coi_ind (A : PAlg l) (m : ℕ) : CompleteOrthogonalIdempotents (ind A m) :=
  ⟨⟨ind_mul_ind A m, fun _ _ h => ind_orth A m h⟩, sum_ind A m⟩

theorem coi_map {A t : PAlg l} (ψ : A.cont ℤ_[l] ⟶ t) (m : ℕ) :
    CompleteOrthogonalIdempotents fun c => Hom.f ψ (ind A m c) :=
  (coi_ind A m).map (Hom.f ψ)

theorem contMap_ind {A A' : PAlg l} (φ : A ⟶ A') (m : ℕ) (c : ZMod (l ^ m)) :
    Hom.f (contMap φ ℤ_[l]) (ind A m c) = ind A' m c := by
  refine cont_ext fun z => ?_
  change Hom.f φ (Hom.f (A.evCont z) (ind A m c)) = _
  rw [ev_ind, ev_ind]
  split_ifs <;> simp

theorem exists_roots (A : PAlg l) (a : A.A) :
    ∃ ρ : ℕ → A.A, ρ 0 = a ∧ ∀ m, ρ (m + 1) ^ l = ρ m := by
  choose g hg using A.frob_bijective.2
  refine ⟨fun m => g^[m] a, rfl, fun m => ?_⟩
  show (g^[m + 1] a) ^ l = g^[m] a
  rw [Function.iterate_succ_apply']
  exact hg _

theorem roots_unique (A : PAlg l) {a b : ℕ → A.A} (h0 : a 0 = b 0)
    (ha : ∀ m, a (m + 1) ^ l = a m) (hb : ∀ m, b (m + 1) ^ l = b m) : a = b := by
  funext m
  induction m with
  | zero => exact h0
  | succ m ih => exact A.frob_bijective.1 ((ha m).trans (ih.trans (hb m).symm))

theorem mul_sub_eq_zero_of_sum {R I : Type} [CommRing R] [Fintype I] [DecidableEq I] {a b : I → R}
    (hi : ∀ i, a i * a i = a i) (ho : ∀ i j, i ≠ j → a i * a j = 0) {x : R}
    (hx : x = ∑ i, a i * b i) (i : I) : a i * (x - b i) = 0 := by
  rw [hx, mul_sub, Finset.mul_sum, Finset.sum_eq_single i, ← mul_assoc, hi, sub_self]
  · intro j _ hj
    rw [← mul_assoc, ho i j hj.symm, zero_mul]
  · simp

theorem eq_sum_of_mul_sub {R I : Type} [CommRing R] [Fintype I] {a b : I → R}
    (h1 : ∑ i, a i = 1) {x : R} (hx : ∀ i, a i * (x - b i) = 0) : x = ∑ i, a i * b i := by
  have : ∑ i, a i * x = ∑ i, a i * b i :=
    Finset.sum_congr rfl fun i _ => by have := hx i; rw [mul_sub, sub_eq_zero] at this; exact this
  rw [← this, ← Finset.sum_mul, h1, one_mul]

end GlobalTheory.CompanionTheory.ContUniv
