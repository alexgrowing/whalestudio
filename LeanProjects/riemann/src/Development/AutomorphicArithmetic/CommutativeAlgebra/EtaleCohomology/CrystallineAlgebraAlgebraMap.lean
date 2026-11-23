import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

section Ring

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, CommRing (T i)]
  (f : ∀ i, R →+* T i)

private theorem wit_bij (h : Function.Bijective fun (a : R) i => f i a) :
    Function.Bijective fun (x : WittVector l R) i => WittVector.map (f i) x := by
  constructor
  · intro x y e
    ext n
    refine h.1 (funext fun i => ?_)
    have := congrArg (fun w => WittVector.coeff w n) (congrFun e i)
    simpa only [WittVector.map_coeff] using this
  · intro y
    choose c hc using fun n => h.2 (fun i => (y i).coeff n)
    refine ⟨WittVector.mk l c, funext fun i => ?_⟩
    ext n
    rw [WittVector.map_coeff]
    exact congrFun (hc n) i

private theorem l_unit (S : Type) [CommRing S] (k : ℕ) :
    IsUnit ((l : WL l S) ^ k) := by
  have : IsUnit (algebraMap (WittVector l S) (WL l S) (l : WittVector l S)) :=
    IsLocalization.Away.algebraMap_isUnit (l : WittVector l S)
  rw [map_natCast] at this
  exact this.pow k

private theorem exists_num {S : Type} [CommRing S] (x : WL l S) :
    ∃ (a : WittVector l S) (k : ℕ), x * (l : WL l S) ^ k = algebraMap _ (WL l S) a := by
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (l : WittVector l S)) x
  refine ⟨a, k, ?_⟩
  simpa only [map_pow, map_natCast] using h

private theorem away_bij (h : Function.Bijective fun (a : R) i => f i a) :
    Function.Bijective fun (x : WL l R) i => awayW (f i) x := by
  have hw := wit_bij (l := l) f h
  constructor
  · have hz : ∀ x : WL l R, (∀ i, awayW (f i) x = 0) → x = 0 := by
      intro x hx
      obtain ⟨a, k, hk⟩ := exists_num x
      have h1 : ∀ i, ∃ m : ℕ, (l : WittVector l (T i)) ^ m * WittVector.map (f i) a = 0 := by
        intro i
        have : algebraMap _ (WL l (T i)) (WittVector.map (f i) a) = 0 := by
          rw [← awayW_algebraMap, ← hk, map_mul, hx i, zero_mul]
        obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (l : WittVector l (T i))) _ _).1 this
        exact ⟨m, hm⟩
      choose m hm using h1
      have h2 : (l : WittVector l R) ^ (∑ i, m i) * a = 0 := by
        refine hw.1 (funext fun i => ?_)
        have hd : m i ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        change WittVector.map (f i) _ = WittVector.map (f i) 0
        rw [map_mul, map_pow, map_natCast, map_zero, ← Nat.sub_add_cancel hd, pow_add, mul_assoc, hm i, mul_zero]
      have h3 : (l : WL l R) ^ (∑ i, m i) * (x * (l : WL l R) ^ k) = 0 := by
        rw [hk]
        have := congrArg (algebraMap _ (WL l R)) h2
        rwa [map_mul, map_pow, map_natCast, map_zero] at this
      exact ((l_unit R _).mul_right_eq_zero.1 h3 |> (l_unit R k).mul_left_eq_zero.1)
    intro x y e
    have := hz (x - y) fun i => by
      have := congrFun e i
      simp only at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.1 this
  · intro y
    choose a k hk using fun i => exists_num (y i)
    have hd : ∀ i, k i ≤ ∑ j, k j := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    obtain ⟨c, hc⟩ := hw.2 fun i => a i * (l : WittVector l (T i)) ^ (∑ j, k j - k i)
    obtain ⟨u, hu⟩ := l_unit (l := l) R (∑ j, k j) |>.exists_right_inv
    refine ⟨algebraMap _ (WL l R) c * u, funext fun i => ?_⟩
    refine (l_unit (l := l) (T i) (∑ j, k j)).mul_right_cancel ?_
    have e1 : awayW (f i) ((l : WL l R) ^ ∑ j, k j) = (l : WL l (T i)) ^ ∑ j, k j := by
      rw [map_pow, map_natCast]
    have e2 : awayW (f i) (algebraMap _ (WL l R) c * u) * (l : WL l (T i)) ^ ∑ j, k j =
        algebraMap _ (WL l (T i)) (WittVector.map (f i) c) := by
      rw [← e1, ← map_mul, mul_assoc, mul_comm u, hu, mul_one, awayW_algebraMap]
    have hci : WittVector.map (f i) c = a i * (l : WittVector l (T i)) ^ (∑ j, k j - k i) := congrFun hc i
    rw [e2, hci, map_mul, ← hk i, map_pow, map_natCast, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hd i)]

end Ring

section Acr

variable {A : PAlg l} {ι : Type} [Fintype ι] {B : ι → PAlg l} (f : ∀ i, A ⟶ B i)

private theorem crystallineAlgebra_algebraMap {C D : PAlg l} (g : C ⟶ D) (w : C.W) :
    (pdOk_hom g).acr0 (algebraMap C.W C.Acr0 w) = algebraMap D.W D.Acr0 (mapW g w) :=
  Subtype.ext (awayW_algebraMap (Hom.f g) w)

private theorem crystallineAlgebra_bijective (h : Function.Bijective fun (a : A.A) i => Hom.f (f i) a) :
    Function.Bijective fun (x : A.Acr0) i => (pdOk_hom (f i)).acr0 x := by
  classical
  have hw := wit_bij (l := l) (fun i => Hom.f (f i)) h
  have ha := away_bij (l := l) (fun i => Hom.f (f i)) h
  constructor
  · intro x y e
    exact Subtype.ext (ha.1 (funext fun i => congrArg Subtype.val (congrFun e i)))
  · have hs : ∀ i (y : WL l (B i).A), y ∈ (B i).Acr0 → ∃ z : A.Acr0, awayW (Hom.f (f i)) z.1 = y := by
      intro i y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        refine ⟨A.dxi0 k, ?_⟩
        have := awayW_dpw (Hom.f (f i)) k (A.isUnit_natCast k.factorial_ne_zero) A.xi
        exact this.trans (congrArg (dpw k) (mapW_xi (f i)))
      | algebraMap w =>
        obtain ⟨c, hc⟩ := hw.2 (Pi.single i w)
        have hci : WittVector.map (Hom.f (f i)) c = w := by simpa using congrFun hc i
        refine ⟨algebraMap A.W A.Acr0 c, ?_⟩
        have := awayW_algebraMap (l := l) (Hom.f (f i)) c
        rw [hci] at this
        exact this
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a * b, map_mul _ _ _⟩
    intro y
    choose z hz using fun i => hs i (y i).1 (y i).2
    choose E hE using fun i => hw.2 (Pi.single i (1 : WittVector l (B i).A))
    refine ⟨∑ i, algebraMap A.W A.Acr0 (E i) * z i, funext fun j => ?_⟩
    simp only
    rw [map_sum, Finset.sum_eq_single j]
    · have e0 : mapW (f j) (E j) = 1 := (congrFun (hE j) j).trans (Pi.single_eq_same _ _)
      have e1 : (pdOk_hom (f j)).acr0 (algebraMap A.W A.Acr0 (E j)) = 1 := by
        rw [crystallineAlgebra_algebraMap, e0]; exact map_one _
      rw [map_mul, e1, one_mul]
      exact Subtype.ext (hz j)
    · intro i _ hij
      have e0 : mapW (f j) (E i) = 0 := (congrFun (hE i) j).trans (Pi.single_eq_of_ne hij.symm _)
      have e1 : (pdOk_hom (f j)).acr0 (algebraMap A.W A.Acr0 (E i)) = 0 := by
        rw [crystallineAlgebra_algebraMap, e0]; exact map_zero _
      rw [map_mul, e1, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

private theorem acr_bij (n : ℕ) (h : Function.Bijective fun (a : A.A) i => Hom.f (f i) a) :
    Function.Bijective fun (x : A.Acr n) i => mapAcr (f i) n x := by
  have h0 := crystallineAlgebra_bijective f h
  constructor
  · have hz : ∀ x : A.Acr n, (∀ i, mapAcr (f i) n x = 0) → x = 0 := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h1 : ∀ i, ∃ c : (B i).Acr0, c * (l : (B i).Acr0) ^ n = (pdOk_hom (f i)).acr0 y := fun i =>
        Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 (hx i))
      choose c hc using h1
      obtain ⟨d, hd⟩ := h0.2 c
      have hy : y = d * (l : A.Acr0) ^ n := h0.1 (funext fun i => by
        have hdi : (pdOk_hom (f i)).acr0 d = c i := congrFun hd i
        simp only
        rw [map_mul, map_pow, map_natCast, hdi, hc i])
      rw [hy]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    intro x y e
    have := hz (x - y) fun i => by
      have := congrFun e i
      simp only at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.1 this
  · intro y
    choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    obtain ⟨d, hd⟩ := h0.2 z
    refine ⟨A.mkAcr n d, funext fun i => ?_⟩
    have hdi : (pdOk_hom (f i)).acr0 d = z i := congrFun hd i
    have : mapAcr (f i) n (A.mkAcr n d) = (B i).mkAcr n ((pdOk_hom (f i)).acr0 d) := rfl
    simp only
    rw [this, hdi]
    exact hz i

end Acr

end UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.acrAdd :
    UpperTheory.Ru.crystallineComparison.AcrAdd := fun _ _ n _ S hS => UpperTheory.Ru.crystallineComparison.acr_bij (fun i => (S.f i).hom) n hS
