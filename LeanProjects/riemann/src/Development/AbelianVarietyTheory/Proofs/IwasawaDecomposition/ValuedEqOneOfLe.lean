import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.TupHecke

section General

variable {L : Type} [Field L] [NumberField L]

abbrev FI (L : Type) [Field L] [NumberField L] : Type := (FiniteAdeleRing (𝓞 L) L)ˣ

def sing (P : HeightOneSpectrum (𝓞 L)) : (P.adicCompletion L)ˣ →* FI L := Units.map (finiteSingle L P)

def cmp (P : HeightOneSpectrum (𝓞 L)) : FI L →* (P.adicCompletion L)ˣ :=
  Units.map { toFun := fun a => a P, map_one' := rfl, map_mul' := fun _ _ => rfl }

variable (L) in

def incl : FI L →* Ideles L := Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

variable (L) in

def finP : Ideles L →* FI L := Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem cmp_val (P : HeightOneSpectrum (𝓞 L)) (u : FI L) :
    (cmp P u : P.adicCompletion L) = (u : FiniteAdeleRing (𝓞 L) L) P := rfl

theorem incl_sing (P : HeightOneSpectrum (𝓞 L)) (x) : incl L (sing P x) = localIdele L P x := rfl

theorem finitePart_incl (u : FI L) : finP L (incl L u) = u := rfl

theorem finitePart_localIdele (P : HeightOneSpectrum (𝓞 L)) (x) : finP L (localIdele L P x) = sing P x := rfl

theorem finitePart_infIdele (w : InfinitePlace L) (x) : finP L (infIdele L w x) = 1 := rfl

open Classical in
theorem cmp_sing_self (P : HeightOneSpectrum (𝓞 L)) (x) : cmp P (sing P x) = x := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) P x P = x
  exact Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) P _ _

open Classical in
theorem cmp_sing_ne {P Q : HeightOneSpectrum (𝓞 L)} (h : P ≠ Q) (x) : cmp P (sing Q x) = 1 := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) Q x P = 1
  exact Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) h _ _

theorem fi_ext {u u' : FI L} (h : ∀ P, cmp P u = cmp P u') : u = u' :=
  Units.ext (FiniteAdeleRing.ext _ fun P => congrArg Units.val (h P))

open Classical in
theorem cmp_prod (T : Finset (HeightOneSpectrum (𝓞 L))) (x : ∀ Q : HeightOneSpectrum (𝓞 L), (Q.adicCompletion L)ˣ)
    (P : HeightOneSpectrum (𝓞 L)) : cmp P (∏ Q ∈ T, sing Q (x Q)) = if P ∈ T then x P else 1 := by
  rw [map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem P h fun Q _ hQ => cmp_sing_ne hQ.symm _, cmp_sing_self]
  · exact Finset.prod_eq_one fun Q hQ => cmp_sing_ne (by rintro rfl; exact h hQ) _

theorem valued_eq_one_of_le {P : HeightOneSpectrum (𝓞 L)} (x : (P.adicCompletion L)ˣ)
    (h : Valued.v (x : P.adicCompletion L) ≤ 1) (h' : Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≤ 1) :
    Valued.v (x : P.adicCompletion L) = 1 := by
  refine le_antisymm h ?_
  have e : Valued.v (x : P.adicCompletion L) * Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact e.symm.le.trans (mul_le_of_le_one_right' h')

theorem finite_nonunit (u : FI L) : {P | ¬ IsUnitAt P (cmp P u)}.Finite := by
  have h1 := Filter.eventually_cofinite.1 (u : FiniteAdeleRing (𝓞 L) L).2
  have h2 := Filter.eventually_cofinite.1 ((u⁻¹ : FI L) : FiniteAdeleRing (𝓞 L) L).2
  refine (h1.union h2).subset fun P hP => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  exact hP (valued_eq_one_of_le _ hn.1 hn.2)

theorem finite_nat {N : ℕ} (hN : 0 < N) :
    {P : HeightOneSpectrum (𝓞 L) | Valued.v (N : P.adicCompletion L) ≠ 1}.Finite := by
  refine (finite_nonunit (Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom
    (Units.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')))).subset fun P hP h => hP ?_
  rw [← map_natCast (algebraMap L (P.adicCompletion L))]
  exact h

def Cong (N : ℕ) (u : FI L) : Prop :=
  ∀ P, IsUnitAt P (cmp P u) ∧ Valued.v ((cmp P u : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)

variable {G : Type} [CommGroup G]

theorem eq_one_of_local {N : ℕ} (hN : 0 < N) (ψ : FI L →* G) (hψ : ∀ u, Cong N u → ψ u = 1) (u : FI L)
    (h : ∀ P, ψ (sing P (cmp P u)) = 1) : ψ u = 1 := by
  classical
  set T := ((finite_nonunit u).union (finite_nat (L := L) hN)).toFinset with hT
  have e : u = (∏ Q ∈ T, sing Q (cmp Q u)) * ((∏ Q ∈ T, sing Q (cmp Q u))⁻¹ * u) := by simp
  rw [e, map_mul, map_prod, Finset.prod_eq_one fun Q _ => h Q, one_mul]
  refine hψ _ fun P => ?_
  rw [map_mul, map_inv, cmp_prod]
  split_ifs with hP
  · simp [IsUnitAt]
  · simp only [hT, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hP
    rw [inv_one, one_mul, hP.2]
    exact ⟨hP.1, Valuation.map_sub_le _ hP.1.le (by simp)⟩

theorem cong_sing {N : ℕ} {P : HeightOneSpectrum (𝓞 L)} {x : (P.adicCompletion L)ˣ} (h : IsUnitAt P x)
    (h' : Valued.v ((x : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)) : Cong N (sing P x) := by
  intro Q
  by_cases e : Q = P
  · subst e
    rw [cmp_sing_self]
    exact ⟨h, h'⟩
  · rw [cmp_sing_ne e]
    simp [IsUnitAt]

theorem local_of_global {N : ℕ} (hN : 0 < N) (ψ : FI L →* G) (hψ : ∀ u, Cong N u → ψ u = 1)
    (P : HeightOneSpectrum (𝓞 L)) (h : ∀ k : Lˣ, ψ (sing P (atFin P k)) = 1) (x : (P.adicCompletion L)ˣ) :
    ψ (sing P x) = 1 := by
  have hx0 : Valued.v (x : P.adicCompletion L) ≠ 0 := by simp
  have hN0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hN
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (mul_ne_zero hx0 hN0)
  have hd : DenseRange (algebraMap L (P.adicCompletion L)) := HeightOneSpectrum.denseRange_algebraMap (K := L) P
  have ho : IsOpen ((fun y : P.adicCompletion L => (x : P.adicCompletion L) - y) ⁻¹'
      {z | Valued.v z ≤ WithZero.exp (-(n : ℤ))}) :=
    (GlobalTheory.Idele.isOpen_valued_le (K := L) P (-(n : ℤ))).preimage (by fun_prop)
  obtain ⟨k, hk⟩ := hd.exists_mem_open ho ⟨x, by simp⟩
  have hk1 : Valued.v ((x : P.adicCompletion L) - algebraMap L _ k) <
    Valued.v (x : P.adicCompletion L) * Valued.v (N : P.adicCompletion L) := lt_of_le_of_lt hk hn
  have hk2 : Valued.v (algebraMap L (P.adicCompletion L) k) = Valued.v (x : P.adicCompletion L) := by
    have := Valuation.map_sub_eq_of_lt_left Valued.v
      (hk1.trans_le (mul_le_of_le_one_right' (GlobalTheory.AdLat.valued_natCast_le_one P N)))
    rwa [sub_sub_cancel] at this
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hk2
    exact hx0 hk2.symm
  have e : x = atFin P (Units.mk0 k hk0) * ((atFin P (Units.mk0 k hk0))⁻¹ * x) := by simp
  have ev : ((atFin P (Units.mk0 k hk0) : (P.adicCompletion L)ˣ) : P.adicCompletion L) = algebraMap L _ k := rfl
  have hk3 : algebraMap L (P.adicCompletion L) k ≠ 0 := by simpa using hk0
  rw [e, map_mul, map_mul, h, one_mul]
  refine hψ _ (cong_sing ?_ ?_)
  · unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ev, map_mul, map_inv₀, hk2, inv_mul_cancel₀ hx0]
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, ev]
    have e2 : (algebraMap L (P.adicCompletion L) k)⁻¹ * x - 1 =
      (algebraMap L (P.adicCompletion L) k)⁻¹ * (x - algebraMap L _ k) := by field_simp
    rw [e2, map_mul, map_inv₀, hk2, inv_mul_le_iff₀ (zero_lt_iff.2 hx0)]
    exact hk1.le

theorem continuous_finP {N : ℕ} (hN : 0 < N) (ψ : FI L →* ℂˣ) (hψ : ∀ u, Cong N u → ψ u = 1) :
    Continuous (ψ.comp (finP L)) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 L)), ∀ P, P ∉ T → Valued.v (N : P.adicCompletion L) = 1 :=
    ⟨(finite_nat (L := L) hN).toFinset, fun P hP => by simpa using hP⟩
  choose n hn using fun P : HeightOneSpectrum (𝓞 L) =>
    GlobalTheory.Idele.exists_exp_neg_lt (GlobalTheory.AdLat.valued_natCast_ne_zero P hN)
  have ho := (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open L).2 T (T.sup n)
  have h1 := ho.mem_nhds (x := (1 : Ideles L)) ⟨one_mem _, fun v _ => by
    have : ((1 : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 := rfl
    rw [this, sub_self, map_zero]
    exact zero_le⟩
  have h2 : (fun _ => (1 : ℂˣ)) =ᶠ[nhds (1 : Ideles L)] (ψ.comp (finP L)) := by
    filter_upwards [h1] with a ha
    have hu : ∀ P, IsUnitAt P (cmp P (finP L a)) := ha.1
    refine (hψ (finP L a) fun P => ⟨hu P, ?_⟩).symm
    by_cases hP : P ∈ T
    · refine le_trans (ha.2 P hP) (le_trans ?_ (hn P).le)
      rw [WithZero.exp_le_exp]
      have := Finset.le_sup (f := n) hP
      omega
    · rw [hT P hP]
      exact Valuation.map_sub_le _ (hu P).le (by simp)
  exact continuous_of_continuousAt_one _ (continuousAt_const.congr h2)

theorem apply_eq_apply_finitePart_of_pow_eq_one [IsTotallyComplex L] (ψ : Ideles L →* G) {n : ℕ} (hn : 0 < n) (h : ∀ a, ψ a ^ n = 1)
    (a : Ideles L) : ψ a = ψ (incl L (finP L a)) := by
  have hroot : ∀ (w : InfinitePlace L) (z : w.Completion), ∃ y, y ^ n = z := fun w z => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (e z) hn
    exact ⟨e.symm y, by rw [← map_pow, hy, e.symm_apply_apply]⟩
  choose y hy using fun w => hroot w ((a : AdeleRing (𝓞 L) L).1 w)
  let Y : AdeleRing (𝓞 L) L := (y, 1)
  have e : Y ^ n = ((a * (incl L (finP L a))⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) := by
    refine Prod.ext (funext fun w => (hy w).trans (mul_one _).symm) ?_
    exact (one_pow n).trans (congrArg Prod.snd a.mul_inv).symm
  have hu : IsUnit Y := (isUnit_pow_iff hn.ne').1 (e ▸ Units.isUnit _)
  obtain ⟨b, hb⟩ := hu
  have e2 : b ^ n = a * (incl L (finP L a))⁻¹ := Units.ext (by rw [Units.val_pow_eq_pow_val, hb, e])
  have := h b
  rwa [← map_pow, e2, map_mul, map_inv, mul_inv_eq_one] at this

theorem eq_self_of_fix (φ : FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L)
    (h1 : ∀ x : L, φ (algebraMap L _ x) = algebraMap L _ x)
    (h2 : ∀ z : FiniteAdeleRing (𝓞 L) L, (∀ P, Valued.v (z P) ≤ 1) → ∀ P, Valued.v (φ z P) ≤ 1)
    (z : FiniteAdeleRing (𝓞 L) L) : φ z = z := by
  rw [← sub_eq_zero]
  refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated L).1 _ fun N hN => ?_
  obtain ⟨x, a, ha, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L N hN).1 z
  refine ⟨φ a - a, fun v => sub_mem (h2 a ha v) (ha v), ?_⟩
  rw [map_add, h1, map_nsmul, smul_sub]
  abel

end General

end GlobalTheory.Mem.TupHecke
