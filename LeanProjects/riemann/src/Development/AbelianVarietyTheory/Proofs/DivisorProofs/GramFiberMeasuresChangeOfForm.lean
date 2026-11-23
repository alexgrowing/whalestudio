import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Classify
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimSys
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraInjectiveClearDenom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.TateCompare
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKGeo.GammaUniq

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem exists_simSys_all {N : ℕ} (hN : 0 < N) (hK : N.Coprime p) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (he : ∀ n q q' z z', e n q q' z → e n q q' z' → z = z') (I₁ I₂ : TateIsoO D k Q act e)
    (hI : ∀ y, I₁.ev N y = I₂.ev N y) :
    ∃ t : SimSys D N N, ∀ n, 0 < n → n.Coprime p → ∀ y, I₂.ev n y = I₁.ev n (t.g n y) := by
  choose g hg using exists_lift I₁ I₂
  choose u hu using exists_mult I₁ I₂
  have hdiv : ∀ {n m : ℕ}, (n * m).Coprime p → n.Coprime p := fun {n m} h =>
    Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) h
  have utow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n] := by
    intro n m hn hm hc
    have h : I₁.ζ n ^ u (n * m) = I₁.ζ n ^ u n := by
      rw [hu n hn (hdiv hc), ← I₂.ζ_pow n m hn hm hc, ← hu _ (Nat.mul_pos hn hm) hc, ← pow_mul, mul_comm (u _) m,
        pow_mul, I₁.ζ_pow n m hn hm hc]
    rwa [pow_eq_pow_iff_modEq, ← (I₁.ζ_prim n hn (hdiv hc)).eq_orderOf] at h
  have gtow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z := by
    intro n m hn hm hc x
    rw [← ev_eq_iff I₁ hn (hdiv hc), hg n hn (hdiv hc), ← I₁.tower n m hn hm hc, hg _ (Nat.mul_pos hn hm) hc,
      I₂.tower n m hn hm hc]
  have sim2 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y,
      (n : ℤ) ∣ 2 * (D.EF (g n x) (g n y) - u n * D.EF x y) := by
    intro n hn hc x y
    have h₁ := I₁.isom n hn hc (g n x) (g n y)
    rw [hg n hn hc, hg n hn hc] at h₁
    have h := he _ _ _ _ _ h₁ (I₂.isom n hn hc x y)
    rw [← hu n hn hc, ← zpow_natCast, ← _root_.zpow_mul] at h
    rw [← (I₁.ζ_prim n hn hc).zpow_eq_one_iff_dvd, mul_sub, _root_.zpow_sub, h,
      show (u n : ℤ) * (2 * D.EF x y) = 2 * (u n * D.EF x y) by ring, mul_inv_cancel]
  refine ⟨{
    g := g
    u := u
    lin := fun n hn hc c x => ?_
    u_cop := fun n hn hc => ?_
    u_tower := utow
    surj := fun n hn hc x => ?_
    inj := fun n hn hc x z h => ?_
    sim := fun n hn hc x y => ?_
    tower := gtow
    one := fun x => ?_ }, fun n hn hc y => (hg n hn hc y).symm⟩
  · rw [← ev_eq_iff I₁ hn hc, hg n hn hc, I₁.lin, I₂.lin, hg n hn hc]
  · rw [← (I₁.ζ_prim n hn hc).pow_iff_coprime hn, hu n hn hc]
    exact I₂.ζ_prim n hn hc
  · obtain ⟨y, hy⟩ := (I₂.onto n hn hc _).1 ((I₁.onto n hn hc _).2 ⟨x, rfl⟩)
    refine ⟨y, ?_⟩
    rw [← ev_eq_iff I₁ hn hc, hg n hn hc, hy]
  · rw [← I₂.ker n hn hc, ← hg n hn hc, h]
    exact I₁.ev_nsmul_self hn hc z
  · by_cases hp : p = 2
    · subst hp
      have hco : IsCoprime (n : ℤ) 2 := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hc
      exact hco.dvd_of_dvd_mul_left (sim2 n hn hc x y)
    · have hc2 : (n * 2).Coprime p :=
        Nat.Coprime.mul_left hc ((Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp))
      have h := sim2 (n * 2) (by omega) hc2 x y
      obtain ⟨z, hz⟩ := gtow n 2 hn two_pos hc2 x
      obtain ⟨w, hw⟩ := gtow n 2 hn two_pos hc2 y
      obtain ⟨a, ha⟩ := (utow n 2 hn two_pos hc2).dvd
      obtain ⟨c, hcc⟩ := h
      rw [hz, hw] at hcc
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at hcc
      push_cast at hcc
      refine ⟨c - D.EF (g n x) w - D.EF z (g n y) - n * D.EF z w - a * D.EF x y, ?_⟩
      have h2 : (2 : ℤ) ≠ 0 := two_ne_zero
      apply mul_left_cancel₀ h2
      linear_combination hcc - 2 * D.EF x y * ha
  · rw [← ev_eq_iff I₁ hN hK, hg N hN hK, hI]

theorem isIntAf_mul {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a * c) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hc v)

theorem isIntAf_intCast (c : ℤ) : IsIntAf (c : AfP p) := fun v => by
  rw [map_intCast]; exact intCast_mem _ c

theorem inAf_mem (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem smul_mem {a : AfP p} (ha : IsIntAf a) {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) : a • z ∈ LaHat D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * c, x, isIntAf_mul ha hc, by rw [TensorProduct.smul_tmul', smul_eq_mul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_mem (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) (hA : ∀ x, A (inAf D x) ∈ LaHat D)
    {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) : A z ∈ LaHat D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = c • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul]
    exact smul_mem hc (hA x)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem eq_zero_of_dvd (a : AfP p) (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ c, IsIntAf c ∧ a = n • c) : a = 0 := by
  have key : ∀ v : AwayP p, AfP.eval v a = 0 := by
    intro v
    by_contra hne
    obtain ⟨l, hl0, hlp, hlv⟩ : ∃ l : ℕ, 0 < l ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
      have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
      have hmax : v.1.asIdeal.IsMaximal := v.1.isMaximal
      have hmp : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
      have hnle : ¬ v.1.asIdeal ≤ Ideal.span {(p : ℤ)} := fun hle => v.2 (hmax.eq_of_le hmp.ne_top hle)
      obtain ⟨x, hx, hxp⟩ := Set.not_subset.1 hnle
      have hxp' : ¬ (p : ℤ) ∣ x := fun hd => hxp (Ideal.mem_span_singleton.2 hd)
      refine ⟨x.natAbs, Int.natAbs_pos.2 (fun h0 => hxp' (h0 ▸ dvd_zero _)), ?_, ?_⟩
      · exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (fun hd => hxp' (Int.natCast_dvd.2 hd))).symm
      · rcases Int.natAbs_eq x with h1 | h1
        · rw [← h1]; exact hx
        · rw [← neg_eq_iff_eq_neg.2 h1]; exact neg_mem hx
    have hlt : Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) < 1 := by
      have e : ((l : ℕ) : v.1.adicCompletion ℚ) = algebraMap ℤ (v.1.adicCompletion ℚ) (l : ℤ) := by simp
      have e2 : Valued.v (algebraMap ℤ (v.1.adicCompletion ℚ) (l : ℤ)) = v.1.valuation ℚ (algebraMap ℤ ℚ (l : ℤ)) := by
        rw [IsScalarTower.algebraMap_apply ℤ ℚ (v.1.adicCompletion ℚ)]
        exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
      rw [e, e2, HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hlv
    have hv0 : Valued.v (AfP.eval v a) ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨j, hj⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hv0)
    obtain ⟨c, hc, e⟩ := h (l ^ j) (pow_pos hl0 j) (Nat.Coprime.pow_left j hlp)
    have hc1 : Valued.v (AfP.eval v c) ≤ 1 := hc v
    have : Valued.v (AfP.eval v a) ≤ Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) ^ j := by
      rw [e, map_nsmul, nsmul_eq_mul, map_mul, Nat.cast_pow, map_pow]
      exact mul_le_of_le_one_right' hc1
    exact absurd hj (not_lt.2 this)
  exact Subtype.ext (funext key)

def basAf {J : Type} (b : Module.Basis J ℤ D.La) : Module.Basis J (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (b.baseChange ℚ).baseChange (AfP p)

theorem basAf_apply {J : Type} (b : Module.Basis J ℤ D.La) (i : J) : basAf b i = inAf D (b i) := by
  simp [basAf, inAf]

theorem isIntAf_repr {J : Type} (b : Module.Basis J ℤ D.La) (i : J) {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) :
    IsIntAf ((basAf b).repr z i) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : (basAf b).repr (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) i = ((b.repr x i : ℤ) : AfP p) * c := by
      simp [basAf, Algebra.smul_def]
    rw [e]
    exact isIntAf_mul (isIntAf_intCast _) hc
  | zero => simpa using isIntAf_intCast (p := p) 0
  | add x y _ _ hx hy =>
    intro v
    rw [map_add, Finsupp.add_apply, map_add]
    exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    intro v
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (hx v)

theorem eq_zero_of_dvd_laHat (z : AfP p ⊗[ℚ] VQ D)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) : z = 0 := by
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  refine (basAf b).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine eq_zero_of_dvd _ fun n hn hc => ?_
  obtain ⟨w, hw, rfl⟩ := h n hn hc
  exact ⟨_, isIntAf_repr b i hw, by rw [map_nsmul, Finsupp.smul_apply]⟩

theorem end_ext {A B : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)} (h : ∀ x, A (inAf D x) = B (inAf D x)) : A = B := by
  have := D.freeLa
  exact (basAf (Module.Free.chooseBasis ℤ D.La)).ext fun i => by rw [basAf_apply, h]

theorem actOn_injective {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hr : Function.Injective rep) (R : Type) [CommRing R] [Algebra ℚ R] :
    Function.Injective (actOn rep R) := by
  have h₁ : Function.Injective (rep.toLinearMap.lTensor R) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hr
  have j := (TensorProduct.isBaseChange ℚ V R).end
  have e : ∀ x, actOn rep R x = j.equiv (rep.toLinearMap.lTensor R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul]
      ext v
      have := (TensorProduct.isBaseChange ℚ V R).endHom_comp_apply (rep c) v
      have e₁ : actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
        rw [Algebra.smul_def]; rfl
      rw [e₁]
      simp at this ⊢
      simp [this, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y h
  rw [e, e] at h
  exact h₁ (j.equiv.injective h)

variable {G : HTGroup p} (L : Link D G)

theorem actG_injective : Function.Injective L.actG := by
  intro g h e
  have := D.finLa
  have h₁ : (g.1.1 : AfP p ⊗[ℚ] G.C) = h.1.1 := actOn_injective L.rep L.rep_inj (AfP p) e
  have h₁' : g.1.1 = h.1.1 := Units.ext h₁
  refine Subtype.ext (Prod.ext h₁' (Units.ext ?_))
  have hg := mem_uGroup.1 g.2
  have hh := mem_uGroup.1 h.2
  rw [h₁, hh] at hg
  have hinj : Function.Injective (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    Algebra.TensorProduct.includeLeft_injective (S := ℚ) (algebraMap ℚ G.C).injective
  exact (hinj hg).symm

theorem inAf_add (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := by
  simp only [inAf, TensorProduct.tmul_add]

end GlobalTheory.LKGeo.GammaUniq
