import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotFiniteIntegralClosure

noncomputable section

namespace GlobalTheory.SeriesSupportTest

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial

def plHom (D : D7) (k : Fin 2) (v : D.nd.PlG k) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) →+* MonoidAlgebra ℂ (G0g D.nd) := by
  classical
  exact MonoidAlgebra.mapDomainRingHom ℂ
    (MonoidHom.mulSingle (fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩)

theorem atPlace_eq (D : D7) (k : Fin 2) (v : D.nd.PlG k) (a) : atPlace D k v a = plHom D k v a := rfl

theorem atPlace_central (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (ha : ∀ b, a * b = b * a) :
    atPlace D k v a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
  classical
  rw [Subalgebra.mem_center_iff, atPlace_eq]
  intro b
  set kv : (Σ k : Fin 2, D.nd.PlG k) := ⟨k, v⟩ with hkv
  have hof : ∀ h, plHom D k v (MonoidAlgebra.of ℂ _ h) =
      MonoidAlgebra.of ℂ (G0g D.nd) (Pi.mulSingle kv h) := by
    intro h
    simp [plHom, kv]
  have hcomm : ∀ g' : G0g D.nd, g' kv = 1 → ∀ y,
      Commute (MonoidAlgebra.of ℂ (G0g D.nd) g') (plHom D k v y) := by
    intro g' hg' y
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      rw [hof]
      show _ * _ = _ * _
      rw [← map_mul, ← map_mul]
      congr 1
      funext j
      by_cases hj : j = kv
      · subst hj
        simp [hg']
      · simp [Pi.mulSingle_eq_of_ne hj]
    | add x y hx hy =>
      rw [map_add]
      exact hx.add_right hy
    | smul r x hx =>
      have e : plHom D k v (r • x) = r • plHom D k v x := by
        simp only [plHom, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul]
      rw [e]
      exact hx.smul_right r
  induction b using MonoidAlgebra.induction_on with
  | of g =>
    have hg : g = (Pi.mulSingle kv (g kv) : G0g D.nd) * ((Pi.mulSingle kv (g kv) : G0g D.nd)⁻¹ * g) :=
      (mul_inv_cancel_left _ _).symm
    have h1 : ((Pi.mulSingle kv (g kv) : G0g D.nd)⁻¹ * g : G0g D.nd) kv = 1 := by simp
    have hc : Commute (MonoidAlgebra.of ℂ (G0g D.nd) g) (plHom D k v a) := by
      rw [hg, map_mul, ← hof]
      refine Commute.mul_left ?_ (hcomm _ h1 a)
      exact (Commute.map (ha (MonoidAlgebra.of ℂ _ (g kv))).symm (plHom D k v))
    exact hc.eq
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem exists_acts (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V]
    (cen : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] Module.End ℂ V)
    (k : Fin 2) (v : D.nd.PlG k) (F : V) (hF : F ≠ 0) :
    ∃ f, cen ⟨_, atPlace_central D k v _ (D.ntypes.eSer_central k f)⟩ F ≠ 0 := by
  obtain ⟨S, -, hsum⟩ := D.ntypes.eSer_sum k
  have h1 : (∑ f ∈ S, (⟨atPlace D k v (D.ntypes.eSer k f),
      atPlace_central D k v _ (D.ntypes.eSer_central k f)⟩ :
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 1 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, atPlace_eq, ← map_sum, hsum, map_one,
      OneMemClass.coe_one]
  by_contra hne
  push Not at hne
  apply hF
  calc F = cen 1 F := by rw [map_one]; rfl
    _ = ∑ f ∈ S, cen ⟨atPlace D k v (D.ntypes.eSer k f),
          atPlace_central D k v _ (D.ntypes.eSer_central k f)⟩ F := by
        rw [← h1, map_sum, LinearMap.sum_apply]
    _ = 0 := Finset.sum_eq_zero fun f _ => hne f

theorem exists_onMt (D : D7) (μ j) (k : Fin 2) (v : D.nd.PlG k) (F : D.what₂.Mt μ j) (hF : F ≠ 0) :
    ∃ f, D.ntypes.onMt μ j (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_acts D (D.ntypes.cenMt μ j) k v F hF
  refine ⟨f, ?_⟩
  rw [NTypes.onMt, dif_pos (atPlace_central D k v _ (D.ntypes.eSer_central k f))]
  exact hf

theorem exists_onAmb (D : D7) (μ) (k : Fin 2) (v : D.nd.PlG k) (F : D.what₂.Amb μ) (hF : F ≠ 0) :
    ∃ f, D.ntypes.onAmb μ (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_acts D (D.ntypes.cenAmb μ) k v F hF
  refine ⟨f, ?_⟩
  rw [NTypes.onAmb, dif_pos (atPlace_central D k v _ (D.ntypes.eSer_central k f))]
  exact hf

private theorem exists_equiv_monicOf_of_perm {K : Type} [Field K] (N : ℕ) (π : Equiv.Perm K[X])
    (hπ : ∀ f, ((π f).Monic ∧ (π f).natDegree = N) ↔ (f.Monic ∧ f.natDegree = N)) :
    ∃ e : (Fin N → K) ≃ (Fin N → K), ∀ b, Formalism.CyclotomicNorms.monicOf (e b) = π (Formalism.CyclotomicNorms.monicOf b) := by
  have hm : ∀ b : Fin N → K, (Formalism.CyclotomicNorms.monicOf b).Monic ∧ (Formalism.CyclotomicNorms.monicOf b).natDegree = N :=
    fun b => ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf b, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf b⟩
  have hfw : ∀ b : Fin N → K, (π (Formalism.CyclotomicNorms.monicOf b)).Monic ∧ (π (Formalism.CyclotomicNorms.monicOf b)).natDegree = N :=
    fun b => (hπ _).2 (hm b)
  have hbw : ∀ b : Fin N → K,
      (π.symm (Formalism.CyclotomicNorms.monicOf b)).Monic ∧ (π.symm (Formalism.CyclotomicNorms.monicOf b)).natDegree = N := by
    intro b
    have := hm b
    rw [← Equiv.apply_symm_apply π (Formalism.CyclotomicNorms.monicOf b)] at this
    exact (hπ _).1 this
  have back : ∀ p : K[X], p.Monic → p.natDegree = N →
      Formalism.CyclotomicNorms.monicOf (fun i : Fin N => p.coeff i) = p :=
    fun p hp hd => Formalism.CyclotomicNorms.Sqf.monicOf_coeffs p hp hd
  have cf : ∀ (b : Fin N → K), (fun i : Fin N => (Formalism.CyclotomicNorms.monicOf b).coeff i) = b :=
    fun b => funext fun i => Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt b i
  refine ⟨{ toFun := fun b i => (π (Formalism.CyclotomicNorms.monicOf b)).coeff i
            invFun := fun b i => (π.symm (Formalism.CyclotomicNorms.monicOf b)).coeff i
            left_inv := fun b => ?_
            right_inv := fun b => ?_ }, fun b => back _ (hfw b).1 (hfw b).2⟩
  · show (fun i : Fin N => (π.symm (Formalism.CyclotomicNorms.monicOf fun i : Fin N => (π (Formalism.CyclotomicNorms.monicOf b)).coeff i)).coeff i) = b
    rw [back _ (hfw b).1 (hfw b).2, Equiv.symm_apply_apply, cf]
  · show (fun i : Fin N => (π (Formalism.CyclotomicNorms.monicOf fun i : Fin N => (π.symm (Formalism.CyclotomicNorms.monicOf b)).coeff i)).coeff i) = b
    rw [back _ (hbw b).1 (hbw b).2, Equiv.apply_symm_apply, cf]

private theorem exists_equiv_monicOf_sigma_places (D : D7) [∀ k, Fact (D.host.g k).Prime] (π : ∀ k : Fin 2, Equiv.Perm (ZMod (D.host.g k))[X])
    (mon : ∀ k f, ((π k f).Monic ∧ (π k f).natDegree = D.R.r) ↔ (f.Monic ∧ f.natDegree = D.R.r)) :
    ∃ e : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))) ≃
      (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      ∀ a kv, Formalism.CyclotomicNorms.monicOf (e a kv) = π kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) := by
  choose e he using fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
    exists_equiv_monicOf_of_perm (K := ZMod (D.host.g kv.1)) D.R.r (π kv.1) (mon kv.1)
  exact ⟨Equiv.piCongrRight e, fun a kv => he kv (a kv)⟩

structure Relabel (D : D7) where
  π : ∀ k : Fin 2, Equiv.Perm (ZMod (D.host.g k))[X]
  mon : ∀ k f, ((π k f).Monic ∧ (π k f).natDegree = D.R.r) ↔ (f.Monic ∧ f.natDegree = D.R.r)
  lab : ∀ k f, IsLabel D k (π k f) ↔ IsLabel D k f
  good : ∀ t : Tup2 D, D.ntypes.goodTuple (fun k v => π k (t k v)) ↔ D.ntypes.goodTuple t

def relTypes (D : D7) (P : Relabel D) : NTypes D.naut :=
  { D.ntypes with
    eSer := fun k f => D.ntypes.eSer k (P.π k f)
    eSer_idem := fun k f => D.ntypes.eSer_idem k _
    eSer_central := fun k f => D.ntypes.eSer_central k _
    eSer_orth := fun k f f' h => D.ntypes.eSer_orth k _ _ fun e => h ((P.π k).injective e)
    eSer_zero := fun k f h => D.ntypes.eSer_zero k _ fun h' => h ((P.lab k f).1 h')
    eSer_sum := fun k => by
      obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
      refine ⟨S, hS, ?_⟩
      rw [← hsum]
      refine Finset.sum_equiv (P.π k) (fun f => ?_) fun _ _ => rfl
      rw [hS, hS]; exact (P.lab k f).symm }

theorem relabel_types_e0 (D : D7) (P : Relabel D) : (relTypes D P).e0 = D.ntypes.e0 := by
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  obtain ⟨e, he⟩ := exists_equiv_monicOf_sigma_places D P.π P.mon
  simp only [NTypes.e0]
  congr 2
  funext g
  conv_rhs => rw [← finsum_comp_equiv e]
  congr 1
  funext a
  have hfun : (fun k v => Formalism.CyclotomicNorms.monicOf (e a ⟨k, v⟩)) =
      fun k v => P.π k (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := by
    funext k v
    exact he a ⟨k, v⟩
  have hcond : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (e a ⟨k, v⟩)) ↔
      D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := by
    rw [hfun]
    exact P.good _
  split_ifs with h1 h2 h2
  · exact Finset.prod_congr rfl fun kv _ => by rw [he a kv]; rfl
  · exact absurd (hcond.mpr h1) h2
  · exact absurd (hcond.mp h2) h1
  · rfl

def rel (D : D7) (P : Relabel D) : D7 :=
  { D with
    ntypes := relTypes D P
    nStage_trivialCharacter_compat := by
      unfold NTypes.IdempotentMatchesAction; rw [relabel_types_e0]; exact D.nStage_trivialCharacter_compat
    nStage_trivialCharacter_coeff_eq := by rw [relabel_types_e0]; exact D.nStage_trivialCharacter_coeff_eq
    bc_tie := D.bc_tie
    rbar_tie := D.rbar_tie
    mtpar_tie := D.mtpar_tie }

theorem not_admissible_relabel (D : D7) (P : Relabel D) (h : adm3 D) (μ j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (σ : D.ntypes.Par) (F) (hF : F ∈ D.ntypes.MtPar μ j σ) (h0 : F ≠ 0) (k : Fin 2) (v : D.nd.PlG k)
    (hm : P.π k (D.ntypes.labPar k σ v) ≠ D.ntypes.labPar k σ v) :
    (rel D P).what₂ = D.what₂ ∧ (rel D P).ntypes.e0 = D.ntypes.e0 ∧ ¬ adm3 (rel D P) := by
  refine ⟨rfl, relabel_types_e0 D P, fun hr => hm ?_⟩
  obtain ⟨f0, hf0⟩ := exists_onMt D μ j k v F h0
  have hL : f0 = D.ntypes.labPar k σ v := h.2.1 μ j h1 h2 σ k v f0 F hF hf0
  subst hL
  have hne : D.ntypes.onMt μ j (atPlace D k v (D.ntypes.eSer k
      (P.π k ((P.π k).symm (D.ntypes.labPar k σ v))))) F ≠ 0 := by
    rwa [Equiv.apply_symm_apply]
  have e := hr.2.1 μ j h1 h2 σ k v _ F hF hne
  have e2 := congrArg (P.π k) e
  rw [Equiv.apply_symm_apply] at e2
  exact e2.symm

theorem galois_rel (D : D7) (P : Relabel D) (h : adm3 D)
    (hc : ∀ τ k f, IsLabel D k f → P.π k (labAct D τ k f) = labAct D τ k (P.π k f))
    (τ : ℂ ≃+* ℂ) (k : Fin 2) (f) (hf : IsLabel (rel D P) k f) :
    ((rel D P).ntypes.eSer k f).coeff.mapRange τ (map_zero τ) =
      ((rel D P).ntypes.eSer k (labAct (rel D P) τ k f)).coeff := by
  have hf' : IsLabel D k f := hf
  show (D.ntypes.eSer k (P.π k f)).coeff.mapRange τ (map_zero τ) =
    (D.ntypes.eSer k (P.π k (labAct D τ k f))).coeff
  rw [hc τ k f hf']
  exact h.1 τ k _ ((P.lab k f).2 hf')

def swapRel (D : D7) (a b : ∀ k : Fin 2, (ZMod (D.host.g k))[X]) (ha : ∀ k, IsLabel D k (a k))
    (hb : ∀ k, IsLabel D k (b k)) (ha' : ∀ k, ¬ Squarefree (a k)) (hb' : ∀ k, ¬ Squarefree (b k)) : Relabel D := by
  classical
  have key : ∀ k (Q : (ZMod (D.host.g k))[X] → Prop), (Q (a k) ↔ Q (b k)) → ∀ f,
      Q (Equiv.swap (a k) (b k) f) ↔ Q f := fun k Q hQ f => by
    rw [Equiv.swap_apply_def]; split_ifs with e1 e2
    · rw [e1]; exact hQ.symm
    · rw [e2]; exact hQ
    · rfl
  have fix : ∀ k f, Squarefree f → Equiv.swap (a k) (b k) f = f := fun k f hf =>
    Equiv.swap_apply_of_ne_of_ne (fun e => ha' k (e ▸ hf)) (fun e => hb' k (e ▸ hf))
  exact
  { π := fun k => Equiv.swap (a k) (b k)
    mon := fun k => key k (fun f => f.Monic ∧ f.natDegree = D.R.r)
      (iff_of_true ⟨(ha k).1, (ha k).2.1⟩ ⟨(hb k).1, (hb k).2.1⟩)
    lab := fun k => key k (IsLabel D k) (iff_of_true (ha k) (hb k))
    good := fun t => by
      constructor
      · intro h
        have : (fun k v => Equiv.swap (a k) (b k) (t k v)) = t := by
          funext k v
          exact fix k _ ((key k Squarefree (iff_of_false (ha' k) (hb' k)) _).1 ((h k).1.2.1 v))
        rwa [this] at h
      · intro h
        have : (fun k v => Equiv.swap (a k) (b k) (t k v)) = t := by
          funext k v
          exact fix k _ ((h k).1.2.1 v)
        rwa [this] }

section Dual

variable {K : Type} [Field K]

theorem deg_rev {q : K[X]} (h : q.coeff 0 ≠ 0) : q.reverse.natDegree = q.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h), Nat.sub_zero]

theorem rev_rev {q : K[X]} (h : q.coeff 0 ≠ 0) : q.reverse.reverse = q := by
  show reflect q.reverse.natDegree q.reverse = q
  rw [deg_rev h]
  exact reflect_reflect

theorem coeff_of_dvd {q f : K[X]} (h : q ∣ f) (hf : f.coeff 0 ≠ 0) : q.coeff 0 ≠ 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [mul_coeff_zero] at hf
  exact left_ne_zero_of_mul hf

theorem rev_dvd {q f : K[X]} (h : q ∣ f) : q.reverse ∣ f.reverse := by
  obtain ⟨r, rfl⟩ := h
  rw [reverse_mul_of_domain]
  exact dvd_mul_right _ _

theorem unit_of_rev {q : K[X]} (h : q.coeff 0 ≠ 0) (hu : IsUnit q.reverse) : IsUnit q := by
  have hd : q.reverse.natDegree = 0 := natDegree_eq_of_degree_eq_some (isUnit_iff_degree_eq_zero.mp hu)
  rw [deg_rev h] at hd
  rw [eq_C_of_natDegree_eq_zero hd]
  exact isUnit_C.mpr (Ne.isUnit h)

def dl (f : K[X]) : K[X] := C (f.coeff 0)⁻¹ * f.reverse

theorem dl_lab {N : ℕ} {f : K[X]} (h : f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) :
    (dl f).Monic ∧ (dl f).natDegree = N ∧ (dl f).coeff 0 = (f.coeff 0)⁻¹ := by
  obtain ⟨hm, hd, h0⟩ := h
  have hrd : f.reverse.natDegree = N := by rw [deg_rev h0, hd]
  have hlc : f.reverse.leadingCoeff = f.coeff 0 := by
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0]
  have hc0 : f.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hm.leadingCoeff]
  refine ⟨?_, ?_, ?_⟩
  · show (C (f.coeff 0)⁻¹ * f.reverse).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, hlc, inv_mul_cancel₀ h0]
  · show (C (f.coeff 0)⁻¹ * f.reverse).natDegree = N
    rw [natDegree_C_mul (inv_ne_zero h0), hrd]
  · show (C (f.coeff 0)⁻¹ * f.reverse).coeff 0 = _
    rw [coeff_C_mul, hc0, mul_one]

theorem dl_dl {N : ℕ} {f : K[X]} (h : f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) : dl (dl f) = f := by
  have h3 := (dl_lab h).2.2
  rw [show dl (dl f) = C ((dl f).coeff 0)⁻¹ * (dl f).reverse from rfl, h3, inv_inv,
    show dl f = C (f.coeff 0)⁻¹ * f.reverse from rfl, reverse_mul_of_domain, reverse_C,
    rev_rev h.2.2, ← mul_assoc, ← C_mul, mul_inv_cancel₀ h.2.2, C_1, one_mul]

theorem dvd_dl {q f : K[X]} (h : q ∣ f) : q.reverse ∣ dl f := by
  show q.reverse ∣ C (f.coeff 0)⁻¹ * f.reverse
  exact dvd_mul_of_dvd_right (rev_dvd h) _

theorem ptp_inv (l : ℕ) {L : Type} [Field L] (x : L) :
    Formalism.CyclotomicNorms.primeToPart l x⁻¹ = (Formalism.CyclotomicNorms.primeToPart l x)⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    have key : ∀ n : ℕ, (0 : L) ^ n = ((0 : L) ^ n)⁻¹ := fun n => by
      rcases n with _ | n <;> simp
    unfold Formalism.CyclotomicNorms.primeToPart
    rw [inv_zero]
    exact key _
  · have ho : orderOf x⁻¹ = orderOf x := by
      calc orderOf x⁻¹ = orderOf ((Units.mk0 x hx)⁻¹ : Lˣ) := by
            rw [← orderOf_units, Units.val_inv_eq_inv_val, Units.val_mk0]
        _ = orderOf (Units.mk0 x hx) := orderOf_inv _
        _ = orderOf x := by rw [← orderOf_units, Units.val_mk0]
    unfold Formalism.CyclotomicNorms.primeToPart
    rw [ho, inv_pow]

theorem root_dl {g : ℕ} [Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]} (h : f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar (dl f)) : x⁻¹ ∈ Formalism.CyclotomicNorms.rootsBar f := by
  obtain ⟨hm, hd, h0⟩ := h
  have hdl := dl_lab ⟨hm, hd, h0⟩
  unfold Formalism.CyclotomicNorms.rootsBar at hx ⊢
  have hx2 : eval x ((dl f).map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) = 0 :=
    (mem_roots ((hdl.1.map _).ne_zero)).mp hx
  rw [eval_map] at hx2
  refine (mem_roots ((hm.map _).ne_zero)).mpr ?_
  show eval x⁻¹ (f.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) = 0
  rw [eval_map]
  have hx' : eval₂ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) x f.reverse = 0 := by
    rw [show dl f = C (f.coeff 0)⁻¹ * f.reverse from rfl, eval₂_mul, eval₂_C] at hx2
    exact (mul_eq_zero.mp hx2).resolve_left ((_root_.map_ne_zero _).mpr (inv_ne_zero h0))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [eval₂_at_zero, coeff_zero_reverse, hm.leadingCoeff, map_one] at hx'
    exact one_ne_zero hx'
  let _ := invertibleOfNonzero (inv_ne_zero hx0)
  rw [← eval₂_reverse_eq_zero_iff, invOf_eq_inv, inv_inv]
  exact hx'

private theorem irreducible_reverse_of_coeff_zero_ne_zero {q : K[X]} (h0 : q.coeff 0 ≠ 0) (hq : Irreducible q) :
    Irreducible q.reverse := by
  have hr0 : q.reverse.coeff 0 ≠ 0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hq.ne_zero
  refine irreducible_iff.mpr ⟨fun hu => hq.not_isUnit (unit_of_rev h0 hu), fun a b hab => ?_⟩
  have e : q = a.reverse * b.reverse := by rw [← reverse_mul_of_domain, ← hab, rev_rev h0]
  rcases hq.isUnit_or_isUnit e with hu | hu
  · left
    exact unit_of_rev (coeff_of_dvd (by rw [hab]; exact dvd_mul_right a b) hr0) hu
  · right
    exact unit_of_rev (coeff_of_dvd (by rw [hab]; exact dvd_mul_left b a) hr0) hu

theorem good_dl {N g : ℕ} [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X]) (χ : PP → J → (ZMod g)ˣ)
    (h : Formalism.CyclotomicNorms.IsGood N g f χ) : Formalism.CyclotomicNorms.IsGood N g (fun v => dl (f v)) (fun v j => (χ v j)⁻¹) := by
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  have hdl0 : ∀ v, (dl (f v)).coeff 0 ≠ 0 := fun v => by
    rw [(dl_lab (ha v)).2.2]
    exact inv_ne_zero (ha v).2.2
  refine ⟨fun v => ⟨(dl_lab (ha v)).1, (dl_lab (ha v)).2.1, hdl0 v⟩, fun v => ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq0 : q.coeff 0 ≠ 0 := coeff_of_dvd (dvd_trans (dvd_mul_right q q) hq) (hdl0 v)
    have h2 : q.reverse * q.reverse ∣ f v := by
      have := dvd_dl hq
      rwa [dl_dl (ha v), reverse_mul_of_domain] at this
    exact unit_of_rev hq0 (hb v _ h2)
  · intro ℓ hℓ hB v x hx y hy hxy
    have := hc ℓ hℓ hB v _ (root_dl (ha v) hx) _ (root_dl (ha v) hy) (by rw [ptp_inv, ptp_inv, hxy])
    exact inv_injective this
  · intro ℓ hℓ hg v j x hx heq
    apply hd ℓ hℓ hg v j _ (root_dl (ha v) hx)
    dsimp only at heq
    rw [ptp_inv, heq, Units.val_inv_eq_inv_val, map_inv₀, ptp_inv, inv_inv]
  · intro a ha1 ha2
    obtain ⟨v, hv⟩ := he a ha1 ha2
    refine ⟨v, fun ⟨q, hq, hqd⟩ => hv ⟨q.reverse, ?_, ?_⟩⟩
    · have := dvd_dl hq
      rwa [dl_dl (ha v)] at this
    · rw [deg_rev (coeff_of_dvd hq (hdl0 v)), hqd]
  · obtain ⟨v, q, hirr, hq, hp, h1, h2⟩ := hf
    have hq0 := coeff_of_dvd hq (ha v).2.2
    refine ⟨v, q.reverse, irreducible_reverse_of_coeff_zero_ne_zero hq0 hirr, dvd_dl hq, ?_⟩
    rw [deg_rev hq0]
    exact ⟨hp, h1, h2⟩

end Dual

def dualFun (D : D7) (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  open Classical in if IsLabel D k f then dualLab D k f else f

theorem label_dual (D : D7) (k : Fin 2) {f} (h : IsLabel D k f) : IsLabel D k (dualLab D k f) := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have h' := dl_lab (N := D.R.r) h
  show (dl f).Monic ∧ (dl f).natDegree = D.R.r ∧ (dl f).coeff 0 ≠ 0
  exact ⟨h'.1, h'.2.1, by rw [h'.2.2]; exact inv_ne_zero h.2.2⟩

theorem dualFun_invol (D : D7) (k : Fin 2) : Function.Involutive (dualFun D k) := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro f
  by_cases h : IsLabel D k f
  · have e1 : dualFun D k f = dualLab D k f := by unfold dualFun; rw [if_pos h]
    have e2 : dualFun D k (dualLab D k f) = dualLab D k (dualLab D k f) := by
      unfold dualFun; rw [if_pos (label_dual D k h)]
    rw [e1, e2]
    exact dl_dl (N := D.R.r) h
  · unfold dualFun
    rw [if_neg h, if_neg h]

theorem good_dualFun (D : D7) (t : Tup2 D) (h : D.ntypes.goodTuple t) :
    D.ntypes.goodTuple (fun k v => dualFun D k (t k v)) := by
  unfold NTypes.goodTuple at h ⊢
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2⟩ := h k
  have e : (fun v => dualFun D k (t k v)) = fun v => dl (t k v) := by
    funext v
    unfold dualFun
    rw [if_pos (show IsLabel D k (t k v) from h1.1 v)]
    rfl
  show Formalism.CyclotomicNorms.IsGood _ _ (fun v => dualFun D k (t k v)) _ ∧
    Formalism.CyclotomicNorms.IsGood _ _ (fun v => dualFun D k (t k v)) _
  rw [e]
  exact ⟨by simpa only [inv_inv] using good_dl _ _ h2, good_dl _ _ h1⟩

def dualRel (D : D7) : Relabel D where
  π k := (dualFun_invol D k).toPerm
  mon k f := by
    show ((dualFun D k f).Monic ∧ (dualFun D k f).natDegree = _) ↔ _
    unfold dualFun
    split_ifs with h
    · exact iff_of_true ⟨(label_dual D k h).1, (label_dual D k h).2.1⟩ ⟨h.1, h.2.1⟩
    · rfl
  lab k f := by
    show IsLabel D k (dualFun D k f) ↔ _
    unfold dualFun
    split_ifs with h
    · exact iff_of_true (label_dual D k h) h
    · rfl
  good t := by
    refine ⟨fun h => ?_, good_dualFun D t⟩
    have := good_dualFun D _ h
    have e : (fun k v => dualFun D k (dualFun D k (t k v))) = t := by
      funext k v; exact dualFun_invol D k _
    exact e ▸ this

theorem not_admissible_dual_relabel (D : D7) (h : adm3 D) (μ j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (σ : D.ntypes.Par) (F) (hF : F ∈ D.ntypes.MtPar μ j σ) (h0 : F ≠ 0) (k : Fin 2) (v : D.nd.PlG k)
    (hl : IsLabel D k (D.ntypes.labPar k σ v))
    (hm : dualLab D k (D.ntypes.labPar k σ v) ≠ D.ntypes.labPar k σ v) :
    (rel D (dualRel D)).what₂ = D.what₂ ∧ (rel D (dualRel D)).ntypes.e0 = D.ntypes.e0 ∧
      ¬ adm3 (rel D (dualRel D)) := by
  refine not_admissible_relabel D (dualRel D) h μ j h1 h2 σ F hF h0 k v ?_
  show dualFun D k (D.ntypes.labPar k σ v) ≠ D.ntypes.labPar k σ v
  unfold dualFun
  rw [if_pos hl]
  exact hm

theorem not_admissible_with_ambient_top (D : D7) (μ) (F : D.what₂.Amb μ) (h0 : F ≠ 0) (σ σ' : D.ntypes.Par)
    (k : Fin 2) (v : D.nd.PlG k)
    (hne : dualLab D k (D.ntypes.labPar k σ v) ≠ dualLab D k (D.ntypes.labPar k σ' v)) :
    ¬ adm3 (GlobalTheory.GoodProjectorTest.withAmb D fun _ _ => ⊤) := by
  intro hA
  obtain ⟨f, hf⟩ := exists_onAmb D μ k v F h0
  have hT : F ∈ (⊤ : Submodule ℂ (D.what₂.Amb μ)) := Submodule.mem_top
  have e1 := hA.2.2 μ σ k v f F hT hf
  have e2 := hA.2.2 μ σ' k v f F hT hf
  exact hne (e1.symm.trans e2)

theorem admissible_with_ambient_bot (D : D7) (h : adm3 D) : adm3 (GlobalTheory.GoodProjectorTest.withAmb D fun _ _ => ⊥) := by
  refine ⟨h.1, h.2.1, ?_⟩
  rintro (μ : D.what₂.Tup) σ' k v f (F : D.what₂.Amb μ) hF hne
  have hF' : F ∈ (⊥ : Submodule ℂ (D.what₂.Amb μ)) := hF
  have hF0 : @Eq (D.what₂.Amb μ) F 0 := (Submodule.mem_bot ℂ).mp hF'
  have hne' : D.ntypes.onAmb μ (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 := hne
  exact (hne' (by rw [hF0]; exact map_zero _)).elim

end GlobalTheory.SeriesSupportTest
