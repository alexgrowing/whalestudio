import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FunObj.LocTensor

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV ValuativeRel GlobalTheory.PlaceModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem exists_finsupp {X Y V₁ V₂ ι : Type} [AddCommGroup V₁] [Module ℂ V₁] (S : Submodule ℂ (X → ℂ)) (Q : (Y → ℂ) → Prop)
    (T₁ : (X → ℂ) →ₗ[ℂ] V₁) (T₂ : (Y → ℂ) → V₂) {h : X → ℂ} (hS : h ∈ S) (h0 : T₁ h ≠ 0) (s : Finset ι)
    (a : ι → X → ℂ) (b : ι → Y → ℂ) (ha : ∀ i ∈ s, a i ∈ S) (hb : ∀ i ∈ s, Q (b i)) :
    ∃ (τ : (Unit × V₁) × V₂ →₀ ℂ) (φ₁ : _ → X → ℂ) (φ₂ : _ → Y → ℂ),
      (∀ d ∈ τ.support, (φ₁ d ∈ S ∧ T₁ (φ₁ d) = d.1.2) ∧ Q (φ₂ d) ∧ T₂ (φ₂ d) = d.2) ∧
      ∀ x y, (τ.sum fun d c => c * (φ₁ d x * φ₂ d y)) = ∑ i ∈ s, a i x * b i y := by
  classical
  let P : (X → Y → ℂ) → Prop := fun F => ∃ (τ : (Unit × V₁) × V₂ →₀ ℂ) (φ₁ : _ → X → ℂ) (φ₂ : _ → Y → ℂ),
      (∀ d ∈ τ.support, (φ₁ d ∈ S ∧ T₁ (φ₁ d) = d.1.2) ∧ Q (φ₂ d) ∧ T₂ (φ₂ d) = d.2) ∧
      ∀ x y, (τ.sum fun d c => c * (φ₁ d x * φ₂ d y)) = F x y
  have step : ∀ F, P F → ∀ u ∈ S, T₁ u ≠ 0 → ∀ v, Q v → P fun x y => u x * v y + F x y := by
    rintro F ⟨τ, φ₁, φ₂, h1, h2⟩ u hu hu0 v hv
    have hfin : {c : ℂ | c = 0 ∨ ((((), c • T₁ u), T₂ v) : (Unit × V₁) × V₂) ∈ τ.support}.Finite :=
      (Set.finite_singleton 0).union (τ.support.finite_toSet.preimage fun c _ c' _ e =>
        smul_left_injective ℂ hu0 (congrArg (fun d : (Unit × V₁) × V₂ => d.1.2) e))
    obtain ⟨c, hc⟩ := hfin.exists_notMem
    simp only [Set.mem_setOf_eq, not_or] at hc
    set d₀ : (Unit × V₁) × V₂ := (((), c • T₁ u), T₂ v) with hd
    refine ⟨Finsupp.single d₀ c⁻¹ + τ, Function.update φ₁ d₀ (c • u), Function.update φ₂ d₀ v, fun d hd' => ?_, fun x y => ?_⟩
    · by_cases e : d = d₀
      · rw [e, Function.update_self, Function.update_self]
        exact ⟨⟨S.smul_mem _ hu, map_smul _ _ _⟩, hv, rfl⟩
      · rw [Function.update_of_ne e, Function.update_of_ne e]
        refine h1 d ?_
        simpa [Finsupp.single_eq_of_ne e] using hd'
    · rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finsupp.sum_single_index (zero_mul _),
        Function.update_self, Function.update_self]
      beta_reduce
      rw [← h2]
      congr 1
      · rw [Pi.smul_apply, smul_eq_mul, mul_assoc c, inv_mul_cancel_left₀ hc.1]
      · refine Finsupp.sum_congr fun d hd' => ?_
        have e : d ≠ d₀ := fun e => hc.2 (e ▸ hd')
        rw [Function.update_of_ne e, Function.update_of_ne e]
  change P fun x y => ∑ i ∈ s, a i x * b i y
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp, by simp⟩
  | insert i s hi ih =>
    have ih' := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)) fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have h1 := ha i (Finset.mem_insert_self _ _)
    have h2 := hb i (Finset.mem_insert_self _ _)
    simp only [Finset.sum_insert hi]
    by_cases e : T₁ (a i) = 0
    · have := step _ (step _ ih' (-h) (neg_mem hS) (by rwa [map_neg, neg_ne_zero]) _ h2) (a i + h) (add_mem h1 hS)
        (by rwa [map_add, e, zero_add]) _ h2
      convert this using 3
      simp only [Pi.add_apply, Pi.neg_apply]
      ring
    · exact step _ ih' _ h1 e _ h2

theorem exists_cosets {G Y : Type} [AddCommGroup G] (Λ H : AddSubgroup G) {k : ℕ} (tf : Function.Injective fun t : G => k • t)
    {R : Set G} (hR : R.Finite) (hR' : ∀ t ∈ Λ ⊓ H, ∃ r ∈ R, ∃ u ∈ Λ ⊓ H, t = r + (k * k) • u) (F : G → Y → ℂ)
    (h1 : ∀ u ∈ Λ, ∀ t y, F (t + k • u) y = F t y) (h2 : ∀ t y, t ∈ H → F t y ≠ 0 → k • t ∈ Λ) :
    ∃ (ι : Type) (s : Finset ι) (a : ι → G → ℂ) (r : ι → G),
      (∀ i ∈ s, (∀ t, a i t ≠ 0 → t ∈ H ∧ k • t ∈ Λ) ∧ ∀ u ∈ Λ ⊓ H, ∀ t, a i (t + k • u) = a i t) ∧
      ∀ t y, t ∈ H → F t y = ∑ i ∈ s, a i t * F (r i) y := by
  classical
  let K := (Λ ⊓ H).map (nsmulAddMonoidHom k)
  have hP : ({t | t ∈ H ∧ k • t ∈ Λ} ∩ (fun t : G => k • t) ⁻¹' R).Finite := (hR.preimage tf.injOn).inter_of_right _
  refine ⟨G ⧸ K, hP.toFinset.image QuotientAddGroup.mk, fun q t => if QuotientAddGroup.mk t = q then 1 else 0,
    Quotient.out, fun q hq => ?_, fun t y ht => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨⟨p1, p2⟩, -⟩ := hP.mem_toFinset.1 hp
    refine ⟨fun t ht => ?_, fun u hu t => ?_⟩
    · obtain ⟨u, hu, h⟩ := QuotientAddGroup.eq.1 (of_not_not fun h => ht (if_neg h) : _ = _).symm
      obtain rfl : t = p + k • u := by rw [show k • u = _ from h]; abel
      exact ⟨add_mem p1 (nsmul_mem hu.2 _), by rw [smul_add]; exact add_mem p2 (nsmul_mem (nsmul_mem hu.1 _) _)⟩
    · beta_reduce
      rw [QuotientAddGroup.mk_add_of_mem t (show k • u ∈ K from ⟨u, hu, rfl⟩)]
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]
    split_ifs with h
    · obtain ⟨⟨_, u, hu, rfl⟩, h'⟩ := QuotientAddGroup.mk_out_eq_mul K t
      rw [h']
      exact (h1 u hu.1 t y).symm
    · by_contra h0
      obtain ⟨r, hr, u, hu, h'⟩ := hR' _ ⟨h2 t y ht h0, nsmul_mem ht k⟩
      refine h (Finset.mem_image.2 ⟨t - k • u, hP.mem_toFinset.2 ⟨⟨sub_mem ht (nsmul_mem hu.2 _), ?_⟩, ?_⟩, ?_⟩)
      · rw [smul_sub]
        exact sub_mem (h2 t y ht h0) (nsmul_mem (nsmul_mem hu.1 _) _)
      · change k • (t - k • u) ∈ R
        rwa [smul_sub, h', smul_smul, add_sub_cancel_right]
      · rw [sub_eq_add_neg]
        exact QuotientAddGroup.mk_add_of_mem t (neg_mem ⟨_, hu, rfl⟩)

variable {D : D7}

def sbSpace {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : Submodule ℂ (Mx D m n → ℂ) where
  carrier := {Φ | IsSBHalf e Λ Φ}
  zero_mem' := ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩
  smul_mem' c Φ := by
    rintro ⟨h1, k, hk, h2, h3⟩
    exact ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k, hk, fun u hu hu' t => congrArg (c * ·) (h2 u hu hu' t),
      fun t ht => h3 t (right_ne_zero_of_mul ht)⟩
  add_mem' := by
    rintro Φ Φ' ⟨h1, k, hk, h2, h3⟩ ⟨h1', k', hk', h2', h3'⟩
    have hh : ∀ (l : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (l • u) := fun l u hu i j => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu]
    have ho : ∀ t, (Φ + Φ') t ≠ 0 → Φ t ≠ 0 ∨ Φ' t ≠ 0 := fun t ht => by
      by_contra! h
      exact ht (by rw [Pi.add_apply, h.1, h.2, add_zero])
    refine ⟨fun t ht => (ho t ht).elim (h1 t) (h1' t), k * k', mul_pos hk hk', fun u hu hu' t => ?_, fun t ht => ?_⟩
    · rw [Pi.add_apply, Pi.add_apply, ← h2 _ (nsmul_mem hu k') (hh _ _ hu') t, ← h2' _ (nsmul_mem hu k) (hh _ _ hu') t,
        smul_smul, smul_smul, mul_comm k' k]
    · rcases ho t ht with h | h
      · rw [mul_comm, mul_smul]; exact nsmul_mem (h3 t h) _
      · rw [mul_smul]; exact nsmul_mem (h3' t h) _

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_sb (hS : ΛS.FG) (hT : ΛT.FG) {e : AE D} (he : e * e = e) {Y : Type} (F : WO S T → Y → ℂ) {k : ℕ} (hk : 0 < k)
    (h1 : ∀ u ∈ latO S T ΛS ΛT fun _ => True, ∀ t y, F (t + k • u) y = F t y)
    (h2 : ∀ t y, IsHalf e t → F t y ≠ 0 → k • t ∈ latO S T ΛS ΛT fun _ => True) :
    ∃ (ι : Type) (s : Finset ι) (a : ι → WO S T → ℂ) (r : ι → WO S T),
      (∀ i ∈ s, IsSBHalf e (latO S T ΛS ΛT fun _ => True) (a i)) ∧ ∀ t y, IsHalf e t → F t y = ∑ i ∈ s, a i t * F (r i) y := by
  obtain ⟨R, hR, hR'⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS hT (fun _ => True) (k * k) (mul_pos hk hk)
  have tf : Function.Injective fun t : WO S T => k • t := fun x y h => Matrix.ext fun i j =>
    sub_eq_zero.1 (GlobalTheory.PlaceVec.natCast_mul_eq_zero k _ hk (by
      rw [mul_sub, ← nsmul_eq_mul, ← nsmul_eq_mul]
      exact sub_eq_zero.2 (congrFun (congrFun h i) j)))
  obtain ⟨ι, s, a, r, h3, h4⟩ := exists_cosets _ (half S T e) tf (hR.image fun r => e • r) (fun t ht => by
    obtain ⟨r, hr, u, hu, htr⟩ := hR' t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])) u hu,
      (mem_half S T).2 (by rw [smul_smul, he])⟩, ?_⟩
    rw [← (mem_half S T).1 ht.2, htr, smul_add, smul_comm e (k * k) u]) F h1 fun t y ht => h2 t y ((isHalf_iff S T).2 ht)
  exact ⟨ι, s, a, r, fun i hi => ⟨fun t ht => (isHalf_iff S T).2 ((h3 i hi).1 t ht).1, k, hk,
    fun u hu hu' => (h3 i hi).2 u ⟨hu, (isHalf_iff S T).1 hu'⟩, fun t ht => ((h3 i hi).1 t ht).2⟩,
    fun t y ht => h4 t y ((isHalf_iff S T).1 ht)⟩

def locM {a b : ℕ} (β : GL (Fin a) (Formalism.IndefR.Lev.EAf D)) (β' : GL (Fin b) (Formalism.IndefR.Lev.EAf D)) (w : Pl D.host.E)
    (x : Mx D a b) : Matrix (Fin a) (Fin b) (Kw w) :=
  ((loc w β)⁻¹).val * (x.map fun z => cpt w (toEAf D z)) * (loc w β').val

theorem locM_eq {a b : ℕ} (β : GL (Fin a) (Formalism.IndefR.Lev.EAf D)) (β' : GL (Fin b) (Formalism.IndefR.Lev.EAf D)) (w : Pl D.host.E)
    (x : Mx D a b) : locM β β' w x = ((β⁻¹).val * x.map (toEAf D) * β'.val).map (cpt w) := by
  rw [Matrix.map_mul, Matrix.map_mul, locM, ← map_inv]
  rfl

theorem locM_add {a b : ℕ} (β : GL (Fin a) (Formalism.IndefR.Lev.EAf D)) (β' : GL (Fin b) (Formalism.IndefR.Lev.EAf D)) (w : Pl D.host.E)
    (x y : Mx D a b) : locM β β' w (x + y) = locM β β' w x + locM β β' w y := by
  rw [locM, locM, locM, ← Matrix.add_mul, ← Matrix.mul_add]
  congr 2
  exact Matrix.ext fun i j => ((cpt w).comp (toEAf D)).map_add _ _

theorem cpt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∉ P) :
    cpt Q (toEAf D e) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, map_sum]
  exact Finset.sum_eq_zero fun P' hP => (cpt_of_isIdemAt (hes P' hP)).2 Q fun h => hQ (h ▸ hP)

theorem exists_mult (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {e : AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (β : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    (β' : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (n : Pl D.host.E → ℕ) : ∃ k : ℕ, 0 < k ∧
      (∀ u ∈ latO S T ΛS ΛT fun _ => True, ∀ w ∈ P, GivenAdm.CongM (unifAt w ^ n w) (locM β β' w (k • u))) ∧
      ∀ x : WO S T, IsHalf e x → (∀ w ∈ P, ∀ i j, locM β β' w x i j ∈ 𝒪[Kw w]) → k • x ∈ latO S T ΛS ΛT fun _ => True := by
  obtain ⟨k₁, hk₁, h₁⟩ := GlobalTheory.PlaceVec.exists_nsmul_mul_int (β⁻¹).val β'.val
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.exists_nsmul_mul_int β.val (β'⁻¹).val
  obtain ⟨k₃, hk₃, h₃⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT
  obtain ⟨N, hN, hP⟩ := GlobalTheory.PlaceVec.exists_nat_mem_places P
  refine ⟨N ^ P.sup n * (k₄ * k₂) * (k₁ * k₃), by positivity, fun u hu w hw i j => ?_, fun x hx hi => ?_⟩
  · have h1 := GlobalTheory.PlaceVec.isIntM_nsmul (h₁ _ (h₃ u hu)) (k₄ * k₂) i j
    have h2 : locM β β' w ((N ^ P.sup n * (k₄ * k₂) * (k₁ * k₃)) • u) i j =
        (N : Kw w) ^ P.sup n * cpt w (((k₄ * k₂) • k₁ • ((β⁻¹).val * k₃ • u.map (toEAf D) * β'.val)) i j) := by
      rw [locM_eq, GlobalTheory.PlaceVec.map_toEAf_nsmul, mul_assoc, mul_smul, mul_smul, mul_smul k₁, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_apply, Matrix.smul_apply, map_nsmul,
        nsmul_eq_mul, Nat.cast_pow]
    have h3 : valuation (Kw w) (N : Kw w) ≤ valuation (Kw w) (unifAt w : Kw w) := by
      rw [isUnif_unifAt w, le_uniformizer_iff]
      refine (Good.isEquiv_Kw w).lt_one_iff_lt_one.2 ?_
      have := (w.valuation_lt_one_iff_mem (K := D.host.E) (N : 𝓞 D.host.E)).2 (hP w hw)
      rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
      simpa using this
    have h4 : valuation (Kw w) (unifAt w : Kw w) ≤ 1 := (isUnif_unifAt w).mem
    rw [h2, map_mul, map_pow, Units.val_pow_eq_pow_val, map_pow]
    exact (mul_le_of_le_one_right' ((Good.isEquiv_Kw w).le_one_iff_le_one.2 ((mem_OA_iff _).1 h1 w))).trans
      ((pow_le_pow_left₀ zero_le h3 _).trans (pow_le_pow_right_of_le_one' h4 (Finset.le_sup hw)))
  · have h1 : IsIntM ((β⁻¹).val * x.map (toEAf D) * β'.val) := fun i j => (mem_OA_iff _).2 fun Q => by
      change (((β⁻¹).val * x.map (toEAf D) * β'.val).map (cpt Q)) i j ∈ _
      rw [← locM_eq]
      by_cases hQ : Q ∈ P
      · exact (Good.isEquiv_Kw Q).le_one_iff_le_one.1 (hi Q hQ i j)
      · have : (x.map fun z => cpt Q (toEAf D z)) = 0 := Matrix.ext fun i j => by
          rw [Matrix.map_apply, ← hx i j, RingHom.map_mul, RingHom.map_mul, cpt_idemSum he hQ, zero_mul, Matrix.zero_apply]
        rw [locM, this, Matrix.mul_zero, Matrix.zero_mul]
        exact zero_mem _
    have h2 := h₂ _ h1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      ← GlobalTheory.PlaceVec.map_toEAf_nsmul] at h2
    have := h₄ (k₂ • x) (GlobalTheory.PlaceVec.half_infPart (GlobalTheory.PlaceVec.idemSum_infPart he)
      (nsmul_mem ((isHalf_iff S T).1 hx) _)) h2
    rw [mul_right_comm, mul_smul, mul_smul k₄]
    exact nsmul_mem this _

theorem exists_model {ψ : AddChar (AF D.host.F) ℂ} {θ sS sT} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {f₀ : WO S T → ℂ} (h₀ : IsVacO ψ θ S T sS sT ΛS ΛT f₀) :
    ∃ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), Tm (halfInd e (latO S T ΛS ΛT fun _ => True)) ≠ 0 ∧
      ∀ φ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) φ →
        IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ φ (Tm φ) := by
  obtain ⟨Tm, h⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ h₀.1 _ _ _ _ hS hT _ e he _ h₀.2.theta h₀.2.lat).1
  refine ⟨Tm, fun h0 => ?_, fun φ hφ => ⟨⟨Tm, h⟩, fun T' h' => GlobalTheory.PlaceVec.placeModel_unique h₀.1 hS hT
    (GlobalTheory.PlaceVec.idemSum_mul_self he) (GlobalTheory.PlaceVec.idemSum_infPart he) h h' hφ⟩⟩
  obtain ⟨⟨p, hp⟩, hn⟩ := h₀.2.norm
  have := hn p hp
  rw [← h.vac, one_smul, h0] at this
  simp [nrm2] at this

theorem exists_tensor {S' T' : HSp D} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ} {θ sS sT sS' sT'}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT') {e : AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {f₀ : WO S T → ℂ} (h₀ : IsVacO ψ θ S T sS sT ΛS ΛT f₀)
    {f₀' : WO S' T' → ℂ} (h₀' : IsVacO ψ θ S' T' sS' sT' ΛS' ΛT' f₀') (β₁ β₂ β₃ β₄) (n : Pl D.host.E → ℕ)
    (F : WO S T → WO S' T' → ℂ)
    (h1 : ∀ x y u v, (∀ w ∈ P, GivenAdm.CongM (unifAt w ^ n w) (locM β₁ β₂ w u)) →
      (∀ w ∈ P, GivenAdm.CongM (unifAt w ^ n w) (locM β₃ β₄ w v)) → F (x + u) (y + v) = F x y)
    (h2 : ∀ x y, F x y ≠ 0 → ∀ w ∈ P, (∀ i j, locM β₁ β₂ w x i j ∈ 𝒪[Kw w]) ∧ ∀ i j, locM β₃ β₄ w y i j ∈ 𝒪[Kw w]) :
    ∃ (τ : (Unit × (WO S T → ℂ)) × (WO S' T' → ℂ) →₀ ℂ) (φ₁ : _ → WO S T → ℂ) (φ₂ : _ → WO S' T' → ℂ),
      (∀ d ∈ τ.support, (IsSBHalf e (latO S T ΛS ΛT fun _ => True) (φ₁ d) ∧
        IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (φ₁ d) d.1.2) ∧
        IsSBHalf e (latO S' T' ΛS' ΛT' fun _ => True) (φ₂ d) ∧
        IsThetaAt ψ (symplO S' T') (heisO ψ S' T') e (latO S' T' ΛS' ΛT' fun _ => True) 1 f₀' (φ₂ d) d.2) ∧
      ∀ x y, IsHalf e x → IsHalf e y → (τ.sum fun d c => c * (φ₁ d x * φ₂ d y)) = F x y := by
  classical
  obtain ⟨T₁, t0, t1⟩ := exists_model hS hT he h₀
  obtain ⟨T₂, -, t2⟩ := exists_model hS' hT' he h₀'
  obtain ⟨k, hk, a1, a2⟩ := exists_mult hS.1 hT.1 he β₁ β₂ n
  obtain ⟨l, hl, b1, b2⟩ := exists_mult hS'.1 hT'.1 he β₃ β₄ n
  have z : ∀ {a b : ℕ} (β β') (w), GivenAdm.CongM (unifAt w ^ n w) (locM β β' w (0 : Mx D a b)) := fun β β' w i j => by
    rw [left_eq_add.1 ((congrArg _ (add_zero 0)).symm.trans (locM_add β β' w 0 0)), Matrix.zero_apply, map_zero]
    exact zero_le
  obtain ⟨ι, s, a, r, ha, hF⟩ := exists_sb hS.1.fg hT.1.fg (GlobalTheory.PlaceVec.idemSum_mul_self he) F hk
    (fun u hu x y => by simpa only [add_zero] using h1 x y _ 0 (a1 u hu) fun w _ => z _ _ w)
    fun x y hx h => a2 x hx fun w hw => (h2 x y h w hw).1
  obtain ⟨τ, φ₁, φ₂, c1, c2⟩ := exists_finsupp (sbSpace e (latO S T ΛS ΛT fun _ => True))
    (IsSBHalf e (latO S' T' ΛS' ΛT' fun _ => True)) T₁ T₂ (GlobalTheory.isSBHalf_halfInd e _) t0 s a
    (fun i y => if IsHalf e y then F (r i) y else 0) ha fun i _ => by
      have hne : ∀ y, (if IsHalf e y then F (r i) y else 0) ≠ 0 → IsHalf e y ∧ F (r i) y ≠ 0 := fun y hy => by
        by_cases h : IsHalf e y
        · exact ⟨h, by rwa [if_pos h] at hy⟩
        · exact absurd (if_neg h) hy
      refine ⟨fun y hy => (hne y hy).1, l, hl, fun u hu hu' y => ?_,
        fun y hy => b2 y (hne y hy).1 fun w hw => (h2 _ y (hne y hy).2 w hw).2⟩
      refine if_congr ?_ (by simpa only [add_zero] using h1 (r i) y 0 _ (fun w _ => z _ _ w) (b1 u hu)) rfl
      rw [isHalf_iff, isHalf_iff]
      exact add_mem_cancel_right (nsmul_mem ((isHalf_iff S' T').1 hu') _)
  refine ⟨τ, φ₁, φ₂, fun d hd => ?_, fun x y hx hy => by simp only [c2, hF x y hx, if_pos hy]⟩
  obtain ⟨⟨d1, d2⟩, d3, d4⟩ := c1 d hd
  exact ⟨⟨d1, d2 ▸ t1 _ d1⟩, d3, d4 ▸ t2 _ d3⟩

variable {T₀ : Type} {L : LevCh D T₀} {sc : Consts} {G : GridData L sc}

theorem prod_coord (B : Frames G) (t : T₀) {X M Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hM : M.1 ≤ D.R.m ∧ M.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) {n : Pl D.host.E → ℕ}
    {Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank M)) (Fin ((locGrid G t w).rank X) ⊕ Fin ((locGrid G t w).rank Y)) (Kw w) → ℂ}
    (hΦ : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w))
    (F : Mx D (G.V (.grid X.1 X.2)).rank (G.V (.grid M.1 M.2)).rank → Mx D (G.V (.grid M.1 M.2)).rank (G.V (.grid Y.1 Y.2)).rank → ℂ)
    (hF : F = fun x₁ x₂ => ∏ w ∈ locPl G t, Φ w (fromCols (B.coord t w hX hM (x₁.map fun a => cpt w (toEAf D a)))
        (B.coord t w hM hY (x₂.map fun a => cpt w (toEAf D a)))ᵀ)) :
    (∀ x y u v, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locM (B.β X.1 X.2) (B.β M.1 M.2) w u)) →
      (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locM (B.β M.1 M.2) (B.β Y.1 Y.2) w v)) → F (x + u) (y + v) = F x y) ∧
    ∀ x y, F x y ≠ 0 → ∀ w ∈ locPl G t, (∀ i j, locM (B.β X.1 X.2) (B.β M.1 M.2) w x i j ∈ 𝒪[Kw w]) ∧
      ∀ i j, locM (B.β M.1 M.2) (B.β Y.1 Y.2) w y i j ∈ 𝒪[Kw w] := by
  subst hF
  have key : ∀ w {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) (x : Mx D _ _) i j,
      B.coord t w hX hY (x.map fun a => cpt w (toEAf D a)) i j = locM (B.β X.1 X.2) (B.β Y.1 Y.2) w x
        (Fin.cast (rank_vertex G t w hX) j) (Fin.cast (rank_vertex G t w hY) i) := fun _ _ _ _ _ _ _ _ => rfl
  refine ⟨fun x y u v hu hv => Finset.prod_congr rfl fun w hw => ?_, fun x y h w hw => ?_⟩
  · refine (congrArg _ (Matrix.ext fun i j => ?_)).trans ((hΦ w hw).2 _
      (fromCols (B.coord t w hX hM (u.map fun a => cpt w (toEAf D a)))
        (B.coord t w hM hY (v.map fun a => cpt w (toEAf D a)))ᵀ) (GivenAdm.mem_matLat_smul.2 ?_))
    · rcases j with j | j <;>
        simp only [Matrix.add_apply, fromCols_apply_inl, fromCols_apply_inr, transpose_apply, key, locM_add]
    · rintro i (j | j)
      · exact hu w hw _ _
      · exact hv w hw _ _
  · have h1 := mem_matLat_stdLat.1 (of_not_not fun h' => Finset.prod_ne_zero_iff.1 h w hw ((hΦ w hw).1 _ h'))
    exact ⟨fun i j => h1 (Fin.cast (rank_vertex G t w hM).symm j) (.inl (Fin.cast (rank_vertex G t w hX).symm i)),
      fun i j => h1 (Fin.cast (rank_vertex G t w hM).symm i) (.inr (Fin.cast (rank_vertex G t w hY).symm j))⟩

variable {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T₀) (i j : Fin D.R.m) {μ₀ : T₀}

theorem exists_hasLocal_small (hL : L.Is μ₀) {e : AE D} (he : IsIdemSum e (locPl G t)) {n : Pl D.host.E → ℕ}
    {Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ}
    (hΦ : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) : ∃ τ : TotT G (routeSmall t i j),
    HasLocal B t e (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
      (IsLocVec W (.mu t i j) e (ρ.vT i j)) (IsLocVec W (.chi i j) e (ρ.vX i j)) τ Φ := by
  have h := prod_coord B t (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩ hΦ _ rfl
  have a := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  exact exists_tensor a (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
    (isSelfDualC_neg (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd) a he (ρ.vT_is t i j i.2.le j.2)
    (ρ.vX_is i j i.2 j.2.le) _ _ _ _ n _ h.1 h.2

theorem exists_hasLocal_big (hL : L.Is μ₀) {e : AE D} (he : IsIdemSum e (locPl G t)) {n : Pl D.host.E → ℕ}
    {Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ}
    (hΦ : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) : ∃ τ : TotT G (routeBig t i j),
    HasLocal B t e (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
      (IsLocVec W (.chi i (j + 1)) e (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) e (ρ.vT (i + 1) j)) τ Φ := by
  have h := prod_coord B t (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ hΦ _ rfl
  have a := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  exact exists_tensor (isSelfDualC_neg a) (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd a he (ρ.vX_is i (j + 1) i.2 j.2)
    (ρ.vT_is t (i + 1) j i.2 j.2) _ _ _ _ n _ h.1 h.2

theorem exists_idemSum_locPl (hL : L.Is μ₀) (G : GridData L sc) (t : T₀) : ∃ e, IsIdemSum e (locPl G t) := by
  refine GlobalTheory.GridIdem.exists_isIdemSum _ (fun w hw => ?_) fun w hw w' hw' h => Good.under_injOn hL G t hw hw' h
  rcases Good.locPl_cases hw with ⟨a, b⟩ | ⟨-, -, b⟩
  · exact b ▸ G.pl.w_split _ a
  · exact exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h.symm)

theorem exists_hasFlip_of_nat (hL : L.Is μ₀) {n : Pl D.host.E → ℕ}
    {Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ}
    (hΦ : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w))
    (hΦ' : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (flipAt W t i j w (n w) (Φ w))) :
    ∃ τ τ', HasFlip B t ρ i j n Φ τ τ' := by
  obtain ⟨e, he⟩ := exists_idemSum_locPl hL G t
  obtain ⟨τ', h'⟩ := exists_hasLocal_small B ρ t i j hL he hΦ
  obtain ⟨τ, h⟩ := exists_hasLocal_big B ρ t i j hL he hΦ'
  exact ⟨τ, τ', e, he, h', h⟩

end GlobalTheory.FunObj.LocTensor

end
