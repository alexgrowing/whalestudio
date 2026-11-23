import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers

noncomputable section

namespace GlobalTheory.EX.DQ.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB NumberField

theorem goodAllAt_iff (D : D7) (C : NChoice D) (I : TwIn D) : GoodAllAt D C I ↔ GlobalTheory.TwAll.TwGoodAtAll D C I := by
  have h : ∀ (a : ℤ) (l : ℕ), Nat.Coprime a.natAbs l ↔ IsCoprime a (l : ℤ) := fun a l => by
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  simp only [GoodAllAt, GlobalTheory.TwAll.TwGoodAtAll, h]

theorem exps (D : D7) (i : D.ntw.Tw) :
    ¬ Nat.Coprime (0 : ℤ).natAbs (D.ntw.l i) ∧ Nat.Coprime (-1 : ℤ).natAbs (D.ntw.l i) :=
  ⟨by simpa using (D.ntw.lPrime i).out.ne_one, by simp⟩

theorem tup_setDiv (D : D7) (N) (h) : TupUsedAt (setDiv D N h) ↔ TupUsedAt D := Iff.rfl
theorem mt_setDiv (D : D7) (N) (h) : MtStableAt (setDiv D N h) ↔ MtStableAt D := Iff.rfl
theorem conj_setDiv (D : D7) (O : Obj D) (N) (h) : TwConjAt (setDiv D N h) (O.tr N h).nch ↔ TwConjAt D O.nch := Iff.rfl
theorem av_setDiv (D : D7) (N) (h) : AvRec (setDiv D N h) = AvRec D := rfl
theorem ok_setDiv (D : D7) (N) (h) (I : TwIn D) (i) : TwIn.Ok (D := setDiv D N h) ⟨{I.E with}, I.N0, I.S⟩ i ↔ I.Ok i := Iff.rfl
set_option maxHeartbeats 2000000 in
theorem one_setDiv (D : D7) (N) (h) (I : TwIn D) (i b Q k ψ) : TwGoodOne (setDiv D N h) ⟨{I.E with}, I.N0, I.S⟩ i b Q k ψ ↔ TwGoodOne D I i b Q k ψ := Iff.rfl

theorem tup_finite {D : D7} (h : TupUsedAt D) (hf : {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite) : Finite D.what₂.Tup := by
  have : (Set.univ : Set D.what₂.Tup) ⊆ insert D.what₂.mu0 (insert D.what₂.muStar (insert D.what₂.muStar'
      (D.what₂.muAt '' {w | D.what₂.muAt w ≠ D.what₂.mu0}))) := by
    intro μ _
    rcases h μ with h | h | h | ⟨w, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · by_cases h0 : D.what₂.muAt w = D.what₂.mu0
      · exact Or.inl (h.trans h0)
      · exact Or.inr (Or.inr (Or.inr ⟨w, h0, h.symm⟩))
  exact Set.finite_univ_iff.1 ((((hf.image _).insert _).insert _).insert _ |>.subset this)

section Lat

variable {O L V : Type} [CommRing O] [Field L] [NumberField L] [AddCommGroup V] [Module ℂ V] {φ : O →+* ℂ}

theorem mem_carrier_iff (M : Rows.OLat O φ V) (x : V) :
    x ∈ M.carrier ↔ x ∈ AddSubgroup.closure {y | ∃ c : O, ∃ v ∈ M.gen, y = φ c • v} := by
  classical
  constructor
  · rintro ⟨c, rfl⟩
    exact sum_mem fun v hv => AddSubgroup.subset_closure ⟨c v, v, hv, rfl⟩
  · intro hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, v, hv, rfl⟩ := hy
      refine ⟨Pi.single v c, ?_⟩
      rw [Finset.sum_eq_single v (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (fun h => absurd hv h)]
      simp
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, rfl⟩ := hb
      exact ⟨c + d, by simp [add_smul, Finset.sum_add_distrib]⟩
    | neg a _ ha =>
      obtain ⟨c, rfl⟩ := ha
      exact ⟨-c, by simp⟩

open Classical in

def sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) : Rows.OLat O φ V where
  gen := (Finset.univ ×ˢ M.gen).image fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2
  span_top := by
    rw [eq_top_iff, ← M.span_top, Submodule.span_le]
    intro v hv
    obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 L)) := (RingOfIntegers.basis L).index_nonempty
    have h0 : σ (RingOfIntegers.basis L i : L) ≠ 0 := by
      rw [map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
      exact (RingOfIntegers.basis L).ne_zero i
    have := Submodule.smul_mem (Submodule.span ℂ (((Finset.univ ×ˢ M.gen).image
      fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2 : Finset V) : Set V)) (σ (RingOfIntegers.basis L i : L))⁻¹
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, v), by simpa using hv, rfl⟩)))
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this

theorem smul_mem_sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) (a : 𝓞 L) (c : O) {v : V} (hv : v ∈ M.gen) :
    (φ c * σ (a : L)) • v ∈ (sat σ M).carrier := by
  classical
  rw [mem_carrier_iff]
  have e : (φ c * σ (a : L)) • v = ∑ i, φ (((RingOfIntegers.basis L).repr a i : ℤ) * c) •
      σ (RingOfIntegers.basis L i : L) • v := by
    conv_lhs => rw [← (RingOfIntegers.basis L).sum_repr a]
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  rw [e]
  exact sum_mem fun i _ => AddSubgroup.subset_closure
    ⟨_, _, Finset.mem_image.2 ⟨(i, v), by simpa using hv, rfl⟩, rfl⟩

theorem subset_sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) : M.carrier ⊆ (sat σ M).carrier := by
  intro x hx
  rw [mem_carrier_iff] at hx ⊢
  refine (AddSubgroup.closure_le _).2 ?_ hx
  rintro _ ⟨c, v, hv, rfl⟩
  have := smul_mem_sat σ M 1 c hv
  rw [mem_carrier_iff] at this
  simpa using this

theorem sat_stable (σ : L →+* ℂ) (M : Rows.OLat O φ V) (a : 𝓞 L) : ∀ y ∈ (sat σ M).carrier,
    σ (a : L) • y ∈ (sat σ M).carrier := by
  classical
  intro y hy
  rw [mem_carrier_iff] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, w, hw, rfl⟩ := hy
    obtain ⟨⟨i, v⟩, hv, rfl⟩ := Finset.mem_image.1 hw
    have := smul_mem_sat σ M (a * RingOfIntegers.basis L i) c (Finset.mem_product.1 hv).2
    convert this using 1
    simp [smul_smul, mul_left_comm]
  | zero => rw [mem_carrier_iff]; simp
  | add x y _ _ hx hy => rw [mem_carrier_iff] at *; rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mem_carrier_iff] at *; rw [smul_neg]; exact neg_mem hx

theorem range_of_stable (σ : L →+* ℂ) (M : Rows.OLat O φ V) (hli : LinearIndependent ℂ (fun v : M.gen => (v : V)))
    {v : V} (hv : v ∈ M.gen) (a : 𝓞 L) (h : ∀ y ∈ M.carrier, σ (a : L) • y ∈ M.carrier) : σ (a : L) ∈ Set.range φ := by
  classical
  have h1 : v ∈ M.carrier := (mem_carrier_iff M v).2 (AddSubgroup.subset_closure ⟨1, v, hv, by simp⟩)
  obtain ⟨c, hc⟩ := h v h1
  have := Fintype.linearIndependent_iff.1 hli (fun w => φ (c w) - (Pi.single v (σ (a : L)) : V → ℂ) w) (by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [Finset.sum_coe_sort M.gen (fun w => φ (c w) • w), ← hc,
      Finset.sum_coe_sort M.gen (fun w => (Pi.single v (σ (a : L)) : V → ℂ) w • w),
      Finset.sum_eq_single v (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (fun h => absurd hv h)]
    simp) ⟨v, hv⟩
  exact ⟨c v, by simpa [sub_eq_zero] using this⟩

end Lat

set_option maxHeartbeats 4000000 in

def setMt (D : D7) (M : ∀ μ, Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (D.what₂.Amb μ)) : D7 :=
  { D with
    what₂ := { D.what₂ with Mtilde := M }
    nd := { D.nd with }
    ntw := { D.ntw with }
    naut := { D.naut with }
    nbc := { D.nbc with }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with }
    nth := { D.nth with } }

def satRec (D : D7) : D7 := setMt D fun μ => sat D.what₂.embLL (D.what₂.Mtilde μ)

theorem mtStable_sat (D : D7) : MtStableAt (satRec D) :=
  fun (μ : D.what₂.Tup) a y hy => sat_stable D.what₂.embLL (D.what₂.Mtilde μ) a y hy

theorem tup_setMt (D : D7) (M) : TupUsedAt (setMt D M) ↔ TupUsedAt D := Iff.rfl

theorem qd_sat (D : D7) (h : TupUsedAt D) (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0)
    (O : Obj (satRec D)) : QD (satRec D) O :=
  ⟨(tup_setMt D _).2 h, twAllAt_of_untwisted _ _ hu, mtStable_sat D⟩

theorem not_mtStable_of_free (D : D7) (μ : D.what₂.Tup)
    (hli : LinearIndependent ℂ (fun v : (D.what₂.Mtilde μ).gen => (v : D.what₂.Amb μ))) (hne : (D.what₂.Mtilde μ).gen.Nonempty)
    (a : 𝓞 D.what₂.LL) (ha : (a : D.what₂.LL) ∉ Set.range D.what₂.OtoLL) : ¬ MtStableAt D := fun h => by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨c, hc⟩ := range_of_stable D.what₂.embLL (D.what₂.Mtilde μ) hli hv a (h μ a)
  exact ha ⟨c, D.what₂.embLL.injective hc⟩

theorem used_muTw {D : D7} (h : TupUsedAt D) (w) : DV.Used D (D.what₂.muTw w) := h _

set_option maxHeartbeats 2000000 in
theorem good_setDiv (D : D7) (O : Obj D) (N) (h) (N0 S) :
    GoodAllAt (setDiv D N h) (O.tr N h).nch ⟨twEOf (O.tr N h).xd, N0, S⟩ ↔ GoodAllAt D O.nch ⟨twEOf O.xd, N0, S⟩ :=
  forall_congr' fun w => forall_congr' fun _ => and_congr (ok_setDiv D N h ⟨twEOf O.xd, N0, S⟩ (O.nch.twI w))
    (forall_congr' fun a => forall_congr' fun _ =>
      one_setDiv D N h ⟨twEOf O.xd, N0, S⟩ (O.nch.twI w) (O.nch.sd w) (O.nch.Q w) (O.nch.k' w) (O.nch.psi' w ^ a))

theorem qd_setDiv (D : D7) (O : Obj D) (N) (h) : QD (setDiv D N h) (O.tr N h) ↔ QD D O :=
  and_congr (tup_setDiv D N h) (and_congr (and_congr (conj_setDiv D O N h)
    (exists_congr fun N0 => exists_congr fun S => good_setDiv D O N h N0 S)) (mt_setDiv D N h))

theorem not_class_of_false {eps : ℝ} (Fm : FamP eps) : ¬ cls7 (fun _ _ => False) Fm := fun h =>
  (Fm.toFamCore.exists_pt 0).elim fun x hx =>
    hx.2.2.2.elim fun i => familyClass_points_satisfy_objectProperty _ Fm h x hx.2.1 i

theorem twGood_of_twAllF {eps : ℝ} {Fm : FamP eps} (h : TwAllF Fm) : TwGood Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨hc, N0, S, hS⟩ := h x hx hx1 i
  exact ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, by simpa using (hS w hw).2 1 (by simp)⟩⟩

theorem duty_of_duty7 {eps : ℝ} {Fm : FamP eps} (h : Duty7 Fm) : DC.Duty Fm :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

end GlobalTheory.EX.DQ.Model

end
