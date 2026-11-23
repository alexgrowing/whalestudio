import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TminusLinApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NatCastInvMemRp

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Classical

section Abstract

variable {Γ A K : Type} [Group Γ] [Field K] [CharZero K] (sm : Γ → A → A)
  (h1 : ∀ a, sm 1 a = a) (hm : ∀ γ γ' a, sm (γ * γ') a = sm γ (sm γ' a))

include h1 hm in
theorem sm_inv_sm (γ : Γ) (a : A) : sm γ⁻¹ (sm γ a) = a := by rw [← hm, inv_mul_cancel, h1]

def fibEquiv (b0 : A) (γ0 : Γ) : {γ : Γ // sm γ b0 = sm γ0 b0} ≃ {γ : Γ // sm γ b0 = b0} where
  toFun γ := ⟨γ0⁻¹ * γ.1, by rw [hm, γ.2, sm_inv_sm sm h1 hm]⟩
  invFun γ := ⟨γ0 * γ.1, by rw [hm, γ.2]⟩
  left_inv γ := Subtype.ext (mul_inv_cancel_left γ0 γ.1)
  right_inv γ := Subtype.ext (inv_mul_cancel_left γ0 γ.1)

include h1 hm in
theorem T_finite (b0 : A) (hfin : Finite {γ : Γ // sm γ b0 = b0}) (B : Finset A) : {γ : Γ | sm γ b0 ∈ B}.Finite := by
  have e : {γ : Γ | sm γ b0 ∈ B} = ⋃ b ∈ B, {γ | sm γ b0 = b} := by
    ext γ
    simp
  rw [e]
  refine Set.Finite.biUnion B.finite_toSet (fun b _ => ?_)
  by_cases h : ∃ γ0, sm γ0 b0 = b
  · obtain ⟨γ0, rfl⟩ := h
    have : Finite {γ : Γ // sm γ b0 = sm γ0 b0} := Finite.of_equiv _ (fibEquiv sm h1 hm b0 γ0).symm
    exact Set.finite_coe_iff.1 this
  · refine Set.finite_empty.subset ?_
    intro γ hγ
    exact (h ⟨γ, hγ⟩).elim

include h1 hm in
theorem orbit_sum_stabilizer (b0 : A) (B : Finset A) (f : A → K) (T : Finset Γ) (hT : ∀ γ, γ ∈ T ↔ sm γ b0 ∈ B) :
    ∑ γ ∈ T, f (sm γ b0) =
      (Nat.card {γ : Γ // sm γ b0 = b0} : K) * ∑ b ∈ B.filter (fun b => ∃ γ, b = sm γ b0), f b := by
  rw [Finset.sum_comp f (fun γ => sm γ b0), Finset.mul_sum]
  have himg : T.image (fun γ => sm γ b0) = B.filter (fun b => ∃ γ, b = sm γ b0) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨(hT γ).1 hγ, γ, rfl⟩
    · rintro ⟨hb, γ, rfl⟩
      exact ⟨γ, (hT γ).2 hb, rfl⟩
  rw [himg]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  obtain ⟨hbB, γ0, rfl⟩ := Finset.mem_filter.1 hb
  rw [nsmul_eq_mul, ← Nat.card_congr (fibEquiv sm h1 hm b0 γ0)]
  congr 2
  refine (Nat.subtype_card _ (fun γ => ?_)).symm
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨(hT γ).2 ?_, h⟩
    rw [h]
    exact hbB

theorem sum_orb (S : A → Prop) (Rp : Finset A) (hex : ∀ a, S a → ∃! a0, a0 ∈ Rp ∧ ∃ γ, a = sm γ a0) (B : Finset A)
    (hB : ∀ b ∈ B, S b) (f : A → K) :
    ∑ b ∈ B, f b = ∑ b0 ∈ Rp, ∑ b ∈ B.filter (fun b => ∃ γ, b = sm γ b0), f b := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  obtain ⟨a0, ⟨h0, hγ⟩, huniq⟩ := hex b (hB b hb)
  rw [Finset.sum_eq_single a0]
  · rw [if_pos hγ]
  · intro c hc hne
    rw [if_neg]
    intro h
    exact hne (huniq c ⟨hc, h⟩)
  · intro h
    exact absurd h0 h

def TT (b0 : A) (hfin : Finite {γ : Γ // sm γ b0 = b0}) (B : Finset A) : Finset Γ :=
  (T_finite sm h1 hm b0 hfin B).toFinset

theorem mem_TT (b0 : A) (hfin : Finite {γ : Γ // sm γ b0 = b0}) (B : Finset A) (γ : Γ) :
    γ ∈ TT sm h1 hm b0 hfin B ↔ sm γ b0 ∈ B := Set.Finite.mem_toFinset _

include h1 hm in

theorem sum_unfold (S : A → Prop) (Rp : Finset A) (hRp : ∀ a ∈ Rp, S a)
    (hex : ∀ a, S a → ∃! a0, a0 ∈ Rp ∧ ∃ γ, a = sm γ a0)
    (hst : ∀ a, S a → 0 < Nat.card {γ : Γ // sm γ a = a}) (B : Finset A) (hB : ∀ b ∈ B, S b) (f : A → K) :
    ∑ b ∈ B, f b = ∑ b0 ∈ Rp.attach, (Nat.card {γ : Γ // sm γ b0.1 = b0.1} : K)⁻¹ *
      ∑ γ ∈ TT sm h1 hm b0.1 (Nat.card_pos_iff.1 (hst b0.1 (hRp b0.1 b0.2))).2 B, f (sm γ b0.1) := by
  rw [sum_orb sm S Rp hex B hB f, ← Finset.sum_attach]
  refine Finset.sum_congr rfl (fun b0 _ => ?_)
  rw [orbit_sum_stabilizer sm h1 hm b0.1 B f _ (mem_TT sm h1 hm b0.1 _ B), ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.2 (hst b0.1 (hRp b0.1 b0.2)).ne'

include h1 hm in

theorem adj (S : A → Prop) (Rp : Finset A) (hRp : ∀ a ∈ Rp, S a)
    (hex : ∀ a, S a → ∃! a0, a0 ∈ Rp ∧ ∃ γ, a = sm γ a0)
    (hst : ∀ a, S a → 0 < Nat.card {γ : Γ // sm γ a = a})
    (R : A → A → Prop) (hR : ∀ γ a b, R a b → R (sm γ a) (sm γ b)) (hRS : ∀ a b, R a b → (S a ↔ S b))
    (up dn : A → Finset A) (hup : ∀ a, S a → ∀ b, b ∈ up a ↔ R a b) (hdn : ∀ b, S b → ∀ a, a ∈ dn b ↔ R a b)
    (φ : A → A → K) (hφ : ∀ γ a b, φ (sm γ a) (sm γ b) = φ a b) :
    ∑ a ∈ Rp, (Nat.card {γ : Γ // sm γ a = a} : K)⁻¹ * ∑ b ∈ up a, φ a b =
      ∑ b ∈ Rp, (Nat.card {γ : Γ // sm γ b = b} : K)⁻¹ * ∑ a ∈ dn b, φ a b := by
  have hL : ∀ a ∈ Rp, (Nat.card {γ : Γ // sm γ a = a} : K)⁻¹ * ∑ b ∈ up a, φ a b =
      ∑ b0 ∈ Rp.attach, (Nat.card {γ : Γ // sm γ a = a} : K)⁻¹ * ((Nat.card {γ : Γ // sm γ b0.1 = b0.1} : K)⁻¹ *
        ∑ γ ∈ TT sm h1 hm b0.1 (Nat.card_pos_iff.1 (hst b0.1 (hRp b0.1 b0.2))).2 (up a), φ a (sm γ b0.1)) := by
    intro a ha
    rw [sum_unfold sm h1 hm S Rp hRp hex hst (up a)
      (fun b hb => (hRS a b ((hup a (hRp a ha) b).1 hb)).1 (hRp a ha)) (φ a), Finset.mul_sum]
  have hRr : ∀ b ∈ Rp, (Nat.card {γ : Γ // sm γ b = b} : K)⁻¹ * ∑ a ∈ dn b, φ a b =
      ∑ a0 ∈ Rp.attach, (Nat.card {γ : Γ // sm γ b = b} : K)⁻¹ * ((Nat.card {γ : Γ // sm γ a0.1 = a0.1} : K)⁻¹ *
        ∑ γ ∈ TT sm h1 hm a0.1 (Nat.card_pos_iff.1 (hst a0.1 (hRp a0.1 a0.2))).2 (dn b), φ (sm γ a0.1) b) := by
    intro b hb
    rw [sum_unfold sm h1 hm S Rp hRp hex hst (dn b)
      (fun a ha => (hRS a b ((hdn b (hRp b hb) a).1 ha)).2 (hRp b hb)) (fun a => φ a b), Finset.mul_sum]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hRr, ← Finset.sum_attach Rp, ← Finset.sum_attach Rp, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  rw [← mul_assoc, ← mul_assoc, mul_comm ((Nat.card {γ : Γ // sm γ a.1 = a.1} : K)⁻¹)]
  congr 1
  refine Finset.sum_nbij' (fun γ => γ⁻¹) (fun γ => γ⁻¹) ?_ ?_ (fun γ _ => inv_inv γ) (fun γ _ => inv_inv γ) ?_
  · intro γ hγ
    rw [mem_TT] at hγ ⊢
    have h2 := hR γ⁻¹ _ _ ((hup a.1 (hRp a.1 a.2) _).1 hγ)
    rw [sm_inv_sm sm h1 hm] at h2
    exact (hdn b.1 (hRp b.1 b.2) _).2 h2
  · intro γ hγ
    rw [mem_TT] at hγ ⊢
    have h2 := hR γ⁻¹ _ _ ((hdn b.1 (hRp b.1 b.2) _).1 hγ)
    rw [sm_inv_sm sm h1 hm] at h2
    exact (hup a.1 (hRp a.1 a.2) _).2 h2
  · intro γ _
    rw [← hφ γ⁻¹ a.1 (sm γ b.1), sm_inv_sm sm h1 hm]

end Abstract

section Conc

open Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf} (C : Level P) (v : Fin P.nV) (i : ℕ)

def upd (L : P.Tup) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) : P.Tup :=
  Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A

theorem upd_self (L : P.Tup) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) : upd v L A v = A :=
  Function.update_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) v A L

theorem upd_ne (L : P.Tup) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) {u : Fin P.nV} (h : u ≠ v) :
    upd v L A u = L u :=
  Function.update_of_ne (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) h A L

theorem upd_inj (L : P.Tup) : Function.Injective (upd v L) := by
  intro A B h
  have := congrFun h v
  rwa [upd_self, upd_self] at this

def Rel (L L1 : P.Tup) : Prop := IsEdge p (P.n' v) i ⟨L v, L1 v⟩ ∧ ∀ u, u ≠ v → L u = L1 u

theorem Rel_smul (γ : C.Γ) (L L1 : P.Tup) (h : Rel v i L L1) : Rel v i (C.smul γ L) (C.smul γ L1) := by
  refine ⟨nt_edge_map p (P.n' v) i (C.act v γ) (L v) (L1 v) h.1, fun u hu => ?_⟩
  show (L u).map _ = (L1 u).map _
  rw [h.2 u hu]

theorem Rel_lat (L L1 : P.Tup) (h : Rel v i L L1) : P.IsLatTup L ↔ P.IsLatTup L1 := by
  constructor
  · intro hL u
    by_cases hu : u = v
    · subst hu
      exact h.1.2.1
    · rw [← h.2 u hu]
      exact hL u
  · intro hL u
    by_cases hu : u = v
    · subst hu
      exact h.1.1
    · rw [h.2 u hu]
      exact hL u

def upS (L : P.Tup) : Finset P.Tup := (UP P v i (L v)).image (upd v L)

def dnS (L1 : P.Tup) : Finset P.Tup := (EE P v i (L1 v)).image (upd v L1)

theorem mem_upS (L L1 : P.Tup) : L1 ∈ upS v i L ↔ Rel v i L L1 := by
  unfold upS
  rw [Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨?_, fun u hu => (upd_ne v L A hu).symm⟩
    rw [upd_self]
    exact (mem_UP P).1 hA
  · intro h
    refine ⟨L1 v, (mem_UP P).2 h.1, ?_⟩
    funext u
    by_cases hu : u = v
    · subst hu
      exact upd_self u L _
    · rw [upd_ne v L _ hu]
      exact h.2 u hu

theorem mem_dnS (L L1 : P.Tup) : L ∈ dnS v i L1 ↔ Rel v i L L1 := by
  unfold dnS
  rw [Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨?_, fun u hu => upd_ne v L1 A hu⟩
    rw [upd_self]
    exact (mem_EE P).1 hA
  · intro h
    refine ⟨L v, (mem_EE P).2 h.1, ?_⟩
    funext u
    by_cases hu : u = v
    · subst hu
      exact upd_self u L1 _
    · rw [upd_ne v L1 _ hu]
      exact (h.2 u hu).symm

theorem adj_level {K : Type} [Field K] [CharZero K] (Rc : Finset P.Tup) (hlat : ∀ L ∈ Rc, P.IsLatTup L)
    (hex : ∀ L, P.IsLatTup L → ∃! L0, L0 ∈ Rc ∧ ∃ γ : C.Γ, L = C.smul γ L0)
    (hst : ∀ L, P.IsLatTup L → 0 < Nat.card {γ : C.Γ // C.smul γ L = L})
    (φ : P.Tup → P.Tup → K) (hφ : ∀ (γ : C.Γ) L L1, φ (C.smul γ L) (C.smul γ L1) = φ L L1) :
    ∑ L ∈ Rc, (Nat.card {γ : C.Γ // C.smul γ L = L} : K)⁻¹ *
        ∑ᶠ (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨L v, A⟩),
          φ L (Function.update L v A) =
      ∑ L1 ∈ Rc, (Nat.card {γ : C.Γ // C.smul γ L1 = L1} : K)⁻¹ *
        ∑ᶠ (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨A, L1 v⟩),
          φ (Function.update L1 v A) L1 := by
  have e1 : ∀ L : P.Tup, ∑ᶠ (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨L v, A⟩),
      φ L (Function.update L v A) = ∑ L1 ∈ upS v i L, φ L L1 := by
    intro L
    unfold upS
    rw [Finset.sum_image (fun a _ b _ h => upd_inj v L h)]
    exact finsum_mem_eq_finite_toFinset_sum _ (up_fin P v i (L v))
  have e2 : ∀ L1 : P.Tup, ∑ᶠ (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) i ⟨A, L1 v⟩),
      φ (Function.update L1 v A) L1 = ∑ L ∈ dnS v i L1, φ L L1 := by
    intro L1
    unfold dnS
    rw [Finset.sum_image (fun a _ b _ h => upd_inj v L1 h)]
    exact finsum_mem_eq_finite_toFinset_sum _ (edges_fin P v i (L1 v))
  simp_rw [e1, e2]
  exact adj C.smul (lsmul_one C) (lsmul_mul C) P.IsLatTup Rc hlat hex hst (Rel v i) (Rel_smul C v i) (Rel_lat v i)
    (upS v i) (dnS v i) (fun L _ L1 => mem_upS v i L L1) (fun L1 _ L => mem_dnS v i L L1) φ hφ

end Conc

section Final

variable {p : ℕ} [Fact p.Prime]

theorem up_down_adjoint (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) : Formalism.MainNotions.FormalGroupSystem.adm6 D X Y := by
  intro j hj v' i φ hφ
  have : CharZero Y.Kc := Formalism.MainNotions.FormalGroupSystem.Pf.charZero_K' p Y.Kc

  let Rc : X.Lv.comp j → Finset (X.Pj j).Tup := fun c => ((Y.Rep j).filter fun La => La.1 = c).image Prod.snd
  have hRc : ∀ c L, L ∈ Rc c ↔ (c, L) ∈ Y.Rep j := by
    intro c L
    simp only [Rc, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨c', L'⟩, ⟨h1, h2⟩, h3⟩
      cases h2
      cases h3
      exact h1
    · intro h
      exact ⟨(c, L), ⟨h, rfl⟩, rfl⟩
  have split : ∀ F : X.Lt j → Y.Kc, ∑ La ∈ Y.Rep j, F La =
      ∑ c ∈ (Y.Rep j).image Prod.fst, ∑ L ∈ Rc c, F (c, L) := by
    intro F
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := (Y.Rep j).image Prod.fst)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Rc]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun x hx => ?_)
      obtain ⟨c', L⟩ := x
      have h2 : c' = c := (Finset.mem_filter.1 hx).2
      cases h2
      rfl
    · rintro ⟨c1, L1⟩ h1 ⟨c2, L2⟩ h2 h
      have e1 : c1 = c := (Finset.mem_filter.1 h1).2
      have e2 : c2 = c := (Finset.mem_filter.1 h2).2
      cases e1
      cases e2
      cases h
      rfl
  rw [split, split]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  exact adj_level (X.Lv.lev j c) v' i (Rc c) (fun L hL => Y.Rep_lat j (c, L) ((hRc c L).1 hL))
    (fun L hL => by
      obtain ⟨L0, ⟨h0, hγ⟩, hu⟩ := Y.Rep_ex j hj c L hL
      exact ⟨L0, ⟨(hRc c L0).2 h0, hγ⟩, fun L2 h2 => hu L2 ⟨(hRc c L2).1 h2.1, h2.2⟩⟩)
    (fun L hL => Y.stab_fin j hj (c, L) hL) (φ c) (hφ c)

end Final

end Formalism.L2.G.Pend
