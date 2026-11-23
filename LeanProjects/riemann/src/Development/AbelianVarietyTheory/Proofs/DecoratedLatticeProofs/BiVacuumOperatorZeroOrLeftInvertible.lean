import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSplitPlacesActsBySignsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsolateAbstractStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZeroOrInv

open GlobalTheory.LatVac

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def twoT (x : WO A S × WO S A') : (WO A S → WO S A' → ℂ) →ₗ[ℂ] (WO A S → WO S A' → ℂ) where
  toFun C := fun u v => heisO ψ A S x.1 (fun u' => heisO ψ S A' x.2 (C u') v) u
  map_add' C C' := by
    funext u v
    simp only [heisO, Pi.add_apply]
    ring
  map_smul' c C := by
    funext u v
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem twoT_apply (x : WO A S × WO S A') (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    twoT ψ A S A' x C u v = ψ (symplOH A S u x.1) * (ψ (symplOH S A' v x.2) * C (u + x.1) (v + x.2)) := rfl

theorem symplOH_add_l (T T' : HSp D) (x x' y : WO T T') :
    symplOH T T' (x + x') y = symplOH T T' x y + symplOH T T' x' y := by
  unfold symplOH
  rw [symplO_add_left, mul_add]

theorem symplOH_add_r (T T' : HSp D) (x y y' : WO T T') :
    symplOH T T' x (y + y') = symplOH T T' x y + symplOH T T' x y' := by
  unfold symplOH
  rw [symplO_add_right, mul_add]

theorem symplOH_two (T T' : HSp D) (x y : WO T T') : symplOH T T' x y + symplOH T T' x y = symplO T T' x y := by
  unfold symplOH
  rw [← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]

theorem symplO_skew' (T T' : HSp D) (x y : WO T T') : symplO T T' y x = -symplO T T' x y := by
  rw [← symplOH_two, ← symplOH_two, symplOH_skew, neg_add]

theorem psi_ne_zero (z : AF D.host.F) : ψ z ≠ 0 := by
  intro h
  have h1 := ψ.map_add_eq_mul z (-z)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

def bet (x y : WO A S × WO S A') : ℂ := ψ (symplOH A S x.1 y.1) * ψ (symplOH S A' x.2 y.2)

def chi (x γ : WO A S × WO S A') : ℂ := ψ (symplO A S γ.1 x.1) * ψ (symplO S A' γ.2 x.2)

theorem twoT_zero (C : WO A S → WO S A' → ℂ) : twoT ψ A S A' 0 C = C := by
  funext u v
  change heisO ψ A S 0 (fun u' => heisO ψ S A' 0 (C u') v) u = C u v
  simp only [LatVac.heisO_zero]

theorem twoT_mul (x y : WO A S × WO S A') (C : WO A S → WO S A' → ℂ) :
    twoT ψ A S A' x (twoT ψ A S A' y C) = bet ψ A S A' x y • twoT ψ A S A' (x + y) C := by
  funext u v
  simp only [twoT_apply, Pi.smul_apply, smul_eq_mul, bet, Prod.fst_add, Prod.snd_add, symplOH_add_l, symplOH_add_r,
    AddChar.map_add_eq_mul, add_assoc]
  ring

theorem bet_ne_zero (x y : WO A S × WO S A') : bet ψ A S A' x y ≠ 0 :=
  mul_ne_zero (psi_ne_zero ψ _) (psi_ne_zero ψ _)

theorem twoT_comm (x γ : WO A S × WO S A') (C : WO A S → WO S A' → ℂ) :
    twoT ψ A S A' γ (twoT ψ A S A' x C) = chi ψ A S A' x γ • twoT ψ A S A' x (twoT ψ A S A' γ C) := by
  rw [twoT_mul, twoT_mul, smul_smul, add_comm x γ]
  congr 1
  simp only [bet, chi]
  rw [symplOH_skew A S γ.1 x.1, symplOH_skew S A' γ.2 x.2, ← symplOH_two A S γ.1 x.1, ← symplOH_two S A' γ.2 x.2]
  simp only [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  field_simp [psi_ne_zero ψ]

theorem comb_single (T T' : HSp D) (x : WO T T') (c : ℂ) (f : WO T T' → ℂ) :
    comb ψ T T' (Finsupp.single x c) f = c • heisO ψ T T' x f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (zero_smul ℂ (heisO ψ T T' x f))]

theorem biComb_single (x : WO A S × WO S A') (c : ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' (Finsupp.single x.1 c) (Finsupp.single x.2 1) C = c • twoT ψ A S A' x C := by
  funext u v
  simp only [biComb, comb_single, twoT_apply, heisO, Pi.smul_apply, smul_eq_mul, one_mul]

theorem biComb_eq (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' C = ∑ x ∈ c.support, ∑ y ∈ c'.support, (c x * c' y) • twoT ψ A S A' (x, y) C := by
  funext u v
  simp only [biComb, comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, twoT_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

def goodG (P : Pl D → Prop) : AddSubgroup (WO A S × WO S A') where
  carrier := {x | MxAt P x.1 ∧ MxAt P x.2}
  zero_mem' := ⟨fun _ _ => zero_mem (idAt D P), fun _ _ => zero_mem (idAt D P)⟩
  add_mem' := fun hx hy => ⟨fun i j => add_mem (hx.1 i j) (hy.1 i j), fun i j => add_mem (hx.2 i j) (hy.2 i j)⟩
  neg_mem' := fun hx => ⟨fun i j => neg_mem (hx.1 i j), fun i j => neg_mem (hx.2 i j)⟩

def kOp (op : BiOp A S A') : (WO A S × WO S A') →₀ ℂ :=
  ∑ i, ∑ x ∈ (op.u i).support, ∑ y ∈ (op.u' i).support, Finsupp.single (x, y) (op.u i x * op.u' i y)

theorem app_eq (op : BiOp A S A') (C : WO A S → WO S A' → ℂ) :
    op.app ψ C = ∑ p ∈ (kOp A S A' op).support, kOp A S A' op p • twoT ψ A S A' p C := by
  let t : WO A S × WO S A' → ℂ → (WO A S → WO S A' → ℂ) := fun p c => c • twoT ψ A S A' p C
  have hz : ∀ p, t p 0 = 0 := fun p => zero_smul ℂ _
  have ha : ∀ p a b, t p (a + b) = t p a + t p b := fun p a b => add_smul a b _
  change _ = (kOp A S A' op).sum t
  unfold kOp
  rw [← Finsupp.sum_finset_sum_index hz ha]
  unfold BiOp.app
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [biComb_eq, ← Finsupp.sum_finset_sum_index hz ha]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finsupp.sum_finset_sum_index hz ha]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_single_index (hz _)]

theorem kOp_good (P : Pl D → Prop) (op : BiOp A S A') (hop : OpAt P op) :
    ∀ p ∈ (kOp A S A' op).support, p ∈ goodG A S A' P := by
  classical
  intro p hp
  obtain ⟨i, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hp)
  obtain ⟨x, hx, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hp)
  obtain ⟨y, hy, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hp)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hp)]
  exact ⟨(hop i).1 x hx, (hop i).2 y hy⟩

def ofK (κ : (WO A S × WO S A') →₀ ℂ) : BiOp A S A' where
  n := κ.support.card
  u k := Finsupp.single (κ.support.equivFin.symm k).1.1 (κ (κ.support.equivFin.symm k))
  u' k := Finsupp.single (κ.support.equivFin.symm k).1.2 1

theorem ofK_app (κ : (WO A S × WO S A') →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    (ofK A S A' κ).app ψ C = ∑ p ∈ κ.support, κ p • twoT ψ A S A' p C := by
  change ∑ k : Fin κ.support.card, biComb ψ A S A' (Finsupp.single (κ.support.equivFin.symm k).1.1
    (κ (κ.support.equivFin.symm k))) (Finsupp.single (κ.support.equivFin.symm k).1.2 1) C = _
  rw [Finset.sum_congr rfl fun k _ => biComb_single ψ A S A' ((κ.support.equivFin.symm k).1) _ C]
  exact (Equiv.sum_comp κ.support.equivFin.symm (fun p : κ.support => κ p • twoT ψ A S A' p C)).trans
    (Finset.sum_coe_sort κ.support (fun p => κ p • twoT ψ A S A' p C))

theorem ofK_at (P : Pl D → Prop) (κ : (WO A S × WO S A') →₀ ℂ) (hκ : ∀ p ∈ κ.support, p ∈ goodG A S A' P) :
    OpAt P (ofK A S A' κ) := by
  intro k
  have hk := hκ _ (κ.support.equivFin.symm k).2
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]; exact hk.1
  · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]; exact hk.2

theorem biComb_sum {ι : Type} (s : Finset ι) (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ) (F : ι → WO A S → WO S A' → ℂ) :
    biComb ψ A S A' e e' (∑ i ∈ s, F i) = ∑ i ∈ s, biComb ψ A S A' e e' (F i) := by
  simp only [biComb_eq, map_sum, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Finset.sum_comm

theorem comp_part (P : Pl D → Prop) (op : BiOp A S A') (hop : OpAt P op) (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ)
    (he : CombAt P e) (he' : CombAt P e') :
    ∃ op' : BiOp A S A', OpAt P op' ∧ ∀ C, op'.app ψ C = biComb ψ A S A' e e' (op.app ψ C) := by
  choose c hcs hcf using fun i => (GlobalTheory.HeisComb.main D ψ A S).1 e (op.u i)
  choose c' hcs' hcf' using fun i => (GlobalTheory.HeisComb.main D ψ S A').1 e' (op.u' i)
  refine ⟨⟨op.n, c, c'⟩, fun i => ⟨fun w hw => ?_, fun w hw => ?_⟩, fun C => ?_⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := hcs i w hw
    exact fun a b => add_mem (he x hx a b) ((hop i).1 y hy a b)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hcs' i w hw
    exact fun a b => add_mem (he' x hx a b) ((hop i).2 y hy a b)
  · change ∑ i, biComb ψ A S A' (c i) (c' i) C = biComb ψ A S A' e e' (∑ i, biComb ψ A S A' (op.u i) (op.u' i) C)
    rw [biComb_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (GlobalTheory.ProdLocInv.biComb_comp ψ A S A' e (op.u i) (c i) e' (op.u' i) (c' i) (hcf i) (hcf' i) C).symm

theorem symplO_zero_left (T T' : HSp D) (w : WO T T') : symplO T T' 0 w = 0 := by
  rw [symplO_skew', show symplO T T' w 0 = 0 from (symplHom T T' w).map_zero, neg_zero]

theorem psi_eq_one_of_neg {z : AF D.host.F} (h : ψ (-z) = 1) : ψ z = 1 := by
  rw [AddChar.map_neg_eq_inv, inv_eq_one] at h
  exact h

end GlobalTheory.ZeroOrInv

open GlobalTheory.ZeroOrInv GlobalTheory.LatVac in

theorem GlobalTheory.FinPl.biInv_main : ∀ D : D7, GlobalTheory.FinPl.BiInv D := by
  intro D k _ _ _ _ ι p I P hP ψ hψ A S A' op hop
  refine ⟨fun LA LS LA' hA hS hA' => ?_, fun e e' he he' => comp_part ψ A S A' P op hop e e' he he'⟩
  classical
  let Γ : AddSubgroup (WO A S × WO S A') :=
    (latO A S (LA : Set (Fin A.rank → D.host.E)) (LS : Set (Fin S.rank → D.host.E)) P).prod
      (latO S A' (LS : Set (Fin S.rank → D.host.E)) (LA' : Set (Fin A'.rank → D.host.E)) P)
  have hΓG : Γ ≤ goodG A S A' P := fun x hx =>
    ⟨LatMem.latO_mxAt (AddSubgroup.mem_prod.1 hx).1, LatMem.latO_mxAt (AddSubgroup.mem_prod.1 hx).2⟩
  have hex : ∀ γ : WO A S × WO S A', ∃ s : ℂ, γ ∈ Γ →
      s ≠ 0 ∧ ∀ C ∈ {C | BiVacAt ψ LA LS LA' P C}, twoT ψ A S A' γ C = s • C := by
    intro γ
    by_cases hγ : γ ∈ Γ
    · obtain ⟨ε₁, hε₁, h₁⟩ := GlobalTheory.T.homLatticeCompletion_splitPlaces_acts_by_signs D k ι p I P hP ψ hψ A S LA LS hA hS γ.1 (AddSubgroup.mem_prod.1 hγ).1
      obtain ⟨ε₂, hε₂, h₂⟩ := GlobalTheory.T.homLatticeCompletion_splitPlaces_acts_by_signs D k ι p I P hP ψ hψ S A' LS LA' hS hA' γ.2 (AddSubgroup.mem_prod.1 hγ).2
      refine ⟨ε₁ * ε₂, fun _ => ⟨mul_ne_zero (left_ne_zero_of_mul_eq_one hε₁) (left_ne_zero_of_mul_eq_one hε₂),
        fun C hC => ?_⟩⟩
      funext u v
      change heisO ψ A S γ.1 (fun u' => heisO ψ S A' γ.2 (C u') v) u = (ε₁ * ε₂) * C u v
      have e2 : (fun u' => heisO ψ S A' γ.2 (C u') v) = ε₂ • fun u' => C u' v := by
        funext u'
        rw [h₂ (C u') (hC.2 u')]
        rfl
      rw [e2, LatVac.heisO_smul, h₁ _ (hC.1 v)]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · exact ⟨1, fun h => absurd h hγ⟩
  choose aF haF using hex
  have hχ : ∀ x, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, chi ψ A S A' (x + γ') γ = chi ψ A S A' x γ := by
    intro x γ hγ γ' hγ'
    obtain ⟨g1, g2⟩ := AddSubgroup.mem_prod.1 hγ
    obtain ⟨g1', g2'⟩ := AddSubgroup.mem_prod.1 hγ'
    have e1 := (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ A S LA LS hA hS P γ.1 (LatMem.latO_mxAt g1)).1 g1 γ'.1 g1'
    have e2 := (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S A' LS LA' hS hA' P γ.2 (LatMem.latO_mxAt g2)).1 g2 γ'.2 g2'
    simp only [chi, Prod.fst_add, Prod.snd_add, symplO_add_right, AddChar.map_add_eq_mul, e1, e2, mul_one]
  have hsep : ∀ x ∈ goodG A S A' P, ∀ y ∈ goodG A S A' P, x - y ∉ Γ →
      ∃ γ ∈ Γ, chi ψ A S A' x γ ≠ chi ψ A S A' y γ := by
    intro x hx y hy hxy
    have hd : x - y ∈ goodG A S A' P := sub_mem hx hy
    rw [AddSubgroup.mem_prod, not_and_or] at hxy
    rcases hxy with h | h
    · rw [GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ A S LA LS hA hS P (x - y).1 hd.1] at h
      push_neg at h
      obtain ⟨l, hl, hne⟩ := h
      refine ⟨(l, 0), AddSubgroup.mem_prod.2 ⟨hl, zero_mem _⟩, fun heq => hne ?_⟩
      simp only [chi, symplO_zero_left, AddChar.map_zero_eq_one, mul_one] at heq
      have hx1 : x.1 = (x - y).1 + y.1 := by rw [Prod.fst_sub, sub_add_cancel]
      rw [hx1, symplO_add_right, AddChar.map_add_eq_mul] at heq
      have h1 : ψ (symplO A S l (x - y).1) = 1 :=
        mul_right_cancel₀ (psi_ne_zero ψ _) (heq.trans (one_mul _).symm)
      rw [symplO_skew'] at h1
      exact psi_eq_one_of_neg ψ h1
    · rw [GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S A' LS LA' hS hA' P (x - y).2 hd.2] at h
      push_neg at h
      obtain ⟨l, hl, hne⟩ := h
      refine ⟨(0, l), AddSubgroup.mem_prod.2 ⟨zero_mem _, hl⟩, fun heq => hne ?_⟩
      simp only [chi, symplO_zero_left, AddChar.map_zero_eq_one, one_mul] at heq
      have hx2 : x.2 = (x - y).2 + y.2 := by rw [Prod.snd_sub, sub_add_cancel]
      rw [hx2, symplO_add_right, AddChar.map_add_eq_mul] at heq
      have h1 : ψ (symplO S A' l (x - y).2) = 1 :=
        mul_right_cancel₀ (psi_ne_zero ψ _) (heq.trans (one_mul _).symm)
      rw [symplO_skew'] at h1
      exact psi_eq_one_of_neg ψ h1
  rcases GlobalTheory.T.eq_zero_or_exists_inverse_combination_of_separating (WO A S × WO S A') Γ (goodG A S A' P) (WO A S → WO S A' → ℂ) (twoT ψ A S A')
      {C | BiVacAt ψ LA LS LA' P C} (bet ψ A S A') aF (chi ψ A S A') hΓG (twoT_zero ψ A S A') (twoT_mul ψ A S A')
      (bet_ne_zero ψ A S A') (fun γ hγ => haF γ hγ) (fun γ _ x v => twoT_comm ψ A S A' x γ v) hχ hsep
      (kOp A S A' op).support (kOp A S A' op) (kOp_good A S A' P op hop) with h | ⟨κ, hκ, hinv⟩
  · left
    intro C hC
    rw [app_eq]
    exact h C hC
  · right
    exact ⟨ofK A S A' κ, ofK_at A S A' P κ hκ, fun C hC => by rw [ofK_app, app_eq]; exact hinv C hC⟩
