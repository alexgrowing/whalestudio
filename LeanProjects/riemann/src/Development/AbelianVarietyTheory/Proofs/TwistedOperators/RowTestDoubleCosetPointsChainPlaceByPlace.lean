import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRowFlagTiltUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointTrivialOffTensorPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.PlaceChain

open GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem mt_cut {a : AE D} (h : a * a = a ∧ cA D a = a) (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutPart a V g) - 1 = a • (Formalism.L2.Theta.mt V g - 1) := by
  rw [mt_cutPart h.1 h.2, smul_sub, sub_smul, one_smul]
  abel

theorem cut_one {a : AE D} (h : a * a = a ∧ cA D a = a) (V : HSp D) : cutPart a V 1 = 1 := by
  apply GlobalTheory.IdemSupport.mt_inj V
  have h1 := mt_cut h V 1
  rw [GlobalTheory.IdemSupport.mt_one, sub_self, smul_zero, sub_eq_zero] at h1
  rw [h1, GlobalTheory.IdemSupport.mt_one]

theorem cut_zero (V : HSp D) (g : GA D V) : cutPart 0 V g = 1 := by
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [mt_cutPart (mul_zero (0 : AE D)) (map_zero (cA D)), GlobalTheory.IdemSupport.mt_one, zero_smul, sub_zero, one_smul,
    zero_add]

theorem cut_self {e : AE D} (h : (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e) (V : HSp D)
    {g : GA D V} (hg : SuppAt e V g) : cutPart (e + cA D e) V g = g := by
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [mt_cutPart h.1 h.2]
  ext i j
  have hij := hg i j
  simp only [Matrix.sub_apply] at hij
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination hij

theorem cut_add {a b : AE D} (ha : a * a = a ∧ cA D a = a) (hb : b * b = b ∧ cA D b = b) (hab : a * b = 0) (V : HSp D)
    (g : GA D V) : cutPart a V g * cutPart b V g = cutPart (b + a) V g := by
  have hab' : b * a = 0 := by rw [mul_comm]; exact hab
  have hba : (b + a) * (b + a) = b + a ∧ cA D (b + a) = b + a := by
    refine ⟨?_, by rw [map_add, ha.2, hb.2]⟩
    rw [add_mul, mul_add, mul_add, hb.1, ha.1, hab, hab', add_zero, zero_add]
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [GlobalTheory.IdemSupport.mt_mul, eq_add_of_sub_eq (mt_cut ha V g), eq_add_of_sub_eq (mt_cut hb V g),
    eq_add_of_sub_eq (mt_cut hba V g)]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hab', zero_smul, one_mul, mul_one,
    zero_add, add_smul]
  abel

private lemma mul_self_and_mul_cA_eq_zero_of_isIdemAt {e : AE D} {w : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e w) :
    e * e = e ∧ e * cA D e = 0 := by
  obtain ⟨⟨h1, h2, -⟩, -⟩ := h
  exact ⟨h1, h2⟩

theorem loc_cut {e : AE D} {w : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e w) (V : HSp D) (g : GA D V) :
    loc w (Lev.finE V (cutPart (e + cA D e) V g)) = loc w (Lev.finE V g) := by
  obtain ⟨h1, h2⟩ := mul_self_and_mul_cA_eq_zero_of_isIdemAt he
  have hf := idem_conj_sum h1 h2
  have c1 : GlobalTheory.StdFrames.cpt w (GlobalTheory.LevSplit.finSw D e) = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt he).1
  have c2 : GlobalTheory.StdFrames.cpt w (GlobalTheory.LevSplit.finSw D (cA D e)) = 0 := by
    have h3 := congrArg (fun x => GlobalTheory.StdFrames.cpt w (GlobalTheory.LevSplit.finSw D x)) h2
    simp only [map_mul, map_zero, c1, one_mul] at h3
    exact h3
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [GlobalTheory.StdFrames.loc, Matrix.GeneralLinearGroup.map_apply]
  rw [GlobalTheory.LevSplit.finE_val, GlobalTheory.LevSplit.finE_val, Matrix.map_apply, Matrix.map_apply, mt_cutPart hf.1 hf.2]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, c1, c2]
  ring

theorem inBasis_cut {e : AE D} {w : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e w) (V : HSp D) {n : ℕ} (h : n = V.rank)
    (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) :
    GlobalTheory.FunObj.inBasis h β w (Lev.finE V (cutPart (e + cA D e) V g)) = GlobalTheory.FunObj.inBasis h β w (Lev.finE V g) := by
  simp only [GlobalTheory.FunObj.inBasis, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, loc_cut he V g]

theorem cut_mem_grpOff {e a : AE D} {w : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e w) (ha : a * a = a ∧ cA D a = a)
    (h0 : a * (e + cA D e) = 0) (V : HSp D) (g : GA D V) :
    cutPart a V g ∈ GlobalTheory.FinPl.grpOff V (· = w.under (𝓞 D.host.F)) := by
  obtain ⟨⟨-, -, v', ε, hε, hse⟩, -⟩ := id he
  have hv := GlobalTheory.RowVal.placeIdem_eq_under_of_idemAt he hε hse
  subst hv
  obtain ⟨α, rfl, hα, -⟩ := hε
  have hc : GlobalTheory.FinPl.compAt D (w.under (𝓞 D.host.F)) (e + cA D e) = 1 := by
    rw [hse, (GlobalTheory.FinPl.SetCut.parts_pairA α).2, hα, Algebra.TensorProduct.one_def]
  have ha0 : GlobalTheory.FinPl.compAt D (w.under (𝓞 D.host.F)) a = 0 := by
    have h3 := congrArg (GlobalTheory.FinPl.compAt D (w.under (𝓞 D.host.F))) h0
    rwa [map_mul, hc, mul_one, map_zero] at h3
  show cutPart a V g ∈ GlobalTheory.FinPl.congGrp V (GlobalTheory.FinPl.idOff D _)
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro i j
  rw [← Matrix.sub_apply, mt_cut ha V g, Matrix.smul_apply, smul_eq_mul]
  simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf, RingHom.mem_ker, map_mul]
  rintro ⟨u, rfl⟩
  rw [ha0, zero_mul]

theorem real_mem_grpOff (V : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) {a : GA D V} (ha : a ∈ GinfC V) :
    a ∈ GlobalTheory.FinPl.grpOff V P := by
  have hf : finHom V a = 1 := ha
  show a ∈ GlobalTheory.FinPl.congGrp V (GlobalTheory.FinPl.idOff D P)
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro i j
  have key : finPart D (Formalism.L2.Theta.mt V a i j) = (finHom V a : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    rw [finHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe, Matrix.map_apply]
    rfl
  have key2 : finPart D (Formalism.L2.Theta.mt V a i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = 0 := by
    rw [map_sub, key, hf, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf, RingHom.mem_ker, GlobalTheory.FinPl.compAt, RingHom.comp_apply, key2,
    map_zero, implies_true]

theorem isFinOf_mul {V : HSp D} {δ r b b₀ : GA D V} (h : IsFinOf (δ * r) b) (h₀ : IsFinOf δ b₀) (hr : r ∈ GfC V) :
    b = b₀ * r := by
  obtain ⟨hb, a, ha, hab⟩ := h
  obtain ⟨hb₀, a₀, ha₀, hab₀⟩ := h₀
  have e1 : a = a₀ * (b₀ * r) * b⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, hab, ← hab₀, mul_assoc]
  have e3 : a₀⁻¹ * a = b₀ * r * b⁻¹ := by
    rw [e1]
    group
  have e2 : a₀⁻¹ * a = 1 :=
    GlobalTheory.PointAtPlace.eq_one_of_mem V _ (by rw [e3]; exact mul_mem (mul_mem hb₀ hr) (inv_mem hb))
      (mul_mem (inv_mem ha₀) ha)
  rw [inv_mul_eq_one] at e2
  rw [← e2, ← hab₀, mul_assoc] at hab
  exact mul_left_cancel hab

section Fam

variable {P : Finset (Pl D.host.E)} {e : AE D} {eL : P → AE D}

theorem idemAt_of_single {x : AE D} {w : Pl D.host.E} (h : IsIdemSum x {w}) : Formalism.L2.NTheta.IsIdemAt x w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  rw [Finset.sum_singleton]
  exact hes w (Finset.mem_singleton_self w)

theorem eq_sum (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) : e = ∑ w, eL w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P es]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ _ _ (hes w.1 w.2) (h w)).1 rfl

private lemma mul_eL_eq_eL_of_isIdemSum (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) (u : P) :
    e * eL u = eL u := by
  rw [eq_sum he h, Finset.sum_mul, Finset.sum_eq_single u]
  · exact (mul_self_and_mul_cA_eq_zero_of_isIdemAt (h u)).1
  · intro v _ hv
    exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ _ _ (h v) (h u)).2 (fun heq => hv (Subtype.ext heq))
  · intro hu
    exact absurd (Finset.mem_univ u) hu

private lemma eL_mul_cA_eL_eq_zero (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) (u u' : P) :
    eL u * cA D (eL u') = 0 := by
  obtain ⟨-, hec⟩ := id he
  calc eL u * cA D (eL u') = (e * eL u) * cA D (e * eL u') := by rw [mul_eL_eq_eL_of_isIdemSum he h u, mul_eL_eq_eL_of_isIdemSum he h u']
    _ = (e * cA D e) * (eL u * cA D (eL u')) := by rw [map_mul]; ring
    _ = 0 := by rw [hec, zero_mul]

theorem orth (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) {w w' : P} (hw : w ≠ w') :
    (eL w + cA D (eL w)) * (eL w' + cA D (eL w')) = 0 := by
  have e0 : eL w * eL w' = 0 :=
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ _ _ (h w) (h w')).2 (fun heq => hw (Subtype.ext heq))
  rw [add_mul, mul_add, mul_add, ← map_mul (cA D) (eL w) (eL w'), e0, map_zero, eL_mul_cA_eL_eq_zero he h w w',
    mul_comm (cA D (eL w)) (eL w'), eL_mul_cA_eL_eq_zero he h w' w]
  simp

theorem idem_sum (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) (S : Finset P) :
    (∑ w ∈ S, (eL w + cA D (eL w))) * (∑ w ∈ S, (eL w + cA D (eL w))) = (∑ w ∈ S, (eL w + cA D (eL w))) ∧
      cA D (∑ w ∈ S, (eL w + cA D (eL w))) = ∑ w ∈ S, (eL w + cA D (eL w)) := by
  have hi : ∀ u, (eL u + cA D (eL u)) * (eL u + cA D (eL u)) = eL u + cA D (eL u) ∧
      cA D (eL u + cA D (eL u)) = eL u + cA D (eL u) := fun u =>
    idem_conj_sum (mul_self_and_mul_cA_eq_zero_of_isIdemAt (h u)).1 (mul_self_and_mul_cA_eq_zero_of_isIdemAt (h u)).2
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.sum_eq_single u (fun v _ hv => orth he h (Ne.symm hv)) (fun hu' => absurd hu hu'), (hi u).1]
  · rw [map_sum]
    exact Finset.sum_congr rfl fun u _ => (hi u).2

theorem sum_orth (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) {S : Finset P} {w : P} (hw : w ∉ S) :
    (∑ w ∈ S, (eL w + cA D (eL w))) * (eL w + cA D (eL w)) = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun u hu => orth he h (fun huw => hw (huw ▸ hu))

variable (eL) in

def cutS (S : Finset P) {V : HSp D} (g : GA D V) : GA D V := cutPart (∑ w ∈ S, (eL w + cA D (eL w))) V g

theorem cutS_empty {V : HSp D} (g : GA D V) : cutS eL ∅ g = 1 := by
  unfold cutS
  rw [Finset.sum_empty]
  exact cut_zero _ g

theorem cutS_one (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) (S : Finset P) (V : HSp D) :
    cutS eL S (1 : GA D V) = 1 := by
  unfold cutS
  exact cut_one (idem_sum he h S) V

theorem cutS_univ (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) {V : HSp D} {g : GA D V}
    (hg : SuppAt e V g) : cutS eL Finset.univ g = g := by
  have hs : ∑ w ∈ (Finset.univ : Finset P), (eL w + cA D (eL w)) = e + cA D e := by
    rw [Finset.sum_add_distrib, ← map_sum, ← eq_sum he h]
  have hi := idem_sum he h Finset.univ
  unfold cutS
  rw [hs] at hi ⊢
  exact cut_self hi _ hg

theorem cutS_insert (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) {S : Finset P} {w : P} (hw : w ∉ S)
    {V : HSp D} (g : GA D V) : cutS eL S g * cutPart (eL w + cA D (eL w)) V g = cutS eL (insert w S) g := by
  unfold cutS
  rw [Finset.sum_insert hw]
  exact cut_add (idem_sum he h S) (idem_conj_sum (mul_self_and_mul_cA_eq_zero_of_isIdemAt (h w)).1 (mul_self_and_mul_cA_eq_zero_of_isIdemAt (h w)).2)
    (sum_orth he h hw) _ g

theorem cutS_mem (he : IsIdemSum e P) (h : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1) {S : Finset P} {w : P} (hw : w ∉ S)
    {V : HSp D} (g : GA D V) : cutS eL S g ∈ GlobalTheory.FinPl.grpOff V (· = w.1.under (𝓞 D.host.F)) := by
  unfold cutS
  exact cut_mem_grpOff (h w) (idem_sum he h S) (sum_orth he h hw) _ g

end Fam

end GlobalTheory.PlaceChain

namespace GlobalTheory.PlaceChain

open GlobalTheory.ExpansionInvariance

theorem isTilt_one {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (hj : j ∉ idx D) :
    IsTilt G j 1 := by
  unfold IsTilt
  refine ⟨one_mem _, fun _ => rfl, fun σ h₁ h₂ => ?_⟩
  have hj' : j = D.R.m - 1 := by
    by_contra hne
    apply hj
    simp only [idx, List.mem_range'_1]
    obtain ⟨k, hk⟩ := D.R.m_even
    omega
  subst hj'
  have hσ : σ = 0 := by omega
  subst hσ
  refine ⟨by rw [GlobalTheory.IdemSupport.mt_one, Matrix.one_mul], ?_, ?_⟩ <;> (ext a b; exact b.elim0)

private lemma suppAt_one_twisted_operators {D : D7} {e : AE D} {V : HSp D} : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.IdemSupport.mt_one, sub_self, Matrix.zero_apply, mul_zero]

private lemma zero_not_mem_idx' {D : D7} : 0 ∉ idx D := by
  simp [idx]

set_option maxHeartbeats 800000 in

theorem points : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ p : Pts ch.G, IsRealPt p → ∃ q : Finset (locPl ch.G t) → Pts ch.G, q ∅ = p * b₀ ∧ q Finset.univ = p * b ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∃ r r₀ h : Pts ch.G, OneLoc t w.1 (eL w) r (fun j => if j ∈ idx D then sgnAt ch.G t s w.1 j * (repsAt ch.G t w.1).elt (β w) (D.R.m, j) else 1) ∧ OneLoc t w.1 (eL w) r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) j)⁻¹ else 1) ∧ (∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.1.under (𝓞 D.host.F))) ∧ h * r = q (insert w S) ∧ h * r₀ = q S := by
  refine Exists.intro 0 (fun ε CF _ => Exists.intro 0 ?_)
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ s t β b b₀ hrep hbase eL heL p hp
  have hL : ∀ w, Formalism.L2.NTheta.IsIdemAt (eL w) w.1 := fun w => idemAt_of_single (heL w)
  obtain ⟨hH₀, hbI, hb1⟩ := hbase
  obtain ⟨e₀, he₀, hs₀, hl₀⟩ := id hH₀
  obtain ⟨hr1, hr2⟩ := hrep
  have h0i : 0 ∉ idx D := zero_not_mem_idx'
  have hX : ∀ j, ∃ x : GA D (ch.G.V (.grid D.R.m j)), (j ∈ idx D → x ∈ GfC _ ∧ b j = b₀ j * x ∧
      ∃ e, IsIdemSum e (locPl ch.G t) ∧ SuppAt e _ x ∧ ∀ (hj : j ≤ D.R.m) (w : locPl ch.G t),
        inBasis (rank_vertex ch.G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (ch.S.B.β D.R.m j) w.1
          (Lev.finE (ch.G.V (.grid D.R.m j)) x) = sgnAt ch.G t s w.1 j * (repsAt ch.G t w.1).elt (β w) (D.R.m, j)) ∧
      (j ∉ idx D → x = 1) := by
    intro j
    by_cases hj : j ∈ idx D
    · have hjm : j < D.R.m := by
        have h' := hj
        simp only [idx, List.mem_range'_1] at h'
        omega
      obtain ⟨δ, r, hδ, hHr, hfin⟩ := hr2 j hj hjm.le
      obtain ⟨δ', hδ', hfin'⟩ := hbI j hj
      have hdd : δ = δ' := GlobalTheory.TiltUnique.tilt_unique ch.G hjm δ δ' hδ hδ'
      subst hdd
      have hrf : r ∈ GfC _ := GlobalTheory.RowCover.mem_GfC_of_hasLoc t ch.S.B hjm.le r _ hHr
      obtain ⟨e, he, hse, hloc⟩ := id hHr
      exact ⟨r, fun _ => ⟨hrf, isFinOf_mul hfin hfin' hrf, e, he, hse, fun _ w => hloc w⟩, fun h' => absurd hj h'⟩
    · exact ⟨1, fun h' => absurd h' hj, fun _ => rfl⟩
  choose X hX using hX
  refine ⟨fun S j => if j = 0 then p j * cutS eL Sᶜ (b₀ j) else p j * b₀ j * cutS eL S (X j), ?_, ?_, ?_⟩
  · funext j
    dsimp only
    rw [Pi.mul_apply]
    split_ifs with hj0
    · subst hj0
      rw [Finset.compl_empty, cutS_univ he₀ hL hs₀]
    · rw [cutS_empty, mul_one]
  · funext j
    dsimp only
    rw [Pi.mul_apply]
    split_ifs with hj0
    · subst hj0
      rw [Finset.compl_univ, cutS_empty, mul_one, hr1 0 h0i, mul_one]
    · by_cases hji : j ∈ idx D
      · obtain ⟨-, hbX, e, he, hse, -⟩ := (hX j).1 hji
        rw [cutS_univ he hL hse, hbX, mul_assoc]
      · rw [(hX j).2 hji, cutS_one he₀ hL, hr1 j hji, hb1 j hj0 hji, mul_one]
  · intro S w hw
    have hwc : w ∈ Sᶜ := Finset.mem_compl.2 hw
    obtain ⟨hw1, hw2⟩ := mul_self_and_mul_cA_eq_zero_of_isIdemAt (hL w)
    have hfw := idem_conj_sum hw1 hw2
    refine ⟨fun j => if j = 0 then 1 else cutPart (eL w + cA D (eL w)) _ (X j),
      fun j => if j = 0 then cutPart (eL w + cA D (eL w)) _ (b₀ j) else 1,
      fun j => if j = 0 then p j * cutS eL (Sᶜ.erase w) (b₀ j) else p j * b₀ j * cutS eL S (X j),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      dsimp only
      by_cases hj0 : j = 0
      · subst hj0
        rw [if_pos rfl, if_neg h0i, map_one, map_one]
        exact ⟨suppAt_one_twisted_operators, rfl⟩
      · rw [if_neg hj0]
        by_cases hji : j ∈ idx D
        · obtain ⟨-, -, e, -, -, hloc⟩ := (hX j).1 hji
          rw [if_pos hji, inBasis_cut (hL w), hloc hj w]
          exact ⟨suppAt_cutPart hw1 hw2 _ _, rfl⟩
        · rw [if_neg hji, (hX j).2 hji, cut_one hfw, map_one, map_one]
          exact ⟨suppAt_one_twisted_operators, rfl⟩
    · intro j hj
      dsimp only
      by_cases hj0 : j = 0
      · subst hj0
        rw [if_pos rfl, if_pos rfl, inBasis_cut (hL w), hl₀ w]
        exact ⟨suppAt_cutPart hw1 hw2 _ _, rfl⟩
      · rw [if_neg hj0, if_neg hj0, map_one, map_one]
        exact ⟨suppAt_one_twisted_operators, rfl⟩
    · intro j _
      dsimp only
      by_cases hj0 : j = 0
      · subst hj0
        refine ⟨1, isTilt_one ch.G h0i, ?_⟩
        rw [if_pos rfl, inv_one, one_mul]
        exact mul_mem (real_mem_grpOff _ _ (hp.1 0)) (cutS_mem he₀ hL (Finset.notMem_erase w Sᶜ) _)
      · rw [if_neg hj0]
        by_cases hji : j ∈ idx D
        · obtain ⟨δ, hδ, hb₀f, a, ha, rfl⟩ := hbI j hji
          refine ⟨a * b₀ j, hδ, ?_⟩
          have hc : a⁻¹ * p j * b₀ j = b₀ j * (a⁻¹ * p j) :=
            GlobalTheory.AdelicSplit.commute_GinfC_GfC _ (mul_mem (inv_mem ha) (hp.1 j)) hb₀f
          have e4 : (a * b₀ j)⁻¹ * (p j * b₀ j * cutS eL S (X j)) = a⁻¹ * p j * cutS eL S (X j) := by
            rw [_root_.mul_inv_rev, show p j * b₀ j * cutS eL S (X j) = a * (a⁻¹ * p j * b₀ j) * cutS eL S (X j) by group, hc]
            group
          rw [e4]
          exact mul_mem (mul_mem (real_mem_grpOff _ _ (inv_mem ha)) (real_mem_grpOff _ _ (hp.1 j)))
            (cutS_mem he₀ hL hw _)
        · refine ⟨1, isTilt_one ch.G hji, ?_⟩
          rw [inv_one, one_mul, hb1 j hj0 hji, mul_one]
          exact mul_mem (real_mem_grpOff _ _ (hp.1 j)) (cutS_mem he₀ hL hw _)
    · funext j
      dsimp only
      rw [Pi.mul_apply]
      split_ifs with hj0
      · rw [mul_one, Finset.compl_insert]
      · rw [mul_assoc, cutS_insert he₀ hL hw]
    · funext j
      dsimp only
      rw [Pi.mul_apply]
      split_ifs with hj0
      · rw [mul_assoc, cutS_insert he₀ hL (Finset.notMem_erase w Sᶜ), Finset.insert_erase hwc]
      · rw [mul_one]

end GlobalTheory.PlaceChain

end
