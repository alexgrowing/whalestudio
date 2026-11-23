import Formalism.SharpRestriction.InertJacobiLevels.VVEqEmptyOfNotIsResidueClassZero
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section Drop

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts) (Cr : ℝ)
  (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
  (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
  (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)

def tieL : SizeData₂ D := tieWeightData L0 X0 K {p | NoGain X0 K Cr p} len hw hg hu

def tieX : G.Inst D (tieL L0 X0 K Cr len hw hg hu) := tieInst L0 X0 K {p | NoGain X0 K Cr p} len hw hg hu

theorem tieL_drop_iff (p : ℕ) :
    p ∈ (tieL L0 X0 K Cr len hw hg hu).drop ↔
      NoGain (tieX L0 X0 K Cr len hw hg hu) K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T :=
  Iff.rfl

theorem tieL_supp_sat (w : D.what₂.places.Pl)
    (h : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ (tieL L0 X0 K Cr len hw hg hu).sc.X'' D.R.n) :
    w ∈ (tieL L0 X0 K Cr len hw hg hu).supp :=
  tie_supp_sat L0 X0 K _ len hw hg hu w h

theorem tieL_fills
    (hf : ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × G.HH D),
      (D.eTau τ : D.R.GG) = G.plGG D z → G.fill X0 (G.bL L0) j z = wj D j τ)
    (w : D.what₂.places.Pl) : G.ParametersFill (tieX L0 X0 K Cr len hw hg hu) K w :=
  tie_fills L0 X0 K _ len hw hg hu hf w

theorem tieL_keeps :
    (tieL L0 X0 K Cr len hw hg hu).sc = L0.sc ∧ (tieL L0 X0 K Cr len hw hg hu).aT = L0.aT ∧
    (tieL L0 X0 K Cr len hw hg hu).bT = L0.bT ∧ (tieL L0 X0 K Cr len hw hg hu).etaSz = L0.etaSz ∧
    (tieL L0 X0 K Cr len hw hg hu).Sc = L0.Sc ∧ (tieL L0 X0 K Cr len hw hg hu).Cc = L0.Cc ∧
    (tieL L0 X0 K Cr len hw hg hu).Ct = L0.Ct ∧ (tieL L0 X0 K Cr len hw hg hu).CGam = L0.CGam ∧
    (tieL L0 X0 K Cr len hw hg hu).de2 = L0.de2 ∧ (tieL L0 X0 K Cr len hw hg hu).j0 = L0.j0 ∧
    (tieL L0 X0 K Cr len hw hg hu).F = Fval L0 ∧ (tieL L0 X0 K Cr len hw hg hu).E = L0.E ∧
    (tieL L0 X0 K Cr len hw hg hu).NuLat = L0.NuLat ∧ (tieL L0 X0 K Cr len hw hg hu).LaG = G.La K L0.sc ∧
    (tieL L0 X0 K Cr len hw hg hu).lenMN = len ∧
    (tieX L0 X0 K Cr len hw hg hu).bs = X0.bs ∧ (tieX L0 X0 K Cr len hw hg hu).off = X0.off ∧
    (tieX L0 X0 K Cr len hw hg hu).kapI = X0.kapI ∧ (tieX L0 X0 K Cr len hw hg hu).ep = X0.ep :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Drop

structure FieldData where
  φ : Formalism.HC.Frame
  E : Type
  [fld : Field E]
  [nf : NumberField E]
  gal : (E ≃ₐ[ℚ] E) ≃* φ.GG
  N : ℕ
  ζ : CyclotomicField N ℚ
  a : E
  b : E

attribute [instance] FieldData.fld FieldData.nf

def FieldData.e (F : FieldData) : ℕ := F.φ.e

abbrev FieldData.Lf (F : FieldData) : Type := F.E

def FieldData.hval (F : FieldData) (p : ℕ) : ℕ :=
  (F.φ.iotaInv (Classical.epsilon (fun g : F.φ.GG =>
    ∃ (P : Ideal (𝓞 F.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : F.E ≃ₐ[ℚ] F.E), IsArithFrobAt ℤ σ P ∧ F.gal σ = g)).2).val

def fieldDataH (x : Σ R : Ranks, Host R) : FieldData :=
  ⟨x.1.toFrame, x.2.E, x.2.gal, x.2.condN, x.2.cycZeta, x.2.sqq, x.2.sqd⟩

def fieldData (D : D7) : FieldData := fieldDataH ⟨D.R, D.host⟩

theorem hP_val (D : D7) (p : ℕ) : (G.hP D p).val = (fieldData D).hval p := rfl

theorem hP_val_eq {D D' : D7} (h : fieldData D = fieldData D') (p : ℕ) : (G.hP D p).val = (G.hP D' p).val := by
  rw [hP_val, hP_val, h]

theorem bsC_val_eq {N N' : ℕ} [NeZero N] [NeZero N'] (hN : N = N') (h t : ZMod N) (h' t' : ZMod N')
    (hh : h.val = h'.val) (ht : t.val = t'.val) : (bsC h t).val = (bsC h' t').val := by
  rw [bsC_val, bsC_val, hh, ht, hN]

theorem bsA_val_eq {φ φ' : Formalism.HC.Frame} (hφ : φ = φ') (h t : φ.A) (h' t' : φ'.A)
    (hh : h.val = h'.val) (ht : t.val = t'.val) : (bsA h t).val = (bsA h' t').val := by
  subst hφ
  rw [Formalism.HC.Frame.A.val_injective _ hh, Formalism.HC.Frame.A.val_injective _ ht]

theorem mem_TT_iff_val {D D' : D7} (_he : D.R.e = D'.R.e)
    (hTT : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val) (t : G.HH D) (t' : G.HH D')
    (ht : t.val = t'.val) : t ∈ D.host.TT ↔ t' ∈ D'.host.TT := by
  constructor
  · intro h
    have h1 : t.val ∈ D'.host.TT.image Formalism.HC.Frame.A.val := hTT ▸ Finset.mem_image_of_mem _ h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h1
    have : s = t' := Formalism.HC.Frame.A.val_injective _ (hst.trans ht)
    exact this ▸ hs
  · intro h
    have h1 : t'.val ∈ D.host.TT.image Formalism.HC.Frame.A.val := hTT ▸ Finset.mem_image_of_mem _ h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h1
    have : s = t := Formalism.HC.Frame.A.val_injective _ (hst.trans ht.symm)
    exact this ▸ hs

theorem offC_false_eq {D D' : D7} (hR : D.R = D'.R)
    (hTT : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val) (sc : Scale) (j : ℕ) (t : G.HH D) (t' : G.HH D')
    (ht : t.val = t'.val) : offC D sc j (false, t) = offC D' sc j (false, t') := by
  have h1 : G.IsTopPl D (false, t) ↔ G.IsTopPl D' (false, t') := by
    unfold G.IsTopPl
    simp only [true_and]
    exact mem_TT_iff_val (congrArg (fun R : Ranks => R.e) hR) hTT t t' ht
  have h2 : ¬ G.IsThickPl D (false, t) := fun h => Bool.noConfusion h.1
  have h3 : ¬ G.IsThickPl D' (false, t') := fun h => Bool.noConfusion h.1
  unfold offC
  rw [if_neg h2, if_neg h3, hR]
  by_cases h : G.IsTopPl D (false, t)
  · rw [if_pos h, if_pos (h1.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (h1.2 h'))]

theorem val_dig_add {φ φ' : Formalism.HC.Frame} (h : φ = φ') (s : ℕ) (u : φ.A) (u' : φ'.A) (hu : u.val = u'.val) :
    (φ.dig s + u).val = (φ'.dig s + u').val := by
  subst h
  rw [Formalism.HC.Frame.A.val_injective _ hu]

theorem thick_iff_val {D D' : D7} (he : D.R.toFrame = D'.R.toFrame) (hT2 : D.host.T2 = D'.host.T2)
    (hu0 : D.host.u0.val = D'.host.u0.val) (t : G.HH D) (t' : G.HH D') (ht : t.val = t'.val) :
    G.IsThickPl D (true, t) ↔ G.IsThickPl D' (true, t') := by
  have key : ∀ (E E' : D7), E.R.toFrame = E'.R.toFrame → E.host.T2 = E'.host.T2 → E.host.u0.val = E'.host.u0.val →
      ∀ (t : G.HH E) (t' : G.HH E'), t.val = t'.val → G.IsThickPl E (true, t) → G.IsThickPl E' (true, t') := by
    intro E E' he hT2 hu0 t t' ht h
    obtain ⟨-, h⟩ := h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    refine ⟨rfl, Finset.mem_image.2 ⟨s, hT2 ▸ hs, ?_⟩⟩
    apply Formalism.HC.Frame.A.val_injective
    have h1 : (E.R.dig s + E.host.u0).val = t.val := congrArg Formalism.HC.Frame.A.val hst
    rw [← ht, ← h1]
    exact val_dig_add he.symm s _ _ hu0.symm
  exact ⟨key D D' he hT2 hu0 t t' ht, key D' D he.symm hT2.symm hu0.symm t' t ht.symm⟩

theorem offC_eq {D D' : D7} (hR : D.R = D'.R)
    (hTT : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val) (hT2 : D.host.T2 = D'.host.T2)
    (hu0 : D.host.u0.val = D'.host.u0.val) (sc : Scale) (j : ℕ) (c : Bool) (t : G.HH D) (t' : G.HH D')
    (ht : t.val = t'.val) : offC D sc j (c, t) = offC D' sc j (c, t') := by
  cases c
  · exact offC_false_eq hR hTT sc j t t' ht
  · have h1 := thick_iff_val (congrArg Ranks.toFrame hR) hT2 hu0 t t' ht
    have h2 : ¬ G.IsTopPl D (true, t) := fun h => Bool.noConfusion h.1
    have h3 : ¬ G.IsTopPl D' (true, t') := fun h => Bool.noConfusion h.1
    unfold offC
    rw [if_neg h2, if_neg h3, hR]
    by_cases h : G.IsThickPl D (true, t)
    · rw [if_pos h, if_pos (h1.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (h1.2 h'))]

theorem offW_true_eq {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hR : D.R = D'.R)
    (hTT : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val) (hT2 : D.host.T2 = D'.host.T2)
    (hu0 : D.host.u0.val = D'.host.u0.val) (hsc : L.sc = L'.sc) (j : ℕ)
    (t : G.HH D) (t' : G.HH D') (ht : t.val = t'.val)
    (hwj : 1 ≤ j → j ≤ D.R.m → wj D j (tauOf D (true, t)) = wj D' j (tauOf D' (true, t'))) :
    offW L j (true, t) = offW L' j (true, t') := by
  have hl : j ∈ SizeData₂.lifts D ↔ j ∈ SizeData₂.lifts D' := by unfold SizeData₂.lifts; rw [hR]
  unfold offW
  by_cases hj : j ∈ SizeData₂.lifts D
  · rw [if_pos hj, if_pos (hl.1 hj)]
    have hj' := Finset.mem_Icc.1 hj
    rw [if_neg (fun h => Bool.noConfusion h.1), if_neg (fun h => Bool.noConfusion h.1), hwj hj'.1 hj'.2]
  · rw [if_neg hj, if_neg (fun h' => hj (hl.2 h')), hsc]
    exact offC_eq hR hTT hT2 hu0 _ j true t t' ht

theorem offW_false_eq {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hR : D.R = D'.R)
    (hTT : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val) (hsc : L.sc = L'.sc) (j : ℕ)
    (t : G.HH D) (t' : G.HH D') (ht : t.val = t'.val)
    (hwj : 1 ≤ j → j ≤ D.R.m → wj D j (tauOf D (false, t)) - (G.bL L t : ℝ) =
      wj D' j (tauOf D' (false, t')) - (G.bL L' t' : ℝ)) :
    offW L j (false, t) = offW L' j (false, t') := by
  have hl : j ∈ SizeData₂.lifts D ↔ j ∈ SizeData₂.lifts D' := by unfold SizeData₂.lifts; rw [hR]
  have hm := mem_TT_iff_val (congrArg (fun R : Ranks => R.e) hR) hTT t t' ht
  unfold offW
  by_cases hj : j ∈ SizeData₂.lifts D
  · rw [if_pos hj, if_pos (hl.1 hj)]
    have hj' := Finset.mem_Icc.1 hj
    have h0 := hwj hj'.1 hj'.2
    by_cases h : t ∈ D.host.TT
    · rw [if_pos ⟨rfl, h⟩, if_pos ⟨rfl, hm.1 h⟩]
      exact h0
    · have e1 : G.bL L t = 0 := by unfold G.bL; rw [dif_neg h]
      have e2 : G.bL L' t' = 0 := by unfold G.bL; rw [dif_neg (fun h' => h (hm.2 h'))]
      rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h (hm.2 h'.2))]
      simp only [e1, e2, Int.cast_zero] at h0
      exact h0
  · rw [if_neg hj, if_neg (fun h' => hj (hl.2 h')), hsc]
    exact offC_false_eq hR hTT _ j t t' ht

section Totals

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts) (dr : Set ℕ)
  (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
  (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
  (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)

theorem mem_suppAt_below (p : ℕ) (hle : (p : ℝ) ≤ L0.sc.X'' D.R.n) (w : D.what₂.places.Pl) :
    w ∈ suppAt (tieWeightData L0 X0 K dr len hw hg hu) p ↔ D.what₂.places.resChar w = p := by
  unfold suppAt
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨tie_supp_sat L0 X0 K dr len hw hg hu w (by rw [h]; exact hle), h⟩

theorem sum_sz_const (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p) (c : ℝ) :
    ∑ w ∈ S, SizeData₂.sz w c = 2 * Real.log p * c := by
  have h := factEtaMean D p hp S hS
  unfold SizeData₂.sz SizeData₂.lwP
  rw [← h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  ring

open Classical in

theorem tie_gainTot_below (p : ℕ) (hp : p.Prime) (hle : (p : ℝ) ≤ L0.sc.X'' D.R.n) :
    gainTot (tieWeightData L0 X0 K dr len hw hg hu) p = 2 * Real.log p *
      ((if G.IsResidueClassZero D p ∨ G.IsSg D p then ∑ j ∈ SizeData₂.lifts D, G.gainP X0 K (G.aL L0) (G.bL L0) p j else 0) -
        G.tauP X0 K (G.aL L0) (G.bL L0) p) := by
  have hS := mem_suppAt_below L0 X0 K dr len hw hg hu p hle
  rw [← sum_sz_const p hp _ hS]
  unfold gainTot
  refine Finset.sum_congr rfl (fun w hw' => ?_)
  have hwp : D.what₂.places.resChar w = p := (hS w).1 hw'
  have hws : w ∈ tieSupp L0 := (Finset.mem_filter.1 hw').1
  congr 1
  show (∑ j ∈ SizeData₂.lifts D, if w ∈ tieSupp L0 ∧ (G.IsResidueClassZero D (D.what₂.places.resChar w) ∨
      G.IsSg D (D.what₂.places.resChar w)) then
        G.gainP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) j else 0) -
      G.tauP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) = _
  rw [hwp]
  by_cases hin : G.IsResidueClassZero D p ∨ G.IsSg D p
  · simp only [if_pos hin, if_pos (And.intro hws hin)]
  · simp only [if_neg hin, if_neg (fun h : w ∈ tieSupp L0 ∧ (G.IsResidueClassZero D p ∨ G.IsSg D p) => hin h.2),
      Finset.sum_const_zero]

theorem gainP_eq_zero_of_lt (a b : G.HH D → ℤ) (p j : ℕ) (h : L0.sc.X'' D.R.n < (p : ℝ)) :
    G.gainP X0 K a b p j = 0 := by
  unfold G.gainP
  rw [if_pos (Or.inr h)]

open Classical in

theorem tie_gainTot_above (p : ℕ) (h : L0.sc.X'' D.R.n < (p : ℝ)) :
    gainTot (tieWeightData L0 X0 K dr len hw hg hu) p = 0 := by
  unfold gainTot
  refine Finset.sum_eq_zero (fun w hw' => ?_)
  have hwp : D.what₂.places.resChar w = p := (Finset.mem_filter.1 hw').2
  have e : (∑ j ∈ SizeData₂.lifts D, (tieWeightData L0 X0 K dr len hw hg hu).gain j w) -
      (tieWeightData L0 X0 K dr len hw hg hu).tau w = 0 := by
    show (∑ j ∈ SizeData₂.lifts D, if w ∈ tieSupp L0 ∧ (G.IsResidueClassZero D (D.what₂.places.resChar w) ∨
      G.IsSg D (D.what₂.places.resChar w)) then
        G.gainP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) j else 0) -
      G.tauP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) = 0
    rw [hwp, tauP_above L0 X0 K _ _ _ h, sub_zero]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [gainP_eq_zero_of_lt L0 X0 K _ _ _ _ h, ite_self]
  rw [e]
  simp [SizeData₂.sz]

theorem tie_ioTot_below (p : ℕ) (hp : p.Prime) (hle : (p : ℝ) ≤ L0.sc.X'' D.R.n) :
    ioTot (tieWeightData L0 X0 K dr len hw hg hu) p = 2 * Real.log p * G.ioP X0 K (G.aL L0) (G.bL L0) p := by
  have hS := mem_suppAt_below L0 X0 K dr len hw hg hu p hle
  rw [← sum_sz_const p hp _ hS]
  unfold ioTot
  refine Finset.sum_congr rfl (fun w hw' => ?_)
  have hwp : D.what₂.places.resChar w = p := (hS w).1 hw'
  show SizeData₂.sz w (G.ioP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w)) = _
  rw [hwp]

theorem tie_ioTot_above (p : ℕ) (h : L0.sc.X'' D.R.n < (p : ℝ)) :
    ioTot (tieWeightData L0 X0 K dr len hw hg hu) p = 0 := by
  unfold ioTot
  refine Finset.sum_eq_zero (fun w hw' => ?_)
  have hwp : D.what₂.places.resChar w = p := (Finset.mem_filter.1 hw').2
  show SizeData₂.sz w (G.ioP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w)) = 0
  rw [hwp, ioP_eq_zero_of_lt L0 X0 K _ _ _ h]
  simp [SizeData₂.sz]

theorem tie_TTw_vals (w : D.what₂.places.Pl) :
    ((tieWeightData L0 X0 K dr len hw hg hu).TTw w).image (fun t : D.host.TT => (t : D.R.A).val) =
      (G.TTP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w)).image Formalism.HC.Frame.A.val := by
  have h : ((tieWeightData L0 X0 K dr len hw hg hu).TTw w).map (Function.Embedding.subtype _) =
      G.TTP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) :=
    Finset.subtype_map_of_mem (TTP_subset L0 X0 K _ _ _)
  rw [← h, Finset.map_eq_image, Finset.image_image]
  rfl

theorem tie_TTwVals_of_mem (p : ℕ) (w0 : D.what₂.places.Pl)
    (h0 : w0 ∈ suppAt (tieWeightData L0 X0 K dr len hw hg hu) p) :
    TTwVals (tieWeightData L0 X0 K dr len hw hg hu) p = {(G.TTP X0 K (G.aL L0) (G.bL L0) p).image Formalism.HC.Frame.A.val} := by
  unfold TTwVals
  ext s
  rw [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨w, hw', rfl⟩
    rw [tie_TTw_vals, (Finset.mem_filter.1 hw').2]
  · rintro rfl
    refine ⟨w0, h0, ?_⟩
    rw [tie_TTw_vals, (Finset.mem_filter.1 h0).2]

theorem tie_TTwVals_below (p : ℕ) (hp : p.Prime) (hle : (p : ℝ) ≤ L0.sc.X'' D.R.n) :
    TTwVals (tieWeightData L0 X0 K dr len hw hg hu) p = {(G.TTP X0 K (G.aL L0) (G.bL L0) p).image Formalism.HC.Frame.A.val} := by
  obtain ⟨w0, h0⟩ := exists_place_over D p hp
  exact tie_TTwVals_of_mem L0 X0 K dr len hw hg hu p w0 ((mem_suppAt_below L0 X0 K dr len hw hg hu p hle w0).2 h0)

def UnderSupp (p : ℕ) : Prop :=
  (p : ℝ) ≤ L0.sc.X'' D.R.n ∨ p ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨
    ∃ w ∈ L0.supp, D.what₂.places.resChar w = p

open Classical in

theorem tie_TTwVals (p : ℕ) (hp : p.Prime) :
    TTwVals (tieWeightData L0 X0 K dr len hw hg hu) p =
      if UnderSupp L0 p then {(G.TTP X0 K (G.aL L0) (G.bL L0) p).image Formalism.HC.Frame.A.val} else ∅ := by
  by_cases h : UnderSupp L0 p
  · rw [if_pos h]
    have hex : ∃ w0, w0 ∈ suppAt (tieWeightData L0 X0 K dr len hw hg hu) p := by
      rcases h with h | h | ⟨w, hw', hwp⟩
      · obtain ⟨w0, h0⟩ := exists_place_over D p hp
        exact ⟨w0, Finset.mem_filter.2 ⟨(mem_tieSupp L0 w0).2 (Or.inl (by rw [h0]; exact h)), h0⟩⟩
      · obtain ⟨w0, h0⟩ := exists_place_over D p hp
        exact ⟨w0, Finset.mem_filter.2 ⟨(mem_tieSupp L0 w0).2 (Or.inr (Or.inl (by rw [h0]; exact h))), h0⟩⟩
      · exact ⟨w, Finset.mem_filter.2 ⟨(mem_tieSupp L0 w).2 (Or.inr (Or.inr hw')), hwp⟩⟩
    obtain ⟨w0, h0⟩ := hex
    exact tie_TTwVals_of_mem L0 X0 K dr len hw hg hu p w0 h0
  · rw [if_neg h]
    unfold TTwVals
    rw [Finset.image_eq_empty]
    unfold suppAt
    rw [Finset.filter_eq_empty_iff]
    intro w hw' hwp
    apply h
    rcases (mem_tieSupp L0 w).1 hw' with h1 | h1 | h1
    · exact Or.inl (by rw [← hwp]; exact h1)
    · exact Or.inr (Or.inl (by rw [← hwp]; exact h1))
    · exact Or.inr (Or.inr ⟨w, h1, hwp⟩)

end Totals

end Formalism.MainNotions.Inhab

end
