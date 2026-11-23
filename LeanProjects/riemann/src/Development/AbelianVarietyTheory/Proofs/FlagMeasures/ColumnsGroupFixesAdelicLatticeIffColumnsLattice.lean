import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinkUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MiddleLatticeSelfDualAnisotropicPairingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedColumnLatticeHasLevelAndDualGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.St.G.Stabk

theorem span_subring_ind {A : Type} [CommRing A] {n : Type} (S : Subring A) (G : Set (n → A)) (P : (n → A) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ a ∈ S, ∀ x, P x → P (a • x)) (hg : ∀ x ∈ G, P x) :
    ∀ x ∈ Submodule.span S G, P x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hg y hy
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul c y _ hy => exact hsmul (c : A) c.2 y hy

theorem smul_mem_subring {A : Type} [CommRing A] {n : Type} {S : Subring A} (N : Submodule S (n → A)) {a : A}
    (ha : a ∈ S) {x : n → A} (hx : x ∈ N) : a • x ∈ N := N.smul_mem ⟨a, ha⟩ hx

theorem mulVec_span {A : Type} [CommRing A] {n : Type} [Fintype n] {S : Subring A} (N : Submodule S (n → A))
    (G : Set (n → A)) (Y : Matrix n n A) (hg : ∀ x ∈ G, Y *ᵥ x ∈ N) : ∀ x ∈ Submodule.span S G, Y *ᵥ x ∈ N := by
  refine span_subring_ind S G (fun x => Y *ᵥ x ∈ N) ?_ ?_ ?_ hg
  · simp
  · intro x y hx hy
    simpa [Matrix.mulVec_add] using N.add_mem hx hy
  · intro a ha x hx
    simpa [Matrix.mulVec_smul] using smul_mem_subring N ha hx

theorem gen_step {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {S : Subring A}
    (N : Submodule S (n → A)) (Y : Matrix n n A) {p q : n → A} {a : A} (ha : a ∈ S) (hp : p ∈ N)
    (hYp : Y *ᵥ p ∈ N) (hq : (Y - 1) *ᵥ q ∈ N) : (Y - 1) *ᵥ (p + a • q) ∈ N := by
  have e : (Y - 1) *ᵥ (p + a • q) = (Y *ᵥ p - p) + a • ((Y - 1) *ᵥ q) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e]
  exact N.add_mem (N.sub_mem hYp hp) (smul_mem_subring N ha hq)

theorem inv_stab {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {S : Subring A}
    (N : Submodule S (n → A)) (Y Yi : Matrix n n A) (h1 : Y * Yi = 1)
    (hst : ∀ x, x ∈ N ↔ Y *ᵥ x ∈ N) : ∀ x ∈ N, Yi *ᵥ x ∈ N := by
  intro x hx
  refine (hst _).2 ?_
  rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem inv_dq {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {S : Subring A}
    (N : Submodule S (n → A)) (Y Yi : Matrix n n A) (h1 : Yi * Y = 1)
    (hst : ∀ x ∈ N, Yi *ᵥ x ∈ N) {x : n → A} (hx : (Y - 1) *ᵥ x ∈ N) : (Yi - 1) *ᵥ x ∈ N := by
  have e : (Yi - 1) *ᵥ x = -(Yi *ᵥ ((Y - 1) *ᵥ x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, Matrix.mul_one, ← Matrix.neg_mulVec, neg_sub]
  rw [e]
  exact N.neg_mem (hst _ hx)

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)

theorem mem_span_q (hw : WittX X u wt) (y : (VS D).V) (he : ∀ a, (VS D).hT (X.eX a) y = 0)
    (hf : ∀ a, (VS D).hT (X.fY a) y = 0) (hz : (VS D).hT (X.zu u) y = 0) :
    ∃ w : Fin (D.R.N 0) → D.host.E, y = ∑ j, w j • qFr wt j := by
  obtain ⟨Q, Qi, G', hQQi, -, hq, hQe, hQf, hQz, -, -⟩ := qFrame_basis_gram D X u wt hw
  have crd_smul' : ∀ (c : D.host.E) (v : (VS D).V), X.crd (c • v) = X.ιE.symm c • X.crd v := fun c v => by
    funext i
    simp only [HidaSetting.crd, crdOf, Pi.smul_apply, map_smul, Finsupp.coe_smul, smul_eq_mul, map_mul]
  have crd_sum' : ∀ (f : (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) → (VS D).V),
      X.crd (∑ k, f k) = ∑ k, X.crd (f k) := by
    intro f
    funext i
    simp only [HidaSetting.crd, crdOf, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  have crd_inj : ∀ v w : (VS D).V, X.crd v = X.crd w → v = w := by
    intro v w h
    apply X.bas.repr.injective
    ext i
    have h' := congrFun h i
    simpa [HidaSetting.crd, crdOf] using h'
  have hcol : ∀ k i, X.crd (famQ X u wt k) i = Q i k := by
    intro k i
    rcases k with j | a | a | ⟨⟩
    · exact (hq j i).symm
    · exact (hQe a i).symm
    · exact (hQf a i).symm
    · exact (hQz i).symm
  set t := Qi *ᵥ X.crd y with ht
  have h1 : X.crd y = Q *ᵥ t := by
    rw [ht, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  have hv : X.crd (∑ k, X.ιE (t k) • famQ X u wt k) = X.crd y := by
    rw [crd_sum', h1]
    funext i
    simp only [crd_smul', RingEquiv.symm_apply_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcol,
      Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hy' : y = ∑ k, X.ιE (t k) • famQ X u wt k := (crd_inj _ _ hv).symm
  have hqe : ∀ j b, (VS D).hT (X.eX b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inl b))
  have hqf : ∀ j b, (VS D).hT (X.fY b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inl b)))
  have hqz : ∀ j, (VS D).hT (X.zu u) (qFr wt j) = 0 := fun j =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inr ())))
  have hF : ∀ b, X.ιE (t (Sum.inr (Sum.inr (Sum.inl b)))) = 0 := by
    intro b
    have h0 := he b
    rw [hy'] at h0
    simp [map_sum, Fintype.sum_sum_type, famQ, hqe, X.ee, X.ef, (X.zu_orth u b).1] at h0
    simpa using h0
  have hE : ∀ b, X.ιE (t (Sum.inr (Sum.inl b))) = 0 := by
    intro b
    have h0 := hf b
    rw [hy'] at h0
    simp [map_sum, Fintype.sum_sum_type, famQ, hqf, X.ff, hT_fe, (X.zu_orth u b).2] at h0
    simpa using h0
  have hZ : ∀ x : Unit, X.ιE (t (Sum.inr (Sum.inr (Sum.inr x)))) = 0 := by
    intro x
    cases x
    have h0 := hz
    rw [hy'] at h0
    simp [map_sum, Fintype.sum_sum_type, famQ, hqz, hT_ze, hT_zf, hT_zz_ne X u] at h0
    simpa using h0
  refine ⟨fun j => X.ιE (t (Sum.inl j)), ?_⟩
  conv_lhs => rw [hy']
  simp [Fintype.sum_sum_type, famQ, hE, hF, hZ]

theorem crd_mem_L {y : (VS D).V} (hy : y ∈ (VS D).L0) : X.crd y ∈ X.B.I.L := by
  rw [X.L_eq]
  convert hy using 1
  simp only [HidaSetting.crd, crdOf, RingEquiv.apply_symm_apply]
  exact X.bas.sum_repr y

theorem decomp (hw : WittX X u wt) {x₀ : (VS D).V} (hx₀ : x₀ ∈ X.Lb) (h1 : (VS D).hT (X.zu u) x₀ = 1)
    {y : (VS D).V} (hy : y ∈ (VS D).L0) :
    ∃ (c c' : Fin D.R.rS → D.host.E) (s : X.B.I.E) (w : Fin (D.R.N 0) → D.host.E),
      s ∈ (algebraMap (𝓞 X.B.I.E) X.B.I.E).range ∧ w ∈ Mq wt ∧
      y = ∑ a, c a • X.eX a + ∑ a, c' a • X.fY a + X.ιE s • x₀ + ∑ j, w j • qFr wt j := by
  obtain ⟨-, -, hsplit⟩ := GlobalTheory.T.middleLattice_selfDual_anisotropic_pairing D X u
  have hLb_L0 : X.Lb ≤ (VS D).L0 := by
    rw [X.Lam_split]
    exact le_sup_right.trans le_sup_left
  have hint : ∀ a ∈ (VS D).L0, ∀ b ∈ (VS D).L0,
      (VS D).hT a b ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro a ha b hb
    have hu := (VS D).baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular at hu
    have hb' : b ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 := by rw [hu]; exact hb
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hb'
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hb'
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hb' a ha)
    exact ⟨o, ho⟩
  have hy'Lb := hsplit y hy
  generalize hY : y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a = y' at hy'Lb
  obtain ⟨o, ho⟩ := hint _ (hLb_L0 (X.zu_Lb u)) _ (hLb_L0 hy'Lb)
  have hperp : ∀ a, (VS D).hT (X.eX a) (y' - (VS D).hT (X.zu u) y' • x₀) = 0 := by
    intro a
    rw [map_sub, map_smul, (X.Lb_perp _ hy'Lb a).1, (X.Lb_perp _ hx₀ a).1, smul_zero, sub_zero]
  have hperp' : ∀ a, (VS D).hT (X.fY a) (y' - (VS D).hT (X.zu u) y' • x₀) = 0 := by
    intro a
    rw [map_sub, map_smul, (X.Lb_perp _ hy'Lb a).2, (X.Lb_perp _ hx₀ a).2, smul_zero, sub_zero]
  have hzp : (VS D).hT (X.zu u) (y' - (VS D).hT (X.zu u) y' • x₀) = 0 := by
    rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, sub_self]
  obtain ⟨w, hw'⟩ := mem_span_q X u wt hw _ hperp hperp' hzp
  have hs : (VS D).hT (X.zu u) y' • x₀ ∈ X.Lb := by
    rw [← ho, algebraMap_smul]
    exact X.Lb.smul_mem o hx₀
  refine ⟨fun a => (VS D).hT (X.fY a) y, fun a => (VS D).hT (X.eX a) y,
    X.ιE.symm ((VS D).hT (X.zu u) y'), w, ?_, ?_, ?_⟩
  · refine ⟨NumberField.RingOfIntegers.mapRingEquiv X.ιE.symm o, ?_⟩
    rw [← ho]
    rfl
  · unfold Mq
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, Fintype.linearCombination_apply, ← hw']
    exact hLb_L0 (X.Lb.sub_mem hy'Lb hs)
  · rw [RingEquiv.apply_symm_apply, ← hw', ← hY]
    abel

def ic (v : (VS D).V) : VA X.B.I := incl X.B.I (X.crd v)

theorem ic_add (v w : (VS D).V) : ic X (v + w) = ic X v + ic X w := by
  funext i
  simp only [ic, incl, Pi.add_apply, HidaSetting.crd, crdOf, map_add, Finsupp.coe_add]

theorem ic_smul (a : D.host.E) (v : (VS D).V) :
    ic X (a • v) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm a) • ic X v := by
  funext i
  simp only [ic, incl, Pi.smul_apply, HidaSetting.crd, crdOf, map_smul, Finsupp.coe_smul, smul_eq_mul, map_mul]

theorem ic_zero : ic X (0 : (VS D).V) = 0 := by
  funext i
  simp [ic, incl, HidaSetting.crd, crdOf]

theorem ic_sum {ι : Type} (s : Finset ι) (f : ι → (VS D).V) : ic X (∑ i ∈ s, f i) = ∑ i ∈ s, ic X (f i) := by
  classical
  refine Finset.induction_on s (by simp [ic_zero]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, ic_add, ih]

variable {X u}

theorem fix_comb (h : Hfin X u) (c c' : Fin D.R.rS → D.host.E) :
    X.B.I.fmat (h : X.B.I.Gf) *ᵥ ic X (∑ a, c a • X.eX a + ∑ a, c' a • X.fY a) =
      ic X (∑ a, c a • X.eX a + ∑ a, c' a • X.fY a) := by
  have he : ∀ a, X.B.I.fmat (h : X.B.I.Gf) *ᵥ ic X (X.eX a) = ic X (X.eX a) := fun a =>
    h.2 (X.eR a) (Set.mem_union_left _ (Set.mem_union_left _ ⟨a, rfl⟩))
  have hf : ∀ a, X.B.I.fmat (h : X.B.I.Gf) *ᵥ ic X (X.fY a) = ic X (X.fY a) := fun a =>
    h.2 (X.fR a) (Set.mem_union_left _ (Set.mem_union_right _ ⟨a, rfl⟩))
  rw [ic_add, ic_sum, ic_sum]
  simp only [ic_smul, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, he, hf]

theorem isometry_fix_flagAnisotropicVector_of_fix_frame (h : Hfin X u) : X.B.I.fmat (h : X.B.I.Gf) *ᵥ ic X (X.zu u) = ic X (X.zu u) := by
  have hm : X.zR u ∈ fixSet X u := Set.mem_union_right _ rfl
  exact h.2 _ hm

def ratA (x : Fin (D.R.N 0) → D.host.E) : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F :=
  fun j => Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (x j)

theorem ratA_mem {L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)} {x : Fin (D.R.N 0) → D.host.E}
    (hx : x ∈ L) : ratA x ∈ hat D.host.F L := Submodule.subset_span ⟨x, hx, rfl⟩

theorem ratA_split (w d : Fin (D.R.N 0) → D.host.E) (a : D.host.E) :
    ratA w = ratA (w - a • d) + Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) a • ratA d := by
  funext j
  simp [ratA, map_sub, map_mul]

variable {wt} {ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F}

theorem embA_sub (x y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (x - y) = embA X wt ιA x - embA X wt ιA y := by
  unfold embA
  simp only [Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem key0 (hι : IsAdeleIso X ιA) (h : Hfin X u)
    (Yc : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] Ad D.host.F))
    (hrep : ∀ x, X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (Yc *ᵥ x))
    (w : Fin (D.R.N 0) → D.host.E) :
    embA X wt ιA ((Yc - 1) *ᵥ ratA w) =
      X.B.I.fmat (h : X.B.I.Gf) *ᵥ ic X (∑ j, w j • qFr wt j) - ic X (∑ j, w j • qFr wt j) := by
  have hr : embA X wt ιA (ratA w) = ic X (∑ j, w j • qFr wt j) := LinkCheck.embA_rat X wt ιA hι w
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, embA_sub, ← hrep, hr]

theorem key1 (hι : IsAdeleIso X ιA) (h : Hfin X u)
    (Yc : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] Ad D.host.F))
    (hrep : ∀ x, X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (Yc *ᵥ x))
    (d : Fin (D.R.N 0) → D.host.E) (x₀ : (VS D).V) (a : D.host.E)
    (hd : Fintype.linearCombination D.host.E (qFr wt) d = x₀ + a • X.zu u) :
    embA X wt ιA ((Yc - 1) *ᵥ ratA d) = X.B.I.fmat (h : X.B.I.Gf) *ᵥ ic X x₀ - ic X x₀ := by
  rw [key0 hι h Yc hrep d]
  have e : ∑ j, d j • qFr wt j = x₀ + a • X.zu u := by
    rw [← hd, Fintype.linearCombination_apply]
  rw [e, ic_add, ic_smul, Matrix.mulVec_add, Matrix.mulVec_smul, isometry_fix_flagAnisotropicVector_of_fix_frame h]
  abel

theorem dual_iff (hw : TLat (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (Mq wt))
    (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    x ∈ hat D.host.F (dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt)) ↔
      ∀ z ∈ hat D.host.F (Mq wt), hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) z x ∈
        OAd D.host.F D.host.E := by
  have hf := record_facts D u
  exact (dualL_local_adelic _ _ _ _ _ hf.2.2.2.2.2.1 hf.2.2.2.2.2.2 _ hw.1).2.2 x

theorem carry (hw : WittX X u wt) (hι : IsAdeleIso X ιA) (h : Hfin X u)
    (Yc : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] Ad D.host.F))
    (hrep : ∀ x, X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (Yc *ᵥ x))
    (hst : ∀ x ∈ hat D.host.F (Mq wt), Yc *ᵥ x ∈ hat D.host.F (Mq wt))
    (hq : ∀ x, (∀ z ∈ hat D.host.F (Mq wt), hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) z x ∈
        OAd D.host.F D.host.E) → (Yc - 1) *ᵥ x ∈ hat D.host.F (Mq wt)) :
    ∀ v ∈ X.B.I.Lf, X.B.I.fmat (h : X.B.I.Gf) *ᵥ v ∈ X.B.I.Lf := by
  obtain ⟨hTL, x₀, hx₀, h1, d, hd, hdx, -⟩ := GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator D X u wt hw
  obtain ⟨hembL, -, -, -, -, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hw hι
  intro v hv
  refine mulVec_span X.B.I.Lf
    (Set.range fun x : X.B.I.L => fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((x : Fin X.B.I.n → X.B.I.E) i))
    (X.B.I.fmat (h : X.B.I.Gf)) ?_ v hv
  rintro _ ⟨⟨x, hxL⟩, rfl⟩
  have hyL0 : (∑ i, X.ιE (x i) • X.bas i) ∈ (VS D).L0 := (X.L_eq x).1 hxL
  have hcy : X.crd (∑ i, X.ιE (x i) • X.bas i) = x := by
    funext i
    simp [HidaSetting.crd, crdOf, Finsupp.single_apply]
  have hgen : ic X (∑ i, X.ιE (x i) • X.bas i) = fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (x i) := by
    unfold ic incl
    rw [hcy]
  obtain ⟨c, c', s, w, hs, hwM, hyeq⟩ := decomp X u wt hw hx₀ h1 hyL0
  have hA : (Yc - 1) *ᵥ ratA w ∈ hat D.host.F (Mq wt) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact Submodule.sub_mem _ (hst _ (ratA_mem hwM)) (ratA_mem hwM)
  have hB : (Yc - 1) *ᵥ ratA d ∈ hat D.host.F (Mq wt) := hq _ ((dual_iff hTL (ratA d)).1 (ratA_mem hd))
  have hS : Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) s ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Or.inl ⟨⟨s, hs⟩, rfl⟩)
  have key : X.B.I.fmat (h : X.B.I.Gf) *ᵥ ic X (∑ i, X.ιE (x i) • X.bas i) =
      ic X (∑ i, X.ιE (x i) • X.bas i) +
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) s • embA X wt ιA ((Yc - 1) *ᵥ ratA d) +
        embA X wt ιA ((Yc - 1) *ᵥ ratA w) := by
    rw [key1 hι h Yc hrep d x₀ _ hdx, key0 hι h Yc hrep w, hyeq,
      ic_add X (∑ a, c a • X.eX a + ∑ a, c' a • X.fY a + X.ιE s • x₀) (∑ j, w j • qFr wt j),
      ic_add X (∑ a, c a • X.eX a + ∑ a, c' a • X.fY a) (X.ιE s • x₀), ic_smul X (X.ιE s) x₀,
      RingEquiv.symm_apply_apply, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, fix_comb h c c',
      smul_sub]
    abel
  show X.B.I.fmat (h : X.B.I.Gf) *ᵥ (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (x i)) ∈ X.B.I.Lf
  rw [← hgen, key]
  refine X.B.I.Lf.add_mem (X.B.I.Lf.add_mem ?_ ?_) ((hembL _).1 hA)
  · rw [hgen]
    exact Submodule.subset_span ⟨⟨x, hxL⟩, rfl⟩
  · exact smul_mem_subring X.B.I.Lf hS ((hembL _).1 hB)

end GlobalTheory.St.G.Stabk

namespace GlobalTheory.St.G

open GlobalTheory.St.G.Stabk in

theorem stabK_iff : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ((h : X.B.I.Gf) ∈ X.B.I.Kset ↔ ((∀ x, x ∈ hat D.host.F (Mq wt) ↔ y.1.1 *ᵥ x ∈ hat D.host.F (Mq wt)) ∧ ∀ x, (∀ z ∈ hat D.host.F (Mq wt), hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) z x ∈ OAd D.host.F D.host.E) → (y.1.1 - 1) *ᵥ x ∈ hat D.host.F (Mq wt))) := by
  intro D X u wt ιA hw hι h y hr
  obtain ⟨hTL, x₀, hx₀, h1, d, hd, hdx, hdual⟩ := GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator D X u wt hw
  obtain ⟨hembL, -, -, -, -, hrepAll⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hw hι
  have hrep := hrepAll h y hr
  obtain ⟨Yi, hYYi, hYiY⟩ : ∃ Yi, y.1.1 * Yi = 1 ∧ Yi * y.1.1 = 1 :=
    ⟨_, Units.mul_inv y.1, Units.inv_mul y.1⟩
  have hK : (h : X.B.I.Gf) ∈ X.B.I.Kset ↔
      ∀ v, v ∈ X.B.I.Lf ↔ X.B.I.fmat (h : X.B.I.Gf) *ᵥ v ∈ X.B.I.Lf := Iff.rfl
  rw [hK]
  constructor
  · intro hKh
    have hS : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ y.1.1 *ᵥ x ∈ hat D.host.F (Mq wt) := by
      intro x
      rw [hembL, hembL, ← hrep]
      exact hKh _
    refine ⟨hS, ?_⟩
    have hx₀L : ic X x₀ ∈ X.B.I.Lf := by
      have hx₀L0 : x₀ ∈ (VS D).L0 := by
        rw [X.Lam_split]
        exact (le_sup_right.trans le_sup_left : X.Lb ≤ _) hx₀
      exact Submodule.subset_span ⟨⟨X.crd x₀, crd_mem_L X hx₀L0⟩, rfl⟩
    have hdq : (y.1.1 - 1) *ᵥ ratA d ∈ hat D.host.F (Mq wt) := by
      rw [hembL, key1 hι h y.1.1 hrep d x₀ _ hdx]
      exact Submodule.sub_mem _ ((hKh _).1 hx₀L) hx₀L
    intro x hx
    have hxd := (dual_iff hTL x).2 hx
    refine span_subring_ind _ _ (fun x => (y.1.1 - 1) *ᵥ x ∈ hat D.host.F (Mq wt)) ?_ ?_ ?_ ?_ x hxd
    · simp
    · intro a b ha hb
      simpa [Matrix.mulVec_add] using Submodule.add_mem _ ha hb
    · intro a ha b hb
      simpa [Matrix.mulVec_smul] using smul_mem_subring _ ha hb
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨a, ha⟩ := hdual z hz
      have hAint : Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (a : D.host.E) ∈ OAd D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨(a : D.host.E), ⟨a, rfl⟩⟩, rfl⟩)
      show (y.1.1 - 1) *ᵥ ratA z ∈ hat D.host.F (Mq wt)
      rw [ratA_split z d (a : D.host.E)]
      exact gen_step _ _ hAint (ratA_mem ha) ((hS _).1 (ratA_mem ha)) hdq
  · rintro ⟨hS, hdq⟩
    have hst : ∀ x ∈ hat D.host.F (Mq wt), y.1.1 *ᵥ x ∈ hat D.host.F (Mq wt) := fun x hx => (hS x).1 hx
    have hst' := inv_stab (hat D.host.F (Mq wt)) y.1.1 Yi hYYi hS
    have hq' : ∀ x, (∀ z ∈ hat D.host.F (Mq wt), hR (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) z x ∈ OAd D.host.F D.host.E) →
        (Yi - 1) *ᵥ x ∈ hat D.host.F (Mq wt) :=
      fun x hx => inv_dq (hat D.host.F (Mq wt)) y.1.1 Yi hYiY hst' (hdq x hx)
    have hinv : X.B.I.fmat ((h⁻¹ : Hfin X u) : X.B.I.Gf) * X.B.I.fmat (h : X.B.I.Gf) = 1 := by
      exact Units.inv_mul _
    have hrep' : ∀ x, X.B.I.fmat ((h⁻¹ : Hfin X u) : X.B.I.Gf) *ᵥ embA X wt ιA x =
        embA X wt ιA (Yi *ᵥ x) := by
      intro x
      have e1 : embA X wt ιA x = X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA (Yi *ᵥ x) := by
        rw [hrep, Matrix.mulVec_mulVec, hYYi, Matrix.one_mulVec]
      rw [e1, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    intro v
    constructor
    · exact carry hw hι h y.1.1 hrep hst hdq v
    · intro hv
      have e2 : v = X.B.I.fmat ((h⁻¹ : Hfin X u) : X.B.I.Gf) *ᵥ (X.B.I.fmat (h : X.B.I.Gf) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [e2]
      exact carry hw hι h⁻¹ Yi hrep' hst' hq' _ hv

end GlobalTheory.St.G

end
