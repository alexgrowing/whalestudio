import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.FlatThreeSteps

open Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.TwoStepModel GlobalTheory.FlatVecSum

section Places

variable {D : D7}

theorem idem_ne_zero {a : AE D} {Q : Pl D.host.E} (h : IsIdemAt a Q) : a ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
  have := (h.2 x hx0).1 hx
  rw [zero_mul, RingHom.map_zero] at this
  exact this (zero_mem _)

theorem eq_of_mul_ne_zero {a b : AE D} {P Q : Pl D.host.E} (ha : IsIdemAt a P) (hb : IsIdemAt b Q) (h : a * b ≠ 0) : P = Q := by
  have e := (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero ha.1 hb.1).resolve_right h
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [ha.2 x hx, hb.2 x hx, e]

theorem isIdemAt_conj {a : AE D} {P : Pl D.host.E} (h : IsIdemAt a P) : IsIdemAt (cA D a) (conjPl P) :=
  GlobalTheory.MovedIdem.isIdemAt_conj h fun _ => Iff.rfl

theorem idemAt_conj {P : Pl D.host.E} (h : IsIdemAt (idemAt P) P) : idemAt (conjPl P) = cA D (idemAt P) :=
  idemAt_eq (isIdemAt_conj h)

theorem conj_notMem {A : Finset (Pl D.host.E)} (hA : SplitSet A) {P : Pl D.host.E} (hP : P ∈ A) : conjPl P ∉ A := fun h => by
  have h0 := hA.mul_conj h hP
  rw [← idemAt_conj (hA.isIdemAt hP), (hA.isIdemAt h).1.1] at h0
  exact idem_ne_zero (hA.isIdemAt h) h0

theorem mem_or_conj_mem {A B : Finset (Pl D.host.E)} (hA : SplitSet A) (hB : SplitSet B)
    (h : idem A + cA D (idem A) = idem B + cA D (idem B)) {P : Pl D.host.E} (hP : P ∈ A) : P ∈ B ∨ conjPl P ∈ B := by
  by_contra hn
  rw [not_or] at hn
  have k : idemAt P * idem A = idemAt P :=
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hA.isIdemAt ha).1) (fun a ha b hb hab => hA.mul_eq_zero ha hb hab) hP
  have k' : idemAt P * cA D (idem A) = 0 := by
    rw [idem, map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun j hj => hA.mul_conj hP hj
  have l : idemAt P * idem B = 0 := by
    rw [idem, Finset.mul_sum]
    refine Finset.sum_eq_zero fun j hj => by_contra fun h0 => hn.1 ?_
    rw [eq_of_mul_ne_zero (hA.isIdemAt hP) (hB.isIdemAt hj) h0]
    exact hj
  have l' : idemAt P * cA D (idem B) = 0 := by
    rw [idem, map_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun j hj => by_contra fun h0 => hn.2 ?_
    rw [eq_of_mul_ne_zero (hA.isIdemAt hP) (isIdemAt_conj (hB.isIdemAt hj)) h0, conjPl_conjPl]
    exact hj
  refine idem_ne_zero (hA.isIdemAt hP) ?_
  linear_combination idemAt P * h - k - k' + l + l'

theorem idem_image_conj {A : Finset (Pl D.host.E)} (hA : SplitSet A) : idem (A.image conjPl) = cA D (idem A) := by
  rw [idem, Finset.sum_image (fun a _ b _ (hab : conjPl a = conjPl b) => by rw [← conjPl_conjPl a, hab, conjPl_conjPl b]),
    idem, map_sum]
  exact Finset.sum_congr rfl fun P hP => idemAt_conj (hA.isIdemAt hP)

end Places

section Models

variable {D : D7} {S T : HSp D} {F : Frame S T}

theorem isThetaAt_of_model (hF : F.Good) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0) {f₀ Φ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hT : IsPlaceModel F.ψ (symplO S T) (heisO F.ψ S T) a F.lat 1 f₀ Tm)
    (hΦ : IsSBHalf a F.lat Φ) : IsThetaAt F.ψ (symplO S T) (heisO F.ψ S T) a F.lat 1 f₀ Φ (Tm Φ) :=
  ⟨⟨_, hT⟩, fun _ h₂ => GlobalTheory.PlaceVec.placeModel_unique hF.vac.1 hF.sdS hF.sdT ha hinf hT h₂ hΦ⟩

theorem step (hF : F.Good) {a b : AE D} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) (hinf : infPart D b = 0)
    {f₀ Ψ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel F.ψ (symplO S T) (heisO F.ψ S T) (a + b) F.lat 1 f₀ Tm) (hΨ : IsSBHalf b F.lat Ψ) :
    ∃ f, IsThetaAt F.ψ (symplO S T) (heisO F.ψ S T) b F.lat 1 f₀ Ψ f ∧
      IsPlaceModel F.ψ (symplO S T) (heisO F.ψ S T) a F.lat 1 f (Tm ∘ₗ tensorHalf a b Ψ) := by
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ F.lat, a • u ∈ F.lat := fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  refine ⟨_, ?_, isPlaceModel_comp_tensorHalf ha hb hab hΛ hΨ hT⟩
  rw [add_comm] at hT
  exact isThetaAt_of_model hF hb hinf (isPlaceModel_comp_restrictHalf hb ha (by rw [mul_comm, hab]) hΛ hT) hΨ

def dat (F : Frame S T) (Q : Finset (Pl D.host.E)) (ω : Reds D T.rank S.rank → ℂ) (x : WO S T) : ℂ :=
  if IsHalf (idem Q) x ∧ IsIntM (frMapO S T F.βS F.βT x) then ω (fun PP => redM PP (frMapO S T F.βS F.βT x)) else 0

theorem isSBHalf_dat (hF : F.Good) {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {ω : Reds D T.rank S.rank → ℂ}
    (hω : ∀ y y', (∀ PP ∈ Q, y PP = y' PP) → ω y = ω y') : IsSBHalf (idem Q) F.lat (dat F Q ω) := by
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart hQ.isIdemSum
  refine GlobalTheory.PlaceDatum.isSBHalf_of_red _ _ (frMapO S T F.βS F.βT) (GlobalTheory.PlaceDatum.frMapO_add _ _)
      (GlobalTheory.PlaceDatum.exists_den_frMapO hF.sdS.1.fg hF.sdT.1.fg _ _) ?_ Q ω hω
  obtain ⟨K, hK, h'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hF.sdS.1 hF.sdT.1 F.βS F.βT
  exact ⟨K, hK, fun t ht => h' t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩

theorem idem_split {Q J K : Finset (Pl D.host.E)} (hd : Disjoint J K) (hU : ∀ P, P ∈ Q ↔ P ∈ J ∨ P ∈ K) :
    idem Q = idem J + idem K := by
  rw [idem, idem, idem, ← Finset.sum_union hd]
  exact Finset.sum_congr (Finset.ext fun P => by rw [hU, Finset.mem_union]) fun _ _ => rfl

theorem idemAt_mul_idem {Q K : Finset (Pl D.host.E)} (hQ : SplitSet Q) (hK : K ⊆ Q) {P : Pl D.host.E} (hP : P ∈ Q) (hn : P ∉ K) :
    idemAt P * idem K = 0 := by
  rw [idem, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j hj => hQ.mul_eq_zero hP (hK hj) fun e => hn (e ▸ hj)

open GlobalTheory.ExportSeries.Model GlobalTheory.AdelicLatMove in

theorem tensorHalf_dat (F : Frame S T) {Q J K : Finset (Pl D.host.E)} (hQ : SplitSet Q) (hd : Disjoint J K)
    (hU : ∀ P, P ∈ Q ↔ P ∈ J ∨ P ∈ K) {ω ω' : Reds D T.rank S.rank → ℂ}
    (hω : ∀ y y', (∀ PP ∈ J, y PP = y' PP) → ω y = ω y') (hω' : ∀ y y', (∀ PP ∈ K, y PP = y' PP) → ω' y = ω' y') :
    tensorHalf (idem J) (idem K) (dat F K ω') (dat F J ω) = dat F Q fun y => ω y * ω' y := by
  have sJ : J ⊆ Q := fun P h => (hU P).2 (Or.inl h)
  have sK : K ⊆ Q := fun P h => (hU P).2 (Or.inr h)
  have hj := GlobalTheory.PlaceVec.idemSum_mul_self (hQ.mono sJ).isIdemSum
  have hk := GlobalTheory.PlaceVec.idemSum_mul_self (hQ.mono sK).isIdemSum
  funext x
  rw [tensorHalf_apply, ← idem_split hd hU]
  unfold dat
  by_cases hx : IsHalf (idem Q) x
  swap
  · rw [if_neg hx, if_neg (show ¬ (IsHalf (idem Q) x ∧ IsIntM (frMapO S T F.βS F.βT x)) from fun h => hx h.1), mul_zero]
  have hxe : idem J • x + idem K • x = x := by
    rw [← add_smul, ← idem_split hd hU]
    exact Matrix.ext fun i j => hx i j
  have i1 := isHalf_smul hj x
  have i2 := isHalf_smul hk x
  rw [if_pos hx, mul_one]
  by_cases hi : IsIntM (frMapO S T F.βS F.βT x)
  · have k1 : IsIntM (frMapO S T F.βS F.βT (idem J • x)) := by
      rw [frMapO_smul]; exact isIntM_smul hj hi
    have k2 : IsIntM (frMapO S T F.βS F.βT (idem K • x)) := by
      rw [frMapO_smul]; exact isIntM_smul hk hi
    rw [if_pos ⟨i1, k1⟩, if_pos ⟨i2, k2⟩, if_pos ⟨hx, hi⟩]
    congr 1
    · refine hω _ _ fun PP hPP => ?_
      have e : frMapO S T F.βS F.βT (idem J • x) =
          frMapO S T F.βS F.βT x - toEAf D (idem K) • frMapO S T F.βS F.βT x := by
        rw [← frMapO_smul, eq_sub_iff_add_eq, ← frMapO_add', hxe]
      rw [e, GlobalTheory.RedHalfDrop.redM_sub_smul PP hi (toEAf_mem_intAf_of_idem hk)
        (GlobalTheory.RedHalfDrop.resS_eq_zero_of_mul (hQ.isIdemAt (sJ hPP)) _
          (idemAt_mul_idem hQ sK (sJ hPP) (Finset.disjoint_left.1 hd hPP)))]
    · refine hω' _ _ fun PP hPP => ?_
      have e : frMapO S T F.βS F.βT (idem K • x) =
          frMapO S T F.βS F.βT x - toEAf D (idem J) • frMapO S T F.βS F.βT x := by
        rw [← frMapO_smul, eq_sub_iff_add_eq', ← frMapO_add', hxe]
      rw [e, GlobalTheory.RedHalfDrop.redM_sub_smul PP hi (toEAf_mem_intAf_of_idem hj)
        (GlobalTheory.RedHalfDrop.resS_eq_zero_of_mul (hQ.isIdemAt (sK hPP)) _
          (idemAt_mul_idem hQ sJ (sK hPP) (Finset.disjoint_right.1 hd hPP)))]
  · rw [if_neg (show ¬ (IsHalf (idem Q) x ∧ IsIntM (frMapO S T F.βS F.βT x)) from fun h => hi h.2)]
    by_cases k2 : IsIntM (frMapO S T F.βS F.βT (idem K • x))
    · rw [if_neg (show ¬ (IsHalf (idem J) (idem J • x) ∧
        IsIntM (frMapO S T F.βS F.βT (idem J • x))) from fun k1 => hi ?_), zero_mul]
      rw [← hxe, frMapO_add']
      exact fun i j => add_mem (k1.2 i j) (k2 i j)
    · rw [if_neg (show ¬ (IsHalf (idem K) (idem K • x) ∧
        IsIntM (frMapO S T F.βS F.βT (idem K • x))) from fun h => k2 h.2), mul_zero]

theorem vec_three_steps (hF : F.Good) {G : TypeDat D T.rank} {Q J K : Finset (Pl D.host.E)} (h : PlacesOK G.Pg Q)
    (hd : Disjoint J K) (hU : ∀ P, P ∈ Q ↔ P ∈ J ∨ P ∈ K) {ω ω' : Reds D T.rank S.rank → ℂ}
    (hω : ∀ y y', (∀ PP ∈ J, y PP = y' PP) → ω y = ω y') (hω' : ∀ y y', (∀ PP ∈ K, y PP = y' PP) → ω' y = ω' y') :
    ∃ fg hA : WO S T → ℂ, IsThetaAt F.ψ (symplO S T) (heisO F.ψ S T) (cA D (idem G.Pg)) F.lat 1 F.f₀
      (fun x => if IsHalf (cA D (idem G.Pg)) x ∧ IsIntM (frMapAdj S T F.βS F.βT x) then
        omegaG G.levT G.muC (fun PP => redM PP (frMapAdj S T F.βS F.βT x)) else 0) fg ∧
      IsThetaAt F.ψ (symplO S T) (heisO F.ψ S T) (idem K) F.lat 1 fg (dat F K ω') hA ∧
      IsThetaAt F.ψ (symplO S T) (heisO F.ψ S T) (idem J) F.lat 1 hA (dat F J ω) (F.vec G Q fun y => ω y * ω' y) := by
  obtain ⟨hg, hq, ho, -, -⟩ := idem_orth h
  have hg' : cA D (idem G.Pg) * cA D (idem G.Pg) = cA D (idem G.Pg) := by rw [← RingHom.map_mul, hg]
  obtain ⟨P, s1, s2, hP⟩ := h.split
  have hQ := hP.mono s2
  have sJ : J ⊆ Q := fun P h => (hU P).2 (Or.inl h)
  have sK : K ⊆ Q := fun P h => (hU P).2 (Or.inr h)
  have hj := GlobalTheory.PlaceVec.idemSum_mul_self (hQ.mono sJ).isIdemSum
  have hk := GlobalTheory.PlaceVec.idemSum_mul_self (hQ.mono sK).isIdemSum
  have hjk : idem J * idem K = 0 := by
    rw [show idem J = ∑ PP ∈ J, idemAt PP from rfl, Finset.sum_mul]
    exact Finset.sum_eq_zero fun j hj => idemAt_mul_idem hQ sK (sJ hj) (Finset.disjoint_left.1 hd hj)
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart (hP.mono s1).isIdemSum)
  have hSB := GlobalTheory.PlaceVec.isSBHalf_of_red hF.sdS.1 hF.sdT.1 hinf (frMapAdj S T F.βS F.βT)
    (GlobalTheory.PlaceVec.frMapAdj_add S T _ _) (GlobalTheory.PlaceVec.frMapAdj_up S T _ _) (GlobalTheory.PlaceVec.frMapAdj_down S T _ _) G.Pg
    (omegaG G.levT G.muC) (GlobalTheory.PlaceDatum.omegaG_congr G.levT G.muC)
  have hM := Frame.isPlaceModel_placeMap hF h
  have hM' : IsPlaceModel F.ψ (symplO S T) (heisO F.ψ S T) (idem Q + cA D (idem G.Pg)) F.lat 1 F.f₀
      (F.placeMap (halfIdem G.Pg Q)) := by
    rw [show idem Q + cA D (idem G.Pg) = halfIdem G.Pg Q from add_comm _ _]
    exact hM
  obtain ⟨fg, t1, m1⟩ := step hF hq hg' ho hinf hM' hSB
  have m1' := m1
  rw [show ∀ (f : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsPlaceModel F.ψ (symplO S T) (heisO F.ψ S T) (idem Q) F.lat 1 f Tm =
      IsPlaceModel F.ψ (symplO S T) (heisO F.ψ S T) (idem J + idem K) F.lat 1 f Tm from
        fun f Tm => by rw [idem_split hd hU]] at m1'
  obtain ⟨hA, t2, m2⟩ := step hF hj hk hjk (GlobalTheory.PlaceVec.idemSum_infPart (hQ.mono sK).isIdemSum) m1'
    (isSBHalf_dat hF (hQ.mono sK) hω')
  have t3 := isThetaAt_of_model hF hj (GlobalTheory.PlaceVec.idemSum_infPart (hQ.mono sJ).isIdemSum) m2
    (isSBHalf_dat hF (hQ.mono sJ) hω)
  refine ⟨fg, hA, t1, t2, ?_⟩
  rw [LinearMap.comp_apply, tensorHalf_dat F hQ hd hU hω hω', LinearMap.comp_apply] at t3
  rw [Frame.vec, datumFn_eq_tensor hF h (ω := fun y => ω y * ω' y) fun y y' hy => by
    rw [hω y y' fun PP hPP => hy PP (sJ hPP), hω' y y' fun PP hPP => hy PP (sK hPP)]]
  exact t3

end Models

section Real

open GlobalTheory.ConjTwist

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem xiR_eq_of_mem {B : Base (Vc D i) (Wc D i)} {ψ : Twist D Circle} {t t₀ : T0} (ht : R.xi t = B.de.chi * ψ.chi)
    (hL : R.toLevCh.Is t₀) (hB : B.Good) (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {PP : Pl D.host.E} (hPP : PP ∈ R.Q t)
    (hm : PP ∈ B.de.Q ∪ ψ.Q) : R.xiR t PP = B.de.locC PP * ψ.locC PP := by
  obtain ⟨P, -, h2, hP⟩ := hQ.1.split
  have s1 : B.de.Q ⊆ P := fun a ha => h2 (by simp [ha])
  have s2 : ψ.Q ⊆ P := fun a ha => h2 (by simp [ha])
  have hp : PP ∈ P := h2 hm
  refine MonoidHom.ext fun u => Units.ext ?_
  obtain ⟨x, hx⟩ := exists_isLocUnit (hP.isIdemAt hp) u
  obtain ⟨k1, k2⟩ := hx.res
  have key : ∀ {ν : Twist D Circle}, ν.Good → ν.Q ⊆ P → ((ν.chi x : Circle) : ℂ) = ((ν.locC PP u : ℂˣ) : ℂ) := by
    intro ν hν hs
    unfold Twist.locC
    split_ifs with k
    · rw [hx.eq (hν.res PP k)]
      rfl
    · rw [hx.eq_one hν.unram hP hs hp k]
      rfl
  rw [← eq_res_of_chrEq (hL.xi t) (hP.isIdemAt hp) (hL.xi_tame t PP) (hL.xiR t PP hPP) x hx.off k1 u k2, ht,
    MonoidHom.mul_apply, MonoidHom.mul_apply, Circle.coe_mul, Units.val_mul, key hB.de s1, key hψ s2]

theorem locFn_eq_prod {S T : HSp D} {B : Base S T} {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) (y : Reds D T.rank S.rank) :
    B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y = ∏ PP ∈ B.de.Q ∪ ψ.Q, flat (B.de.locC PP * ψ.locC PP) (y PP) := by
  rw [Base.locFn, Finset.prod_coe_sort ψ.Q fun PP => flat (ψ.resC PP) (y PP), Finset.prod_union hQ.2]
  congr 1
  · refine Finset.prod_congr rfl fun PP hP => ?_
    rw [Twist.locC, Twist.locC, if_pos hP, if_neg (Finset.disjoint_left.1 hQ.2 hP), mul_one]
  · refine Finset.prod_congr rfl fun PP hP => ?_
    rw [Twist.locC, Twist.locC, if_pos hP, if_neg (Finset.disjoint_right.1 hQ.2 hP), one_mul]

end Real

theorem vecFlat_three_steps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (eg ea et : AE D) (fg hA : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum ea (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ IsIdemSum et (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ GlobalTheory.BaseCmp.IsTypeVec R i eg fg ∧ ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) ea) hA ∧ ThAt R i (cA D et) hA (GlobalTheory.BaseCmp.flatDat R i ((flipPart (R := R) t (B.de.Q ∪ ψ.Q)).image conjPl) (fun PP => B.de.locC PP * ψ.locC PP) (cA D et)) ((princ B).vecFlat ψ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i t _ B ψ hB h hψ hQ hxi hid
  have hs : SplitSet (R.Q t) := (GlobalTheory.ConjTwist.Test.splitSet_Pg hC i t).mono (by convert Finset.subset_union_right)
  obtain ⟨P, s1, s2, hP⟩ := hQ.1.split
  have hQ' : SplitSet (B.de.Q ∪ ψ.Q) := hP.mono s2
  have mk : ∀ PP, PP ∈ keepPart (R := R) t (B.de.Q ∪ ψ.Q) ↔ PP ∈ R.Q t ∧ PP ∈ B.de.Q ∪ ψ.Q := fun PP => Finset.mem_filter
  have mf : ∀ PP, PP ∈ flipPart (R := R) t (B.de.Q ∪ ψ.Q) ↔ PP ∈ R.Q t ∧ PP ∉ B.de.Q ∪ ψ.Q := fun PP => Finset.mem_filter
  generalize keepPart (R := R) t (B.de.Q ∪ ψ.Q) = K at mk ⊢
  generalize flipPart (R := R) t (B.de.Q ∪ ψ.Q) = L at mf ⊢
  have hK : SplitSet K := hs.mono fun PP hPP => ((mk PP).1 hPP).1
  have hL : SplitSet L := hs.mono fun PP hPP => ((mf PP).1 hPP).1
  have hd : Disjoint (L.image conjPl) K := Finset.disjoint_left.2 fun PP h1 h2 => by
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h1
    exact conj_notMem hs ((mf _).1 hP').1 ((mk _).1 h2).1
  have hU : ∀ PP, PP ∈ B.de.Q ∪ ψ.Q ↔ PP ∈ L.image conjPl ∨ PP ∈ K := fun PP => by
    constructor
    · intro hPP
      rcases mem_or_conj_mem hQ' hs hid.symm hPP with k | k
      · exact Or.inr ((mk _).2 ⟨k, hPP⟩)
      · exact Or.inl (Finset.mem_image.2 ⟨_, (mf _).2 ⟨k, conj_notMem hQ' hPP⟩, conjPl_conjPl PP⟩)
    · rintro (k | k)
      · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 k
        exact (mem_or_conj_mem hs hQ' hid ((mf _).1 hP').1).resolve_left ((mf _).1 hP').2
      · exact ((mk _).1 k).2
  have cg : ∀ (Q : Finset (Pl D.host.E)) (ξ : ResChars D ℂˣ) (y y' : Reds D (Wc D i).rank (Vc D i).rank),
      (∀ PP ∈ Q, y PP = y' PP) → GlobalTheory.ConjTwist.omegaFlat Q (Wc D i).rank ξ y = GlobalTheory.ConjTwist.omegaFlat Q (Wc D i).rank ξ y' :=
    fun Q ξ y y' hy => by
      rw [omegaFlat_eq_prod, omegaFlat_eq_prod]
      exact Finset.prod_congr rfl fun PP hPP => by rw [hy PP hPP]
  obtain ⟨fg, hA, t1, t2, t3⟩ := vec_three_steps (G := princG B.G) hB.frame hQ.1 hd hU
    (cg (L.image conjPl) fun PP => B.de.locC PP * ψ.locC PP) (cg K (R.xiR t))
  have e : (fun y : Reds D (Wc D i).rank (Vc D i).rank =>
      GlobalTheory.ConjTwist.omegaFlat (L.image conjPl) (Wc D i).rank (fun PP => B.de.locC PP * ψ.locC PP) y *
        GlobalTheory.ConjTwist.omegaFlat K (Wc D i).rank (R.xiR t) y) = B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) := by
    funext y
    rw [locFn_eq_prod hQ, omegaFlat_eq_prod, omegaFlat_eq_prod,
      show B.de.Q ∪ ψ.Q = L.image conjPl ∪ K from Finset.ext fun PP => by rw [hU, Finset.mem_union], Finset.prod_union hd]
    congr 1
    exact Finset.prod_congr rfl fun PP hPP => by
      rw [xiR_eq_of_mem hxi hC.lev hB hψ hQ ((mk _).1 hPP).1 ((mk _).1 hPP).2]
  rw [e] at t3
  simp only [omegaG_princ] at t1
  unfold dat at t2 t3
  rw [idem_image_conj hL] at t3
  refine ⟨idem R.Pg, idem K, idem L, fg, hA, h.Pg ▸ (hP.mono s1).isIdemSum, hK.isIdemSum, hL.isIdemSum, ?_, ?_, ?_⟩
  · unfold GlobalTheory.BaseCmp.IsTypeVec GlobalTheory.BaseCmp.lattice₂
    rw [← h.ψ, ← h.ΛS, ← h.ΛT, ← h.βS, ← h.βT, ← h.vac, ← h.Pg]
    exact t1
  · unfold ThAt GlobalTheory.BaseCmp.flatDat
    rw [← h.ψ, ← h.ΛS, ← h.ΛT, ← h.βS, ← h.βT]
    exact t2
  · unfold ThAt GlobalTheory.BaseCmp.flatDat
    rw [← h.ψ, ← h.ΛS, ← h.ΛT, ← h.βS, ← h.βT]
    exact t3

end GlobalTheory.FlatThreeSteps

end
