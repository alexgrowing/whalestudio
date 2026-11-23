import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.LiftRowCohT

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Saturated
open PI.DCRelEquiv.UnitaryGroupMassFormula (mem_orth_iff isom_app gmap_mul')
open LiftRowCohT

namespace LiftRowCohF

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem ff_herm (x y : S.V) : starRingEnd E (S.hT x y) = S.hT y x := S.herm.eq x y

theorem ff_swap {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← ff_herm x y, h, map_zero]

theorem ff_iso_span {p : Fin r → S.V} (hp : ∀ a b, S.hT (p a) (p b) = 0) {x y : S.V}
    (hx : x ∈ Submodule.span E (Set.range p)) (hy : y ∈ Submodule.span E (Set.range p)) : S.hT x y = 0 := by
  have h1 : ∀ a, ∀ z ∈ Submodule.span E (Set.range p), S.hT (p a) z = 0 := by
    intro a z hz
    have hle : Submodule.span E (Set.range p) ≤ LinearMap.ker (S.hT (p a)) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact LinearMap.mem_ker.2 (hp a b)
    exact LinearMap.mem_ker.1 (hle hz)
  have hle : Submodule.span E (Set.range p) ≤ LinearMap.ker (S.hT.flip y) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_ker.2 (by simpa using h1 a y hy)
  simpa using LinearMap.mem_ker.1 (hle hx)

theorem ff_repr {e f : Fin r → S.V} (hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range e)) : x = ∑ a, S.hT (f a) x • e a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp [map_sum, hfe]

def ffP (p q : Fin r → S.V) (c d : Fin r → E) : S.V := ∑ a, c a • p a + ∑ a, d a • q a

theorem ffP_mem {p q : Fin r → S.V} {H : Submodule E S.V} (hp : ∀ a, p a ∈ H) (hq : ∀ a, q a ∈ H)
    (c d : Fin r → E) : ffP p q c d ∈ H := by
  unfold ffP
  exact H.add_mem (H.sum_mem fun a _ => H.smul_mem _ (hp a)) (H.sum_mem fun a _ => H.smul_mem _ (hq a))

theorem ff_hyp {p q : Fin r → S.V} (hp : ∀ a b, S.hT (p a) (p b) = 0) (hq : ∀ a b, S.hT (q a) (q b) = 0)
    (hpq : ∀ a b, S.hT (p a) (q b) = if a = b then 1 else 0) (c d c' d' : Fin r → E) :
    S.hT (ffP p q c d) (ffP p q c' d') =
      ∑ a, (starRingEnd E (c a) * d' a + starRingEnd E (d a) * c' a) := by
  have hqp : ∀ a b, S.hT (q a) (p b) = if a = b then 1 else 0 := by
    intro a b
    rw [← ff_herm, hpq]
    by_cases h : a = b <;> simp [h, Ne.symm]
  simp [ffP, map_sum, LinearMap.sum_apply, hp, hq, hpq, hqp, mul_ite, Finset.sum_add_distrib]

theorem ff_split_eval {H : Submodule E S.V} {w w' P P' : S.V} (hw : w ∈ orth S H) (hw' : w' ∈ orth S H)
    (hP : P ∈ H) (hP' : P' ∈ H) : S.hT (w + P) (w' + P') = S.hT w w' + S.hT P P' := by
  have h1 : S.hT w P' = 0 := ff_swap (mem_orth_iff.1 hw P' hP')
  have h2 : S.hT P w' = 0 := mem_orth_iff.1 hw' P hP
  simp only [map_add, LinearMap.add_apply, h1, h2]
  ring

def ffC (f : Fin r → S.V) (v : S.V) : Fin r → E := fun a => S.hT (f a) v

def ffMu (e f x g : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id + ∑ a, (S.hT (f a)).smulRight (x a - e a) + ∑ a, (S.hT (e a)).smulRight (g a - f a)

theorem ffMu_apply (e f x g : Fin r → S.V) (v : S.V) :
    ffMu e f x g v = v + ∑ a, S.hT (f a) v • (x a - e a) + ∑ a, S.hT (e a) v • (g a - f a) := by
  simp [ffMu, LinearMap.sum_apply, LinearMap.smulRight_apply]

theorem ffMu_eq (e f x g : Fin r → S.V) (v : S.V) :
    ffMu e f x g v = (v - ffP e f (ffC f v) (ffC e v)) + ffP x g (ffC f v) (ffC e v) := by
  rw [ffMu_apply]
  simp only [ffP, ffC, smul_sub, Finset.sum_sub_distrib]
  abel

variable {e f : Fin r → S.V}

abbrev ffH (e f : Fin r → S.V) : Submodule E S.V := Submodule.span E (Set.range e ∪ Set.range f)

theorem ff_orth_part (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0) (v : S.V) :
    v - ffP e f (ffC f v) (ffC e v) ∈ orth S (ffH e f) := by
  rw [mem_orth_iff]
  intro y hy
  have key : ffH e f ≤ LinearMap.ker (S.hT.flip (v - ffP e f (ffC f v) (ffC e v))) := by
    refine Submodule.span_le.2 (Set.union_subset ?_ ?_) <;> rintro _ ⟨b, rfl⟩ <;>
      simp [LinearMap.mem_ker, ffP, ffC, map_sum, LinearMap.sum_apply, hee, hef, hfe, hff, mul_ite]
  simpa using LinearMap.mem_ker.1 (key hy)

theorem ffMu_isom {x g : Fin r → S.V} (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0)
    (hxx : ∀ a b, S.hT (x a) (x b) = 0) (hgg : ∀ a b, S.hT (g a) (g b) = 0)
    (hxg : ∀ a b, S.hT (x a) (g b) = if a = b then 1 else 0) (hxH : ∀ a, x a ∈ ffH e f)
    (hgH : ∀ a, g a ∈ ffH e f) (v v' : S.V) :
    S.hT (ffMu e f x g v) (ffMu e f x g v') = S.hT v v' := by
  have heH : ∀ a, e a ∈ ffH e f := fun a => Submodule.subset_span (Or.inl ⟨a, rfl⟩)
  have hfH : ∀ a, f a ∈ ffH e f := fun a => Submodule.subset_span (Or.inr ⟨a, rfl⟩)
  have ho := ff_orth_part hee hff hef hfe v
  have ho' := ff_orth_part hee hff hef hfe v'
  have key : S.hT v v' = S.hT (v - ffP e f (ffC f v) (ffC e v)) (v' - ffP e f (ffC f v') (ffC e v')) +
      ∑ a, (starRingEnd E (ffC f v a) * ffC e v' a + starRingEnd E (ffC e v a) * ffC f v' a) := by
    conv_lhs => rw [← sub_add_cancel v (ffP e f (ffC f v) (ffC e v)),
      ← sub_add_cancel v' (ffP e f (ffC f v') (ffC e v'))]
    rw [ff_split_eval ho ho' (ffP_mem heH hfH _ _) (ffP_mem heH hfH _ _), ff_hyp hee hff hef]
  rw [ffMu_eq e f x g v, ffMu_eq e f x g v',
    ff_split_eval ho ho' (ffP_mem hxH hgH _ _) (ffP_mem hxH hgH _ _), ff_hyp hxx hgg hxg, key]

theorem ff_inj_of_isom {m : S.V →ₗ[E] S.V} (h : ∀ v v', S.hT (m v) (m v') = S.hT v v') :
    Function.Injective m := by
  refine (injective_iff_map_eq_zero m).2 fun v hv => S.nondeg.1 v fun y => ?_
  rw [← h v y, hv, map_zero, LinearMap.zero_apply]

theorem ffMu_e {x g : Fin r → S.V} (hee : ∀ a b, S.hT (e a) (e b) = 0)
    (hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0) (b : Fin r) : ffMu e f x g (e b) = x b := by
  rw [ffMu_apply]
  simp [hfe, hee]

theorem ffMu_fix {x g : Fin r → S.V} {v : S.V} (h1 : ∀ a, S.hT (f a) v = 0) (h2 : ∀ a, S.hT (e a) v = 0) :
    ffMu e f x g v = v := by
  rw [ffMu_apply]
  simp [h1, h2]

theorem ffMu_sub_e {x g : Fin r → S.V} {v : S.V} (h2 : ∀ a, S.hT (e a) v = 0) :
    ffMu e f x g v - v = ∑ a, S.hT (f a) v • (x a - e a) := by
  rw [ffMu_apply]
  simp [h2]

theorem ffMu_sub_f {x g : Fin r → S.V} {v : S.V} (h1 : ∀ a, S.hT (f a) v = 0) :
    ffMu e f x g v - v = ∑ a, S.hT (e a) v • (g a - f a) := by
  rw [ffMu_apply]
  simp [h1]

theorem ff_dual_pair (x : Fin r → S.V) (U : Matrix (Fin r) (Fin r) E)
    (hUT : U * Matrix.of (fun a b => S.hT (f a) (x b)) = 1) (a b : Fin r) :
    S.hT (x a) (∑ c, starRingEnd E (U b c) • f c) = if a = b then 1 else 0 := by
  have h := congrFun (congrFun hUT b) a
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h
  have hc : S.hT (x a) (∑ c, starRingEnd E (U b c) • f c) =
      starRingEnd E (∑ c, U b c * S.hT (f c) (x a)) := by
    simp [map_sum, ff_herm]
  rw [hc, h]
  by_cases hab : a = b <;> simp [hab, Ne.symm]

theorem ff_det {x : Fin r → S.V} (hx : LinearIndependent E x) (hxe : ∀ b, x b = ∑ a, S.hT (f a) (x b) • e a) :
    (Matrix.of (fun a b => S.hT (f a) (x b))).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hw0
  have hsum : ∑ b, w b • x b = 0 := by
    calc ∑ b, w b • x b = ∑ b, w b • ∑ a, S.hT (f a) (x b) • e a :=
          Finset.sum_congr rfl fun b _ => by rw [← hxe b]
      _ = ∑ a, (∑ b, S.hT (f a) (x b) * w b) • e a := by
          simp only [Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun b _ => by rw [mul_comm]
      _ = 0 := by
          refine Finset.sum_eq_zero fun a _ => ?_
          have h := congrFun hw a
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
          rw [h, zero_smul]
  exact funext (Fintype.linearIndependent_iff.1 hx w hsum)

theorem ff_gmap_latSpan (ν : S.V ≃ₗ[E] S.V) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (v : Fin r → S.V) : Formalism.HermitianLatticesTheory.gmap ν (latSpan aa v) = latSpan aa (fun a => ν (v a)) := by
  unfold Formalism.HermitianLatticesTheory.gmap Formalism.L2.SG.Saturated.latSpan
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, ⟨a, c, hc, rfl⟩, rfl⟩
    exact ⟨a, c, hc, by simp⟩
  · rintro ⟨a, c, hc, rfl⟩
    exact ⟨c • v a, ⟨a, c, hc, rfl⟩, by simp⟩

theorem ff_gmap_inf (ν : S.V ≃ₗ[E] S.V) (A : Submodule (𝓞 E) S.V) (U : Submodule E S.V) :
    Formalism.HermitianLatticesTheory.gmap ν (A ⊓ toO S U) = Formalism.HermitianLatticesTheory.gmap ν A ⊓ toO S (U.map (ν : S.V →ₗ[E] S.V)) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_inf _ (by simpa using ν.injective)]
  congr 1

theorem ff_mem_dual {Λ : Submodule (𝓞 E) S.V} {x : S.V} :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ ↔ ∀ y ∈ Λ, S.hT y x ∈ (1 : Submodule (𝓞 E) E) := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp [Submodule.mem_iInf]

theorem ff_lat_le {Λ' Me L Mf : Submodule (𝓞 E) S.V} {Yf : Submodule E S.V}
    (hΛ : Λ' = Me ⊔ L ⊔ Mf) (hU : Formalism.HermitianLatticesTheory.dual S.hT Λ' = Λ')
    (hMf : ∀ v ∈ Mf, v ∈ Yf) (hY : ∀ a ∈ Yf, ∀ b ∈ Yf, S.hT a b = 0) (hLY : ∀ l ∈ L, ∀ v ∈ Yf, S.hT l v = 0)
    {ν : S.V ≃ₗ[E] S.V} (hν : ν ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h1 : ∀ x ∈ Me, ν x ∈ Me)
    (h2 : ∀ x ∈ Me, ν.symm x ∈ Me) (h3 : ∀ x ∈ L, ν x = x) (h4 : ∀ x ∈ Yf, ν.symm x ∈ Yf) :
    Formalism.HermitianLatticesTheory.gmap ν Λ' ≤ Λ' := by
  subst hΛ
  have hmem : ∀ z, z ∈ Me ⊔ L ⊔ Mf ↔ ∀ y ∈ Me ⊔ L ⊔ Mf, S.hT y z ∈ (1 : Submodule (𝓞 E) E) := by
    intro z
    have h := ff_mem_dual (Λ := Me ⊔ L ⊔ Mf) (x := z)
    rwa [hU] at h
  have hMe : Me ≤ Me ⊔ L ⊔ Mf := le_sup_left.trans le_sup_left
  have hL : L ≤ Me ⊔ L ⊔ Mf := le_sup_right.trans le_sup_left
  have hMf' : Mf ≤ Me ⊔ L ⊔ Mf := le_sup_right
  have hsymm : ∀ y w, S.hT y (ν w) = S.hT (ν.symm y) w := by
    intro y w
    rw [← isom_app hν (ν.symm y) w, LinearEquiv.apply_symm_apply]
  have hn : ∀ n ∈ Mf, ν n ∈ Me ⊔ L ⊔ Mf := by
    intro n hn
    have hnΛ := hMf' hn
    refine (hmem _).2 fun y hy => ?_
    obtain ⟨y12, hy12, y3, hy3, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy12
    simp only [map_add, LinearMap.add_apply]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · rw [hsymm]
      exact (hmem n).1 hnΛ _ (hMe (h2 y1 hy1))
    · rw [← h3 y2 hy2, isom_app hν]
      exact (hmem n).1 hnΛ _ (hL hy2)
    · rw [hsymm, hY _ (h4 _ (hMf y3 hy3)) n (hMf n hn)]
      exact Submodule.zero_mem _
  unfold Formalism.HermitianLatticesTheory.gmap
  intro w hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z12, hz12, n, hn', rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨m, hm, l, hl, rfl⟩ := Submodule.mem_sup.1 hz12
  show ν (m + l + n) ∈ Me ⊔ L ⊔ Mf
  rw [map_add, map_add, h3 l hl]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hMe (h1 m hm)) (hL hl)) (hn n hn')

end Gen

end LiftRowCohF

open LiftRowCohF

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem frameCorrection_holds : FrameFixNeed X Y u u' := by
  intro s y β _ _ hP _ _
  have hγi : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  have hβi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hP.1.1
  have hβΛ : Formalism.HermitianLatticesTheory.gmap β s.lam = s.lam := hP.1.2
  have hδi : β * s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem hβi hγi
  have hδΛ : Formalism.HermitianLatticesTheory.gmap (β * s.lin) s.lam' = s.lam := by rw [gmap_mul', hγΛ, hβΛ]
  have hRL' : IsRowLat D (X.Fu u') s.lam' := (Y.rowsOK u').1 s.lam' s.mem'
  obtain ⟨f, L, hff, hef, hL, hzL, hΛ'⟩ := Y.split u' s.lam' s.mem'
  set e := (X.Fu u').e with he_def
  have hee : ∀ a b, (VS D).hT (e a) (e b) = 0 := (X.Fu u').e_iso
  have hfe : ∀ a b, (VS D).hT (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← ff_herm, hef]
    rcases eq_or_ne a b with rfl | h
    · simp
    · simp [h, Ne.symm h]

  have hA : Xsp (lf D (X.Fu u')) = Submodule.span D.host.E (Set.range e) := rfl
  have hX2 : Xsp y.1 = (Xsp (lf D (X.Fu u'))).map ((β * s.lin : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
      (VS D).V →ₗ[D.host.E] (VS D).V) := by
    rw [liftT_xsp_eq, ← hP.2.1 D.R.rS, ← liftT_xsp_eq]
    show (Xsp (mapLF s.lin (lf D (X.Fu u')))).map _ = _
    rw [liftT_xsp_mapLF _ hγi, ← liftT_map_mul]

  set δ : (VS D).V ≃ₗ[D.host.E] (VS D).V := β * s.lin with hδ
  set x : Fin D.R.rS → (VS D).V := fun b => δ.symm (y.1.fl.e b) with hx_def
  have hxδ : ∀ b, δ (x b) = y.1.fl.e b := fun b => δ.apply_symm_apply _
  have hxA : ∀ b, x b ∈ Submodule.span D.host.E (Set.range e) := by
    intro b
    have hm : y.1.fl.e b ∈ Xsp y.1 := Submodule.subset_span ⟨b, rfl⟩
    rw [hX2] at hm
    obtain ⟨w, hw, hwe⟩ := hm
    have hxw : x b = w := by
      simp only [hx_def]
      rw [← hwe]
      simp
    rw [hxw]
    exact hw
  have hxi : LinearIndependent D.host.E x :=
    y.1.fl.e_indep.map' (δ.symm : (VS D).V →ₗ[D.host.E] (VS D).V) (LinearEquiv.ker _)
  have hxe : ∀ b, x b = ∑ a, (VS D).hT (f a) (x b) • e a := fun b => ff_repr hfe (hxA b)
  have hdet := ff_det hxi hxe
  set T := Matrix.of (fun a b => (VS D).hT (f a) (x b)) with hT
  have hUT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.2 hdet)
  set g : Fin D.R.rS → (VS D).V := fun b => ∑ c, starRingEnd D.host.E (T⁻¹ b c) • f c with hg_def
  have hxx : ∀ a b, (VS D).hT (x a) (x b) = 0 := by
    intro a b
    rw [← isom_app hδi (x a) (x b), hxδ, hxδ]
    exact y.1.fl.e_iso a b
  have hgg : ∀ a b, (VS D).hT (g a) (g b) = 0 := by
    intro a b
    simp [hg_def, map_sum, hff]
  have hxg : ∀ a b, (VS D).hT (x a) (g b) = if a = b then 1 else 0 := ff_dual_pair x T⁻¹ hUT
  have hxH : ∀ a, x a ∈ ffH e f := fun a => Submodule.span_mono Set.subset_union_left (hxA a)
  have hgH : ∀ a, g a ∈ ffH e f := fun a =>
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨c, rfl⟩))

  have hiso := ffMu_isom hee hff hef hfe hxx hgg hxg hxH hgH
  set μ := LinearEquiv.ofInjectiveEndo (ffMu e f x g) (ff_inj_of_isom hiso) with hμ_def
  have hμ : ∀ v, μ v = ffMu e f x g v := fun v => rfl
  have hμi : μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun a b => by rw [hμ, hμ]; exact hiso a b
  have hμe : ∀ b, μ (e b) = x b := fun b => by rw [hμ]; exact ffMu_e hee hfe b
  have hμL : ∀ v ∈ L, μ v = v := fun v hv => by
    rw [hμ]; exact ffMu_fix (fun a => (hL v hv a).2) (fun a => (hL v hv a).1)
  have hAiso : ∀ v ∈ Submodule.span D.host.E (Set.range e), ∀ w ∈ Submodule.span D.host.E (Set.range e),
      (VS D).hT v w = 0 := fun v hv w hw => ff_iso_span hee hv hw
  have hμo : ∀ v ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), μ v - v ∈ Xsp (lf D (X.Fu u')) := by
    intro v hv
    have h2 : ∀ a, (VS D).hT (e a) v = 0 := fun a => mem_orth_iff.1 hv (e a) (Submodule.subset_span ⟨a, rfl⟩)
    rw [hμ, ffMu_sub_e h2, hA]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
      (Submodule.sub_mem _ (hxA a) (Submodule.subset_span ⟨a, rfl⟩))
  have hμX : ∀ v ∈ Xsp (lf D (X.Fu u')), μ v ∈ Xsp (lf D (X.Fu u')) := by
    intro v hv
    have ho : v ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) := mem_orth_iff.2 fun w hw => hAiso w hw v hv
    have := Submodule.add_mem _ (hμo v ho) hv
    rwa [sub_add_cancel] at this

  set Yf := Submodule.span D.host.E (Set.range f) with hYf
  have hYiso : ∀ a ∈ Yf, ∀ b ∈ Yf, (VS D).hT a b = 0 := fun a ha b hb => ff_iso_span hff ha hb
  have hμY : ∀ v ∈ Yf, μ v ∈ Yf := by
    intro v hv
    have h1 : ∀ a, (VS D).hT (f a) v = 0 := fun a => hYiso _ (Submodule.subset_span ⟨a, rfl⟩) _ hv
    have hd : μ v - v ∈ Yf := by
      rw [hμ, ffMu_sub_f h1]
      refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.subset_span ⟨a, rfl⟩))
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    have := Submodule.add_mem _ hd hv
    rwa [sub_add_cancel] at this
  have hYmap : Yf.map (μ : (VS D).V →ₗ[D.host.E] (VS D).V) = Yf := liftT_map_eq hμY
  have hμYs : ∀ v ∈ Yf, μ.symm v ∈ Yf := by
    intro v hv
    rw [← hYmap] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa using hw

  have hMeXS : XLam s.lam' (lf D (X.Fu u')) = latSpan (aaS D) e := hRL'.2.2
  have hy' : XLam s.lam y.1 = latSpan (aaS D) y.1.fl.e := y.2.2.2.2
  have e1 : Formalism.HermitianLatticesTheory.gmap δ (latSpan (aaS D) x) = Formalism.HermitianLatticesTheory.gmap δ (latSpan (aaS D) e) := by
    rw [ff_gmap_latSpan, show (fun b => δ (x b)) = y.1.fl.e from funext hxδ, ← hy', ← hMeXS]
    unfold XLam
    rw [ff_gmap_inf, hδΛ, hX2]
  have e2 : latSpan (aaS D) x = latSpan (aaS D) e :=
    Submodule.map_injective_of_injective (f := ((δ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars
      (𝓞 D.host.E))) δ.injective e1
  have hμMe : Formalism.HermitianLatticesTheory.gmap μ (latSpan (aaS D) e) = latSpan (aaS D) e := by
    rw [ff_gmap_latSpan, show (fun b => μ (e b)) = x from funext hμe, e2]
  have h1 : ∀ v ∈ latSpan (aaS D) e, μ v ∈ latSpan (aaS D) e := fun v hv => liftT_maps hμMe hv
  have h2 : ∀ v ∈ latSpan (aaS D) e, μ.symm v ∈ latSpan (aaS D) e := by
    intro v hv
    rw [← hμMe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa using hw

  have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT s.lam' = s.lam' := hRL'.2.1.2.1
  have hMf : ∀ v ∈ latSpan (fun a => (aaS D a)⁻¹) f, v ∈ Yf := by
    intro v hv
    have hle : latSpan (fun a => (aaS D a)⁻¹) f ≤ Yf.restrictScalars (𝓞 D.host.E) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, t, -, rfl⟩
      exact Yf.smul_mem t (Submodule.subset_span ⟨a, rfl⟩)
    exact hle hv
  have hLY : ∀ l ∈ L, ∀ v ∈ Yf, (VS D).hT l v = 0 := by
    intro l hl v hv
    have hle : Yf ≤ LinearMap.ker ((VS D).hT l) :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact LinearMap.mem_ker.2 (ff_swap (hL l hl a).2))
    exact LinearMap.mem_ker.1 (hle hv)
  have hle1 : Formalism.HermitianLatticesTheory.gmap μ s.lam' ≤ s.lam' :=
    ff_lat_le hΛ' hU hMf hYiso hLY hμi h1 h2 hμL hμYs
  have hμsi : μ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun a b => by
    rw [← isom_app hμi (μ.symm a) (μ.symm b)]
    simp
  have hle2 : Formalism.HermitianLatticesTheory.gmap μ.symm s.lam' ≤ s.lam' :=
    ff_lat_le hΛ' hU hMf hYiso hLY hμsi h2 (by simpa using h1)
      (fun v hv => (μ.symm_apply_eq).2 (hμL v hv).symm) (by simpa using hμY)
  have hμΛ : Formalism.HermitianLatticesTheory.gmap μ s.lam' = s.lam' :=
    le_antisymm hle1 fun v hv => ⟨μ.symm v, hle2 ⟨v, hv, rfl⟩, μ.apply_symm_apply v⟩

  have hδ'i : δ * μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem hδi hμi
  have hzs : s.frame.fl.z = s.lin (X.Fu u').z := by
    simp [GTerm.frame, mapLF, dif_pos hγi, Formalism.L2.SG.TermOp.mapFlag]
  have hz : (δ * μ) (X.Fu u').z = y.1.fl.z := by
    show β (s.lin (μ (X.Fu u').z)) = _
    rw [hμL _ hzL, ← hzs]
    exact hP.2.2.1
  have hyz : y.1.zt = y.1.fl.z := y.2.1.2
  refine ⟨μ, hμi, hμΛ, hμX, hμo, 1, one_mem_NLam _ _, 1, one_mem_NLam _ _, ?_, ?_⟩
  · intro a
    rw [mapLF, dif_pos hδ'i]
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simp only [frame, FlagG.fvec, Fin.snoc_last]
      exact hz
    · simp only [frame, FlagG.fvec, Fin.snoc_castSucc]
      show (δ * μ) (e b) = y.1.fl.e b
      rw [show (δ * μ) (e b) = δ (μ (e b)) from rfl, hμe b]
      exact hxδ b
  · rw [mapLF, dif_pos hδ'i]
    show (δ * μ) (X.Fu u').z = y.1.zt
    rw [hyz]
    exact hz

end Formalism.L2.SG.Pf.RowForm
