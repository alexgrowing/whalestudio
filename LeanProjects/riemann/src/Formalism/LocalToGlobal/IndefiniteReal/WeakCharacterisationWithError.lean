import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Err

open Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat3

def withErr (R : RealDat3 D A3 Ks) (e : type_of% R.err0) : RealDat3 D A3 Ks :=
  { R with toRealDat := { R.toRealDat with err0 := e } }

variable {R : RealDat3 D A3 Ks} {F : Face3 D A3}

def _root_.Formalism.IndefR.Links.reErr {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Am : DefAmb Bs}
    (X : CxData Am) (e : type_of% X.err0) : CxData Am := { X with err0 := e }

theorem partAt_withErr (e i p v) : (R.withErr e).PartAt F i p v ↔ R.PartAt F i p v := by
  exact Iff.rfl

theorem zs_withErr (e) : ((R.withErr e).toCx3 F).zs = (R.toCx3 F).zs := by
  rfl

set_option maxHeartbeats 1000000 in

theorem weak_characterisation_with_error (h : R.WeakCharacterisation F) (e) : (R.withErr e).WeakCharacterisation F := by
  cases_type* RealDat3.WeakCharacterisation RealDat.BaseW RealDat.IsGrp RealDat.IsFam RealDat.IsModels RealDat.IsChainW RealDat.IsThPW RealDat3.IsInert RealDat3.IsScal RealDat3.IsTup
  repeat' (first | assumption | constructor)

end RealDat3

end Err

section Three

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin Formalism.IndefR.Eqv

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {F : Face3 D A3}

namespace RealDat3

variable (R : RealDat3 D A3 Ks)

def updS (kap : ℝ) (lam : type_of% R.lam3) : RealDat3 D A3 Ks :=
  { R with toRealDat := R.toRealDat.upd6 kap R.lam, lam3 := lam }

def Eig0 (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) (l : ℝ) : Prop :=
  R.Wp3 i p ≠ ⊥ ∧ ∀ x ∈ R.Wp3 i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x

variable (F) in

def EigOff (i : Fin D.R.m) (p : A3.fam3.base3.Ix) (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  PartX F.cr (R.toCx3 F) false i p v ∧ SimX F.cr (R.toCx3 F) false i p v l

variable {R}

theorem toCx3_updS (kap lam) : (R.updS kap lam).toCx3 F = reScal (R.toCx3 F) (fun _ => kap) lam := rfl

theorem base_eigenvalue_unique {i t p} (l l' : ℝ) (h : R.Eig0 i t p l) (h' : R.Eig0 i t p l') : l = l' := by
  obtain ⟨hb, hl⟩ := h
  obtain ⟨-, hl'⟩ := h'
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hxx : (l : ℂ) • x = (l' : ℂ) • x := (hl x hx).symm.trans (hl' x hx)
  have hc : (l : ℂ) = (l' : ℂ) := by
    by_contra hne
    apply hx0
    have hne' : (l : ℂ) - (l' : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have h0 : ((l : ℂ) - (l' : ℂ)) • x = 0 := by rw [sub_smul, hxx, sub_self]
    calc x = ((l : ℂ) - (l' : ℂ))⁻¹ • (((l : ℂ) - (l' : ℂ)) • x) := by
          rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = 0 := by rw [h0, smul_zero]
  exact_mod_cast hc

theorem eigOff_unique {i p v} (l l' : ℝ) (h : R.EigOff F i p v l) (h' : R.EigOff F i p v l') : l = l' := by
  obtain ⟨⟨x, hx, hm⟩, hs⟩ := h
  obtain ⟨-, hs'⟩ := h'
  have e1 := hs x hx x
  have e2 := hs' x hx x
  have hc : ((l : ℝ) : ℂ) = ((l' : ℝ) : ℂ) := mul_right_cancel₀ hm (e1.symm.trans e2)
  exact_mod_cast hc

theorem partAt_updS (kap lam i p v) : (R.updS kap lam).PartAt F i p v ↔ PartX F.cr (R.toCx3 F) false i p v := by
  exact Iff.rfl

theorem sim_updS (kap lam i p v l) : SimX F.cr ((R.updS kap lam).toCx3 F) false i p v l ↔ SimX F.cr (R.toCx3 F) false i p v l := by
  exact Iff.rfl

theorem zs_updS (kap lam) : ((R.updS kap lam).toCx3 F).zs = (R.toCx3 F).zs := by
  rfl

end RealDat3

open Classical in

theorem scalars_exist (R : RealDat3 D A3 Ks) : ∃ kap lam, (R.updS kap lam).IsScal F := by

  have hcan : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] {a b : ℂ} {x : N}, x ≠ 0 → a • x = b • x → a = b := by
    intro N _ _ a b x hx h
    by_contra hne
    apply hx
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : (a - b) • x = 0 := by rw [sub_smul, h, sub_self]
    calc x = (a - b)⁻¹ • ((a - b) • x) := by rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = 0 := by rw [h0, smul_zero]

  obtain ⟨lam, hlam⟩ : ∃ lam : Fin D.R.m → T → A3.fam3.base3.Ix → InfinitePlace D.what₂.LL → ℝ,
      ∀ i t p v, lam i t p v =
        if v = A3.A.v0 then
          (if h : ∃ l, R.Eig0 i t p l then h.choose else Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i))
        else
          (if h : ∃ l, R.EigOff F i p v l then h.choose else Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i)) :=
    ⟨_, fun _ _ _ _ => rfl⟩

  obtain ⟨kap, hkap⟩ : ∃ kap : ℝ, ∀ κ : ℝ,
      Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 (R.updS 0 lam).lamN κ →
      (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p ≠ 0) → kap = κ := by
    by_cases hex : ∃ κ : ℝ,
        Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 (R.updS 0 lam).lamN κ ∧
        (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p ≠ 0)
    · obtain ⟨κ0, hk0, -⟩ := hex
      refine ⟨κ0, fun κ hk hnd => ?_⟩
      obtain ⟨t, p, hE, hP⟩ := hnd
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
      have e := hcan hx0 ((hk0 t p x hx).symm.trans (hk t p x hx))
      have e' : κ0 * ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p =
          κ * ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p := by exact_mod_cast e
      exact mul_right_cancel₀ hP e'
    · exact ⟨0, fun κ hk hnd => absurd ⟨κ, hk, hnd⟩ hex⟩
  refine ⟨kap, lam, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i t p l hb hl
    have hE : R.Eig0 i t p l := ⟨hb, hl⟩
    show lam i t p A3.A.v0 = l
    rw [hlam, if_pos rfl, dif_pos ⟨l, hE⟩]
    exact RealDat3.base_eigenvalue_unique (R := R) _ _ (Exists.choose_spec _) hE
  · intro κ hk hnd
    exact hkap κ hk hnd
  · intro i p v l hv hP hS
    have hPX : PartX F.cr (R.toCx3 F) false i p v := (RealDat3.partAt_updS kap lam i p v).1 hP
    have hSX : SimX F.cr (R.toCx3 F) false i p v l := (RealDat3.sim_updS kap lam i p v l).1 hS
    have hE : R.EigOff F i p v l := ⟨hPX, hSX⟩
    show lam i A3.A.μ0 p v = l
    rw [hlam, if_neg hv, dif_pos ⟨l, hE⟩]
    exact RealDat3.eigOff_unique (R := R) _ _ (Exists.choose_spec _) hE
  · intro i t p hb
    show lam i t p A3.A.v0 = Real.exp ((F.Zsc ((R.updS kap lam).toCx3 F).zs).l6m i)
    rw [RealDat3.zs_updS, hlam, if_pos rfl, dif_neg]
    rintro ⟨l, hl⟩
    exact hl.1 hb
  · intro i p v hv hnP
    show lam i A3.A.μ0 p v = Real.exp ((F.Zsc ((R.updS kap lam).toCx3 F).zs).l6m i)
    rw [RealDat3.zs_updS, hlam, if_neg hv, dif_neg]
    rintro ⟨l, hl⟩
    exact hnP ((RealDat3.partAt_updS kap lam i p v).2 hl.1)
  · intro i t p v hv
    show lam i t p v = lam i A3.A.μ0 p v
    rw [hlam, hlam, if_neg hv, if_neg hv]

variable (D A3 Ks) in

def ThreeFaceBaseDatumExists (F : Face3 D A3) : Prop := ∃ R : RealDat3 D A3 Ks, R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces

def FormsExist (F : Face3 D A3) (Geo : RealDat D A3.A Ks → Prop) : Prop :=
  ∀ R : RealDat3 D A3 Ks, R.toRealDat.Pre1 F.lv2 → R.toRealDat.IsChainW → R.toRealDat.IsThPW → R.toRealDat.FullY → R.toRealDat.FullP →
    ∃ nW FW err0, (R.toRealDat.upd5 nW FW R.mu R.twPl err0).grp_chiW ∧ Geo (R.toRealDat.upd5 nW FW R.mu R.twPl err0)

end Three

end Formalism.IndefR.Links

end
