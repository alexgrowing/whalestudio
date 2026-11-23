import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsQuasicoherentDualOm

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace NumberField
open scoped TensorProduct NNReal CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections)
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HTSheaf GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.HTm

section Generic

variable {p : ℕ} [Fact p.Prime] {C : SCF p} {Λ : Type} [CommRing Λ] [StarRing Λ]
  {P : Point p (fldVal C) ↥(intO ↥C.S) Λ} {X : Scheme.{0}} {G : Over X} [GrpObj G] [QuasiSeparated G.hom]
  {z : Sp ↥(intO ↥C.S) ⟶ X} {φ : P.G.left ⟶ G.left} {hφ : IsGrpPullback P.G G z φ}
  {La : Type} [AddCommGroup La] {lv : La → ChTor.Pts P.A.A} {n : ℕ} {h : La →+ Γ(modN (omega G) (p ^ n), ⊤)}

omit [QuasiSeparated G.hom] in

theorem pow_smul_eq (w : P.OmC) : ((p : ↥C.S) ^ n) • w = p ^ n • w := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

theorem isVal_iff (hadd : ∀ a b, lv (a + b) = lv a * lv b) (hker : ∀ a, lv a = 1 → ∃ b, a = p ^ n • b) {t : P.T}
    {v v' : P.OmC} (hv : IsVal hφ lv h t v) :
    (∃ w ∈ P.latOm, v - v' = ((p : ↥C.S) ^ n) • w) ↔ IsVal hφ lv h t v' := by
  simp only [pow_smul_eq]
  refine ⟨fun ⟨w, hw, e⟩ => ?_, fun ⟨a, ha, hv'⟩ => (hv.isLiftAt hadd hker ha).sub hv'⟩
  obtain ⟨a, ha, hv⟩ := hv
  exact ⟨a, ha, hv.of_sub (neg_mem hw) (by rw [smul_neg, ← e, neg_sub])⟩

theorem fibLat_eq (hadd : ∀ a b, lv (a + b) = lv a * lv b) (hker : ∀ a, lv a = 1 → ∃ b, a = p ^ n • b)
    (htors : ∀ a, lv a ^ p ^ n = 1) {J : Type} [Fintype J] (b : J → La)
    (hb : ∀ a, h a ∈ (spanSub fun i => h (b i)).sec ⊤) {f : P.T → P.OmC} (hf : ∀ t, IsVal hφ lv h t (f t)) :
    (fibLat hφ (preSub (cokernel.π (p ^ n • 𝟙 (omega G))) (spanSub fun i => h (b i)))).toAddSubgroup =
      P.latOm.toAddSubgroup ⊓ (Ospan (C := ↥C.S) (Set.range f) ⊔
        P.latOm.toAddSubgroup.map (DistribSMul.toAddMonoidHom P.OmC ((p : ↥C.S) ^ n))) := by
  have e : P.latOm.toAddSubgroup.map (DistribSMul.toAddMonoidHom P.OmC ((p : ↥C.S) ^ n)) =
      (P.latOm.map (p ^ n • LinearMap.id)).toAddSubgroup :=
    AddSubgroup.ext fun v => exists_congr fun w => and_congr_right fun _ => by
      rw [DistribSMul.toAddMonoidHom_apply, pow_smul_eq]; rfl
  have key : fibLat hφ (preSub (cokernel.π (p ^ n • 𝟙 (omega G))) (spanSub fun i => h (b i))) =
      Submodule.span _ (Set.range f) ⊔ P.latOm.map (p ^ n • LinearMap.id) := by
    refine le_antisymm (fibLat_preSub_spanSub_le hφ _ (fun w hw => ?_) fun i => ?_)
      (sup_le (Submodule.span_le.2 ?_) (Submodule.map_le_iff_le_comap.2 fun w hw => nsmul_mem_fibLat_preSub hφ _ hw))
    · exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := p ^ n • LinearMap.id) hw)
    · obtain ⟨t, ht⟩ := (tate_free_of_card p _ _ P.card_torsion).2.1 n _ (htors (b i))
      exact ⟨f t, Submodule.mem_sup_left (Submodule.subset_span (Set.mem_range_self t)),
        (hf t).isLiftAt hadd hker ht.symm⟩
    · rintro _ ⟨t, rfl⟩
      obtain ⟨a, -, ha⟩ := hf t
      exact ha.mem_fibLat hφ (hb a)
  rw [e, ospan_eq_span, ← Submodule.sup_toAddSubgroup, ← key]
  exact (inf_eq_right.2 fun _ hv => fibLat_le hφ _ hv).symm

end Generic

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p) {Z : ct.Mdl} {n : ℕ}

section Points

variable (h : HTOn Z n) (y : ct.Pt Z)

def IsValAt (t : (htpTrue ct).Tp y) (v : (htpTrue ct).OmV y) : Prop :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  IsVal (ct.isGrpPullback_htToMdl y) (levPt y.P (p ^ n)) h.1 t v

def IsHT : Prop := ∀ (y : ct.Pt Z) (t : (htpTrue ct).Tp y), IsValAt ct h y t ((htpTrue ct).ht y t)

def latAt (M : Sub Z.om) : AddSubgroup ((htpTrue ct).OmV y) :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  (fibLat (ct.isGrpPullback_htToMdl y) M).toAddSubgroup

theorem latAt_le (M : Sub Z.om) : latAt ct y M ≤ (htpTrue ct).om y :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  fibLat_le (ct.isGrpPullback_htToMdl y) M

theorem IsValAt.mem {t : (htpTrue ct).Tp y} {v : (htpTrue ct).OmV y} (hv : IsValAt ct h y t v) : v ∈ (htpTrue ct).om y :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  hv.choose_spec.2.mem

open Classical in

def eOm (σ : D.host.E →+* ℂ) : (htpTrue ct).OmV y →ₗ[(ct.fld y).C] (htpTrue ct).OmV y :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  EigenSplit.proj (isSplitting_embInt y.P) (ct.htPt y).actOm σ

def eLat (σ : D.host.E →+* ℂ) : AddSubgroup ((htpTrue ct).OmV y) :=
  (latAt ct y (epsOm ct h σ)).comap
    (DistribSMul.toAddMonoidHom _ (show (ct.fld y).C from y.P.fK (dif ct Z σ : Z.i.c.F)))

def wLat (σ : D.host.E →+* ℂ) : AddSubgroup ((htpTrue ct).TC y) where
  carrier := {x | ∃ l : (htpTrue ct).OmV y →ₗ[(ct.fld y).C] (ct.fld y).C, (∀ v ∈ eLat ct h y (conjEmb σ), ‖l v‖ ≤ 1) ∧
    ∀ t, (htpTrue ct).psiC y x t = l (eOm ct y (conjEmb σ) ((htpTrue ct).htC y t))}
  zero_mem' := ⟨0, fun _ _ => by simp, fun _ => by simp⟩
  add_mem' := fun ⟨l, hl, e⟩ ⟨l', hl', e'⟩ => ⟨l + l', fun v hv =>
    (IsUltrametricDist.norm_add_le_max (S := ↥y.C.S) _ _).trans (max_le (hl v hv) (hl' v hv)),
    fun t => by rw [map_add, LinearMap.add_apply, e, e', LinearMap.add_apply]⟩
  neg_mem' := fun ⟨l, hl, e⟩ => ⟨-l, fun v hv => (norm_neg _).trans_le (hl v hv),
    fun t => by rw [map_neg, LinearMap.neg_apply, e, LinearMap.neg_apply]⟩

variable (hn : p ^ n ∣ Z.i.l.A)
include hn

theorem exists_val : ∃ f : (htpTrue ct).Tp y →+ (htpTrue ct).OmV y, ∀ t, IsValAt ct h y t (f t) :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  exists_isVal (ct.isGrpPullback_htToMdl y) h.1 (levPt_add y.P _) fun q => ((levPt_spec y.P hn).1 q).1

theorem isValAt_iff {t : (htpTrue ct).Tp y} {v v' : (htpTrue ct).OmV y} (hv : IsValAt ct h y t v) :
    (∃ w ∈ (htpTrue ct).om y, v - v' = ((p : (ct.fld y).C) ^ n) • w) ↔ IsValAt ct h y t v' :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  isVal_iff (levPt_add y.P _) (fun a => ((levPt_spec y.P hn).2.1 a).1) hv

theorem latAt_omP {f : (htpTrue ct).Tp y → (htpTrue ct).OmV y} (hf : ∀ t, IsValAt ct h y t (f t)) :
    latAt ct y (omP h) = (htpTrue ct).om y ⊓ (Ospan (C := (ct.fld y).C) (Set.range f) ⊔
      ((htpTrue ct).om y).map (DistribSMul.toAddMonoidHom ((htpTrue ct).OmV y) ((p : (ct.fld y).C) ^ n))) :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  fibLat_eq (levPt_add y.P _) (fun a => ((levPt_spec y.P hn).2.1 a).1)
    (fun a => ((levPt_spec y.P hn).1 _).2 ⟨a, rfl⟩) _ (mem_imHT h) hf

end Points

theorem IsHT.pull {B : ct.Mdl} [IsIso B.π] (e : Z.i = B.i) {h : HTOn B n} (hh : IsHT ct h) : IsHT ct (pull Z e h) := by
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  obtain ⟨⟨i, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈, z₉, z₁₀⟩, w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈, w₉, w₁₀⟩ := Z
  obtain rfl : i = B.i := e
  let Z : ct.Mdl := ⟨⟨B.i, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈, z₉, z₁₀⟩, w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈, w₉, w₁₀⟩
  change IsHT ct (HTm.pull Z (B := B) rfl h)
  intro y t
  let y₀ : ct.Pt B := ⟨y.C, y.P, y.z ≫ toBase Z B rfl, by
    rw [Category.assoc, toBase_π, eqToHom_refl, Category.comp_id, y.z_π]⟩
  obtain ⟨a, ha, hv⟩ := hh y₀ t
  refine ⟨a, ha, IsLiftAt.pbMod (ct.isGrpPullback_htToMdl y₀) (isGrpPullback_toBaseG Z B rfl)
    (ct.isGrpPullback_htToMdl y) rfl ?_ hv⟩
  refine B.tMap.cart.1.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((toBaseG_φ Z B rfl).trans (Category.comp_id _))).trans ?_)
    exact (ct.htToMdl_φ y).trans (ct.htToMdl_φ y₀).symm
  · exact ((ct.isGrpPullback_htToMdl y).comp (isGrpPullback_toBaseG Z B rfl)).1.w.trans
      (ct.isGrpPullback_htToMdl y₀).1.w.symm

theorem A_Xn (n : ℕ) : (ct.Xn n).i.l.A = κ.l.A * p ^ n := (ct.B.lvl (some n)).2.2.1

theorem pow_dvd_A (n : ℕ) : p ^ n ∣ (ct.Xn n).i.l.A := A_Xn ct n ▸ dvd_mul_left _ _

theorem eq_of_i_eq {n m : ℕ} (h : (ct.Xn n).i = (ct.Xn m).i) : n = m :=
  Nat.pow_right_injective ct.hp.two_le (Nat.eq_of_mul_eq_mul_left κ.l.A_pos
    ((A_Xn ct n).symm.trans ((congrArg (·.l.A) h).trans (A_Xn ct m))))

instance isIso_π_Xn (n : ℕ) : IsIso (ct.Xn n).π := ct.B.iso (some n)

theorem blowUp_i (J : ct.Idl Z) : (ct.blowUp Z J).i = Z.i := by
  by_cases h : ∃ Z', IsNBlow Z J Z'
  · exact (blowUp_spec h).1
  · exact congrArg (·.i) (dif_neg h : blowUp Z J = Z)

def htEval (h : HTOn (ct.Xn n) n) (y : ct.Pt (ct.Xn n)) : (htpTrue ct).Tp y →+ (htpTrue ct).OmV y :=
  (exists_val ct h y (pow_dvd_A ct n)).choose

theorem isValAt_htEval (h : HTOn (ct.Xn n) n) (y : ct.Pt (ct.Xn n)) (t : (htpTrue ct).Tp y) :
    IsValAt ct h y t (htEval ct h y t) := (exists_val ct h y (pow_dvd_A ct n)).choose_spec t

theorem isHT_iff (h : HTOn (ct.Xn n) n) : IsHT ct h ↔ ∀ (y : ct.Pt (ct.Xn n)) (t : (htpTrue ct).Tp y),
    htEval ct h y t ∈ (htpTrue ct).om y ∧
      ∃ v ∈ (htpTrue ct).om y, htEval ct h y t - (htpTrue ct).ht y t = ((p : (ct.fld y).C) ^ n) • v :=
  forall₂_congr fun y t => ((and_iff_right ((isValAt_htEval ct h y t).mem ct h y)).trans
    (isValAt_iff ct h y (pow_dvd_A ct n) (isValAt_htEval ct h y t))).symm

def IsModelOf (Z : ct.Mdl) (n : ℕ) (h : HTOn (ct.Xn n) n) : Prop :=
  3 ≤ n ∧ IsHT ct h ∧ Z = ct.blowUp (ct.Xn n) (htIdl ct h)

theorem IsModelOf.i_eq {h : HTOn (ct.Xn n) n} (H : IsModelOf ct Z n h) : Z.i = (ct.Xn n).i := H.2.2 ▸ blowUp_i ct _

def IsHTBlowup (Z' Z : ct.Mdl) : Prop := ∃ n h, Z = ct.Xn n ∧ IsModelOf ct Z' n h

theorem isHTBlowup_iff {Z' : ct.Mdl} : IsHTBlowup ct Z' (ct.Xn n) ↔ ∃ h, IsModelOf ct Z' n h := by
  refine ⟨?_, fun ⟨h, H⟩ => ⟨n, h, rfl, H⟩⟩
  rintro ⟨m, h, e, H⟩
  obtain rfl := eq_of_i_eq ct (congrArg (·.i) e)
  exact ⟨h, H⟩

open Classical in

def htData (Z : ct.Mdl) : Σ n, HTOn Z n :=
  if H : ∃ d : Σ n, HTOn (ct.Xn n) n, IsModelOf ct Z d.1 d.2 then
    ⟨H.choose.1, pull Z (H.choose_spec.i_eq ct) H.choose.2⟩ else ⟨0, 0⟩

theorem htData_eq (H : IsHTBlowup ct Z (ct.Xn n)) :
    ∃ (h : HTOn (ct.Xn n) n) (H' : IsModelOf ct Z n h), htData ct Z = ⟨n, pull Z (H'.i_eq ct) h⟩ := by
  obtain ⟨h₀, H₀⟩ := (isHTBlowup_iff ct).1 H
  have H₁ : ∃ d : Σ n, HTOn (ct.Xn n) n, IsModelOf ct Z d.1 d.2 := ⟨⟨n, h₀⟩, H₀⟩
  have key : ∀ (d : Σ n, HTOn (ct.Xn n) n) (Hd : IsModelOf ct Z d.1 d.2), ∃ (h : HTOn (ct.Xn n) n) (H' : IsModelOf ct Z n h),
      (⟨d.1, pull Z (Hd.i_eq ct) d.2⟩ : Σ n, HTOn Z n) = ⟨n, pull Z (H'.i_eq ct) h⟩ := by
    rintro ⟨m, h⟩ Hd
    obtain rfl : n = m := eq_of_i_eq ct ((H₀.i_eq ct).symm.trans (Hd.i_eq ct))
    exact ⟨h, Hd, rfl⟩
  rw [htData, dif_pos H₁]
  exact key _ H₁.choose_spec

def omSub (Z : ct.Mdl) : Sub Z.om := omP (htData ct Z).2

def epsSub (Z : ct.Mdl) (σ : D.host.E →+* ℂ) : Sub Z.om := epsOm ct (htData ct Z).2 σ

theorem latAt_omSub (H : IsHTBlowup ct Z (ct.Xn n)) (y : ct.Pt Z) :
    latAt ct y (omSub ct Z) = (htpTrue ct).om y ⊓ (Ospan (C := (ct.fld y).C) (Set.range ((htpTrue ct).ht y)) ⊔
      ((htpTrue ct).om y).map (DistribSMul.toAddMonoidHom ((htpTrue ct).OmV y) ((p : (ct.fld y).C) ^ n))) := by
  obtain ⟨h, H', e⟩ := htData_eq ct H
  rw [omSub, e]
  exact latAt_omP ct _ y (H'.i_eq ct ▸ pow_dvd_A ct n) (H'.2.1.pull ct _ y)

def embB (D : D7) (s : Bool) (τ : PsiT D) : D.host.E →+* ℂ := bif s then conjEmb (At.psiEmb D τ) else At.psiEmb D τ

section Boundary

variable {ct}

structure IntPt (Z : ct.Mdl) : Type where

  C : SCF p

  alg : Z.i.c.V ct.W →+* ↥(intO ↥C.S)

  fK : Z.i.c.F →+* ↥C.S
  compat : (intO ↥C.S).subtype.comp alg = fK.comp (Z.i.c.V ct.W).subtype

  z : Sp ↥(intO ↥C.S) ⟶ Z.X
  z_s : z ≫ Z.s = spMap alg

namespace IntPt

def ofPt (y : ct.Pt Z) : IntPt Z where
  C := y.C
  alg := y.P.alg
  fK := y.P.fK
  compat := y.P.compat
  z := y.z
  z_s := by rw [← Z.π_s, reassoc_of% y.z_π, y.P.yt_over]

variable (y : IntPt Z)

def gen : Sp ↥y.C.S ⟶ Z.X := spMap (intO ↥y.C.S).subtype ≫ y.z

def Om : Type := Γ((Scheme.Modules.pullback y.gen).obj Z.om, ⊤)

instance : AddCommGroup y.Om := inferInstanceAs (AddCommGroup Γ((Scheme.Modules.pullback y.gen).obj Z.om, ⊤))

instance : Module ↥y.C.S y.Om :=
  Module.compHom Γ((Scheme.Modules.pullback y.gen).obj Z.om, ⊤) (LieVB.cst ↥y.C.S)

theorem le_gen {U : Z.X.Opens} (e : ⊤ ≤ y.z ⁻¹ᵁ U) : ⊤ ≤ y.gen ⁻¹ᵁ U := fun _ _ => e trivial

def ev {U : Z.X.Opens} (e : ⊤ ≤ y.z ⁻¹ᵁ U) (s : Γ(Z.om, U)) : y.Om := pullbackSections y.gen Z.om (y.le_gen e) s

def lat (M : Sub Z.om) : AddSubgroup y.Om :=
  Ospan (C := ↥y.C.S) {v | ∃ (U : Z.X.Opens) (e : ⊤ ≤ y.z ⁻¹ᵁ U), ∃ s ∈ M.sec U, y.ev e s = v}

theorem lat_mono {M M' : Sub Z.om} (h : ∀ U, M.sec U ≤ M'.sec U) : y.lat M ≤ y.lat M' :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, ⟨U, e, s, hs, hx⟩, hv⟩ => ⟨a, ha, x, ⟨U, e, s, h U hs, hx⟩, hv⟩

def actOm : 𝓞 D.host.E →+* Module.End ↥y.C.S y.Om where
  toFun a :=
    { toFun := (act (pullAct (omAct Z) y.gen) a).app ⊤
      map_add' := map_add _
      map_smul' := fun _ _ => Scheme.Modules.Hom.app_smul _ _ _ }
  map_one' := LinearMap.ext fun s => congr(Scheme.Modules.Hom.app $(map_one (pullAct (omAct Z) y.gen)) ⊤ s)
  map_mul' a b := LinearMap.ext fun s => congr(Scheme.Modules.Hom.app $(map_mul (pullAct (omAct Z) y.gen) a b) ⊤ s)
  map_zero' := LinearMap.ext fun s => congr(Scheme.Modules.Hom.app $(map_zero (pullAct (omAct Z) y.gen)) ⊤ s)
  map_add' a b := LinearMap.ext fun s => congr(Scheme.Modules.Hom.app $(map_add (pullAct (omAct Z) y.gen) a b) ⊤ s)

open Classical in

def eOm (σ : D.host.E →+* ℂ) : y.Om →ₗ[↥y.C.S] y.Om :=
  EigenSplit.proj ((isSplitting_embK Z.i.c).map y.fK) y.actOm σ

def eLat (σ : D.host.E →+* ℂ) : AddSubgroup y.Om :=
  (y.lat (epsSub ct Z σ)).comap (DistribSMul.toAddMonoidHom _ (y.fK (dif ct Z σ : Z.i.c.F)))

theorem actOm_eOm (σ : D.host.E →+* ℂ) (a : 𝓞 D.host.E) (v : y.Om) :
    y.actOm a (y.eOm σ v) = y.fK (embK Z.i.c σ a) • y.eOm σ v := by
  classical
  exact EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem ((isSplitting_embK Z.i.c).map y.fK) y.actOm σ v) a

end IntPt

def BdPt (Z : ct.Mdl) : Type := {y : IntPt Z // ∀ x, y.gen x ∉ Z.opn}

end Boundary

end GlobalTheory.LocM.HTm

namespace GlobalTheory.LocM

open HTm

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def htmTrue (ct : At S κ p) : HTmSt ct (shfTrue ct) (htpTrue ct) where
  IsHTBlowup := IsHTBlowup ct
  eOmP Z s τ := Z.ofMod (epsSub ct Z (embB D s τ)).toMod
  htSES Z τ := ses ct (htData ct Z).2 (At.psiEmb D τ)
  BT n := BTOn ct (ct.Xn n) n
  extA B := B.Ext ct
  compat B B' := B.Compat ct B'
  HTn n := HTOn (ct.Xn n) n
  htEval := htEval ct
  htIdl := htIdl ct
  IsHTBlowup_def _ _ hn := (isHTBlowup_iff ct).trans (exists_congr fun h =>
    (and_iff_right hn).trans (and_congr_left' (isHT_iff ct h)))
  wFib h y τ := wLat ct h y (At.psiEmb D τ)
  omSh Z := Z.ofMod (omSub ct Z).toMod
  omPat {Z} y := latAt ct y (omSub ct Z)
  omPat_def _ _ _ H y := latAt_omSub ct H y
  BPt Z := BdPt Z
  bfld y := y.1.C.toCF
  OmB y := y.1.Om
  obAdd _ := inferInstance
  obMod y := (inferInstance : Module ↥y.1.C.S y.1.Om)
  omB {Z} y := y.1.lat (Lat.top Z).N
  omPB {Z} y := y.1.lat (omSub ct Z)
  eOmB y τ := y.1.eLat (At.psiEmb D τ)
  eB y τ := y.1.eOm (At.psiEmb D τ)

namespace HTm

variable (ct : At S κ p)

def omShIso (Z : ct.Mdl) : ((htmTrue ct).omSh Z).toMod ≅ (omSub ct Z).toMod :=
  @At.presIso _ _ _ _ _ _ _ ct Z _ (isFiniteQC_omP ct _)

def eOmPIso (Z : ct.Mdl) (s : Bool) (τ : PsiT D) :
    ((htmTrue ct).eOmP Z s τ).toMod ≅ (epsSub ct Z (embB D s τ)).toMod :=
  @At.presIso _ _ _ _ _ _ _ ct Z _ (isFiniteQC_epsOm ct _ _)

theorem latticeAt_omega_eq_inf_hodgeTateSpan {n : ℕ} (h : HTOn (ct.Xn n) n) (y : ct.Pt (ct.Xn n)) :
    latAt ct y (omP h) = (htpTrue ct).om y ⊓ (Ospan (C := (ct.fld y).C) (Set.range (htEval ct h y)) ⊔
      ((htpTrue ct).om y).map (DistribSMul.toAddMonoidHom ((htpTrue ct).OmV y) ((p : (ct.fld y).C) ^ n))) :=
  latAt_omP ct h y (pow_dvd_A ct n) (isValAt_htEval ct h y)

theorem htSES_k₀ {Z : ct.Mdl} {n : ℕ} (H : IsHTBlowup ct Z (ct.Xn n)) (τ : PsiT D) :
    At.SES.k₀ ((htmTrue ct).htSES Z τ) = n - 2 := by
  obtain ⟨h, H', e⟩ := htData_eq ct H
  exact congrArg (fun d : Σ n, HTOn Z n => d.1 - 2) e

example (Z : ct.Mdl) (y : (htmTrue ct).BPt Z) : (htmTrue ct).omPB y ≤ (htmTrue ct).omB y :=
  y.1.lat_mono fun U => (Lat.isTop_top U).ge.trans' le_top

example (Z : ct.Mdl) (h : HTOn Z 0) (U : Z.X.Opens) (s : Γ(Z.om, U)) : s ∈ (omP h).sec U := by
  simpa using pow_smul_mem_omP h s

example (Z : ct.Mdl) : ¬ (htmTrue ct).IsHTBlowup Z (ct.Xn 2) := fun H =>
  have ⟨_, H'⟩ := (isHTBlowup_iff ct).1 H
  absurd H'.1 (by decide)

example (Z : ct.Mdl) (y : ct.Pt Z) (x : Sp ↥y.C.S) : (IntPt.ofPt y).gen x ∈ Z.opn :=
  have e : y.P.y ≫ (ct.Y Z.i).j = (spMap (intO ↥y.C.S).subtype ≫ y.z) ≫ Z.π := by rw [← y.P.ext, ← y.z_π, Category.assoc]
  ⟨y.P.y x, congr($e x)⟩

end HTm

end GlobalTheory.LocM
