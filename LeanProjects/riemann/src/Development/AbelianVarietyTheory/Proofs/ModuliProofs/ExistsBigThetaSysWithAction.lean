import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory.ThetaSysOfObj

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH GlobalTheory.SymBaseChange

theorem exists_big (g n : ℕ) (hn : 2 ≤ n) : ∃ k j₁ : ℕ, 2 ≤ k ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set N := (n ^ (k₀ + 2)) ^ 2 with hN
  have hN₁ : k₀ + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨k₀ + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem exists_level {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {g k : ℕ} [NeZero k]
    {J : Type} {b : TBase o k} (u : TObj g k J b (spMap (algebraMap o R))) :
    ∃ lev : Out.Level u.pol k (unitOn (Units.map (algebraMap o R).toMonoidHom b.ζ)), lev.pt = u.pt := by
  have ez : unitS (spMap (algebraMap o R)) b.ζ = unitOn (Units.map (algebraMap o R).toMonoidHom b.ζ) :=
    Units.ext (congrArg (fun q => q.hom (b.ζ : o))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap o R)))).symm
  have hv : ∀ c : Fin k, ((c : ℕ) : ZMod k).val = c := fun c => ZMod.val_cast_of_lt c.2
  refine ⟨⟨u.pt, ?_, u.torsion, fun K _ _ s c c' h => ?_, fun K _ _ s y hy => ?_, fun i j => ez ▸ u.pairing i j⟩, rfl⟩
  · have h₁ : IsPrimitiveRoot (algebraMap o R b.ζ) k :=
      (b.prim Ω (algebraMap o Ω)).of_map_of_injective (f := R.val) Subtype.val_injective
    exact IsPrimitiveRoot.coe_units_iff.1 (h₁.map_of_injective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1)
  · have := u.ab.comm
    let w : Over.mk s ⟶ baseOver (Sp R) := Over.homMk s (by simp)
    have e : ∀ c : Fin (2 * g) → Fin k, linComb (fun i => w ≫ u.pt i) (fun i => (((c i : ℕ) : ZMod k)).val) =
        linComb (fun i => w ≫ u.pt i) (fun i => (c i : ℕ)) := fun c => congrArg _ (funext fun i => hv _)
    have t : linComb (fun i => w ≫ u.pt i) (fun i => (((c' i : ℕ) : ZMod k)).val) ^ k = 1 := by
      refine (congrArg (· ^ k) (ThetaPtUp.map_linComb (preHom w) u.pt _).symm).trans ?_
      rw [← map_pow]
      exact (congrArg _ (ThetaPtUp.lab_pow u fun i => ((c' i : ℕ) : ZMod k))).trans (map_one _)
    have q := (u.bij K s _ t).unique (y₁ := fun i => ((c i : ℕ) : ZMod k)) (y₂ := fun i => ((c' i : ℕ) : ZMod k))
      ((e c).trans (h.trans (e c').symm)) rfl
    exact funext fun i => Fin.ext ((hv _).symm.trans ((congrArg ZMod.val (congrFun q i)).trans (hv _)))
  · obtain ⟨c, hc, -⟩ := u.bij K s y hy
    exact ⟨fun i => ⟨(c i).val, ZMod.val_lt _⟩, hc⟩

theorem exists_act {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {B B' : Scheme.{0}}
    (t : SAB H B) {G' : Over B'} [GrpObj G'] [IsCommMonObj G'] {f : B' ⟶ B} {φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G f φ) {L' : LB G'.left} (hL' : L'.IsLB) (hb : LBIso L' (t.PP.L.pull φ)) :
    ∃ act : Geo.Tor.OAct (𝓞 E) G', (∀ a, (act.act a).left ≫ φ = φ ≫ (t.act.act a).left) ∧
      (∀ a, LBIso (cubeLB G' ![fst _ _ ≫ act.act a, snd _ _] L')
        (cubeLB G' ![fst _ _, snd _ _ ≫ act.act (H.bar a)] L')) ∧
      LBIso L' (cubeLB G' ![𝟙 _, act.act H.w0] L') := by
  choose w hw pa using fun a => @exists_endo _ _ _ _ _ _ _ _ h (t.act.act a) (t.act.hom a)
  have p₁ : ∀ a, pushPt h.1.w (w a) = pushPt h.1.w (𝟙 G') ≫ t.act.act a := fun a =>
    (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa a _)
  have hB : (t.PP.L.pull φ).IsLB := pull_isLB t.PP.isLB φ
  refine ⟨⟨w, hw, ?_, fun a b => ?_, fun a b => ?_⟩, fun a => ?_, fun a => ?_, ?_⟩
  · apply pushPt_injective h
    rw [p₁, t.act.one, Category.comp_id]
  · apply pushPt_injective h
    rw [pa, p₁, p₁, t.act.mul, Category.assoc]
  · apply pushPt_injective h
    have q : pushPt h.1.w (w a * w b) = pushPt h.1.w (w a) * pushPt h.1.w (w b) := map_mul (pushHom h G') _ _
    rw [q, p₁, p₁, p₁, t.act.add, MonObj.comp_mul]
  · exact (congrArg (fun z => z.left) (p₁ a)).trans (congrArg (· ≫ _) (Category.id_comp φ))
  · have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ w a, snd G' G'] (t.PP.L.pull φ))
        (cubeLB G' ![fst G' G', snd G' G' ≫ w (H.bar a)] (t.PP.L.pull φ)) := by
      let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ _).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
      (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
        (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))
  · have h₁ : LBIso (t.PP.L.pull φ) (cubeLB G' ![𝟙 G', w H.w0] (t.PP.L.pull φ)) := by
      let U := pushPt h.1.w (𝟙 G')
      refine LBIso.chartPull (Geo.Tor.chartPullPull t.PP.L _ U.left (Category.id_comp _))
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact p₁ _
    exact LBIso.trans hL' hB (DVR.linComb_isLB L' hL' _ _) hb
      (LBIso.trans hB (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
        (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

theorem exists_unit_generic (hL : Laws) (hL₂ : Laws2) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    [hb : ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) {I : Type} (x : I → (baseOver (Sp S.R) ⟶ ρ.P.A))
    (a : I → S.Gam) (hx : ∀ i, x i ^ (S.r * S.N) = ρ.pt (a i)) (v : I → Ω) {m : ℕ} (hm : m = S.r * S.N)
    (w : Over.mk (spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R)) (hw : w.left = spMap S.R.val.toRingHom)
    (H : IsThetaPt ρ.P m (fun i => w ≫ x i)
      (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v i))) :
    ∃ c : Ω, c ≠ 0 ∧ ∀ i, ∃ e : ℕ, v i = c * algebraMap o Ω (S.ζ ^ e) * S.th (a i) := by
  subst hm
  have := hb.ded
  have : IsNoetherianRing S.R := isNoetherianRing_of_fg S.fg
  have hu : IsUnit (((S.r * S.N) ^ 2 : ℕ) : Γ(Sp S.R, ⊤)) := by
    have := ((S.unit.map (algebraMap o S.R)).map (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom).pow 2
    rwa [map_natCast, map_natCast, ← Nat.cast_pow] at this
  obtain ⟨α, hα⟩ := hL.mulPull _ ρ.P (S.r * S.N)
  have hth : IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := fun s => by
    obtain ⟨r, hr, -⟩ := ρ.th₁_basis s
    exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩
  have lift : ∀ (z : ℤ), z = ((S.r * S.N) ^ 2 : ℕ) → ∀ i, ∃ θ : ThetaGrp ρ.P.A ρ.P.L z (baseOver (Sp S.R)),
      SymLift ρ.P.A ρ.P.L z ((S.r * S.N) ^ 2) (x i) θ := by
    rintro _ rfl i
    exact exists_symLift_global hL _ ρ.P _ H.1.pow hu _ _ (by rw [sq, pow_mul, hx, (ρ.fr_tors (a i)).1])
  obtain ⟨v₁, h₁⟩ := ThetaLocal.exists_isThetaPtOver ρ.P _ α hα x ρ.th₁ hth (lift _ (Nat.cast_pow _ _).symm)
  let iso := Scheme.ΓSpecIso (CommRingCat.of S.R)
  obtain ⟨v₂, rfl⟩ : ∃ v₂ : I → S.R, v₁ = fun i => fn (v₂ i) :=
    ⟨fun i => iso.hom.hom (v₁ i), funext fun i => (iso.hom_inv_id_apply (v₁ i)).symm⟩
  obtain ⟨c, hc⟩ := thetaPt_eq_unit_mul_th hL o Ω S ρ I x a v₂ hx h₁
  have : IsAffine (Over.mk (spMap S.R.val.toRingHom)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (baseOver (Sp S.R)).left := inferInstanceAs (IsAffine (Spec _))
  have h₂ := ThetaBaseChange.isThetaPtOver_pull_of_gen ρ.P h₁ w
    fun _ => EmbPull.isGenSec_pullS ρ.P hL₂.secBaseChangeAny w
  let e : Γ(Sp Ω, ⊤) ≃+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk (spMap S.R.val.toRingHom)).left, ⊤) := e.symm.isLocalRing
  obtain ⟨d, hd⟩ := ThetaUniq.exists_unit_over hL.globalFns ρ.P H.1 h₂ (ThetaUniq.isThetaPtOver_of_local _ _ H)
  refine ⟨e d.val * (c : S.R), mul_ne_zero (d.isUnit.map e).ne_zero (c.isUnit.map S.R.val).ne_zero, fun i => ?_⟩
  obtain ⟨m, hm⟩ := hc i
  have q := (congrArg e (hd i)).trans (map_mul e _ _)
  have q₂ : w.left.appTop.hom (fn (v₂ i)) = e.symm (v₂ i) := by
    rw [hw]
    exact (congrArg (fun q => q.hom (v₂ i))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom S.R.val.toRingHom))).symm
  refine ⟨m, (e.apply_symm_apply (v i)).symm.trans (q.trans ?_)⟩
  rw [q₂, e.apply_symm_apply, hm, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc]

theorem finite_of_le {Ω : Type} [Field Ω] {F F' : Subfield Ω} (le : F ≤ F') (H : Module.Finite F Ω) :
    Module.Finite F' Ω := by
  letI := (Subfield.inclusion le).toAlgebra
  haveI : IsScalarTower F F' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite F _ _

theorem finite_of_ratios {o Ω I K : Type} [CommRing o] [Field Ω] [Algebra o Ω] {v : I → Ω} {t : K → Ω} {a : I → K}
    {c : Ω} (hc : c ≠ 0) (h : ∀ i, ∃ z : o, v i = c * algebraMap o Ω z * t (a i))
    (H : Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = v i / v i'})) Ω) :
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω := by
  have le : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = v i / v i'}) ≤
      Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) := by
    refine Subfield.closure_le.2 (Set.union_subset (fun x hx => Subfield.subset_closure (Or.inl hx)) ?_)
    rintro _ ⟨i, i', rfl⟩
    obtain ⟨z, hz⟩ := h i
    obtain ⟨z', hz'⟩ := h i'
    rw [hz, hz', _root_.mul_assoc, _root_.mul_assoc, mul_div_mul_left _ _ hc, mul_div_mul_comm]
    exact mul_mem (div_mem (Subfield.subset_closure (Or.inl ⟨z, rfl⟩)) (Subfield.subset_closure (Or.inl ⟨z', rfl⟩)))
      (Subfield.subset_closure (Or.inr ⟨_, _, rfl⟩))
  exact finite_of_le le H

theorem exists_points {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {R : Type} [CommRing R] {g k : ℕ}
    {J : Type} {b : TBase o k} {s : Sp R ⟶ Sp o} (u : TObj g k J b s) (S : ThetaSys o Ω) (ρ : S.Real) (hg : S.g = g)
    {f : Sp S.R ⟶ Sp R} {φ : ρ.P.A.left ⟶ u.A.left} (hp : IsGrpPullback ρ.P.A u.A f φ)
    (h : ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + g →
      (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ = f ≫ (u.pt i₁ ^ (S.r * S.N)).left ∧
      (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ = f ≫ (u.pt i₂ ^ (S.r * S.N)).left) :
    ∃ (x : Ix g k → (baseOver (Sp S.R) ⟶ ρ.P.A)) (a : Ix g k → S.Gam),
      (∀ i, x i ^ (S.r * S.N) = ρ.pt (a i)) ∧ (∀ i, (x i).left ≫ φ = f ≫ (u.lab i).left) ∧ ∀ i, x i ^ k = 1 := by
  have := ρ.P.isAb.comm
  let w : Over.mk ((baseOver (Sp S.R)).hom ≫ f) ⟶ baseOver (Sp R) :=
    Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)
  let y : Fin (2 * g) → (baseOver (Sp S.R) ⟶ ρ.P.A) := fun i =>
    Over.homMk (hp.1.lift (f ≫ (u.pt i).left) (𝟙 _) (by rw [Category.assoc, Over.w]; simp)) (hp.1.lift_snd _ _ _)
  have hy : ∀ i, pushHom hp _ (y i) = preHom w (u.pt i) := fun i => Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  have hx : ∀ c : Ix g k, pushHom hp _ (linComb y fun i => (c i).val) = preHom w (u.lab c) := fun c => by
    rw [TObj.lab, ThetaPtUp.map_linComb, ThetaPtUp.map_linComb, funext hy]
  have key : ∀ i a, (ρ.pt a).left ≫ φ = f ≫ (u.pt i ^ (S.r * S.N)).left → y i ^ (S.r * S.N) = ρ.pt a := fun i a e => by
    apply pushPt_injective hp
    refine (map_pow (pushHom hp _) _ _).trans ?_
    rw [hy, ← map_pow]
    exact Over.OverMorphism.ext e.symm
  have hy' : ∀ i, ∃ a, y i ^ (S.r * S.N) = ρ.pt a := fun i => by
    rcases lt_or_ge (i : ℕ) g with hi | hi
    · exact ⟨_, key i _ (h ⟨i, by omega⟩ i ⟨i + g, by omega⟩ rfl rfl).1⟩
    · exact ⟨_, key i _ (h ⟨i - g, by omega⟩ ⟨i - g, by omega⟩ i rfl (by simp only; omega)).2⟩
  let Q : Submonoid (baseOver (Sp S.R) ⟶ ρ.P.A) :=
    { carrier := {z | ∃ a, z ^ (S.r * S.N) = ρ.pt a}
      mul_mem' := fun {z z'} ⟨a, ha⟩ ⟨a', ha'⟩ => ⟨a + a', by rw [mul_pow, ha, ha', ρ.pt_add]⟩
      one_mem' := ⟨0, by
        have e := ρ.pt_add 0 0
        rw [add_zero] at e
        rw [one_pow, mul_eq_left.1 e.symm]⟩ }
  have hQ : ∀ c : Ix g k, (linComb y fun i => (c i).val) ∈ Q := fun c =>
    Q.list_prod_mem fun z hz => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hz
      exact Q.pow_mem (hy' i) _
  choose a ha using hQ
  refine ⟨_, a, ha, fun c => congrArg (fun z => z.left) (hx c), fun c => pushPt_injective hp ?_⟩
  refine (map_pow (pushHom hp _) _ _).trans (Eq.trans ?_ (map_one (pushHom hp _)).symm)
  rw [hx, ← map_pow, ThetaPtUp.lab_pow, map_one]

end GlobalTheory.ThetaSysOfObj

namespace GlobalTheory

open ThetaSysOfObj in

theorem exists_big_thetaSys_with_action : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A), S.Big ∧ S.N = (n ^ k) ^ 2 ∧ Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω ∧ IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (t₀.PP.L.pull φ) ∧ (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) ∧ (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) ∧ (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) := by
  intro hL hL₂ E _ _ _ H g n hn ho
  obtain ⟨k, j₁, hk, hj₁, big⟩ := exists_big g n hn.two_le
  refine ⟨k, j₁ + 2 * k, fun j hj => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + k * 2 := ⟨j - k * 2, by omega⟩
  rw [pow_add, pow_mul]
  intro o Ω _ _ _ hb R J b u t₀ e v hR hΩ he hiso hth hfin
  have := u.ab.comm
  have : NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2) := ⟨by have := hn.pos; positivity⟩
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have ge := isGrpPullback_of_iso e.symm
  have lb : ∀ {Y : Scheme.{0}} (ψ : Y ⟶ u.A.left), LBIso (t₀.PP.L.pull (ψ ≫ e.inv.left)) (u.L.pull ψ) := fun ψ =>
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ (ψ ≫ e.inv.left) rfl) (chartPullSame u.L _ _ _ _ fun _ => by
      rw [Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.comp_id]) hiso
  have hS : ZH.HypS u.A u.L := SymBaseChange.hypS_baseChange _ _ t₀.G u.A _ _ t₀.PP.L u.L t₀.PP.isLB u.isLB
    (ge.congr rfl (Category.id_comp _).symm)
    ((lb (𝟙 _)).chartPull (chartPullId _) (chartPullUnpull u.L _ rfl)).symm
    ⟨t₀.act.act H.w0, t₀.act.act (H.bar H.w0), t₀.act.hom _, t₀.act.hom _,
      by rw [← t₀.act.add, HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t₀.act.one], t₀.prim, t₀.adj _⟩
  have hun : IsUnit (n : o) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    (((dvd_pow_self n (by omega : j ≠ 0)).trans (dvd_mul_right _ _)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  obtain ⟨lev, hlev⟩ := exists_level R u
  obtain ⟨S, ρ, h, φ, -, hN, hr, hg, hp, hlb, hpt⟩ :=
    T.exists_thetaSystem_of_polarised_level hL hL₂ o Ω R hR hΩ u.pol n k j b.ζ hn ho hk (by omega) hun hS lev
  rw [hlev] at hpt
  have := ρ.P.isAb.comm
  have hp' := (IsGrpPullback.comp hp ge).congr (Category.comp_id _) rfl
  have hlb' : LBIso ρ.P.L (t₀.PP.L.pull (φ ≫ e.inv.left)) :=
    LBIso.trans ρ.P.isLB (pull_isLB u.isLB _) (pull_isLB t₀.PP.isLB _) hlb (lb φ).symm
  obtain ⟨act, h₁, h₂, h₃⟩ := exists_act t₀ hp' ρ.P.isLB hlb'
  refine ⟨S, ρ, h, φ ≫ e.inv.left, act, big j (by omega) o Ω S hg hN hr, hN, ?_, hp', hlb', h₁, h₂, h₃⟩
  obtain ⟨x, a, hx, hx', hk'⟩ := exists_points u S ρ hg hp hpt
  let w : Over.mk (spMap S.R.val.toRingHom) ⟶ Out.baseOver (Sp S.R) := Over.homMk (spMap S.R.val.toRingHom) (by simp)
  have ef : spMap R.val.toRingHom ≫ 𝟙 _ =
      spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom :=
    (Category.comp_id _).trans (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)
      (CommRingCat.ofHom S.R.val.toRingHom))
  have Q := hasTh_baseChange hL₂ o g _ J b _ _ u R Ω R.val.toRingHom _ v hth
  rw [ef] at Q
  have Q' := (ThetaPtUp.isThetaPt_iff (P₀ := u.pol) (P := ρ.P) (T := Over.mk (spMap S.R.val.toRingHom)) hp hlb
    (x := fun i => w ≫ x i) (fun i => (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (hx' i).symm).trans (Category.assoc _ _ _).symm))
    (fun i => by rw [← MonObj.comp_pow, hk', MonObj.comp_one]) _).2 Q
  obtain ⟨c, hc, hv⟩ := exists_unit_generic hL hL₂ S ρ x a hx _ (by rw [hN, hr]) w rfl Q'
  exact finite_of_ratios hc (fun i => (hv i).elim fun m hm => ⟨_, hm⟩) hfin

end GlobalTheory

end
