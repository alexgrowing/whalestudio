import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinWeilO

open GlobalTheory.SplitScalar GlobalTheory.FinWeil

variable {D : D7}

def finSub (S T : HSp D) : Submodule (AE D) (WO S T) where
  carrier := {u | u.map (infPart D) = 0}
  add_mem' {x y} hx hy := by
    funext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [RingHom.map_add, h1, h2, add_zero]
  zero_mem' := by
    funext i j
    exact (infPart D).map_zero
  smul_mem' a x hx := by
    funext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (a * x i j) = 0
    rw [RingHom.map_mul, h1, mul_zero]

def XF (S T : HSp D) : Type := finSub S T

instance (S T : HSp D) : AddCommGroup (XF S T) := inferInstanceAs (AddCommGroup (finSub S T))

instance (S T : HSp D) : Module (AE D) (XF S T) := inferInstanceAs (Module (AE D) (finSub S T))

@[coe] def XF.val {S T : HSp D} (x : XF S T) : WO S T := Subtype.val x

instance (S T : HSp D) : CoeOut (XF S T) (WO S T) := ⟨XF.val⟩

def XF.mk {S T : HSp D} (u : WO S T) (hu : u.map (infPart D) = 0) : XF S T := (⟨u, hu⟩ : finSub S T)

theorem XF.fin {S T : HSp D} (x : XF S T) : (x : WO S T).map (infPart D) = 0 := Subtype.property x

theorem XF.ext {S T : HSp D} {x y : XF S T} (h : (x : WO S T) = y) : x = y := Subtype.ext h

theorem XF.coe_mk {S T : HSp D} (u : WO S T) (hu : u.map (infPart D) = 0) : (XF.mk u hu : WO S T) = u := rfl

theorem XF.coe_add {S T : HSp D} (x y : XF S T) : ((x + y : XF S T) : WO S T) = x + y := rfl

theorem XF.coe_sub {S T : HSp D} (x y : XF S T) : ((x - y : XF S T) : WO S T) = x - y := rfl

theorem XF.coe_nsmul {S T : HSp D} (n : ℕ) (x : XF S T) : ((n • x : XF S T) : WO S T) = n • (x : WO S T) := rfl

theorem XF.coe_zero {S T : HSp D} : ((0 : XF S T) : WO S T) = 0 := rfl

def XF.incl (S T : HSp D) : XF S T →+ WO S T := AddMonoidHom.mk' XF.val XF.coe_add

def intA (D : D7) : 𝓞 D.host.E →+* AE D := (incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem intA_apply (r : 𝓞 D.host.E) : intA D r = incA D (r : D.host.E) := rfl

theorem cA_intA (r : 𝓞 D.host.E) : cA D (intA D r) = intA D (sgO D r) := by
  rw [intA_apply, intA_apply, GlobalTheory.DualPairCheck.cA_incA, coe_sgO, GlobalTheory.SplitIdem.star_eq_conj]

theorem finPart_intA (r : 𝓞 D.host.E) : finPart D (intA D r) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => by rw [map_one]; exact one_mem _, r, rfl⟩

instance modXF (S T : HSp D) : Module (𝓞 D.host.E) (XF S T) := Module.compHom _ (intA D)

variable {S T : HSp D}

theorem smul_def (r : 𝓞 D.host.E) (x : XF S T) : r • x = intA D r • x := rfl

theorem coe_smul (r : 𝓞 D.host.E) (x : XF S T) : ((r • x : XF S T) : WO S T) = intA D r • (x : WO S T) := rfl

def mulF (S T : HSp D) (a : AE D) : XF S T →ₗ[𝓞 D.host.E] XF S T where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' r x := by rw [RingHom.id_apply, smul_def, smul_def, smul_comm]

theorem mulF_apply (a : AE D) (x : XF S T) : mulF S T a x = a • x := rfl

theorem coe_mulF (a : AE D) (x : XF S T) : (mulF S T a x : WO S T) = a • (x : WO S T) := rfl

theorem actO_smul (g : GA D S) (h : GA D T) (a : AE D) (x : WO S T) :
    actO S T g h (a • x) = a • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem mt_mul (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := rfl

theorem mt_one (V : HSp D) : mt V 1 = 1 := rfl

theorem mem_finSub_iff {u : WO S T} : u ∈ finSub S T ↔ realIdem D • u = 0 := by
  constructor
  · exact fun h => Matrix.ext fun i j => realIdem_mul_of_fin (congrFun (congrFun h i) j)
  · intro h
    funext i j
    have h1 := congrArg (infPart D) (congrFun (congrFun h i) j)
    rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, infPart_realIdem, one_mul] at h1
    exact h1.trans (infPart D).map_zero

theorem actO_mem_finSub (g : GA D S) (h : GA D T) {u : WO S T} (hu : u ∈ finSub S T) :
    actO S T g h u ∈ finSub S T := by
  rw [mem_finSub_iff] at hu ⊢
  rw [← actO_smul, hu, actO, Matrix.mul_zero, Matrix.zero_mul]

def rhoF (S T : HSp D) : GA D S × GA D T →* Module.End (𝓞 D.host.E) (XF S T) where
  toFun p :=
    { toFun := fun x => XF.mk (actO S T p.1 p.2 x) (actO_mem_finSub _ _ x.fin)
      map_add' := fun x y => XF.ext (actO_add _ _ _ _)
      map_smul' := fun r x => XF.ext (actO_smul _ _ _ _) }
  map_one' := LinearMap.ext fun x => XF.ext (by
    show actO S T 1 1 x = x
    rw [actO, inv_one, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one])
  map_mul' p q := LinearMap.ext fun x => XF.ext (by
    show actO S T (p.1 * q.1) (p.2 * q.2) x = actO S T p.1 p.2 (actO S T q.1 q.2 x)
    simp only [actO, _root_.mul_inv_rev, mt_mul, Matrix.mul_assoc])

theorem coe_rhoF (p : GA D S × GA D T) (x : XF S T) : (rhoF S T p x : WO S T) = actO S T p.1 p.2 x := rfl

theorem smul_mul_mul {A : Type} [CommRing A] {m n : ℕ} {a : A} {g k : Matrix (Fin n) (Fin n) A}
    {h : Matrix (Fin m) (Fin m) A} (h1 : g * k = 1) (hg : a • g = a • 1) (hh : a • h = a • 1)
    (u : Matrix (Fin m) (Fin n) A) : a • (h * u * k) = a • u := by
  have h2 : a • k = a • 1 := by
    rw [← h1, ← Matrix.smul_mul, hg, Matrix.smul_mul, Matrix.one_mul]
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, hh, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, h2, Matrix.mul_smul, Matrix.mul_one]

theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 :=
  (mt_mul V g g⁻¹).symm.trans ((congrArg (mt V) (mul_inv_cancel g)).trans (mt_one V))

theorem smul_actO {a : AE D} {g : GA D S} {h : GA D T}
    (hg : a • mt S g = a • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))
    (hh : a • mt T h = a • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)))
    (u : WO S T) : a • actO S T g h u = a • u :=
  smul_mul_mul (mt_mul_inv S g) hg hh u

def latF (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (XF S T) where
  carrier := {x | (x : WO S T) ∈ latO S T LS LT fun _ => True}
  add_mem' hx hy := (latO S T LS LT fun _ => True).add_mem hx hy
  zero_mem' := (latO S T LS LT fun _ => True).zero_mem
  smul_mem' r _ hx := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ _ (finPart_intA r) _ hx

theorem mem_latF {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {x : XF S T} :
    x ∈ latF S T LS LT ↔ (x : WO S T) ∈ latO S T LS LT fun _ => True := Iff.rfl

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := GlobalTheory.WeilVacMove.isTheta_add
  zero_mem' := GlobalTheory.WeilVacMove.isTheta_zero
  smul_mem' c _ hf := GlobalTheory.WeilVacMove.isTheta_smul c hf

variable {ψ : AddChar (AF D.host.F) ℂ}

def gamF (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x y : XF S T) : ℂ := ψ (symplO S T x y)

def phase (ψ : AddChar (AF D.host.F) ℂ) (w : 𝓞 D.host.E) (x : XF S T) : ℂ :=
  ψ (-symplOH S T (intA D w • (x : WO S T)) x)

theorem phase_ne_zero (w : 𝓞 D.host.E) (x : XF S T) : phase ψ w x ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ (-symplOH S T (intA D w • (x : WO S T)) x) (symplOH S T (intA D w • (x : WO S T)) x)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, show ψ (-symplOH S T (intA D w • (x : WO S T)) x) = 0 from h,
    zero_mul] at this
  exact one_ne_zero this

def opF (hψ : IsCharAF D.host.F ψ) (S T : HSp D) (w : 𝓞 D.host.E) (x : XF S T) :
    thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T :=
  phase ψ w x • (heisL ψ S T x).restrict fun _ hf => GlobalTheory.FinTranslate.isTheta_heisO_fin hψ x.fin hf

theorem coe_opF (hψ : IsCharAF D.host.F ψ) (w : 𝓞 D.host.E) (x : XF S T) (f : thetaSub ψ S T) :
    (opF hψ S T w x f : WO S T → ℂ) = phase ψ w x • heisO ψ S T x f := rfl

theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, symplO_smul]

theorem symplO_self (x : WO S T) : symplO S T x x = 0 := by
  have h := symplOH_add_self S T x x
  nth_rewrite 1 [symplOH_skew] at h
  rw [neg_add_cancel] at h
  exact h.symm

theorem isHeis_opF (hψ : IsCharAF D.host.F ψ) (S T : HSp D) {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) :
    IsHeis (sgO D) w (gamF ψ S T) (opF hψ S T w) where
  sg_sg r := by
    apply Subtype.ext
    show ((sgO D (sgO D r) : 𝓞 D.host.E) : D.host.E) = (r : D.host.E)
    rw [coe_sgO, coe_sgO, ← GlobalTheory.SplitIdem.star_eq_conj, ← GlobalTheory.SplitIdem.star_eq_conj, star_star]
  w_add := hw
  add_left x y z := by
    rw [gamF, gamF, gamF, XF.coe_add, GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul]
  add_right x y z := by
    rw [gamF, gamF, gamF, XF.coe_add, GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul]
  alt x := by rw [gamF, symplO_self, AddChar.map_zero_eq_one]
  adj r x y := by rw [gamF, gamF, coe_smul, coe_smul, symplO_smul, cA_intA]
  zero v := by
    apply Subtype.ext
    rw [coe_opF, phase, XF.coe_zero, heisO_zero, symplOH, symplO_zero_right, mul_zero, neg_zero,
      AddChar.map_zero_eq_one, one_smul]
  comp x y v := by
    apply Subtype.ext
    rw [Submodule.coe_smul, coe_opF, coe_opF, coe_opF, heisO_smul, heisO_heisO, smul_smul, smul_smul, smul_smul,
      XF.coe_add, phase, phase, phase, gamF, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, coe_smul, XF.coe_add]
    congr 2
    have h1 : intA D w • (x : WO S T) + cA D (intA D w) • (x : WO S T) = x := by
      rw [← add_smul, cA_intA, ← RingHom.map_add, hw, RingHom.map_one, one_smul]
    have h2 := congrArg (fun z => symplOH S T z y) h1
    simp only [symplOH_add_left] at h2
    have h3 := symplOH_smul (intA D w) (y : WO S T) x
    rw [symplOH_skew S T (cA D (intA D w) • (x : WO S T)) y] at h3
    rw [smul_add, symplOH_add_left, symplOH_add_right, symplOH_add_right, ← symplOH_add_self]
    linear_combination h3 - h2

theorem selfDual_latF {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ (latO S T LS LT fun _ => True) ↔
      ∀ u' ∈ (latO S T LS LT fun _ => True), ψ (symplO S T u u') = 1)) :
    SelfDual (gamF ψ S T) (latF S T LS LT) := fun x =>
  (hd x x.fin).trans ⟨fun h a ha => h a ha, fun h a ha => h (XF.mk a (latO_fin ha)) ha⟩

theorem exists_w (D : D7) : ∃ w : 𝓞 D.host.E, w + sgO D w = 1 := by
  obtain ⟨b, hb⟩ := GlobalTheory.SemiChar.exists_int_add_star D
  refine ⟨b, Subtype.ext ?_⟩
  show (b : D.host.E) + ((sgO D b : 𝓞 D.host.E) : D.host.E) = 1
  rw [coe_sgO, ← GlobalTheory.SplitIdem.star_eq_conj, hb]

end GlobalTheory.FinWeilO

end
