import Mathlib
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.KerMtPin
import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.HermitianColumns.HermCols
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

def CongAt (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Prop :=
  ∀ a b, IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ *
    ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)

abbrev ratA (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {N : ℕ} :
    GL (Fin N) E →* GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))

def NearAt (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) : Prop :=
  CongAt P n (x⁻¹ * ratA F g)

theorem congAt_one (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) : CongAt (F := F) (N := N) P n 1 := by
  intro a b
  refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simp

theorem nearAt_self (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin N) E) : NearAt (F := F) P n (ratA F g) g := by
  unfold NearAt
  rw [inv_mul_cancel]
  exact congAt_one P n

theorem nearAt_rat_mul (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (γ g : GL (Fin N) E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : NearAt P n (ratA F γ * x) (γ * g) ↔ NearAt P n x g := by
  unfold NearAt
  rw [map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

end Cong

section Lat

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

def latCo (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (a : 𝓞 E)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) (Fin N → E) :=
  mvL co (compan (sp := sp) J a (latAd y Lb))

variable {sp : Spaces R F E}

theorem mvL_mul (g h : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) : mvL (g * h) Λ = mvL g (mvL h Λ) := by
  unfold mvL
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  show toLE (g * h) x = toLE g (toLE h x)
  rw [toLE_apply, toLE_apply, toLE_apply, Matrix.mulVec_mulVec, Units.val_mul]

theorem latCo_eq_latK (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (h : toLE co = stdCo (sp.cm.sig : E →+* E) J) (a : 𝓞 E)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latCo sp J co a y Lb = latK sp J a y Lb := by
  unfold latCo latK toStd mvL
  rw [h]

theorem latCo_rat (J : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) (hγ : γ ∈ UJ (sp.cm.sig : E →+* E) J) (a : 𝓞 E)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latCo sp J co a (ratA F γ * y) Lb = mvL (co * γ * co⁻¹) (latCo sp J co a y Lb) := by
  unfold latCo
  rw [latAd_rat, compan_mvL J a γ hγ, ← mvL_mul, ← mvL_mul, inv_mul_cancel_right]

theorem latCo_mul (J : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) (hγ : γ ∈ UJ (sp.cm.sig : E →+* E) J) (a : 𝓞 E)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latCo sp J (co * γ) a y Lb = latCo sp J co a (ratA F γ * y) Lb := by
  unfold latCo
  rw [latAd_rat, compan_mvL J a γ hγ, mvL_mul]

def toStdCo (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) : (Fin N → E) ≃ₗ[E] (Fin N → E) :=
  (toLE co).symm.trans (stdCo σ J)

theorem latK_eq_map (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (a : 𝓞 E)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latK sp J a y Lb = (latCo sp J co a y Lb).map ((toStdCo (sp.cm.sig : E →+* E) J co).toLinearMap.restrictScalars (𝓞 E)) := by
  unfold latCo latK toStd mvL
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  simp [toStdCo]

end Lat

section SeamS

open Formalism.L2.Ker Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

def seamP (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 D.host.E) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE) P

theorem mem_seamP (P : HeightOneSpectrum (𝓞 X.E)) (x : 𝓞 X.E) :
    RingOfIntegers.mapRingEquiv s.iE x ∈ (seamP s P).asIdeal ↔ x ∈ P.asIdeal := by
  simp [seamP, HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]

def seamGL {n : ℕ} : (Sp X.E n ≃ₗ[X.E] Sp X.E n) →* GL (Fin n) D.host.E :=
  (bc (s.iE : X.E →+* D.host.E)).comp
    ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := X.E)).symm.toMonoidHom.comp
      (LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E)).symm.toMonoidHom)

theorem seamGL_mulVec {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (x : Sp X.E n) :
    ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (x l)) = fun l => s.iE (g x l) := by
  funext l
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [h]
  have h2 := RingHom.map_mulVec (s.iE : X.E →+* D.host.E) (LinearMap.toMatrix' g.toLinearMap) x l
  rw [LinearMap.toMatrix'_mulVec] at h2
  exact h2.symm

def seamHom {a b : ℕ} (x : HomE D.host.E a b) : HomE X.E a b :=
  Matrix.toLin' ((LinearMap.toMatrix' x).map s.iE.symm)

theorem seamHom_apply {a b : ℕ} (x : HomE D.host.E a b) (w : Sp X.E a) (l : Fin b) :
    s.iE (seamHom s x w l) = x (fun k => s.iE (w k)) l := by
  have h := RingHom.map_mulVec (s.iE : X.E →+* D.host.E) ((LinearMap.toMatrix' x).map s.iE.symm) w l
  have h2 : ((LinearMap.toMatrix' x).map s.iE.symm).map (s.iE : X.E →+* D.host.E) = LinearMap.toMatrix' x := by
    ext p q
    simp
  rw [h2, LinearMap.toMatrix'_mulVec] at h
  exact h

end SeamS

section Levels

open Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def MidLev (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K) : Prop :=
  ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h,
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) ∧ z = chiInv Ch sel mu cst j P h r

theorem exists_midLev_iff (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) :
    (∃ z, MidLev Ch sel mu cst j P h g z) ↔ g ∈ prCat (Pr := Pr) cst.sharp j P.1 h :=
  ⟨fun ⟨_, r, hr, hg, _⟩ => ⟨r, hr, hg⟩, fun ⟨r, hr, hg⟩ => ⟨_, r, hr, hg, rfl⟩⟩

open Classical in

def SameCoset {n : ℕ} (P : rowSG Pr sel mu) (y y' : Sp X.E n) : Prop :=
  ∀ l, IntAt P.1 (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ * (y - y') l)

open Classical in

def topDep (P : rowSG Pr sel mu) : ℕ := if P.1 ∈ Pr.vGs then 1 else 2 * cst.M

open Classical in

def rowLevTop (Pr : Primes X) (R : Ranks) (sharp : Bool) (n : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) :
    Subgroup (Sp X.E ((n - 1) + 0) ≃ₗ[X.E] Sp X.E ((n - 1) + 0)) :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.JGsym P (qOf P) R.k R.rS R.r R.t (n - 1) 0 else LocE.JG P (qOf P) R.k R.r R.t (n - 1) 0)
  else LocE.JQ P (qOf P) R.r (n - 1) 0

open Classical in

def rowChrTop (sharp : Bool) (j n : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : HomE X.E ((n - 1) + 0) ((n - 1) + 0)) : X.K :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.lamGBS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t j (n - 1) 0 h
      else LocE.lamGB (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t j (n - 1) 0 h)
  else LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P) R.r (n - 1) h

def TopLev (j : ℕ) (P : rowSG Pr sel mu) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K) : Prop :=
  ∃ g' ∈ rowLevTop Pr R cst.sharp (R.N j) P.1,
    prXpG X.E (R.N j) ∘ₗ g.toLinearMap = g'.toLinearMap ∘ₗ prXpG X.E (R.N j) ∧
    atNL X.E (R.N j) (R.N j - 1) ∘ₗ g.toLinearMap = atNL X.E (R.N j) (R.N j - 1) ∧
    z = rowChrTop Ch mu cst.sharp j (R.N j) P.1 g'.toLinearMap

example (j : ℕ) (P : rowSG Pr sel mu) : ∃ z, TopLev Ch sel mu cst j P 1 z :=
  ⟨_, 1, Subgroup.one_mem _, rfl, rfl, rfl⟩

example (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : ∃ z, MidLev Ch sel mu cst j P h 1 z :=
  (exists_midLev_iff Ch sel mu cst j P h 1).2 (Subgroup.one_mem _)

end Levels

section Moved

open Formalism.L2.Forms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {S : StepLevel F E σ J T f bad} (k : basePts S) (κ : S.U)

theorem mul_toMoved {x x₁ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (e : x₁.1 = x.1 * κ.1) :
    (x₁ * basePtU k).1 = (x * basePtU k).1 * (toMoved k κ).1 := by
  show x₁.1 * k.1 = x.1 * k.1 * (k.1⁻¹ * κ.1 * k.1)
  rw [e]
  group

theorem det_toMoved : Matrix.GeneralLinearGroup.det (toMoved k κ).1 = Matrix.GeneralLinearGroup.det κ.1 := by
  show Matrix.GeneralLinearGroup.det (k.1⁻¹ * κ.1 * k.1) = _
  rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]

theorem prV_mul_basePt {x x₁ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (v : HeightOneSpectrum (𝓞 F))
    (e : bc (prV (E := E) v) x₁.1 = bc (prV (E := E) v) x.1) :
    bc (prV (E := E) v) (x₁ * basePtU k).1 = bc (prV (E := E) v) (x * basePtU k).1 := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, e]

end Moved

section Charts

open Formalism.L2.Forms Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 1000000 in

structure StepCharts (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (i : ℕ) (hi : i ≤ D.R.m) where

  T : ℕ

  bad : Set (HeightOneSpectrum (𝓞 D.host.F))

  eY : C.Y i ≃ Fr D i hi

  Ch : Type

  chOf : C.cls i → Ch

  lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)

  K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)

namespace StepCharts

variable {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}

def ofStepIn {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {G : GAtP p}
    (S : StepIn M i hi G) : StepCharts C i hi where
  T := S.T
  bad := S.bad
  eY := S.eY
  Ch := S.Ch
  chOf := S.chOf
  lat := S.lat
  K := S.K

def ofOne {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (eY : C.Y i ≃ Fr D i hi)
    {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)} (K : LevelChart D T bad i hi (C.stab i) lat) : StepCharts C i hi where
  T := T
  bad := bad
  eY := eY
  Ch := Unit
  chOf := fun _ => ()
  lat := lat
  K := fun _ =>
    { lev := K.lev
      y := fun c => K.y c.1
      y_bij := K.y_bij.comp ⟨Subtype.val_injective, fun c => ⟨⟨c, rfl⟩, rfl⟩⟩
      y_lat := fun c => K.y_lat c.1
      stabI := fun c => K.stabI c.1
      stabI_inj := fun c => K.stabI_inj c.1
      stabI_range := fun c => K.stabI_range c.1 }

variable (St : StepCharts C i hi)

def y (c : C.cls i) : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := (St.K (St.chOf c)).y ⟨c, rfl⟩

theorem y_eq {β : St.Ch} (c : {c // St.chOf c = β}) : (St.K β).y c = St.y c.1 := by
  obtain ⟨c, rfl⟩ := c
  rfl

abbrev Base : Type := ∀ β : St.Ch, basePts (St.K β).lev

def move (k : St.Base) : StepCharts C i hi := { St with K := fun β => moveChart (St.K β) (k β) }

theorem move_y (k : St.Base) (c : C.cls i) : (St.move k).y c = St.y c * basePtU (k (St.chOf c)) := rfl

end StepCharts

end Charts

section LevTie

open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
  (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)
  (Rel : SB → (Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) → X.K → Prop)

def InFrame (P : SB) (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) : Prop :=
  NearAt (seamP s P.1) (dep P) ((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P)) (seamGL s g)

def LocLe : Prop :=
  ∀ (P : SB) (v : HeightOneSpectrum (𝓞 D.host.F)), IsOver v (seamP s P.1) →
    ∀ κ ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), bc (prV (E := D.host.E) v) κ ∈ lev.Uloc v →
      ∃ g z, Rel P g z ∧ InFrame s fb dep P κ g

def LocGe : Prop :=
  ∀ (P : SB) (v : HeightOneSpectrum (𝓞 D.host.F)), IsOver v (seamP s P.1) →
    ∀ κ ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (∃ g z, Rel P g z ∧ InFrame s fb dep P κ g) → bc (prV (E := D.host.E) v) κ ∈ lev.Uloc v

def ChiIs : Prop :=
  ∀ (κ : lev.U) (g : SB → Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (z : SB → X.K),
    (∀ P, Rel P (g P) (z P) ∧ InFrame s fb dep P κ.1 (g P)) → ((lev.chi κ : ℂˣ) : ℂ) * s.σ₀ (∏ P, z P) = 1

def FunMoved {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal)
    (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (d : Deco X.E (D.R.N i) ST SG) : Prop :=
  ∀ w ∈ d.N, ∀ z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)),
    (z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l)) → d.f P w = ι (lev.fT v h z)

example (P : SB) : InFrame s fb dep P 1 1 := by
  unfold InFrame NearAt
  simpa using congAt_one (F := D.host.F) (N := D.R.N i) (seamP s P.1) (dep P)

end LevTie

section Comparison₂

open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsAdIso {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) : Prop :=
  (∀ x : E, ι (x ⊗ₜ[F] 1) = algebraMap E _ x) ∧
    ∀ y, y ∈ RInt F E ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι y P) ≤ 1

theorem exists_isAdIso (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E, IsAdIso ι := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E
  exact ⟨ι, h1, h2⟩

theorem IsAdIso.val_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E} (hι : IsAdIso ι) {P : HeightOneSpectrum (𝓞 E)} {z : AfE F E}
    (h : IntAtA (F := F) P z) : Valued.v (ι z P) ≤ 1 := by
  obtain ⟨s, hs, hm⟩ := h
  have h1 := (hι.2 _).1 hm P
  have h2 : ι (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) := hι.1 _
  rw [map_mul, h2] at h1
  have h3 : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E s)) P) = 1 := by
    show Valued.v (((algebraMap (𝓞 E) E s : E)) : P.adicCompletion E) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 hs
  have h4 : (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E s) * ι z) P =
      (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E s)) P * ι z P := rfl
  rwa [h4, map_mul, h3, one_mul] at h1

example {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (h : CongAt (F := F) P n (-1 : GL (Fin 1) (AfE F E))) : P.valuation E ((((qOf P : ℕ) : E) ^ n)⁻¹ * (-2)) ≤ 1 := by
  obtain ⟨ι, hι⟩ := exists_isAdIso F E
  have h1 := hι.val_le (h 0 0)
  have h2 : iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (((-1 : GL (Fin 1) (AfE F E)) : Matrix (Fin 1) (Fin 1) (AfE F E)) - 1) 0 0 =
      iA F E ((((qOf P : ℕ) : E) ^ n)⁻¹ * (-2)) := by
    rw [map_mul, map_neg, map_ofNat]
    congr 1
    simp
    norm_num
  rw [h2, show ι (iA F E ((((qOf P : ℕ) : E) ^ n)⁻¹ * (-2))) = algebraMap E _ ((((qOf P : ℕ) : E) ^ n)⁻¹ * (-2)) from hι.1 _] at h1
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact h1

section W

variable {D : D7} {X : Fields} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
  {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))

def IsChainTopW (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ)
    (pt : ∀ i, i ≤ m2 + 1 → C.cls i → ChPt (R := D.R) sel mu v i) (ix : ∀ i, i ≤ m2 → C.cls i → L.β i)
    (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (pT : C.cls (m2 + 1 + 1) → ChPt (R := D.R) sel mu v (m2 + 1 + 1)) : Prop :=
  (∀ i (hi : i ≤ m2 + 1) c, r.N i c = (pt i hi c).deco.1.N) ∧
  (∀ c', yb c' ∈ ybSet sel mu cst (pt (m2 + 1) le_rfl c').deco.1.N) ∧
  (∀ i (hi : i < m2) c c' x, r.Xi i c c' x =
    σ (XiEntry Ch sel mu cst L i (ix i hi.le c) (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c') x)) ∧
  (∀ c c' x, r.Xi m2 c c' x =
    σ (XiCpl1 Ch sel mu cst L m2 (ix m2 le_rfl c) (pt m2 (Nat.le_succ _) c) (pt (m2 + 1) le_rfl c') (yb c') x)) ∧
  r.TopPinAt Ch sel mu cst σ v m2 (pt (m2 + 1) le_rfl) yb pT ∧
  (∀ i, i ≤ m2 + 1 → ∀ c, r.pin i c) ∧ ∀ c', r.pin (m2 + 1 + 1) c' ↔ ∃ d, OverRow sel mu v d (pT c')

theorem isChainTop_iff (r : KerRead C X) (σ : X.K →+* ℂ) (v : Pr.Word) (m2 : ℕ) :
    r.IsChainTop Ch sel mu cst L σ v m2 ↔ r.SS = Sall sel mu v ∧ r.lev = levC sel mu cst v ∧
      ∃ pt ix yb pT, IsChainTopW Ch sel mu cst L r σ v m2 pt ix yb pT := Iff.rfl

end W

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)

include μ in

theorem m_eq : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm

include μ in

theorem cpl_lt : t.m2 + 1 < D.R.m := by have := m_eq t μ; omega

include μ in

theorem top_le : t.m2 + 1 + 1 ≤ D.R.m := by have := m_eq t μ; omega

abbrev SB : Finset (HeightOneSpectrum (𝓞 t.X.E)) := rowSG t.Pr t.sel (t.tup μ)

def UnderSB (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop := ∃ P ∈ SB t μ, IsOver v (seamP t.seam P)

def ssRec : Finset (HeightOneSpectrum (𝓞 D.host.E)) :=
  (t.rd u μ).SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv t.seam.iE)).toEmbedding

theorem mem_ssRec (P : HeightOneSpectrum (𝓞 t.X.E)) : seamP t.seam P ∈ ssRec t u μ ↔ P ∈ (t.rd u μ).SS :=
  Finset.mem_map' _

abbrev ChainCharts (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type 1 := ∀ i (hi : i ≤ D.R.m), StepCharts (D.chTw u μ) i hi

variable (St : ChainCharts D u μ)

structure AdData where

  crd : ∀ i, i ≤ D.R.m → GL (Fin (D.R.N i)) D.host.E

  iA : AfE t.X.F t.X.E ≃+* AfE D.host.F D.host.E

  q : (AfE t.X.F t.X.E)ˣ →* D.Dt

  pt : ∀ i, i ≤ D.R.m → (D.chTw u μ).cls i → ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i

  yb : (D.chTw u μ).cls (t.m2 + 1) → Set (Sp t.X.E (D.R.N (t.m2 + 1)))

  ib : ∀ i (hi : i < D.R.m), (St i hi.le).Ch → (t.idx μ).β i

  fb : ∀ i (hi : i ≤ D.R.m), (St i hi).Ch → SB t μ → GL (Fin (D.R.N i)) D.host.E

  y0 : (St (t.m2 + 1) (cpl_lt t μ).le).Ch → SB t μ → Sp t.X.E (D.R.N (t.m2 + 1))

variable {t u μ St} (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

def AdData.midRel (i : ℕ) (hi : i < D.R.m) (β : (St i hi.le).Ch) (P : SB t μ)
    (g : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i)) (z : t.X.K) : Prop :=
  MidLev t.Ch t.sel (t.tup μ) (t.cst μ) i P ((t.idx μ).h i (A.ib i hi β) P) g z

def AdData.cplRel (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (P : SB t μ)
    (g : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (z : t.X.K) : Prop :=
  A.midRel (t.m2 + 1) (cpl_lt t μ) β P g z ∧ SameCoset t.sel (t.tup μ) (t.cst μ) P (g (A.y0 β P)) (A.y0 β P)

def AdData.mov (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  ratA D.host.F (A.crd i hi) * ((St i hi).y c).1

structure AdPins : Prop where

  fields : t.X.AbelianUnramifiedExtensionConditions

  sel : IsSel t.X t.sel

  avoid : (∀ k, t.Pr.g k ∈ t.S) ∧ t.Pr.T (t.word u) ∈ t.S

  ch : t.ChTie

  mu0 : ∀ j, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ (fun τ => (D.hc (t.seam.iT τ)).e j) j (t.glob.mu0 j)

  psi : ∀ P x, IsIntegral ℤ ((t.cst μ).psi P x)

  iA_rat : ∀ x : t.X.E, A.iA (x ⊗ₜ[t.X.F] 1) = t.seam.iE x ⊗ₜ[D.host.F] 1

  iA_int : ∀ y, A.iA y ∈ RInt D.host.F D.host.E ↔ y ∈ RInt t.X.F t.X.E

  q_read : t.IsUnitNormOneQuotient A.q

  q_dt : ∀ (x : (AfE t.X.F t.X.E)ˣ) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det y.1 = h90 (sigD D) (Units.map A.iA.toRingHom.toMonoidHom x) → A.q x = dtU y

  muTil : ∀ ι : AfE t.X.F t.X.E ≃+* FiniteAdeleRing (𝓞 t.X.E) t.X.E, IsAdIso ι →
    ∀ (j : Fin D.R.m) (b : Neutral.B1.Ideles t.X.E) (x : (AfE t.X.F t.X.E)ˣ), Formalism.L2.Host.IsFinIdele b →
      ι (x : AfE t.X.F t.X.E) = (b : AdeleRing (𝓞 t.X.E) t.X.E).2 → D.muTil (j.1 + 1) (A.q x) = (t.glob.mu0 j).1 b

  ref : μ = D.what₂.mu0 → t.tup μ = 1 ∧ (t.O u μ).mt = D.muTil

  tw : t.MtTwAt A.q (· = μ)

  crd_orth : ∀ i (hi : i ≤ D.R.m), cT (sigD D : D.host.E →+* D.host.E) (A.crd i hi).1 * (A.crd i hi).1 = gramN D i hi

  frm : ∀ i (hi : i ≤ D.R.m) y τ, (t.O u μ).frm i y τ = atInf (embT D) (A.crd i hi).1 τ * ((St i hi).eY y).1 τ

structure AdTie : Prop where

  chain : IsChainTopW t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) (t.rd u μ) t.seam.σ₀ (t.word u) t.m2
    (fun i hi => A.pt i (hi.trans (cpl_lt t μ).le))
    (fun i hi c => A.ib i ((Nat.lt_succ_of_le hi).trans (cpl_lt t μ)) ((St i _).chOf c)) A.yb (A.pt _ (top_le t μ))

  T_eq : ∀ i hi, (St i hi).T = (D.mem u).A.T

  bad : ∀ i hi, ∀ v ∈ (St i hi).bad, UnderSB t μ v

  lat : ∀ i hi c, t.seam.lat ((t.rd u μ).N i c) =
    latCo D.sp (gramN D i hi) (A.crd i hi) a ((St i hi).y c).1 ((St i hi).K ((St i hi).chOf c)).lev.Lb

  frame : ∀ i hi c (P : SB t μ), NearAt (seamP t.seam P.1) ((t.cst μ).D P)
    (A.mov i hi c * ratA D.host.F (A.fb i hi ((St i hi).chOf c) P)) (seamGL t.seam (frsF t.sel (t.tup μ) (A.pt i hi c) P))

  fnl : ∀ i hi (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
    IsOver v (seamP t.seam P.1) → ∃ ι : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal,
      ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1

  coset : ∀ c, ∀ y ∈ A.yb c, ∀ P : SB t μ, SameCoset t.sel (t.tup μ) (t.cst μ) P
    ((frsF t.sel (t.tup μ) (A.pt _ (cpl_lt t μ).le c) P).symm y) (A.y0 ((St _ (cpl_lt t μ).le).chOf c) P)

  levMid : ∀ i (hi : i < D.R.m), i ≤ t.m2 → ∀ β,
    LocLe t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β) ∧
    LocGe t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β) ∧
    ChiIs t.seam ((St i hi.le).K β).lev (A.fb i hi.le β) (t.cst μ).D (A.midRel i hi β)

  levCpl : ∀ β,
    LocLe t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β) ∧
    LocGe t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β) ∧
    ChiIs t.seam ((St _ (cpl_lt t μ).le).K β).lev (A.fb _ _ β) (t.cst μ).D (A.cplRel β)

  levTop : ∀ β,
    LocLe t.seam ((St _ (top_le t μ)).K β).lev (A.fb _ _ β) (topDep t.sel (t.tup μ) (t.cst μ))
      (TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1)) ∧
    ChiIs t.seam ((St _ (top_le t μ)).K β).lev (A.fb _ _ β) (topDep t.sel (t.tup μ) (t.cst μ))
      (TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1))

  dt : ∀ i hi c (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det ((St i hi).y c).1 → (t.O u μ).dt i c = dtU y

  aa : t.amb.AAUnit (Sall t.sel (t.tup μ) (t.word u))

variable {A dtU a}

theorem AdTie.isChainTop (H : AdTie A dtU a) :
    (t.rd u μ).IsChainTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.seam.σ₀ (t.word u) t.m2 := by
  have h := t.rd_chain u μ
  obtain ⟨h1, h2, -⟩ := h
  exact (isChainTop_iff _ _ _ _ _ _ _ _ _).2 ⟨h1, h2, ⟨_, _, _, _, H.chain⟩⟩

theorem AdTie.N_eq (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    (t.rd u μ).N i c = (A.pt i hi c).deco.1.N := by
  rcases Nat.lt_or_ge i (t.m2 + 1 + 1) with h | h
  · exact H.chain.1 i (by omega) c
  · obtain rfl : i = t.m2 + 1 + 1 := by have := m_eq t μ; omega
    exact H.chain.2.2.2.2.1.1 c

theorem AdTie.latK_eq (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    latK D.sp (gramN D i hi) a ((St i hi).y c).1 ((St i hi).K ((St i hi).chOf c)).lev.Lb =
      (t.seam.lat ((t.rd u μ).N i c)).map
        ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).toLinearMap.restrictScalars (𝓞 D.host.E)) := by
  rw [H.lat i hi c]
  exact latK_eq_map _ _ _ _ _

variable (St) in

abbrev AdDatum : Type :=
  ∀ i (hi : i + 1 ≤ D.R.m), (St i (Nat.le_of_succ_le hi)).Ch → (St (i + 1) hi).Ch →
    UPts (sigD D) (gramN D i (Nat.le_of_succ_le hi)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
    UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → HomE D.host.E (D.R.N i) (D.R.N (i + 1)) → ℂ

variable (A dtU a)

structure AdLawAt (XiAd : AdDatum St) (muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ) : Prop where

  read : ∀ i hi c c' z, XiAd i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') ((St i _).y c) ((St (i + 1) hi).y c') z =
    (t.rd u μ).Xi i c c' (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))

  rat : ∀ i hi β β' x x' x₁ x₁', ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)),
    ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), x₁.1 = ratA D.host.F γ * x.1 → x₁'.1 = ratA D.host.F γ' * x'.1 →
    ∀ z, XiAd i hi β β' x₁ x₁' z = XiAd i hi β β' x x' (inFr
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)

  lev : ∀ i hi β β' x x' x₁ x₁' (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 → ∀ z,
    muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i _).K β).lev.chi κ : ℂˣ) : ℂ) * XiAd i hi β β' x₁ x₁' z =
      muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * XiAd i hi β β' x x' z

  away : ∀ i hi β β' x x' x₁ x₁',
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧
      bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1) → XiAd i hi β β' x₁ x₁' = XiAd i hi β β' x x'

  loc : ∀ i hi β β' x x', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev
    (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
    (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb) (XiAd i hi β β' x x')

  supp : ∀ i hi β β' x x' z, XiAd i hi β β' x x' z ≠ 0 → z ∈ divLat (t.rd u μ).lev (homAt (ssRec t u μ)
    (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
    (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb))

  int : ∀ i hi β β' x x' z, IntOff (t.O u μ).S (XiAd i hi β β' x x' z)

  mu_read : ∀ i < D.R.m, ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm,
    muT (i + 1) (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ)

  mu_cls : ∀ i < D.R.m, ∀ k hk c, muT (i + 1) (Matrix.GeneralLinearGroup.det ((St k hk).y c).1) =
    (((t.O u μ).mt (i + 1) ((t.O u μ).dt k c) : ℂˣ) : ℂ)

  mu_mul : ∀ i < D.R.m, muT (i + 1) 1 = 1 ∧ ∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), muT (i + 1) (x * y) = muT (i + 1) x * muT (i + 1) y

  mu_alg : ∀ i < D.R.m, ∀ x ∈ U1 (sigD D), muT (i + 1) x ∈ TaylorLogMetric.Qbar

  mu_unr : ∀ i < D.R.m, ∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E →
    (∀ v, UnderSB t μ v → prV (E := D.host.E) v (x : AfE D.host.F D.host.E) = 1) → muT (i + 1) x = 1

  mu_rat : ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧
    ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 →
      muT (i + 1) (ratId D.host.F D.host.E z) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

def AdLaw : Prop := ∃ XiAd muT, AdLawAt A dtU a XiAd muT

variable {A dtU a}

theorem AdLawAt.mu_ne {XiAd : AdDatum St} {muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ} (H : AdLawAt A dtU a XiAd muT) {i : ℕ} (hi : i < D.R.m)
    {x : (AfE D.host.F D.host.E)ˣ} (hx : x ∈ U1 (sigD D)) : muT (i + 1) x ≠ 0 := by
  intro h0
  have h := (H.mu_mul i hi).2 x hx x⁻¹ (Subgroup.inv_mem _ hx)
  rw [mul_inv_cancel, (H.mu_mul i hi).1, h0, zero_mul] at h
  exact one_ne_zero h

variable (St) in

abbrev ChainBase : Type := ∀ i hi, (St i hi).Base

variable (St) in

def moveCharts (k : ChainBase St) : ChainCharts D u μ := fun i hi => (St i hi).move (k i hi)

def AdData.unmove {k : ChainBase St} (B : AdData t u μ (moveCharts St k)) : AdData t u μ St :=
  ⟨B.crd, B.iA, B.q, B.pt, B.yb, B.ib, B.fb, B.y0⟩

theorem AdPins.unmove_iff {k : ChainBase St} (B : AdData t u μ (moveCharts St k)) : AdPins B.unmove dtU ↔ AdPins B dtU :=
  ⟨fun h => { h with }, fun h => { h with }⟩

def AdDatum.unmove {k : ChainBase St} (Xi : AdDatum (moveCharts St k)) : AdDatum St := fun i hi β β' x x' =>
  Xi i hi β β' (x * basePtU (k i _ β)) (x' * basePtU (k (i + 1) hi β'))

variable (A dtU a)

structure AdLawAtB (k : ChainBase St) (XiAd : AdDatum St) (muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ) : Prop where

  read : ∀ i hi c c' z, XiAd i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') ((St i _).y c) ((St (i + 1) hi).y c') z =
    (t.rd u μ).Xi i c c' (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))

  rat : ∀ i hi β β' x x' x₁ x₁', ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)),
    ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), x₁.1 = ratA D.host.F γ * x.1 → x₁'.1 = ratA D.host.F γ' * x'.1 →
    ∀ z, XiAd i hi β β' x₁ x₁' z = XiAd i hi β β' x x' (inFr
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)

  lev : ∀ i hi β β' x x' x₁ x₁' (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 → ∀ z,
    muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i _).K β).lev.chi κ : ℂˣ) : ℂ) * XiAd i hi β β' x₁ x₁' z =
      muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * XiAd i hi β β' x x' z

  away : ∀ i hi β β' x x' x₁ x₁',
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧
      bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1) → XiAd i hi β β' x₁ x₁' = XiAd i hi β β' x x'

  loc : ∀ i hi β β' x x', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev
    (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
    (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb) (XiAd i hi β β' x x')

  supp : ∀ i hi β β' x x' z, XiAd i hi β β' x x' z ≠ 0 → z ∈ divLat (t.rd u μ).lev (homAt (ssRec t u μ)
    (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i _).K β).lev.Lb)
    (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb))

  int : ∀ i hi β β' x x' z, IntOff (t.O u μ).S (XiAd i hi β β' x x' z)

  mu_read : ∀ i < D.R.m, ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm,
    muT (i + 1) (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ)

  mu_cls : ∀ i < D.R.m, ∀ j hj c, muT (i + 1) (Matrix.GeneralLinearGroup.det (((St j hj).y c).1 * (k j hj ((St j hj).chOf c)).1)) =
    (((t.O u μ).mt (i + 1) ((t.O u μ).dt j c) : ℂˣ) : ℂ)

  mu_mul : ∀ i < D.R.m, muT (i + 1) 1 = 1 ∧ ∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), muT (i + 1) (x * y) = muT (i + 1) x * muT (i + 1) y

  mu_alg : ∀ i < D.R.m, ∀ x ∈ U1 (sigD D), muT (i + 1) x ∈ TaylorLogMetric.Qbar

  mu_unr : ∀ i < D.R.m, ∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E →
    (∀ v, UnderSB t μ v → prV (E := D.host.E) v (x : AfE D.host.F D.host.E) = 1) → muT (i + 1) x = 1

  mu_rat : ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧
    ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 →
      muT (i + 1) (ratId D.host.F D.host.E z) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

def AdLawB (k : ChainBase St) : Prop := ∃ XiAd muT, AdLawAtB A dtU a k XiAd muT

variable {A dtU a}

theorem adLawAtB_one_iff {XiAd : AdDatum St} {muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ} :
    AdLawAtB A dtU a (fun _ _ _ => 1) XiAd muT ↔ AdLawAt A dtU a XiAd muT :=
  ⟨fun h => { h with mu_cls := fun i hi j hj c => by simpa using h.mu_cls i hi j hj c },
    fun h => { h with mu_cls := fun i hi j hj c => by simpa using h.mu_cls i hi j hj c }⟩

theorem latK_basePt {i : ℕ} {hi : i ≤ D.R.m} {β : (St i hi).Ch} (k : basePts ((St i hi).K β).lev)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    latK D.sp (gramN D i hi) a (x * k.1) ((St i hi).K β).lev.Lb = latK D.sp (gramN D i hi) a x ((St i hi).K β).lev.Lb := by
  unfold latK
  rw [latAd_basePt]

set_option maxHeartbeats 1000000 in

theorem AdLawAt.unmove {k : ChainBase St} {B : AdData t u μ (moveCharts St k)} {Xi : AdDatum (moveCharts St k)}
    {muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ} (H : AdLawAt B dtU a Xi muT) : AdLawAtB B.unmove dtU a k Xi.unmove muT where
  read := H.read
  rat i hi β β' x x' x₁ x₁' γ hγ γ' hγ' e e' := H.rat i hi β β' _ _ _ _ γ hγ γ' hγ'
    ((congrArg (· * (k i _ β).1) e).trans (mul_assoc _ _ _)) ((congrArg (· * (k (i + 1) hi β').1) e').trans (mul_assoc _ _ _))
  lev i hi β β' x x' x₁ x₁' κ κ' e e' z := by
    have h := H.lev i hi β β' (x * basePtU (k i _ β)) (x' * basePtU (k (i + 1) hi β')) (x₁ * basePtU (k i _ β)) (x₁' * basePtU (k (i + 1) hi β'))
      (toMoved (k i _ β) κ) (toMoved (k (i + 1) hi β') κ') (mul_toMoved _ _ e) (mul_toMoved _ _ e') z
    rw [← det_toMoved (k i _ β) κ, ← det_toMoved (k (i + 1) hi β') κ', ← chi_toMoved (k i _ β) κ, ← chi_toMoved (k (i + 1) hi β') κ']
    exact h
  away i hi β β' x x' x₁ x₁' h := H.away i hi β β' _ _ _ _ fun v hv =>
    ⟨prV_mul_basePt _ v (h v hv).1, prV_mul_basePt _ v (h v hv).2⟩
  loc i hi β β' x x' := by
    rw [← latK_basePt (k i _ β), ← latK_basePt (k (i + 1) hi β')]
    exact H.loc i hi β β' (x * basePtU (k i _ β)) (x' * basePtU (k (i + 1) hi β'))
  supp i hi β β' x x' := by
    rw [← latK_basePt (k i _ β), ← latK_basePt (k (i + 1) hi β')]
    exact H.supp i hi β β' (x * basePtU (k i _ β)) (x' * basePtU (k (i + 1) hi β'))
  int i hi β β' x x' := H.int i hi β β' _ _
  mu_read := H.mu_read
  mu_cls := H.mu_cls
  mu_mul := H.mu_mul
  mu_alg := H.mu_alg
  mu_unr := H.mu_unr
  mu_rat := H.mu_rat

theorem AdLaw.unmove {k : ChainBase St} {B : AdData t u μ (moveCharts St k)} (H : AdLaw B dtU a) : AdLawB B.unmove dtU a k :=
  let ⟨_, _, h⟩ := H
  ⟨_, _, h.unmove⟩

example {k : ChainBase St} {B : AdData t u μ (moveCharts St k)} (H : AdTie B dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i)
    (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm)
    (h : Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det (((St i hi).y c).1 * (k i hi ((St i hi).chOf c)).1)) :
    (t.O u μ).dt i c = dtU y := H.dt i hi c y h

end Comparison₂

open Formalism.MainNotions in

def AdLawOfTie : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl Kc Y cX) (t : Formalism.L2.Ker.KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ) (A : AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a → AdLaw A dtU a

end GlobalTheory.TwU

end
