import Mathlib
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyCoefficientFieldPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.DIV.Cons NumberField
open scoped PowerSeries Cardinal

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeModelCharts

abbrev SpecOf (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

abbrev specMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : SpecOf S ⟶ SpecOf R :=
  Spec.map (CommRingCat.ofHom f)

def genPt (R : Type) [CommRing R] [IsDomain R] : SpecOf R := (⊥ : PrimeSpectrum R)

def clPt (R : Type) [CommRing R] [IsLocalRing R] : SpecOf R := IsLocalRing.closedPoint R

structure Code : Type where

  val : ℝ

structure SmallField (p : ℕ) : Type where

  S : Set Code
  [fld : NontriviallyNormedField S]
  [ultra : IsUltrametricDist S]
  [ac : IsAlgClosed S]
  [cpl : CompleteSpace S]
  [ch0 : CharZero S]
  norm_p : ‖(p : S)‖ = (p : ℝ)⁻¹

def SmallField.toCF {p : ℕ} (F : SmallField p) : CF p :=
  @CF.mk p F.S F.fld F.ultra F.ac F.cpl F.ch0 F.norm_p

def OC {p : ℕ} (F : CF p) : ValuationSubring F.C := (NormedField.valuation (K := F.C)).valuationSubring

theorem mem_OC {p : ℕ} (F : CF p) (x : F.C) : x ∈ OC F ↔ ‖x‖ ≤ 1 := by
  rw [OC, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  rfl

def IsCp {p : ℕ} (F : CF p) : Prop := Dense {x : F.C | IsAlgebraic ℚ x}

def OC.map {p : ℕ} {F F' : CF p} (φ : F.C →+* F'.C) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : OC F →+* OC F' :=
  (φ.comp (OC F).subtype).codRestrict (OC F') fun x => by
    rw [mem_OC]
    exact (hφ x).trans_le ((mem_OC F x).1 x.2)

theorem exists_smallField {p : ℕ} (F : CF p) (h : #F.C ≤ 𝔠) :
    ∃ (F' : SmallField p) (e : F'.toCF.C ≃+* F.C), ∀ x, ‖e x‖ = ‖x‖ := by
  obtain ⟨ι⟩ : Nonempty (F.C ↪ ℝ) := by
    rw [← Cardinal.le_def, Cardinal.mk_real]; exact h
  let ι' : F.C → Code := fun x => ⟨ι x⟩
  have hι : Function.Injective ι' := fun x y hxy => ι.injective (congrArg Code.val hxy)
  let S : Set Code := Set.range ι'
  let e₀ : S ≃ F.C := (Equiv.ofInjective ι' hι).symm
  letI : Field S := e₀.field
  let e : S ≃+* F.C := e₀.ringEquiv
  letI nf : NormedField S := NormedField.induced S F.C (e : S →+* F.C) e.injective
  have hn : ∀ x : S, ‖x‖ = ‖e x‖ := fun _ => rfl
  letI nt : NontriviallyNormedField S :=
    { nf with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := F.C)
        exact ⟨e.symm x, by rw [hn, e.apply_symm_apply]; exact hx⟩ }
  have hiso : Isometry e := AddMonoidHomClass.isometry_of_norm e fun x => (hn x).symm
  haveI : IsUltrametricDist S :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hn, hn, hn, map_add]; exact IsUltrametricDist.norm_add_le_max _ _
  haveI : IsAlgClosed S := IsAlgClosed.of_ringEquiv F.C S e.symm
  haveI : CompleteSpace S := (IsometryEquiv.mk e.toEquiv hiso).completeSpace
  haveI : CharZero S := (e : S →+* F.C).charZero
  exact ⟨{ S := S, norm_p := by rw [hn, map_natCast, F.norm_p] }, e, fun x => (hn x).symm⟩

theorem mk_le_continuum_of_denseRange {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

theorem mk_padicComplex_le (p : ℕ) [Fact p.Prime] : #(PadicComplex p) ≤ 𝔠 := by
  have h1 : #ℚ_[p] ≤ 𝔠 := mk_le_continuum_of_denseRange _ (Padic.denseRange_ratCast p)
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have h2 : #(PadicAlgCl p) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans (max_le h1 Cardinal.aleph0_le_continuum)
  exact mk_le_continuum_of_denseRange (X := PadicComplex p) _
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) h2

theorem nonempty_smallField (p : ℕ) [Fact p.Prime] : Nonempty (SmallField p) :=
  (exists_smallField (Formalism.MainNotions.DIV.Inh.cfPadic p) (mk_padicComplex_le p)).nonempty

structure OLam (p : ℕ) [Fact p.Prime] where

  O : Type
  [cr : CommRing O]
  [dom : IsDomain O]
  [dvr : IsDiscreteValuationRing O]
  [alg : Algebra ℤ_[p] O]
  [fin : Module.Finite ℤ_[p] O]
  inj : Function.Injective (algebraMap ℤ_[p] O)

attribute [instance] OLam.cr OLam.dom OLam.dvr OLam.alg OLam.fin

def OLam.padic (p : ℕ) [Fact p.Prime] : OLam p where
  O := ℤ_[p]
  inj := fun _ _ h => h

def OLam.Large {p : ℕ} [Fact p.Prime] (B : OLam p) (E : Type) [Field E] [NumberField E] (M₀ : ℕ) : Prop :=
  3 ≤ M₀ ∧ Nat.Coprime M₀ p ∧ Nat.card (𝓞 E →+* B.O) = Module.finrank ℚ E ∧ ∃ ζ : B.O, IsPrimitiveRoot ζ M₀

variable {p : ℕ} [Fact p.Prime]

def genFib {B : OLam p} (M : ModelG B.O) : M.Z.Opens :=
  M.str ⁻¹ᵁ (PrimeSpectrum.basicOpen (p : B.O) : (SpecOf B.O).Opens)

structure Model (B : OLam p) extends ModelG B.O where

  U : Z.Opens
  nonempty : Nonempty Z
  normal : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)
  proper : IsProper str
  flat : Flat str
  semi : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G.X
  U_le : U ≤ genFib toModelG
  U_dense : (genFib toModelG : Set Z) ⊆ closure (U : Set Z)
  ab_U : IsAbSch (bchG U.ι G)

namespace Model

variable {B : OLam p} (M : Model B)

structure Pt : Type where

  F : SmallField p

  yt : SpecOf (OC F.toCF) ⟶ M.Z
  gen_mem : yt (genPt _) ∈ M.U

variable {M}

def Pt.fld (y : M.Pt) : CF p := y.F.toCF

def Pt.y (y : M.Pt) : SpecOf y.fld.C ⟶ M.Z := specMap (OC y.F.toCF).subtype ≫ y.yt

def Pt.red (y : M.Pt) : M.Z := y.yt (clPt _)

def Pt.G (y : M.Pt) : GrpSch (SpecOf (OC y.F.toCF)) := bchG y.yt M.G

def Pt.Good (y : M.Pt) : Prop := IsAbSch y.G

def Pt.Bad (y : M.Pt) : Prop := ¬ y.Good

end Model

structure DVRing (B : OLam p) where

  V : Type
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal V) V]

  j : B.O →+* V
  j_inj : Function.Injective j
  j_local : IsLocalHom j

attribute [instance] DVRing.cr DVRing.dom DVRing.dvr DVRing.cpl

structure DVRing.FinExt {B : OLam p} (V W : DVRing B) where

  i : V.V →+* W.V
  i_inj : Function.Injective i
  i_fin : i.Finite
  i_j : i.comp V.j = W.j

def DVRing.FinExt.refl {B : OLam p} (V : DVRing B) : V.FinExt V :=
  ⟨RingHom.id _, fun _ _ h => h, RingHom.Finite.id _, rfl⟩

def DVRing.padic (p : ℕ) [Fact p.Prime] : DVRing (OLam.padic p) where
  V := ℤ_[p]
  j := RingHom.id _
  j_inj := fun _ _ h => h
  j_local := inferInstanceAs (IsLocalHom (RingHom.id ℤ_[p]))

section Eval

open scoped PowerSeries.WithPiTopology

theorem exists_evalU (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (π : V) (hπ : π ∈ IsLocalRing.maximalIdeal V) :
    ∃ φ : V⟦X⟧ →+* V, (∀ a, φ (PowerSeries.C a) = a) ∧ φ PowerSeries.X = π := by
  letI : WithIdeal V := ⟨IsLocalRing.maximalIdeal V⟩
  have hI : IsAdic (IsLocalRing.maximalIdeal V) := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp inferInstance
  have ha : PowerSeries.HasEval π := WithIdeal.isTopologicallyNilpotent_of_mem hπ
  refine ⟨PowerSeries.eval₂Hom (φ := RingHom.id V) continuous_id ha, fun a => ?_, ?_⟩
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]; rfl
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

theorem evalU_unique (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (π : V) (hπ : π ∈ IsLocalRing.maximalIdeal V) (φ ψ : V⟦X⟧ →+* V)
    (hφ : ∀ a, φ (PowerSeries.C a) = a) (hφ' : φ PowerSeries.X = π)
    (hψ : ∀ a, ψ (PowerSeries.C a) = a) (hψ' : ψ PowerSeries.X = π) : φ = ψ := by
  have key : ∀ (n : ℕ) (f : V⟦X⟧), φ f - ψ f ∈ IsLocalRing.maximalIdeal V ^ n := by
    intro n
    induction n with
    | zero => intro f; simp
    | succ n ih =>
      intro f
      rw [PowerSeries.eq_X_mul_shift_add_const f]
      simp only [map_add, map_mul, hφ, hψ, hφ', hψ', add_sub_add_right_eq_sub, ← mul_sub]
      rw [pow_succ']
      exact Ideal.mul_mem_mul hπ (ih _)
  refine RingHom.ext fun f => sub_eq_zero.1 ?_
  refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal V) inferInstance _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n f

def evalU (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (π : V) (hπ : π ∈ IsLocalRing.maximalIdeal V) : V⟦X⟧ →+* V :=
  (exists_evalU V π hπ).choose

theorem evalU_spec (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (π : V) (hπ : π ∈ IsLocalRing.maximalIdeal V) :
    (∀ a, evalU V π hπ (PowerSeries.C a) = a) ∧ evalU V π hπ PowerSeries.X = π :=
  (exists_evalU V π hπ).choose_spec

end Eval

def DVRing.Unif {B : OLam p} (V : DVRing B) : Type := {π : V.V // Irreducible π}

theorem DVRing.Unif.mem {B : OLam p} {V : DVRing B} (π : V.Unif) : π.1 ∈ IsLocalRing.maximalIdeal V.V :=
  π.2.not_isUnit

def DVRing.Unif.sec {B : OLam p} {V : DVRing B} (π : V.Unif) : SpecOf V.V ⟶ SpecOf V.V⟦X⟧ :=
  specMap (evalU V.V π.1 π.mem)

namespace Model

variable {B : OLam p} (M : Model B)

structure DVPt (V : DVRing B) : Type where

  yt : SpecOf V.V ⟶ M.Z
  comm : yt ≫ M.str = specMap V.j
  gen_mem : yt (genPt _) ∈ M.U

structure Chart (V : DVRing B) : Type where

  χ : SpecOf V.V⟦X⟧ ⟶ M.Z
  comm : χ ≫ M.str = specMap ((PowerSeries.C (R := V.V)).comp V.j)

variable {M}

def DVPt.Good {V : DVRing B} (y : M.DVPt V) : Prop := IsAbSch (bchG y.yt M.G)

def DVPt.Bad {V : DVRing B} (y : M.DVPt V) : Prop := ¬ y.Good

def DVPt.red {V : DVRing B} (y : M.DVPt V) : M.Z := y.yt (clPt _)

def DVPt.ext {V W : DVRing B} (y : M.DVPt V) (e : V.FinExt W) : M.DVPt W where
  yt := specMap e.i ≫ y.yt
  comm := by
    rw [Category.assoc, y.comm, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e.i_j]
  gen_mem := by
    have h : specMap e.i (genPt W.V) = genPt V.V :=
      PrimeSpectrum.ext (Ideal.comap_bot_of_injective e.i e.i_inj)
    rw [Scheme.Hom.comp_apply, h]
    exact y.gen_mem

def Chart.At {V : DVRing B} (c : M.Chart V) (π : V.Unif) (y : M.DVPt V) : Prop := π.sec ≫ c.χ = y.yt

def Chart.InOpen {V : DVRing B} (c : M.Chart V) (π : V.Unif) : Prop :=
  ∀ q : PrimeSpectrum V.V⟦X⟧, PowerSeries.C π.1 * PowerSeries.X ∉ q.asIdeal → c.χ q ∈ M.U

def Chart.IsChartAt {V : DVRing B} (c : M.Chart V) (π : V.Unif) (y : M.DVPt V) : Prop :=
  c.At π y ∧ c.InOpen π

def Chart.G {V : DVRing B} (c : M.Chart V) : GrpSch (SpecOf V.V⟦X⟧) := bchG c.χ M.G

def Chart.AbExact {V : DVRing B} (c : M.Chart V) : Prop :=
  IsAbSch (bchG (Scheme.Opens.ι (X := SpecOf V.V⟦X⟧) (PrimeSpectrum.basicOpen PowerSeries.X)) c.G) ∧
    ∀ q : PrimeSpectrum V.V⟦X⟧, PowerSeries.X ∈ q.asIdeal → ¬ AbelianAt c.G q

def Chart.pbIdeal {V : DVRing B} (c : M.Chart V) (I : M.Z.IdealSheafData) : Ideal V.V⟦X⟧ :=
  ((I.comap c.χ).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of V.V⟦X⟧)).hom.hom

def Chart.PbPrincipal {V : DVRing B} (c : M.Chart V) (I : M.Z.IdealSheafData) : Prop :=
  (c.pbIdeal I).IsPrincipal

variable (M)

def OpenIsAbelianLocus : Prop := ∀ z : M.Z, z ∈ genFib M.toModelG → AbelianAt M.G z → z ∈ M.U

def HasCharts : Prop :=
  ∀ (V : DVRing B) (y : M.DVPt V), y.Bad →
    ∃ (W : DVRing B) (e : V.FinExt W) (π : W.Unif) (c : M.Chart W), c.IsChartAt π (y.ext e) ∧ c.AbExact

def AbelianAtGen : Prop := ∀ η : M.toModelG.Gen, M.toModelG.abAt η

end Model

theorem isAbSch_trivial (S : Scheme.{0}) : ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme (Grp.trivial (Over S)).X :=
  GlobalTheory.isAbelianScheme_powObj_of_isAbelianScheme _ (GlobalTheory.Diag.isAbelianScheme_unit S) 0

def Model.base (B : OLam p) : Model B where
  Z := SpecOf B.O
  str := 𝟙 _
  G := Grp.trivial _
  U := (𝟙 (SpecOf B.O) : _ ⟶ _) ⁻¹ᵁ (PrimeSpectrum.basicOpen (p : B.O) : (SpecOf B.O).Opens)
  nonempty := ⟨genPt _⟩
  normal := fun (z : PrimeSpectrum B.O) => by
    haveI : IsLocalization.AtPrime ((Spec.structureSheaf B.O).presheaf.stalk z) z.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk B.O z
    have h1 : IsDomain ((Spec.structureSheaf B.O).presheaf.stalk z) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors (M := z.asIdeal.primeCompl) _
        z.asIdeal.primeCompl_le_nonZeroDivisors
    have h2 : IsIntegrallyClosed ((Spec.structureSheaf B.O).presheaf.stalk z) :=
      isIntegrallyClosed_of_isLocalization (R := B.O) _ z.asIdeal.primeCompl
        z.asIdeal.primeCompl_le_nonZeroDivisors
    exact ⟨h1, h2⟩
  proper := inferInstance
  flat := inferInstance
  semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (isAbSch_trivial _)
  U_le := le_rfl
  U_dense := subset_closure
  ab_U := by
    have h := GlobalTheory.isAbelianScheme_pullback_obj
      (Scheme.Opens.ι ((𝟙 (SpecOf B.O) : _ ⟶ _) ⁻¹ᵁ (PrimeSpectrum.basicOpen (p : B.O) : (SpecOf B.O).Opens))) _
      (isAbSch_trivial (SpecOf B.O))
    exact ⟨h.comm, h.proper, h.smooth, h.geomConnected⟩

theorem OLam.p_ne_zero (B : OLam p) : (p : B.O) ≠ 0 := by
  rw [← map_natCast (algebraMap ℤ_[p] B.O)]
  exact (map_ne_zero_iff _ B.inj).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

def Model.basePt {B : OLam p} (V : DVRing B) : (Model.base B).DVPt V where
  yt := specMap V.j
  comm := Category.comp_id _
  gen_mem := fun h => B.p_ne_zero (V.j_inj (by
    have h' : V.j (p : B.O) ∈ (⊥ : Ideal V.V) := h
    rw [map_zero]; exact h'))

def Model.baseChart {B : OLam p} (V : DVRing B) : (Model.base B).Chart V where
  χ := specMap ((PowerSeries.C (R := V.V)).comp V.j)
  comm := Category.comp_id _

example {B : OLam p} (V : DVRing B) (π : V.Unif) : (Model.baseChart V).At π (Model.basePt V) := by
  change specMap _ ≫ specMap _ = specMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun a => (evalU_spec V.V π.1 π.mem).1 _

theorem nonempty_pt (p : ℕ) [Fact p.Prime] : Nonempty (Model.base (OLam.padic p)).Pt := by
  obtain ⟨F, e, he⟩ := exists_smallField (Formalism.MainNotions.DIV.Inh.cfPadic p) (mk_padicComplex_le p)
  let a : ℤ_[p] →+* PadicComplex p := (algebraMap ℚ_[p] (PadicComplex p)).comp PadicInt.Coe.ringHom
  have ha : ∀ x, ‖a x‖ ≤ 1 := fun x => by
    have : ‖a x‖ = ‖(x : ℚ_[p])‖ := norm_algebraMap' (PadicComplex p) (x : ℚ_[p])
    rw [this]; exact x.2
  let b : ℤ_[p] →+* F.toCF.C := (e.symm : (Formalism.MainNotions.DIV.Inh.cfPadic p).C →+* F.toCF.C).comp a
  have hb : ∀ x, b x ∈ OC F.toCF := fun x => by
    rw [mem_OC, ← he]
    exact (congrArg norm (e.apply_symm_apply (a x))).trans_le (ha x)
  refine ⟨⟨F, specMap (b.codRestrict (OC F.toCF) hb), fun h => ?_⟩⟩
  have h' : (b.codRestrict (OC F.toCF) hb) (p : ℤ_[p]) ∈ (⊥ : Ideal (OC F.toCF)) := h
  rw [map_natCast, Ideal.mem_bot] at h'
  exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.1 h')

def UniqueExtension (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (B : OLam p) (M : Model B) (A K : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] (j : B.O →+* A) (y : SpecOf K ⟶ M.Z),
    y ≫ M.str = specMap ((algebraMap A K).comp j) →
      ∃! yt : SpecOf A ⟶ M.Z, specMap (algebraMap A K) ≫ yt = y ∧ yt ≫ M.str = specMap j

def SmallFieldsSuffice (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (B : OLam p) (M : Model B) (F : CF p) (yt : SpecOf (OC F) ⟶ M.Z), yt (genPt _) ∈ M.U →
    ∃ (y : M.Pt) (φ : y.fld.C →+* F.C) (hφ : ∀ x, ‖φ x‖ = ‖x‖),
      yt = specMap (OC.map (F := y.F.toCF) φ hφ) ≫ y.yt

def GenericPointsExist (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (B : OLam p) (M : Model B) (η : M.toModelG.Gen),
    ∃ y : M.Pt, y.red = M.toModelG.gpt η ∧ ∀ z : M.Z, z ⤳ y.yt (genPt _) → z = y.yt (genPt _)

def ChartsGiveAbelianAtGen (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (B : OLam p) (M : Model B), M.HasCharts → M.AbelianAtGen

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeModelCharts

end
