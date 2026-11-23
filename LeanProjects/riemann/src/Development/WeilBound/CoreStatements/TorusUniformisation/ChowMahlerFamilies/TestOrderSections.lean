import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHoldsStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsIntegrallyClosedOfDenom
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestrictionStatement
import ReciprocityTheory.DualLattices.ExistsSmulMemOfMemSpan
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionFamilyIdempotent
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestOrderSections

open ReciprocityTheory.PGsh.L2

section Gen

variable {R : Type} [CommRing R] {C : Type} [Field C] {RC : Type} [CommRing RC] [Algebra RC C]

theorem span_push (φ : R →+* C) (hφ : ∀ r, ∃ s : RC, algebraMap RC C s = φ r) {X X' : Type} (u : X' → X)
    (S : Set (X → R)) (M : Submodule RC (X' → C)) (hS : ∀ g ∈ S, (fun x => φ (g (u x))) ∈ M)
    (g : X → R) (hg : g ∈ Submodule.span R S) : (fun x => φ (g (u x))) ∈ M := by
  induction hg using Submodule.span_induction with
  | mem g hg => exact hS g hg
  | zero =>
    have : (fun x => φ ((0 : X → R) (u x))) = 0 := by ext x; simp
    rw [this]; exact M.zero_mem
  | add a b _ _ ha hb =>
    have : (fun x => φ ((a + b) (u x))) = (fun x => φ (a (u x))) + fun x => φ (b (u x)) := by ext x; simp
    rw [this]; exact M.add_mem ha hb
  | smul r a _ ha =>
    obtain ⟨s, hs⟩ := hφ r
    have : (fun x => φ ((r • a) (u x))) = s • fun x => φ (a (u x)) := by
      ext x; simp [Algebra.smul_def, hs]
    rw [this]; exact M.smul_mem s ha

variable {N : Type} [AddCommGroup N]

def extSp (RC : Type) [CommRing RC] [Algebra RC C] (φ : R →+* C) (A : Subalgebra R (Multiplicative N → R)) :
    Submodule RC (N → C) :=
  Submodule.span RC {f | ∃ g ∈ A, f = fun x => φ (g (Multiplicative.ofAdd x))}

theorem mem_extSp (φ : R →+* C) {A : Subalgebra R (Multiplicative N → R)} {g : Multiplicative N → R} (hg : g ∈ A) :
    (fun x => φ (g (Multiplicative.ofAdd x))) ∈ extSp RC φ A :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem extSp_stable (φ : R →+* C) {A : Subalgebra R (Multiplicative N → R)} (α : N → N)
    (hα : ∀ g ∈ A, (fun t => g (Multiplicative.ofAdd (α (Multiplicative.toAdd t)))) ∈ A) :
    ∀ h ∈ extSp RC φ A, (fun x => h (α x)) ∈ extSp RC φ A := by
  intro h hh
  have : extSp RC φ A ≤ (extSp RC φ A).comap (LinearMap.funLeft RC C α) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact mem_extSp φ (hα g hg)
  exact this hh

theorem exists_hopf [Fintype N] [DecidableEq N] [IsDomain RC] [ValuationRing RC] [IsFractionRing RC C]
    (φ : R →+* C) (hinj : Function.Injective φ) (hφ : ∀ r, ∃ s : RC, algebraMap RC C s = φ r)
    {A : Subalgebra R (Multiplicative N → R)} (hA : IsHopfOrder A) :
    ∃ AA : HopfOrder (C := C) RC N, AA.carrier = extSp RC φ A := by
  refine ⟨⟨extSp RC φ A, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · refine SecondCohomologyLattice.isLat_of_fg _ ?_ ?_
    · have hfg : (Subalgebra.toSubmodule A).FG := Module.Finite.iff_fg.1 hA.finite
      obtain ⟨s, hs⟩ := hfg
      classical
      refine ⟨s.image fun g x => φ (g (Multiplicative.ofAdd x)), le_antisymm ?_ ?_⟩
      · refine Submodule.span_le.2 ?_
        intro f hf
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hf)
        refine mem_extSp φ ?_
        have : g ∈ Subalgebra.toSubmodule A := hs ▸ Submodule.subset_span hg
        exact this
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨g, hg, rfl⟩
        refine span_push φ hφ Multiplicative.ofAdd (s : Set _) _ (fun g hg => Submodule.subset_span ?_) g ?_
        · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨g, hg, rfl⟩)
        · rw [hs]; exact hg
    · obtain ⟨d, hd, hdA⟩ := hA.full
      have hd' : φ d ≠ 0 := fun h => hd (hinj (by rw [h, map_zero]))
      rw [eq_top_iff, ← (Pi.basisFun C N).span_eq, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have h1 := mem_extSp (RC := RC) φ (hdA (Pi.single (Multiplicative.ofAdd x) 1))
      have h2 := Submodule.smul_mem _ (φ d)⁻¹ (Submodule.subset_span (R := C) h1)
      have e : (Pi.basisFun C N) x = (φ d)⁻¹ • fun z : N => φ ((d • (Pi.single (Multiplicative.ofAdd x) 1 :
          Multiplicative N → R)) (Multiplicative.ofAdd z)) := by
        ext z
        by_cases hz : z = x
        · subst hz; simp [hd']
        · have : Multiplicative.ofAdd z ≠ Multiplicative.ofAdd x := fun h => hz (Multiplicative.ofAdd.injective h)
          simp [hz, this]
      rw [e]
      exact h2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩ x
    exact hφ _
  · have := mem_extSp (RC := RC) φ A.one_mem
    convert this using 1
    ext x; simp
  · intro f g hf hg
    have := Submodule.mul_mem_mul hf hg
    unfold extSp at this
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨a * b, A.mul_mem ha hb, ?_⟩
    ext x; simp
  · intro f hf
    have : extSp RC φ A ≤ (tensorSpan RC (extSp RC φ A)).comap (addPull RC N) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      refine span_push φ hφ (fun z : N × N => (Multiplicative.ofAdd z.1, Multiplicative.ofAdd z.2)) _
        (tensorSpan RC (extSp RC φ A)) ?_ _ (hA.comul g hg)
      rintro _ ⟨a, ha, b, hb, rfl⟩
      refine Submodule.subset_span ⟨_, mem_extSp φ ha, _, mem_extSp φ hb, ?_⟩
      ext z; simp
    exact this hf
  · exact extSp_stable φ (fun x => -x) hA.inv

end Gen

theorem span_eq_spanOver {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) {X : Type}
    (S : Set (X → C)) : (Submodule.span RC S).toAddSubgroup = spanOver RC S := by
  refine le_antisymm ?_ ?_
  · intro f hf
    have key : ∀ a ∈ RC, a • f ∈ spanOver RC S := by
      have hf' : f ∈ Submodule.span RC S := hf
      induction hf' using Submodule.span_induction with
      | mem g hg => exact fun a ha => AddSubgroup.subset_closure ⟨a, ha, g, hg, rfl⟩
      | zero => intro a _; rw [smul_zero]; exact zero_mem _
      | add u v hu hv h1 h2 => intro a ha; rw [smul_add]; exact add_mem (h1 hu a ha) (h2 hv a ha)
      | smul r u hu h1 =>
        intro a ha
        have : a • r • u = (a * (r : C)) • u := by rw [mul_smul]; rfl
        rw [this]
        exact h1 hu _ (RC.mul_mem ha r.2)
    simpa using key 1 RC.one_mem
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact Submodule.smul_mem _ (⟨a, ha⟩ : RC) (Submodule.subset_span he)

theorem sec_mul {A F : Type} [CommRing A] [Field F] (pq : A →+* F) (sc : F →+ A)
    (h1 : ∀ a, pq (sc a) = a) (h2 : ∀ u a, pq u = 0 → u * sc a = 0) (u : A) (x : F) :
    sc (pq u * x) = u * sc x := by
  have a1 := FunctionFamilyIdempotent.sec_eq pq sc h1 h2 (u * sc x)
  have a2 := FunctionFamilyIdempotent.sec_eq pq sc h1 h2 (sc x)
  rw [map_mul, h1] at a1
  rw [h1] at a2
  linear_combination a1 - u * a2

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F] {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω]
  {c' : ∀ k, J k}

theorem ordW_eq (P : ChartPack G O c') (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {C : Type} [Field C]
    [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) :
    (TestPt.testOrdW P sc RC).toAddSubgroup =
      spanOver RC (bcMap Ω C (Fin (D.p + D.q) → F) '' (funLat P sc : Set ((Fin (D.p + D.q) → F) → Ω))) := by
  unfold TestPt.testOrdW TestPt.testOrd
  rw [Submodule.map_span, span_eq_spanOver]
  refine congrArg (spanOver RC) (Set.Subset.antisymm ?_ ?_)
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨fun a => ((g (toN sc a) : CR O y c') : Ω), AddSubgroup.mem_map.2 ⟨g, hg, rfl⟩, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.1 hf
    exact ⟨fun x => algebraMap Ω C ((g (Multiplicative.ofAdd x) : CR O y c') : Ω), ⟨g, hg, rfl⟩, rfl⟩

open PositivityTheory.Xgn.FunctionFamilyIdempotent in
theorem bt_mul [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    [Finite (TorsT E (D.p + D.q) p)] (P : ChartPack G O c') (a : 𝓞 E) :
    ∀ f ∈ P.Γ₁.btOrder ⊤, (fun t => f (mulT _ p a t)) ∈ P.Γ₁.btOrder ⊤ := by
  haveI := 𝔐.t.act.hom a
  haveI := frac_epi (CR O y c')
  refine (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.1 (𝔐.t.act.act a) (mulT _ p a) ?_
  intro t
  obtain ⟨x, rfl⟩ := qmk_surj _ p t
  rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, mulT_qmk, G.t₁.lin, Over.comp_left, P.pts₁]
  simp only [Category.assoc]

theorem ord_mul [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    [Finite (TorsT E (D.p + D.q) p)] (P : ChartPack G O c') {C : Type} [Field C]
    [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) (u : 𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) :
    ∀ h ∈ TestPt.testOrd P RC,
      (fun x : TestPt.NAdd E (D.p + D.q) p => h (fun k => u * x k)) ∈ TestPt.testOrd P RC := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
  exact extSp_stable (RC := RC) ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω))
    (fun (x : TestPt.NAdd E (D.p + D.q) p) k => Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) a * x k) (bt_mul P a)

theorem ord_hopf [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')]
    [Fintype (TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (TestPt.NAdd E (D.p + D.q) p)]
    (P : ChartPack G O c') {C : Type} [Field C]
    [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) [ValuationRing RC] [IsFractionRing RC C]
    (hR : ∀ a ∈ CR O y c', algebraMap Ω C a ∈ RC) :
    ∃ AA : HopfOrder (C := C) RC (TestPt.NAdd E (D.p + D.q) p), AA.carrier = TestPt.testOrd P RC :=
  exists_hopf (RC := RC) ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω))
    ((algebraMap Ω C).injective.comp Subtype.val_injective) (fun r => ⟨⟨_, hR r r.2⟩, rfl⟩)
    (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁ 𝔐.t.semi.smooth).1

theorem ord_ret [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    [Finite (TorsT E (D.p + D.q) p)] (P : ChartPack G O c') {C : Type} [Field C]
    [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) {pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F}
    {sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})} (hsec : IsSec pq sc) :
    ∀ h ∈ TestPt.testOrd P RC,
      (fun x => h (TestPt.toNAdd sc (TestPt.fromNAdd pq x))) ∈ TestPt.testOrd P RC := by
  intro h hh
  have e : (fun x => h (TestPt.toNAdd sc (TestPt.fromNAdd pq x))) =
      fun x : TestPt.NAdd E (D.p + D.q) p => h (fun k => sc 1 * x k) :=
    funext fun x => congrArg h (funext fun k => FunctionFamilyIdempotent.sec_eq pq sc hsec.1 hsec.2 (x k))
  rw [e]
  exact ord_mul P RC (sc 1) h hh

theorem ordW_stable [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    [Finite (TorsT E (D.p + D.q) p)] (P : ChartPack G O c') {C : Type} [Field C]
    [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) {pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F}
    {sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})} (hsec : IsSec pq sc) :
    GlobalTheory.CompanionTheory.Ar.GR.FStable F (TestPt.testOrdW P sc RC) := by
  rintro a _ ⟨h, hh, rfl⟩
  refine ⟨_, ord_mul P RC (sc a) h hh, ?_⟩
  refine funext fun x => congrArg h (funext fun k => ?_)
  have := sec_mul pq sc hsec.1 hsec.2 (sc a) (x k)
  rw [hsec.1] at this
  exact this.symm

end Chart

end PositivityTheory.Xgn.TestOrderSections

open PositivityTheory.Xgn.TestOrderSections PositivityTheory.Xgn.FunctionFamilyIdempotent in
theorem PositivityTheory.Xgn.test_order_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ p _ hpS _ _ _ b _ φ _ A _ _ _ m _ hpm O _ _ _ _ _ _ _
    t₀ Sg _ e φ' F _ _ _ pq sc w σ hO hsec G c' hc' P i _ _ C _ _ _ _ RC hT χ _ _ _ _
  obtain ⟨hch, hno, hic, hfr, -⟩ := PositivityTheory.Xgn.torsion_packing_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV p hpS A m hpm O c' hc'
  obtain ⟨halg, ⟨v, hv, hvp⟩, -, hR⟩ := hT
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap Ω C).injective
  have hvI : v.Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv x).1 x.2, fun r hr => ⟨⟨r, (hv r).2 hr⟩, rfl⟩⟩
  haveI : ValuationRing RC := ValuationRing.of_integers v hvI
  haveI : IsFractionRing RC C := hvI.isFractionRing
  haveI := finite_tors (E := E) (D.p + D.q) (p_ne_zero pq sc hsec)
  obtain ⟨AA, hAA⟩ := ord_hopf P RC hR
  have hret := ord_ret P RC hsec
  rw [← hAA] at hret
  obtain ⟨⟨AW, hAW⟩, -⟩ := GlobalTheory.T.hopf_order_retract_restriction p C v RC hvI hvp _ AA _ (TestPt.toNAdd sc) (TestPt.fromNAdd pq)
    (fun z => funext fun k => hsec.1 (z k)) hret
  rw [hAA] at hAW
  have hAW' : AW.carrier = TestPt.testOrdW P sc RC := hAW
  refine ⟨AA, AW, hAA, hAW', ?_, hret, ?_⟩
  · rw [hAW']
    exact ordW_eq P sc RC
  · rw [hAW']
    exact ordW_stable P RC hsec
