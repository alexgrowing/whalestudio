import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemMaximalIdealBall

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht

def AbOfTrivSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p)
    (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P), p.Prime →
    Subsingleton A.Ylat → P.yt (closedPoint ↥(intO ↥C.S)) ∈ abLocus Y.t.G

def TrivOfAbSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p)
    (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P), p.Prime →
    P.yt (closedPoint ↥(intO ↥C.S)) ∈ abLocus Y.t.G → Subsingleton A.Ylat

def StalkSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p),
    p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (η : Z.Gen), ∃ _ : IsDomain (Z.X.presheaf.stalk η.1),
      IsDiscreteValuationRing (Z.X.presheaf.stalk η.1) ∧ CharZero (Z.X.presheaf.stalk η.1) ∧
      Countable (Z.X.presheaf.stalk η.1) ∧ (p : Z.X.presheaf.stalk η.1) ∈ maximalIdeal (Z.X.presheaf.stalk η.1) ∧
      ∀ q : Spec (Z.X.presheaf.stalk η.1), q.asIdeal = ⊥ → Z.X.fromSpecStalk η.1 q ∈ Z.opn

def FieldSt : Prop :=
  ∀ (p : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] [Countable R],
    p.Prime → (p : R) ∈ maximalIdeal R → ∃ (C : SCF p) (f : R →+* ↥(intO ↥C.S)) (K : Subfield ↥C.S),
      Function.Injective f ∧ IsLocalHom f ∧
      K = (Subfield.closure (Set.range fun a => ((f a : ↥(intO ↥C.S)) : ↥C.S))).topologicalClosure ∧
      IsDiscreteValuationRing ↥(intO ↥K) ∧ Dense {x : ↥C.S | IsAlgebraic ↥K x}

def ExtendSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p),
    (∀ (i : Idx H p) (k : Type) [Field k] (x : Sp k ⟶ (Y i).X), Set.range x ⊆ Set.range (Y i).j →
      ∃ (f : i.c.F →+* k) (y : Sp k ⟶ (Xo i.l).XF i.c), y ≫ pullback.snd _ _ = spMap f ∧ y ≫ (Y i).j = x) ∧
    (∀ (Z : Mdl Y i₀) (C : SCF p) (z : Sp ↥(intO ↥C.S) ⟶ Z.X),
      Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn → ∃ y : PtAt Z C, y.z = z) ∧
    ∀ (Z : Mdl Y i₀) (C : SCF p) (w : Sp ↥C.S ⟶ Z.X) (alg : Z.i.c.V W →+* ↥(intO ↥C.S)), Set.range w ⊆ Z.opn →
      w ≫ Z.s = spMap ((intO ↥C.S).subtype.comp alg) → ∃ y : PtAt Z C, y.gen = w

def EmbSt : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (C : SCF p) (f : ↥F →+* ↥C.S),
    p.Prime → (p : ℂ) ∈ W.nonunits → FiniteDimensional ℚ ↥F → (∀ x : ↥F, (x : ℂ) ∈ W → ‖f x‖ ≤ 1) →
    ∃ ι : ↥(algebraicClosure ℚ ℂ) →+* ↥C.S, (∀ (x : ↥F) (h : (x : ℂ) ∈ algebraicClosure ℚ ℂ), ι ⟨x, h⟩ = f x) ∧
      ∀ x : ↥(algebraicClosure ℚ ℂ), (x : ℂ) ∈ W → ‖ι x‖ ≤ 1

def RootsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : TateIso Dw k Q act e)
    (z : ℕ → kˣ), 1 ≤ Dw.p + Dw.q → (∀ n, 0 < n → IsPrimitiveRoot (z n) n) →
    (∀ n m, 0 < n → 0 < m → z (n * m) ^ m = z n) → z l.A = I.ζ l.A →
    ∃ I' : TateIso Dw k Q act e, (∀ n, 0 < n → I'.ζ n = z n) ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a

def TowerSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W),
    p.Prime → (p : ℂ) ∈ W.nonunits → 1 ≤ Dw.p + Dw.q → ∀ (C : SCF p) (i₁ : Idx H p) (P₁ : PointsOfFlagModel.PtC (Y i₁) C),
    ∃ P : ∀ i : Idx H p, PointsOfFlagModel.PtC (Y i) C, P i₁ = P₁ ∧
      ∀ (i i' : Idx H p) (τ : (Y i').X ⟶ (Y i).X) (mu : SABMap (Y i').t (Y i).t τ), i.l.Dvd i'.l → IsTrans i i' τ mu →
        (P i').yt ≫ τ = (P i).yt

def CocycleSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W)
    (i₁ i₂ i₃ : Idx H p) (τ : (Y i₂).X ⟶ (Y i₁).X) (mu : SABMap (Y i₂).t (Y i₁).t τ) (τ' : (Y i₃).X ⟶ (Y i₂).X)
    (mu' : SABMap (Y i₃).t (Y i₂).t τ') (τ'' : (Y i₃).X ⟶ (Y i₁).X) (mu'' : SABMap (Y i₃).t (Y i₁).t τ''),
    i₁.l.Dvd i₂.l → i₂.l.Dvd i₃.l → IsTrans i₁ i₂ τ mu → IsTrans i₂ i₃ τ' mu' → IsTrans i₁ i₃ τ'' mu'' →
    (Y i₃).m.φ ≫ mu'.φ ≫ mu.φ = (Y i₃).m.φ ≫ mu''.φ

def FrameMoveSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H)
    (c : Coeff l) (c' : Coeff l') (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (g : X' ⟶ X) (m : SABMap t' t g)
    (R : Type) [CommRing R] (f : c.F →+* R) (f' : c'.F →+* R) (x : Sp R ⟶ X'),
    (∀ τ a, f' (embK c' τ a) = f (embK c τ a)) →
    (∀ u' : Vecs Dw t' R, IsFrame t' f' x u' → IsFrame (Dw := Dw) t f (x ≫ g) (fun τ i => u' τ i ≫ m.φ)) ∧
    ∀ u : Vecs Dw t R, IsFrame t f (x ≫ g) u → ∃ u' : Vecs Dw t' R, IsFrame t' f' x u' ∧ ∀ τ i, u' τ i ≫ m.φ = u τ i

def FrameBaseSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R R' : Type) [CommRing R] [CommRing R'] (f : c.F →+* R) (x : Sp R ⟶ X)
    (φ : R →+* R') (u : Vecs Dw t R), IsFrame t f x u → IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ)

def FlagBaseSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p)
    (Z : Mdl Y i₀) (k : Type) [Field k] (w : Sp k ⟶ Z.X),
    (Set.range w ⊆ Z.opn → ∃ u, Z.FlagAt w u) ∧
    ∀ (k' : Type) [Field k'] (φ : k →+* k') (u : Vecs Dw (Y Z.i).t k), Z.FlagAt w u → Z.FlagAt (spMap φ ≫ w) (u.bc φ)

def FamSt : Prop :=
  ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (Z : ct.Mdl) (C : SCF p)
    (y : PtAt Z C) (K : Subfield ↥C.S) (w : Sp ↥K ⟶ Z.X), spMap K.subtype ≫ w = y.gen →
    ∃ fam : Fam ct.Y (idx0 ct) C, fam.pt Z = y ∧ ∃ w' : Sp ↥K ⟶ ct.YY.X, spMap K.subtype ≫ w' = (fam.pt ct.YY).gen

theorem evAt_fromSpecStalk {X : Scheme.{0}} (x : X) {B : Type} [CommRing B] (f : X.presheaf.stalk x →+* B) {U : X.Opens}
    (hU : x ∈ U) (h : ⊤ ≤ (spMap f ≫ X.fromSpecStalk x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    evAt (spMap f ≫ X.fromSpecStalk x) h s = f ((X.presheaf.germ U x hU).hom s) := by
  have h0 : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun q _ =>
    ((specializes_closedPoint (q : PrimeSpectrum _)).map (X.fromSpecStalk x).continuous).mem_open U.2
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hU)
  have e1 : (X.fromSpecStalk x).appLE U ⊤ h0 = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  have e2 := Scheme.Hom.appLE_comp_appLE (spMap f) (X.fromSpecStalk x) U ⊤ ⊤ h0 le_rfl
  have e3 : (spMap f).appLE ⊤ ⊤ le_rfl = (spMap f).appTop := (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (spMap f ≫ X.fromSpecStalk x).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      X.presheaf.germ U x hU ≫ CommRingCat.ofHom f := by
    rw [← e2, e1, e3, Category.assoc, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact congrArg (_ ≫ ·) ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv_hom_id_assoc _)
  exact congrArg (fun φ => φ.hom s) e4

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem base_ext {C : Type} [NormedField C] [IsUltrametricDist C] (i : Idx H p) (x x' : Sp ↥(intO C) ⟶ (Y i).X)
    (h : spMap (intO C).subtype ≫ x = spMap (intO C).subtype ≫ x') : x = x' := by
  have := projProper _ _ _ (Y i).proj
  have : (Y i).X.IsSeparated := ⟨by rw [← terminal.comp_from (Y i).s]; infer_instance⟩
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    exact ((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem abP_red_iff {Z₁ Z₂ : Mdl Y i₀} {C : SCF p} (y₁ : PtAt Z₁ C) (y₂ : PtAt Z₂ C) (h : NatImg Z₁ Z₂ y₁.gen y₂.gen) :
    Z₁.abP y₁.red ↔ Z₂.abP y₂.red := by
  obtain ⟨τ, mu, u, -, h₁, -⟩ := h
  have e : y₂.z ≫ Z₂.π = y₁.z ≫ Z₁.π ≫ τ := base_ext Z₂.i _ _ (by simpa [PtAt.gen] using h₁)
  have e' : Z₂.π y₂.red = τ (Z₁.π y₁.red) := congrArg (fun f => f (closedPoint ↥(intO ↥C.S))) e
  rw [Mdl.abP, Mdl.abP, e']
  exact (abLocus_pullback abLocusOne (Y Z₂.i).t.semi mu.cart.1 _).symm

theorem exists_isTrans (hN : N2 Y) (i i' : Idx H p) (hl : i.l.Dvd i'.l) (hc : i.c.F ≤ i'.c.F) :
    ∃ mu, IsTrans i i' (hN.2.choose i i' hl hc) mu := by
  let b : i.c.V W →+* i'.c.V W :=
    ((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i'.c.V W) fun x => x.2
  have hb : IsIncl b := fun _ => rfl
  obtain ⟨π', mu, r, h⟩ := hN.2.choose_spec.1 i i' hl hc b hb
  exact ⟨mu, b, π', r, hb, h⟩

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} {ct : At S κ p}

theorem corr_base (Z : ct.Mdl) : Corr Z ct.Xm := by
  have h : ct.Xm.i = idx0 ct := ct.B.lvl none
  refine ⟨h ▸ Z.dvd, ?_, fun σ => by rw [ct.B.ty none σ]; exact Finset.empty_subset _⟩
  rw [h]; exact Z.le

theorem abP_redK_iff (Z : ct.Mdl) (y : DVP ct) : ct.abP (redK Z y) ↔ ct.abP (redK ct.Xm y) :=
  abP_red_iff _ _ (y.fam.compat Z ct.Xm (corr_base Z))

theorem finrank_eq_zero_iff {Z : ct.Mdl} (x : ct.Pt Z) :
    Module.finrank (𝓞 D.host.E) (ct.Ylat x) = 0 ↔ Subsingleton (ct.Ylat x) := by
  have : Module.Finite (𝓞 D.host.E) (ct.Ylat x) := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.IsTorsionFree (𝓞 D.host.E) (ct.Ylat x) := by
    refine ⟨fun r hr a b hab => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    obtain ⟨s, hs⟩ : r ∣ ((Algebra.norm ℤ r : ℤ) : 𝓞 D.host.E) := by
      have := Ideal.absNorm_mem (Ideal.span {r})
      rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at this
      rcases Int.natAbs_eq (Algebra.norm ℤ r) with h | h <;> rw [h] <;> simpa using this
    have hn : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.2 hr0
    have h2 : r • a = r • b := hab
    have h3 : Algebra.norm ℤ r • a = Algebra.norm ℤ r • b := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 D.host.E), ← Int.cast_smul_eq_zsmul (𝓞 D.host.E), hs, mul_comm, mul_smul,
        mul_smul, h2]
    exact smul_right_injective _ hn h3
  exact Module.finrank_zero_iff

theorem ptK_good (hg : GoodIff ct) (Z : ct.Mdl) (y : DVP ct) : Subsingleton (ct.Ylat (ptK Z y)) ↔ dvRho y = 0 :=
  (hg Z (ptK Z y)).trans ((abP_redK_iff Z y).trans ((hg _ (ptK ct.Xm y)).symm.trans (finrank_eq_zero_iff _).symm))

theorem dvRho_pos_iff (hg : GoodIff ct) (Z : ct.Mdl) (y : DVP ct) : 0 < dvRho y ↔ ¬ ct.abP (redK Z y) := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ← ptK_good hg Z y]
  exact not_congr (hg Z (ptK Z y))

variable {Z : ct.Mdl} {y : DVP ct} {e : Ext y}

theorem imgU_inQ (χ : Chart Z y e) : ct.inQ (imgU χ) := by
  have h : CharZero ((Sp e.R).residueField (primeU e)) := by
    have hpr : (primeU e : PrimeSpectrum e.R).asIdeal.IsPrime := PowerSeries.span_X_isPrime
    have hq : CharZero (primeU e : PrimeSpectrum e.R).asIdeal.ResidueField := by
      refine ⟨fun a b hab => ?_⟩
      have h1 : algebraMap e.R (primeU e : PrimeSpectrum e.R).asIdeal.ResidueField ((a : e.R) - b) = 0 := by
        rw [map_sub, map_natCast, map_natCast, hab, sub_self]
      have h2 : (a : e.R) - b ∈ Ideal.span {(PowerSeries.X : e.R)} := Ideal.algebraMap_residueField_eq_zero.1 h1
      rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, map_natCast, map_natCast, sub_eq_zero] at h2
      exact_mod_cast h2
    exact @charZero_of_injective_ringHom _ _ _ _ (Scheme.Spec.residueFieldIso (CommRingCat.of e.R) (primeU e)).inv.hom
      (RingHom.injective _) hq
  exact RingHom.charZero (χ.hom.residueFieldMap (primeU e)).hom

theorem chAt_imgM (χ : Chart Z y e) (h : chAt χ) : imgM χ = redK Z y := by
  obtain ⟨ev, h₁, h₂, h₃⟩ := h
  have : IsLocalHom ev := IsLocalHom.of_surjective ev fun x => ⟨_, h₁ x⟩
  have e1 : spMap (inclO e.L) (closedPoint _) = closedPoint e.O := comap_closedPoint (inclO e.L)
  have e2 : spMap ev (closedPoint _) = closedPoint e.R := comap_closedPoint ev
  rw [redK, PtAt.red, ← h₃]
  exact (congrArg χ.hom ((congrArg (spMap ev) e1).trans e2)).symm

theorem chAbExact_imgU (χ : Chart Z y e) (h : chAbExact χ) : ¬ ct.abP (imgU χ) :=
  fun h' => (h (primeU e)).1 h' (Ideal.mem_span_singleton_self _)

theorem goodIff_of (h₁ : AbOfTrivSt) (h₂ : TrivOfAbSt) (ct : At S κ p) : GoodIff ct := fun Z x => by
  have e : Z.π (x.z (closedPoint ↥(intO ↥x.C.S))) = x.P.yt (closedPoint _) :=
    congrArg (fun f => f (closedPoint ↥(intO ↥x.C.S))) x.z_π
  rw [Mdl.abP, e]
  exact ⟨h₁ _ _ _ _ _ _ _ _ _ _ _ _ (ct.dat x) ct.hp, h₂ _ _ _ _ _ _ _ _ _ _ _ _ (ct.dat x) ct.hp⟩

theorem genEx_of (h₁ : StalkSt) (h₂ : FieldSt) (h₃ : ExtendSt) (h₄ : FamSt) (ct : At S κ p) : GenEx ct := by
  intro Z η
  obtain ⟨_, _, _, _, hp, hgen⟩ := h₁ _ _ _ _ _ _ ct.Y _ ct.hp ct.hW Z η
  obtain ⟨C, f, K, hinj, hloc, hK, hdvr, hdense⟩ := h₂ p (Z.X.presheaf.stalk η.1) ct.hp hp
  let z : Sp ↥(intO ↥C.S) ⟶ Z.X := spMap f ≫ Z.X.fromSpecStalk η.1
  have hz : Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn := by
    rintro _ ⟨q, rfl⟩
    refine hgen (spMap f (spMap (intO ↥C.S).subtype q)) ?_
    change Ideal.comap f (Ideal.comap (intO ↥C.S).subtype q.asIdeal) = ⊥
    rw [show q.asIdeal = ⊥ from @Ideal.eq_bot_of_prime _ _ _ q.2, Ideal.comap_bot_of_injective _ (intO ↥C.S).subtype_injective,
      Ideal.comap_bot_of_injective _ hinj]
  obtain ⟨y, hy⟩ := (h₃ _ _ _ _ _ _ ct.Y _).2.1 Z C z hz
  let g : Z.X.presheaf.stalk η.1 →+* ↥K := ((intO ↥C.S).subtype.comp f).codRestrict K fun a =>
    hK ▸ Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨a, rfl⟩)
  obtain ⟨fam, hf, hrat⟩ := h₄ _ _ _ _ _ _ _ ct Z C y K (spMap g ≫ Z.X.fromSpecStalk η.1) (by
    rw [PtAt.gen, hy, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]; rfl)
  refine ⟨⟨C, K, hK ▸ Subfield.isClosed_topologicalClosure _, hdvr, hdense, fam, hrat⟩, ?_, ?_⟩
  · change (fam.pt Z).red = η.1
    have e1 : spMap f (closedPoint _) = closedPoint (Z.X.presheaf.stalk η.1) := comap_closedPoint f
    rw [hf, PtAt.red, hy]
    exact (congrArg (Z.X.fromSpecStalk η.1) e1).trans Scheme.fromSpecStalk_closedPoint
  · change ∃ h : (fam.pt Z).fnFld ≤ K, (Subfield.inclusion h).Finite
    have : (fam.pt Z).fnFld = K := by
      rw [hf, hK, PtAt.fnFld]
      congr 2
      ext c
      have key : ∀ (U : Z.X.Opens) (hU : η.1 ∈ U) (h : ⊤ ≤ y.z ⁻¹ᵁ U) (s : Γ(Z.X, U)),
          evAt y.z h s = f ((Z.X.presheaf.germ U η.1 hU).hom s) := by
        intro U hU h s
        revert h
        rw [hy]
        intro h
        exact evAt_fromSpecStalk η.1 f hU h s
      have hred : y.z (closedPoint _) = η.1 := by
        rw [hy]
        exact (congrArg (Z.X.fromSpecStalk η.1) (comap_closedPoint f)).trans Scheme.fromSpecStalk_closedPoint
      constructor
      · rintro ⟨U, h, s, rfl⟩
        have hU : η.1 ∈ U := hred ▸ h (Set.mem_univ (closedPoint _))
        exact ⟨_, congrArg Subtype.val (key U hU h s).symm⟩
      · rintro ⟨a, rfl⟩
        obtain ⟨U, hU, s, rfl⟩ := Z.X.presheaf.germ_exist a
        have h : ⊤ ≤ y.z ⁻¹ᵁ U := fun q _ =>
          ((specializes_closedPoint (q : PrimeSpectrum _)).map y.z.continuous).mem_open U.2 (hred ▸ hU)
        exact ⟨U, h, s, congrArg Subtype.val (key U hU h s).symm⟩
    exact ⟨this.le, RingHom.Finite.of_surjective _ fun x => ⟨⟨x.1, this ▸ x.2⟩, rfl⟩⟩

def chtOf (ct : At S κ p) (hg : GoodIff ct) (hx : GenEx ct) : ChtSt ct where
  DVP := DVP ct
  dvRho := dvRho
  Ext := Ext
  Chart := Chart
  chAt := chAt
  chOpen := chOpen
  chAbExact := chAbExact
  chModU := chModU
  chConst := chConst
  pbPrinc := pbPrinc
  redK := redK
  dvRho_pos_iff := dvRho_pos_iff hg
  genK η := (hx _ η).choose
  redK_genK η := (hx _ η).choose_spec.1
  imgM := imgM
  imgU := imgU
  img_spz := img_spz
  imgU_inQ := imgU_inQ
  chAt_imgM := chAt_imgM
  chAbExact_imgU := chAbExact_imgU
  RFam := RFam
  chFam := chFam
  ptK := ptK
  ptK_good := ptK_good hg
  vpi := vpi
  vpi_pos := vpi_pos
  ordGe := ordGe
  yEta η := ptK _ (hx _ η).choose
  yEta_good {Z} η := (hg Z _).trans (by
    have h : redK Z (hx _ η).choose = η.1 := (hx _ η).choose_spec.1
    exact iff_of_eq (congrArg Z.abP h))

end GlobalTheory.LocM.Cht
